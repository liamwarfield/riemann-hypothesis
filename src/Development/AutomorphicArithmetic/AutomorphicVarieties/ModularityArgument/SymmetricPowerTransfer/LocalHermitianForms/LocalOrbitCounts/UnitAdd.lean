module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FixPSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.FixMlIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FinsumQuotientNormsOfNonsplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSquareSqSubFourIffIsSquareUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RelIndexStabilizerLevelOneOfIsSquareUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.KapMove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FzdLaw

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RelIndexStabilizerOrderLevelZero
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.relIndex_stabilizer_order_level_zero :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → (Hu O (yy π 0 x)).relIndex (Gu O τ) = 1 := by
  intro O K _ _ _ _ _ Δ τ L hD π n e h x hc
  have hy : yy π 0 x = x := by simp [yy]
  have hO : PK.Ord O (yy π 0 x) = (PK.Mx O τ : Set (Etau K τ)) := by
    rw [hy, Gen1.span L hc.gen]
    rfl
  rw [Subgroup.relIndex_eq_one]
  intro u hu
  show PS.ml u (PK.Ord O (yy π 0 x)) = PK.Ord O (yy π 0 x)
  rw [hO]
  exact ml_Mx hu.1 hu.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsDiscriminantNormalForm
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.exists_discriminant_normal_form :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → τ ∈ (algebraMap O K).range → ∀ (s : O) (ε : Oˣ), τ ^ 2 - 4 = algebraMap O K (ε * s ^ 2) → ∃ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x ∧ Ideal.span {s} = Ideal.span {π ^ n} := by
  intro O K _ _ _ _ _ Δ τ hL hτ hτr s ε hs
  haveI := hL.frac
  have inj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨t, rfl⟩ := hτr
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hτ
    rw [hs]
    simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, μ, hμ⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  have h2K : algebraMap O K (((hL.two.unit)⁻¹ : Oˣ) : O) * 2 = 1 := by
    have h1 : (((hL.two.unit)⁻¹ : Oˣ) : O) * 2 = 1 := hL.two.val_inv_mul
    have h3 := congrArg (algebraMap O K) h1
    rw [map_mul, map_one, map_ofNat] at h3
    exact h3
  have two_ne : (2 : K) ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2K
    exact zero_ne_one h2K
  have hI : algebraMap O K (((hL.two.unit)⁻¹ : Oˣ) : O) = 2⁻¹ := by
    field_simp
    exact h2K
  have hP : algebraMap O K (ϖ ^ n) ≠ 0 := by
    rw [map_ne_zero_iff _ inj]
    exact pow_ne_zero _ hϖ.ne_zero
  have hrel : algebraMap O K t ^ 2 - 4
      = algebraMap O K ε * algebraMap O K μ ^ 2 * algebraMap O K (ϖ ^ n) ^ 2 := by
    rw [hs, hμ]
    simp only [map_mul, map_pow]
    ring
  set T := algebraMap O K t with hT
  set P := algebraMap O K (ϖ ^ n) with hPdef
  let x : Etau K T := ⟨-T / 2 / P, 1 / P⟩
  have hxre : x.re = -T / 2 / P := rfl
  have hxim : x.im = 1 / P := rfl
  have htr : trace x = 0 := by
    rw [trace_def, hxre, hxim]
    field_simp
    ring
  refine ⟨ϖ, n, ε * μ * μ * (hL.two.unit)⁻¹ * (hL.two.unit)⁻¹, t * (((hL.two.unit)⁻¹ : Oˣ) : O), x,
    ⟨hϖ, ⟨?_, ?_, ?_⟩, htr, ?_, ?_⟩, ?_⟩
  · rw [htr]
    exact ⟨0, map_zero _⟩
  · refine ⟨-((ε * μ * μ * (hL.two.unit)⁻¹ * (hL.two.unit)⁻¹ : Oˣ) : O), ?_⟩
    rw [norm_def, hxre, hxim]
    simp only [map_neg, Units.val_mul, map_mul, hI]
    field_simp
    linear_combination hrel
  · refine ⟨ε * μ * μ, ?_⟩
    rw [hxim, hrel]
    simp only [Units.val_mul, map_mul]
    field_simp
  · apply QuadraticAlgebra.ext
    · rw [algebraMap_etau, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_mul, hxre, hxim]
      simp only [Units.val_mul, map_mul, hI]
      field_simp
      linear_combination hrel
    · rw [algebraMap_etau, QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.im_mul, hxre, hxim]
      field_simp
      ring
  · apply QuadraticAlgebra.ext
    · show (0 : K) = (algebraMap O (Etau K T) (t * (((hL.two.unit)⁻¹ : Oˣ) : O))).re + (yy ϖ n x).re
      rw [algebraMap_etau, QuadraticAlgebra.algebraMap_re]
      simp only [yy, QuadraticAlgebra.re_smul, smul_eq_mul, map_mul, hI, hxre]
      rw [← hT, ← hPdef]
      field_simp
      ring
    · show (1 : K) = (algebraMap O (Etau K T) (t * (((hL.two.unit)⁻¹ : Oˣ) : O))).im + (yy ϖ n x).im
      rw [algebraMap_etau, QuadraticAlgebra.algebraMap_im]
      simp only [yy, QuadraticAlgebra.im_smul, smul_eq_mul, hxim]
      rw [← hPdef]
      field_simp
      ring
  · rw [Ideal.span_singleton_eq_span_singleton, hμ]
    exact associated_unit_mul_left _ _ μ.isUnit
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.PKappa
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem sum_split (I : ℕ → ℕ) (q : ℕ) (h0 : I 0 = 1) (h1 : I 1 + 1 = q)
    (hs : ∀ m, 1 ≤ m → I (m + 1) = q * I m) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), I m = q ^ n := by
  have key : ∀ k, I (k + 1) + q ^ k = q ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      rw [hs (k + 1) (by omega)]
      calc q * I (k + 1) + q ^ (k + 1) = q * (I (k + 1) + q ^ k) := by ring
        _ = q ^ (k + 1 + 1) := by rw [ih]; ring
  induction n with
  | zero => simp [h0]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    linarith [key k]

private theorem sum_inert (I : ℕ → ℕ) (q : ℕ) (h0 : I 0 = 1) (h1 : I 1 = q + 1)
    (hs : ∀ m, 1 ≤ m → I (m + 1) = q * I m) (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + m) * (I m : ℤ) = (q : ℤ) ^ n := by
  have key : ∀ k, (I (k + 1) : ℤ) = (q : ℤ) ^ (k + 1) + (q : ℤ) ^ k := by
    intro k
    induction k with
    | zero => simp [h1]
    | succ k ih =>
      rw [hs (k + 1) (by omega)]
      push_cast
      rw [ih]
      ring
  induction n with
  | zero => simp [h0]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have e : ∑ m ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k + 1 + m) * (I m : ℤ)
        = -∑ m ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k + m) * (I m : ℤ) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [show k + 1 + m = (k + m) + 1 by omega, pow_succ]
      ring
    rw [e, ih, key k, show k + 1 + (k + 1) = 2 * (k + 1) by omega, pow_mul]
    norm_num

section
variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K}

private theorem ev_odd (L : IsLoc O Δ) {g y : K} (hg0 : g ≠ 0) (hg : ¬ EvenVal O g) (hy : y ≠ 0) :
    EvenVal O (y * g) ↔ ¬ EvenVal O y := by
  constructor
  · intro h hy'
    apply hg
    have e := PS.even_mul h (PS.even_inv hy')
    rwa [show y * g * y⁻¹ = g by field_simp] at e
  · intro hy'
    have h1 := (PS.even_or L hy hg0 hg).resolve_left hy'
    have h2 : EvenVal O (g ^ 2) := ⟨1, g, hg0, by simp⟩
    have e := PS.even_mul h1 h2
    rwa [show y / g * g ^ 2 = y * g by field_simp] at e

private theorem ev_pow (L : IsLoc O Δ) {π : O} (hπ : Irreducible π) (k : ℕ) :
    EvenVal O (algebraMap O K (π ^ k)) ↔ Even k := by
  haveI := L.frac
  have hinj := IsFractionRing.injective O K
  have hπ0 : algebraMap O K π ≠ 0 := by
    intro h
    exact hπ.ne_zero (hinj (by rw [h, map_zero]))
  induction k with
  | zero =>
    simp only [pow_zero, map_one]
    exact ⟨fun _ => ⟨0, rfl⟩, fun _ => ⟨1, 1, one_ne_zero, by simp⟩⟩
  | succ k ih =>
    have hy : algebraMap O K (π ^ k) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero k hπ0
    rw [pow_succ, map_mul, ev_odd L hπ0 (PS.not_even_irr L hπ) hy, Nat.even_add_one]
    exact not_congr ih

end

theorem UpperTheory.V.Z.Sym.Loc.pKappa :
    UpperTheory.V.Z.Sym.Loc.PKappa := by
  unfold UpperTheory.V.Z.Sym.Loc.PKappa
  intro O K _ _ _ _ _ Δ τ L hD hτ s ε hDs
  classical
  obtain ⟨π, n, e, h, x, hC, hspan⟩ := UpperTheory.exists_discriminant_normal_form O K Δ τ L hD hτ s ε hDs
  have hπ : Irreducible π := hC.irr
  haveI := L.frac
  have hinj := IsFractionRing.injective O K
  have hπ0 : algebraMap O K π ≠ 0 := by
    intro h0
    exact hπ.ne_zero (hinj (by rw [h0, map_zero]))
  have hodd : ¬ EvenVal O (algebraMap O K π) := PS.not_even_irr L hπ
  have hP : ∀ m, algebraMap O K (π ^ (n + m)) ≠ 0 := fun m => by
    rw [map_pow]
    exact pow_ne_zero _ hπ0
  set q := Nat.card (IsLocalRing.ResidueField O) with hq
  set r : ℕ → ℕ := fun m => (PK.Hu O (PK.yy π m x)).relIndex (PK.Gu O τ) with hr
  have r0 : r 0 = 1 := UpperTheory.relIndex_stabilizer_order_level_zero O K Δ τ L hD π n e h x hC
  have rs : ∀ m, 1 ≤ m → r (m + 1) = q * r m := by
    intro m hm
    have h1 := (UpperTheory.stabilizer_order_level_antitone_le_units O K Δ τ L hD π n e h x hC m).1
    have h2 := (UpperTheory.stabilizer_order_level_antitone_le_units O K Δ τ L hD π n e h x hC m).2
    simp only [hr]
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ h1 h2, UpperTheory.relIndex_stabilizer_succ_eq_card_residueField O K Δ τ L hD π n e h x hC m hm]
  have hcount : ∀ t : Kˣ, ((PS.Gs O τ (↑t) 1).ncard : ℂ) = ∑ m ∈ Finset.range (n + 1),
      if EvenVal O ((t : K) * algebraMap O K (π ^ (n + m))) then (r m : ℂ) else 0 := by
    intro t
    rw [PK.gs_count L hD hC t]
    push_cast
    rfl
  have hRHS : Nat.card (O ⧸ Ideal.span {s}) = q ^ n := by
    rw [hspan, UpperTheory.card_quotient_span_uniformizer_pow O K Δ τ L π hπ n]
  rw [hRHS]
  have hDe := UpperTheory.isSquare_sq_sub_four_iff_isSquare_unit O K Δ τ L hD π n e h x hC
  have hL := hsLaw O K Δ L
  by_cases hsq : IsSquare (τ ^ 2 - 4)
  · have hE : IsSquare (e : O) := hDe.1 hsq
    have r1 : r 1 + 1 = q := (UpperTheory.relIndex_stabilizer_level_one_of_isSquare_unit O K Δ τ L hD π n e h x hC).2 hE
    have hall : ∀ t : Kˣ, t ∈ NE τ := fun t => (hsNE O K Δ τ L hD t).2 (hL.2.2.2 _ _ hD hsq)
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 (hall (Units.mk0 (algebraMap O K π) hπ0))
    have hnb' : PS.nU b = Units.mk0 (algebraMap O K π) hπ0 := hb
    have hnb : QuadraticAlgebra.norm (b : Etau K τ) = algebraMap O K π := by
      rw [← PS.nU_val, hnb', Units.val_mk0]
    have hC13 := UpperTheory.evenValuation_norm_compactUnits_of_split O K Δ τ L hD hsq
    have hbC : b ∉ Cint O τ := by
      intro hb'
      have := hC13.1 b hb'
      rw [hnb] at this
      exact hodd this
    have cover : ∀ y : (Etau K τ)ˣ, ∃ z, ∃ c ∈ Cint O τ, y = 1 * c * z ^ 2 ∨ y = b * c * z ^ 2 := by
      intro y
      have hy0 : QuadraticAlgebra.norm (y : Etau K τ) ≠ 0 := by
        rw [← PS.nU_val]
        exact Units.ne_zero _
      rcases PS.even_or L hy0 hπ0 hodd with hev | hev
      · obtain ⟨z, c, hc, hyz⟩ := hC13.2 y hev
        exact ⟨z, c, hc, Or.inl (by rw [hyz, one_mul])⟩
      · have hev' : EvenVal O (QuadraticAlgebra.norm ((b⁻¹ * y : (Etau K τ)ˣ) : Etau K τ)) := by
          rw [← PS.nU_val]
          simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, PS.nU_val, hnb]
          rwa [div_eq_mul_inv, mul_comm] at hev
        obtain ⟨z, c, hc, hyz⟩ := hC13.2 _ hev'
        exact ⟨z, c, hc, Or.inr (by rw [mul_assoc, ← hyz, mul_inv_cancel_left])⟩
    have uniq : ∀ z : (Etau K τ)ˣ, z ^ 2 * 1 * b⁻¹ ∈ Cint O τ → z ∈ Cint O τ := by
      intro z hz
      exfalso
      apply hodd
      have h1 : EvenVal O (QuadraticAlgebra.norm ((z ^ 2 * 1 * b⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := hC13.1 _ hz
      have h2 : EvenVal O (((PS.nU z : Kˣ) : K) ^ 2) := ⟨1, _, Units.ne_zero _, by rw [Units.val_one, map_one, one_mul]⟩
      have h3 := PS.even_mul h2 (PS.even_inv h1)
      have e3 : ((PS.nU z : Kˣ) : K) ^ 2 * (QuadraticAlgebra.norm ((z ^ 2 * 1 * b⁻¹ : (Etau K τ)ˣ) : Etau K τ))⁻¹
          = algebraMap O K π := by
        rw [← PS.nU_val, ← hnb, ← PS.nU_val]
        simp only [map_mul, map_pow, map_one, mul_one, map_inv, Units.val_mul, Units.val_pow_eq_pow_val,
          Units.val_inv_eq_inv_val]
        field_simp
      rwa [e3] at h3
    have disj : ∀ t : K, Disjoint (PS.Gs O τ t 1) (PS.Gs O τ t b) := by
      intro t
      rw [Set.disjoint_left]
      rintro S ⟨_, c, hc, hg⟩ ⟨_, c', hc', hg'⟩
      have hu := PS.gen_uniq hg hg'
      apply hbC
      have e1 : b = (1 * c) * ((1 * c)⁻¹ * (b * c')) * c'⁻¹ := by group
      rw [e1]
      exact (Cint O τ).mul_mem ((Cint O τ).mul_mem (by rwa [one_mul]) hu) ((Cint O τ).inv_mem hc')
    have hp : ∀ t : Kˣ, pcount O τ (t : K) = ((PS.Gs O τ (↑t) 1).ncard : ℂ)
        + ((PS.Gs O τ (↑(t * Units.mk0 (algebraMap O K π) hπ0)) 1).ncard : ℂ) := by
      intro t
      rw [PS.pcount_eq L hD t 1 b cover uniq,
        Set.ncard_union_eq (disj _) (PS.gs_fin L hD t 1) (PS.gs_fin L hD t b), PS.gs_ncard (↑t) b, hnb',
        ← Units.val_mul]
      exact Nat.cast_add _ _
    haveI : Unique (Kˣ ⧸ NE τ) :=
      { default := 1
        uniq := fun u => by
          obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective u
          exact (QuotientGroup.eq_one_iff a).2 (hall a) }
    rw [finsum_unique]
    have hterm : ∀ t0 : Kˣ, ∀ m ∈ Finset.range (n + 1),
        ((if EvenVal O ((t0 : K) * algebraMap O K (π ^ (n + m))) then (r m : ℂ) else 0) +
          (if EvenVal O (((t0 * Units.mk0 (algebraMap O K π) hπ0 : Kˣ) : K) * algebraMap O K (π ^ (n + m)))
            then (r m : ℂ) else 0)) = (r m : ℂ) := by
      intro t0 m _
      rw [Units.val_mul, Units.val_mk0,
        show (t0 : K) * algebraMap O K π * algebraMap O K (π ^ (n + m))
          = (t0 : K) * algebraMap O K (π ^ (n + m)) * algebraMap O K π by ring,
        ev_odd L hπ0 hodd (mul_ne_zero (Units.ne_zero t0) (hP m))]
      by_cases hE : EvenVal O ((t0 : K) * algebraMap O K (π ^ (n + m)))
      · rw [if_pos hE, if_neg (not_not.2 hE), add_zero]
      · rw [if_neg hE, if_pos hE, zero_add]
    rw [hL.2.2.2 _ _ hD hsq, one_mul, hp, hcount, hcount, ← Finset.sum_add_distrib, Finset.sum_congr rfl (hterm _)]
    exact_mod_cast sum_split r q r0 r1 rs n
  · have hE : ¬ IsSquare (e : O) := fun h' => hsq (hDe.2 h')
    have r1 : r 1 = q + 1 := (UpperTheory.relIndex_stabilizer_level_one_of_isSquare_unit O K Δ τ L hD π n e h x hC).1 hE
    have hCt : Cint O τ = ⊤ := UpperTheory.compactTorusUnits_eq_top_of_nonsplit O K Δ τ L hD hsq
    obtain ⟨⟨g, hg⟩, hfin⟩ := UpperTheory.finsum_quotient_norms_of_nonsplit O K Δ τ L hD hsq
    have cover : ∀ y : (Etau K τ)ˣ, ∃ z, ∃ c ∈ Cint O τ, y = 1 * c * z ^ 2 ∨ y = 1 * c * z ^ 2 :=
      fun y => ⟨1, y, by rw [hCt]; exact Subgroup.mem_top _, Or.inl (by simp)⟩
    have uniq : ∀ z : (Etau K τ)ˣ, z ^ 2 * 1 * 1⁻¹ ∈ Cint O τ → z ∈ Cint O τ :=
      fun z _ => by rw [hCt]; exact Subgroup.mem_top _
    have hp : ∀ t : Kˣ, pcount O τ (t : K) = ((PS.Gs O τ (↑t) 1).ncard : ℂ) := by
      intro t
      rw [PS.pcount_eq L hD t 1 1 cover uniq, Set.union_self]
    have hGs : ∀ (t : K) (a : (Etau K τ)ˣ), PS.Gs O τ t a = PS.Gs O τ t 1 := by
      intro t a
      ext S
      simp only [PS.Gs, Set.mem_setOf_eq, hCt, Subgroup.mem_top, true_and, one_mul]
      constructor
      · rintro ⟨hf, c, hc⟩
        exact ⟨hf, a * c, hc⟩
      · rintro ⟨hf, c, hc⟩
        exact ⟨hf, a⁻¹ * c, by rwa [mul_inv_cancel_left]⟩
    have hs0 : algebraMap O K s ≠ 0 := by
      intro h0
      apply hD
      rw [hDs, map_mul, map_pow, h0]
      ring
    have hDv : EvenVal O (τ ^ 2 - 4) := ⟨ε, algebraMap O K s, hs0, by rw [hDs, map_mul, map_pow]⟩
    have hg1 : hs (τ ^ 2 - 4) (g : K) = -1 := by
      have h1 : ¬ hs (τ ^ 2 - 4) (g : K) = 1 := fun h' => hg ((hsNE O K Δ τ L hD g).2 h')
      unfold UpperTheory.V.Z.Sym.Loc.hs at h1 ⊢
      split_ifs at h1 ⊢
      · exact absurd rfl h1
      · rfl
    have hgodd : ¬ EvenVal O (g : K) := fun hev => by
      have h2 := hL.2.1 _ _ hDv hev
      rw [hg1] at h2
      norm_num at h2
    have hinv : ∀ t ∈ NE τ, ∀ y : Kˣ, hs (τ ^ 2 - 4) ((t * y : Kˣ) : K) * pcount O τ ((t * y : Kˣ) : K)
        = hs (τ ^ 2 - 4) (y : K) * pcount O τ (y : K) := by
      intro t ht y
      obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 ht
      have ha' : PS.nU a = t := ha
      rw [Units.val_mul, hsMul O K Δ L _ _ _ hD (Units.ne_zero _) (Units.ne_zero _),
        (hsNE O K Δ τ L hD t).1 ht, one_mul, ← Units.val_mul, hp, hp]
      congr 1
      rw [Units.val_mul, mul_comm, ← ha', ← PS.gs_ncard, hGs]
    have hf := hfin (fun t : Kˣ => hs (τ ^ 2 - 4) (t : K) * pcount O τ (t : K)) hinv g hg
    rw [hf]
    have hterm : ∀ m ∈ Finset.range (n + 1),
        ((if EvenVal O (((1 : Kˣ) : K) * algebraMap O K (π ^ (n + m))) then (r m : ℂ) else 0) +
          -(if EvenVal O ((g : K) * algebraMap O K (π ^ (n + m))) then (r m : ℂ) else 0))
          = (-1 : ℂ) ^ (n + m) * (r m : ℂ) := by
      intro m _
      rw [Units.val_one, one_mul, ev_pow L hπ, mul_comm (g : K),
        ev_odd L (Units.ne_zero g) hgodd (hP m), ev_pow L hπ]
      by_cases hev : Even (n + m)
      · simp [hev, hev.neg_one_pow]
      · simp [hev, (Nat.not_even_iff_odd.1 hev).neg_one_pow]
    rw [(hsNE O K Δ τ L hD 1).1 (NE τ).one_mem, hg1, hp, hp, hcount, hcount, one_mul, neg_one_mul,
      ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl hterm]
    exact_mod_cast sum_inert r q r0 r1 rs n
end

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

private theorem res_rep {k : Type} [Field k] [Finite k] (h2 : (2 : k) ≠ 0) {e u : k} (he : e ≠ 0) (he1 : 1 - e ≠ 0) (hu : u ≠ 0) :
    ∃ a b : k, a ≠ 0 ∧ a ^ 2 - e * b ^ 2 = u := by
  classical
  haveI := Fintype.ofFinite k
  have hodd : Fintype.card k % 2 = 1 := by
    have hc : ringChar k ≠ 2 := by
      intro hc
      apply h2
      have h0 := ringChar.Nat.cast_ringChar (R := k)
      rw [hc] at h0
      exact_mod_cast h0
    have := (FiniteField.even_card_iff_char_two (F := k)).not.1 hc
    omega
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2 - Polynomial.C u) (g := Polynomial.C (-e) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_sub_C (by norm_num) u) (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.2 he)) hodd
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul] at hab
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by
      rintro rfl
      apply hu
      linear_combination -hab
    refine ⟨e * b * (2 / (1 - e)), b * ((1 + e) / (1 - e)), ?_, ?_⟩
    · exact mul_ne_zero (mul_ne_zero he hb) (div_ne_zero h2 he1)
    · have key : (e * b * (2 / (1 - e))) ^ 2 - e * (b * ((1 + e) / (1 - e))) ^ 2
          = -e * b ^ 2 * ((1 - e) / (1 - e)) ^ 2 := by ring
      rw [key, div_self he1, one_pow, mul_one]
      linear_combination hab
  · exact ⟨a, b, ha, by linear_combination hab⟩

private theorem int_rep {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K} (L : IsLoc O Δ)
    (e u : Oˣ) (he : IsUnit (1 - (e : O))) : ∃ (x : Oˣ) (y : O), (x : O) ^ 2 - e * y ^ 2 = u := by
  classical
  haveI := L.fin
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal O) O := L.compl
  have hu0 : IsLocalRing.residue O u ≠ 0 := (u.isUnit.map (IsLocalRing.residue O)).ne_zero
  have he0 : IsLocalRing.residue O e ≠ 0 := (e.isUnit.map (IsLocalRing.residue O)).ne_zero
  have he1 : 1 - IsLocalRing.residue O e ≠ 0 := by
    rw [← map_one (IsLocalRing.residue O), ← map_sub]
    exact (he.map (IsLocalRing.residue O)).ne_zero
  have h2 : (2 : IsLocalRing.ResidueField O) ≠ 0 := by
    have h3 := L.two.map (IsLocalRing.residue O)
    rw [map_ofNat] at h3
    exact h3.ne_zero
  obtain ⟨a, b, ha, hab⟩ := res_rep h2 he0 he1 hu0
  obtain ⟨x0, rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨y0, rfl⟩ := IsLocalRing.residue_surjective b
  have hx0 : IsUnit x0 := by
    by_contra hx
    apply ha
    exact (IsLocalRing.residue_eq_zero_iff x0).2 ((IsLocalRing.mem_maximalIdeal _).2 hx)
  obtain ⟨c, hc⟩ : ∃ c : O, c = (u : O) + e * y0 ^ 2 := ⟨_, rfl⟩
  let P : Polynomial O := Polynomial.X ^ 2 - Polynomial.C c
  have hPm : P.Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hP0 : P.eval x0 ∈ IsLocalRing.maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [hc]
    simp only [map_sub, map_pow, map_add (f := _), map_mul]
    linear_combination hab
  have hd : P.derivative.eval x0 = 2 * x0 := by
    simp only [P, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    norm_num
  have hP1 : IsUnit (P.derivative.eval x0) := by
    rw [hd]
    exact L.two.mul hx0
  obtain ⟨x, hx, hxx⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal O) P hPm x0 hP0
    (hP1.map _)
  have hxu : IsUnit x := by
    by_contra hn
    have h5 : x ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hn
    have h6 := Ideal.sub_mem _ h5 hxx
    rw [sub_sub_cancel] at h6
    exact (IsLocalRing.mem_maximalIdeal _).1 h6 hx0
  refine ⟨hxu.unit, y0, ?_⟩
  have hx' : x ^ 2 - c = 0 := by
    have h4 := hx.eq_zero
    simpa [P] using h4
  rw [IsUnit.unit_spec]
  linear_combination hx' + hc

private theorem int_co {O K : Type} [CommRing O] [Field K] [Algebra O K] {Δ s : K} {e : O} (h : Δ * s ^ 2 = algebraMap O K e) (x y : O) :
    IsInt O (⟨algebraMap O K x, s * algebraMap O K y⟩ : Lsq K Δ) := by
  have hw : IsIntegral O (⟨0, s⟩ : Lsq K Δ) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    have hsq : (⟨0, s⟩ : Lsq K Δ) ^ 2 = algebraMap O (Lsq K Δ) e := by
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ) e]
      ext
      · simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re]
        linear_combination h
      · simp only [pow_two, QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_im]
        ring
    rw [hsq]
    exact isIntegral_algebraMap
  have he : (⟨algebraMap O K x, s * algebraMap O K y⟩ : Lsq K Δ)
      = algebraMap O (Lsq K Δ) x + algebraMap O (Lsq K Δ) y * ⟨0, s⟩ := by
    rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ) x, IsScalarTower.algebraMap_apply O K (Lsq K Δ) y]
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re,
        QuadraticAlgebra.algebraMap_im]
      ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re,
        QuadraticAlgebra.algebraMap_im]
      ring
  show IsIntegral O _
  rw [he]
  exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul hw)

private theorem unit_add {O : Type} [CommRing O] [IsLocalRing O] {a b : O} (ha : IsUnit a) (hb : b ∈ IsLocalRing.maximalIdeal O) :
    IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 h
  have h2 : a ∈ IsLocalRing.maximalIdeal O := by
    have h3 := Ideal.sub_mem _ h1 hb
    rwa [add_sub_cancel_right] at h3
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 ha

private theorem choice {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K} (L : IsLoc O Δ)
    (s : O) (ε : Oˣ) (hs0 : algebraMap O K s ≠ 0) (hm : s ∈ IsLocalRing.maximalIdeal O) :
    ∃ (r : K) (e : Oˣ) (ν p : Lsq K Δ) (b : K) (v w : Oˣ), Δ * r ^ 2 = algebraMap O K e ∧ IsInt O ν ∧ QuadraticAlgebra.norm ν = -1 ∧
      QuadraticAlgebra.norm p = -algebraMap O K (ε * s ^ 2) ∧ b ≠ 0 ∧ hs Δ b = hs Δ (algebraMap O K s) ∧
      p.im = r * (algebraMap O K v * b) ∧ algebraMap O K (ε * s ^ 2) + QuadraticAlgebra.trace (ν * p) = algebraMap O K w * b := by
  classical
  obtain ⟨u0, s0, hs00, hΔ⟩ := L.even
  have hL := hsLaw O K Δ L
  have hre : Δ * (s0⁻¹) ^ 2 = algebraMap O K u0 := by
    rw [hΔ]
    field_simp
  have hN : ∀ x y : K, QuadraticAlgebra.norm (⟨x, s0⁻¹ * y⟩ : Lsq K Δ) = x ^ 2 - algebraMap O K u0 * y ^ 2 := by
    intro x y
    rw [QuadraticAlgebra.norm_def]
    simp only
    linear_combination (-(y ^ 2)) * hre
  have hT : ∀ x1 y1 x2 y2 : K, QuadraticAlgebra.trace ((⟨x1, s0⁻¹ * y1⟩ : Lsq K Δ) * ⟨x2, s0⁻¹ * y2⟩)
      = 2 * (x1 * x2 + algebraMap O K u0 * y1 * y2) := by
    intro x1 y1 x2 y2
    show 2 * ((⟨x1, s0⁻¹ * y1⟩ : Lsq K Δ) * ⟨x2, s0⁻¹ * y2⟩).re + 0 * _ = _
    simp only [QuadraticAlgebra.re_mul]
    linear_combination (2 * y1 * y2) * hre
  have hS0 : (ε : O) * s ^ 2 ∈ IsLocalRing.maximalIdeal O :=
    Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hm 2 two_pos)
  by_cases hu1 : IsUnit (1 - (u0 : O))
  · have hinv1 : IsUnit (1 - ((u0⁻¹ : Oˣ) : O)) := by
      have e0 : 1 - ((u0⁻¹ : Oˣ) : O) = -((u0⁻¹ : Oˣ) : O) * (1 - u0) := by
        linear_combination -(Units.inv_mul u0)
      rw [e0]
      exact ((u0⁻¹).isUnit.neg).mul hu1
    obtain ⟨a2, a1, ha⟩ := int_rep L u0⁻¹ (u0⁻¹ * ε) hinv1
    obtain ⟨y, x, hxy⟩ := int_rep L u0⁻¹ u0⁻¹ hinv1
    rw [Units.val_mul] at ha
    have hu := Units.mul_inv u0
    have ha' : a1 ^ 2 - (u0 : O) * (a2 : O) ^ 2 = -(ε : O) := by
      linear_combination (-(u0 : O)) * ha - (a1 ^ 2 + ε) * hu
    have hxy' : x ^ 2 - (u0 : O) * (y : O) ^ 2 = -1 := by
      linear_combination (-(u0 : O)) * hxy - (x ^ 2 + 1) * hu
    obtain ⟨σ, hσ, hσu⟩ : ∃ σ : O, σ ^ 2 = 1 ∧ IsUnit (x * a1 + u0 * (σ * y) * a2) := by
      by_cases h1 : IsUnit (x * a1 + u0 * y * a2)
      · exact ⟨1, one_pow _, by simpa using h1⟩
      · refine ⟨-1, by ring, ?_⟩
        by_contra h2
        have m1 := (IsLocalRing.mem_maximalIdeal _).2 h1
        have m2 := (IsLocalRing.mem_maximalIdeal _).2 h2
        have m3 := Ideal.sub_mem _ m1 m2
        have e3 : x * a1 + (u0 : O) * y * a2 - (x * a1 + u0 * (-1 * y) * a2) = 2 * (u0 * (y * a2)) := by ring
        rw [e3] at m3
        exact (IsLocalRing.mem_maximalIdeal _).1 m3 (L.two.mul (u0.isUnit.mul (y.isUnit.mul a2.isUnit)))
    have hw := unit_add (L.two.mul hσu) (Ideal.mul_mem_left _ (ε : O) hm)
    refine ⟨s0⁻¹, u0, ⟨algebraMap O K x, s0⁻¹ * algebraMap O K (σ * y)⟩,
      ⟨algebraMap O K (s * a1), s0⁻¹ * algebraMap O K (s * a2)⟩, algebraMap O K s, a2, hw.unit,
      hre, int_co hre _ _, ?_, ?_, hs0, rfl, ?_, ?_⟩
    · rw [hN]
      have k1 : (x : O) ^ 2 - u0 * (σ * y) ^ 2 = -1 := by
        linear_combination hxy' - ((u0 : O) * (y : O) ^ 2) * hσ
      have k2 := congrArg (algebraMap O K) k1
      simp only [map_sub, map_mul, map_pow, map_neg, map_one] at k2
      simp only [map_mul]
      linear_combination k2
    · rw [hN]
      have k1 : (s * a1) ^ 2 - (u0 : O) * (s * a2) ^ 2 = -(ε * s ^ 2) := by
        linear_combination s ^ 2 * ha'
      have k2 := congrArg (algebraMap O K) k1
      simp only [map_sub, map_mul, map_pow, map_neg] at k2
      simp only [map_mul, map_pow, map_neg]
      linear_combination k2
    · show s0⁻¹ * algebraMap O K (s * a2) = s0⁻¹ * (algebraMap O K a2 * algebraMap O K s)
      rw [map_mul, mul_comm (algebraMap O K s)]
    · rw [hT, IsUnit.unit_spec]
      simp only [map_add (f := _), map_mul, map_pow, map_ofNat]
      ring
  · have hm1 : (u0 : O) - 1 ^ 2 ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro h
      apply hu1
      have h' := h.neg
      rwa [neg_sub, one_pow] at h'
    obtain ⟨c, hc, hc1⟩ := sqrtO O K Δ L u0 1 isUnit_one hm1
    have hcu : IsUnit c := by simpa using unit_add isUnit_one hc1
    have hΔ0 : Δ ≠ 0 := by
      rw [hΔ]
      exact mul_ne_zero (u0.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero _ hs00)
    have hsq : IsSquare Δ := ⟨algebraMap O K c * s0, by rw [hΔ, ← hc, map_pow]; ring⟩
    have h1 := unit_add isUnit_one hS0
    have h12 := unit_add isUnit_one (Ideal.mul_mem_left _ 2 hS0)
    have hci := hcu.mul_val_inv
    have h2 := L.two.mul_val_inv
    have h1i := h1.mul_val_inv
    set ci : O := ((hcu.unit⁻¹ : Oˣ) : O)
    set h2i : O := ((L.two.unit⁻¹ : Oˣ) : O)
    set u1i : O := ((h1.unit⁻¹ : Oˣ) : O)
    have hbu : IsUnit (ci * h2i * (1 + ε * s ^ 2)) :=
      ((hcu.unit⁻¹).isUnit.mul (L.two.unit⁻¹).isUnit).mul h1
    refine ⟨s0⁻¹, u0, ⟨algebraMap O K 0, s0⁻¹ * algebraMap O K ci⟩,
      ⟨algebraMap O K (h2i * (1 - ε * s ^ 2)), s0⁻¹ * algebraMap O K (ci * h2i * (1 + ε * s ^ 2))⟩,
      algebraMap O K (ci * h2i * (1 + ε * s ^ 2)), 1, h12.unit * hcu.unit * L.two.unit * h1.unit⁻¹,
      hre, int_co hre _ _, ?_, ?_, (hbu.map (algebraMap O K)).ne_zero, ?_, ?_, ?_⟩
    · rw [hN]
      have k1 : (0 : O) ^ 2 - u0 * ci ^ 2 = -1 := by
        linear_combination (ci ^ 2) * hc - (c * ci + 1) * hci
      have k2 := congrArg (algebraMap O K) k1
      simp only [map_sub, map_mul, map_pow, map_neg, map_one] at k2
      linear_combination k2
    · rw [hN]
      have k1 : (h2i * (1 - ε * s ^ 2)) ^ 2 - (u0 : O) * (ci * h2i * (1 + ε * s ^ 2)) ^ 2 = -(ε * s ^ 2) := by
        linear_combination (ci ^ 2 * h2i ^ 2 * (1 + ε * s ^ 2) ^ 2) * hc
          - ((c * ci + 1) * h2i ^ 2 * (1 + ε * s ^ 2) ^ 2) * hci - ((ε * s ^ 2) * (2 * h2i + 1)) * h2
      have k2 := congrArg (algebraMap O K) k1
      simp only [map_sub, map_add (f := _), map_mul, map_pow, map_neg, map_one] at k2
      simp only [map_sub, map_add (f := _), map_mul, map_pow, map_neg, map_one]
      linear_combination k2
    · rw [hL.2.2.2 _ _ hΔ0 hsq, hL.2.2.2 _ _ hΔ0 hsq]
    · show s0⁻¹ * algebraMap O K (ci * h2i * (1 + ε * s ^ 2))
        = s0⁻¹ * (algebraMap O K ((1 : Oˣ) : O) * algebraMap O K (ci * h2i * (1 + ε * s ^ 2)))
      rw [Units.val_one, map_one, one_mul]
    · rw [hT]
      simp only [Units.val_mul, IsUnit.unit_spec]
      have k1 : ε * s ^ 2 + 2 * (0 * (h2i * (1 - ε * s ^ 2)) + (u0 : O) * ci * (ci * h2i * (1 + ε * s ^ 2)))
          = (1 + 2 * (ε * s ^ 2)) * c * 2 * u1i * (ci * h2i * (1 + ε * s ^ 2)) := by
        linear_combination (-(2 * ci ^ 2 * h2i * (1 + ε * s ^ 2))) * hc
          + ((1 + ε * s ^ 2) * (c * ci + 1) * (2 * h2i) - (1 + 2 * (ε * s ^ 2)) * (2 * h2i) * ((1 + ε * s ^ 2) * u1i)) * hci
          + ((1 + ε * s ^ 2) - (1 + 2 * (ε * s ^ 2)) * ((1 + ε * s ^ 2) * u1i)) * h2
          - (1 + 2 * (ε * s ^ 2)) * h1i
      have k2 := congrArg (algebraMap O K) k1
      simp only [map_add (f := _), map_mul, map_pow, map_zero, map_ofNat, map_one] at k2
      simp only [map_add (f := _), map_mul, map_pow, map_zero, map_ofNat, map_one]
      linear_combination k2

private theorem root_tr {K : Type} [Field K] {τ : K} {u : Etau K τ} (hu : u ^ 2 = -ω) (hn : QuadraticAlgebra.norm u = 1) :
    QuadraticAlgebra.trace u ^ 2 = 2 - τ := by
  obtain ⟨x, y⟩ := u
  have e1 := congrArg QuadraticAlgebra.re hu
  have e2 := congrArg QuadraticAlgebra.im hu
  simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_neg,
    QuadraticAlgebra.im_neg, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im] at e1 e2
  simp only [QuadraticAlgebra.norm_def] at hn
  show (2 * x + τ * y) ^ 2 = 2 - τ
  linear_combination 2 * e1 + 2 * hn + τ * e2

private theorem move {K : Type} [Field K] {Δ τ : K} (h2 : (2 : K) ≠ 0) (hΔ : Δ ≠ 0) (hτ : 2 + τ ≠ 0) {u : Etau K τ} (hu : u ^ 2 = -ω)
    (hn : QuadraticAlgebra.norm u = 1) (z : (Etau K τ)ˣ) (hz : (z : Etau K τ) = 1 + ω) (ν p : Lsq K Δ)
    (hp : QuadraticAlgebra.norm p = -(2 + τ)) (hi : p.im ≠ 0) (r g : K) (hg : g * r * QuadraticAlgebra.trace u = 2 * p.im) :
    ∃ y : (EL Δ τ)ˣ, dLam (ν * p) z * sigL (y : EL Δ τ) * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) = ν • ofE Δ u ∧
      ∀ t : K, (t • (1 : EL Δ τ)) * (y : EL Δ τ) * star (sigL (y : EL Δ τ)) = ((t * g) • r • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ) := by
  obtain ⟨a, b⟩ := u
  have e1 := congrArg QuadraticAlgebra.re hu
  have e2 := congrArg QuadraticAlgebra.im hu
  simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_neg,
    QuadraticAlgebra.im_neg, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im] at e1 e2
  simp only [QuadraticAlgebra.norm_def] at hn
  have h0 : (2 + τ) * (b * (a + b)) = 0 := by linear_combination e2 + hn - e1
  have hb0 : b ≠ 0 := by
    intro hb
    subst hb
    have h3 : (1 : K) = 0 := by linear_combination -hn + e1
    exact one_ne_zero h3
  have hab : a = -b := by
    have h4 := (mul_eq_zero.1 h0).resolve_left hτ
    have h5 := (mul_eq_zero.1 h4).resolve_left hb0
    linear_combination h5
  subst hab
  have eb : (2 - τ) * b ^ 2 = 1 := by linear_combination hn
  obtain ⟨p1, p2⟩ := p
  simp only [QuadraticAlgebra.norm_def] at hp
  change p2 ≠ 0 at hi
  change g * r * (2 * (-b) + τ * b) = 2 * p2 at hg
  have hgr : g * r = -2 * b * p2 := by linear_combination (-(g * r)) * eb - b * hg
  have hc : (2 + τ)⁻¹ * (2 + τ) = 1 := inv_mul_cancel₀ hτ
  set c := (2 + τ)⁻¹ with hcdef
  have hZi : star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) = (⟨c, c⟩ : Etau K τ) := by
    have hz1 : star (z : Etau K τ) * (⟨c, c⟩ : Etau K τ) = 1 := by
      rw [hz]
      refine QuadraticAlgebra.ext ?_ ?_
      · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
        linear_combination hc
      · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
        ring
    have hz2 : star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * star (z : Etau K τ) = 1 := by
      rw [← star_mul', Units.inv_mul, star_one]
    calc star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ))
        = star (((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * (star (z : Etau K τ) * (⟨c, c⟩ : Etau K τ)) := by
          rw [hz1, mul_one]
      _ = ⟨c, c⟩ := by rw [← mul_assoc, hz2, one_mul]
  have h2τ : 2 - τ ≠ 0 := by
    intro h
    rw [h, zero_mul] at eb
    exact zero_ne_one eb
  have hD : τ ^ 2 - 4 ≠ 0 := by
    have h6 : τ ^ 2 - 4 = -((2 + τ) * (2 - τ)) := by ring
    rw [h6]
    exact neg_ne_zero.2 (mul_ne_zero hτ h2τ)
  have h4 : (4 : K) ≠ 0 := by
    have h7 : (4 : K) = 2 * 2 := by norm_num
    rw [h7]
    exact mul_ne_zero h2 h2
  let y0 : EL Δ τ := ⟨⟨p1 - τ * b, p2⟩, ⟨2 * b, 0⟩⟩
  let M : EL Δ τ := ⟨⟨0, 2 * τ * b * p2⟩, ⟨0, -4 * b * p2⟩⟩
  set κ : K := 4 * b ^ 2 * p2 ^ 2 * Δ * (τ ^ 2 - 4) with hκdef
  have hκ : κ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h4 (pow_ne_zero _ hb0)) (pow_ne_zero _ hi)) hΔ) hD
  have hM : y0 * star (sigL y0) = M := by
    refine QuadraticAlgebra.ext (QuadraticAlgebra.ext ?_ ?_) (QuadraticAlgebra.ext ?_ ?_)
    · simp only [y0, M, sigL, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination hp + (2 + τ) * eb
    · simp only [y0, M, sigL, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
    · simp only [y0, M, sigL, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
    · simp only [y0, M, sigL, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
  have hMM : M * M = κ • (1 : EL Δ τ) := by
    refine QuadraticAlgebra.ext (QuadraticAlgebra.ext ?_ ?_) (QuadraticAlgebra.ext ?_ ?_)
    · simp only [M, hκdef, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
    · simp only [M, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
    · simp only [M, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
    · simp only [M, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
  have hinv : y0 * (star (sigL y0) * (κ⁻¹ • M)) = 1 := by
    rw [← mul_assoc, hM, mul_smul_comm, hMM, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  have hI3 : dLam (ν * (⟨p1, p2⟩ : Lsq K Δ)) z * sigL y0 = (ν • ofE Δ (⟨-b, b⟩ : Etau K τ)) * y0 := by
    unfold dLam
    rw [hZi]
    obtain ⟨n1, n2⟩ := ν
    refine QuadraticAlgebra.ext (QuadraticAlgebra.ext ?_ ?_) (QuadraticAlgebra.ext ?_ ?_)
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination n1 * (c * hp - (1 + b * p1) * hc + eb) + Δ * n2 * ((-b * p2) * hc)
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination n1 * ((-b * p2) * hc) + n2 * (c * hp - (1 + b * p1) * hc + eb)
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination n1 * (c * hp + (b * p1 - 1) * hc + eb) + Δ * n2 * ((b * p2) * hc)
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination n1 * ((b * p2) * hc) + n2 * (c * hp + (b * p1 - 1) * hc + eb)
  let y : (EL Δ τ)ˣ := Units.mkOfMulEqOne y0 _ hinv
  refine ⟨y, ?_, ?_⟩
  · show dLam (ν * (⟨p1, p2⟩ : Lsq K Δ)) z * sigL y0 * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) = _
    rw [hI3, mul_assoc]
    have h8 : y0 * ((y⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) = 1 := Units.mul_inv y
    rw [h8, mul_one]
  · intro t
    show (t • (1 : EL Δ τ)) * y0 * star (sigL y0) = _
    refine QuadraticAlgebra.ext (QuadraticAlgebra.ext ?_ ?_) (QuadraticAlgebra.ext ?_ ?_)
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination t * hp + t * (2 + τ) * eb
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination t * τ * hgr
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      ring
    · simp only [y0, sigL, ofE, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_smul, QuadraticAlgebra.im_smul, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, smul_eq_mul]
      linear_combination (-2 * t) * hgr

private theorem hs_sq {K : Type} [Field K] (D x : K) : hs D x * hs D x = 1 := by
  unfold hs
  split_ifs <;> norm_num

theorem UpperTheory.V.Z.Sym.Loc.kapM :
    UpperTheory.V.Z.Sym.Loc.KapM := by
  unfold UpperTheory.V.Z.Sym.Loc.KapM
  intro O K _ _ _ _ _ Δ τ L hD hu0e s ε hm h2τ c hc z hz lam hlam hT
  classical
  obtain ⟨u0, hu0⟩ := hu0e
  haveI := L.frac
  have hinj := IsFractionRing.injective O K
  have hunit : ∀ x : O, IsUnit x → algebraMap O K x ≠ 0 := fun x hx => (hx.map (algebraMap O K)).ne_zero
  have hevu : ∀ x : Oˣ, EvenVal O (algebraMap O K x) := fun x => ⟨x, 1, one_ne_zero, by simp⟩
  have h2K : (2 : K) ≠ 0 := by
    have h3 := hunit 2 L.two
    rwa [map_ofNat] at h3
  have hΔ : Δ ≠ 0 := by
    obtain ⟨uu, ss, hss, hΔe⟩ := L.even
    rw [hΔe]
    exact mul_ne_zero (hunit _ uu.isUnit) (pow_ne_zero 2 hss)
  have hc0 : c ≠ 0 := by
    obtain ⟨cu, cs, hcs, hce⟩ := hc
    rw [hce]
    exact mul_ne_zero (hunit _ cu.isUnit) (pow_ne_zero 2 hcs)
  have h2t : (2 : K) + τ ≠ 0 := by
    intro h0
    apply hD
    linear_combination (τ - 2) * h0
  have hs0 : algebraMap O K s ≠ 0 := by
    intro h0
    apply h2t
    rw [h2τ, map_mul, map_pow, h0]
    ring
  have h2τ' : (2 : K) + τ = algebraMap O K ε * algebraMap O K s ^ 2 := by
    rw [h2τ, map_mul, map_pow]
  have hDalg : τ ^ 2 - 4 = algebraMap O K (((-(u0 * ε) : Oˣ) : O) * s ^ 2) := by
    simp only [Units.val_neg, Units.val_mul, map_mul, map_neg, map_pow]
    linear_combination (algebraMap O K ε * algebraMap O K s ^ 2) * hu0 - (2 - τ) * h2τ'
  have hDv : EvenVal O (τ ^ 2 - 4) := ⟨-(u0 * ε), algebraMap O K s, hs0, by rw [hDalg, map_mul, map_pow]⟩
  have hL := hsLaw O K Δ L
  have hτ0 : algebraMap O K ((ε : O) * s ^ 2 - 2) = τ := by
    rw [map_sub, map_ofNat, ← h2τ]
    ring
  have hm0 : ((ε : O) * s ^ 2 - 2) + 2 ∈ IsLocalRing.maximalIdeal O := by
    rw [sub_add_cancel, pow_two, ← mul_assoc]
    exact Ideal.mul_mem_left _ _ hm
  have hre : ((ε : O) * s ^ 2 - 2) - 2 * (((-1 : ℤˣ) : ℤ) : O) = ((ε : O) * s ^ 2 - 2) + 2 := by
    push_cast
    ring
  obtain ⟨xr, yr, hyr, hsq, hnorm⟩ := rootEx O K Δ τ L ((ε : O) * s ^ 2 - 2) (-1) hτ0 (by rw [hre]; exact hm0)
  have hu2 : (⟨algebraMap O K xr, algebraMap O K yr⟩ : Etau K τ) ^ 2 = -ω := by
    rw [hsq]
    simp
  have htr : QuadraticAlgebra.trace (⟨algebraMap O K xr, algebraMap O K yr⟩ : Etau K τ)
      = algebraMap O K (2 * xr + ((ε : O) * s ^ 2 - 2) * yr) := by
    show 2 * algebraMap O K xr + τ * algebraMap O K yr = _
    rw [map_add (f := _), map_mul, map_mul, hτ0, map_ofNat]
  have ht2 := root_tr hu2 hnorm
  have ht0u : IsUnit (2 * xr + ((ε : O) * s ^ 2 - 2) * yr) := by
    have h5 : (2 * xr + ((ε : O) * s ^ 2 - 2) * yr) ^ 2 = u0 := by
      apply hinj
      rw [map_pow, ← htr, ht2, hu0]
    have h6 : IsUnit ((2 * xr + ((ε : O) * s ^ 2 - 2) * yr) ^ 2) := by
      rw [h5]
      exact u0.isUnit
    exact (isUnit_pow_iff (by norm_num)).1 h6
  obtain ⟨r, e, ν, p, b, v, w, hr, hν, hnν, hnp, hb0, hsb, hpim, hT2⟩ := choice L s ε hs0 hm
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hunit _ e.isUnit
    rw [← hr]
    ring
  have htr0 : QuadraticAlgebra.trace (⟨algebraMap O K xr, algebraMap O K yr⟩ : Etau K τ) ≠ 0 := by
    rw [htr]
    exact hunit _ ht0u
  have hpim0 : p.im ≠ 0 := by
    rw [hpim]
    exact mul_ne_zero hr0 (mul_ne_zero (hunit _ v.isUnit) hb0)
  obtain ⟨g, hgdef⟩ : ∃ g : K, g = 2 * p.im / (r * QuadraticAlgebra.trace
      (⟨algebraMap O K xr, algebraMap O K yr⟩ : Etau K τ)) := ⟨_, rfl⟩
  have hg : g * r * QuadraticAlgebra.trace (⟨algebraMap O K xr, algebraMap O K yr⟩ : Etau K τ) = 2 * p.im := by
    rw [hgdef]
    field_simp
  have hg0 : g ≠ 0 := by
    rw [hgdef]
    exact div_ne_zero (mul_ne_zero h2K hpim0) (mul_ne_zero hr0 htr0)
  have hnp' : QuadraticAlgebra.norm p = -(2 + τ) := by rw [hnp, h2τ]
  obtain ⟨y, hy1, hy2⟩ := move h2K hΔ h2t hu2 hnorm z hz ν p hnp' hpim0 r g hg
  have hcase : ∀ t : Kˣ, lcount O c (ν • ofE Δ (⟨algebraMap O K xr, algebraMap O K yr⟩ : Etau K τ))
      (((↑t * g) • r • (ω : Lsq K Δ)) • ofE Δ (ω - star ω : Etau K τ))
      = pcount O τ (↑t * (g * (τ ^ 2 - 4))) := by
    intro t
    have h7 := caseM O K Δ τ L hD ((ε : O) * s ^ 2 - 2) hτ0 hm0 c hc _ hu2 hnorm ν hν hnν r e hr
      (t * Units.mk0 g hg0)
    rw [Units.val_mul, Units.val_mk0, mul_assoc] at h7
    exact h7
  have hK2 : kapSum O c (dLam (ν * p) z) 1 = ∑ᶠ t : Kˣ ⧸ NE τ, hs (τ ^ 2 - 4) ((Quotient.out t : Kˣ) : K)
      * pcount O τ (((Quotient.out t : Kˣ) : K) * (g * (τ ^ 2 - 4))) := by
    unfold UpperTheory.V.Z.Sym.Loc.kapSum
    refine finsum_congr (fun t => ?_)
    congr 1
    rw [(datIso O K Δ τ c (dLam (ν * p) z) (((Quotient.out t : Kˣ) : K) • (1 : EL Δ τ)) y).1, hy1, hy2,
      hcase]
  have hinvf : ∀ t ∈ NE τ, ∀ x : Kˣ, (fun t : Kˣ => pcount O τ (t : K)) (t * x)
      = (fun t : Kˣ => pcount O τ (t : K)) x := by
    intro t ht x
    simp only [Units.val_mul]
    exact pNorm O K Δ τ L t ht x
  have hSS := (sumShift O K Δ τ L hD (fun t : Kˣ => pcount O τ (t : K)) hinvf
    (Units.mk0 g hg0 * Units.mk0 _ hD)).2.1
  simp only [Units.val_mul, Units.val_mk0] at hSS
  have hPK := pKappa O K Δ τ L hD ⟨_, hτ0⟩ s (-(u0 * ε)) hDalg
  rw [hPK] at hSS
  rw [hSS] at hK2
  have hsDD : hs (τ ^ 2 - 4) (τ ^ 2 - 4) = 1 := by
    have h8 : hs (τ ^ 2 - 4) (-(τ ^ 2 - 4)) = 1 := by
      unfold UpperTheory.V.Z.Sym.Loc.hs
      rw [if_pos ⟨0, 1, by ring⟩]
    have h9 : hs (τ ^ 2 - 4) (-1) = 1 := hL.2.1 _ _ hDv ⟨-1, 1, one_ne_zero, by simp⟩
    have h10 := hsMul O K Δ L (τ ^ 2 - 4) (-1) (-(τ ^ 2 - 4)) hD (by norm_num) (neg_ne_zero.2 hD)
    rw [show (-1 : K) * -(τ ^ 2 - 4) = τ ^ 2 - 4 by ring, h9, h8, one_mul] at h10
    exact h10
  have e2v : EvenVal O (algebraMap O K (2 * v)) := by
    have h11 := hevu (L.two.unit * v)
    simpa using h11
  have et0 : EvenVal O (algebraMap O K (2 * xr + ((ε : O) * s ^ 2 - 2) * yr)) := by
    have h11 := hevu ht0u.unit
    simpa using h11
  have hgb : g / b = algebraMap O K (2 * v) * (algebraMap O K (2 * xr + ((ε : O) * s ^ 2 - 2) * yr))⁻¹ := by
    rw [hgdef, hpim, htr, map_mul, map_ofNat]
    field_simp
  have hevgb : EvenVal O (g / b) := by
    rw [hgb]
    exact PS.even_mul e2v (PS.even_inv et0)
  have hsDg : hs (τ ^ 2 - 4) (g * (τ ^ 2 - 4)) = hs (τ ^ 2 - 4) b := by
    rw [hsMul O K Δ L _ _ _ hD hg0 hD, hsDD, mul_one,
      show g = g / b * b by field_simp,
      hsMul O K Δ L _ _ _ hD (div_ne_zero hg0 hb0) hb0, hL.2.1 _ _ hDv hevgb, one_mul]
  have heps2 : eps τ (ν * p) = hs Δ (algebraMap O K s) * hs (τ ^ 2 - 4) b := by
    unfold UpperTheory.V.Z.Sym.Loc.eps
    rw [show (2 : K) + τ + QuadraticAlgebra.trace (ν * p) = algebraMap O K w * b by rw [h2τ, hT2],
      hsMul O K Δ L _ _ _ hD (hunit _ w.isUnit) hb0, hsMul O K Δ L _ _ _ hΔ (hunit _ w.isUnit) hb0,
      hL.2.1 _ _ hDv (hevu w), hL.2.1 _ _ L.even (hevu w), hsb]
    ring
  have heps1 : eps τ lam * eps τ lam = 1 := by
    unfold UpperTheory.V.Z.Sym.Loc.eps
    linear_combination (hs Δ (2 + τ + QuadraticAlgebra.trace lam) * hs Δ (2 + τ + QuadraticAlgebra.trace lam))
      * hs_sq (τ ^ 2 - 4) (2 + τ + QuadraticAlgebra.trace lam) + hs_sq Δ (2 + τ + QuadraticAlgebra.trace lam)
  have hnνp : QuadraticAlgebra.norm (ν * p) = 2 + τ := by
    rw [map_mul, hnν, hnp, ← h2τ]
    ring
  have hTνp : 2 + τ + QuadraticAlgebra.trace (ν * p) ≠ 0 := by
    rw [h2τ, hT2]
    exact mul_ne_zero (hunit _ w.isUnit) hb0
  have hM := kapMove O K Δ τ L hD c hc0 z hz lam (ν * p) hlam hnνp hT hTνp
  rw [hK2, heps2, hsDg] at hM
  linear_combination (-(kapSum O c (dLam lam z) 1)) * heps1 + eps τ lam * hM
    + (eps τ lam * hs Δ (algebraMap O K s) * (Nat.card (O ⧸ Ideal.span {s}) : ℂ)) * hs_sq (τ ^ 2 - 4) b
