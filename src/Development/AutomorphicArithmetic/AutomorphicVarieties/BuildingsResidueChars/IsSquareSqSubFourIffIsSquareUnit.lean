module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIwahoriTorusProjection

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSquareSqSubFourIffIsSquareUnit
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.isSquare_sq_sub_four_iff_isSquare_unit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → (IsSquare (τ ^ 2 - 4) ↔ IsSquare (e : O)) := by
  intro O K _ _ _ _ _ Δ τ L hD π n e h x hc
  haveI := L.frac
  have E : (ω - algebraMap O (Etau K τ) h) * (ω - algebraMap O (Etau K τ) h) = algebraMap O (Etau K τ) (π ^ n * π ^ n * e) := by
    rw [hc.om, add_sub_cancel_left]
    simp only [yy, smul_mul_smul_comm, hc.sq]
    simp only [algebraMap_etau (O := O), Algebra.smul_def, map_mul]
  have Er := congrArg QuadraticAlgebra.re E
  have Ei := congrArg QuadraticAlgebra.im E
  simp [algebraMap_etau] at Er Ei
  have hτ : τ = 2 * algebraMap O K h := by linear_combination Ei
  have key : τ ^ 2 - 4 = (2 * algebraMap O K π ^ n) ^ 2 * algebraMap O K (e : O) := by
    rw [hτ]
    linear_combination 4 * Er
  constructor
  · rintro ⟨r, hr⟩
    have hq : 2 * algebraMap O K π ^ n ≠ 0 := by
      intro h0
      apply hD
      rw [key, h0]
      ring
    have hsq : (r / (2 * algebraMap O K π ^ n)) ^ 2 = algebraMap O K (e : O) := by
      rw [div_pow, sq r, ← hr, key]
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hq)
    obtain ⟨b, hb⟩ := sq_int L _ _ hsq
    refine ⟨b, IsFractionRing.injective O K ?_⟩
    rw [map_mul, hb, ← hsq]
    ring
  · rintro ⟨b, hb⟩
    refine ⟨2 * algebraMap O K π ^ n * algebraMap O K b, ?_⟩
    rw [key, hb, map_mul]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CardQuotientSpanUniformizerPow
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

private theorem card_step {O : Type} [CommRing O] [IsDomain O] (π : O) (h0 : π ≠ 0) (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {π ^ (n + 1)}) =
      Nat.card (O ⧸ Ideal.span {π ^ n}) * Nat.card (O ⧸ Ideal.span {π}) := by
  have hrange : (AddMonoidHom.mulLeft (π ^ n)).range = (Ideal.span {π ^ n}).toAddSubgroup := by
    ext r
    simp [Ideal.mem_span_singleton', mul_comm]
  have hcomap : (Ideal.span {π ^ (n + 1)}).toAddSubgroup.comap (AddMonoidHom.mulLeft (π ^ n)) =
      (Ideal.span {π}).toAddSubgroup := by
    ext r
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
    show π ^ (n + 1) ∣ π ^ n * r ↔ π ∣ r
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n h0)]
  have hle : (Ideal.span {π ^ (n + 1)}).toAddSubgroup ≤ (Ideal.span {π ^ n}).toAddSubgroup := by
    intro r hr
    simp only [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hr ⊢
    exact (pow_dvd_pow π (Nat.le_succ n)).trans hr
  show (Ideal.span {π ^ (n + 1)}).toAddSubgroup.index =
    (Ideal.span {π ^ n}).toAddSubgroup.index * (Ideal.span {π}).toAddSubgroup.index
  rw [← AddSubgroup.relIndex_mul_index hle, ← hcomap, AddSubgroup.index_comap, hrange, mul_comm]

theorem UpperTheory.card_quotient_span_uniformizer_pow :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → ∀ π : O, Irreducible π → ∀ n : ℕ, Nat.card (O ⧸ Ideal.span {π ^ n}) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  intro O K _ _ _ _ _ Δ τ hL π hπ n
  have hres : Nat.card (IsLocalRing.ResidueField O) = Nat.card (O ⧸ Ideal.span {π}) := by
    rw [← hπ.maximalIdeal_eq]
    rfl
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.span_singleton_one]
    show (⊤ : Ideal O).toAddSubgroup.index = 1
    simp
  | succ k ih =>
    rw [card_step π hπ.ne_zero k, ih, hres, pow_succ]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.StabilizerOrderLevelAntitoneLeUnits
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

section

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

private theorem yy_val (π : O) (m : ℕ) (x : Etau K τ) :
    yy π m x = algebraMap O (Etau K τ) (π ^ m) * x := by
  rw [yy, algebraMap_etau (O := O), Algebra.smul_def]

private theorem mem_ord {y w : Etau K τ} :
    w ∈ Ord O y ↔ ∃ a b : O, w = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y := by
  change w ∈ (Submodule.span O {1, y} : Submodule O (Etau K τ)) ↔ _
  rw [Submodule.mem_span_pair]
  simp only [Algebra.smul_def, mul_one, eq_comm]

private theorem one_mem_ord (y : Etau K τ) : (1 : Etau K τ) ∈ Ord O y :=
  mem_ord.2 ⟨1, 0, by simp⟩

private theorem ord_mul {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    {v w : Etau K τ} (hv : v ∈ Ord O y) (hw : w ∈ Ord O y) : v * w ∈ Ord O y := by
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hv
  obtain ⟨p, q, rfl⟩ := mem_ord.1 hw
  refine mem_ord.2 ⟨a * p + b * q * c, a * q + b * p, ?_⟩
  simp only [map_add (f := _), map_mul]
  linear_combination (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) q) * hy

private theorem ord_mono (π : O) (m : ℕ) (x : Etau K τ) :
    Ord O (yy π (m + 1) x) ⊆ Ord O (yy π m x) := by
  intro w hw
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hw
  refine mem_ord.2 ⟨a, b * π, ?_⟩
  simp only [yy_val, pow_succ, map_mul]
  ring

private theorem yy_sq {π e : O} {x : Etau K τ} (h : x * x = algebraMap O (Etau K τ) e) (m : ℕ) :
    yy π m x * yy π m x = algebraMap O (Etau K τ) (π ^ m * π ^ m * e) := by
  simp only [yy_val, map_mul]
  linear_combination (algebraMap O (Etau K τ) (π ^ m) * algebraMap O (Etau K τ) (π ^ m)) * h

private theorem unit_mem {y : Etau K τ} {u : (Etau K τ)ˣ} (hu : u ∈ Hu O y) :
    (u : Etau K τ) ∈ Ord O y ∧ ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := by
  have h : PS.ml u (Ord O y) = Ord O y := hu
  refine ⟨h.subset ⟨1, one_mem_ord y, mul_one _⟩, ?_⟩
  have := PS.mem_ml.1 (h.symm.subset (one_mem_ord (O := O) y))
  rwa [mul_one] at this

private theorem hu_of_mem {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    {u : (Etau K τ)ˣ} (h1 : (u : Etau K τ) ∈ Ord O y)
    (h2 : ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y) : u ∈ Hu O y := by
  change PS.ml u (Ord O y) = Ord O y
  ext w
  rw [PS.mem_ml]
  refine ⟨fun hw => ?_, fun hw => ord_mul hy h2 hw⟩
  have := ord_mul hy h1 hw
  rwa [Units.mul_inv_cancel_left] at this

private theorem ord_int {y w : Etau K τ} (hy : IsIntegral O y) (hw : w ∈ Ord O y) :
    IsIntegral O w := by
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hw
  exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul hy)

end

theorem UpperTheory.stabilizer_order_level_antitone_le_units :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ m : ℕ, Hu O (yy π (m + 1) x) ≤ Hu O (yy π m x) ∧ Hu O (yy π m x) ≤ Gu O τ := by
  intro O K _ _ _ _ _ Δ τ _ _ π n e h x c m
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨h1, h2⟩ := unit_mem hu
    exact hu_of_mem (yy_sq c.sq m) (ord_mono π m x h1) (ord_mono π m x h2)
  · obtain ⟨h1, h2⟩ := unit_mem hu
    have hi : IsIntegral O (yy π m x) := by
      rw [yy_val]
      exact isIntegral_algebraMap.mul c.gen.int
    exact ⟨ord_int hi h1, ord_int hi h2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsSectionAutomorphicSpaceWithPrescribedValue
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLinearSectionAutomorphicFunctionsOfFree
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.exists_linear_section_automorphicFunctions_of_free :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub), X.Free τ θ U → ∀ (c N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) → ∀ tt : Gp → X.I.T, (∀ b ∈ X.I.Iw 0, ∀ s : X.I.T, tt (s * b) = s * tt b) → ∃ s : (Fin N × Fin m → A) →ₗ[A] X.Fn A m, ∀ v γ i, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, s v (X.glob γ * x i * ((u : Ga), b)) = (((θ (tt b))⁻¹ : Aˣ) : A) • ((τ u⁻¹ : Matrix (Fin m) (Fin m) A) *ᵥ fun j => v (i, j)) := by
  intro Γ Ga Gp _ _ _ X A _ m τ θ U hF c N x hcov hsep tt htt
  choose γ0 i0 u0 hu0 b0 hb0 hg using hcov
  have hle : X.I.Iw c ≤ X.I.Iw 0 := sup_le_sup_left (X.I.Nm_anti (Nat.zero_le c)) _
  refine ⟨{ toFun := fun v g => (((θ (tt (b0 g)))⁻¹ : Aˣ) : A) •
              ((τ (u0 g)⁻¹ : Matrix (Fin m) (Fin m) A) *ᵥ fun j => v (i0 g, j))
            map_add' := fun v w => ?_
            map_smul' := fun a v => ?_ }, fun v γ i u hu b hb => ?_⟩
  · funext g
    rw [Pi.add_apply, ← smul_add, ← mulVec_add]
    rfl
  · funext g
    rw [Pi.smul_apply, RingHom.id_apply, smul_comm a, ← mulVec_smul _ a]
    rfl
  · have h := hg (X.glob γ * x i * ((u : Ga), b))
    have hu1 := hu0 (X.glob γ * x i * ((u : Ga), b))
    have hb1 := hb0 (X.glob γ * x i * ((u : Ga), b))
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    generalize γ0 (X.glob γ * x i * ((u : Ga), b)) = γ1 at h
    generalize i0 (X.glob γ * x i * ((u : Ga), b)) = i1 at h ⊢
    generalize u0 (X.glob γ * x i * ((u : Ga), b)) = u1 at h hu1 ⊢
    generalize b0 (X.glob γ * x i * ((u : Ga), b)) = b1 at h hb1 ⊢
    have hw : ((((u1 * u⁻¹ : X.Ub) : Ga), b1 * b⁻¹) : Ga × Gp) = ((u1 : Ga), b1) * ((u : Ga), b)⁻¹ := rfl
    have hwU : u1 * u⁻¹ ∈ U := mul_mem hu1 (inv_mem hu)
    have hwI : b1 * b⁻¹ ∈ X.I.Iw c := mul_mem hb1 (inv_mem hb)
    have hi : i1 = i := by
      refine hsep i1 i (γ⁻¹ * γ1) _ hwU _ hwI ?_
      rw [hw, map_mul, map_inv, ← mul_assoc, mul_assoc (X.glob γ)⁻¹, mul_assoc (X.glob γ)⁻¹, ← h]
      group
    subst hi
    obtain ⟨-, hs, he⟩ := hF (x i1) (γ1⁻¹ * γ) _ hwU _ (hle hwI) (by
      rw [hw, map_mul, map_inv, mul_assoc, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_assoc, ← h]
      group)
    have ht : tt b1 = ⟨b1 * b⁻¹, hs⟩ * tt b := by
      rw [← htt b (hle hb) ⟨b1 * b⁻¹, hs⟩]
      simp
    have hτ : (τ u1⁻¹ : Matrix (Fin m) (Fin m) A) =
        (θ ⟨b1 * b⁻¹, hs⟩ : A) • (τ u⁻¹ : Matrix (Fin m) (Fin m) A) := by
      have e : u⁻¹ = u1⁻¹ * (u1 * u⁻¹) := by group
      rw [e, map_mul, Units.val_mul, ← Matrix.mul_smul, he, Matrix.mul_one]
    rw [ht, hτ, map_mul, smul_mulVec, smul_smul, ← Units.val_mul]
    congr 2
    rw [mul_inv, mul_right_comm, inv_mul_cancel, one_mul]
end

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.exists_section_automorphicSpace_with_prescribed_values :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ U : Subgroup X.Ub, X.Free τ θ U → ∀ (c N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) → ∃ s : (Fin N × Fin m → A) →ₗ[A] X.Fn A m, ∀ v, s v ∈ X.Sp τ θ U ∧ (∀ i j, s v (x i) j = v (i, j)) ∧ ∀ k : ℕ, (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → (θ t : A) - 1 ∈ maximalIdeal A ^ k) → ∀ y ∈ X.I.Nm c, X.rp A m y (s v) - s v ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ hθ U hF c N x hcov huniq
  unfold Iwa.ContChar at hθ
  obtain ⟨tt, htt1, htt⟩ := UpperTheory.exists_iwahori_torus_projection Gp X.I
  obtain ⟨s, hs⟩ := UpperTheory.exists_linear_section_automorphicFunctions_of_free Γ Ga Gp X A m τ θ U hF c N x hcov huniq tt
    (fun b hb t => ((htt b hb).1 t).1)
  have hN_le : X.I.N ≤ X.I.Iw c := by
    unfold Iwa.Iw
    exact le_sup_left.trans le_sup_left
  have hT_le : X.I.T ≤ X.I.Iw c := by
    unfold Iwa.Iw
    exact le_sup_right.trans le_sup_left
  have hNm_le : X.I.Nm c ≤ X.I.Iw c := by
    unfold Iwa.Iw
    exact le_sup_right
  have hIw0 : X.I.Iw c ≤ X.I.Iw 0 := by
    unfold Iwa.Iw
    exact sup_le_sup_left (X.I.Nm_anti (Nat.zero_le c)) _
  have key : ∀ (k : ℕ) (a e w : A), e - 1 ∈ maximalIdeal A ^ k → a * (e * w) - a * w ∈ maximalIdeal A ^ k := by
    intro k a e w h
    rw [show a * (e * w) - a * w = (a * w) * (e - 1) by ring]
    exact Ideal.mul_mem_left _ _ h
  have hright : ∀ (γ : Γ) (i : Fin N) (u : X.Ub) (b y : Gp),
      X.glob γ * x i * ((u : Ga), b) * (1, y) = X.glob γ * x i * ((u : Ga), b * y) := by
    intro γ i u b y
    rw [mul_assoc]
    exact congrArg _ (Prod.ext (mul_one _) rfl)
  have hdiff : ∀ v (k c' : ℕ), c ≤ c' → (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c' → (θ t : A) - 1 ∈ maximalIdeal A ^ k) →
      ∀ y ∈ X.I.Nm c', ∀ g j, s v (g * (1, y)) j - s v g j ∈ maximalIdeal A ^ k := by
    intro v k c' hcc' hk y hy g j
    obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
    have hb0 : b ∈ X.I.Iw 0 := hIw0 hb
    have hyc : y ∈ X.I.Nm c := X.I.Nm_anti hcc' hy
    obtain ⟨s0, hs0, hts⟩ := (htt b hb0).2.2 c' y hy
    have hby : b * y ∈ X.I.Iw c := mul_mem hb (hNm_le hyc)
    rw [hright, hs v γ i u hu (b * y) hby, hs v γ i u hu b hb, hts, map_mul, mul_inv, Units.val_mul, mul_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    apply key
    have h := hk s0 hs0
    have hinv := Units.inv_mul (θ s0)
    have : (((θ s0)⁻¹ : Aˣ) : A) - 1 = -(((θ s0)⁻¹ : Aˣ) : A) * ((θ s0 : A) - 1) := by
      linear_combination hinv
    rw [this]
    exact Ideal.mul_mem_left _ _ h
  refine ⟨s, fun v => ⟨?_, ?_, ?_⟩⟩
  · unfold Frame.Sp Frame.Amb
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · show (_ ∧ _ ∧ _ ∧ _)
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro γ' g
        obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
        rw [show X.glob γ' * (X.glob γ * x i * ((u : Ga), b)) = X.glob (γ' * γ) * x i * ((u : Ga), b) by
          rw [map_mul]; simp only [mul_assoc], hs v _ i u hu b hb, hs v γ i u hu b hb]
      · unfold fixd
        show ∀ n ∈ X.I.N, _
        intro n hn
        funext g
        show s v (g * (1, n)) = s v g
        obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
        rw [hright, hs v γ i u hu (b * n) (mul_mem hb (hN_le hn)), hs v γ i u hu b hb,
          (htt b (hIw0 hb)).2.1 n hn]
      · intro t
        funext g
        show s v (g * (1, (t : Gp))) = _
        obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
        rw [hright, hs v γ i u hu (b * t) (mul_mem hb (hT_le t.2)), Pi.smul_apply, hs v γ i u hu b hb,
          ((htt b (hIw0 hb)).1 t).2, map_mul, mul_inv, Units.val_mul,
          mul_comm (((θ (tt b))⁻¹ : Aˣ) : A), mul_smul]
      · intro k
        obtain ⟨c0, hc0⟩ := hθ k
        exact ⟨max c c0, fun y hy g j => hdiff v k (max c c0) (le_max_left _ _)
          (fun t ht => hc0 t (X.I.Tc_anti (le_max_right _ _) ht)) y hy g j⟩
    · unfold fixd
      show ∀ u' ∈ U, _
      intro u' hu'
      funext g
      rw [Frame.ra_apply]
      obtain ⟨γ, i, u, hu, b, hb, rfl⟩ := hcov g
      rw [show X.glob γ * x i * ((u : Ga), b) * ((u' : Ga), 1) =
            X.glob γ * x i * (((u * u' : X.Ub) : Ga), b) by
          rw [mul_assoc]; exact congrArg _ (Prod.ext rfl (mul_one _)),
        hs v γ i (u * u') (mul_mem hu hu') b hb, hs v γ i u hu b hb, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, show u' * (u * u')⁻¹ = u⁻¹ by group]
  · intro i j
    have e : x i = X.glob 1 * x i * (((1 : X.Ub) : Ga), (1 : Gp)) := by simp
    rw [e, hs v 1 i 1 U.one_mem 1 (X.I.Iw c).one_mem, htt1]
    simp
  · intro k hk y hy
    unfold Frame.valIn
    rw [Submodule.mem_pi]
    intro g _
    rw [Submodule.mem_pi]
    intro j _
    exact hdiff v k c le_rfl hk y hy g j
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RelIndexStabilizerSuccEqCardResidueField
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

namespace UpperTheory.HilbertUnitGroup

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {τ : K}

private theorem mem_ord {y w : Etau K τ} :
    w ∈ Ord O y ↔ ∃ a b : O, w = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y := by
  change w ∈ Submodule.span O {1, y} ↔ _
  rw [Submodule.mem_span_pair]
  simp only [Algebra.smul_def, mul_one, eq_comm]

private theorem ord_mul {y v w : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    (hv : v ∈ Ord O y) (hw : w ∈ Ord O y) : v * w ∈ Ord O y := by
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hv
  obtain ⟨a', b', rfl⟩ := mem_ord.1 hw
  refine mem_ord.2 ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
  simp only [map_add (f := _), map_mul]
  linear_combination (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) b') * hy

private theorem mem_Hu {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c) {u : (Etau K τ)ˣ} :
    u ∈ Hu O y ↔ (u : Etau K τ) ∈ Ord O y ∧ ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := by
  have one : (1 : Etau K τ) ∈ Ord O y := mem_ord.2 ⟨1, 0, by simp⟩
  have key : ∀ v : (Etau K τ)ˣ, v ∈ Hu O y → ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := fun v hv => by
    have h1 : (1 : Etau K τ) ∈ PS.ml v (Ord O y) := by
      rw [show PS.ml v (Ord O y) = Ord O y from hv]; exact one
    simpa using PS.mem_ml.1 h1
  refine ⟨fun h => ⟨by simpa using key _ (inv_mem h), key _ h⟩, fun ⟨h1, h2⟩ => ?_⟩
  change PS.ml u (Ord O y) = Ord O y
  ext w
  rw [PS.mem_ml]
  refine ⟨fun hw => ?_, fun hw => ord_mul hy h2 hw⟩
  simpa using ord_mul hy h1 hw

private theorem uniq (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {a b a' b' : O}
    (h : algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y =
      algebraMap O (Etau K τ) a' + algebraMap O (Etau K τ) b' * y) : a = a' ∧ b = b' := by
  rw [algebraMap_etau a, algebraMap_etau b, algebraMap_etau a', algebraMap_etau b'] at h
  have im_algebraMap_add_mul : ∀ p q : K, (algebraMap K (Etau K τ) p + algebraMap K (Etau K τ) q * y).im = q * y.im := by
    intro p q; simp
  have kre : ∀ p q : K, (algebraMap K (Etau K τ) p + algebraMap K (Etau K τ) q * y).re = p + q * y.re := by
    intro p q; simp
  have him := congrArg QuadraticAlgebra.im h
  have hre := congrArg QuadraticAlgebra.re h
  rw [im_algebraMap_add_mul, im_algebraMap_add_mul] at him
  rw [kre, kre] at hre
  have hb := mul_right_cancel₀ h0 him
  rw [hb] at hre
  exact ⟨hinj (add_right_cancel hre), hinj hb⟩

private theorem isUnit_fst (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {c : O}
    (hy : y * y = algebraMap O (Etau K τ) c) (hc : ¬ IsUnit c) {u : (Etau K τ)ˣ} (hu : u ∈ Hu O y) {a b : O}
    (e : (u : Etau K τ) = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y) : IsUnit a := by
  obtain ⟨a', b', e'⟩ := mem_ord.1 ((mem_Hu hy).1 hu).2
  have h1 : algebraMap O (Etau K τ) (a * a' + b * b' * c) + algebraMap O (Etau K τ) (a * b' + a' * b) * y =
      algebraMap O (Etau K τ) 1 + algebraMap O (Etau K τ) 0 * y := by
    have := u.mul_inv
    rw [e, e'] at this
    simp only [map_add (f := _), map_mul, map_one, map_zero]
    linear_combination this - (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) b') * hy
  have h2 := (uniq hinj h0 h1).1
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h2 with h3 | h3
  · exact isUnit_of_mul_isUnit_left h3
  · exact absurd (isUnit_of_mul_isUnit_right h3) hc

private theorem step (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {c π : O}
    (hπ : Irreducible π) (hy : y * y = algebraMap O (Etau K τ) c) (hc : π ∣ c) :
    (Hu O (algebraMap O (Etau K τ) π * y)).relIndex (Hu O y) = Nat.card (IsLocalRing.ResidueField O) := by
  classical
  have hcu : ¬ IsUnit c := fun h => hπ.not_isUnit (isUnit_of_dvd_unit hc h)
  have hy' : (algebraMap O (Etau K τ) π * y) * (algebraMap O (Etau K τ) π * y) =
      algebraMap O (Etau K τ) (π * π * c) := by
    simp only [map_mul]; linear_combination (algebraMap O (Etau K τ) π * algebraMap O (Etau K τ) π) * hy
  have hπ0 : IsLocalRing.residue O π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]; exact hπ.not_isUnit
  have hc0 : IsLocalRing.residue O c = 0 := by
    obtain ⟨d, rfl⟩ := hc; rw [map_mul, hπ0, zero_mul]
  have ex : ∀ u : Hu O y, ∃ p : O × O, ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) p.1 + algebraMap O (Etau K τ) p.2 * y := fun u => by
    obtain ⟨a, b, e⟩ := mem_ord.1 ((mem_Hu hy).1 u.2).1
    exact ⟨(a, b), e⟩
  choose P hP using ex
  let g : Hu O y → IsLocalRing.ResidueField O := fun u =>
    IsLocalRing.residue O (P u).2 / IsLocalRing.residue O (P u).1
  have gval : ∀ (u : Hu O y) (a b : O), ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y →
      g u = IsLocalRing.residue O b / IsLocalRing.residue O a := fun u a b e => by
    obtain ⟨h1, h2⟩ := uniq hinj h0 ((hP u).symm.trans e)
    simp only [g, h1, h2]
  have resne : ∀ (u : Hu O y) (a b : O), ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y → IsLocalRing.residue O a ≠ 0 := fun u a b e =>
    ((isUnit_fst hinj h0 hy hcu u.2 e).map (IsLocalRing.residue O)).ne_zero
  have gmul : ∀ u v : Hu O y, g (u * v) = g u + g v := fun u v => by
    have eu := hP u
    have ev := hP v
    have e : (((u * v : Hu O y) : (Etau K τ)ˣ) : Etau K τ) =
        algebraMap O (Etau K τ) ((P u).1 * (P v).1 + (P u).2 * (P v).2 * c) +
          algebraMap O (Etau K τ) ((P u).1 * (P v).2 + (P v).1 * (P u).2) * y := by
      rw [Subgroup.coe_mul, Units.val_mul, eu, ev]
      simp only [map_add (f := _), map_mul]
      linear_combination (algebraMap O (Etau K τ) (P u).2 * algebraMap O (Etau K τ) (P v).2) * hy
    have n1 := resne u _ _ eu
    have n2 := resne v _ _ ev
    rw [gval _ _ _ e, gval _ _ _ eu, gval _ _ _ ev]
    simp only [map_add (f := _), map_mul, hc0, mul_zero, add_zero]
    field_simp
    ring
  let f : Hu O y →* Multiplicative (IsLocalRing.ResidueField O) :=
    MonoidHom.mk' (fun u => Multiplicative.ofAdd (g u)) (fun u v => by rw [gmul, ofAdd_add])
  have fval : ∀ u, f u = Multiplicative.ofAdd (g u) := fun _ => rfl
  have down : ∀ u : Hu O y, f u = 1 → ((u : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O (algebraMap O (Etau K τ) π * y) := fun u hu => by
    have h1 : g u = 0 := by simpa [fval] using hu
    have e := hP u
    rw [gval _ _ _ e, div_eq_zero_iff, or_iff_left (resne u _ _ e), IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton] at h1
    obtain ⟨d, hd⟩ := h1
    refine mem_ord.2 ⟨(P u).1, d, ?_⟩
    rw [e, hd, map_mul]
    ring
  have hker : f.ker = (Hu O (algebraMap O (Etau K τ) π * y)).subgroupOf (Hu O y) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Hu hy']
    refine ⟨fun hu => ⟨down u hu, ?_⟩, fun ⟨h1, _⟩ => ?_⟩
    · have := down u⁻¹ (by rw [map_inv, hu, inv_one])
      simpa using this
    · obtain ⟨a, b, e⟩ := mem_ord.1 h1
      have e' : ((u : (Etau K τ)ˣ) : Etau K τ) =
          algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) (b * π) * y := by
        rw [e, map_mul]; ring
      rw [fval, gval _ _ _ e', map_mul, hπ0, mul_zero, zero_div, ofAdd_zero]
  have hsurj : Function.Surjective f := fun r => by
    obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective (Multiplicative.toAdd r)
    have hn : IsUnit (1 - s * s * c) := by
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := 1 - s * s * c) (b := s * s * c) (by ring) with h | h
      · exact h
      · exact absurd (isUnit_of_mul_isUnit_right h) hcu
    obtain ⟨ν, hν⟩ := hn
    have hν' : algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * (1 - algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) c) = 1 := by
      rw [← map_mul, ← map_mul, ← map_one (algebraMap O (Etau K τ)), ← map_sub, ← hν, ← map_mul, Units.inv_mul]
    let w : (Etau K τ)ˣ :=
      { val := algebraMap O (Etau K τ) 1 + algebraMap O (Etau K τ) s * y
        inv := algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) + algebraMap O (Etau K τ) (-(((ν⁻¹ : Oˣ) : O) * s)) * y
        val_inv := by
          simp only [map_neg, map_mul, map_one]
          linear_combination hν' - (algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s) * hy
        inv_val := by
          simp only [map_neg, map_mul, map_one]
          linear_combination hν' - (algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s) * hy }
    have hw : w ∈ Hu O y := (mem_Hu hy).2 ⟨mem_ord.2 ⟨1, s, rfl⟩, mem_ord.2 ⟨_, _, rfl⟩⟩
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [fval, gval ⟨w, hw⟩ 1 s rfl, map_one, div_one, hs, ofAdd_toAdd]
  have hr : f.range = ⊤ := MonoidHom.range_eq_top.2 hsurj
  change ((Hu O (algebraMap O (Etau K τ) π * y)).subgroupOf (Hu O y)).index = _
  rw [← hker, Subgroup.index_ker, hr, Subgroup.card_top]
  exact Nat.card_congr Multiplicative.toAdd

end UpperTheory.HilbertUnitGroup

theorem UpperTheory.relIndex_stabilizer_succ_eq_card_residueField :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ m : ℕ, 1 ≤ m → (Hu O (yy π (m + 1) x)).relIndex (Hu O (yy π m x)) = Nat.card (IsLocalRing.ResidueField O) := by
  intro O K _ _ _ _ _ Δ τ L _ π n e h x hC m hm
  haveI := L.frac
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hπ := hC.irr
  have hp : algebraMap O K (π ^ m) ≠ 0 := fun h0 =>
    pow_ne_zero m hπ.ne_zero (hinj (by rw [h0, map_zero]))
  have h0 : (yy π m x).im ≠ 0 := by
    rw [yy, im_smul, smul_eq_mul]
    exact mul_ne_zero hp hC.gen.im_ne
  have hsm : ∀ k : ℕ, yy π k x = algebraMap O (Etau K τ) (π ^ k) * x := fun k => by
    rw [yy, Algebra.smul_def, ← algebraMap_etau]
  have hy : yy π m x * yy π m x = algebraMap O (Etau K τ) (π ^ m * π ^ m * (e : O)) := by
    rw [hsm, map_mul, map_mul, ← hC.sq]; ring
  have hc : π ∣ π ^ m * π ^ m * (e : O) :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _) _
  have e1 : yy π (m + 1) x = algebraMap O (Etau K τ) π * yy π m x := by
    rw [hsm, hsm, pow_succ, map_mul]; ring
  rw [e1]
  exact UpperTheory.HilbertUnitGroup.step hinj h0 hπ hy hc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicFormWithPrescribedIwahoriValues
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIwahoriCharacterExtendingTorusCharacter
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.exists_iwahori_character_extending_torus_character :
    ∀ (G : Type) [Group G] (I : Iwa G) (B : Type) [CommGroup B] (c : ℕ) (φ : I.T →* B), (∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) → ∃ ψ : I.Iw c →* B, ∀ b : I.Iw c, ((b : G) ∈ I.N → ψ b = 1) ∧ ((b : G) ∈ I.Nm c → ψ b = 1) ∧ ∀ hb : (b : G) ∈ I.T, ψ b = φ ⟨b, hb⟩ := by
  intro G _ I B _ c φ hφ
  obtain ⟨tt, h1, htt⟩ := UpperTheory.exists_iwahori_torus_projection G I
  have hle : ∀ b ∈ I.Iw c, b ∈ I.Iw 0 := by
    intro b hb
    obtain ⟨x, hx, t, ht, y, hy, h⟩ := (UpperTheory.V.Hi.iwMem G I c b).1.1 hb
    exact (UpperTheory.V.Hi.iwMem G I 0 b).1.2 ⟨x, hx, t, ht, y, I.Nm_anti (Nat.zero_le c) hy, h⟩
  have key : ∀ b ∈ I.Iw 0, ∀ x ∈ I.N, ∀ t : I.T, ∀ y ∈ I.Nm c,
      φ (tt (b * (x * t * y))) = φ (tt b) * φ t := by
    intro b hb x hx t y hy
    have hx0 : x ∈ I.Iw 0 :=
      (UpperTheory.V.Hi.iwMem G I 0 x).1.2 ⟨x, hx, 1, one_mem _, 1, one_mem _, by simp⟩
    have ht0 : (t : G) ∈ I.Iw 0 :=
      (UpperTheory.V.Hi.iwMem G I 0 t).1.2 ⟨1, one_mem _, t, t.2, 1, one_mem _, by simp⟩
    have hbx := mul_mem hb hx0
    obtain ⟨s, hs, e⟩ := (htt _ (mul_mem hbx ht0)).2.2 c y hy
    have e0 : b * (x * t * y) = b * x * t * y := by group
    rw [e0, e, map_mul, hφ s hs, mul_one, ((htt _ hbx).1 t).2, (htt b hb).2.1 x hx, map_mul]
  have key1 : ∀ x ∈ I.N, ∀ t : I.T, ∀ y ∈ I.Nm c, φ (tt (x * t * y)) = φ t := by
    intro x hx t y hy
    have := key 1 (one_mem _) x hx t y hy
    rwa [one_mul, h1, map_one, one_mul] at this
  refine ⟨MonoidHom.mk' (fun b => φ (tt b)) ?_, fun b => ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_⟩⟩
  · intro a b
    obtain ⟨x, hx, t, ht, y, hy, h⟩ := (UpperTheory.V.Hi.iwMem G I c b).1.1 b.2
    have e1 := key a (hle _ a.2) x hx ⟨t, ht⟩ y hy
    have e2 := key1 x hx ⟨t, ht⟩ y hy
    show φ (tt ((a : G) * b)) = φ (tt a) * φ (tt b)
    rw [h, e2]
    exact e1
  · simpa using key1 b hb 1 1 (one_mem _)
  · simpa using key1 1 (one_mem _) 1 b hb
  · simpa using key1 1 (one_mem _) ⟨b, hb⟩ 1 (one_mem _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicFunctionWithValuesOnCosetReps
theorem UpperTheory.exists_automorphic_function_with_values_on_coset_reps :
    ∀ (Γ G K A M ι : Type) [Group Γ] [Group G] [Group K] [CommRing A] [AddCommGroup M] [Module A M] (gl : Γ →* G) (j : K →* G) (ρ : Representation A K M) (x : ι → G), (∀ g, ∃ γ i k, g = gl γ * x i * j k) → (∀ i i' γ k, x i' = gl γ * x i * j k → i = i') → (∀ i γ k, gl γ * x i = x i * j k → ρ k = 1) → ∀ v : ι → M, ∃ Φ : G → M, (∀ γ g, Φ (gl γ * g) = Φ g) ∧ (∀ g k, Φ (g * j k) = ρ k⁻¹ (Φ g)) ∧ ∀ i, Φ (x i) = v i := by
  intro Γ G K A M ι _ _ _ _ _ _ gl j ρ x hcov huniq hstab v
  have key : ∀ γ i k γ' i' k', gl γ * x i * j k = gl γ' * x i' * j k' →
      i = i' ∧ ρ k⁻¹ (v i) = ρ k'⁻¹ (v i') := by
    intro γ i k γ' i' k' h
    have e : x i' = gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹) := by
      calc x i' = (gl γ')⁻¹ * (gl γ' * x i' * j k') * (j k')⁻¹ := by group
        _ = (gl γ')⁻¹ * (gl γ * x i * j k) * (j k')⁻¹ := by rw [h]
        _ = gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹) := by
          simp only [map_mul, map_inv]
          group
    have hii : i = i' := huniq i i' _ _ e
    subst hii
    refine ⟨rfl, ?_⟩
    have e2 : gl (γ'⁻¹ * γ) * x i = x i * j (k' * k⁻¹) := by
      calc gl (γ'⁻¹ * γ) * x i = (gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹)) * (j (k * k'⁻¹))⁻¹ := by group
        _ = x i * j (k' * k⁻¹) := by
          rw [← e]
          simp only [map_mul, map_inv]
          group
    have hρ : ρ (k' * k⁻¹) = 1 := hstab i _ _ e2
    have : ρ k⁻¹ = ρ k'⁻¹ := by
      calc ρ k⁻¹ = ρ (k'⁻¹ * (k' * k⁻¹)) := by group
        _ = ρ k'⁻¹ * ρ (k' * k⁻¹) := map_mul _ _ _
        _ = ρ k'⁻¹ := by rw [hρ, mul_one]
    rw [this]
  choose γf iF kF hg using hcov
  refine ⟨fun g => ρ (kF g)⁻¹ (v (iF g)), ?_, ?_, ?_⟩
  · intro γ g
    have h : gl (γf (gl γ * g)) * x (iF (gl γ * g)) * j (kF (gl γ * g)) =
        gl (γ * γf g) * x (iF g) * j (kF g) := by
      rw [← hg (gl γ * g)]
      conv_lhs => rw [hg g]
      simp only [map_mul, mul_assoc]
    exact (key _ _ _ _ _ _ h).2
  · intro g k
    have h : gl (γf (g * j k)) * x (iF (g * j k)) * j (kF (g * j k)) =
        gl (γf g) * x (iF g) * j (kF g * k) := by
      rw [← hg (g * j k)]
      conv_lhs => rw [hg g]
      simp only [map_mul, mul_assoc]
    dsimp only
    rw [(key _ _ _ _ _ _ h).2, mul_inv_rev, map_mul]
    rfl
  · intro i
    have h : gl (γf (x i)) * x (iF (x i)) * j (kF (x i)) = gl 1 * x i * j 1 := by
      rw [← hg (x i), map_one, map_one, one_mul, mul_one]
    dsimp only
    rw [(key _ _ _ _ _ _ h).2, inv_one, map_one]
    rfl
end

open IsLocalRing Matrix UpperTheory.V.Hi

private noncomputable def rhoT {A B Ω m n : Type} [Group A] [Group B] [Field Ω] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (σ : A →* GL m Ω) (ξ : B →* GL n Ω) (ψ : B →* Ωˣ) :
    Representation Ω (A × B) (Matrix m n Ω) where
  toFun k :=
    { toFun := fun v => (ψ k.2 : Ω) • ((σ k.1 : Matrix m m Ω) * v * (ξ k.2 : Matrix n n Ω)ᵀ)
      map_add' := fun v w => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c v => by simp [smul_comm c] }
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' k k' := by
    refine LinearMap.ext fun v => ?_
    simp [Matrix.mul_assoc, smul_smul, mul_comm]

private theorem rhoT_apply {A B Ω m n : Type} [Group A] [Group B] [Field Ω] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (σ : A →* GL m Ω) (ξ : B →* GL n Ω) (ψ : B →* Ωˣ) (k : A × B)
    (v : Matrix m n Ω) :
    rhoT σ ξ ψ k v = (ψ k.2 : Ω) • ((σ k.1 : Matrix m m Ω) * v * (ξ k.2 : Matrix n n Ω)ᵀ) := rfl

private theorem mulVec_row {Ω m n : Type} [Field Ω] [Fintype n] (M : Matrix n n Ω) (v : Matrix m n Ω) (i : m) :
    M *ᵥ v i = (v * Mᵀ) i := by
  ext k
  simp [Matrix.mul_apply, mulVec, dotProduct, mul_comm]

theorem UpperTheory.exists_automorphicForm_with_prescribed_iwahori_values :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (φ : X.I.T →* Oˣ) (U : Subgroup X.Ub) (c : ℕ) (θ : X.I.T →* Oˣ), (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) → (∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩) → X.Free τ θ U → ∀ (N : ℕ) (x : Fin N → Ga × Gp), (∀ g, ∃ γ i, ∃ u ∈ U, ∃ b ∈ X.I.Iw c, g = X.glob γ * x i * ((u : Ga), b)) → (∀ i j γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw c, x j = X.glob γ * x i * ((u : Ga), b) → i = j) → ∀ v : Fin N → Fin m → Fin (W.d + 1) → Ω, ∃ F ∈ X.ClO W τ U c φ, ∀ n i k, X.unt m W F i (x n) k = v n i k := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ φ U c θ hφ hθ hfree N x hcov huniq v
  obtain ⟨ψ, hψ⟩ := UpperTheory.exists_iwahori_character_extending_torus_character Gp X.I Ωˣ c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ)
    (fun t ht => by simp [hφ t ht])
  have hle : X.I.Iw c ≤ X.I.Iw 0 := sup_le_sup_left (X.I.Nm_anti (Nat.zero_le c)) _
  set τ' := (Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ with hτ'
  let j : U × X.I.Iw c →* Ga × Gp := (X.Ub.subtype.comp U.subtype).prodMap (X.I.Iw c).subtype
  have hj : ∀ k : U × X.I.Iw c, j k = (((k.1 : X.Ub) : Ga), (k.2 : Gp)) := fun _ => rfl
  obtain ⟨Φ, h1, h2, h3⟩ := UpperTheory.exists_automorphic_function_with_values_on_coset_reps Γ (Ga × Gp) (U × X.I.Iw c) Ω
    (Matrix (Fin m) (Fin (W.d + 1)) Ω) (Fin N) X.glob j
    (rhoT (τ'.comp U.subtype) (W.ξ.comp (X.I.Iw c).subtype) ψ) x
    (fun g => by
      obtain ⟨γ, i, u, hu, b, hb, h⟩ := hcov g
      exact ⟨γ, i, (⟨u, hu⟩, ⟨b, hb⟩), h⟩)
    (fun i i' γ k h => huniq i i' γ k.1 k.1.2 k.2 k.2.2 h)
    (fun i γ k h => by
      obtain ⟨hc, hb, e⟩ := hfree (x i) γ k.1 k.1.2 k.2 (hle k.2.2) h
      refine LinearMap.ext fun w => ?_
      have hξ : (W.ξ (k.2 : Gp) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) = (W.χ ⟨k.2, X.I.T_le hb⟩ : Ω) • (1 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) := by
        ext a b
        rw [W.central ⟨k.2, X.I.T_le hb⟩ hc a b]
        simp [Matrix.one_apply]
      have e' : algebraMap O Ω (θ ⟨k.2, hb⟩) • (τ' (k.1 : X.Ub) : Matrix (Fin m) (Fin m) Ω) = 1 := by
        ext a b
        have := congrArg (algebraMap O Ω) (congrFun (congrFun e a) b)
        simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply] at this ⊢
        rw [apply_ite (algebraMap O Ω), map_one, map_zero] at this
        exact this
      rw [hθ] at e'
      rw [rhoT_apply, (hψ k.2).2.2 hb]
      show algebraMap O Ω (φ ⟨k.2, hb⟩) • ((τ' (k.1 : X.Ub) : Matrix (Fin m) (Fin m) Ω) * w *
        (W.ξ (k.2 : Gp) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) = w
      rw [hξ, transpose_smul, transpose_one, Matrix.mul_smul, Matrix.mul_one, smul_smul,
        ← Matrix.smul_mul, e', Matrix.one_mul])
    (fun n => Matrix.of (v n))
  have h2' : ∀ g (k : U × X.I.Iw c), (ψ k.2 : Ω) • ((τ' (k.1 : X.Ub) : Matrix (Fin m) (Fin m) Ω) *
      Φ (g * j k) * (W.ξ (k.2 : Gp) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) = Φ g := by
    intro g k
    have := congrArg (rhoT (τ'.comp U.subtype) (W.ξ.comp (X.I.Iw c).subtype) ψ k) (h2 g k)
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one] at this
    exact this
  have hp : ∀ b : X.I.Iw c, X.rpF Ω (W.d + 1) m b
      (fun i g => (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i) =
      (((ψ b)⁻¹ : Ωˣ) : Ω) • (fun i g => (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i) := by
    intro b
    funext i g
    show (Φ (g * j (1, b)) * (W.ξ (g.2 * b) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i =
      ((((ψ b)⁻¹ : Ωˣ) : Ω) • (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ)) i
    rw [← h2' g (1, b)]
    simp [smul_smul, Matrix.mul_assoc]
  refine ⟨fun i g => (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i, ⟨⟨fun i _ γ g => ?_, fun u hu => ?_⟩,
    fun b hb => ?_, fun b hb => ?_, fun t => ?_⟩, fun n i k => ?_⟩
  · show _ = _ *ᵥ (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i
    rw [mulVec_row]
    simp [h1, Matrix.mul_assoc]
  · funext i g k
    show ((τ' u : Matrix (Fin m) (Fin m) Ω) *
      (Φ (g * j (⟨u, hu⟩, 1)) * (W.ξ (g.2 * 1) : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ)) i k = (Φ g * (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i k
    rw [← h2' g (⟨u, hu⟩, 1)]
    simp [Matrix.mul_assoc]
  · have hb' : b ∈ X.I.Iw c := Subgroup.mem_sup_left (Subgroup.mem_sup_left hb)
    have := hp ⟨b, hb'⟩
    rw [(hψ ⟨b, hb'⟩).1 hb] at this
    simpa using this
  · have hb' : b ∈ X.I.Iw c := Subgroup.mem_sup_right hb
    have := hp ⟨b, hb'⟩
    rw [(hψ ⟨b, hb'⟩).2.1 hb] at this
    simpa using this
  · have hb' : (t : Gp) ∈ X.I.Iw c := Subgroup.mem_sup_left (Subgroup.mem_sup_right t.2)
    have := hp ⟨t, hb'⟩
    rw [(hψ ⟨t, hb'⟩).2.2 t.2] at this
    exact this
  · rw [Frame.unt_apply]
    show (_ *ᵥ (Φ (x n) * (W.ξ (x n).2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)ᵀ) i) k = _
    rw [mulVec_row, Matrix.mul_assoc, ← transpose_mul, Units.inv_mul, transpose_one, Matrix.mul_one, h3]
    rfl
end
