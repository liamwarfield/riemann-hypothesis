module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.KolHom
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem opP_mul' (δ : G ℚ Ω) (a : ℕ) (x y : Ω) : opP δ a (x * y) = opP δ a x * opP δ a y := by
  simp only [opP, map_mul, mul_pow]
  exact mul_div_mul_comm _ _ _ _

private theorem opP_ne' (δ : G ℚ Ω) (a : ℕ) {x : Ω} (hx : x ≠ 0) : opP δ a x ≠ 0 :=
  div_ne_zero ((map_ne_zero δ).2 hx) (pow_ne_zero _ hx)

private theorem opP_eq' {M a : ℕ} (hM : M ≠ 0) {δ : G ℚ Ω} (hδ : Pows M a δ) {x y : Ω} (hy : y ^ M ≠ 0)
    (h : x ^ M = y ^ M) : opP δ a x = opP δ a y := by
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hy
    exact hy rfl
  have hw : (x / y) ^ M = 1 := by rw [div_pow, h, div_self hy]
  have hw0 : x / y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hw
    exact zero_ne_one hw
  have hx : x = y * (x / y) := (mul_div_cancel₀ x hy0).symm
  have h1 : opP δ a (x / y) = 1 := by
    unfold opP
    rw [hδ _ hw, div_self (pow_ne_zero _ hw0)]
  rw [hx, opP_mul', h1, mul_one]

private theorem zeta_inj' {M : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) {i j k : ZMod M}
    (h : ζ ^ i.val = ζ ^ j.val * ζ ^ k.val) : i = j + k := by
  rw [← pow_add] at h
  have h2 : ζ ^ (j.val + k.val) = ζ ^ ((j + k).val) := by
    rw [ZMod.val_add]
    conv_lhs => rw [← Nat.mod_add_div (j.val + k.val) M, pow_add, pow_mul, hζ.pow_eq_one,
      one_pow, mul_one]
  exact ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h.trans h2))

end

theorem UpperTheory.V.ML.kolHom :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n a : ℕ) [NeZero M], F * n ≠ 0 → M ∣ F → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    ∀ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ →
    (∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v) ∧ IsLocallyConstant (fun u : fixMu ℚ Ω F => κ u) ∧
    ∀ Y : Ω, Y ^ M = y → ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y → ζ ^ (κ g).val = g (opP δ a Y) / opP δ a Y / opP δ a z := by
  intro Ω _ _ _ M F n a _ hFn hMF ζ hζ δ hδ y hy hfix κ hK
  have hM : M ≠ 0 := NeZero.ne M
  have gb := galBasic Ω (F * n) hFn
  have gbF : fixMu ℚ Ω (F * n) ≤ fixMu ℚ Ω F := gb.2.2.2.2.2.2.2.2.1 F (dvd_mul_right F n)
  obtain ⟨Y₀, hY₀, hK'⟩ := hK
  have hgy : ∀ g : G ℚ Ω, g y / y ≠ 0 := fun g => div_ne_zero ((map_ne_zero g).mpr hy) hy
  have hY0 : Y₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hY₀
    exact hy hY₀.symm
  have hA : opP δ a Y₀ ≠ 0 := opP_ne' δ a hY0
  have key : ∀ Y : Ω, Y ^ M = y → ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y →
      ζ ^ (κ g).val = g (opP δ a Y) / opP δ a Y / opP δ a z := by
    intro Y hY g hg z hz
    obtain ⟨z₀, -, hz₀, hκ⟩ := hK' g hg
    have e1 : opP δ a Y = opP δ a Y₀ :=
      opP_eq' hM hδ (by rw [hY₀]; exact hy) (hY.trans hY₀.symm)
    have e2 : opP δ a z = opP δ a z₀ :=
      opP_eq' hM hδ (by rw [hz₀]; exact hgy g) (hz.trans hz₀.symm)
    rw [e1, e2]
    exact hκ
  have hmul : ∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v := by
    intro u hu v hv
    obtain ⟨zu, -, hzu, hκu⟩ := hK' u hu
    obtain ⟨zv, hzvfix, hzv, hκv⟩ := hK' v hv
    have hzu0 : zu ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM] at hzu
      exact hgy u hzu.symm
    have hzv0 : zv ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM] at hzv
      exact hgy v hzv.symm
    have huy : u y ≠ 0 := (map_ne_zero u).mpr hy
    have hz : (u zv * zu) ^ M = (u * v) y / y := by
      rw [mul_pow, ← map_pow, hzv, hzu, map_div₀, AlgEquiv.mul_apply]
      field_simp
    have euv := key Y₀ hY₀ (u * v) (mul_mem hu hv) (u zv * zu) hz
    have hcomm : δ (u zv) = u (δ zv) := gb.2.2.2.2.2.1 zv hzvfix δ u
    have hPu : opP δ a (u zv) = u (opP δ a zv) := by
      unfold opP
      rw [hcomm, map_div₀, map_pow]
    rw [opP_mul', hPu, AlgEquiv.mul_apply] at euv
    have hfixζ : u (ζ ^ (κ v).val) = ζ ^ (κ v).val := by
      apply hu
      obtain ⟨c, hc⟩ := hMF
      rw [hc, pow_mul, ← pow_mul ζ, mul_comm (κ v).val M, pow_mul, hζ.pow_eq_one, one_pow,
        one_pow]
    have ev' : ζ ^ (κ v).val = u (v (opP δ a Y₀)) / u (opP δ a Y₀) / u (opP δ a zv) := by
      rw [← hfixζ, hκv, map_div₀, map_div₀]
    have hB : opP δ a zu ≠ 0 := opP_ne' δ a hzu0
    have huA : u (opP δ a Y₀) ≠ 0 := (map_ne_zero u).mpr hA
    have huC : u (opP δ a zv) ≠ 0 := (map_ne_zero u).mpr (opP_ne' δ a hzv0)
    apply zeta_inj' hζ
    rw [euv, hκu, ev']
    field_simp
  refine ⟨hmul, ?_, key⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral ℚ (opP δ a Y₀) := (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  haveI := IntermediateField.adjoin.finiteDimensional hint
  let H : Set (G ℚ Ω) := (fixMu ℚ Ω (F * n) : Set (G ℚ Ω)) ∩
    ((IntermediateField.adjoin ℚ {opP δ a Y₀}).fixingSubgroup : Set (G ℚ Ω))
  have hHo : IsOpen H := gb.2.1.inter (IntermediateField.fixingSubgroup_isOpen _)
  have hH0 : ∀ h ∈ H, κ h = 0 := by
    rintro h ⟨h1, h2⟩
    have e := key Y₀ hY₀ h (gbF h1) 1 (by rw [one_pow, hfix h h1, div_self hy])
    have hP1 : opP δ a (1 : Ω) = 1 := by simp [opP]
    have hfx : h (opP δ a Y₀) = opP δ a Y₀ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp h2 _
        (IntermediateField.mem_adjoin_simple_self ℚ _)
    rw [hP1, hfx, div_self hA, div_one] at e
    have e0 := zeta_inj' hζ (i := κ h) (j := 0) (k := 0)
      (by rw [e, ZMod.val_zero, pow_zero, one_mul])
    simpa using e0
  have hS : IsOpen {w : fixMu ℚ Ω F | (x : G ℚ Ω)⁻¹ * w ∈ H} :=
    hHo.preimage (continuous_const.mul continuous_subtype_val)
  have hx : x ∈ {w : fixMu ℚ Ω F | (x : G ℚ Ω)⁻¹ * w ∈ H} := by
    show (x : G ℚ Ω)⁻¹ * x ∈ H
    rw [inv_mul_cancel]
    exact ⟨one_mem _, one_mem _⟩
  filter_upwards [hS.mem_nhds hx] with w hw
  have hw' : (x : G ℚ Ω)⁻¹ * w ∈ fixMu ℚ Ω F := gbF hw.1
  have e := hmul x x.2 _ hw'
  rw [mul_inv_cancel_left, hH0 _ hw, add_zero] at e
  exact e
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.DerBasic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem derivation_ne_zero (q : ℕ) (t : G ℚ Ω) {u : Ω} (hu : u ≠ 0) : der1 q t u ≠ 0 := by
  unfold der1
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ((map_ne_zero _).2 hu)

private theorem derivation_mul (q : ℕ) (t : G ℚ Ω) (u v : Ω) : der1 q t (u * v) = der1 q t u * der1 q t v := by
  unfold der1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, mul_pow]

private theorem derivation_zpow (q : ℕ) (t : G ℚ Ω) (u : Ω) (k : ℤ) : der1 q t (u ^ k) = der1 q t u ^ k := by
  unfold der1
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow₀, ← zpow_natCast ((t ^ i) u ^ k) i, ← zpow_natCast ((t ^ i) u) i, ← zpow_mul, ← zpow_mul,
    mul_comm]

private theorem derivation_galois_equivariant (q : ℕ) (t g : G ℚ Ω) (u : Ω) (h : ∀ s : G ℚ Ω, g (s u) = s (g u)) :
    g (der1 q t u) = der1 q t (g u) := by
  unfold der1
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, h]

private theorem der_mul (τ : ℕ → G ℚ Ω) (L : List ℕ) (u v : Ω) : der τ L (u * v) = der τ L u * der τ L v := by
  induction L with
  | nil => simp only [der.eq_1]
  | cons q L ih => rw [der.eq_2, der.eq_2, der.eq_2, ih, derivation_mul]

private theorem der_one (τ : ℕ → G ℚ Ω) (L : List ℕ) : der τ L (1 : Ω) = 1 := by
  induction L with
  | nil => rw [der.eq_1]
  | cons q L ih =>
    rw [der.eq_2, ih]
    unfold der1
    simp

private def derHom (τ : ℕ → G ℚ Ω) (L : List ℕ) : Ω →* Ω where
  toFun := der τ L
  map_one' := der_one τ L
  map_mul' := der_mul τ L

private theorem tele (q : ℕ) (t : G ℚ Ω) (u : Ω) (hu : u ≠ 0) (h : (t ^ (q - 1)) u = u) :
    t (der1 q t u) / der1 q t u = u ^ (q - 1) / nrm q t u := by
  have key : ∀ (a : ℕ → Ω) (n : ℕ),
      (∏ i ∈ Finset.range n, a (i + 1) ^ i) * (∏ i ∈ Finset.range n, a i) * a n =
        a 0 * a n ^ n * ∏ i ∈ Finset.range n, a i ^ i := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
      calc (∏ i ∈ Finset.range n, a (i + 1) ^ i) * a (n + 1) ^ n * ((∏ i ∈ Finset.range n, a i) * a n) * a (n + 1)
          = ((∏ i ∈ Finset.range n, a (i + 1) ^ i) * (∏ i ∈ Finset.range n, a i) * a n) * a (n + 1) ^ (n + 1) := by ring
        _ = a 0 * a n ^ n * (∏ i ∈ Finset.range n, a i ^ i) * a (n + 1) ^ (n + 1) := by rw [ih]
        _ = a 0 * a (n + 1) ^ (n + 1) * ((∏ i ∈ Finset.range n, a i ^ i) * a n ^ n) := by ring
  have hD : der1 q t u ≠ 0 := derivation_ne_zero q t hu
  have hN : nrm q t u ≠ 0 := by
    unfold nrm
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr hu
  have htD : t (der1 q t u) = ∏ i ∈ Finset.range (q - 1), ((t ^ (i + 1)) u) ^ i := by
    unfold der1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, pow_succ', AlgEquiv.mul_apply]
  have hk := key (fun i => (t ^ i) u) (q - 1)
  simp only [pow_zero, AlgEquiv.one_apply, h] at hk
  rw [div_eq_div_iff hD hN, htD]
  have hD' : der1 q t u = ∏ i ∈ Finset.range (q - 1), ((t ^ i) u) ^ i := rfl
  have hN' : nrm q t u = ∏ i ∈ Finset.range (q - 1), (t ^ i) u := rfl
  rw [hD', hN']
  apply mul_right_cancel₀ hu
  linear_combination hk

end

theorem UpperTheory.V.ML.derBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N r : ℕ), N ≠ 0 → ∀ (τ : ℕ → G ℚ Ω) (L : List ℕ) (u : Ω), u ≠ 0 → (∀ g ∈ fixMu ℚ Ω N, g u = u) →
    der τ L u ≠ 0 ∧ (∀ g ∈ fixMu ℚ Ω N, g (der τ L u) = der τ L u) ∧ (∀ g : G ℚ Ω, g (der τ L u) = der τ L (g u)) ∧
    ((∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation u = 1) → ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation (der τ L u) = 1) ∧
    (∀ v : Ω, der τ L (u * v) = der τ L u * der τ L v) ∧ (∀ k : ℤ, der τ L (u ^ k) = der τ L u ^ k) ∧
    (∀ q, der τ L (der1 q (τ q) u) = der1 q (τ q) (der τ L u)) ∧ (∀ L', L.Perm L' → der τ L u = der τ L' u) ∧
    ∀ q : ℕ, 1 ≤ q → (τ q ^ (q - 1)) u = u → τ q (der1 q (τ q) u) / der1 q (τ q) u = u ^ (q - 1) / nrm q (τ q) u := by
  intro Ω _ _ _ N r hN τ L u hu hfix
  obtain ⟨-, -, -, -, -, hcomm, -, -, -, -⟩ := galBasic Ω N hN
  have hfix1 : ∀ (q : ℕ) (t : G ℚ Ω) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g ∈ fixMu ℚ Ω N, g (der1 q t x) = der1 q t x := by
    intro q t x hx g hg
    rw [derivation_galois_equivariant q t g x (fun s => hcomm x hx g s), hx g hg]
  have hfixL : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g ∈ fixMu ℚ Ω N, g (der τ L x) = der τ L x := by
    intro L x hx
    induction L with
    | nil => simpa only [der.eq_1] using hx
    | cons q L ih =>
      rw [der.eq_2]
      exact hfix1 q (τ q) _ ih
  have hneL : ∀ L : List ℕ, der τ L u ≠ 0 := by
    intro L
    induction L with
    | nil =>
      rw [der.eq_1]
      exact hu
    | cons q L ih =>
      rw [der.eq_2]
      exact derivation_ne_zero q (τ q) ih
  have hcommL : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ g : G ℚ Ω, g (der τ L x) = der τ L (g x) := by
    intro L x hx g
    induction L with
    | nil => simp only [der.eq_1]
    | cons q L ih =>
      rw [der.eq_2, der.eq_2, derivation_galois_equivariant q (τ q) g _ (fun s => hcomm _ (hfixL L x hx) g s), ih]
  have hder1 : ∀ (L : List ℕ) (x : Ω), (∀ g ∈ fixMu ℚ Ω N, g x = x) →
      ∀ (q : ℕ) (t : G ℚ Ω), der τ L (der1 q t x) = der1 q t (der τ L x) := by
    intro L x hx q t
    have e : der τ L (der1 q t x) = derHom τ L (der1 q t x) := rfl
    rw [e]
    unfold der1
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow]
    show der τ L ((t ^ i) x) ^ i = _
    rw [← hcommL L x hx]
  have hconj : ∀ x : Ω, (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation x = 1) →
      ∀ (s : G ℚ Ω) (A : ValuationSubring Ω), ¬ Over A r → A.valuation (s x) = 1 := by
    intro x hx s A hA
    obtain ⟨-, -, -, hlt, heq⟩ := (placeBasic Ω).2.2.2.2.2.2.2.2.2 (s⁻¹ • A) s
    have hsA : s • (s⁻¹ • A) = A := smul_inv_smul s A
    rw [hsA] at hlt heq
    apply (heq x).mpr
    apply hx
    intro hB
    apply hA
    have hr := (hlt (r : Ω)).mpr hB
    show A.valuation (r : Ω) < 1
    simpa using hr
  have hvalL : (∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation u = 1) →
      ∀ (L : List ℕ) (A : ValuationSubring Ω), ¬ Over A r → A.valuation (der τ L u) = 1 := by
    intro hu1 L
    induction L with
    | nil => simpa only [der.eq_1] using hu1
    | cons q L ih =>
      intro A hA
      rw [der.eq_2]
      unfold der1
      rw [map_prod]
      apply Finset.prod_eq_one
      intro i _
      rw [Valuation.map_pow, hconj _ ih _ A hA, one_pow]
  have hzpowL : ∀ (L : List ℕ) (k : ℤ), der τ L (u ^ k) = der τ L u ^ k := by
    intro L k
    induction L with
    | nil => simp only [der.eq_1]
    | cons q L ih => rw [der.eq_2, der.eq_2, ih, derivation_zpow]
  have hperm : ∀ L' : List ℕ, L.Perm L' → der τ L u = der τ L' u := by
    intro L' hp
    induction hp with
    | nil => rfl
    | cons q _ ih => rw [der.eq_2, der.eq_2, ih]
    | swap a b l =>
      rw [der.eq_2, der.eq_2, der.eq_2, der.eq_2]
      have hx := hfixL l u hfix
      have h1 : der1 b (τ b) (der1 a (τ a) (der τ l u)) = der τ [b] (der1 a (τ a) (der τ l u)) := by
        rw [der.eq_2, der.eq_1]
      rw [h1, hder1 [b] _ hx, der.eq_2, der.eq_1]
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
  exact ⟨hneL L, hfixL L u hfix, fun g => hcommL L u hfix g, fun h => hvalL h L, der_mul τ L u, hzpowL L,
    fun q => hder1 L u hfix q (τ q), hperm, fun q _ h => tele q (τ q) u hu h⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ChiDvd
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ImportsAlt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.ext :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (O W : Type) [CommRing O] [AddCommGroup W] [Module O W] (M F n : ℕ), F ≠ 0 → ∀ (β : G ℚ Ω →* Oˣ) (ν : G ℚ Ω → W), IsNu M F n β ν → ∀ δ : G ℚ Ω, IsUnit ((β δ : O) - 1) →
    ∃ c : G ℚ Ω → W, IsCoc β c ∧ (∀ u ∈ fixMu ℚ Ω F, c u = ν u) ∧ ∀ g, ∃ u ∈ fixMu ℚ Ω F, ∃ y : O, c g = y • ν u := by
  intro Ω _ _ _ O W _ _ _ M F n hF β ν hν δ hδ
  obtain ⟨hN, -, hcomm, -⟩ := galBasic Ω F hF
  have hk : (↑hδ.unit⁻¹ : O) * ((β δ : O) - 1) = 1 := hδ.val_inv_mul
  have h1 : ν 1 = 0 := by
    have := hν.add 1 (fixMu ℚ Ω F).one_mem 1 (fixMu ℚ Ω F).one_mem
    simpa using this
  have hinv : ∀ u ∈ fixMu ℚ Ω F, ν u⁻¹ = -ν u := by
    intro u hu
    have := hν.add u hu u⁻¹ ((fixMu ℚ Ω F).inv_mem hu)
    rw [mul_inv_cancel, h1] at this
    exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact this.symm)
  have hcm : ∀ g, g * δ * g⁻¹ * δ⁻¹ ∈ fixMu ℚ Ω F := fun g => hcomm g δ
  refine ⟨fun g => (-(↑hδ.unit⁻¹ : O)) • ν (g * δ * g⁻¹ * δ⁻¹), ⟨?_, ?_⟩, ?_, fun g => ⟨_, hcm g, _, rfl⟩⟩
  · have hc : Continuous (fun g : G ℚ Ω => g * δ * g⁻¹ * δ⁻¹) := by
      have c1 : Continuous (fun g : G ℚ Ω => g * δ) := continuous_mul_const δ
      have c2 : Continuous (fun g : G ℚ Ω => g⁻¹) := continuous_inv
      have c3 : Continuous (fun g : G ℚ Ω => g * δ * g⁻¹) := c1.mul c2
      exact (continuous_mul_const δ⁻¹).comp c3
    have hf : Continuous (fun g : G ℚ Ω => (⟨g * δ * g⁻¹ * δ⁻¹, hcm g⟩ : fixMu ℚ Ω F)) := hc.subtype_mk hcm
    have hl : IsLocallyConstant (fun g : G ℚ Ω => ν (g * δ * g⁻¹ * δ⁻¹)) := hν.lc.comp_continuous hf
    exact hl.comp (fun w => (-(↑hδ.unit⁻¹ : O)) • w)
  · intro g h
    have e : g * h * δ * (g * h)⁻¹ * δ⁻¹ = g * (h * δ * h⁻¹ * δ⁻¹) * g⁻¹ * (g * δ * g⁻¹ * δ⁻¹) := by
      group
    have hmem : g * (h * δ * h⁻¹ * δ⁻¹) * g⁻¹ ∈ fixMu ℚ Ω F := hN.conj_mem _ (hcm h) g
    show (-(↑hδ.unit⁻¹ : O)) • ν (g * h * δ * (g * h)⁻¹ * δ⁻¹) =
      (-(↑hδ.unit⁻¹ : O)) • ν (g * δ * g⁻¹ * δ⁻¹) + (β g : O) • ((-(↑hδ.unit⁻¹ : O)) • ν (h * δ * h⁻¹ * δ⁻¹))
    rw [e, hν.add _ hmem _ (hcm g), hν.eqv g _ (hcm h), smul_add, smul_comm (-(↑hδ.unit⁻¹ : O)) (β g : O)]
    abel
  · intro u hu
    have hconj : δ * u⁻¹ * δ⁻¹ ∈ fixMu ℚ Ω F := hN.conj_mem _ ((fixMu ℚ Ω F).inv_mem hu) δ
    have e : u * δ * u⁻¹ * δ⁻¹ = u * (δ * u⁻¹ * δ⁻¹) := by
      group
    have e2 : ν u + (β δ : O) • -ν u = -(((β δ : O) - 1) • ν u) := by
      rw [sub_smul, one_smul, smul_neg]
      abel
    show (-(↑hδ.unit⁻¹ : O)) • ν (u * δ * u⁻¹ * δ⁻¹) = ν u
    rw [e, hν.add u hu _ hconj, hν.eqv δ u⁻¹ ((fixMu ℚ Ω F).inv_mem hu), hinv u hu, e2, smul_neg, neg_smul,
      neg_neg, smul_smul, hk, one_smul]
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem chi_dvd (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [Algebra ℤ_[l] O] (n : ℕ) (g : G ℚ Ω) (h : g ∈ fixMu ℚ Ω (l ^ n)) :
    (l : O) ^ n ∣ (chiO ℚ Ω l O g : O) - 1 := by
  have hl : l.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' hl.one_lt⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have h1 : (1 : ZMod (l ^ n)) = modularCyclotomicCharacter Ω
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω (l ^ n)) (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) := by
    apply modularCyclotomicCharacter.unique
    intro t ht
    rw [ZMod.val_one, pow_one]
    rw [mem_rootsOfUnity] at ht
    exact h (t : Ω) (by rw [← Units.val_pow_eq_pow_val, ht, Units.val_one])
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)).val.toZModPow n = 1 := by
    rw [cyclotomicCharacter.toZModPow, ← h1]
  have h3 : (l : ℤ_[l]) ^ n ∣ (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)).val - 1 := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h2, map_one, sub_self]
  have h4 := map_dvd (algebraMap ℤ_[l] O) h3
  simpa [chiO, cycZ] using h4

theorem UpperTheory.V.ML.step :
    Rec → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (N₀ m F N q : ℕ) (α : G ℚ Ω →* Oˣ), Dat l N₀ m F α → F ∣ N → N ≠ 0 → q.Prime → q ≡ 1 [MOD F] →
    ∀ ν : G ℚ Ω → QO l O, IsNu (l ^ m) F (N * q) (dualChar l α) ν → ∀ (δ : G ℚ Ω) (a₀ a : O) (w₀ : QO l O), a₀ ∣ a → a ∣ (l : O) ^ m → (∀ y : O, y • w₀ = 0 ↔ a ∣ y) →
    (∀ u ∈ fixMu ℚ Ω F, a • ν u = 0) → ∀ c ∈ ShT (QO l O) α δ F a₀,
    (∀ A : ValuationSubring Ω, Over A N → ¬ Over A F → ¬ Over A q → ∀ g ∈ Dec (F := ℚ) A, c g = 0) →
    ∀ A : ValuationSubring Ω, Over A q → ∀ g ∈ Dec (F := ℚ) A, ∀ τ ∈ Ine (F := ℚ) A, ∀ y : O, ν τ = y • w₀ → y • c g = 0 := by
  intro hRec Ω _ _ _ l _ O _ _ _ _ _ N₀ m F N q α hD hFN hN hq hq1 ν hν δ a₀ a w₀ ha₀a hal hw₀ hνa c hc hyp A hA g hg τ hτ y hy
  obtain ⟨⟨hlc, hcoc⟩, -, hac0, hunrc, hlocc⟩ := hc
  have hl : l.Prime := Fact.out
  have hF : F ≠ 0 := by
    rintro rfl
    exact hN (zero_dvd_iff.mp hFN)
  have hlmF : l ^ m ∣ F := Dvd.intro_left N₀ hD.lev.symm
  have hlF : l ∣ F := (dvd_pow_self l (by have := hD.pos; omega)).trans hlmF
  have hlN : l ∣ N := hlF.trans hFN
  have hql : q ≠ l := by
    intro hql
    have h := hq1.of_dvd hlF
    rw [hql] at h
    unfold Nat.ModEq at h
    rw [Nat.mod_self, Nat.mod_eq_of_lt hl.one_lt] at h
    exact absurd h (by norm_num)
  obtain ⟨-, hopen, -, -, -, -, -, -, -, -⟩ := galBasic Ω F hF
  obtain ⟨-, hfrobEx, hoverMul, hcopNot, hIne, -, hPows, -, hplace, -⟩ := placeBasic Ω
  have hcop : q.Coprime F := hq1.gcd_eq.trans (Nat.gcd_one_left F)
  have hAF : ¬Over A F := hcopNot A q F hcop hA
  have hIneA : Ine A ≤ fixMu ℚ Ω F := hIne A F hAF
  have hdivA : ∀ x ∈ fixMu ℚ Ω F, a ∣ (α x : O) - 1 := fun x hx => hal.trans (hD.triv x hx)
  have hl0 : (l : O) ≠ 0 := by
    obtain ⟨hinj, -⟩ := dvrFacts l O
    intro h0
    have h1 : algebraMap ℤ_[l] O (l : ℤ_[l]) = algebraMap ℤ_[l] O 0 := by simpa using h0
    exact (Nat.cast_ne_zero.mpr hl.ne_zero : (l : ℤ_[l]) ≠ 0) (hinj h1)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact pow_ne_zero m hl0 (zero_dvd_iff.mp hal)
  let S : Subgroup (G ℚ Ω) :=
    { carrier := {x | a ∣ (α x : O) - 1}
      mul_mem' := fun {x z} hx hz => by
        have e : (α (x * z) : O) - 1 = (α x : O) * ((α z : O) - 1) + ((α x : O) - 1) := by
          rw [map_mul, Units.val_mul]; ring
        show a ∣ (α (x * z) : O) - 1
        rw [e]
        exact dvd_add (dvd_mul_of_dvd_right hz _) hx
      one_mem' := by
        show a ∣ (α 1 : O) - 1
        simp
      inv_mem' := fun {x} hx => by
        have hxx : (α x⁻¹ : O) * (α x : O) = 1 := by
          rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
        have e : (α x⁻¹ : O) - 1 = -(α x⁻¹ : O) * ((α x : O) - 1) := by
          linear_combination hxx
        show a ∣ (α x⁻¹ : O) - 1
        rw [e]
        exact dvd_mul_of_dvd_right hx _ }
  have hSo : IsOpen {x : G ℚ Ω | a ∣ (α x : O) - 1} :=
    Subgroup.isOpen_mono (H₁ := fixMu ℚ Ω F) (H₂ := S) (fun x hx => hdivA x hx) hopen
  obtain ⟨φ, hφ⟩ := hfrobEx A q hq hA
  have hφF : φ ∈ fixMu ℚ Ω F := by
    intro z hz
    rw [hPows A q F φ hφ hAF z hz, pow_eq_pow_mod q hz, hq1, ← pow_eq_pow_mod 1 hz, pow_one]
  obtain ⟨v, hv, hnv, -⟩ := hplace A q hq hA
  have hfr : IsFrob A (normV v) φ := by rw [hnv]; exact hφ
  have hDecA : Dec A ≤ fixMu ℚ Ω F := Kum.decGen ℚ Ω A v φ (fixMu ℚ Ω F) hv hfr hopen hIneA hφF
  obtain ⟨δ', hδ'⟩ := hD.notCyc
  have hβ : IsUnit (((dualChar l α) δ' : O) - 1) := by
    have hu : (((α δ')⁻¹ : Oˣ) : O) * (α δ' : O) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e : ((dualChar l α) δ' : O) - 1 =
        -(((α δ')⁻¹ : Oˣ) : O) * ((α δ' : O) - (chiO ℚ Ω l O δ' : O)) := by
      simp only [dualChar, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
      linear_combination hu
    rw [e]
    exact (Units.isUnit _).neg.mul hδ'
  obtain ⟨n, hncoc, hnν, hnform⟩ := ext Ω O (QO l O) (l ^ m) F (N * q) hF (dualChar l α) ν hν δ' hβ
  have han : ∀ x, a • n x = 0 := by
    intro x
    obtain ⟨u, hu, z, hz⟩ := hnform x
    rw [hz, smul_comm, hνa u hu, smul_zero]
  have hac : ∀ x, a • c x = 0 := by
    intro x
    obtain ⟨k, hk⟩ := ha₀a
    rw [hk, mul_comm, mul_smul, hac0, smul_zero]
  have hnotF : ∀ B : ValuationSubring Ω, ¬Over B (N * q) → ¬Over B F := by
    intro B hB hBF
    obtain ⟨k, hk⟩ := hFN
    exact hB ((hoverMul B N q).mpr (Or.inl (by rw [hk]; exact (hoverMul B F k).mpr (Or.inl hBF))))
  have hunr : ∀ B : ValuationSubring Ω, ¬Over B (N * q) → ∀ x ∈ Ine B,
      a ∣ (α x : O) - 1 ∧ c x = 0 ∧ n x = 0 := by
    intro B hB x hx
    have hBF := hnotF B hB
    have hxF := hIne B F hBF hx
    exact ⟨hdivA x hxF, hunrc B hBF x hx, by rw [hnν x hxF]; exact hν.unr B hB x hx⟩
  have hloc : ∀ B : ValuationSubring Ω, Over B N → ¬Over B q →
      ∃ w, a • w = 0 ∧ ∀ x ∈ Dec B, c x = (α x : O) • w - w := by
    intro B hBN hBq
    by_cases hBF : Over B F
    · obtain ⟨w, hw, hw'⟩ := hlocc B hBF
      obtain ⟨k, hk⟩ := ha₀a
      exact ⟨w, by rw [hk, mul_comm, mul_smul, hw, smul_zero], hw'⟩
    · exact ⟨0, smul_zero _, fun x hx => by rw [hyp B hBN hBF hBq x hx, smul_zero, sub_zero]⟩
  have hdec : ∀ x ∈ Dec A, a ∣ (α x : O) - 1 ∧ a ∣ ((dualChar l α) x : O) - 1 := by
    intro x hx
    have hxF := hDecA hx
    refine ⟨hdivA x hxF, ?_⟩
    have hxl : x ∈ fixMu ℚ Ω (l ^ m) := fixMu_le ℚ Ω hlmF hxF
    have h1 := chi_dvd Ω l O m x hxl
    have h2 := hdivA x⁻¹ (inv_mem hxF)
    have e : ((dualChar l α) x : O) - 1 =
        (chiO ℚ Ω l O x : O) * ((α x⁻¹ : O) - 1) + ((chiO ℚ Ω l O x : O) - 1) := by
      simp only [dualChar, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_inv]
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right h2 _) (hal.trans h1)
  have hine : ∀ x ∈ Ine A, c x = 0 := fun x hx => hunrc A hAF x hx
  have hnτ : n τ = y • w₀ := by rw [hnν τ (hIneA hτ)]; exact hy
  exact hRec Ω l hD.odd_l O α a ha0 w₀ hw₀ hSo N q hN hlN hq hql c n ⟨hlc, hcoc⟩ hncoc hac han hunr hloc
    A hA hdec hine g hg τ hτ y hnτ
end
