module

public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalDivisorBirationalCompare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsPrimeCartierDivisor

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficients
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficients
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

noncomputable def DivOver.ordHom {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) : X.functionFieldˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (E.ord f)
  map_one' := by simp
  map_mul' f g := by simp [E.ord_mul]

theorem DivOver.ord_prod_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) {ι : Type} (s : Finset ι) (f : ι → X.functionFieldˣ) (e : ι → ℤ) :
    E.ord (∏ j ∈ s, f j ^ e j) = ∑ j ∈ s, e j * E.ord (f j) := by
  have h := congrArg Multiplicative.toAdd (map_prod E.ordHom (fun j => f j ^ e j) s)
  rw [toAdd_prod] at h
  calc E.ord (∏ j ∈ s, f j ^ e j) = Multiplicative.toAdd (E.ordHom (∏ j ∈ s, f j ^ e j)) := rfl
    _ = ∑ j ∈ s, Multiplicative.toAdd (E.ordHom (f j ^ e j)) := h
    _ = ∑ j ∈ s, e j * E.ord (f j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_zpow, toAdd_zpow, smul_eq_mul]
      rfl

theorem DivOver.ord_eq_zero_of_unitAt {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {E : DivOver p} {x : X} (hE : E.Through x) (v : X.functionFieldˣ)
    (hv : UnitAt x (v : X.functionField)) : E.ord v = 0 := by
  obtain ⟨a, ha, hav⟩ := hv
  have h1 : (v : X.functionField) ∈ E.ring := hE _ ⟨a, hav⟩
  have hinv : algebraMap (X.presheaf.stalk x) X.functionField (↑(ha.unit⁻¹)) =
      ((v⁻¹ : X.functionFieldˣ) : X.functionField) := by
    rw [Units.val_inv_eq_inv_val]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← hav, ← map_mul, IsUnit.mul_val_inv, map_one]
  have h2 : ((v⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring := hE _ ⟨_, hinv⟩
  have e1 := (E.ord_nonneg_iff v).mpr h1
  have e2 := (E.ord_nonneg_iff v⁻¹).mpr h2
  rw [E.ord_inv] at e2
  omega

theorem coeff_criterion_snc : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ) (B : Closeds Y), 0 < m → IsDivOfForm K η → FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → (G - m • K).supp ≤ B → ∀ (y : Y) (g : Y.functionFieldˣ), G.IsEqn y g → ∀ E : DivOver q, E.Through y → ((∀ w, w ⤳ y → (G - m • K).mult w < m) → -1 < discrep E η m g) ∧ ((∀ w, w ⤳ y → (G - m • K).mult w ≤ m) → -1 ≤ discrep E η m g) := by
  intro k _ _ Y _ _ q n _ η hη K G m B hm hK hsnc hsupp y g hG E hE
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have hdim : topologicalKrullDim Y = n :=
    HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q n inferInstance
  obtain ⟨U, hy, z, J, w, u, hc⟩ := exists_isSncChart k Y q n B hsnc y
  have hgen : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩
  have hfg := isFreeGen_formOf hgen hc.frame
  have hω0 : formOf U hgen (dOn q z) ≠ 0 := by
    intro h0
    have := hfg.1 (a₁ := 0) (a₂ := 1) (by simp only [h0, smul_zero])
    exact zero_ne_one this
  have hr : hfg.repr η ≠ 0 := by
    intro h0
    apply hη
    rw [← hfg.repr_smul η, h0, zero_smul]
  have hηh : η = ((Units.mk0 _ hr : Y.functionFieldˣ) : Y.functionField) • formOf U hgen (dOn q z) :=
    (hfg.repr_smul η).symm
  set h : Y.functionFieldˣ := Units.mk0 _ hr with hdef
  have hKy : K.IsEqn y h := hK U (dOn q z) hc.frame y hy h hηh
  have hD1 : (G - m • K).IsEqn y (g / h ^ m) := hG.sub (hKy.nsmul m)
  have hD2 := IsSncChart.isEqn_monomial k Y q n B y U hy z J w u hc (G - m • K) hsupp
  have hunit := (hD1.iff_unitAt).mp hD2
  have hzero := DivOver.ord_eq_zero_of_unitAt hE
    ((∏ j ∈ J, u j ^ (G - m • K).mult (w j)) / (g / h ^ m)) (by simpa using hunit)
  rw [div_eq_mul_inv, E.ord_mul, E.ord_inv, div_eq_mul_inv, E.ord_mul, E.ord_inv,
    DivOver.ord_prod_zpow, E.ord_pow] at hzero
  have hform : E.formOrd η = E.ord h + E.formOrd (formOf U hgen (dOn q z)) := by
    rw [hηh]
    exact E.formOrd_smul hdim hω0 h
  have hF0 : 0 ≤ E.formOrd (formOf U hgen (dOn q z)) :=
    E.formOrd_formOf_nonneg hdim hy hE (dOn q z) hω0
  have hF1 := E.sum_ord_sub_one_le_formOrd_dOn hdim hy hE z hω0 (J := ↥J) (fun j => j.1)
    Subtype.val_injective (fun j => u j.1) (fun j => hc.val j.1 j.2)
  rw [Finset.sum_coe_sort J (fun j => E.ord (u j))] at hF1
  have hnn : ∀ j ∈ J, 0 ≤ E.ord (u j) := fun j hj =>
    (E.ord_nonneg_iff _).mpr (hE _ (by rw [hc.val j hj]; exact regAt_fnOf hy _ _))
  set F := E.formOrd (formOf U hgen (dOn q z)) with hFdef
  set S := ∑ j ∈ J, E.ord (u j) with hSdef
  change S - 1 ≤ F at hF1
  set T := ∑ j ∈ J, (G - m • K).mult (w j) * E.ord (u j) with hTdef
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have hdisc : discrep E η m g = ((m * F - T : ℤ) : ℚ) / m := by
    have hg' : E.ord g = m * E.ord h + T := by linarith
    unfold discrep
    rw [hform, hg']
    push_cast
    field_simp
    ring
  rw [hdisc]
  constructor
  · intro hlt
    have hT : T ≤ (m - 1) * S := by
      rw [hSdef, hTdef, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      have := hlt (w j) (hc.spec j hj)
      exact mul_le_mul_of_nonneg_right (by omega) (hnn j hj)
    have hS0 : 0 ≤ S := Finset.sum_nonneg hnn
    have key : -(m : ℤ) < m * F - T := by
      rcases eq_or_lt_of_le hS0 with hS | hS
      · rw [← hS] at hT
        have : (m : ℤ) * F ≥ 0 := mul_nonneg (by exact_mod_cast hm.le) hF0
        have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
        linarith
      · have : (m : ℤ) * (S - 1) ≤ m * F :=
          mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hm.le)
        nlinarith
    rw [lt_div_iff₀ hm']
    have : ((-(m : ℤ) : ℤ) : ℚ) < ((m * F - T : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at this ⊢
    linarith
  · intro hle
    have hT : T ≤ m * S := by
      rw [hSdef, hTdef, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j hj => ?_)
      exact mul_le_mul_of_nonneg_right (hle (w j) (hc.spec j hj)) (hnn j hj)
    have key : -(m : ℤ) ≤ m * F - T := by
      have : (m : ℤ) * (S - 1) ≤ m * F :=
        mul_le_mul_of_nonneg_left (by linarith) (by exact_mod_cast hm.le)
      nlinarith
    rw [le_div_iff₀ hm']
    have : ((-(m : ℤ) : ℤ) : ℚ) ≤ ((m * F - T : ℤ) : ℚ) := by exact_mod_cast key
    push_cast at this ⊢
    linarith

end GlobalTheory.Discrepancy
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KltOfSncCoefficientsStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.klt_of_snc_coefficients : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ) (B : Closeds Y), 0 < m → IsDivOfForm K η → FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → (G - m • K).supp ≤ B → ∀ (y : Y) (g : Y.functionFieldˣ), G.IsEqn y g → ∀ E : DivOver q, E.Through y → ((∀ w, w ⤳ y → (G - m • K).mult w < m) → -1 < discrep E η m g) ∧ ((∀ w, w ⤳ y → (G - m • K).mult w ≤ m) → -1 ≤ discrep E η m g) := by
  first | exact @_root_.GlobalTheory.Discrepancy.coeff_criterion_snc | exact _root_.GlobalTheory.Discrepancy.coeff_criterion_snc | (intros; apply _root_.GlobalTheory.Discrepancy.coeff_criterion_snc <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicities
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicities
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

private theorem unitAt_of_ord_eq_zero_coheight_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {v : X}
    (hv : Order.coheight v = 1) {h : X.functionField} (h0 : h ≠ 0)
    (hord : Scheme.ord h v = 0) : UnitAt v h := by
  haveI := hufd v
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk v) := krullDimLE_of_coheight_le hv.le
  by_cases hF : IsField (X.presheaf.stalk v)
  · obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk v) h
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨b', hbb'⟩ := hF.mul_inv_cancel hb0
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply h0
      rw [← hab, map_zero, zero_div]
    obtain ⟨a', haa'⟩ := hF.mul_inv_cancel ha0
    refine ⟨a * b', ?_, ?_⟩
    · refine isUnit_iff_exists_inv.mpr ⟨a' * b, ?_⟩
      calc a * b' * (a' * b) = (a * a') * (b * b') := by ring
        _ = 1 := by rw [haa', hbb', one_mul]
    · rw [← hab, map_mul]
      have : algebraMap (X.presheaf.stalk v) X.functionField b *
          algebraMap (X.presheaf.stalk v) X.functionField b' = 1 := by
        rw [← map_mul, hbb', map_one]
      rw [eq_div_iff (fun h' => hb0 (IsFractionRing.injective (X.presheaf.stalk v) X.functionField
        (by rw [h', map_zero]))), mul_assoc, mul_comm _ (algebraMap _ _ b), this, mul_one]
  · haveI : IsDiscreteValuationRing (X.presheaf.stalk v) := by
      have hmax : ∀ I : Ideal (X.presheaf.stalk v), I ≠ ⊥ → I.IsPrime → I.IsMaximal :=
        Ring.krullDimLE_one_iff_of_isPrime_bot.mp inferInstance
      have hne : IsLocalRing.maximalIdeal (X.presheaf.stalk v) ≠ ⊥ :=
        IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hF
      have key := (IsDiscreteValuationRing.TFAE (X.presheaf.stalk v) hF).out 4 1
      exact key.mp ⟨inferInstance, ⟨IsLocalRing.maximalIdeal _, ⟨hne, inferInstance⟩,
        fun P hP => IsLocalRing.eq_maximalIdeal (hmax P hP.1 hP.2)⟩⟩
    have h1 : Scheme.ordHom v hv h = 1 := by
      have := (Scheme.ord_eq_iff hv h0 (n := 0)).mp hord
      simpa using this
    have hmem : h ∈ MonoidHom.mker (Ring.ordFrac (X.presheaf.stalk v) (K := X.functionField)) :=
      MonoidHom.mem_mker.mpr h1
    rw [Ring.mker_ordFrac_eq_isUnitSubmonoid] at hmem
    obtain ⟨a, ha, rfl⟩ := hmem
    exact ⟨a, ha, rfl⟩
private theorem Scheme_ord_one {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (v : X) :
    Scheme.ord (1 : X.functionField) v = 0 := by
  have h := Scheme.ord_mul (x := v) (one_ne_zero : (1 : X.functionField) ≠ 0) one_ne_zero
  rw [mul_one] at h
  omega

private theorem Scheme_ord_units_zpow {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : (X.functionField)ˣ) (n : ℤ) (v : X) :
    Scheme.ord ((g ^ n : (X.functionField)ˣ) : X.functionField) v =
      n * Scheme.ord (g : X.functionField) v := by
  let φ : (X.functionField)ˣ →* Multiplicative ℤ :=
    { toFun := fun a => Multiplicative.ofAdd (Scheme.ord (a : X.functionField) v)
      map_one' := by simp [Scheme_ord_one]
      map_mul' := fun a b => by
        rw [Units.val_mul, Scheme.ord_mul a.ne_zero b.ne_zero, ofAdd_add] }
  have h := map_zpow φ g n
  have h2 := congrArg Multiplicative.toAdd h
  simpa [φ, toAdd_zpow, smul_eq_mul] using h2

private theorem Scheme_ord_units_inv {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (g : (X.functionField)ˣ) (v : X) :
    Scheme.ord ((g⁻¹ : (X.functionField)ˣ) : X.functionField) v =
      - Scheme.ord (g : X.functionField) v := by
  have h := Scheme.ord_mul (x := v) g.ne_zero (g⁻¹).ne_zero
  rw [Units.mul_inv, Scheme_ord_one] at h
  omega

private theorem unitAt_of_ord_eq_zero_on_open {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {y : X} (U : X.Opens)
    (hy : y ∈ U) (h : (X.functionField)ˣ)
    (hord : ∀ v ∈ U, Scheme.ord (h : X.functionField) v = 0) : UnitAt y (h : X.functionField) := by
  haveI : GlobalTheory.IsNormalScheme X :=
    ⟨fun x => inferInstance, fun x => by haveI := hufd x; infer_instance⟩
  have key : ∀ g : (X.functionField)ˣ, (∀ v ∈ U, Scheme.ord (g : X.functionField) v = 0) →
      RegAt y (g : X.functionField) := by
    intro g hg
    apply regAt_of_forall_coheight_eq_one
    intro z hz hz1
    exact (unitAt_of_ord_eq_zero_coheight_one hufd hz1 g.ne_zero (hg z (hz.mem_open U.isOpen hy))).regAt
  obtain ⟨a, ha⟩ := key h hord
  obtain ⟨b, hb⟩ := key h⁻¹ (fun v hv => by rw [Scheme_ord_units_inv, hord v hv, neg_zero])
  refine ⟨a, ?_, ha⟩
  have hab : algebraMap (X.presheaf.stalk y) X.functionField (a * b) =
      algebraMap (X.presheaf.stalk y) X.functionField 1 := by
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  exact isUnit_iff_exists_inv.mpr ⟨b, IsFractionRing.injective _ _ hab⟩

private theorem exists_local_unit_ord_eq_finite_sum {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [DecidableEq X] (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (c : X → ℤ)
    (S : Finset X) (hS : ∀ z ∈ S, Order.coheight z = 1) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ f : (X.functionField)ˣ, ∀ v ∈ U,
      Scheme.ord (f : X.functionField) v = ∑ z ∈ S, if v = z then c z else 0 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, 1, fun v _ => by simp [Scheme_ord_one]⟩
  | insert z S hzS ih =>
    obtain ⟨U1, hx1, f1, hf1⟩ := ih (fun w hw => hS w (Finset.mem_insert_of_mem hw))
    obtain ⟨U2, hx2, π, hπ⟩ := PrimeDivCartier.exists_local_eqn X hufd z
      (hS z (Finset.mem_insert_self z S)) x
    refine ⟨U1 ⊓ U2, ⟨hx1, hx2⟩, f1 * π ^ (c z), fun v hv => ?_⟩
    rw [Finset.sum_insert hzS, Units.val_mul, Scheme.ord_mul f1.ne_zero (π ^ c z).ne_zero,
      Scheme_ord_units_zpow, hf1 v hv.1, hπ v hv.2]
    split_ifs <;> simp [add_comm]

theorem _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
      (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ c : X → ℤ,
        (Function.support c).Finite → (∀ z, c z ≠ 0 → Order.coheight z = 1) →
          ∃ D : CartierDiv X, ∀ z, D.mult z = c z := by
  intro X _ _ hufd c hfin hc
  classical
  have hS : ∀ z ∈ hfin.toFinset, Order.coheight z = 1 :=
    fun z hz => hc z (hfin.mem_toFinset.mp hz)
  have hsum : ∀ v, (∑ z ∈ hfin.toFinset, if v = z then c z else 0) = c v := by
    intro v
    rw [Finset.sum_ite_eq]
    split_ifs with hv
    · rfl
    · have : c v = 0 := by
        by_contra h'
        exact hv (hfin.mem_toFinset.mpr h')
      exact this.symm
  choose U hxU f hf using fun x => exists_local_unit_ord_eq_finite_sum hufd c hfin.toFinset hS x
  have hmem : (fun x => germOf x (f x)) ∈ cartierGroup X := by
    intro x
    refine ⟨U x, hxU x, f x, fun y hy => ?_⟩
    rw [germOf_eq_iff]
    have hu := unitAt_of_ord_eq_zero_on_open hufd (U x ⊓ U y) ⟨hy, hxU y⟩ (f x * (f y)⁻¹)
      (fun v hv => by
        rw [Units.val_mul, Scheme.ord_mul (f x).ne_zero ((f y)⁻¹).ne_zero, Scheme_ord_units_inv,
          hf x v hv.1, hf y v hv.2, add_neg_cancel])
    simpa [div_eq_mul_inv] using hu
  let D : CartierDiv X := (⟨fun x => germOf x (f x), hmem⟩ : cartierGroup X)
  refine ⟨D, fun z => ?_⟩
  have he : D.IsEqn z (f z) := rfl
  rw [he.mult_eq, hf z z (hxU z), hsum]
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicitiesStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_cartier_with_multiplicities : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ c : X → ℤ, (Function.support c).Finite → (∀ z, c z ≠ 0 → Order.coheight z = 1) → ∃ D : CartierDiv X, ∀ z, D.mult z = c z := by
  first | exact @_root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial | exact _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial | (intros; apply _root_.GlobalTheory.Cartier.CartierDiv.exists_mult_eq_of_locallyFactorial <;> assumption)
end
end
