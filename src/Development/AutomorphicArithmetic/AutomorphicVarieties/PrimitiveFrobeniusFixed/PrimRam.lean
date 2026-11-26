module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PrimRam
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem primRam_lift (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) (u : (ZMod N)ˣ)
    (hu : u ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker) :
    ∃ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω N σ = u := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨v, hv⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r)
    (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA v
  refine ⟨σ, hσ, ?_⟩
  apply (Chr.clsFacts ℚ Ω N).2.2.1
  refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨?_, ?_⟩
  · intro ζ hζ
    have hcop : (N / r ^ N.factorization r).Coprime r :=
      (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
    have hfix := (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA (N / r ^ N.factorization r) hcop ζ hζ).2 σ hσ
    rw [MonoidHom.mem_ker.mp hu, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ,
      pow_one]
    exact hfix
  · rw [← hv, ← hσv]
    rfl

private theorem primRam_l (l : ℕ) [Fact l.Prime] (c : HV.Coef l) : ¬ IsUnit (l : c.O) := by
  intro hu
  haveI := c.fin
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  have hker : RingHom.ker (algebraMap ℤ_[l] c.O) ≤ IsLocalRing.maximalIdeal ℤ_[l] :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨Q, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (IsLocalRing.maximalIdeal ℤ_[l]) hker
  have hl : ((l : ℤ_[l])) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  rw [← hQc, Ideal.mem_comap, map_natCast] at hl
  exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hl hu)

private theorem primRam_unit (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (n : ℕ) (hn : ¬ l ∣ n) (x : c.O) (hx : x ^ n = 1)
    (h1 : x ≠ 1) : IsUnit (x - 1) := by
  haveI := c.dvr
  by_contra hne
  have hm : x - 1 ∈ IsLocalRing.maximalIdeal c.O := (IsLocalRing.mem_maximalIdeal _).2 hne
  have hsum : ∑ i ∈ Finset.range n, x ^ i = 0 := by
    have h := mul_geom_sum x n
    rw [hx, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h1)
  have hdiff : ∑ i ∈ Finset.range n, (x ^ i - 1) ∈ IsLocalRing.maximalIdeal c.O := by
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨y, hy⟩ := sub_dvd_pow_sub_pow x 1 i
    rw [one_pow] at hy
    rw [hy]
    exact Ideal.mul_mem_right _ _ hm
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    zero_sub, neg_mem_iff] at hdiff
  have hlm : (l : c.O) ∈ IsLocalRing.maximalIdeal c.O :=
    (IsLocalRing.mem_maximalIdeal _).2 (primRam_l l c)
  have hcop : IsCoprime ((l : ℤ)) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 hn)
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom c.O)
  simp only [eq_intCast, Int.cast_natCast] at hab
  have h1m : (1 : c.O) ∈ IsLocalRing.maximalIdeal c.O := by
    rw [← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hdiff)
  exact (IsLocalRing.maximalIdeal.isMaximal c.O).ne_top ((Ideal.eq_top_iff_one _).2 h1m)

private theorem exists_prime_dvd_over_of_over_mul_iff (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    (hmul : ∀ m n : ℕ, Over A (m * n) ↔ Over A m ∨ Over A n) (n : ℕ) (hn : n ≠ 0) (h : Over A n) :
    ∃ r, r.Prime ∧ r ∣ n ∧ Over A r := by
  refine Nat.recOnMul (motive := fun n => n ≠ 0 → Over A n → ∃ r, r.Prime ∧ r ∣ n ∧ Over A r)
    ?_ ?_ ?_ ?_ n hn h
  · intro h0
    exact absurd rfl h0
  · intro _ h1
    simp [Over] at h1
  · intro p hp _ hpA
    exact ⟨p, hp, dvd_rfl, hpA⟩
  · intro a b iha ihb hab hAab
    rcases (hmul a b).1 hAab with ha | hb
    · obtain ⟨r, hr, hra, hrA⟩ := iha (left_ne_zero_of_mul hab) ha
      exact ⟨r, hr, hra.mul_right b, hrA⟩
    · obtain ⟨r, hr, hrb, hrA⟩ := ihb (right_ne_zero_of_mul hab) hb
      exact ⟨r, hr, hrb.mul_left a, hrA⟩

theorem UpperTheory.V.ML.primRam :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (f : ℕ) [NeZero f] (ψ : DirichletCharacter c.O f), ψ.IsPrimitive → ¬ l ∣ orderOf ψ →
    (∀ A : ValuationSubring Ω, Over A f → ∃ g ∈ Ine (F := ℚ) A, IsUnit (((Chr.dirG ℚ Ω ψ g : c.Oˣ) : c.O) - 1)) ∧
    (∀ A : ValuationSubring Ω, ¬ Over A f → ∀ g ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω ψ g = 1) ∧ ∀ g : G ℚ Ω, Chr.dirG ℚ Ω ψ g ≠ 1 → IsUnit (((Chr.dirG ℚ Ω ψ g : c.Oˣ) : c.O) - 1) := by
  intro Ω _ inst _ l _ c f _ ψ hprim hord
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hpb := placeBasic Ω
  have hC : ∀ g : G ℚ Ω, Chr.dirG ℚ Ω ψ g ≠ 1 →
      IsUnit (((Chr.dirG ℚ Ω ψ g : c.Oˣ) : c.O) - 1) := by
    intro g hg
    apply primRam_unit l c (orderOf ψ) hord
    · show ((MulChar.toUnitHom ψ (Chr.cls ℚ Ω f g) : c.Oˣ) : c.O) ^ orderOf ψ = 1
      rw [MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
        MulChar.one_apply_coe]
    · intro h
      exact hg (Units.val_eq_one.mp h)
  refine ⟨?_, ?_, hC⟩
  · intro A hA
    obtain ⟨r, hr, hrf, hAr⟩ := exists_prime_dvd_over_of_over_mul_iff Ω A (hpb.2.2.1 A) f (NeZero.ne f) hA
    have hsub : ¬ (ZMod.unitsMap (Nat.ordCompl_dvd f r)).ker ≤ (MulChar.toUnitHom ψ).ker := by
      intro hle
      have hft := (DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := ψ)
        (Nat.ordCompl_dvd f r)).2 hle
      have hdvd := DirichletCharacter.conductor_dvd_of_mem_conductorSet ψ hft
      rw [(DirichletCharacter.isPrimitive_def ψ).1 hprim] at hdvd
      have hpos : 0 < f / r ^ f.factorization r := Nat.ordCompl_pos r (NeZero.ne f)
      have hlt : f / r ^ f.factorization r < f :=
        Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne f))
          (Nat.one_lt_pow (hr.factorization_pos_of_dvd (NeZero.ne f) hrf).ne' hr.one_lt)
      exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.2 hlt)
    obtain ⟨u, hu, hψu⟩ := SetLike.not_le_iff_exists.mp hsub
    obtain ⟨σ, hσ, hσu⟩ := primRam_lift Ω f r hr A hAr u hu
    refine ⟨σ, hσ, hC σ ?_⟩
    show MulChar.toUnitHom ψ (Chr.cls ℚ Ω f σ) ≠ 1
    rw [hσu]
    exact fun h => hψu (MonoidHom.mem_ker.mpr h)
  · intro A hA g hg
    have hk := (Chr.clsFacts ℚ Ω f).2.2.2.2 A hA hg
    show MulChar.toUnitHom ψ (Chr.cls ℚ Ω f g) = 1
    rw [MonoidHom.mem_ker.mp hk, map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.ShaToShT
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {O W : Type} [CommRing O] [AddCommGroup W] [Module O W]

private theorem shT_mono (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) (F : ℕ) {a b : O} (h : a ∣ b) :
    ShT W α δ F a ≤ ShT W α δ F b := by
  obtain ⟨t, rfl⟩ := h
  rintro c ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, h2, fun g => by rw [mul_comm, mul_smul, h3, smul_zero], h4, fun A hA => ?_⟩
  obtain ⟨m, hm, h⟩ := h5 A hA
  exact ⟨m, by rw [mul_comm, mul_smul, hm, smul_zero], h⟩

private theorem norm_coc (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) (hδ : IsUnit ((α δ : O) - 1)) (c : G ℚ Ω → W)
    (hc : IsCoc α c) : ∃ m : W, IsCoc α (fun g => c g - ((α g : O) • m - m)) ∧ c δ - ((α δ : O) • m - m) = 0 := by
  set u := hδ.unit with hu0
  have hu : (u : O) = (α δ : O) - 1 := hδ.unit_spec
  refine ⟨((u⁻¹ : Oˣ) : O) • c δ, ⟨?_, fun g h => ?_⟩, ?_⟩
  · have hloc : IsLocallyConstant fun g : G ℚ Ω => c (g * δ) :=
      hc.1.comp_continuous (continuous_mul_const δ)
    have heq : (fun g => c g - ((α g : O) • ((u⁻¹ : Oˣ) : O) • c δ - ((u⁻¹ : Oˣ) : O) • c δ)) =
        fun g => c g - (((u⁻¹ : Oˣ) : O) • (c (g * δ) - c g) - ((u⁻¹ : Oˣ) : O) • c δ) := by
      funext g
      rw [hc.2 g δ, add_sub_cancel_left, smul_comm (α g : O)]
    rw [heq]
    exact hc.1.sub (((hloc.sub hc.1).comp fun v => ((u⁻¹ : Oˣ) : O) • v).sub
      (IsLocallyConstant.const _))
  · beta_reduce
    rw [hc.2 g h, map_mul, Units.val_mul, mul_smul]
    module
  · have e : (α δ : O) • (((u⁻¹ : Oˣ) : O) • c δ) - ((u⁻¹ : Oˣ) : O) • c δ =
        (u : O) • (((u⁻¹ : Oˣ) : O) • c δ) := by
      rw [hu, sub_smul, one_smul]
    rw [e, smul_smul, Units.mul_inv, one_smul, sub_self]

private theorem unit_kill {x : O} (hx : IsUnit x) {a : O} {w : W} (h : a • x • w = 0) : a • w = 0 := by
  obtain ⟨u, rfl⟩ := hx
  calc a • w = ((u⁻¹ : Oˣ) : O) • (a • (u : O) • w) := by
        rw [smul_comm _ a]
        simp [smul_smul]
    _ = 0 := by rw [h, smul_zero]

private theorem conj_cob (α : G ℚ Ω →* Oˣ) {c : G ℚ Ω → W} (hc : IsCoc α c) (σ x : G ℚ Ω) (m : W)
    (h : c (σ⁻¹ * x * σ) = (α (σ⁻¹ * x * σ) : O) • m - m) :
    c x = (α x : O) • ((α σ : O) • m - c σ) - ((α σ : O) • m - c σ) := by
  have hc1 : c 1 = 0 := by
    have := hc.2 1 1
    simp only [mul_one, map_one, Units.val_one, one_smul] at this
    exact left_eq_add.mp this
  have e0 : c σ⁻¹ + (α σ⁻¹ : O) • c σ = 0 := by
    rw [← hc.2, inv_mul_cancel, hc1]
  have e1 : c (σ⁻¹ * x * σ) = c σ⁻¹ + (α σ⁻¹ : O) • (c x + (α x : O) • c σ) := by
    rw [mul_assoc, hc.2, hc.2]
  have ea : (α (σ⁻¹ * x * σ) : O) = (α x : O) := by
    rw [map_mul, map_mul, map_inv]
    congr 1
    calc (α σ)⁻¹ * α x * α σ = α x * ((α σ)⁻¹ * α σ) := by ac_rfl
      _ = α x := by rw [inv_mul_cancel, mul_one]
  have hs : (α σ : O) * (α σ⁻¹ : O) = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [e1, ea] at h
  linear_combination (norm := module) (α σ : O) • h - (α σ : O) • e0 - hs • (c x + (α x : O) • c σ - c σ)

private theorem dec_of_ine (α : G ℚ Ω →* Oˣ) {c : G ℚ Ω → W} (hc : IsCoc α c) (g d : G ℚ Ω) (m : W)
    (hg : IsUnit ((α g : O) - 1)) (h : c g = (α g : O) • m - m)
    (h' : c (d⁻¹ * g * d) = (α (d⁻¹ * g * d) : O) • m - m) : c d = (α d : O) • m - m := by
  have key := conj_cob α hc d g m h'
  rw [h] at key
  have e : ((α g : O) - 1) • m = ((α g : O) - 1) • ((α d : O) • m - c d) := by
    rw [sub_smul, one_smul, sub_smul, one_smul]
    exact key
  rw [hg.smul_left_cancel] at e
  linear_combination (norm := module) e

end

private theorem mem_shT (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) (F : ℕ)
    (h1 : ∀ A : ValuationSubring Ω, ¬ Over A F → ∀ g ∈ Ine (F := ℚ) A, α g = 1)
    (h2 : ∀ A : ValuationSubring Ω, Over A F → ¬ Over A l → ∃ g ∈ Ine (F := ℚ) A, IsUnit ((α g : O) - 1))
    (c : G ℚ Ω → QO l O) (hc : IsCoc α c) (hδ : c δ = 0)
    (hs : ∀ D ∈ shaFam ℚ Ω l, ∃ m : QO l O, ∀ g ∈ D, c g = (α g : O) • m - m) :
    ∃ a : O, a ≠ 0 ∧ c ∈ ShT (QO l O) α δ F a := by
  classical
  obtain ⟨A0, hA0⟩ := (placeBasic Ω).1 l (Fact.out : l.Prime)
  obtain ⟨m0, hm0⟩ := hs (Dec A0) (Or.inl ⟨A0, hA0, rfl⟩)
  have hfin : (Set.range c).Finite := hc.1.range_finite
  choose ann hann0 hann using (UpperTheory.V.ML.qoCyc l O).1
  let S : Finset (QO l O) := insert m0 hfin.toFinset
  refine ⟨∏ w ∈ S, ann w, Finset.prod_ne_zero_iff.mpr fun w _ => hann0 w, ?_⟩
  have kill : ∀ w ∈ S, (∏ w ∈ S, ann w) • w = 0 :=
    fun w hw => (hann w _).mpr (Finset.dvd_prod_of_mem _ hw)
  set a := ∏ w ∈ S, ann w
  have killc : ∀ g, a • c g = 0 :=
    fun g => kill _ (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr ⟨g, rfl⟩))
  have killm0 : a • m0 = 0 := kill _ (Finset.mem_insert_self _ _)
  refine ⟨hc, hδ, killc, fun A hA g hg => ?_, fun A hA => ?_⟩
  · obtain ⟨m, hm⟩ := hs (Ine A) (Or.inr ⟨A, rfl⟩)
    rw [hm g hg, h1 A hA g hg, Units.val_one, one_smul, sub_self]
  · by_cases hl : Over A l
    · obtain ⟨σ, rfl⟩ := (placeBasic Ω).2.2.2.2.2.2.2.1 A0 A l (Fact.out : l.Prime) hA0 hl
      refine ⟨(α σ : O) • m0 - c σ, ?_, fun d hd => ?_⟩
      · rw [smul_sub, smul_comm a (α σ : O) m0, killm0, smul_zero, killc, sub_zero]
      · have hd' : σ⁻¹ * d * σ ∈ Dec A0 := (((placeBasic Ω).2.2.2.2.2.2.2.2.2 A0 σ).1 d).mp hd
        exact conj_cob α hc σ d m0 (hm0 _ hd')
    · obtain ⟨g0, hg0, hu⟩ := h2 A hA hl
      obtain ⟨m, hm⟩ := hs (Ine A) (Or.inr ⟨A, rfl⟩)
      refine ⟨m, ?_, fun d hd => ?_⟩
      · have e : ((α g0 : O) - 1) • m = c g0 := by rw [hm g0 hg0, sub_smul, one_smul]
        exact unit_kill hu (by rw [e, killc])
      · have hdA : d • A = A := mem_Dec.mp hd
        have hg' : d⁻¹ * g0 * d ∈ Ine A := by
          have hh := ((placeBasic Ω).2.2.2.2.2.2.2.2.2 A d).2.1 g0
          rw [hdA] at hh
          exact hh.mp hg0
        exact dec_of_ine α hc g0 d m hu (hm g0 hg0) (hm _ hg')

theorem UpperTheory.V.ML.shaToShT :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω), IsUnit ((α δ : O) - 1) → ∀ F : ℕ, F ≠ 0 →
    (∀ A : ValuationSubring Ω, ¬ Over A F → ∀ g ∈ Ine (F := ℚ) A, α g = 1) →
    (∀ A : ValuationSubring Ω, Over A F → ¬ Over A l → ∃ g ∈ Ine (F := ℚ) A, IsUnit ((α g : O) - 1)) → ∀ n : ℕ∞,
    (∀ a : O, a ≠ 0 → Module.length O (ShT (QO l O) α δ F a) ≤ n) → Module.length O (ShaU (twist₂ l α) l (⊤ : Subgroup (G ℚ Ω))) ≤ n := by
  intro Ω _ _ _ l _ O _ _ _ _ _ α δ hδ F hF h1 h2 n hn
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let T : Subgroup (G ℚ Ω) := ⊤
  let ι : Z1U (twist₂ l α) T →ₗ[O] (G ℚ Ω → QO l O) :=
    { toFun := fun z g => (z : T → QO l O) ⟨g, Subgroup.mem_top g⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι : Function.Injective ι := by
    intro z z' h
    apply Subtype.ext
    funext u
    exact congrFun h u.1
  let Q : Z1U (twist₂ l α) T →ₗ[O] H1U (twist₂ l α) T := Submodule.mkQ _
  let P : ℕ → Submodule O (H1U (twist₂ l α) T) := fun k =>
    ((ShT (QO l O) α δ F (ϖ ^ k)).comap ι).map Q
  refine UpperTheory.V.Kum.lenDirected O (H1U (twist₂ l α) T) (ShaU (twist₂ l α) l T) P n ?_ ?_ ?_
  · intro i j hij
    exact Submodule.map_mono (Submodule.comap_mono (shT_mono α δ F (pow_dvd_pow ϖ hij)))
  · intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hloc := UpperTheory.V.Base.mk_mem_locSel.mp hx
    obtain ⟨hzc, hzco⟩ := z.2
    set c : G ℚ Ω → QO l O := ι z with hcE
    have hcoc : IsCoc α c := by
      refine ⟨(IsLocallyConstant.iff_continuous _).mpr
        (hzc.comp (continuous_id.subtype_mk fun g => Subgroup.mem_top g)), fun g h => ?_⟩
      exact hzco ⟨g, Subgroup.mem_top g⟩ ⟨h, Subgroup.mem_top h⟩
    obtain ⟨m, hc', hδ'⟩ := norm_coc α δ hδ c hcoc
    set c' : G ℚ Ω → QO l O := fun g => c g - ((α g : O) • m - m) with hcE'
    have hs : ∀ D ∈ shaFam ℚ Ω l, ∃ m' : QO l O, ∀ g ∈ D, c' g = (α g : O) • m' - m' := by
      intro D hD
      obtain ⟨mD, hmD⟩ := hloc D hD
      refine ⟨mD - m, fun g hg => ?_⟩
      have e := hmD ⟨g, Subgroup.mem_top g⟩ hg
      change c g = (α g : O) • mD - mD at e
      simp only [hcE', e]
      module
    obtain ⟨a, ha0, hmem⟩ := mem_shT Ω l O α δ F h1 h2 c' hc' hδ' hs
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hmem' : c' ∈ ShT (QO l O) α δ F (ϖ ^ k) :=
      shT_mono α δ F (Units.mul_left_dvd.mpr dvd_rfl) hmem
    let z' : Z1U (twist₂ l α) T := ⟨fun v => c' v.1,
      (hc'.1.comp_continuous continuous_subtype_val).continuous, fun v w => hc'.2 v.1 w.1⟩
    have hq : Q z = Q z' := by
      simp only [Q, Submodule.mkQ_apply]
      rw [UpperTheory.V.Base.mk_eq_mk]
      refine ⟨m, fun v => ?_⟩
      change c v.1 - c' v.1 = (α v.1 : O) • m - m
      simp only [hcE']
      abel
    change Q z ∈ _
    rw [hq]
    exact Submodule.mem_iSup_of_mem k (Submodule.mem_map_of_mem (show z' ∈ _ from hmem'))
  · intro n₀
    refine ⟨n₀, le_rfl, ?_⟩
    calc Module.length O (P n₀) ≤ Module.length O ((ShT (QO l O) α δ F (ϖ ^ n₀)).comap ι) :=
          Module.length_le_of_surjective (Q.submoduleMap _) (LinearMap.submoduleMap_surjective Q _)
      _ ≤ Module.length O (ShT (QO l O) α δ F (ϖ ^ n₀)) :=
          Module.length_le_of_injective (ι.restrict fun x hx => hx)
            (fun x y hxy => Subtype.ext (hι (congrArg Subtype.val hxy)))
      _ ≤ n := hn _ (pow_ne_zero _ hϖ.ne_zero)
end
