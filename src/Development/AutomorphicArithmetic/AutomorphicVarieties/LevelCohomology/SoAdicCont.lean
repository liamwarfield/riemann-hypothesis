module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDualGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoAdicCont
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem one_le_addVal_toNat_of_ne_zero_of_not_isUnit {l : ℕ} [Fact l.Prime] (c : HV.Coef l) (y : c.O) (h0 : y ≠ 0)
    (hu : ¬ IsUnit y) : 1 ≤ (IsDiscreteValuationRing.addVal c.O y).toNat := by
  have h1 : IsDiscreteValuationRing.addVal c.O y ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have h2 : IsDiscreteValuationRing.addVal c.O y ≠ 0 := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_zero_iff]
  rw [Nat.one_le_iff_ne_zero, Ne, ENat.toNat_eq_zero]
  tauto

private theorem prime_inv_pow_lt_one_of_one_le {l : ℕ} [Fact l.Prime] (k : ℕ) (hk : 1 ≤ k) :
    ((l : ℝ)⁻¹) ^ k < 1 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl) (by omega)

private theorem base_eO_toNat_ne_zero {l : ℕ} [Fact l.Prime] (c : HV.Coef l) :
    (Base.eO l c.O).toNat ≠ 0 := by
  intro he
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have h := Base.normO l c.O w hw.ne_zero
  rw [he, pow_zero] at h
  have hk := prime_inv_pow_lt_one_of_one_le (l := l) _ (one_le_addVal_toNat_of_ne_zero_of_not_isUnit c w hw.ne_zero hw.not_isUnit)
  linarith

private theorem norm_lt_one_of_not_isUnit {l : ℕ} [Fact l.Prime] (c : HV.Coef l) (y : c.O) (hy : ¬ IsUnit y) :
    ‖(y : PadicAlgCl l)‖ < 1 := by
  by_cases h0 : y = 0
  · subst h0
    simp
  · have he := base_eO_toNat_ne_zero c
    have h := Base.normO l c.O y h0
    have hk := prime_inv_pow_lt_one_of_one_le (l := l) _ (one_le_addVal_toNat_of_ne_zero_of_not_isUnit c y h0 hy)
    rw [← h] at hk
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).mp hk

private theorem dvd_of_norm_lt {l : ℕ} [Fact l.Prime] (c : HV.Coef l) (a x : c.O)
    (h : ‖(x : PadicAlgCl l)‖ < ‖(a : PadicAlgCl l)‖) : a ∣ x := by
  by_cases hx : x = 0
  · subst hx
    exact dvd_zero a
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [ZeroMemClass.coe_zero, norm_zero] at h
    linarith [norm_nonneg (x : PadicAlgCl l)]
  have he := base_eO_toNat_ne_zero c
  have hxa := pow_lt_pow_left₀ h (norm_nonneg _) he
  rw [Base.normO l c.O x hx, Base.normO l c.O a ha] at hxa
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlt := (pow_lt_pow_iff_right_of_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl)).mp hxa
  have hta : IsDiscreteValuationRing.addVal c.O a ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have htx : IsDiscreteValuationRing.addVal c.O x ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, ← ENat.coe_toNat hta, ← ENat.coe_toNat htx]
  exact_mod_cast hlt.le

private theorem ev_dvd {l : ℕ} [Fact l.Prime] (c : HV.Coef l) (a : c.O) (ha : a ≠ 0) (x : c.O) :
    ∀ᶠ y in nhds x, a ∣ y - x := by
  have ha' : 0 < ‖(a : PadicAlgCl l)‖ := norm_pos_iff.mpr (by exact_mod_cast ha)
  have hc : Continuous (fun y : c.O => ‖(y : PadicAlgCl l) - x‖) :=
    (continuous_subtype_val.sub continuous_const).norm
  have h0 : ‖((x : c.O) : PadicAlgCl l) - x‖ < ‖(a : PadicAlgCl l)‖ := by
    rw [sub_self, norm_zero]
    exact ha'
  have hev : ∀ᶠ y : c.O in nhds x, ‖(y : PadicAlgCl l) - x‖ < ‖(a : PadicAlgCl l)‖ :=
    hc.continuousAt.eventually_lt (continuous_const (y := ‖(a : PadicAlgCl l)‖)).continuousAt h0
  filter_upwards [hev] with y hy
  apply dvd_of_norm_lt c
  push_cast
  exact hy

private theorem norm_coef_O_coe_padicAlgCl_le_one {l : ℕ} [Fact l.Prime] (c : HV.Coef l) (y : c.O) :
    ‖(y : PadicAlgCl l)‖ ≤ 1 := by
  by_cases hu : IsUnit y
  · have h := Base.normO l c.O y hu.ne_zero
    rw [IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu, ENat.toNat_zero, pow_zero] at h
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) (base_eO_toNat_ne_zero c)).mp h).le
  · exact (norm_lt_one_of_not_isUnit c y hu).le

theorem UpperTheory.V.X.So.adicCont :
    ∀ (l : ℕ) [Fact l.Prime] (c : HV.Coef l), (∀ a : c.O, a ≠ 0 → Continuous (Lev.mk a)) ∧ ∀ (X : Type) [TopologicalSpace X] (z : X → c.O), Alg.AdicCont (maximalIdeal c.O) z ↔ Continuous z := by
  intro l _ c
  refine ⟨fun a ha => ?_, fun X _ z => ?_⟩
  · apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [ev_dvd c a ha x] with y hy
    rw [← sub_eq_zero, ← map_sub, Lev.mk_eq_zero]
    exact hy
  · obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible c.O
    have hm : ∀ N : ℕ, maximalIdeal c.O ^ N = Ideal.span {w ^ N} := fun N => by
      rw [hw.maximalIdeal_eq, Ideal.span_singleton_pow]
    constructor
    · intro hz
      apply continuous_induced_rng.mpr
      rw [continuous_iff_continuousAt]
      intro g0
      rw [ContinuousAt, Metric.tendsto_nhds]
      intro ε hε
      have hw1 : ‖(w : PadicAlgCl l)‖ < 1 := norm_lt_one_of_not_isUnit c w hw.not_isUnit
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hw1
      have hl := (IsLocallyConstant.iff_eventually_eq _).mp (hz N) g0
      filter_upwards [hl] with g hg
      rw [Ideal.Quotient.eq, hm, Ideal.mem_span_singleton] at hg
      obtain ⟨t, ht⟩ := hg
      rw [dist_eq_norm]
      simp only [Function.comp_apply]
      have he : ((z g : c.O) : PadicAlgCl l) - z g0 = (w : PadicAlgCl l) ^ N * t := by
        exact_mod_cast congrArg (fun u : c.O => (u : PadicAlgCl l)) ht
      rw [he, norm_mul, norm_pow]
      calc ‖(w : PadicAlgCl l)‖ ^ N * ‖(t : PadicAlgCl l)‖ ≤ ‖(w : PadicAlgCl l)‖ ^ N * 1 :=
            mul_le_mul_of_nonneg_left (norm_coef_O_coe_padicAlgCl_le_one c t) (by positivity)
        _ < ε := by
          rw [mul_one]
          exact hN
    · intro hz N
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g0
      have hne : w ^ N ≠ 0 := pow_ne_zero _ hw.ne_zero
      have h1 := (hz.tendsto g0).eventually (ev_dvd c (w ^ N) hne (z g0))
      filter_upwards [h1] with g hg
      rw [Ideal.Quotient.eq, hm, Ideal.mem_span_singleton]
      exact hg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDualEmb
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.dualEmb :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (a : O), a ≠ 0 → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module O M] [Module (ZMod (l ^ r)) M], Nonempty (M ≃ₗ[O] (O ⧸ Ideal.span {a})) → ∃ ι : ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M →+ QO l O, Function.Injective ι ∧ (∀ w, a • w = 0 ↔ w ∈ Set.range ι) ∧ ∀ (y : ℤ_[l]) (x : O) (φ φ' : ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M), (∀ m, φ' m = PadicInt.toZModPow r y * φ (x • m)) → ι φ' = (algebraMap ℤ_[l] O y * x) • ι φ := by
  intro l _ O _ _ _ _ _ a ha r M _ _ _ hM
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨φ₀, hker, hsurj⟩ := UpperTheory.V.X.So.dualGen l O a ha r M hM
  obtain ⟨w, hw⟩ := (UpperTheory.V.ML.qoCyc l O).2.1 a ha
  choose c hc using hsurj
  have key : ∀ x x' : O, (∀ m : M, φ₀ (x • m) = φ₀ (x' • m)) → x • w = x' • w := by
    intro x x' h
    have hd : a ∣ x - x' := (hker _).1 (fun m => by rw [sub_smul, map_sub, h, sub_self])
    have h0 := (hw (x - x')).2 hd
    rwa [sub_smul, sub_eq_zero] at h0
  have kill : ∀ (s : O) (n : M), ((l : O) ^ r * s) • n = 0 := by
    intro s n
    rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)),
      ZMod.natCast_self, zero_smul]
  have scal : ∀ (y : ℤ_[l]) (n : M),
      φ₀ (algebraMap ℤ_[l] O y • n) = PadicInt.toZModPow r y * φ₀ n := by
    intro y n
    have hmem : y - ((PadicInt.toZModPow r y).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
    obtain ⟨t, ht⟩ := hmem
    have hy : y = ((PadicInt.toZModPow r y).val : ℤ_[l]) + (l : ℤ_[l]) ^ r * t := by
      rw [← ht]; ring
    conv_lhs => rw [hy]
    rw [map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_smul, kill, add_zero,
      Nat.cast_smul_eq_nsmul O, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  refine ⟨{ toFun := fun φ => c φ • w, map_zero' := ?_, map_add' := ?_ }, ?_, ?_, ?_⟩
  · show c 0 • w = 0
    rw [← zero_smul O w]
    apply key
    intro m
    rw [← hc, zero_smul, map_zero]
    rfl
  · intro φ ψ
    show c (φ + ψ) • w = c φ • w + c ψ • w
    rw [← add_smul]
    apply key
    intro m
    have e1 := hc (φ + ψ) m
    have e2 := hc φ m
    have e3 := hc ψ m
    rw [add_smul, map_add (f := _), ← e1, ← e2, ← e3]
    exact TDual.add_apply φ ψ m
  · rw [injective_iff_map_eq_zero]
    intro φ hφ
    change c φ • w = 0 at hφ
    have hd := (hw _).1 hφ
    apply LinearMap.ext
    intro m
    rw [hc φ m, (hker _).2 hd m]
    rfl
  · intro v
    constructor
    · intro hv
      obtain ⟨y, rfl⟩ := (UpperTheory.V.ML.qoCyc l O).2.2.1 a w ha hw v hv
      refine ⟨(φ₀.toAddMonoidHom.comp (DistribSMul.toAddMonoidHom M y)).toZModLinearMap (l ^ r), ?_⟩
      show c _ • w = y • w
      apply key
      intro m
      rw [← hc]
      rfl
    · rintro ⟨φ, rfl⟩
      show a • (c φ • w) = 0
      rw [smul_smul]
      exact (hw _).2 (dvd_mul_right a _)
  · intro y x φ φ' h
    show c φ' • w = (algebraMap ℤ_[l] O y * x) • (c φ • w)
    rw [smul_smul]
    apply key
    intro m
    have e1 := hc φ' m
    have e2 := hc φ (x • m)
    rw [← e1]
    refine (h m).trans ((congrArg (fun z => PadicInt.toZModPow r y * z) e2).trans ?_)
    rw [smul_smul,
      show algebraMap ℤ_[l] O y * x * c φ = algebraMap ℤ_[l] O y * (c φ * x) by ring,
      mul_smul (algebraMap ℤ_[l] O y), scal]
end
