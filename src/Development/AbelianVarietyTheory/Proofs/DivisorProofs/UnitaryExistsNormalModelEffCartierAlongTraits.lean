module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryComparisonLatticePeriodsAtPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastIntCombinationMinimiserCellUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelCartierDivisorThetaSetup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsLinearSimilitudeMemKernelPolarisatiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorOrdersAllTraitsOverModuli

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteThetaTuplesLeastOrdersUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteThetaTuplesLeastOrdersUnitary
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.exists_uLocTuples_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), ∃ (ι : ℕ) (K : Type) (_ : Fintype K) (Jk : K → Type) (_ : ∀ k, Fintype (Jk k)) (t : ∀ k, Jk k → X₁.Ω₁), 1 ≤ ι ∧ (∀ k j, t k j ≠ 0) ∧ ∀ (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ (∀ j, UOrdGe M T ξ (t k j) a) ∧ ∃ j, UOrdEq M T ξ (t k j) a := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁
  have hNodd : Odd X₁.S.N := by rw [X₁.ρ.N_eq]; exact (X₁.ρ.n_odd.pow).pow
  have hN2 := X₁.S.N_ge
  have hN3 : 3 ≤ X₁.S.N := by obtain ⟨j, hj⟩ := hNodd; omega
  haveI hN0 : NeZero X₁.S.N := ⟨by omega⟩
  obtain ⟨m₁, m₂, hm₁, hm₂, hX⟩ := GlobalTheory.T.unitaryComparison_lattice_periods_at_point E H Dw hpq l Xo c C X₁
  obtain ⟨B, ι₀, 𝓛, hι₀, hT⟩ := GlobalTheory.T.least_intCombination_minimiserCell_unitary E H (min Dw.p Dw.q) φ hφ X₁.S.N hN3 hNodd
  haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by omega)⟩
  haveI : NeZero ((X₁.S.r * X₁.S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  haveI : Finite (AddSubgroup X₁.S.Gam) :=
    Finite.of_injective (fun H : AddSubgroup X₁.S.Gam => (H : Set X₁.S.Gam)) SetLike.coe_injective
  haveI : ∀ T₀ : AddSubgroup X₁.S.Gam, Finite (T₀ →+ ZMod X₁.S.N) := fun T₀ =>
    Finite.of_injective (fun f : T₀ →+ ZMod X₁.S.N => (f : T₀ → ZMod X₁.S.N)) DFunLike.coe_injective
  let Dt := Σ T₀ : AddSubgroup X₁.S.Gam, (T₀ →+ ZMod X₁.S.N) × (X₁.S.J × (T₀ → ZMod ((X₁.S.r * X₁.S.N) ^ 2))) × X₁.S.Gam
  haveI : Finite Dt := inferInstance
  let Es : Set X₁.Ω₁ := {v | v ≠ 0} ∩ Set.range (fun d : Dt => X₁.S.FF d.1 d.2.1 d.2.2.1 / X₁.S.th d.2.2.2)
  have hEs : Es.Finite := (Set.finite_range _).inter_of_right _
  letI : Fintype Es := hEs.fintype
  let K := Σ n : Fin B, Σ _ : {L // L ∈ 𝓛 n.1}, ((Fin n.1 → ZMod X₁.S.N) → Es)
  let Jk : K → Type := fun k => {ν // ν ∈ k.2.1.1}
  let t : ∀ k, Jk k → X₁.Ω₁ := fun k j => ∏ cl, ((k.2.2 cl : Es) : X₁.Ω₁) ^ ((m₁ : ℤ) * j.1 cl)
  refine ⟨m₂ * ι₀, K, inferInstance, Jk, fun k => inferInstance, t, ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  · intro k j
    exact Finset.prod_ne_zero_iff.2 fun cl _ => zpow_ne_zero _ (k.2.2 cl).2.1
  intro M U₀ EE out hAdm hEE x
  obtain ⟨X, _, _, _, _, n, eb, b₀, μ, e, hrank, hbal, hpos, hμ, hmin, he, htr⟩ := hX M U₀ EE out hAdm hEE x
  obtain ⟨hnB, hL⟩ := hT n X hrank eb
  obtain ⟨L, hLmem, hLprop⟩ := hL b₀ hbal hpos μ hμ hmin
  have heE : ∀ cl, e cl ∈ Es := fun cl => by
    obtain ⟨hne, T₀, c', κ, x₀, _, hc⟩ := he cl
    exact ⟨hne, ⟨⟨T₀, c', κ, x₀⟩, hc.symm⟩⟩
  refine ⟨⟨⟨n, hnB⟩, ⟨L, hLmem⟩, fun cl => ⟨e cl, heE cl⟩⟩, ?_⟩
  intro T ξ hthr hspec
  obtain ⟨π, hπs, hπmin, hq⟩ := htr T ξ hthr hspec
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  set b' : LinearMap.BilinForm ℤ X := pull π T.be with hb'
  have hbeBal : T.be ∈ balForms H.bar T.P.D.toPre.X := by rw [balForms_eq_levelForms]; exact T.lev
  have hb'bal : b' ∈ balForms H.bar X := pull_mem π hbeBal
  have hμ0 : μ 0 = 0 := by
    by_contra h0
    have h1 := hmin 0 0 (fun i => by simp)
    have h2 := hpos _ h0
    simp at h1
    omega
  have hb'psd : ∀ y, 0 ≤ b' y y := by
    intro y
    have h1 := hπmin 0 ((X₁.S.N : ℤ) • y) (fun i => by simp)
    have hNpos : (0 : ℤ) < X₁.S.N := by exact_mod_cast (show 0 < X₁.S.N by omega)
    have h2 : (0 : ℤ) ≤ (X₁.S.N : ℤ) * ((X₁.S.N : ℤ) * T.be (π y) (π y)) := by
      simpa [hμ0, map_zsmul, LinearMap.smul_apply, smul_eq_mul] using h1
    show 0 ≤ T.be (π y) (π y)
    exact (mul_nonneg_iff_of_pos_left hNpos).1 ((mul_nonneg_iff_of_pos_left hNpos).1 h2)
  obtain ⟨hle, ν₀, hν₀, heq⟩ := hLprop b' hb'bal hb'psd hπmin
  have hφeq : φ.evalZ b' = φ.evalZ T.be := evalZ_pull φ hπs T.be
  have hφ0 : 0 ≤ φ.evalZ b' := (hφ X hrank).evalZ_nonneg hb'bal hb'psd
  set y : Sp (FractionRing T.V) ⟶ M.Z := jK T.V ≫ ξ with hy
  set z₀ := y (IsLocalRing.closedPoint (FractionRing T.V)) with hz₀
  have hsp : ∀ w, y w ⤳ z₀ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hz₀U : z₀ ∈ U₀ := by
    obtain ⟨ξ₀, hξ₀, -⟩ := hthr
    have hz : z₀ = (ξ₀ ≫ U₀.ι) (IsLocalRing.closedPoint (FractionRing T.V)) := by rw [hξ₀]
    rw [hz]
    have hm : (ξ₀ ≫ U₀.ι) (IsLocalRing.closedPoint (FractionRing T.V)) ∈ Set.range U₀.ι := by
      exact ⟨ξ₀ (IsLocalRing.closedPoint (FractionRing T.V)), rfl⟩
    rw [U₀.range_ι] at hm; exact hm
  have hO : M.ringOn U₀ ≤ M.O z₀ := RatModel.ringOn_le_O (M := M) hz₀U
  have hOv := hAdm.1
  have hFFR : ∀ (T₀ : AddSubgroup X₁.S.Gam) c' κ, X₁.S.FF T₀ c' κ ∈ X₁.S.R := by
    intro T₀ c' κ
    haveI : Fintype T₀ := Fintype.ofFinite _
    unfold ThetaSys.FF
    rw [finsum_eq_sum_of_fintype]
    exact Subalgebra.sum_mem _ fun t _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (X₁.S.ev_mem _ _))
  have hunit : ∀ cl, e cl ≠ 0 ∧ e cl ∈ M.O z₀ ∧ (e cl)⁻¹ ∈ M.O z₀ := by
    intro cl
    obtain ⟨hne, T₀, c', κ, x₀, hiso, hc⟩ := he cl
    rw [hc] at hne ⊢
    have hF : X₁.S.FF T₀ c' κ ≠ 0 := (div_ne_zero_iff.1 hne).1
    have hth : X₁.S.th x₀ ≠ 0 := (div_ne_zero_iff.1 hne).2
    refine ⟨hne, hO ?_, hO ?_⟩
    · rw [div_eq_mul_inv]; exact Subalgebra.mul_mem _ (hOv.le (hFFR T₀ c' κ)) (hOv.th_unit x₀ hth)
    · rw [inv_div, div_eq_mul_inv]
      exact Subalgebra.mul_mem _ (hOv.le (X₁.S.th_mem x₀)) (hOv.FF_unit T₀ c' κ hiso hF)
  have hvne : ∀ cl, M.val y (e cl) ≠ 0 := by
    intro cl
    have h1 := RatModel.val_mul (M := M) hsp (hunit cl).2.1 (hunit cl).2.2
    rw [mul_inv_cancel₀ (hunit cl).1, RatModel.val_one] at h1
    exact left_ne_zero_of_mul_eq_one h1.symm
  have hpow : ∀ cl, M.val y (e cl ^ m₁) = M.val y (e cl) ^ m₁ := by
    intro cl
    have := GlobalTheory.T.integralModel_value_prod_zpow_localUnits M y z₀ hsp (Finset.univ : Finset Unit) (fun _ => e cl) (fun _ => (m₁ : ℤ)) fun _ => hunit cl
    simpa using this
  choose v w hvw using fun cl => GlobalTheory.T.fractionRing_eq_uniformiser_zpow_mul_unit T.irr (M.val y (e cl)) (hvne cl)
  have hϖ0 : algebraMap T.V (FractionRing T.V) T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 T.irr.ne_zero
  have hunitK : ∀ (a : T.Vˣ) (k : ℤ), algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
      (algebraMap T.V (FractionRing T.V) (a : T.V)) ^ k := by
    intro a k
    have h1 : algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
        ((Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom (a ^ k) : (FractionRing T.V)ˣ) : FractionRing T.V) := rfl
    rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]; rfl
  have hNv : ∀ cl, (m₁ : ℤ) * v cl = (m₂ : ℤ) * b' (μ cl) (μ cl) := by
    intro cl
    obtain ⟨w', hw'⟩ := hq cl
    have hq0 : 0 ≤ (m₂ : ℤ) * b' (μ cl) (μ cl) := mul_nonneg (by positivity) (hb'psd _)
    rw [hpow] at hw'
    have h2 : algebraMap T.V (FractionRing T.V) T.ϖ ^ ((m₁ : ℤ) * v cl) *
        algebraMap T.V (FractionRing T.V) ((w cl ^ (m₁ : ℤ) : T.Vˣ) : T.V) =
        algebraMap T.V (FractionRing T.V) T.ϖ ^ ((((m₂ : ℤ) * b' (μ cl) (μ cl)).toNat : ℕ) : ℤ) *
        algebraMap T.V (FractionRing T.V) (w' : T.V) := by
      rw [hunitK, mul_comm (m₁ : ℤ) (v cl), zpow_mul, zpow_natCast, zpow_natCast, ← mul_pow, ← hvw cl]
      rw [show (((m₂ : ℤ) * b' (μ cl) (μ cl)).toNat) = (((m₂ : ℤ) * T.be (π (μ cl)) (π (μ cl))).toNat) from rfl]
      rw [hw', map_mul, map_pow, zpow_natCast]
    have := GlobalTheory.T.uniformiser_zpow_mul_unit_exponent_unique T.irr _ _ _ _ h2
    rw [this, Int.toNat_of_nonneg hq0]
  let Ev : ((Fin n → ZMod X₁.S.N) → ℤ) → ℤ := fun ν => ∑ cl, v cl * ((m₁ : ℤ) * ν cl)
  have hE : ∀ ν, (Ev ν : ℝ) = (m₂ : ℝ) * ∑ cl, (ν cl : ℝ) * (b' (μ cl) (μ cl) : ℝ) := by
    intro ν
    have h1 : Ev ν = (m₂ : ℤ) * ∑ cl, ν cl * b' (μ cl) (μ cl) := by
      simp only [Ev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun cl _ => ?_
      have := hNv cl
      linear_combination (ν cl) * this
    rw [h1]; push_cast; ring
  have hzs : ∀ (f : (Fin n → ZMod X₁.S.N) → ℤ) (s : Finset (Fin n → ZMod X₁.S.N)),
      ∏ cl ∈ s, algebraMap T.V (FractionRing T.V) T.ϖ ^ f cl = algebraMap T.V (FractionRing T.V) T.ϖ ^ ∑ cl ∈ s, f cl := by
    intro f s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hϖ0]
  have hval : ∀ ν, M.val y (∏ cl, e cl ^ ((m₁ : ℤ) * ν cl)) = algebraMap T.V (FractionRing T.V) T.ϖ ^ Ev ν *
      algebraMap T.V (FractionRing T.V) ((∏ cl, w cl ^ ((m₁ : ℤ) * ν cl) : T.Vˣ) : T.V) := by
    intro ν
    rw [GlobalTheory.T.integralModel_value_prod_zpow_localUnits M y z₀ hsp _ _ _ fun cl => hunit cl]
    simp only [hvw, mul_zpow, Finset.prod_mul_distrib, ← zpow_mul, ← hunitK]
    rw [hzs, Units.coe_prod, map_prod]
  have hprodO : ∀ ν : (Fin n → ZMod X₁.S.N) → ℤ, (∏ cl, e cl ^ ((m₁ : ℤ) * ν cl)) ∈ M.O z₀ := by
    intro ν
    refine Subalgebra.prod_mem _ fun cl _ => ?_
    rcases Int.eq_nat_or_neg ((m₁ : ℤ) * ν cl) with ⟨k, hk | hk⟩ <;> rw [hk]
    · rw [zpow_natCast]; exact Subalgebra.pow_mem _ (hunit cl).2.1 k
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact Subalgebra.pow_mem _ (hunit cl).2.2 k
  have hge : ∀ ν ∈ L, ((m₂ * ι₀ : ℕ) : ℝ) * φ.evalZ T.be ≤ Ev ν := by
    intro ν hν
    have h1 := mul_le_mul_of_nonneg_left (hle ν hν) (Nat.cast_nonneg (α := ℝ) m₂)
    rw [hE ν, ← hφeq]; push_cast
    nlinarith
  have hE0 : ((Ev ν₀ : ℤ) : ℝ) = ((m₂ * ι₀ : ℕ) : ℝ) * φ.evalZ T.be := by
    rw [hE ν₀, ← heq, ← hφeq]; push_cast; ring
  have hEnn : 0 ≤ Ev ν₀ := by
    have : (0 : ℝ) ≤ (Ev ν₀ : ℝ) := by
      rw [hE0]; exact mul_nonneg (Nat.cast_nonneg _) (hφeq ▸ hφ0)
    exact_mod_cast this
  refine ⟨(Ev ν₀).toNat, ?_, ?_, ?_⟩
  · rw [← hE0]; exact_mod_cast Int.toNat_of_nonneg hEnn
  · intro j
    show UOrdGe M T ξ (∏ cl, e cl ^ ((m₁ : ℤ) * j.1 cl)) _
    have hle' : Ev ν₀ ≤ Ev j.1 := by
      have := hge j.1 j.2; rw [← hE0] at this; exact_mod_cast this
    obtain ⟨d, hd⟩ : ∃ d : ℕ, Ev j.1 = ((Ev ν₀).toNat : ℤ) + d := ⟨(Ev j.1 - Ev ν₀).toNat, by omega⟩
    refine ⟨hprodO j.1, T.ϖ ^ d * ((∏ cl, w cl ^ ((m₁ : ℤ) * j.1 cl) : T.Vˣ) : T.V), ?_⟩
    rw [hval, hd, map_mul, map_mul, map_pow, map_pow, zpow_add₀ hϖ0, zpow_natCast, zpow_natCast, mul_assoc]
  · refine ⟨⟨ν₀, hν₀⟩, ?_⟩
    show UOrdEq M T ξ (∏ cl, e cl ^ ((m₁ : ℤ) * ν₀ cl)) _
    refine ⟨∏ cl, w cl ^ ((m₁ : ℤ) * ν₀ cl), ?_⟩
    rw [hval, map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg hEnn]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteThetaTuplesLeastOrdersUnitaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_theta_tuples_least_orders_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), ∃ (ι : ℕ) (K : Type) (_ : Fintype K) (Jk : K → Type) (_ : ∀ k, Fintype (Jk k)) (t : ∀ k, Jk k → X₁.Ω₁), 1 ≤ ι ∧ (∀ k j, t k j ≠ 0) ∧ ∀ (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ (∀ j, UOrdGe M T ξ (t k j) a) ∧ ∃ j, UOrdEq M T ξ (t k j) a := by
  first | exact @GlobalTheory.UPoinc.exists_uLocTuples_theta | exact GlobalTheory.UPoinc.exists_uLocTuples_theta | (intros; apply GlobalTheory.UPoinc.exists_uLocTuples_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitDivisorSupportNotMemModuliRange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitDivisorSupportNotMemModuliRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.SuppTrait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem isLocallyNoetherian_model {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω]
    (M : RatModel o' Ω) : IsLocallyNoetherian M.Z := by
  haveI := ArithBase.ded (o := o') (Ω := Ω)
  haveI := M.lft
  exact LocallyOfFiniteType.isLocallyNoetherian M.s

theorem centre_apply {X : Scheme.{0}} {x : X} {V : Type} [CommRing V] [IsLocalRing V] (g : X.presheaf.stalk x →+* V)
    [IsLocalHom g] : (spMap g ≫ X.fromSpecStalk x) (closedPoint V) = x := by
  refine (Scheme.Hom.comp_apply _ _ _).trans
    (Eq.trans (congrArg (X.fromSpecStalk x) ?_) (Scheme.fromSpecStalk_closedPoint (x := x)))
  exact comap_closedPoint g

theorem exists_uTrait_centre {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω)
    (y₀ : Sp Ω ⟶ Xo.XF c) (x : M.Z) :
    ∃ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V),
      ξ (closedPoint T.V) = x ∧ jK T.V ≫ ξ = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  haveI := ArithBase.char (o := o') (Ω := Ω)
  haveI := isLocallyNoetherian_model M
  haveI : CharZero (M.Z.presheaf.stalk x) := RingHom.charZero (M.stalkHom x)
  obtain ⟨V, _, _, _, θ, ⟨hd, hcomp, -⟩, hθ, hl⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (M.Z.presheaf.stalk x)
  haveI := hd
  haveI := hcomp
  haveI : CharZero V := charZero_of_injective_ringHom hθ
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  let θ' : M.O x →+* FractionRing V :=
    ((algebraMap V (FractionRing V)).comp θ).comp (M.stalkEquiv x).symm.toRingHom
  have hθ' : Function.Injective θ' :=
    (IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (M.stalkEquiv x).symm.injective)
  let γ₀ : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O x) (K := Ω) hθ'
  have hγ₀ : ∀ a, γ₀ (M.stalkHom x a) = algebraMap V (FractionRing V) (θ a) := by
    intro a
    have h := IsFractionRing.lift_algebraMap (A := M.O x) (K := Ω) hθ' (M.stalkEquiv x a)
    rw [← RatModel.coe_stalkEquiv]
    refine h.trans ?_
    simp [θ']
  obtain ⟨T, f, fK, -, hfl, -, hc, hy⟩ := GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V hB hd (spMap γ₀ ≫ y₀)
  haveI := hfl
  refine ⟨T, spMap (f.comp θ) ≫ M.Z.fromSpecStalk x, fK.comp γ₀, centre_apply _, ?_, ?_⟩
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← GlobalTheory.Poinc.GenTrait.spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e,
      ← Formalism.L2.Pj.spMap_comp', Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']

end GlobalTheory.UPoinc.SuppTrait

namespace GlobalTheory.UPoinc.SuppTrait

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem lift_i_of_closedPoint (C : UCompact Xo c) (V : Type) [CommRing V] [IsLocalRing V] (g : Sp V ⟶ C.Z)
    (hg : g (closedPoint V) ∈ Set.range C.i) : ∃ σ : Sp V ⟶ Xo.XF c, σ ≫ C.i = g := by
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  haveI := C.iF_open
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := inferInstance
  have hinj : Function.Injective (pullback.fst C.z (spMap C.b)) :=
    (pullback.fst C.z (spMap C.b)).isEmbedding.injective
  obtain ⟨x, hx⟩ := hg
  let φ : C.o →+* V := (Spec.preimage (g ≫ C.z)).hom
  have hφ : spMap φ = g ≫ C.z := Spec.map_preimage _
  have hc : spMap φ (closedPoint V) = spMap C.b ((C.iF ≫ pullback.snd C.z (spMap C.b)) x) := by
    rw [hφ]
    refine (Scheme.Hom.comp_apply g C.z _).trans ((congrArg C.z hx.symm).trans ?_)
    show C.z ((C.iF ≫ pullback.fst C.z (spMap C.b)) x) = _
    rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.condition, ← Category.assoc]
    rfl
  have hunit : ∀ a : C.o, a ≠ 0 → IsUnit (φ a) := by
    intro a ha
    by_contra hn
    have hm : a ∈ (spMap φ (closedPoint V)).asIdeal := by
      show φ a ∈ (closedPoint V).asIdeal
      exact (IsLocalRing.mem_maximalIdeal _).2 hn
    rw [hc] at hm
    haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).isPrime
    have hb : C.b a ∈ ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal := hm
    rw [Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal), Ideal.mem_bot] at hb
    exact ha (C.inj (hb.trans (map_zero C.b).symm))
  let ψ : c.F →+* V := IsLocalization.lift (M := nonZeroDivisors C.o) (S := c.F) (g := φ)
    (fun a => hunit a (nonZeroDivisors.ne_zero a.2))
  have hψ : ψ.comp C.b = φ := RingHom.ext fun a => IsLocalization.lift_eq (M := nonZeroDivisors C.o) (S := c.F) _ a
  have hsq : g ≫ C.z = spMap ψ ≫ spMap C.b := by
    rw [← hφ, ← hψ]; exact GlobalTheory.UTraitPt.spMap_comp_eq _ _
  let g₁ : Sp V ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap ψ) hsq
  have e1 : g₁ ≫ pullback.fst C.z (spMap C.b) = g := pullback.lift_fst _ _ _
  have hx₁ : g₁ (closedPoint V) = C.iF x := hinj ((Scheme.Hom.comp_apply g₁ (pullback.fst C.z (spMap C.b)) _).symm.trans
    ((congrArg (fun h : Sp V ⟶ C.Z => h (closedPoint V)) e1).trans
      (hx.symm.trans (Scheme.Hom.comp_apply C.iF (pullback.fst C.z (spMap C.b)) x))))
  have hr : Set.range g₁ ⊆ Set.range C.iF := by
    rintro _ ⟨w, rfl⟩
    have hs : g₁ w ⤳ g₁ (closedPoint V) := (IsLocalRing.specializes_closedPoint w).map g₁.continuous
    rw [hx₁] at hs
    exact hs.mem_open (IsOpenImmersion.isOpen_range C.iF) ⟨x, rfl⟩
  refine ⟨IsOpenImmersion.lift C.iF g₁ hr, ?_⟩
  show _ ≫ C.iF ≫ pullback.fst C.z (spMap C.b) = g
  rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

theorem subsingleton_of_extends (T : UTrait Xo c) (σ : Sp T.V ⟶ Xo.XF c) (h : jK T.V ≫ σ = T.y) :
    Subsingleton T.P.D.toPre.X := by
  obtain ⟨hdvr, -, -⟩ := T.cdvr
  haveI := hdvr
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  have hsemi := Xo.univ.t.semi
  have hAb : IsAbelianScheme Xo.univ.t.G :=
    { comm := hsemi.comm, smooth := hsemi.smooth, proper := Xo.univ.proper, geomConnected := hsemi.geomConnected }
  let f : Sp T.V ⟶ Xo.X := σ ≫ pullback.fst _ _
  have hB : IsAbelianScheme ((Over.pullback f).obj Xo.univ.t.G) := by
    have := hAb.comm
    have := hAb.smooth
    have := hAb.proper
    have := hAb.geomConnected
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · change Smooth (pullback.snd Xo.univ.t.G.hom f)
      infer_instance
    · change IsProper (pullback.snd Xo.univ.t.G.hom f)
      infer_instance
    · change GeometricallyConnected (pullback.snd Xo.univ.t.G.hom f)
      infer_instance
  obtain ⟨e₁, he₁, -⟩ := grpPullback_iso m₁.cart (isGrpPullback_pullback T.t.G (jK T.V))
  have h₂ := (isGrpPullback_pullback ((Over.pullback f).obj Xo.univ.t.G) (jK T.V)).comp
    (isGrpPullback_pullback Xo.univ.t.G f)
  obtain ⟨e₂, he₂, -⟩ := grpPullback_iso (m₂.cart.congr (by rw [← h, Category.assoc]) rfl) h₂
  haveI := he₁
  haveI := he₂
  have hsemiB : IsSemiAbelian ((Over.pullback f).obj Xo.univ.t.G) := by
    open MonObj in
    have := hB.proper
    refine ⟨hB.comm, hB.smooth, inferInstance, inferInstance, hB.geomConnected, ?_⟩
    intro Ω _ _ p
    let A := (Over.pullback p).obj ((Over.pullback f).obj Xo.univ.t.G)
    have hA : IsAbelianScheme A := by
      have := hB.comm
      have := hB.smooth
      have := hB.proper
      have := hB.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd _ p); infer_instance
      · change IsProper (pullback.snd _ p); infer_instance
      · change GeometricallyConnected (pullback.snd _ p); infer_instance
    have hunit : IsIso (toUnit (splitTorus (Sp Ω) PUnit)) := by
      have h : 𝟙 (splitTorus (Sp Ω) PUnit) = 1 := by
        rw [← Diag.diagMap_id, ← Diag.diagMap_zero]
        congr 1
      exact ⟨η, h.symm, toUnit_unique _ _⟩
    exact ⟨{ X := PUnit
             B := A
             isAbelian := hA
             q := 𝟙 A
             q_hom := inferInstance
             q_flat := by rw [Over.id_left]; infer_instance
             q_surjective := by rw [Over.id_left]; infer_instance
             q_quasiCompact := by rw [Over.id_left]; infer_instance
             i := toUnit _ ≫ η
             i_hom := by have := hA.comm; infer_instance
             isKernel := by have := hunit; exact IsPullback.of_vert_isIso ⟨Category.comp_id _⟩ }⟩
  obtain ⟨F, -, -⟩ := GlobalTheory.Poinc.TraitUniq.extIso T.t.semi hsemiB (e₁.symm ≪≫ e₂)
    (show IsMonHom (e₁.inv ≫ e₂.hom) from inferInstance)
  have hp : IsProper T.t.G.hom := by
    have := hB.proper
    have : IsIso F.hom.left := inferInstanceAs (IsIso ((Over.forget _).map F.hom))
    rw [← Over.w F.hom]
    infer_instance
  exact GlobalTheory.ChartNotAb.subsingleton_of_closed_mem_abLocus T.P (fun _ _ _ _ _ => inferInstance)

end GlobalTheory.UPoinc.SuppTrait


open GlobalTheory.UPoinc.SuppTrait in
theorem GlobalTheory.UPoinc.SuppTrait.support_not_mem_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (ι : ℕ) (D : GlobalTheory.EffCartierData Y.Z), (∀ y ∈ D.idealSheaf.support, y ∉ U₀) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ Y U₀ EE out πY hAdm hhom ι D hoff hord y hy hC
  obtain ⟨T, ξ, γ, hcen, hgen, hTy⟩ := exists_uTrait_centre Y X₁.uΩ y
  have hU₀ : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact Y.top_le_preimage_pt hAdm.1.ne (x := w) trivial
  have hthru : ∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y := by
    refine ⟨spMap γ ≫ IsOpenImmersion.lift U₀.ι Y.pt hU₀, by rw [Category.assoc, IsOpenImmersion.lift_fac, hgen], ?_⟩
    rw [Category.assoc, out.u₀_gen _ (IsOpenImmersion.lift_fac _ _ _)]
    obtain ⟨x', hx', hu⟩ := X₁.lies_uΩ
    exact ⟨spMap γ ≫ x', by rw [Category.assoc, hx'], by rw [Category.assoc, hu, hTy]⟩
  obtain ⟨a, ha, hJ⟩ := hord T ξ hthru
  have hpt : Y.pt ≫ πY ≫ X₁.π = X₁.uΩ ≫ C.i := by
    have h : Y.pt ≫ πY = X₁.M.pt := hhom.trans (by
      rw [show spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom = 𝟙 _ from Spec.map_id _, Category.id_comp])
    rw [← Category.assoc, h, X₁.comp, Category.assoc]
  have hsq : jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ C.i := by
    rw [← Category.assoc, hgen, Category.assoc, hpt, hTy]
    simp only [USetup.uΩ, Category.assoc]
  obtain ⟨σ, hσ⟩ := lift_i_of_closedPoint C T.V (ξ ≫ πY ≫ X₁.π) (by
    show X₁.π (πY (ξ (closedPoint T.V))) ∈ _
    rw [hcen]; exact hC)
  haveI := C.isPreimmersion_i
  have hσ' : jK T.V ≫ σ = T.y := by
    rw [← cancel_mono C.i, Category.assoc, hσ, hsq]
  haveI := subsingleton_of_extends T σ hσ'
  have ha0 : a = 0 := by
    rw [InvFun.evalZ, InvFun.eval_of_subsingleton, mul_zero] at ha
    exact_mod_cast ha
  subst ha0
  rw [pow_zero, Ideal.span_singleton_one] at hJ
  have htop : FinalTheorems.stalkId D.idealSheaf (ξ (closedPoint T.V)) = ⊤ := by
    by_contra h
    have hle : (FinalTheorems.stalkId D.idealSheaf (ξ (closedPoint T.V))).map (Scheme.stalkClosedPointTo ξ).hom ≤
        maximalIdeal T.V := Ideal.map_le_iff_le_comap.2 fun b hb =>
          (map_mem_nonunits_iff _ b).2 (IsLocalRing.le_maximalIdeal h hb)
    have hle' : idlAlong D.idealSheaf ξ ≤ maximalIdeal T.V := hle
    rw [hJ] at hle'
    exact (maximalIdeal.isMaximal T.V).ne_top (top_le_iff.1 hle')
  exact (mem_support_iff_stalkId _ y).1 hy (hcen ▸ htop)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitDivisorSupportNotMemModuliRangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTraitDivisor_support_not_mem_moduli_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ (ι : ℕ) (D : GlobalTheory.EffCartierData Y.Z), (∀ y ∈ D.idealSheaf.support, y ∉ U₀) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i := by
  first | exact @GlobalTheory.UPoinc.SuppTrait.support_not_mem_range | exact GlobalTheory.UPoinc.SuppTrait.support_not_mem_range | (intros; apply GlobalTheory.UPoinc.SuppTrait.support_not_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierGluingLocalTuples
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonCharacterGroupOfGoodReductionTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonCharacterGroupOfGoodReductionTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.GoodRedU

theorem subsingleton_lattice_of_range_subset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), Set.range ξ ⊆ (U₀ : Set Y.Z) → (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → Subsingleton T.P.D.toPre.X := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out _ T ξ hξ ⟨ξ₀, hξ₀, hlies⟩
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1

  have hr : Set.range ξ ⊆ Set.range U₀.ι := by rw [Scheme.Opens.range_ι]; exact hξ
  let ξ' : Sp T.V ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι ξ hr
  have hξ' : ξ' ≫ U₀.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  have hK : jK T.V ≫ ξ' = ξ₀ := by
    rw [← cancel_mono U₀.ι, Category.assoc, hξ', hξ₀]
  let q : Sp T.V ⟶ Sp X₁.S.R := ξ' ≫ out.u₀
  have hB := GlobalTheory.isAbelianScheme_pullback_obj q X₁.ρ.P.A X₁.ρ.P.isAb

  obtain ⟨g, hg⟩ := Spec.map_surjective (ξ₀ ≫ out.u₀)
  have hf : X₁.Lies (spMap g.hom) T.y := by
    show X₁.Lies (Spec.map (CommRingCat.ofHom g.hom)) T.y
    rw [CommRingCat.ofHom_hom, hg]; exact hlies
  obtain ⟨G, _, α, β, hα, hβ, -⟩ := hf.uOver
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  obtain ⟨e₁, he₁, -⟩ := grpPullback_iso m₂.cart hβ
  obtain ⟨e₂, he₂, -⟩ := grpPullback_iso (isGrpPullback_pullback T.t.G (jK T.V)) m₁.cart
  haveI := he₁
  haveI := he₂
  have hq : spMap g.hom = jK T.V ≫ q := by
    show Spec.map (CommRingCat.ofHom g.hom) = _
    rw [CommRingCat.ofHom_hom, hg, ← hK, Category.assoc]
  have h₁ := ((isGrpPullback_of_iso e₂).comp ((isGrpPullback_of_iso e₁).comp hα)).congr
    (by rw [Category.id_comp, Category.id_comp, hq]) rfl
  have h₂ := (isGrpPullback_pullback ((Over.pullback q).obj X₁.ρ.P.A) (jK T.V)).comp
    (isGrpPullback_pullback X₁.ρ.P.A q)
  obtain ⟨e, he, -⟩ := grpPullback_iso h₁ h₂

  obtain ⟨Eiso, -, -⟩ := TraitUniq.extIso T.t.semi (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB) e he
  have hp : IsProper T.t.G.hom := by
    have := hB.proper
    have : IsIso Eiso.hom.left := inferInstanceAs (IsIso ((Over.forget _).map Eiso.hom))
    rw [← Over.w Eiso.hom]
    infer_instance
  have hc : (closedPoint T.V : Sp T.V) ∈ abLocus T.t.G := fun _ _ _ _ _ => inferInstance
  exact ChartNotAb.subsingleton_of_closed_mem_abLocus T.P hc

end GlobalTheory.UPoinc.GoodRedU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonCharacterGroupOfGoodReductionTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_characterGroup_of_goodReduction_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), Set.range ξ ⊆ (U₀ : Set Y.Z) → (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → Subsingleton T.P.D.toPre.X := by
  first | exact @GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset | exact GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset | (intros; apply GlobalTheory.UPoinc.GoodRedU.subsingleton_lattice_of_range_subset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierGluingLocalTuples
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def toA (T : UTrait Xo c) {X : Scheme.{0}} (ξ : Sp T.V ⟶ X) : ATrait X where
  V := T.V
  dvr := T.cdvr.1
  char := T.cdvr.2.2
  complete := T.cdvr.2.1
  ϖ := T.ϖ
  irr := T.irr
  ξ := ξ

variable {C : UCompact Xo c}

theorem exists_utrait_of_stalk (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (x : Y.Z) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (hcomp : IsAdicComplete (maximalIdeal V) V) (θ : Y.Z.presheaf.stalk x →+* V)
    (hθ : Function.Injective θ) :
    ∃ (T : UTrait Xo c) (f : V →+* T.V) (γ : X₁.Ω₁ →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧
      (∀ a, γ (Y.stalkHom x a) = algebraMap T.V (FractionRing T.V) (f (θ a))) ∧
      jK T.V ≫ spMap (f.comp θ) ≫ Y.Z.fromSpecStalk x = spMap γ ≫ Y.pt ∧ T.y = spMap γ ≫ X₁.uΩ := by
  haveI := ArithBase.char (o := X₁.o₁) (Ω := X₁.Ω₁)
  haveI : CharZero (Y.Z.presheaf.stalk x) := (Y.stalkHom x).charZero
  haveI : CharZero V := charZero_of_injective_ringHom hθ
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  let θ' : Y.O x →+* FractionRing V :=
    ((algebraMap V (FractionRing V)).comp θ).comp (Y.stalkEquiv x).symm.toRingHom
  have hθ' : Function.Injective θ' :=
    (IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (Y.stalkEquiv x).symm.injective)
  let γ₀ : X₁.Ω₁ →+* FractionRing V := IsFractionRing.lift (A := Y.O x) (K := X₁.Ω₁) hθ'
  have hγ₀ : ∀ a, γ₀ (Y.stalkHom x a) = algebraMap V (FractionRing V) (θ a) := by
    intro a
    have h := IsFractionRing.lift_algebraMap (A := Y.O x) (K := X₁.Ω₁) hθ' (Y.stalkEquiv x a)
    rw [← RatModel.coe_stalkEquiv]
    refine h.trans ?_
    simp [θ']
  obtain ⟨T, f, fK, hfi, hfl, -, hc, hy⟩ :=
    GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V hB inferInstance (spMap γ₀ ≫ X₁.uΩ)
  refine ⟨T, f, fK.comp γ₀, hfi, hfl, ?_, ?_, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hγ₀, hc]
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (Y.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← GlobalTheory.Poinc.GenTrait.spMap_stalkHom_fromSpecStalk Y x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e,
      ← Formalism.L2.Pj.spMap_comp', Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']

end GlobalTheory.UPoinc.UGlue


open GlobalTheory.UPoinc.UGlue GlobalTheory.Poinc.OrdGlue in
theorem GlobalTheory.UPoinc.UGlue.glue (hgood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), Set.range ξ ⊆ (U₀ : Set Y.Z) → (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → Subsingleton T.P.D.toPre.X) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (ι : ℕ) (K : Type) [Fintype K] (Jk : K → Type) [∀ k, Fintype (Jk k)] (t : ∀ k, Jk k → X₁.Ω₁), (∀ k j, t k j ≠ 0) → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → (∀ k, Nonempty (Jk k) → Y.HasDiv (t k)) → (∀ x : Y.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ (∀ j, UOrdGe Y T ξ (t k j) a) ∧ ∃ j, UOrdEq Y T ξ (t k j) a) → ∃ D : GlobalTheory.EffCartierData Y.Z, (∀ y ∈ D.idealSheaf.support, y ∉ U₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  intro E _ _ _ H Dw _ φ _ l Xo c C X₁ ι K _ Jk _ t _ Y U₀ EE out hAdm hdiv hloc
  haveI := isLocallyNoetherian Y
  haveI := ArithBase.char (o := X₁.o₁) (Ω := X₁.Ω₁)
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z := hAdm.1.normal
  have hU₀ : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact Y.top_le_preimage_pt hAdm.1.ne (x := w) trivial

  have hthru : ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z) (γ : X₁.Ω₁ →+* FractionRing T.V), jK T.V ≫ ξ = spMap γ ≫ Y.pt →
      T.y = spMap γ ≫ X₁.uΩ → ∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧
        X₁.Lies (ξ₀ ≫ out.u₀) T.y := by
    intro T ξ γ h₁ h₂
    refine ⟨spMap γ ≫ IsOpenImmersion.lift U₀.ι Y.pt hU₀, ?_, spMap γ ≫ spMap (ratHull X₁.S.R).val.toRingHom, ?_, ?_⟩
    · rw [Category.assoc, IsOpenImmersion.lift_fac, h₁]
    · rw [Category.assoc, spMap_val_toRat, Category.assoc, out.u₀_gen _ (IsOpenImmersion.lift_fac _ _ _)]
    · rw [h₂, Category.assoc]

  have hcentre : ∀ x : Y.Z, ∃ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z) (γ : X₁.Ω₁ →+* FractionRing T.V),
      ξ (closedPoint T.V) = x ∧ jK T.V ≫ ξ = spMap γ ≫ Y.pt ∧ T.y = spMap γ ≫ X₁.uΩ := by
    intro x
    haveI : CharZero (Y.Z.presheaf.stalk x) := RingHom.charZero (Y.stalkHom x)
    obtain ⟨V, _, _, _, θ, ⟨hd, hc, -⟩, hi, hl⟩ := GlobalTheory.DvrDom.exists_cdvr_dominating (Y.Z.presheaf.stalk x)
    obtain ⟨T, f, γ, -, hfl, -, h₂, h₃⟩ := exists_utrait_of_stalk X₁ Y x V hc θ hi
    haveI := hfl
    exact ⟨T, _, γ, GlobalTheory.Poinc.OrdGlue.centre (f.comp θ), h₂, h₃⟩

  have hreg : ∀ (x : Y.Z) (s : X₁.Ω₁), (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z) (γ : X₁.Ω₁ →+* FractionRing T.V),
      jK T.V ≫ ξ = spMap γ ≫ Y.pt → T.y = spMap γ ≫ X₁.uΩ → ξ (closedPoint T.V) = x →
        ∃ w : T.V, γ s = algebraMap T.V (FractionRing T.V) w) → s ∈ Y.O x := by
    intro x s h
    haveI : CharZero (Y.Z.presheaf.stalk x) := RingHom.charZero (Y.stalkHom x)
    haveI := (hN x).2
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Y.O x) s
    obtain ⟨a, rfl⟩ := (Y.stalkEquiv x).surjective a
    obtain ⟨b, rfl⟩ := (Y.stalkEquiv x).surjective b
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact nonZeroDivisors.ne_zero hb (map_zero _)
    have hb1 : Y.stalkHom x b ≠ 0 := (map_ne_zero_iff _ (Y.stalkHom_injective x)).2 hb0
    change Y.stalkHom x a / Y.stalkHom x b ∈ Y.O x
    obtain ⟨c', rfl⟩ := GlobalTheory.Poinc.dvd_of_forall_complete_dvr (Y.Z.presheaf.stalk x) a b hb0 fun V _ _ _ hV θ hθ hl => by
      obtain ⟨T, f, γ, hf, hfl, h₄, h₂, h₃⟩ := exists_utrait_of_stalk X₁ Y x V hV θ hθ
      haveI := hfl
      obtain ⟨w, hw⟩ := h T _ γ h₂ h₃ (GlobalTheory.Poinc.OrdGlue.centre (f.comp θ))
      refine dvd_of_map_dvd f hf ⟨w, IsFractionRing.injective T.V (FractionRing T.V) ?_⟩
      rw [map_mul, ← h₄, ← h₄, ← hw, ← map_mul]
      congr 1
      change _ = _ * (Y.stalkHom x a / Y.stalkHom x b)
      rw [mul_div_cancel₀ _ hb1]
    rw [map_mul, mul_div_cancel_left₀ _ hb1]
    exact (Y.stalkEquiv x c').2
  have hgen : ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme,
      ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → (toA T ξ).GenIn U₀ := by
    rintro T ξ ⟨ξ₀, h₀, -⟩ _ ⟨w, rfl⟩
    rw [← Scheme.Opens.range_ι]
    exact ⟨ξ₀ w, by change U₀.ι (ξ₀ w) = (jK T.V ≫ ξ) w; rw [← h₀]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩
  have exists_spread {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
      (f : ∀ x : X, X.presheaf.stalk x) (hU : ∀ η ∈ U, ringKrullDim (X.presheaf.stalk η) = 1 → IsUnit (f η))
      (hne : ∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → genericPoint X ∈ U) (x : X) (h0 : f x ≠ 0)
      (hc : ∀ (η : X) (h : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
        Associated ((X.presheaf.stalkSpecializes h).hom (f x)) (f η)) :
      ∃ (W : X.Opens) (hx : x ∈ W) (s : Γ(X, W)), (X.presheaf.germ W x hx).hom s = f x ∧
        ∀ (η : X) (hη : η ∈ W), ringKrullDim (X.presheaf.stalk η) = 1 →
          Associated ((X.presheaf.germ W η hη).hom s) (f η) := by
    obtain ⟨W₀, hx₀, s₀, hs₀⟩ := X.presheaf.exists_germ_eq (f x)
    obtain ⟨⟨W, hW⟩, hx, hle⟩ := EffCartierData.exists_affine_le hx₀
    let s : Γ(X, W) := resG X hle s₀
    have hs : (X.presheaf.germ W x hx).hom s = f x := (Cartier.germ_resG hle _ hx _).trans hs₀
    let B : Set X := {η | ∃ hη : η ∈ W, ringKrullDim (X.presheaf.stalk η) = 1 ∧
      ¬ Associated ((X.presheaf.germ W η hη).hom s) (f η)}
    have hgen : ∀ {V : X.Opens} {y : X}, y ∈ V → genericPoint X ∈ V := fun {V y} hy =>
      ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨y, trivial, hy⟩
    have hB : B.Finite := by
      rcases B.eq_empty_or_nonempty with h | ⟨η₀, -, h₀, -⟩
      · rw [h]; exact Set.finite_empty
      have hs0 : s ≠ 0 := fun e => h0 (by rw [← hs, e, map_zero])
      have hb : genericPoint X ∈ X.basicOpen s := by
        rw [X.mem_basicOpen s _ (hgen hx)]
        have : (X.presheaf.germ W _ (hgen hx)).hom s ≠ 0 := fun e =>
          hs0 (germ_injective_of_isIntegral X _ (hgen hx) (e.trans (map_zero _).symm))
        exact (IsUnit.mk0 (G₀ := X.functionField) _ this)
      refine (GlobalTheory.Poinc.TraitGlue.finite_dim_one hW (U ⊓ X.basicOpen s) (hgen hx) ⟨hne η₀ h₀, hb⟩).subset ?_
      rintro η ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun h4 => h3 ?_⟩
      exact (associated_one_iff_isUnit.2 ((X.mem_basicOpen s η h1).1 h4.2)).trans
        (associated_one_iff_isUnit.2 (hU η h4.1 h2)).symm
    have hcl : IsClosed (⋃ η ∈ B, closure ({η} : Set X)) := hB.isClosed_biUnion fun _ _ => isClosed_closure
    let W' : X.Opens := W ⊓ ⟨_, hcl.isOpen_compl⟩
    have hx' : x ∈ W' := by
      refine ⟨hx, fun hm => ?_⟩
      obtain ⟨η, ⟨h1, h2, h3⟩, h4⟩ := Set.mem_iUnion₂.1 hm
      have h5 : η ⤳ x := specializes_iff_mem_closure.2 h4
      refine h3 ?_
      rw [← GlobalTheory.Poinc.TraitGlue.specializes_germ h5 hx h1, hs]
      exact hc η h5 h2
    refine ⟨W', hx', resG X inf_le_left s, (Cartier.germ_resG _ _ hx' _).trans hs, fun η hη h1 => ?_⟩
    rw [Cartier.germ_resG]
    by_contra hn
    exact hη.2 (Set.mem_iUnion₂.2 ⟨η, ⟨hη.1, h1, hn⟩, subset_closure rfl⟩)

  have exists_of_germs {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
      (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (U : X.Opens)
      (f : ∀ x : X, X.presheaf.stalk x) (hU : ∀ η ∈ U, ringKrullDim (X.presheaf.stalk η) = 1 → IsUnit (f η))
      (hne : ∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → genericPoint X ∈ U) (h0 : ∀ x, f x ≠ 0)
      (hc : ∀ (x η : X) (h : η ⤳ x), ringKrullDim (X.presheaf.stalk η) = 1 →
        Associated ((X.presheaf.stalkSpecializes h).hom (f x)) (f η)) :
      ∃ D : EffCartierData X, (∀ x ∈ D.idealSheaf.support, x ∉ U) ∧
        ∀ x, FinalTheorems.stalkId D.idealSheaf x = Ideal.span {f x} := by
    choose W hx s hs hW using fun x => exists_spread U f hU hne x (h0 x) (hc x)
    have hs0 : ∀ x, s x ≠ 0 := fun x e => h0 x (by rw [← hs x, e, map_zero])
    have hreg : ∀ x, Cartier.IsRegularFn (s x) := fun x => Cartier.isRegularFn_of_ne_zero (hs0 x)
    have hdvd : ∀ (i j y : X) (hi : y ∈ W i) (hj : y ∈ W j),
        (X.presheaf.germ _ y hi).hom (s i) ∣ (X.presheaf.germ _ y hj).hom (s j) := by
      intro i j y hi hj
      refine GlobalTheory.Poinc.TraitGlue.dvd_of_generisations hX y (fun e =>
        hs0 i (germ_injective_of_isIntegral X _ hi (e.trans (map_zero _).symm))) fun η hη h1 => ?_
      have hi' : η ∈ W i := hη.mem_open (W i).isOpen hi
      have hj' : η ∈ W j := hη.mem_open (W j).isOpen hj
      rw [GlobalTheory.Poinc.TraitGlue.specializes_germ hη hi hi', GlobalTheory.Poinc.TraitGlue.specializes_germ hη hj hj']
      exact ((hW i η hi' h1).trans (hW j η hj' h1).symm).dvd
    let D : EffCartierData X :=
      { ι := X
        U := W
        f := s
        cover := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩
        regular := hreg
        assoc := fun i j => ((hreg i).resG _).associated_of_germ ((hreg j).resG _) fun y hy => by
          rw [Cartier.germ_resG, Cartier.germ_resG]
          exact le_antisymm (Ideal.span_singleton_le_span_singleton.2 (hdvd j i y hy.2 hy.1))
            (Ideal.span_singleton_le_span_singleton.2 (hdvd i j y hy.1 hy.2)) }
    refine ⟨D, fun x hxD hxU => ?_, fun x => (D.stalkId_idealSheaf x x (hx x)).trans (congrArg (fun t => Ideal.span {t}) (hs x))⟩
    refine (D.mem_support_iff x (hx x)).1 hxD ((X.mem_basicOpen (s x) x (hx x)).2 ?_)
    change IsUnit ((X.presheaf.germ _ x (hx x)).hom (s x))
    rw [hs x]
    refine isUnit_of_dvd_one (GlobalTheory.Poinc.TraitGlue.dvd_of_generisations hX x (h0 x) fun η hη h1 => ?_)
    exact ((hc x η hη h1).symm.isUnit (hU η (hη.mem_open U.isOpen hxU) h1)).dvd

  have exists_effCartier_of_orders : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ (U : X.Opens) (R : ATrait X → ℕ → Prop), (∀ (T : ATrait X) (a : ℕ), Set.range T.ξ ⊆ U → R T a → a = 0) → (∀ η : X, ringKrullDim (X.presheaf.stalk η) = 1 → ∃ (T : ATrait X) (a e : ℕ), T.CentredAt η e ∧ T.GenIn U ∧ R T a) → (∀ x : X, ∃ f : X.presheaf.stalk x, ∀ (T : ATrait X) (h : T.ξ (closedPoint T.V) ⤳ x) (a : ℕ), T.GenIn U → R T a → T.HasOrd h f a) → ∃ D : EffCartierData X, (∀ x ∈ D.idealSheaf.support, x ∉ U) ∧ ∀ (T : ATrait X) (a : ℕ), T.GenIn U → R T a → idlAlong D.idealSheaf T.ξ = Ideal.span {T.ϖ ^ a} := by
    intro X _ _ hX U R hR hT hf
    have hf' : ∀ x : X, ∃ f : X.presheaf.stalk x, f ≠ 0 ∧ ∀ (T : ATrait X) (h : T.ξ (closedPoint T.V) ⤳ x) (a : ℕ),
        T.GenIn U → R T a → T.HasOrd h f a := by
      intro x
      obtain ⟨f, hf⟩ := hf x
      by_cases h0 : f = 0
      · refine ⟨1, one_ne_zero, fun T h a h1 h2 => ?_⟩
        have := hf T h a h1 h2
        rw [h0, ATrait.HasOrd, map_zero, map_zero, Ideal.span_singleton_eq_span_singleton] at this
        exact absurd (this.eq_zero_iff.1 rfl) (pow_ne_zero _ T.irr.ne_zero)
      · exact ⟨f, h0, hf⟩
    choose f h0 hf using hf'
    have hself : ∀ (T : ATrait X) (a : ℕ), T.GenIn U → R T a →
        Ideal.span {(Scheme.stalkClosedPointTo T.ξ).hom (f _)} = Ideal.span {T.ϖ ^ a} := by
      intro T a h1 h2
      have := hf _ T specializes_rfl a h1 h2
      rwa [ATrait.HasOrd, TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, RingHom.id_apply] at this
    obtain ⟨D, hD, hD'⟩ := exists_of_germs hX U f (fun η hη h1 => by
        obtain ⟨T, a, e, ⟨rfl, -⟩, h2, h3⟩ := hT η h1
        have ha : a = 0 := hR T a (by
          rintro _ ⟨p, rfl⟩
          exact ((IsLocalRing.specializes_closedPoint p).map T.ξ.continuous).mem_open U.isOpen hη) h3
        have := hself T a h2 h3
        rw [ha, pow_zero, Ideal.span_singleton_one, Ideal.span_singleton_eq_top] at this
        exact isUnit_of_map_unit _ _ this)
      (fun η h1 => by
        obtain ⟨T, a, e, -, h2, -⟩ := hT η h1
        obtain ⟨p⟩ : Nonempty (Sp (FractionRing T.V)) := inferInstanceAs (Nonempty (PrimeSpectrum _))
        exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨_, trivial, h2 ⟨p, rfl⟩⟩) h0
      (fun x η h h1 => by
        obtain ⟨T, a, e, ⟨rfl, -⟩, h2, h3⟩ := hT η h1
        have := GlobalTheory.Poinc.TraitGlue.valuationRing_stalk hX _ h1
        have e1 := Ideal.span_singleton_eq_span_singleton.1 (hf x T h a h2 h3)
        have e2 := Ideal.span_singleton_eq_span_singleton.1 (hself T a h2 h3)
        exact GlobalTheory.Poinc.TraitGlue.associated_of_map (Scheme.stalkClosedPointTo T.ξ).hom (e1.trans e2.symm)
          (e1.ne_zero_iff.2 (pow_ne_zero _ T.irr.ne_zero)))
    refine ⟨D, hD, fun T a h1 h2 => ?_⟩
    rw [idlAlong, hD', Ideal.map_span, Set.image_singleton]
    exact hself T a h1 h2
  refine Exists.elim (exists_effCartier_of_orders Y.Z hN U₀
    (fun A a => ∃ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), A = toA T ξ ∧ (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme,
      ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) ∧ (a : ℝ) = ι * φ.evalZ T.be) ?_ ?_ ?_) fun D ⟨hD, hord⟩ => ?_
  rotate_right
  · refine ⟨D, hD, fun T ξ hT => ?_⟩
    obtain ⟨k, hk⟩ := hloc (ξ (closedPoint T.V))
    obtain ⟨a, ha, -⟩ := hk T ξ hT specializes_rfl
    exact ⟨a, ha, hord (toA T ξ) a (hgen T ξ hT) ⟨T, ξ, rfl, hT, ha⟩⟩
  · rintro _ a hr ⟨T, ξ, rfl, hT, ha⟩
    haveI := hgood E H Dw l Xo c C X₁ Y U₀ EE out hAdm T ξ hr hT
    rw [InvFun.evalZ, InvFun.eval_of_subsingleton, mul_zero] at ha
    exact_mod_cast ha
  · intro η hη
    obtain ⟨T, ξ, γ, rfl, h₁, h₂⟩ := hcentre η
    obtain ⟨k, hk⟩ := hloc (ξ (closedPoint T.V))
    obtain ⟨a, ha, -⟩ := hk T ξ (hthru T ξ γ h₁ h₂) specializes_rfl
    have hinj : Function.Injective (Scheme.stalkClosedPointTo ξ).hom := by
      refine (injective_iff_map_eq_zero _).2 fun b hb => ?_
      have e := val_jK ξ specializes_rfl b
      rw [TopCat.Presheaf.stalkSpecializes_refl, h₁, val_generic] at e
      simp only [CommRingCat.hom_id, RingHom.id_apply] at e
      rw [hb, map_zero, map_eq_zero, map_eq_zero_iff _ (Y.stalkHom_injective _)] at e
      exact e
    have hne : (maximalIdeal (Y.Z.presheaf.stalk (ξ (closedPoint T.V)))).map (Scheme.stalkClosedPointTo ξ).hom ≠ ⊥ := by
      rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
      intro hb
      rw [ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.2 hb)] at hη
      exact zero_ne_one hη
    haveI := T.cdvr.1
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne T.irr
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | h
      · exfalso
        rw [pow_zero, Ideal.span_singleton_one] at he
        have hle : (maximalIdeal (Y.Z.presheaf.stalk (ξ (closedPoint T.V)))).map (Scheme.stalkClosedPointTo ξ).hom ≤
            maximalIdeal T.V := Ideal.map_le_iff_le_comap.2 fun b hb => (map_mem_nonunits_iff _ b).2 hb
        exact (maximalIdeal.isMaximal T.V).ne_top (top_le_iff.1 (he ▸ hle))
      · exact h
    refine ⟨toA T ξ, a, e, ⟨rfl, hinj, he1, specializes_rfl, ?_⟩, hgen T ξ (hthru T ξ γ h₁ h₂), T, ξ, rfl,
      hthru T ξ γ h₁ h₂, ha⟩
    change Ideal.map ((Scheme.stalkClosedPointTo ξ).hom.comp
      (Y.Z.presheaf.stalkSpecializes (specializes_refl (ξ (closedPoint T.V)))).hom) _ = _
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact he
  · intro x
    obtain ⟨k, hk⟩ := hloc x
    obtain ⟨T₀, ξ₀, γ₀, h₀, h₁, h₂⟩ := hcentre x
    obtain ⟨_, -, -, j₁, -⟩ := hk T₀ ξ₀ (hthru T₀ ξ₀ γ₀ h₁ h₂) (specializes_of_eq h₀)
    obtain ⟨j₀, hj₀⟩ := hdiv k ⟨j₁⟩ x
    have hr : t k j₀ ∈ Y.O x := hreg x _ fun T ξ γ h₁ h₂ h₀ => by
      obtain ⟨a, -, hge, -⟩ := hk T ξ (hthru T ξ γ h₁ h₂) (specializes_of_eq h₀)
      obtain ⟨-, w, hw⟩ := hge j₀
      rw [h₁, val_generic] at hw
      exact ⟨_, hw⟩
    obtain ⟨f, hf⟩ := (Y.stalkEquiv x).surjective ⟨_, hr⟩
    have hf' : Y.stalkHom x f = t k j₀ := congrArg Subtype.val hf
    refine ⟨f, ?_⟩
    rintro _ h a - ⟨T, ξ, rfl, hT, ha⟩
    change ξ (closedPoint T.V) ⤳ x at h
    obtain ⟨a', ha', hge, j, w', hw'⟩ := hk T ξ hT h
    obtain rfl : a = a' := by exact_mod_cast ha.trans ha'.symm
    obtain ⟨-, w, hw⟩ := hge j₀
    obtain ⟨q, hq⟩ := (Y.stalkEquiv x).surjective ⟨_, hj₀.2 j⟩
    have hq' : Y.stalkHom x q = t k j / t k j₀ := congrArg Subtype.val hq
    have e₁ := val_jK ξ h f
    have e₂ := val_jK ξ h (f * q)
    rw [hf', hw] at e₁
    rw [map_mul, hf', hq', mul_div_cancel₀ _ hj₀.1, hw', map_mul (Y.Z.presheaf.stalkSpecializes h).hom,
      map_mul (Scheme.stalkClosedPointTo ξ).hom] at e₂
    have e₃ := IsFractionRing.injective T.V (FractionRing T.V) e₁
    have e₄ := IsFractionRing.injective T.V (FractionRing T.V) e₂
    rw [← e₃, mul_assoc] at e₄
    have hu : IsUnit w := isUnit_of_mul_isUnit_left (mul_left_cancel₀ (pow_ne_zero a T.irr.ne_zero) e₄ ▸ w'.isUnit)
    exact (congrArg (fun r => Ideal.span {r}) e₃.symm).trans (Ideal.span_singleton_mul_right_unit hu _)

theorem GlobalTheory.UPoinc.UGlue.exists_effCartier_of_locTuples : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (ι : ℕ) (K : Type) [Fintype K] (Jk : K → Type) [∀ k, Fintype (Jk k)] (t : ∀ k, Jk k → X₁.Ω₁), (∀ k j, t k j ≠ 0) → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → (∀ k, Nonempty (Jk k) → Y.HasDiv (t k)) → (∀ x : Y.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ (∀ j, UOrdGe Y T ξ (t k j) a) ∧ ∃ j, UOrdEq Y T ξ (t k j) a) → ∃ D : GlobalTheory.EffCartierData Y.Z, (∀ y ∈ D.idealSheaf.support, y ∉ U₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} :=
  GlobalTheory.UPoinc.UGlue.glue GlobalTheory.T.subsingleton_characterGroup_of_goodReduction_trait
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierGluingLocalTuplesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_effectiveCartier_gluing_localTuples : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (ι : ℕ) (K : Type) [Fintype K] (Jk : K → Type) [∀ k, Fintype (Jk k)] (t : ∀ k, Jk k → X₁.Ω₁), (∀ k j, t k j ≠ 0) → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE), X₁.S.admitted Y U₀ → (∀ k, Nonempty (Jk k) → Y.HasDiv (t k)) → (∀ x : Y.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ (∀ j, UOrdGe Y T ξ (t k j) a) ∧ ∃ j, UOrdEq Y T ξ (t k j) a) → ∃ D : GlobalTheory.EffCartierData Y.Z, (∀ y ∈ D.idealSheaf.support, y ∉ U₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.UPoinc.UGlue.exists_effCartier_of_locTuples | exact GlobalTheory.UPoinc.UGlue.exists_effCartier_of_locTuples | (intros; apply GlobalTheory.UPoinc.UGlue.exists_effCartier_of_locTuples <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryExistsNormalModelEffCartierAlongTraits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.exists_zhModel_effCartier_orders : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsProjOver X₁.M.s → ∃ (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι ∧ X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z ∧ (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i) ∧ UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ hproj
  obtain ⟨ι, K, hK, Jk, hJ, t, hι, ht, hloc⟩ := GlobalTheory.T.exists_finite_theta_tuples_least_orders_unitary E H Dw hpq φ hφ l Xo c C X₁
  obtain ⟨Y, πY, U₀, EE, out, hhom, hprop, hAdm, hEE, hdiv⟩ :=
    GlobalTheory.Poinc.exists_admissible_projective_theta_model X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big X₁.M hproj K Jk t ht
  obtain ⟨D, hDU, hDord⟩ := GlobalTheory.T.exists_effectiveCartier_gluing_localTuples E H Dw hpq φ hφ l Xo c C X₁ ι K Jk t ht Y U₀ EE out hAdm hdiv
    (hloc Y U₀ EE out hAdm hEE)
  have hsupp := GlobalTheory.T.unitaryTraitDivisor_support_not_mem_moduli_range E H Dw hpq φ hφ l Xo c C X₁ Y U₀ EE out πY hAdm hhom ι D hDU hDord
  exact ⟨ι, Y, πY, D, hι, hhom, hprop, hAdm.1.normal, hsupp,
    GlobalTheory.T.divisor_orders_all_traits_over_moduli E H Dw hpq φ hφ l Xo c C X₁ Y U₀ EE out πY hAdm hEE hhom ι D hsupp hDord⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryExistsNormalModelEffCartierAlongTraitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_exists_normalModel_effCartier_along_traits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsProjOver X₁.M.s → ∃ (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι ∧ X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z ∧ (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i) ∧ UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι := by
  first | exact @GlobalTheory.UPoinc.exists_zhModel_effCartier_orders | exact GlobalTheory.UPoinc.exists_zhModel_effCartier_orders | (intros; apply GlobalTheory.UPoinc.exists_zhModel_effCartier_orders <;> assumption)
end
