module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsUnitaryClassicalTrait

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitPeriodsBoundedBelow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitPeriodsBoundedBelow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.ShortBound

theorem exists_not_dvd_le {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ y, y ≠ 0 → 0 < β y y) (m : ℕ) (hm : 2 ≤ m) :
    ∀ (k : ℕ) (x : X), (β x x).toNat = k → x ≠ 0 →
      ∃ x', x' ≠ 0 ∧ (¬ ∃ v, x' = m • v) ∧ β x' x' ≤ β x x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hk hx
    by_cases hd : ∃ v, x = m • v
    · obtain ⟨v, rfl⟩ := hd
      have hv : v ≠ 0 := by rintro rfl; simp at hx
      have hvv := hβ v hv
      have e : β (m • v) (m • v) = (m : ℤ) * ((m : ℤ) * β v v) := by
        simp [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
      have h2 : 2 * β v v ≤ (m : ℤ) * β v v := mul_le_mul_of_nonneg_right hm' hvv.le
      have h3 : 2 * ((m : ℤ) * β v v) ≤ (m : ℤ) * ((m : ℤ) * β v v) :=
        mul_le_mul_of_nonneg_right hm' (by linarith)
      have hlt : β v v < β (m • v) (m • v) := by rw [e]; linarith
      obtain ⟨x', h1, h2, h3⟩ := ih (β v v).toNat (by omega) v rfl hv
      exact ⟨x', h1, h2, h3.trans hlt.le⟩
    · exact ⟨x, hx, hd, le_rfl⟩

theorem exists_shortest {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (N : ℕ) (a : X) :
    ∃ v : X, ∀ v0, q (a + N • v) ≤ q (a + N • v + N • v0) := by
  have hfin : {x | ¬ q a < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop (q a))
  obtain ⟨b, ⟨hb, v, rfl⟩, hmin⟩ := Set.exists_min_image ({x | ¬ q a < q x} ∩ Set.range fun v => a + N • v) q
    (hfin.inter_of_left _) ⟨a, lt_irrefl _, 0, by simp⟩
  refine ⟨v, fun v0 => ?_⟩
  by_cases h : q a < q (a + N • v + N • v0)
  · exact (not_lt.1 hb).trans h.le
  · exact hmin _ ⟨h, v + v0, by simp [add_assoc]⟩

theorem pos_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) (ha : a ≠ 0) : 0 < q a := by
  by_contra h
  have h : q a ≤ 0 := not_lt.1 h
  have hfin : {x | ¬ (0 : ℝ) < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • a) (smul_left_injective ℤ ha) (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_lt, QuadraticMap.map_smul, zsmul_eq_mul]
  push_cast
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem sc_pos {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) :
    0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (not_lt.1 hge)
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem one_le_of_ne_zero (T : UTrait Xo c) {x : T.P.D.toPre.X} (hx : x ≠ 0) : 1 ≤ Dw.p + Dw.q := by
  haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) _
  haveI : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Nontrivial T.P.D.toPre.X := ⟨x, 0, hx⟩
  have h1 : 0 < Module.finrank (𝓞 E) T.P.D.toPre.X := Module.finrank_pos
  have h2 := UTrait.finrank_le_min E H Dw l Xo c T
  omega

theorem exists_mem_maximalIdeal {C : UCompact Xo c} (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z)
    (hz : IsClosed ({z₁} : Set X₁.M.Z)) (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X) (hx : x ≠ 0) :
    ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁),
      Real.exp (-(1 / (2 * X₁.S.N) * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  obtain ⟨x', hx', hnd, hle⟩ :=
    exists_not_dvd_le t.T.be (be_pos t.T) X₁.S.N X₁.S.N_ge _ x rfl hx
  obtain ⟨wi⟩ := nonempty_uWit X₁
  obtain ⟨yy, hyy⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw (one_le_of_ne_zero t.T hx) l Xo c C X₁ wi p z₁ t
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, hR, G, _, α, β, -, -, -, y₀, hat, u, lb, j, hq, -⟩ :=
    hyy.uIsLab
  let S' := X₁.S.rechart c₀ hc R' fg frac hth hev
  have hdiv' : X₁.M.HasDiv S'.th := fun z => (X₁.hasDiv z).imp fun k hk => (RatModel.div_mul_iff hc).2 hk
  have htests : S'.HasTests :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hU hL hL2 hUT X₁.o₁ X₁.Ω₁ S' ρ').1
  have hy : ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ S'.R a)‖ ≤ 1 := fun a => by
    rw [hat]
    exact RatModel.norm_val_le_one t.cen ((X₁.M.O z₁).algebraMap_mem a)
  obtain ⟨τ, e, hτ, -⟩ := exists_test_match X₁.o₁ X₁.Ω₁ S' ρ' p y₀ u lb
    (GlobalTheory.T.thetaConstant_bounded_by_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u lb hy) (GlobalTheory.T.unitThetaConstants_generate_integralTorsion hL hL2 hUT _ _ S' ρ' p y₀ u lb hy)
    (GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u lb hy) (GlobalTheory.T.exists_norm_torsionSum_shortestVector_eq hL hL2 hUT _ _ S' ρ' p y₀ u lb hy)
    (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hUT _ _ S' ρ' p y₀ u lb hy)
  let α₀ : τ.X := e.symm (j.symm x')
  obtain ⟨v, hv⟩ := exists_shortest τ.q τ.pos X₁.S.N α₀
  have hne : α₀ + X₁.S.N • v ≠ 0 := fun h0 => hnd ⟨-(j (e v)), by
    have h1 := congrArg (fun s => j (e s)) h0
    simp only [α₀, map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, map_zero] at h1
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left h1⟩
  have hqle : τ.q (α₀ + X₁.S.N • v) ≤ t.sc * t.T.be x' x' / 2 := by
    have h1 := hv (-v)
    rw [smul_neg, add_neg_cancel_right] at h1
    refine h1.trans_eq ?_
    rw [hτ, hq]
    simp only [α₀, AddEquiv.apply_symm_apply]
  obtain ⟨h, hm, hh⟩ := GlobalTheory.exists_mem_maximalIdeal_exp_le_norm_val X₁.o₁ X₁.Ω₁ S' X₁.M X₁.normal hdiv' htests z₁ hz p
    t.y y₀ t.cen (fun a ha => hR ha) hat τ _ hv (pos_of_tendsto τ.q τ.pos _ hne)
  refine ⟨h, hm, le_trans (Real.exp_le_exp.2 ?_) hh⟩
  have hsc := sc_pos t
  have hNpos : (0 : ℝ) < X₁.S.N := by
    have := X₁.S.N_ge
    exact_mod_cast (by omega : 0 < X₁.S.N)
  have hb : (t.T.be x' x' : ℝ) ≤ t.T.be x x := by exact_mod_cast hle
  have h1 : τ.q (α₀ + X₁.S.N • v) ≤ t.sc * t.T.be x x / 2 :=
    hqle.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hsc.le) zero_le_two)
  rw [neg_le_neg_iff]
  refine (div_le_div_of_nonneg_right h1 hNpos.le).trans_eq ?_
  field_simp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X' : USetup C) (p : ℕ) [Fact p.Prime], ∃ K : ℝ, ∀ (z' : X'.M.Z), IsClosed ({z'} : Set X'.M.Z) → ∀ t : UCTrait X' p z', X'.S.R ≤ X'.M.O ((gPt p ≫ t.y) (IsLocalRing.closedPoint (PadicAlgCl p))) → ∀ x : t.T.P.D.toPre.X, x ≠ 0 → ∃ h ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  intro E _ _ _ H Dw l Xo c C X' p _
  exact ⟨1 / (2 * X'.S.N), fun z' hz t _ x hx => exists_mem_maximalIdeal X' p z' hz t x hx⟩

end GlobalTheory.UPoinc.ShortBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitPeriodsBoundedBelowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_classical_trait_periods_bounded_below : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X' : USetup C) (p : ℕ) [Fact p.Prime], ∃ K : ℝ, ∀ (z' : X'.M.Z), IsClosed ({z'} : Set X'.M.Z) → ∀ t : UCTrait X' p z', X'.S.R ≤ X'.M.O ((gPt p ≫ t.y) (IsLocalRing.closedPoint (PadicAlgCl p))) → ∀ x : t.T.P.D.toPre.X, x ≠ 0 → ∃ h ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  first | exact @GlobalTheory.UPoinc.ShortBound.main | exact GlobalTheory.UPoinc.ShortBound.main | (intros; apply GlobalTheory.UPoinc.ShortBound.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupRegularOverModuliPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemGenericPointsMemClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem exists_mem_genericPoints_mem_closure (X : Scheme.{0}) (x : X) : ∃ η ∈ genericPoints X, x ∈ closure {η} := by
  obtain ⟨u, hu, hxu⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
  have hc : IsClosed u := isClosed_of_mem_irreducibleComponents u hu
  have hi : IsIrreducible u := hu.prop
  have hg := hi.isGenericPoint_genericPoint_closure
  rw [hc.closure_eq] at hg
  refine ⟨hi.genericPoint, ?_, ?_⟩
  · show closure {hi.genericPoint} ∈ irreducibleComponents X
    rw [hg.def]; exact hu
  · rw [hg.def]; exact hxu rfl

theorem exists_uSetup_regular_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
    1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x : Xo.XF c),
      ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w := by
  intro E _ _ _ H Dw hpq l Xo c C x
  obtain ⟨η, hη, hx⟩ := exists_mem_genericPoints_mem_closure (Xo.XF c) x
  obtain ⟨X, -, hX⟩ := GlobalTheory.UPoinc.GSetup.exists_uSetup E H Dw hpq l Xo c C η hη 0
  have hr : Set.range X.π = closure {C.i η} := GlobalTheory.UPoinc.USetup.range_π_eq E H Dw hpq l Xo c C X η _ hX rfl
  have hxr : C.i x ∈ Set.range X.π := by
    rw [hr, ← specializes_iff_mem_closure]
    exact (specializes_iff_mem_closure.2 hx).map C.i.continuous
  obtain ⟨w, hw⟩ := hxr
  obtain ⟨wi⟩ := nonempty_uWit X
  obtain ⟨U, c₀, hc, fg, frac, hth, hev, ρ', u', -, hwU, -, -, ⟨G, _, α, β, hα, hβ, hL, -⟩, hu'⟩ :=
    GlobalTheory.UPoinc.exists_urechart_affine E H Dw hpq l Xo c C X wi w ⟨x, hw.symm⟩
  let X' : USetup C :=
    { o₁ := X.o₁
      Ω₁ := X.Ω₁
      S := X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev
      ρ := ρ'
      big := X.big
      u := u'
      pulled := ⟨G, _, α, β, hα, hβ, hL⟩
      gen := fun v => by rw [hu']; exact X.gen v
      M := X.M
      normal := X.normal
      π := X.π
      fin := X.fin
      comp := by
        rw [← Category.assoc, hu', X.comp]
        simp only [Category.assoc] }
  exact ⟨X', w, hw, RatModel.ringOn_le_O (M := X.M) hwU⟩

end GlobalTheory.UPoinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupRegularOverModuliPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.SetupAt

theorem exists_uSetup_regular_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x : Xo.XF c), ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w :=
  GlobalTheory.UPoinc.exists_uSetup_regular_at

end GlobalTheory.UPoinc.SetupAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupRegularOverModuliPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSetup_regular_over_moduliPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x : Xo.XF c), ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w := by
  first | exact @GlobalTheory.UPoinc.SetupAt.exists_uSetup_regular_at | exact GlobalTheory.UPoinc.SetupAt.exists_uSetup_regular_at | (intros; apply GlobalTheory.UPoinc.SetupAt.exists_uSetup_regular_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRegularThetaSetupCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRegularThetaSetupCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

def USetup.regSet (X₁ : USetup C) : Set X₁.M.Z := {z | X₁.S.R ≤ X₁.M.O z}

theorem USetup.isOpen_regSet (X₁ : USetup C) : IsOpen X₁.regSet := by
  obtain ⟨s, hs⟩ := X₁.S.fg
  have e : X₁.regSet = ⋂ a ∈ s, {z | a ∈ X₁.M.O z} := by
    ext z
    simp only [USetup.regSet, Set.mem_setOf_eq, Set.mem_iInter]
    rw [← hs, Algebra.adjoin_le_iff]
    exact ⟨fun h a ha => h ha, fun h a ha => h a ha⟩
  rw [e]
  exact isOpen_biInter_finset fun a _ => X₁.M.isOpen_setOf_mem_O a

def USetup.cov (X₁ : USetup C) : Set (Xo.XF c) := {x | ∃ w ∈ X₁.regSet, X₁.π w = C.i x}

theorem USetup.exists_open_cov {X₁ : USetup C} {ξ : Xo.XF c} {w : X₁.M.Z} (hw : X₁.π w = C.i ξ)
    (hR : X₁.S.R ≤ X₁.M.O w) : ∃ W : Set (Xo.XF c), IsOpen W ∧ ξ ∈ W ∧ closure {ξ} ∩ W ⊆ X₁.cov := by
  haveI := X₁.fin
  have hcl : IsClosedMap X₁.π := X₁.π.isClosedMap
  have hF : IsClosed (X₁.π '' (closure {w} \ X₁.regSet)) := hcl _ (isClosed_closure.sdiff X₁.isOpen_regSet)
  refine ⟨C.i ⁻¹' (X₁.π '' (closure {w} \ X₁.regSet))ᶜ, hF.isOpen_compl.preimage C.i.continuous, ?_, ?_⟩
  · rintro ⟨w', ⟨hw', hn⟩, he⟩
    have e := GlobalTheory.eq_of_specializes_of_isIntegralHom X₁.π (specializes_iff_mem_closure.2 hw') (hw.trans he.symm)
    exact hn (by rw [← e]; exact hR)
  · rintro x ⟨hx, hxW⟩
    have hs : C.i ξ ⤳ C.i x := (specializes_iff_mem_closure.2 hx).map C.i.continuous
    have hT : closure {C.i ξ} ⊆ X₁.π '' closure {w} :=
      (hcl _ isClosed_closure).closure_subset_iff.2
        (Set.singleton_subset_iff.2 ⟨w, subset_closure rfl, hw⟩)
    obtain ⟨w', hw', he⟩ := hT (specializes_iff_mem_closure.1 hs)
    refine ⟨w', ?_, he⟩
    by_contra hn
    exact hxW ⟨w', ⟨hw', hn⟩, he⟩

theorem USetup.exists_finite_cover
    (h : ∀ x : Xo.XF c, ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w) :
    ∃ s : Set (USetup C), s.Finite ∧ ∀ x : Xo.XF c, ∃ X' ∈ s, x ∈ X'.cov := by
  haveI := Formalism.L2.Pj.CompFin.isNoetherian_XF Xo c
  suffices key : ∀ T : TopologicalSpace.Closeds (Xo.XF c),
      ∃ s : Set (USetup C), s.Finite ∧ ∀ x ∈ T, ∃ X' ∈ s, x ∈ X'.cov by
    obtain ⟨s, hs, hT⟩ := key ⊤
    exact ⟨s, hs, fun x => hT x trivial⟩
  intro T
  induction T using WellFoundedLT.induction with
  | _ T ih =>
  by_cases hirr : IsIrreducible (T : Set (Xo.XF c))
  · have hg := hirr.isGenericPoint_genericPoint_closure
    rw [T.isClosed.closure_eq] at hg
    obtain ⟨X', w, hw, hR⟩ := h hirr.genericPoint
    obtain ⟨W, hW, hξ, hcov⟩ := USetup.exists_open_cov hw hR
    let T₁ : TopologicalSpace.Closeds (Xo.XF c) := ⟨(T : Set (Xo.XF c)) \ W, T.isClosed.sdiff hW⟩
    have hlt : T₁ < T := by
      refine lt_of_le_of_ne (fun x hx => hx.1) fun e => ?_
      have hmem : hirr.genericPoint ∈ (T₁ : Set (Xo.XF c)) := by
        rw [e]; exact hg.mem
      exact hmem.2 hξ
    obtain ⟨s, hs, hsT⟩ := ih T₁ hlt
    refine ⟨insert X' s, hs.insert X', fun x hx => ?_⟩
    by_cases hxW : x ∈ W
    · exact ⟨X', Set.mem_insert _ _, hcov ⟨by rw [hg.def]; exact hx, hxW⟩⟩
    · obtain ⟨X'', h1, h2⟩ := hsT x ⟨hx, hxW⟩
      exact ⟨X'', Set.mem_insert_of_mem _ h1, h2⟩
  · obtain ⟨S, hSi, hTS⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible T
    have hle : ∀ k ∈ S, k < T := by
      intro k hk
      refine lt_of_le_of_ne ?_ fun e => hirr (e ▸ hSi ⟨k, hk⟩)
      rw [hTS]
      exact Finset.le_sup (f := id) hk
    have hk : ∀ k : S, ∃ s : Set (USetup C), s.Finite ∧ ∀ x ∈ (k : TopologicalSpace.Closeds (Xo.XF c)),
        ∃ X' ∈ s, x ∈ X'.cov := fun k => ih k (hle k k.2)
    choose f hf hfT using hk
    refine ⟨⋃ k, f k, Set.finite_iUnion hf, fun x hx => ?_⟩
    rw [hTS] at hx
    have hx' : x ∈ ((S.sup id : TopologicalSpace.Closeds (Xo.XF c)) : Set (Xo.XF c)) := hx
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at hx'
    simp only [Set.mem_iUnion, Function.comp_apply, id] at hx'
    obtain ⟨k, hkS, hxk⟩ := hx'
    obtain ⟨X'', h1, h2⟩ := hfT ⟨k, hkS⟩ x hxk
    exact ⟨X'', Set.mem_iUnion.2 ⟨_, h1⟩, h2⟩

theorem exists_fin_uSetup_regular_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), (∀ x : Xo.XF c, ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w) → ∃ (m : ℕ) (X' : Fin m → USetup C) (U : ∀ k, (X' k).M.Z.Opens), (∀ k, (X' k).S.R ≤ (X' k).M.ringOn (U k)) ∧ ∀ x : Xo.XF c, ∃ k, ∃ w ∈ U k, (X' k).π w = C.i x := by
  intro E _ _ _ H Dw l Xo c C h
  obtain ⟨s, hs, hcov⟩ := USetup.exists_finite_cover h
  haveI := hs.to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  refine ⟨m, fun k => (e.symm k).1, fun k => ⟨(e.symm k).1.regSet, (e.symm k).1.isOpen_regSet⟩,
    fun k => fun a ha => RatModel.mem_ringOn.2 fun z hz => hz ha, fun x => ?_⟩
  obtain ⟨X'', hX, w, hw, he⟩ := hcov x
  have key : ∀ Y : USetup C, Y = X'' → ∃ w ∈ Y.regSet, Y.π w = C.i x := by
    rintro Y rfl
    exact ⟨w, hw, he⟩
  exact ⟨e ⟨X'', hX⟩, key _ (by simp)⟩

end GlobalTheory.UPoinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRegularThetaSetupCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_regular_thetaSetup_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), (∀ x : Xo.XF c, ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w) → ∃ (m : ℕ) (X' : Fin m → USetup C) (U : ∀ k, (X' k).M.Z.Opens), (∀ k, (X' k).S.R ≤ (X' k).M.ringOn (U k)) ∧ ∀ x : Xo.XF c, ∃ k, ∃ w ∈ U k, (X' k).π w = C.i x := by
  first | exact @GlobalTheory.UPoinc.exists_fin_uSetup_regular_cover | exact GlobalTheory.UPoinc.exists_fin_uSetup_regular_cover | (intros; apply GlobalTheory.UPoinc.exists_fin_uSetup_regular_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicTraitLiftFiniteThroughPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicTraitLiftFiniteThroughPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_lift_finite_through_point : ∀ (X Z : Scheme.{0}) (f : X ⟶ Z), IsFinite f → ∀ (p : ℕ) [Fact p.Prime] (Y : Sp (OO p) ⟶ Z) (w : X), f w = (gPt p ≫ Y) (IsLocalRing.closedPoint (PadicAlgCl p)) → ∃ y : Sp (OO p) ⟶ X, y ≫ f = Y ∧ (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) = w := by
  intro X Z f hf p _ Y w hw

  set x : Sp (PadicAlgCl p) ⟶ Z := gPt p ≫ Y with hxdef
  obtain ⟨⟨z, φ⟩, hzφ⟩ := (Scheme.SpecToEquivOfField (PadicAlgCl p) Z).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hzφ
  have hz : f w = z := by
    rw [hw, ← hzφ]
    exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply z _)
  subst hz
  have hfin := GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite f w
  letI := (f.residueFieldMap w).hom.toAlgebra
  letI := φ.hom.toAlgebra
  haveI : Module.Finite (Z.residueField (f w)) (X.residueField w) := hfin
  haveI : Algebra.IsAlgebraic (Z.residueField (f w)) (X.residueField w) := inferInstance
  let ψ : X.residueField w →ₐ[Z.residueField (f w)] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  set y0 : Sp (PadicAlgCl p) ⟶ X := Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField w with hy0
  have hy0f : y0 ≫ f = gPt p ≫ Y := by
    rw [← hxdef, ← hzφ, hy0, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact ψ.commutes a
  have hy0w : y0 (IsLocalRing.closedPoint (PadicAlgCl p)) = w :=
    (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply w _)

  haveI : IsProper f := inferInstance
  have hE : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f).1
  obtain ⟨⟨l, hl1, hl2⟩⟩ := (hE { R := OO p, K := PadicAlgCl p, i₁ := y0, i₂ := Y, commSq := ⟨hy0f⟩ }).exists_lift
  refine ⟨l, hl2, ?_⟩
  have : gPt p ≫ l = y0 := hl1
  rw [this, hy0w]

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicTraitLiftFiniteThroughPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicTrait_lift_finite_through_point : ∀ (X Z : Scheme.{0}) (f : X ⟶ Z), IsFinite f → ∀ (p : ℕ) [Fact p.Prime] (Y : Sp (OO p) ⟶ Z) (w : X), f w = (gPt p ≫ Y) (IsLocalRing.closedPoint (PadicAlgCl p)) → ∃ y : Sp (OO p) ⟶ X, y ≫ f = Y ∧ (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) = w := by
  first | exact @GlobalTheory.UPoinc.exists_lift_finite_through_point | exact GlobalTheory.UPoinc.exists_lift_finite_through_point | (intros; apply GlobalTheory.UPoinc.exists_lift_finite_through_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowNormValLeUnitaryThetaFiniteModels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowNormValLeUnitaryThetaFiniteModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ValBound

theorem exists_maximalIdeal_pow_le_map_stalkMap (X Y : Scheme.{0}) (f : X ⟶ Y) [IsFinite f] (x : X) [IsNoetherianRing (X.presheaf.stalk x)] :
    ∃ e : ℕ, maximalIdeal (X.presheaf.stalk x) ^ e ≤
      (maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf, le_sInf_iff]
  rintro P ⟨hP, hPp⟩
  let q : Sp (X.presheaf.stalk x) := ⟨P, hPp⟩
  have hcomap : P.comap (f.stalkMap x).hom = maximalIdeal _ :=
    ((maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hPp.ne_top) (Ideal.map_le_iff_le_comap.1 hP)).symm
  have h1 : Spec.map (f.stalkMap x) q = closedPoint (Y.presheaf.stalk (f x)) := by
    exact PrimeSpectrum.ext hcomap
  have e₁ := Scheme.SpecMap_stalkMap_fromSpecStalk f (x := x)
  have hy : f (X.fromSpecStalk x q) = f x := by
    have := congrArg (fun g => g q) e₁
    simp only [Scheme.Hom.comp_apply, h1, Scheme.fromSpecStalk_closedPoint] at this
    exact this.symm
  have hs : X.fromSpecStalk x q ⤳ x := by
    have : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have h2 : (⟨_, hy⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ := (subtype_specializes_iff _ _).mpr hs
  have h3 : X.fromSpecStalk x q = X.fromSpecStalk x (closedPoint _) :=
    (congrArg Subtype.val h2.eq).trans Scheme.fromSpecStalk_closedPoint.symm
  have h4 : q = closedPoint _ := (X.fromSpecStalk x).isEmbedding.injective h3
  exact (congrArg PrimeSpectrum.asIdeal h4).ge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

theorem exists_valHom {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) :
    ∃ φ : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p, (∀ a, t.val a = φ a) ∧ ∀ a, ‖φ a‖ ≤ 1 :=
  ⟨(OO p).subtype.comp ((RatModel.valLoc t.y z₁ (specializes_of_eq t.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom),
    fun a => by
      show X₁.M.val _ ((X₁.M.stalkEquiv z₁ a : X₁.Ω₁)) = _
      rw [RatModel.val_gPt t.cen]
      rfl,
    fun a => (mem_OO_iff _).1 (Subtype.prop _)⟩

theorem val_germ {X : USetup C} {p : ℕ} [Fact p.Prime] {z : X.M.Z} (t : UCTrait X p z) {V : X.M.Z.Opens}
    (hz : z ∈ V) (g : Γ(X.M.Z, V)) :
    t.val (X.M.Z.presheaf.germ V z hz g) = valF (gPt p ≫ t.y) V g := by
  rw [UCTrait.val, RatModel.stalkHom_germ]
  refine RatModel.val_valF ?_ g
  rintro _ ⟨w, rfl⟩
  exact (RatModel.gPt_specializes t.cen w).mem_open V.isOpen hz

theorem val_stalkMap_germ {X₁ X' : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} {z' : X'.M.Z}
    (t : UCTrait X₁ p z₁) (t' : UCTrait X' p z') (hc : t.y ≫ X₁.π = t'.y ≫ X'.π)
    {U : C.Z.Opens} (hU' : X'.π z' ∈ U) (hU₁ : X₁.π z₁ ∈ U) (s : Γ(C.Z, U)) :
    t'.val (X'.π.stalkMap z' (C.Z.presheaf.germ U _ hU' s)) =
      t.val (X₁.M.Z.presheaf.germ (X₁.π ⁻¹ᵁ U) z₁ hU₁ (X₁.π.app U s)) := by
  rw [Scheme.Hom.germ_stalkMap_apply, val_germ t' (V := X'.π ⁻¹ᵁ U) hU', val_germ t hU₁]
  have e1 := GlobalTheory.Points.valR_comp (gPt p ≫ t'.y) X'.π U s
  have e2 := GlobalTheory.Points.valR_comp (gPt p ≫ t.y) X₁.π U s
  rw [Category.assoc, ← hc, ← Category.assoc] at e1
  exact e1.symm.trans e2

theorem exists_pow_norm_val_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ X' : USetup C) (z₁ : X₁.M.Z), ∃ e : ℕ, 1 ≤ e ∧ ∀ (p : ℕ) [Fact p.Prime] (t : UCTrait X₁ p z₁) (z' : X'.M.Z) (t' : UCTrait X' p z'), t.y ≫ X₁.π = t'.y ≫ X'.π → ∀ h' ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖t'.val h'‖ ^ e ≤ ‖t.val h‖ := by
  intro E _ _ _ H Dw l Xo c C X₁ X' z₁
  have hnoeth : ∀ z' : X'.M.Z, IsNoetherianRing (X'.M.Z.presheaf.stalk z') := fun z' => by
    have : IsDedekindDomain X'.o₁ := ArithBase.ded (Ω := X'.Ω₁)
    have := X'.M.lft
    have : IsLocallyNoetherian X'.M.Z := LocallyOfFiniteType.isLocallyNoetherian X'.M.s
    infer_instance
  haveI := X'.fin
  have hfin := X'.π.finite_preimage_singleton (X₁.π z₁)
  choose e he using fun z' : X'.M.Z => haveI := hnoeth z'; exists_maximalIdeal_pow_le_map_stalkMap X'.M.Z C.Z X'.π z'
  refine ⟨hfin.toFinset.sup e + 1, by omega, ?_⟩
  intro p _ t z' t' hc h' hh'
  have hz' : X'.π z' = X₁.π z₁ := by
    have := congrArg (fun g : Sp (OO p) ⟶ C.Z => g (cPt p)) hc
    simp only [Scheme.Hom.comp_apply, t.cen, t'.cen] at this
    exact this.symm
  have hmem : z' ∈ hfin.toFinset := by simp [hz']
  have hle : e z' ≤ hfin.toFinset.sup e + 1 := (Finset.le_sup hmem).trans (Nat.le_succ _)
  have hpow : h' ^ (hfin.toFinset.sup e + 1) ∈ (maximalIdeal _).map (X'.π.stalkMap z').hom :=
    he z' (Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hh' _))
  obtain ⟨φ', hφ', hφ'1⟩ := exists_valHom t'
  obtain ⟨φ₁, hφ₁, -⟩ := exists_valHom t
  have key : ∀ x ∈ (maximalIdeal (C.Z.presheaf.stalk (X'.π z'))).map (X'.π.stalkMap z').hom,
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖φ' x‖ ≤ ‖φ₁ h‖ := by
    intro x hx
    change x ∈ Ideal.span _ at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      obtain ⟨U, hU, s, rfl⟩ := C.Z.presheaf.germ_exist g
      have hU₁ : X₁.π z₁ ∈ U := hz' ▸ hU
      refine ⟨X₁.M.Z.presheaf.germ (X₁.π ⁻¹ᵁ U) z₁ hU₁ (X₁.π.app U s), ?_, ?_⟩
      · rw [mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have h1 : z₁ ∈ X₁.M.Z.basicOpen (X₁.π.app U s) := (X₁.M.Z.mem_basicOpen _ z₁ hU₁).2 hu
        rw [← Scheme.preimage_basicOpen] at h1
        have h2 : X₁.π z₁ ∈ C.Z.basicOpen s := h1
        rw [← hz'] at h2
        exact (mem_nonunits_iff.1 ((mem_maximalIdeal _).1 hg)) ((C.Z.mem_basicOpen s _ hU).1 h2)
      · rw [← hφ', ← hφ₁, val_stalkMap_germ t t' hc hU hU₁ s]
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hxa⟩ := hx
      obtain ⟨b, hb, hyb⟩ := hy
      rcases le_total ‖φ₁ a‖ ‖φ₁ b‖ with hab | hab
      · exact ⟨b, hb, by
          rw [map_add (f := _)]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hxa.trans hab) hyb)⟩
      · exact ⟨a, ha, by
          rw [map_add (f := _)]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hxa (hyb.trans hab))⟩
    | smul b x _ hx =>
      obtain ⟨a, ha, hxa⟩ := hx
      refine ⟨a, ha, ?_⟩
      rw [smul_eq_mul, map_mul, norm_mul]
      calc ‖φ' b‖ * ‖φ' x‖ ≤ 1 * ‖φ' x‖ := mul_le_mul_of_nonneg_right (hφ'1 b) (norm_nonneg _)
        _ = ‖φ' x‖ := one_mul _
        _ ≤ ‖φ₁ a‖ := hxa
  obtain ⟨h, hh, hnorm⟩ := key _ hpow
  refine ⟨h, hh, ?_⟩
  rw [hφ', hφ₁, ← norm_pow, ← map_pow]
  exact hnorm

end GlobalTheory.UPoinc.ValBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowNormValLeUnitaryThetaFiniteModelsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_norm_val_le_unitaryTheta_finite_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ X' : USetup C) (z₁ : X₁.M.Z), ∃ e : ℕ, 1 ≤ e ∧ ∀ (p : ℕ) [Fact p.Prime] (t : UCTrait X₁ p z₁) (z' : X'.M.Z) (t' : UCTrait X' p z'), t.y ≫ X₁.π = t'.y ≫ X'.π → ∀ h' ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), ‖t'.val h'‖ ^ e ≤ ‖t.val h‖ := by
  first | exact @GlobalTheory.UPoinc.ValBound.exists_pow_norm_val_le | exact GlobalTheory.UPoinc.ValBound.exists_pow_norm_val_le | (intros; apply GlobalTheory.UPoinc.ValBound.exists_pow_norm_val_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonOfIsFiniteOfIsClosedImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonOfIsFiniteOfIsClosedImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory

theorem isClosed_singleton_of_isFinite : ∀ (X Z : Scheme.{0}) (f : X ⟶ Z), IsFinite f → ∀ x : X,
    IsClosed ({f x} : Set Z) → IsClosed ({x} : Set X) := by
  intro X Z f hf x hx
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have h : x ⤳ w := specializes_iff_mem_closure.mpr hw
  have e : f w = f x := (h.map f.continuous).mem_closed hx rfl
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have hs : (⟨x, rfl⟩ : f ⁻¹' {f x}) ⤳ ⟨w, e⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val hs.eq.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedSingletonOfIsFiniteOfIsClosedImageStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_singleton_of_isFinite_of_isClosed_image : ∀ (X Z : Scheme.{0}) (f : X ⟶ Z), IsFinite f → ∀ x : X, IsClosed ({f x} : Set Z) → IsClosed ({x} : Set X) := by
  first | exact @GlobalTheory.isClosed_singleton_of_isFinite | exact GlobalTheory.isClosed_singleton_of_isFinite | (intros; apply GlobalTheory.isClosed_singleton_of_isFinite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitPeriodsBoundedBelowClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.PerBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

theorem sc_pos (t : UCTrait X₁ p z₁) : 0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem eq_zero_of_sum_eq_zero (hpq : ¬ 1 ≤ Dw.p + Dw.q) (T : UTrait Xo c) (x : T.P.D.toPre.X) : x = 0 := by
  have hr := UTrait.finrank_le_min E H Dw l Xo c T
  have h0 : Module.finrank (𝓞 E) T.P.D.toPre.X = 0 := by omega
  have : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨a, ha, hax⟩ := Module.finrank_eq_zero_iff.1 h0 x
  obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) a).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero ha)
  have h : n • x = 0 := by
    rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul, hax, smul_zero]
  exact (smul_eq_zero.1 h).resolve_left hn

end GlobalTheory.UPoinc.PerBound


open GlobalTheory.UPoinc.PerBound in
theorem GlobalTheory.UPoinc.lam_of_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ K : ℝ, ∀ (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  intro E _ _ _ H Dw l Xo c C X₁ p _ z₁ hz
  by_cases hpq : 1 ≤ Dw.p + Dw.q
  swap
  · exact ⟨0, fun t x hx => absurd (eq_zero_of_sum_eq_zero hpq t.T x) hx⟩
  obtain ⟨m, X', U, hU, hcov⟩ := GlobalTheory.T.exists_finite_regular_thetaSetup_cover E H Dw l Xo c C (GlobalTheory.T.exists_thetaSetup_regular_over_moduliPoint E H Dw hpq l Xo c C)
  choose K hK using fun k => GlobalTheory.T.unitary_classical_trait_periods_bounded_below E H Dw l Xo c C (X' k) p
  choose e he1 he using fun k => GlobalTheory.T.exists_pow_norm_val_le_unitaryTheta_finite_models E H Dw l Xo c C X₁ (X' k) z₁
  refine ⟨∑ k, (e k : ℝ) * |K k|, fun t x hx => ?_⟩
  have hzc : IsClosed ({X₁.π z₁} : Set C.Z) := by
    haveI := X₁.fin
    have := X₁.π.isClosedMap _ hz
    rwa [Set.image_singleton] at this
  obtain ⟨k, w, hwU, hw⟩ := hcov ((spMap t.ι ≫ t.T.y) (IsLocalRing.closedPoint (PadicAlgCl p)))
  have hgen : (X' k).π w = (gPt p ≫ (t.y ≫ X₁.π)) (IsLocalRing.closedPoint (PadicAlgCl p)) := by
    rw [hw, t.comm]
    rfl
  obtain ⟨y', hy'π, hy'w⟩ := GlobalTheory.T.exists_padicTrait_lift_finite_through_point _ _ (X' k).π (X' k).fin p (t.y ≫ X₁.π) w hgen
  have hz'π : (X' k).π (y' (cPt p)) = X₁.π z₁ := by
    have := congrArg (fun f => f (cPt p)) hy'π
    simp only [Scheme.Hom.comp_apply] at this
    rw [this, t.cen]
  have hz'c := GlobalTheory.T.isClosed_singleton_of_isFinite_of_isClosed_image _ _ _ (X' k).fin (y' (cPt p)) (hz'π ▸ hzc)
  let t' : UCTrait (X' k) p (y' (cPt p)) :=
    { y := y', cen := rfl, T := t.T, ι := t.ι, int := t.int, comm := by rw [hy'π]; exact t.comm }
  have hreg : (X' k).S.R ≤ (X' k).M.O ((gPt p ≫ t'.y) (IsLocalRing.closedPoint (PadicAlgCl p))) := by
    show (X' k).S.R ≤ (X' k).M.O ((gPt p ≫ y') (IsLocalRing.closedPoint (PadicAlgCl p)))
    rw [hy'w]
    exact (hU k).trans (RatModel.ringOn_le_O hwU)
  obtain ⟨h', hh'm, hh'⟩ := hK k (y' (cPt p)) hz'c t' hreg x hx
  obtain ⟨h, hhm, hh⟩ := he k p t (y' (cPt p)) t' hy'π.symm h' hh'm
  refine ⟨h, hhm, le_trans ?_ hh⟩
  have hs : 0 ≤ t.sc * t.T.be x x := mul_nonneg (sc_pos t).le (by exact_mod_cast (be_pos _ x hx).le)
  have hsum : (e k : ℝ) * |K k| ≤ ∑ k, (e k : ℝ) * |K k| :=
    Finset.single_le_sum (f := fun k => (e k : ℝ) * |K k|) (fun k _ => by positivity) (Finset.mem_univ k)
  have hKk : (e k : ℝ) * K k ≤ (e k : ℝ) * |K k| := mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  calc Real.exp (-((∑ k, (e k : ℝ) * |K k|) * (t.sc * t.T.be x x)))
      ≤ Real.exp (-(K k * (t.sc * t.T.be x x))) ^ e k := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.2
        nlinarith
    _ ≤ ‖t'.val h'‖ ^ e k := pow_le_pow_left₀ (Real.exp_pos _).le hh' _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitPeriodsBoundedBelowClosedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classical_trait_periods_bounded_below_closed_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ K : ℝ, ∀ (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  first | exact @GlobalTheory.UPoinc.lam_of_closed | exact GlobalTheory.UPoinc.lam_of_closed | (intros; apply GlobalTheory.UPoinc.lam_of_closed <;> assumption)
end
