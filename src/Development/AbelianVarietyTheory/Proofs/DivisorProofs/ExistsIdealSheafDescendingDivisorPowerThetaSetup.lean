module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafPullbackEqDivisorOfApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongModOfSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitsFourierTermsAllLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitPeriodsBoundedBelowClosedPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxPoincareSeriesAtThetaSetupPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalTraitSystemAtClosedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupClassicalTraitPeriodsBoundedBelowMaxId
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupClassicalTraitPeriodsBoundedBelowMaxId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.LamBound

theorem exists_not_dvd_le {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ y, y ≠ 0 → 0 < β y y) (m : ℕ) (hm : 2 ≤ m) :
    ∀ (k : ℕ) (x : X), (β x x).toNat = k → x ≠ 0 →
      ∃ x', x' ≠ 0 ∧ (¬ ∃ v, x' = m • v) ∧ β x' x' ≤ β x x := _root_.GlobalTheory.UPoinc.ShortBound.exists_not_dvd_le (X := X) β hβ m hm

theorem isE8_apply_zero_zero_pos {W : Matrix (Fin 8) (Fin 8) ℤ} (h : IsE8 W) : 0 < W 0 0 := by
  have h1 := h.1.diag_pos (i := 0)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add] at h1
  have : (0 : ℝ) < W 0 0 := by linarith
  exact_mod_cast this

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem beta_pos (T : Trait F) (x : T.D.toPre.X) (hx : x ≠ 0) : 0 < T.β x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem sc_pos {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) : 0 < c.sc := by
  have hϖ0 : algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 c.T.irr.ne_zero
  have h0 : c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (c.int _).1 hinv
    apply c.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective c.T.V (FractionRing c.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold CTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

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

theorem qW_single {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (x : X) :
    qW W β (Pi.single 0 x) = W 0 0 * β x x := by
  simp [qW, Fin.sum_univ_succ]

theorem lab : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ ε yy, IsLab X₁ ε c yy := by
  intro g n F W Z i X₁ hg hn ho hi hE hT hP p _ z₁ c
  obtain ⟨ε, hε, -⟩ := GlobalTheory.Poinc.exists_diagEnd_isMonHom g n F W _ X₁.ρ.P X₁.u X₁.sharp
  exact ⟨ε, GlobalTheory.Poinc.exists_isLab g n F W Z i X₁ hg hn ho hi hE hT hP ε hε p z₁ c⟩

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ C : ℝ, ∀ (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(C * (c.sc * c.T.β x x))) ≤ ‖c.val h‖ := by
  intro g n F W Z i X₁ hg hn ho hi hE hT hP p _ z₁ hz
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  have hdiv : X₁.M.HasDiv X₁.S.th :=
    hT X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.u X₁.sharp X₁.gen X₁.M X₁.π X₁.normal X₁.comp
  refine ⟨(W 0 0 : ℝ) / X₁.S.N, fun c x hx => ?_⟩
  obtain ⟨x', hx', hnd, hle⟩ :=
    exists_not_dvd_le c.T.β (beta_pos c.T) X₁.S.N X₁.S.N_ge _ x rfl hx
  obtain ⟨ε, yy, c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hR, y₀, hat, u, l, j, hq, -⟩ :=
    lab g n F W Z i X₁ hg hn ho hi hE hT hP p z₁ c
  let S' := X₁.S.rechart c₀ hc R' fg frac hth hev
  have hdiv' : X₁.M.HasDiv S'.th := fun z => (hdiv z).imp fun k hk => (RatModel.div_mul_iff hc).2 hk
  have htests : S'.HasTests :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hU hL hL2 hUT X₁.o₁ X₁.Ω₁ S' ρ').1
  have hy : ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ S'.R a)‖ ≤ 1 := fun a => by
    rw [hat]
    exact RatModel.norm_val_le_one c.cen ((X₁.M.O z₁).algebraMap_mem a)
  obtain ⟨τ, e, hτ, -⟩ := exists_test_match X₁.o₁ X₁.Ω₁ S' ρ' p y₀ u l
    (GlobalTheory.T.thetaConstant_bounded_by_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u l hy) (GlobalTheory.T.unitThetaConstants_generate_integralTorsion hL hL2 hUT _ _ S' ρ' p y₀ u l hy)
    (GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u l hy) (GlobalTheory.T.exists_norm_torsionSum_shortestVector_eq hL hL2 hUT _ _ S' ρ' p y₀ u l hy)
    (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hUT _ _ S' ρ' p y₀ u l hy)
  let α₀ : τ.X := e.symm (j.symm (Pi.single 0 x'))
  obtain ⟨v, hv⟩ := exists_shortest τ.q τ.pos X₁.S.N α₀
  have hne : α₀ + X₁.S.N • v ≠ 0 := fun h0 => hnd ⟨-(j (e v) 0), by
    have h1 := congrFun (congrArg (fun t => j (e t)) h0) 0
    simp only [α₀, map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, map_zero, Pi.add_apply, Pi.single_eq_same,
      Pi.smul_apply, Pi.zero_apply] at h1
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left h1⟩
  have hqle : τ.q (α₀ + X₁.S.N • v) ≤ (W 0 0 : ℝ) * (c.sc * c.T.β x' x') := by
    have h1 := hv (-v)
    rw [smul_neg, add_neg_cancel_right] at h1
    refine h1.trans_eq ?_
    rw [hτ, hq]
    simp only [α₀, AddEquiv.apply_symm_apply, qW_single]
    push_cast
    ring
  obtain ⟨h, hm, hh⟩ := GlobalTheory.exists_mem_maximalIdeal_exp_le_norm_val X₁.o₁ X₁.Ω₁ S' X₁.M X₁.normal hdiv' htests z₁ hz p
    c.y y₀ c.cen (fun a ha => hR ha) hat τ _ hv (pos_of_tendsto τ.q τ.pos _ hne)
  refine ⟨h, hm, le_trans (Real.exp_le_exp.2 ?_) hh⟩
  have hsc := sc_pos c
  have hW : (0 : ℝ) ≤ W 0 0 := by exact_mod_cast (isE8_apply_zero_zero_pos hE).le
  have hNpos : (0 : ℝ) < X₁.S.N := by
    have := X₁.S.N_ge
    exact_mod_cast (by omega : 0 < X₁.S.N)
  have hb : (c.T.β x' x' : ℝ) ≤ c.T.β x x := by exact_mod_cast hle
  have h1 : τ.q (α₀ + X₁.S.N • v) ≤ (W 0 0 : ℝ) * (c.sc * c.T.β x x) :=
    hqle.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hsc.le) hW)
  rw [neg_le_neg_iff, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right h1 hNpos.le

end GlobalTheory.Poinc.LamBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupClassicalTraitPeriodsBoundedBelowMaxIdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetup_classicalTraitPeriods_bounded_below_maxIdeal : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ C : ℝ, ∀ (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X), x ≠ 0 → ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(C * (c.sc * c.T.β x x))) ≤ ‖c.val h‖ := by
  first | exact @GlobalTheory.Poinc.LamBound.main | exact GlobalTheory.Poinc.LamBound.main | (intros; apply GlobalTheory.Poinc.LamBound.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalTraitSystemAtClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.PreSys

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem rank_le (hn : 3 ≤ n) (T : Trait F) : Module.finrank ℤ T.D.toPre.X ≤ g := GlobalTheory.T.siegelTrait_characterGroup_finrank_le_genus_of_three_le g n F hn T

theorem lam (hE : IsE8 W) (hT : ThetaInt F W i) (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z)
    (hz : IsClosed ({z₁} : Set X₁.M.Z)) : ∃ C : ℝ, ∀ (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X), x ≠ 0 →
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(C * (c.sc * c.T.β x x))) ≤ ‖c.val h‖ :=
  GlobalTheory.T.thetaSetup_classicalTraitPeriods_bounded_below_maxIdeal _ n F W Z i X₁ X₁.one_le X₁.three_le X₁.odd X₁.imm hE hT X₁.projM p z₁ hz

variable {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def evC (c : CTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p :=
  (RatModel.valHomOf (gPt p ≫ c.y) z₁ (RatModel.gPt_specializes c.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem evC_apply (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : evC c a = c.val a := rfl

theorem norm_evC_le (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖evC c a‖ ≤ 1 :=
  RatModel.norm_val_le_one c.cen (X₁.M.stalkEquiv z₁ a).2

theorem norm_evC_lt (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) (ha : a ∈ maximalIdeal _) :
    ‖evC c a‖ < 1 := by
  have h1 : ¬ IsUnit (X₁.M.stalkEquiv z₁ a) := fun hu => ha ((isUnit_map_iff (X₁.M.stalkEquiv z₁) a).1 hu)
  exact (RatModel.norm_val_lt_one_iff c.cen (X₁.M.stalkEquiv z₁ a).2).2 h1

theorem sc_pos (c : CTrait X₁ p z₁) : 0 < c.sc := by
  have hϖ0 : algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 c.T.irr.ne_zero
  have h0 : c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (c.int _).1 hinv
    apply c.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective c.T.V (FractionRing c.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold CTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem beta_pos (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X) (hx : x ≠ 0) : 0 < c.T.β x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal c.T.V).ne_top c.T.mono hx
  fin_cases j
  simpa using hj

end GlobalTheory.Poinc.PreSys

namespace GlobalTheory.Poinc.PreSys

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}


variable (X₁ p) in
abbrev Key : Type := (Sp (OO p) ⟶ X₁.M.Z) × (Σ k : ℕ, (Fin k → ℤ) → (Fin k → ℤ) → ℝ)

def Rep (c : CTrait X₁ p z₁) (q : Key X₁ p) : Prop :=
  c.y = q.1 ∧ ∃ e : (Fin q.2.1 → ℤ) ≃ₗ[ℤ] c.T.D.toPre.X, ∀ u v, q.2.2 u v = c.sc * c.T.β (e u) (e v)

def coord (c : CTrait X₁ p z₁) : (Fin (Module.finrank ℤ c.T.D.toPre.X) → ℤ) ≃ₗ[ℤ] c.T.D.toPre.X :=
  (Module.finBasis ℤ c.T.D.toPre.X).equivFun.symm

def keyOf (c : CTrait X₁ p z₁) : Key X₁ p :=
  (c.y, ⟨Module.finrank ℤ c.T.D.toPre.X, fun u v => c.sc * c.T.β (coord c u) (coord c v)⟩)

theorem rep_keyOf (c : CTrait X₁ p z₁) : Rep c (keyOf c) := ⟨rfl, coord c, fun _ _ => rfl⟩


variable (X₁ p z₁) in
def Pts : Type := {q : Key X₁ p // ∃ c : CTrait X₁ p z₁, Rep c q}

noncomputable def pick (y : Pts X₁ p z₁) : CTrait X₁ p z₁ := Classical.choose y.2

theorem pick_rep (y : Pts X₁ p z₁) : Rep (pick y) y.1 := Classical.choose_spec y.2


variable (X₁ p z₁) in
noncomputable def sys : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁) where
  Y := Pts X₁ p z₁
  ev y := evC (pick y)
  ev_le y h := norm_evC_le _ h
  ev_lt y h hh := norm_evC_lt _ h hh
  X y := (pick y).T.D.toPre.X
  rank_le y := rank_le X₁.three_le _
  β y := (pick y).T.β
  bal y := ⟨(pick y).T.symm, fun a u v => by simp⟩
  pos y x hx := beta_pos _ x hx
  sc y := (pick y).sc
  sc_pos y := sc_pos _

theorem sys_matches : (sys X₁ p z₁ (g := g)).Matches := by
  intro c
  refine ⟨⟨keyOf c, c, rep_keyOf c⟩, fun a => ?_, ?_⟩
  · obtain ⟨hy, -⟩ := pick_rep ⟨keyOf c, c, rep_keyOf c⟩
    show evC _ a = c.val a
    rw [evC_apply]
    unfold CTrait.val
    rw [hy]
    rfl
  · obtain ⟨-, e', he'⟩ := pick_rep ⟨keyOf c, c, rep_keyOf c⟩
    have key : ∀ a b : (pick ⟨keyOf c, c, rep_keyOf c⟩).T.D.toPre.X,
        (pick ⟨keyOf c, c, rep_keyOf c⟩).sc * (pick ⟨keyOf c, c, rep_keyOf c⟩).T.β a b =
          c.sc * c.T.β (coord c (e'.symm a)) (coord c (e'.symm b)) := by
      intro a b
      have h := he' (e'.symm a) (e'.symm b)
      rw [e'.apply_symm_apply, e'.apply_symm_apply] at h
      exact h.symm
    exact ⟨e'.symm.trans (coord c), key⟩

theorem sys_lam (hE : IsE8 W) (hT : ThetaInt F W i) (hz : IsClosed ({z₁} : Set X₁.M.Z)) :
    (sys X₁ p z₁ (g := g)).abelian₂ := by
  obtain ⟨C, hC⟩ := lam hE hT X₁ p z₁ hz
  exact ⟨C, fun y x hx => by
    obtain ⟨h, hm, hle⟩ := hC (pick y) x hx
    exact ⟨h, hm, hle⟩⟩

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z),
    IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) →
      ∃ Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁), Φ.Matches ∧ Φ.abelian₂ ∧
        (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X,
          ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) := by
  intro g n F W Z i hE hT X₁ p _ z₁ hz
  exact ⟨sys X₁ p z₁, sys_matches, sys_lam hE hT hz, fun y => ⟨pick y, fun a => rfl, LinearEquiv.refl ℤ _,
    fun a b => rfl⟩⟩

end GlobalTheory.Poinc.PreSys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalTraitSystemAtClosedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classicalTrait_system_at_closedPoint : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z), IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) → ∃ Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁), Φ.Matches ∧ Φ.abelian₂ ∧ (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) := by
  first | exact @GlobalTheory.Poinc.PreSys.main | exact GlobalTheory.Poinc.PreSys.main | (intros; apply GlobalTheory.Poinc.PreSys.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxPoincareSeriesAtThetaSetupPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.GApprox

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem sc_pos {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) : 0 < c.sc := by
  set u := algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ with hu
  have h0 : c.T.ϖ ≠ 0 := c.T.irr.ne_zero
  have hu0 : u ≠ 0 := by
    rw [hu]; exact (IsFractionRing.injective c.T.V (FractionRing c.T.V)).ne_iff' (map_zero _) |>.2 h0
  have hι0 : c.ι u ≠ 0 := (map_ne_zero c.ι).2 hu0
  have hle : ‖c.ι u‖ ≤ 1 := (c.int u).2 ⟨_, rfl⟩
  have hlt : ‖c.ι u‖ < 1 := by
    refine lt_of_le_of_ne hle fun h1 => ?_
    have : ‖c.ι u⁻¹‖ ≤ 1 := by rw [map_inv₀, norm_inv, h1, inv_one]
    obtain ⟨v, hv⟩ := (c.int _).1 this
    apply c.T.irr.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective c.T.V (FractionRing c.T.V)
    rw [map_mul, hv, ← hu, mul_inv_cancel₀ hu0, map_one]
  have hpos : 0 < ‖c.ι u‖ := norm_pos_iff.2 hι0
  unfold CTrait.sc
  rw [← hu]
  linarith [Real.log_neg hpos hlt]

theorem sc_evalZ_eq_of_equiv {φ : InvFun ℤ} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [Module.Finite ℤ X]
    [Module.Finite ℤ Y] (hP : IsPolFanOn id φ X) {β : LinearMap.BilinForm ℤ X} (hs : ∀ a b, β a b = β b a)
    (hp : ∀ x, 0 ≤ β x x) {β' : LinearMap.BilinForm ℤ Y} {s s' : ℝ} (hs0 : 0 ≤ s) (hs' : 0 < s') (e : X ≃ₗ[ℤ] Y)
    (he : ∀ a b, s * β a b = s' * β' (e a) (e b)) : s * φ.evalZ β = s' * φ.evalZ β' := by
  have hmem : toReal β ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) :=
    StrictData.toReal_mem_psdCone (mem_balForms_int.2 hs) hp
  have hform : toReal (pull e.toLinearMap β') = (s / s') • toReal β := by
    refine LinearMap.ext₂ fun a b => ?_
    have := he a b
    simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul, LinearEquiv.coe_coe]
    field_simp
    linarith
  have h1 : φ.evalZ (pull e.toLinearMap β') = φ.evalZ β' := evalZ_pull φ e.surjective _
  rw [← h1, ← evalR_toReal φ (pull _ _), hform, hP.homog _ hmem _ (div_nonneg hs0 hs'.le), evalR_toReal]
  field_simp

theorem sc_evalZ_eq {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} {φ : InvFun ℤ} (hpol : IsPolFan id g φ)
    (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (c : CTrait X₁ p z₁)
    (e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X) (he : ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) :
    Φ.sc y * @InvFun.evalZ ℤ _ φ (Φ.X y) _ (Φ.mod y) (Φ.fin y) (Φ.β y) = c.sc * φ.evalZ c.T.β := by
  have hm : Φ.mod y = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  have hrk : Module.finrank ℤ (Φ.X y) ≤ g := by
    convert Φ.rank_le y <;> first | rfl | exact hm.symm
  have hP : IsPolFanOn id φ (Φ.X y) := hpol _ hrk
  convert sc_evalZ_eq_of_equiv hP (Φ.bal y).1 (fun x => by
      by_cases hx : x = 0
      · simp [hx]
      · exact (Φ.pos y x hx).le) (Φ.sc_pos y).le (sc_pos c) e he

end GlobalTheory.Poinc.GApprox

namespace GlobalTheory.Poinc.GApprox

theorem exists_hasSupports_int (q : ℕ) (φ : InvFun ℤ) (hpol : IsPolFan id q φ) :
    ∃ d, 1 ≤ d ∧ HasSupports (id : ℤ → ℤ) q φ d := by
  refine exists_hasSupports ℤ id q φ hpol fun X _ iM _ _ hX r γ hγ => ?_
  obtain rfl : iM = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  have : Module.Free ℤ X := inferInstance
  exact exists_supports_int φ X (hpol X hX) r γ hγ

end GlobalTheory.Poinc.GApprox

open GlobalTheory.Poinc.GApprox in
theorem GlobalTheory.Poinc.exists_approxAt : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0})
    (i : F.X ⟶ Z) (X₁ : Setup F W i), IsE8 W → ThetaInt F W i → 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ →
    ∃ d : ℕ, 1 ≤ d ∧ ApproxAt X₁ φ d := by
  intro g n F W Z i X₁ hE hT hg φ hpol
  obtain ⟨d₀, hd₀, hsup⟩ := exists_hasSupports_int g φ hpol
  have hW : 0 < W 0 0 := by
    have := hE.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at this
    have h2 : (0 : ℤ) < W 0 0 + W 0 0 := by exact_mod_cast this
    omega
  have hN : 3 ≤ X₁.S.r * X₁.S.N := by
    have h1 := X₁.big.2.2
    have h2 : 1 ≤ X₁.S.N ^ X₁.S.g * X₁.S.g.factorial :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (by have := X₁.S.N_ge; omega))
        (Nat.factorial_ne_zero _))
    omega
  refine ⟨(W 0 0).toNat * d₀, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  intro p _ z₁ c₀ e
  have hcl : IsClosed ({z₁} : Set X₁.M.Z) := c₀.cen ▸ isClosed_singleton_cPt c₀.y
  obtain ⟨Φ, hM, hL, hR⟩ := GlobalTheory.T.exists_classicalTrait_system_at_closedPoint g n F W Z i hE hT X₁ p z₁ hcl
  have hF := GlobalTheory.T.classical_traits_fourier_terms_all_levels g n F W Z i X₁ p z₁ Φ hE.1 hR
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  have hA := approx_of_fpre ℤ id bddAct_int_and_cm.1 g φ hpol d₀ hsup 7 W hE.1 (X₁.S.r * X₁.S.N) p hN _ Φ hL hF
  obtain ⟨y₀, hev₀, e₀, he₀⟩ := hM c₀
  obtain ⟨f, hf1, hf2⟩ := hA y₀ e
  have key : ∀ (y : Φ.Y) (c : CTrait X₁ p z₁) (e' : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X),
      (∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e' a) (e' b)) →
      Φ.sc y * (((W 0 0).toNat * d₀ : ℕ) * @InvFun.evalZ ℤ _ φ (Φ.X y) _ (Φ.mod y) (Φ.fin y) (Φ.β y)) = c.sc * (((W 0 0).toNat * d₀ : ℕ) * φ.evalZ c.T.β) := by
    intro y c e' h
    have := sc_evalZ_eq hpol Φ y c e' h
    calc Φ.sc y * (((W 0 0).toNat * d₀ : ℕ) * @InvFun.evalZ ℤ _ φ (Φ.X y) _ (Φ.mod y) (Φ.fin y) (Φ.β y))
        = ((W 0 0).toNat * d₀ : ℕ) * (Φ.sc y * @InvFun.evalZ ℤ _ φ (Φ.X y) _ (Φ.mod y) (Φ.fin y) (Φ.β y)) := by ring
      _ = c.sc * (((W 0 0).toNat * d₀ : ℕ) * φ.evalZ c.T.β) := by rw [this]; ring
  refine ⟨f, ?_, fun c => ?_⟩
  · rw [← hev₀ f, hf1, key y₀ c₀ e₀ he₀]
  · obtain ⟨y, hev, e', he'⟩ := hM c
    rcases hf2 y with h | ⟨h, hh, hle⟩
    · left; rw [← hev f, ← key y c e' he']; exact h
    · right; exact ⟨h, hh, by rw [← hev f, ← hev h]; exact hle⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxPoincareSeriesAtThetaSetupPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approxPoincareSeries_at_thetaSetup_points : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), IsE8 W → ThetaInt F W i → 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∃ d : ℕ, 1 ≤ d ∧ ApproxAt X₁ φ d := by
  first | exact @GlobalTheory.Poinc.exists_approxAt | exact GlobalTheory.Poinc.exists_approxAt | (intros; apply GlobalTheory.Poinc.exists_approxAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointFactorsThroughSiegelModuliTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointFactorsThroughSiegelModuliTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.TraitOfPoint

variable {p : ℕ} [Fact p.Prime]

set_option synthInstance.maxHeartbeats 400000 in
theorem base_integralClosure (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ∃ _ : IsDiscreteValuationRing (integralClosure ℤ_[p] K), GlobalTheory.Mum.Base (integralClosure ℤ_[p] K) := by
  haveI := GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt p K
  exact ⟨inferInstance, ⟨inferInstance, inferInstance, inferInstance,
    GlobalTheory.DiscEval.isAdicComplete_integralClosure K⟩, GlobalTheory.charZero_integralClosure_padicInt⟩

theorem lft_toInt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : ArithBase o Ω] (M : RatModel o Ω) :
    LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  have hft := h.ft
  have := M.lft
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 hft
  infer_instance

end GlobalTheory.Poinc.TraitOfPoint


open GlobalTheory.Poinc.TraitOfPoint Polynomial in
theorem GlobalTheory.Poinc.exists_trait_of_classical_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z), IsOpenImmersion i → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i → ∃ (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p) (j : T.V →+* OO p) (ξ : Sp T.V ⟶ Y.Z), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) ∧ (∀ v, (j v : PadicAlgCl p) = ι (algebraMap T.V (FractionRing T.V) v)) ∧ IsLocalHom j ∧ spMap j ≫ ξ = y ∧ jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i := by
  intro g n F Z i hi W8 X₁ Y πY p _ y hy
  haveI := hi
  haveI := lft_toInt Y
  obtain ⟨K, hK, H⟩ := GlobalTheory.padicAlgCl_integral_points.2 Y.Z (Y.s ≫ spMap (algebraMap ℤ X₁.o₁)) p y
  haveI := hK
  obtain ⟨j₀, y₀, hj₀, -, hy₀⟩ := H K le_rfl
  obtain ⟨hdvr, hbase⟩ := base_integralClosure K

  have hinj₀ : Function.Injective (algebraMap (integralClosure ℤ_[p] K) (PadicAlgCl p)) :=
    fun a b h => Subtype.ext (Subtype.ext h)
  let ι₀ : FractionRing (integralClosure ℤ_[p] K) →+* PadicAlgCl p := IsFractionRing.lift hinj₀
  have hgen : gPt p ≫ spMap j₀ = spMap ι₀ ≫ jK (integralClosure ℤ_[p] K) :=
    GlobalTheory.ArcPointDescent.sp_sq fun a => by
      simp only [ι₀, IsFractionRing.lift_algebraMap]
      exact hj₀ a
  have hrange : Set.range (jK (integralClosure ℤ_[p] K) ≫ y₀ ≫ πY ≫ X₁.π) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    have hw : w = spMap ι₀ (IsLocalRing.closedPoint (PadicAlgCl p)) := Subsingleton.elim _ _
    refine hy ⟨IsLocalRing.closedPoint (PadicAlgCl p), ?_⟩
    have e : gPt p ≫ y ≫ πY ≫ X₁.π = spMap ι₀ ≫ jK (integralClosure ℤ_[p] K) ≫ y₀ ≫ πY ≫ X₁.π := by
      rw [← hy₀]
      simp only [← Category.assoc]
      rw [hgen]
    rw [e, hw]
    exact Scheme.Hom.comp_apply _ _ _
  let yK := IsOpenImmersion.lift i _ hrange
  obtain ⟨T, f, fK, hfinj, -, hffin, hfK, hTy⟩ :=
    GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n (cycAway n) (zetaAway n) F (integralClosure ℤ_[p] K) hbase hdvr yK

  letI : Algebra (integralClosure ℤ_[p] K) T.V := f.toAlgebra
  haveI : Module.Finite (integralClosure ℤ_[p] K) T.V := hffin
  haveI : Module.IsTorsionFree (integralClosure ℤ_[p] K) T.V :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hfinj
  haveI : Module.IsTorsionFree (integralClosure ℤ_[p] K) (FractionRing T.V) := by
    refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
    rw [IsScalarTower.algebraMap_eq (integralClosure ℤ_[p] K) T.V (FractionRing T.V)]
    exact (IsFractionRing.injective T.V (FractionRing T.V)).comp hfinj
  haveI : Module.IsTorsionFree (integralClosure ℤ_[p] K) (PadicAlgCl p) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj₀
  haveI : Algebra.IsAlgebraic (integralClosure ℤ_[p] K) T.V := inferInstance
  haveI : Algebra.IsAlgebraic T.V (FractionRing T.V) := IsLocalization.isAlgebraic _ (nonZeroDivisors T.V)
  haveI : Algebra.IsAlgebraic (integralClosure ℤ_[p] K) (FractionRing T.V) :=
    Algebra.IsAlgebraic.trans (integralClosure ℤ_[p] K) T.V (FractionRing T.V)
  let ι' : FractionRing T.V →ₐ[integralClosure ℤ_[p] K] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ι : FractionRing T.V →+* PadicAlgCl p := ι'.toRingHom
  have hιf : ∀ a : integralClosure ℤ_[p] K, ι (algebraMap T.V (FractionRing T.V) (f a)) = ((a : K) : PadicAlgCl p) := by
    intro a
    have h1 := ι'.commutes a
    rw [IsScalarTower.algebraMap_apply (integralClosure ℤ_[p] K) T.V (FractionRing T.V)] at h1
    exact h1

  let φ : ℤ_[p] →+* T.V := f.comp (algebraMap ℤ_[p] (integralClosure ℤ_[p] K))
  have hcomp : ι.comp ((algebraMap T.V (FractionRing T.V)).comp φ) = algebraMap ℤ_[p] (PadicAlgCl p) := by
    ext c
    change ι (algebraMap T.V (FractionRing T.V) (f (algebraMap ℤ_[p] (integralClosure ℤ_[p] K) c))) = _
    rw [hιf]
    rfl
  have hφint : φ.IsIntegral :=
    RingHom.IsIntegral.trans _ _ (fun x => Algebra.IsIntegral.isIntegral x) hffin.to_isIntegral

  have hint : ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V)) := by
    intro x
    constructor
    · intro hx
      obtain ⟨P, hPm, hP⟩ := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one (ι x)).2 hx
      have hTV : IsIntegral T.V x := by
        refine ⟨P.map φ, hPm.map φ, ?_⟩
        rw [Polynomial.eval₂_map]
        apply ι.injective
        rw [Polynomial.hom_eval₂, hcomp, map_zero]
        exact hP
      exact IsIntegrallyClosed.isIntegral_iff.1 hTV
    · rintro ⟨v, rfl⟩
      obtain ⟨P, hPm, hP⟩ := hφint v
      apply (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1
      refine ⟨P, hPm, ?_⟩
      have h2 := congrArg (ι.comp (algebraMap T.V (FractionRing T.V))) hP
      rw [Polynomial.hom_eval₂, map_zero] at h2
      rw [← hcomp, ← RingHom.comp_assoc]
      exact h2
  let j : T.V →+* OO p := (ι.comp (algebraMap T.V (FractionRing T.V))).codRestrict (OO p) fun v =>
    (mem_OO_iff _).2 ((hint _).2 ⟨v, rfl⟩)
  have hjf : j.comp f = j₀ := by
    ext a
    change ι (algebraMap T.V (FractionRing T.V) (f a)) = ((j₀ a : OO p) : PadicAlgCl p)
    rw [hιf, hj₀]
  refine ⟨T, ι, j, spMap f ≫ y₀, hint, fun v => rfl, ?_, ?_, ?_⟩
  · refine ⟨fun v hv => ?_⟩
    have h1 : ‖ι (algebraMap T.V (FractionRing T.V) v)‖ = 1 :=
      le_antisymm ((hint _).2 ⟨v, rfl⟩) (not_lt.1 fun h => ((not_isUnit_OO_iff (j v)).2 h) hv)
    have h0 : algebraMap T.V (FractionRing T.V) v ≠ 0 := fun h => by
      rw [h, map_zero, norm_zero] at h1
      exact zero_ne_one h1
    obtain ⟨w, hw⟩ := (hint (algebraMap T.V (FractionRing T.V) v)⁻¹).1 (by rw [map_inv₀, norm_inv, h1, inv_one])
    refine IsUnit.of_mul_eq_one w (IsFractionRing.injective T.V (FractionRing T.V) ?_)
    rw [map_mul, map_one, hw, mul_inv_cancel₀ h0]
  · rw [← Category.assoc, GlobalTheory.ArcPointDescent.sp_comp (h := j₀) (fun a => by rw [← hjf]; rfl), hy₀]
  · have e1 : jK T.V ≫ spMap f = spMap fK ≫ jK (integralClosure ℤ_[p] K) :=
      GlobalTheory.ArcPointDescent.sp_sq fun a => (hfK a).symm
    have hyK : yK ≫ i = jK (integralClosure ℤ_[p] K) ≫ y₀ ≫ πY ≫ X₁.π := IsOpenImmersion.lift_fac _ _ _
    rw [hTy, Category.assoc (spMap fK) yK i, hyK]
    simp only [← Category.assoc]
    rw [e1]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointFactorsThroughSiegelModuliTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classicalPoint_factors_through_siegelModuli_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z), IsOpenImmersion i → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i → ∃ (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p) (j : T.V →+* OO p) (ξ : Sp T.V ⟶ Y.Z), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) ∧ (∀ v, (j v : PadicAlgCl p) = ι (algebraMap T.V (FractionRing T.V) v)) ∧ IsLocalHom j ∧ spMap j ≫ ξ = y ∧ jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i := by
  first | exact @GlobalTheory.Poinc.exists_trait_of_classical_point | exact GlobalTheory.Poinc.exists_trait_of_classical_point | (intros; apply GlobalTheory.Poinc.exists_trait_of_classical_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasApproxPoincareSeriesNatMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasApproxPoincareSeriesNatMultiple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem approxAt_mul_of_one_le (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0})
    (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ) (hm : 1 ≤ m) (hd : ApproxAt X₁ φ d) :
    ApproxAt X₁ φ (d * m) := by
  intro p _ z₁ c₀ e
  obtain ⟨f, hf0, hf⟩ := hd p z₁ c₀ e
  have hpow : ∀ c : CTrait X₁ p z₁, ‖c.val (f ^ m)‖ = ‖c.val f‖ ^ m := fun c => by
    rw [CTrait.val_eq_valInt, CTrait.val_eq_valInt, map_pow]
    push_cast
    exact norm_pow _ _
  have hexp : ∀ c : CTrait X₁ p z₁, Real.exp (-(c.sc * (((d * m : ℕ) : ℝ) * φ.evalZ c.T.β))) =
      Real.exp (-(c.sc * (d * φ.evalZ c.T.β))) ^ m := fun c => by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨f ^ m, ?_, fun c => ?_⟩
  · rw [hpow, hf0, hexp]
  · rcases hf c with h1 | ⟨h, hh, h2⟩
    · left
      rw [hpow, hexp]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 m
    · right
      refine ⟨h, hh, ?_⟩
      rw [hpow]
      exact (pow_le_of_le_one (norm_nonneg _) (c.norm_val_le f) (by omega)).trans h2

theorem approxAt_mul : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ), 1 ≤ m → ApproxAt X₁ φ d → ApproxAt X₁ φ (d * m) := approxAt_mul_of_one_le

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasApproxPoincareSeriesNatMultipleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasApproxPoincareSeries_nat_multiple : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (φ : InvFun ℤ) (d m : ℕ), 1 ≤ m → ApproxAt X₁ φ d → ApproxAt X₁ φ (d * m) := by
  first | exact @GlobalTheory.Poinc.approxAt_mul | exact GlobalTheory.Poinc.approxAt_mul | (intros; apply GlobalTheory.Poinc.approxAt_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDescendingDivisorPowerThetaSetup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.DescentPow

theorem exists_cTrait_norm_eqAt {g n : ℕ} {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {i : F.X ⟶ Z} (hi : IsOpenImmersion i)
    {W8 : Matrix (Fin 8) (Fin 8) ℤ} (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (φ : InvFun ℤ) (ι : ℕ) (D : EffCartierData Y.Z)
    (hord : ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i →
      ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a})
    (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z) (hy : Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i)
    (z₁ : X₁.M.Z) (hz : πY (y (cPt p)) = z₁) :
    ∃ c : CTrait X₁ p z₁, c.y = y ≫ πY ∧ ∀ f, EqAt Y D (y (cPt p)) f →
      ‖Y.val (gPt p ≫ y) f‖ = Real.exp (-(c.sc * (ι * φ.evalZ c.T.β))) := by
  obtain ⟨T, ι', j, ξ, hint, hj, hloc, hξ, hT⟩ := GlobalTheory.T.classicalPoint_factors_through_siegelModuli_trait g n F Z i hi W8 X₁ Y πY p y hy
  have hgen : gPt p ≫ y = spMap ι' ≫ jK T.V ≫ ξ := by
    rw [← hξ, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext v
    exact hj v
  refine ⟨⟨y ≫ πY, ?_, T, ι', hint, ?_⟩, rfl, fun f hf => ?_⟩
  · rw [Scheme.Hom.comp_apply]; exact hz
  · rw [← Category.assoc, ← Category.assoc, hgen]
    simp only [Category.assoc]
    rw [hT]
  · obtain ⟨a, ha, hI⟩ := hord T ξ hT
    have hc : ξ (closedPoint T.V) = y (cPt p) := by
      rw [← hξ, Scheme.Hom.comp_apply]
      exact congrArg ξ (IsLocalRing.comap_closedPoint j).symm
    rw [← hc] at hf
    have key := GlobalTheory.T.norm_localEquation_eq_uniformiser_pow_classicalPoint _ _ Y D T.V T.ϖ a ξ p ι' j hint hj hI f hf
    rw [hξ] at key
    have hpos : 0 < ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ := by
      refine norm_pos_iff.2 ?_
      rw [map_ne_zero, Ne, IsFractionRing.to_map_eq_zero_iff]
      exact T.irr.ne_zero
    show _ = Real.exp (-(-Real.log ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (ι * φ.evalZ T.β)))
    rw [key, ← ha, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hpos]

theorem val_comp_of_centre {g n : ℕ} {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    {W8 : Matrix (Fin 8) (Fin 8) ℤ} (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (hHom : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY) {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z) {z : X₁.M.Z}
    (hz : πY (y (cPt q)) = z) {a : X₁.Ω₁} (ha : a ∈ X₁.M.O z) :
    Y.val (gPt q ≫ y) a = X₁.M.val (gPt q ≫ y ≫ πY) a := by
  have hs : πY ((gPt q ≫ y) (closedPoint (PadicAlgCl q))) ⤳ z :=
    hz ▸ (RatModel.gPt_specializes (M := Y) rfl _).map πY.continuous
  have := hHom.val_comp (gPt q ≫ y) (closedPoint (PadicAlgCl q)) (RatModel.O_le_of_specializes hs ha)
  rw [← Category.assoc]
  exact this.symm

theorem exists_idealSheaf_comap_orders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W8 : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W8 → ThetaInt F W8 i → ∀ (X₁ : Setup F W8 i) (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι → IsProjOver X₁.M.s → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z → (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range i) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∃ (ι' : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι' ∧ (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι' * φ.evalZ T.β ∧ idlAlong (J₁.comap πY) ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hθ φ hφ W8 hE hθi X₁ ι Y πY D hι hP hHom hprop hnorm hsupp hord
  have hi : IsOpenImmersion i := hθ.2.2.1
  obtain ⟨d, hd, hA⟩ := GlobalTheory.T.exists_approxPoincareSeries_at_thetaSetup_points g n F W8 Z i X₁ hE hθi hg φ hφ
  obtain ⟨k, hk⟩ : ι ∣ Nat.lcm ι d := Nat.dvd_lcm_left ι d
  obtain ⟨m, hm⟩ : d ∣ Nat.lcm ι d := Nat.dvd_lcm_right ι d
  have hL0 : 0 < Nat.lcm ι d := Nat.lcm_pos hι hd
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; omega
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hm; omega
  have hAL : ApproxAt X₁ φ (Nat.lcm ι d) := hm ▸ GlobalTheory.T.hasApproxPoincareSeries_nat_multiple g n F W8 Z i X₁ φ d m hm0 hA

  have hord' : ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i →
      ∃ a : ℕ, (a : ℝ) = (Nat.lcm ι d : ℕ) * φ.evalZ T.β ∧ idlAlong (D.nsmul k).idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
    intro T ξ h
    obtain ⟨a, ha, hI⟩ := hord T ξ h
    refine ⟨k * a, ?_, ?_⟩
    · rw [hk]; push_cast; rw [ha]; ring
    · rw [GlobalTheory.TorRef.Scale.idlAlong_nsmul, hI, Ideal.span_singleton_pow, ← pow_mul, mul_comm a k]
  have hsub : ∀ y ∈ (D.nsmul k).idealSheaf.support, y ∈ D.idealSheaf.support := by
    intro y hy
    obtain ⟨j, hj⟩ := D.exists_mem y
    rw [(D.nsmul k).mem_support_iff j hj] at hy
    rw [D.mem_support_iff j hj]
    intro h
    apply hy
    change y ∈ Y.Z.basicOpen (D.f j ^ k)
    rw [Scheme.basicOpen_pow _ _ hk0]
    exact h

  let U : Y.Z.Opens := (πY ≫ X₁.π) ⁻¹ᵁ i.opensRange
  have hmemU : ∀ y : Y.Z, y ∈ U ↔ X₁.π (πY y) ∈ Set.range i := fun y => by
    show (πY ≫ X₁.π) y ∈ Set.range i ↔ _
    rw [Scheme.Hom.comp_apply]
  have hU : (U : Set Y.Z).Nonempty := by
    refine ⟨Y.pt (closedPoint X₁.Ω₁), (hmemU _).2 ?_⟩
    have e : Y.pt ≫ πY ≫ X₁.π = spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom ≫ spMap X₁.S.R.val.toRingHom ≫ X₁.u ≫ i := by
      rw [← Category.assoc, hHom, Category.assoc, X₁.comp]
    have e' := congrArg (fun h : Sp X₁.Ω₁ ⟶ Z => h (closedPoint X₁.Ω₁)) e
    simp only [Scheme.Hom.comp_apply] at e'
    exact ⟨_, e'.symm⟩
  have hDU : ∀ x ∈ (D.nsmul k).idealSheaf.support, x ∉ U := fun x hx hxU => hsupp x (hsub x hx) ((hmemU x).1 hxU)
  have hrange : ∀ {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z), Set.range (gPt q ≫ y) ⊆ U →
      Set.range (gPt q ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i := by
    rintro q _ y hy _ ⟨w, rfl⟩
    have := (hmemU _).1 (hy ⟨w, rfl⟩)
    simpa only [← Category.assoc, Scheme.Hom.comp_apply] using this
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_idealSheaf_pullback_eq_divisor_of_approx X₁.o₁ X₁.Ω₁ X₁.M Y πY hHom hprop (@GlobalTheory.IsNormalScheme.pred _ X₁.normal) hnorm U (D.nsmul k) hU hDU (by
    intro z₀ _ x hxz hx
    obtain ⟨p, hp, y₀, hcen⟩ := GlobalTheory.T.exists_classicalPoint_centred_closedPoint_arithmetic _ _ Y x hx U hU
    obtain ⟨c₀, hc₀y, hc₀⟩ := exists_cTrait_norm_eqAt hi X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y₀ (hrange y₀ hcen.2) z₀
      (by rw [hcen.1, hxz])
    refine ⟨p, hp, y₀, hcen, fun e => ?_⟩
    obtain ⟨f, hf0, hfall⟩ := hAL p z₀ c₀ e
    have hfO : X₁.M.stalkHom z₀ f ∈ X₁.M.O z₀ := (X₁.M.stalkEquiv z₀ f).2
    refine ⟨X₁.M.stalkHom z₀ f, hfO, fun f' hf' => ?_, ?_⟩
    · rw [hc₀ f' (hcen.1 ▸ hf'), val_comp_of_centre X₁ Y πY hHom y₀ (by rw [hcen.1, hxz]) hfO, ← hf0]
      show _ = ‖X₁.M.val (gPt p ≫ c₀.y) _‖
      rw [hc₀y]
    · intro q hq y hyz hyU f' hf'
      have hpq : p = q := GlobalTheory.T.prime_eq_of_classicalPoint_same_centre X₁.M.Z p q (y₀ ≫ πY) (y ≫ πY) (by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcen.1, hxz, hyz])
      subst hpq
      obtain ⟨c, hcy, hc⟩ := exists_cTrait_norm_eqAt hi X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y (hrange y hyU) z₀ hyz
      have hcv : ∀ a, c.val a = Y.val (gPt p ≫ y) (X₁.M.stalkHom z₀ a) := fun a => by
        rw [val_comp_of_centre X₁ Y πY hHom y hyz (a := X₁.M.stalkHom z₀ a) (X₁.M.stalkEquiv z₀ a).2]
        show X₁.M.val (gPt p ≫ c.y) _ = _
        rw [hcy]
      rcases hfall c with h1 | ⟨h, hh, h2⟩
      · left
        rw [← hcv, hc f' hf']
        exact h1
      · right
        refine ⟨X₁.M.stalkHom z₀ h, ⟨(X₁.M.stalkEquiv z₀ h).2, ?_⟩, ?_⟩
        · by_contra hne
          push_neg at hne
          apply (IsLocalRing.mem_maximalIdeal _).1 hh
          have hu : IsUnit (X₁.M.stalkEquiv z₀ h) :=
            (RatModel.isUnit_O_iff _).2 ⟨hne.1, hne.2⟩
          exact (MulEquiv.isUnit_map (X₁.M.stalkEquiv z₀)).1 hu
        · rw [← hcv, ← hcv]
          exact h2)
  refine ⟨Nat.lcm ι d, J, hL0, ?_, ?_⟩
  · rw [hJ]
    intro y hy
    exact hsupp y (hsub y hy)
  · rw [hJ]
    exact hord'

end GlobalTheory.Poinc.DescentPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDescendingDivisorPowerThetaSetupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheaf_descending_divisor_power_thetaSetup : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W8 : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W8 → ThetaInt F W8 i → ∀ (X₁ : Setup F W8 i) (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι → IsProjOver X₁.M.s → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z → (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range i) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∃ (ι' : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι' ∧ (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι' * φ.evalZ T.β ∧ idlAlong (J₁.comap πY) ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.Poinc.DescentPow.exists_idealSheaf_comap_orders | exact GlobalTheory.Poinc.DescentPow.exists_idealSheaf_comap_orders | (intros; apply GlobalTheory.Poinc.DescentPow.exists_idealSheaf_comap_orders <;> assumption)
end
