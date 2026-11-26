module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaWeightPartValueDependsTraitLabelsClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartAttainsBoundUniqueShortestVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassSumsOfTermsPrescribedNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsLift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartsOverDividingThetaConstantIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartsOverDividingThetaConstantIntegral
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSumInt

theorem mem_O_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) (z : M.Z) {u : Ω} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) :
    u ∈ M.O z := by
  haveI := RatModel.isIntegrallyClosed_O hn z
  have hint : IsIntegral (M.O z) u :=
    ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2


variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} in
theorem base_mem (X₁ : Setup F W i) (z₁ : X₁.M.Z) : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
  have h : (X₁.S.supI X₁.M z₁).Nonempty := by
    obtain ⟨x, hx⟩ := X₁.div z₁
    exact ⟨x, hx⟩
  rw [GSum.base, dite_eq_left h]
  exact h.some_mem

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (x : D.X.S.Gam) (j : D.X.S.J) (z' : D.X.M.Z), D.q z' = z₁ → D.X.S.ev x j / D.X.S.th (D.lab (GSum.base X₁ z₁)) ∈ D.X.M.O z' := by
  intro g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D z₁ x j z' hz'
  obtain ⟨y, u, k, hk, hu, he⟩ := GlobalTheory.T.theta_system_value_eq_root_mul_theta_constant _ _ D.X.S D.X.ρ x j
  have hd := GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D z₁ _ (base_mem X₁ z₁) z' hz'
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := fun z => by
    haveI := D.X.normal
    exact ⟨D.X.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩
  rw [he, mul_div_assoc]
  exact mul_mem (mem_O_of_pow_eq_one D.X.M hN z' hk hu) (hd.2 y)

end GlobalTheory.Poinc.GSumInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartsOverDividingThetaConstantIntegralStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightParts_over_dividing_thetaConstant_integral : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (x : D.X.S.Gam) (j : D.X.S.J) (z' : D.X.M.Z), D.q z' = z₁ → D.X.S.ev x j / D.X.S.th (D.lab (GSum.base X₁ z₁)) ∈ D.X.M.O z' := by
  first | exact @GlobalTheory.Poinc.GSumInt.main | exact GlobalTheory.Poinc.GSumInt.main | (intros; apply GlobalTheory.Poinc.GSumInt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaClassSumTermsRootsOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperLevelValuesEqClassSumsPrescribedNorms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartUniqueLeastVectorAttainsExp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateValuesShiftByRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateValuesShiftByRootOfUnity
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.USum

theorem uSame_self {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    USame ρ ρ (fun b => b) (RingHom.id Ω) := by
  let f := spMap S.R.val.toRingHom
  let P := ρ.P
  let P₀ : PolAV (Sp Ω) := {
    A := (Over.pullback f).obj P.A
    isAb := TLinPf.isAb_pullback f P.A P.isAb
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (isGrpPullback_pullback P.A f).1 P.smoothDim
    L := P.L.pull (pullback.fst P.A.hom f)
    isLB := pull_isLB P.isLB _
    rigid := GlobalTheory.PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
    sym := GlobalTheory.PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
    ample := by
      letI := P.isAb.proper
      exact GlobalTheory.AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
    ktriv := by
      obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
      exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv }
  refine ⟨P₀, pullback.fst ρ.P.A.hom (spMap S.R.val.toRingHom), pullback.fst ρ.P.A.hom (spMap S.R.val.toRingHom),
    isGrpPullback_pullback _ _, isGrpPullback_pullback _ _, GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB,
    GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB, fun b => ?_⟩
  refine ⟨pullback.lift (spMap S.R.val.toRingHom ≫ (ρ.pt b).left) (𝟙 _) ?_, pullback.lift_fst _ _ _,
    pullback.lift_fst _ _ _⟩
  rw [Category.assoc, Over.w]; simp [f]

theorem sum_ev_shift : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω}
    (ρ : S.Real) (H : AddSubgroup S.Gam) (m : ℕ), S.N = m ^ 2 → ∀ h h' : S.Gam, m • h = m • h' → h' - h ∈ H →
    ∃ ξ : Ω, (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ t ∈ S.perp H,
      ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j := by
  intro o Ω _ _ _ _ S ρ H m hm h h' e hH
  obtain ⟨P₀, a, a', x, hx, hadd⟩ := exists_isGenLab (uSame_self ρ)
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨ξ₁, ⟨k₁, hk₁, hξ₁⟩, hc₁⟩ :=
    GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue ρ ρ (fun b => b) (RingHom.id Ω) P₀ a a' x hx m hm (m • h) x₀ h rfl
  obtain ⟨ξ₂, ⟨k₂, hk₂, hξ₂⟩, hc₂⟩ :=
    GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue ρ ρ (fun b => b) (RingHom.id Ω) P₀ a a' x hx m hm (m • h) x₀ h' e.symm
  have hξ₂0 : ξ₂ ≠ 0 := by
    rintro rfl
    rw [zero_pow hk₂.ne'] at hξ₂
    exact zero_ne_one hξ₂
  refine ⟨ξ₁ * ξ₂⁻¹, ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, ?_⟩, fun t ht => ?_⟩
  · rw [mul_pow, inv_pow, pow_mul, hξ₁, one_pow, mul_comm k₁, pow_mul, hξ₂, one_pow, inv_one, mul_one]
  obtain ⟨v, hv⟩ := TV.ex hx hadd hm t (h := h) (κ := m • h) rfl
  have hv' := hv.transl hx hadd hm (k := h' - h) (by rw [smul_sub, e, sub_self]) (ht _ hH)
  rw [add_sub_cancel] at hv'
  have E₁ := hc₁ t v hv
  have E₂ := hc₂ t v hv'
  simp only [RingHom.id_apply] at E₁ E₂
  have E := E₂.symm.trans E₁
  have hinv : ξ₂ * ξ₂⁻¹ = 1 := mul_inv_cancel₀ hξ₂0
  rw [← sub_eq_zero]
  refine (mul_eq_zero.1 ?_).resolve_left (mul_ne_zero hξ₂0 hx₀)
  linear_combination E - ξ₁ * S.th x₀ * (∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j) * hinv

end GlobalTheory.UPoinc.USum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateValuesShiftByRootOfUnityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_translate_values_shift_by_root_of_unity : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} (ρ : S.Real) (H : AddSubgroup S.Gam) (m : ℕ), S.N = m ^ 2 → ∀ h h' : S.Gam, m • h = m • h' → h' - h ∈ H → ∃ ξ : Ω, (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ t ∈ S.perp H, ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j := by
  first | exact @GlobalTheory.UPoinc.USum.sum_ev_shift | exact GlobalTheory.UPoinc.USum.sum_ev_shift | (intros; apply GlobalTheory.UPoinc.USum.sum_ev_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartUniqueLeastVectorAttainsExp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.GSumEx

theorem sum_proj_shift {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (i₀ : S.J)
    {T : AddSubgroup S.Gam} (c : T →+ ZMod S.N) {h h' : S.Gam} {ξ : Ω}
    (hs : ∀ t ∈ T, ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h j) :
    ∑ j, algebraMap o Ω (S.proj T c j i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.proj T c j i₀) * S.ev h j := by
  classical
  have key : ∀ h₀ : S.Gam, ∑ j, algebraMap o Ω (S.proj T c j i₀) * S.ev h₀ j =
      algebraMap o Ω (Ring.inverse (Nat.card T : o)) * ∑ t : T, algebraMap o Ω (S.ζN ^ (-(c t)).val) *
        ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h₀ j := by
    intro h₀
    rw [ThetaSys.proj, finsum_eq_sum_of_fintype]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, map_mul, map_sum, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => by ring
  have hsum : ∑ t : T, algebraMap o Ω (S.ζN ^ (-(c t)).val) * ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h' j =
      ξ * ∑ t : T, algebraMap o Ω (S.ζN ^ (-(c t)).val) * ∑ j, algebraMap o Ω (S.ρ t j i₀) * S.ev h j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hs t t.2]
    ring
  rw [key h', key h, hsum]
  ring

theorem norm_val_div {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {p : ℕ} [Fact p.Prime]
    (y : Sp (PadicAlgCl p) ⟶ M.Z) {w b ξ : Ω} {k : ℕ} (hk : 0 < k) (hξ : ξ ^ k = 1)
    (hu : ξ * w ∈ M.O (y (closedPoint _))) (hw : w ∈ M.O (y (closedPoint _))) (hb : b ∈ M.O (y (closedPoint _)))
    (hb0 : M.val y b ≠ 0) : ‖M.val y (ξ * w / b)‖ = ‖M.val y w‖ / ‖M.val y b‖ := by
  have hR := RatModel.range_eq_singleton y (closedPoint (PadicAlgCl p))
  have hsp := RatModel.specializes_of_range_eq hR
  have hbu : IsUnit (⟨b, hb⟩ : M.O (y (closedPoint _))) := (RatModel.val_ne_zero_iff hR _).1 hb0
  obtain ⟨hb0', hbinv⟩ := (RatModel.isUnit_O_iff _).1 hbu
  have hk' : (⟨ξ * w, hu⟩ : M.O (y (closedPoint _))) ^ k = (⟨w, hw⟩ : M.O (y (closedPoint _))) ^ k := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow]
    rw [mul_pow, hξ, one_mul]
  have hnorm : ‖M.val y (ξ * w)‖ = ‖M.val y w‖ := by
    have h1 := congrArg (fun x => ‖RatModel.valHomOf y _ hsp x‖) hk'
    simp only [map_pow, norm_pow, RatModel.valHomOf_apply] at h1
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hk.ne').1 h1
  have hdiv : M.val y (ξ * w / b) = M.val y (ξ * w) * M.val y b⁻¹ := by
    rw [div_eq_mul_inv]
    exact RatModel.val_mul hsp hu hbinv
  have hinv : M.val y b * M.val y b⁻¹ = 1 := by
    rw [← RatModel.val_mul hsp hb hbinv, mul_inv_cancel₀ hb0', RatModel.val_one]
  rw [hdiv, norm_mul, hnorm, eq_inv_of_mul_eq_one_right hinv, norm_inv, div_eq_mul_inv]

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem norm_th_eq_delta (X : Setup F W i) {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ X.M.Z) {c₀ : X.Ω₁} {hc R' fg frac hth hev}
    (hR' : R' ≤ X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p)))) (y₀ : R' →+* PadicAlgCl p)
    (hy₀ : ∀ a : R', y₀ a = X.M.val (gPt p ≫ y) a) {x₀ : X.S.Gam} (hx₀ : X.M.Div X.S.th x₀ (y (cPt p))) :
    ‖X.M.val (gPt p ≫ y) (c₀ * X.S.th x₀)‖ = (X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
  classical
  set yg := gPt p ≫ y with hyg
  have hR := RatModel.range_eq_singleton yg (closedPoint (PadicAlgCl p))
  have hsp := RatModel.specializes_of_range_eq hR
  have hgz : yg (closedPoint (PadicAlgCl p)) ⤳ y (cPt p) := RatModel.gPt_specializes (M := X.M) (y := y) rfl (closedPoint (PadicAlgCl p))
  have hle : ∀ x, ‖X.M.val yg (c₀ * X.S.th x)‖ ≤ ‖X.M.val yg (c₀ * X.S.th x₀)‖ := by
    intro x
    have hq : X.S.th x / X.S.th x₀ ∈ X.M.O (y (cPt p)) := hx₀.2 x
    have hq' : X.S.th x / X.S.th x₀ ∈ X.M.O (yg (closedPoint (PadicAlgCl p))) :=
      RatModel.O_le_of_specializes hgz hq
    have hc0 : c₀ * X.S.th x₀ ∈ X.M.O (yg (closedPoint (PadicAlgCl p))) := hR' (hth x₀)
    have heq : c₀ * X.S.th x = (c₀ * X.S.th x₀) * (X.S.th x / X.S.th x₀) := by
      field_simp [hx₀.1]
    rw [heq, RatModel.val_mul hsp hc0 hq', norm_mul]
    have h1 : ‖X.M.val yg (X.S.th x / X.S.th x₀)‖ ≤ 1 := RatModel.norm_val_le_one rfl hq
    exact mul_le_of_le_one_right (norm_nonneg _) h1
  have hv : ∀ x, ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖ = ‖X.M.val yg (c₀ * X.S.th x)‖ := fun x => by rw [hy₀]
  show _ = ⨆ x, ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖
  simp only [hv]
  refine le_antisymm (le_ciSup (f := fun x => ‖X.M.val yg (c₀ * X.S.th x)‖) ⟨‖X.M.val yg (c₀ * X.S.th x₀)‖, ?_⟩ x₀) (ciSup_le hle)
  rintro _ ⟨x, rfl⟩
  exact hle x

theorem exists_lab {X₁ : Setup F W i} {ε₁} (D : Deep X₁ ε₁) {L : Type} [AddCommGroup L] [IsAddTorsionFree L]
    {yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) L} {yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) L} (hC : D.Compat yy₁ yy)
    {x : D.X.S.Gam} (hx : x ∈ yy.ker) (hk : (X₁.S.r * X₁.S.N) • x = 0) : ∃ b ∈ yy₁.ker, D.lab b = x := by
  classical
  have hd1 : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
    have h2 : D.m ∣ D.X.S.N := by rw [D.sq]; exact Dvd.intro_left _ (sq D.m).symm
    exact (D.dvd.trans h2).trans (Dvd.intro_left _ rfl)
  obtain ⟨d, hd⟩ := hd1
  have hpos : 0 < X₁.S.r * X₁.S.N := Nat.pos_of_ne_zero (NeZero.ne _)
  have hdq : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) = d := by
    rw [hd, Nat.mul_div_cancel_left _ hpos]
  have hdpos : d ≠ 0 := by
    rintro rfl
    exact NeZero.ne (D.X.S.r * D.X.S.N) (by rw [hd, mul_zero])

  have hcoord : ∀ j, d ∣ (x j).val := by
    intro j
    have h1 : D.X.S.r * D.X.S.N ∣ X₁.S.r * X₁.S.N * (x j).val := by
      have h0 : ((X₁.S.r * X₁.S.N) • x) j = 0 := by rw [hk]; rfl
      rw [Pi.smul_apply, nsmul_eq_mul, ← ZMod.natCast_zmod_val (x j), ← Nat.cast_mul] at h0
      exact (ZMod.natCast_eq_zero_iff _ _).1 h0
    generalize (x j).val = v at h1 ⊢
    rw [hd] at h1
    exact Nat.dvd_of_mul_dvd_mul_left hpos h1
  let x' : D.X.S.Gam := fun j => (((x j).val / d : ℕ) : ZMod (D.X.S.r * D.X.S.N))
  have hx' : d • x' = x := by
    funext j
    simp only [x', Pi.smul_apply, nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' (hcoord j),
      ZMod.natCast_zmod_val]
  obtain ⟨a, ha⟩ := D.lab_range x'
  rw [hdq, hx'] at ha
  refine ⟨a, ?_, ha⟩
  obtain ⟨μ, hμ⟩ := QuotientAddGroup.mk_surjective (yy₁ a)
  have h1 := hC a μ hμ.symm
  rw [ha, hdq, (AddMonoidHom.mem_ker).1 hx, eq_comm, QuotientAddGroup.eq_zero_iff] at h1
  obtain ⟨ν, hν⟩ := h1
  simp only [nsmulAddMonoidHom_apply] at hν
  rw [AddMonoidHom.mem_ker, ← hμ, QuotientAddGroup.eq_zero_iff]
  refine ⟨ν, ?_⟩
  simp only [nsmulAddMonoidHom_apply]
  rw [hd, mul_comm (X₁.S.r * X₁.S.N) d, mul_nsmul] at hν
  apply eq_of_nsmul_eq_nsmul_of_addCommute hdpos (AddCommute.all _ _)
  rw [← hν]
  exact smul_comm _ _ _

private theorem isAddTorsionFree_of_free_int {X : Type} [AddCommGroup X] [Module.Free ℤ X] : IsAddTorsionFree X := by
  refine ⟨fun n hn a b hab => ?_⟩
  intro h
  let e := (Module.Free.chooseBasis ℤ X).repr
  apply e.injective
  have h1 : n • e a = n • e b := by
    rw [← map_nsmul, ← map_nsmul, h]
  exact nsmul_right_injective hn h1

private theorem rechart_proj {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (c : Ω)
    (hc : c ≠ 0) (R' : Subalgebra o Ω) (fg : R'.FG) (frac : ∀ x : Ω, ∃ a ∈ R', ∃ b ∈ R', x = a / b)
    (hth : ∀ x, c * S.th x ∈ R') (hev : ∀ x i, c * S.ev x i ∈ R') (T : AddSubgroup S.Gam) (cc : T →+ ZMod S.N) :
    (S.rechart c hc R' fg frac hth hev).proj T cc = S.proj T cc := rfl

private theorem mk_eq_mk_symm_of_mk_addEquiv_eq {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (k : ℕ) (e : X ≃+ Y) (χ : X) (ν : Y)
    (h : (QuotientAddGroup.mk (e χ) : ModN k Y) = QuotientAddGroup.mk ν) :
    (QuotientAddGroup.mk χ : ModN k X) = QuotientAddGroup.mk (e.symm ν) := by
  rw [QuotientAddGroup.eq] at h ⊢
  obtain ⟨β, hβ⟩ := h
  refine ⟨e.symm β, ?_⟩
  simp only [nsmulAddMonoidHom_apply] at hβ ⊢
  rw [← map_nsmul, hβ, map_add (f := _), map_neg, AddEquiv.symm_apply_apply]

private theorem ker_eq_of_addEquiv_compat {G X Y : Type} [AddCommGroup G] [AddCommGroup X] [AddCommGroup Y] (k : ℕ)
    (f : G →+ ModN k X) (f' : G →+ ModN k Y) (e : X ≃+ Y)
    (hf : ∀ a χ, f a = QuotientAddGroup.mk χ → f' a = QuotientAddGroup.mk (e χ)) : f.ker = f'.ker := by
  ext a
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
  obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (f a)
  rw [← hχ, hf a χ hχ.symm, QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨β, hβ⟩
    exact ⟨e β, by rw [← hβ, map_nsmul]⟩
  · rintro ⟨β, hβ⟩
    exact ⟨e.symm β, by rw [← map_nsmul, hβ, AddEquiv.symm_apply_apply]⟩

private theorem thetaSys_proj_congr {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {T T' : AddSubgroup S.Gam} (hT : T = T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ (t : S.Gam) (h : t ∈ T) (h' : t ∈ T'), c ⟨t, h⟩ = c' ⟨t, h'⟩) : S.proj T c = S.proj T' c' := by
  subst hT
  congr 1
  ext t
  exact hc t t.2 t.2


set_option maxHeartbeats 1600000 in
theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → χ ≠ ν → qW W c.T.β ν < qW W c.T.β χ) → ∃ κ, ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ = Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  intro g n F W Z i X₁ hg hn hodd himm hE8 hTI hproj ε₁ hdiag D z₁ z₂ hq p hp c yy₁ hlab₁ y h hy yy hlab hC a ν hν hmin
  classical
  have hK1 := (isLab_onto_and_ker g n F W Z i X₁ hg hn hodd himm hE8 hTI hproj ε₁ hdiag p z₁ c yy₁ hlab₁).2
  have hK2 := (isLab_onto_and_ker g n F W Z i D.X hg hn hodd himm hE8 hTI D.proj D.ε D.diag p (y (cPt p))
    (D.lift c y h) yy hlab).2
  have hK2' : yy.ker = D.X.S.HH D.X.M z₂ := by rw [← hy]; exact hK2
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, hi₀, hR', y₀, hy₀, u, l, j, hq', hyy, -⟩ := hlab
  have hint : ∀ b : D.X.o₁, ‖y₀ (algebraMap D.X.o₁ R' b)‖ ≤ 1 := by
    intro b
    rw [hy₀]
    exact RatModel.norm_val_le_one (M := D.X.M) (y := y) rfl ((D.X.M.O _).algebraMap_mem b)
  have hy₀' : ∀ b : R', y₀ b = D.X.M.val (gPt p ≫ y) (b : D.X.Ω₁) := hy₀
  have hL := GlobalTheory.abelianSchemeLaws_all
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta hL.1 hL.2 GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  have hker : l.yy.ker = yy.ker := ker_eq_of_addEquiv_compat _ l.yy yy j hyy

  set ν' := j.symm ν with hν'
  have hla : l.yy a = QuotientAddGroup.mk ν' := by
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy a)
    rw [← hχ]
    exact mk_eq_mk_symm_of_mk_addEquiv_eq _ j χ ν ((hyy a χ hχ.symm).symm.trans hν)
  have hlma : l.yy (D.m • a) = QuotientAddGroup.mk (D.m • ν') := by
    rw [map_nsmul, hla, ← QuotientAddGroup.mk_nsmul]

  have hmin' : ∀ χ : u.D.toPre.X, D.m • χ ≠ 0 → l.q ν' < l.q (ν' + D.m • χ) := by
    intro χ hχ
    rw [hq', hq', map_add (f := _), map_nsmul, hν', AddEquiv.apply_symm_apply]
    have hne : ν + D.m • j χ ≠ ν := by
      intro he
      apply hχ
      apply j.injective
      rw [map_nsmul, map_zero]
      simpa using he
    have hlt := hmin (ν + D.m • j χ) ⟨j χ, rfl⟩ hne
    have hsc : 0 < c.sc := CTrait.scale_pos c
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hlt) hsc
  have hk2 : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  obtain ⟨hh, hhker, hkm, hnorm⟩ := GlobalTheory.T.weightPart_attains_bound_unique_shortest_vector u l hint D.m (X₁.S.r * X₁.S.N) D.sq hk2 D.dvd ν' hmin'
  rw [hker] at hhker

  have := isAddTorsionFree_of_free_int (X := c.T.D.toPre.X)
  obtain ⟨b, hb, hlb⟩ := exists_lab D hC (x := D.m • hh) (yy.ker.nsmul_mem hhker _) hkm
  have hbH : b ∈ X₁.S.HH X₁.M z₁ := by rw [← hK1]; exact hb
  refine ⟨⟨b, hbH⟩, ?_⟩

  have hhH : hh ∈ D.X.S.HH D.X.M z₂ := by rw [← hK2']; exact hhker
  have hex : ∃ h' ∈ D.X.S.HH D.X.M z₂, D.m • h' = D.lab b := ⟨hh, hhH, hlb.symm⟩
  have hlift : GSum.lift D z₂ b = hex.choose := by rw [GSum.lift, dite_eq_left hex]
  obtain ⟨hH'', hm''⟩ := hex.choose_spec
  obtain ⟨ξ, ⟨k', hk'pos, hξ⟩, hshift⟩ := GlobalTheory.T.theta_translate_values_shift_by_root_of_unity D.X.ρ (D.X.S.HH D.X.M z₂) D.m D.sq hh hex.choose
    (by rw [hm'', hlb]) ((D.X.S.HH D.X.M z₂).sub_mem hH'' hhH)
  have hsh := sum_proj_shift (S := D.X.S) D.X.ρ.i₀ (T := D.X.S.TT D.X.M z₂) (GSum.wtChar D _ a) hshift

  have hne : (X₁.S.supI X₁.M z₁).Nonempty := by
    obtain ⟨x, hx⟩ := X₁.div z₁
    exact ⟨x, hx⟩
  have hbase : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
    rw [GSum.base, dite_eq_left hne]
    exact hne.some_mem
  have hqz : D.q (y (cPt p)) = z₁ := by
    rw [← c.cen, ← h]
    rfl
  have hx₀ := GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ hg hn hodd himm hE8 hTI hproj ε₁ hdiag D z₁ (GSum.base X₁ z₁) hbase
    (y (cPt p)) hqz
  have hth0 := norm_th_eq_delta D.X y (hth := hth) (hev := hev) (hc := hc) (fg := fg) (frac := frac) hR' y₀ hy₀ hx₀
  set x₀ := D.lab (GSum.base X₁ z₁) with hx₀def
  set T := D.X.S.TT D.X.M z₂ with hT
  set wc := GSum.wtChar D T a with hwc
  set Sm := ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj T wc j D.X.ρ.i₀) * D.X.S.ev hh j with hSm
  have hmem : ∀ h₀ : D.X.S.Gam, c₀ * ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj T wc j D.X.ρ.i₀) * D.X.S.ev h₀ j =
      ((∑ j, algebraMap D.X.o₁ R' (D.X.S.proj T wc j D.X.ρ.i₀) * (⟨c₀ * D.X.S.ev h₀ j, hev h₀ j⟩ : R') : R') :
        D.X.Ω₁) := by
    intro h₀
    simp only [Finset.mul_sum, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, Subalgebra.coe_algebraMap]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmemO : ∀ h₀ : D.X.S.Gam, c₀ * ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj T wc j D.X.ρ.i₀) * D.X.S.ev h₀ j ∈
      D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := fun h₀ => by
    rw [hmem h₀]
    exact hR' (Subtype.property _)
  have hpart : GSum.part D z₁ z₂ a ⟨b, hbH⟩ = ξ * (c₀ * Sm) / (c₀ * D.X.S.th x₀) := by
    rw [GSum.part]
    try dsimp only
    rw [hlift, hsh, mul_left_comm ξ c₀ Sm, mul_div_mul_left _ _ hc]
  have hw : ξ * (c₀ * Sm) ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := by
    have := hmemO hex.choose
    rw [hsh] at this
    rw [← mul_assoc, mul_comm ξ c₀, mul_assoc]
    exact this
  have hthO : c₀ * D.X.S.th x₀ ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := hR' (hth x₀)
  have hthne : D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x₀) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hth0
    exact hδ.ne' hth0.symm
  have e1 : D.X.S.proj T wc = D.X.S.proj (D.X.S.perp l.yy.ker) (l.wt (D.m • ν')) := by
    refine thetaSys_proj_congr _ (by rw [hT, ThetaSys.TT, hker, hK2']) _ _ fun t ht ht' => ?_
    exact Eq.trans rfl (l.wt_eq (D.m • a) (D.m • ν') hlma ⟨t, ht'⟩).symm
  have hSmn : ‖D.X.M.val (gPt p ≫ y) (c₀ * Sm)‖ = (D.X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ * Real.exp (-l.q ν') := by
    have e1' : D.X.S.proj T wc =
        (D.X.S.rechart c₀ hc R' fg frac hth hev).proj ((D.X.S.rechart c₀ hc R' fg frac hth hev).perp l.yy.ker)
          (l.wt (D.m • ν')) := by
      rw [rechart_proj]
      exact e1
    rw [← e1', hi₀] at hnorm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hnorm, hSm, hmem hh, ← hy₀', map_sum]
    simp only [map_mul]
  rw [hpart, norm_val_div (M := D.X.M) (gPt p ≫ y) hk'pos hξ hw (hmemO hh) hthO hthne, hSmn, hth0,
    mul_div_cancel_left₀ _ hδ.ne', hq', hν', AddEquiv.apply_symm_apply]
  try rfl

end GlobalTheory.Poinc.GSumEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartUniqueLeastVectorAttainsExpStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPart_unique_least_vector_attains_exp : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → χ ≠ ν → qW W c.T.β ν < qW W c.T.β χ) → ∃ κ, ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ = Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  first | exact @GlobalTheory.Poinc.GSumEx.main | exact GlobalTheory.Poinc.GSumEx.main | (intros; apply GlobalTheory.Poinc.GSumEx.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartLeastVectorNormLeExp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartLeastVectorNormLeExp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.PartLe

theorem ubound {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab)
    (hint : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) {m : ℕ} (hm : S.N = m ^ 2) {a : S.Gam} {χ : u.D.toPre.X}
    (ha : l.yy a = QuotientAddGroup.mk χ) (hmin : ∀ v, l.q χ ≤ l.q (χ + m • v)) {T : AddSubgroup S.Gam}
    (hT : T = S.perp l.yy.ker) (w : T →+ ZMod S.N)
    (hw : ∀ t : T, w t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ (t : S.Gam) (m • a)))
    {h : S.Gam} (hh : h ∈ l.yy.ker) (i : S.J) :
    ‖y₀ (∑ j, algebraMap o S.R (S.proj T w j i) * ⟨S.ev h j, S.ev_mem h j⟩)‖ ≤ S.delta y₀ * Real.exp (-l.q χ) := by
  subst hT
  have hsc : ∀ x, l.q (m • x) = (m : ℝ) ^ 2 * l.q x := fun x => by
    rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
    push_cast
    ring
  have hm0 : (m : ℝ) ^ 2 ≠ 0 := by
    have := GlobalTheory.ZH.GlobalGen.N_pos S
    rw [hm] at this
    exact_mod_cast this.ne'
  have hlab : l.yy (m • a) = QuotientAddGroup.mk (m • χ) := by
    rw [map_nsmul, ha, QuotientAddGroup.mk_nsmul]
  have hwt : w = l.wt (m • χ) := AddMonoidHom.ext fun t => (hw t).trans (l.wt_eq _ _ hlab t).symm
  have key := GlobalTheory.ZH.WeightBound.main GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed o Ω S ρ p
    y₀ u l hint (m • χ) (fun v => by
      have e : m • χ + S.N • v = m • (χ + m • v) := by rw [hm, smul_add, smul_smul, sq]
      rw [e, hsc, hsc]
      exact mul_le_mul_of_nonneg_left (hmin v) (sq_nonneg _)) h hh i
  have e : l.q (m • χ) / S.N = l.q χ := by
    rw [hsc, hm, Nat.cast_pow, mul_div_cancel_left₀ _ hm0]
  rw [e, ← hwt] at key
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, map_mul] using key


set_option maxHeartbeats 1600000 in
theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → qW W c.T.β ν ≤ qW W c.T.β χ) → ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ ≤ Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  intro g n F W Z i X₁ h1 h2 h3 h4 h5 h6 h7 ε₁ h8 D z₁ z₂ hz p _ c yy₁ _ y h hy yy hl _ a ν κ hν hmin
  subst hy
  obtain ⟨-, hHH⟩ := GlobalTheory.Poinc.isLab_onto_and_ker g n F W Z i D.X h1 h2 h3 h4 h5 h6 D.proj D.ε D.diag p _ (D.lift c y h) yy hl
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, hR', y₀, hy₀, u, l, j, hq, hyy, -⟩ := hl
  have hlift : ∀ (b : D.X.S.Gam) μ, yy b = QuotientAddGroup.mk μ → l.yy b = QuotientAddGroup.mk (j.symm μ) := by
    intro b μ hb
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (l.yy b)
    have e1 := hyy b χ hχ.symm
    rw [hb, QuotientAddGroup.eq] at e1
    obtain ⟨w, hw⟩ := e1
    rw [← hχ, eq_comm, QuotientAddGroup.eq]
    refine ⟨j.symm w, ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hw ⊢
    rw [← map_nsmul, hw, map_add (f := _), map_neg, j.symm_apply_apply]
  have hker : yy.ker = l.yy.ker := by
    ext b
    simp only [AddMonoidHom.mem_ker]
    constructor
    · intro hb
      have := hlift b 0 hb
      rwa [map_zero] at this
    · intro hb
      have := hyy b 0 hb
      rwa [map_zero] at this
  have hint : ∀ a : D.X.o₁, ‖y₀ (algebraMap D.X.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one rfl ((D.X.M.O _).algebraMap_mem a)
  have hδ0 := (GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u l hint).1
  have hb : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
    have hne : (X₁.S.supI X₁.M z₁).Nonempty := X₁.div z₁
    rw [GSum.base, dite_eq_left hne]
    exact hne.some_mem
  have hx₀ := GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ h1 h2 h3 h4 h5 h6 h7 ε₁ h8 D z₁ _ hb _ hz
  have hmem : GSum.lift D (y (cPt p)) (κ : X₁.S.Gam) ∈ l.yy.ker := by
    rw [← hker, hHH, GSum.lift]
    split_ifs with hex
    · exact hex.choose_spec.1
    · exact zero_mem _
  have key := ubound (S := D.X.S.rechart c₀ hc R' fg frac hth hev) u l hint (m := D.m) D.sq (hlift a ν hν) (fun v => by
      rw [hq, hq, map_add (f := _), map_nsmul, j.apply_symm_apply]
      exact mul_le_mul_of_nonneg_left (Int.cast_le.2 (hmin _ ⟨j v, rfl⟩)) c.scale_pos.le)
    (T := D.X.S.TT D.X.M (y (cPt p))) (by rw [← hker, hHH]; rfl) (GSum.wtChar D _ a) (fun _ => rfl) hmem D.X.ρ.i₀
  rw [hq, j.apply_symm_apply, hy₀] at key
  unfold GSum.part
  generalize D.lab (GSum.base X₁ z₁) = x₀ at hx₀
  set Sg := ∑ j, algebraMap D.X.o₁ D.X.Ω₁ (D.X.S.proj (D.X.S.TT D.X.M (y (cPt p))) (GSum.wtChar D _ a) j D.X.ρ.i₀) *
      D.X.S.ev (GSum.lift D (y (cPt p)) (κ : X₁.S.Gam)) j with hSg
  have hsp : ∀ w, (gPt p ≫ y) w ⤳ (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hgz : (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ y (cPt p) := RatModel.gPt_specializes rfl _
  have hle : (D.X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ ≤ ‖D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x₀)‖ := by
    refine ciSup_le fun x => (congrArg norm (hy₀ _)).trans_le ?_
    show ‖D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x)‖ ≤ _
    have e : c₀ * D.X.S.th x = D.X.S.th x / D.X.S.th x₀ * (c₀ * D.X.S.th x₀) := by
      have := hx₀.1
      field_simp
    rw [e, RatModel.val_mul hsp (RatModel.O_le_of_specializes hgz (hx₀.2 x)) (hR' (hth _)), norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one rfl (hx₀.2 x))
  have hpos := hδ0.trans_le hle
  have hSR : c₀ * Sg ∈ R' := by
    rw [hSg, Finset.mul_sum]
    refine sum_mem fun k _ => ?_
    rw [mul_left_comm]
    exact mul_mem (R'.algebraMap_mem _) (hev _ _)
  have key' : ‖D.X.M.val (gPt p ≫ y) (c₀ * Sg)‖ ≤ ‖D.X.M.val (gPt p ≫ y) (c₀ * D.X.S.th x₀)‖ *
      Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
    refine le_trans (le_of_eq ?_) (key.trans (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le))
    congr 2
    rw [hSg, Finset.mul_sum, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _
  have hO : Sg / D.X.S.th x₀ ∈ D.X.M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) := by
    obtain ⟨v, hv⟩ := ((RatModel.val_ne_zero_iff (RatModel.range_eq_singleton (gPt p ≫ y) _)
      ⟨c₀ * D.X.S.th x₀, hR' (hth x₀)⟩).1 (norm_pos_iff.1 hpos)).exists_right_inv
    have hv' : c₀ * D.X.S.th x₀ * (v : D.X.Ω₁) = 1 := congrArg Subtype.val hv
    have e : Sg / D.X.S.th x₀ = c₀ * Sg * v := by
      rw [div_eq_iff hx₀.1]
      linear_combination (-Sg) * hv'
    rw [e]
    exact mul_mem (hR' hSR) v.2
  have e : c₀ * Sg = Sg / D.X.S.th x₀ * (c₀ * D.X.S.th x₀) := by
    have := hx₀.1
    field_simp
  rw [e, RatModel.val_mul hsp hO (hR' (hth _)), norm_mul, mul_comm] at key'
  exact le_of_mul_le_mul_left key' hpos

end GlobalTheory.Poinc.PartLe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartLeastVectorNormLeExpStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPart_least_vector_norm_le_exp : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → (∀ χ, CongMod D.m χ ν → qW W c.T.β ν ≤ qW W c.T.β χ) → ‖D.X.M.val (gPt p ≫ y) (GSum.part D z₁ z₂ a κ)‖ ≤ Real.exp (-(c.sc * (qW W c.T.β ν : ℤ))) := by
  first | exact @GlobalTheory.Poinc.PartLe.main | exact GlobalTheory.Poinc.PartLe.main | (intros; apply GlobalTheory.Poinc.PartLe.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperLevelValuesEqClassSumsPrescribedNorms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GSumCls

theorem congMod_iff {X J : Type} [AddCommGroup X] (m : ℕ) (u v : J → X) :
    CongMod m u v ↔ ∀ i, CongMod m (u i) (v i) := by
  constructor
  · rintro ⟨w, hw⟩ i
    exact ⟨w i, by rw [hw]; rfl⟩
  · intro h
    choose w hw using h
    exact ⟨w, funext fun i => by rw [hw i]; rfl⟩

theorem norm_val_root_mul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {z : M.Z} (hy : y (cPt p) = z) {u x : Ω} {k : ℕ} (hk : 0 < k)
    (hu : u ^ k = 1) (hx : x ∈ M.O z) : ‖M.val (gPt p ≫ y) (u * x)‖ = ‖M.val (gPt p ≫ y) x‖ := by
  haveI := RatModel.isIntegrallyClosed_O hM z
  have hint : IsIntegral (M.O z) u := ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hmem : u ∈ M.O z := hv ▸ v.2
  have hs := RatModel.gPt_specializes hy
  have h1 : (⟨u, hmem⟩ : M.O z) ^ k = 1 := Subtype.ext hu
  have h2 : M.val (gPt p ≫ y) u ^ k = 1 := by
    have := congrArg (RatModel.valHomOf (gPt p ≫ y) z hs) h1
    rwa [map_pow, map_one] at this
  have h3 : ‖M.val (gPt p ≫ y) u‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 (by rw [← norm_pow, h2, norm_one])
  rw [RatModel.val_mul hs hmem hx, norm_mul, h3, one_mul]

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem onto_of_isLab {X : Setup F W i} {ε} {p : ℕ} [Fact p.Prime] {z : X.M.Z} {c : CTrait X p z} {yy}
    (h : IsLab X ε c yy) (ν : Fin 8 → c.T.D.toPre.X) : ∃ a, yy a = QuotientAddGroup.mk ν := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, -, hyy, -⟩ := h
  obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (j.symm ν))
  exact ⟨a, by simpa using hyy a _ ha⟩

theorem tendsto_of_isLab {X : Setup F W i} {ε} {p : ℕ} [Fact p.Prime] {z : X.M.Z} {c : CTrait X p z} {yy}
    (h : IsLab X ε c yy) :
    Filter.Tendsto (fun ν : Fin 8 → c.T.D.toPre.X => c.sc * (qW W c.T.β ν : ℤ)) Filter.cofinite Filter.atTop := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, hq, -⟩ := h
  refine (l.pos.comp j.symm.injective.tendsto_cofinite).congr fun ν => ?_
  rw [Function.comp_apply, hq, AddEquiv.apply_symm_apply]

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p _ z₁ z₂ hz
  obtain ⟨U, hU, hgeq⟩ := GlobalTheory.T.thetaWeightPart_value_depends_trait_labels_class g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ z₂ hz
  refine ⟨U, hU, fun c yy₁ hlab => ?_⟩
  have hs : ∀ χ : Fin 8 → c.T.D.toPre.X, ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ ^ (qW W c.T.β χ).toNat =
      Real.exp (-(c.sc * (qW W c.T.β χ : ℤ))) := fun χ => by
    have h0 := qW_nonneg_of_posW W X₁.posW c.T.β c.T.symm (Basic₂.trait_nonneg c.T) χ
    rw [← c.exp_neg_sc_mul, ← Int.cast_natCast (R := ℝ), Int.toNat_of_nonneg h0]
  by_cases hex : ∃ y : Sp (OO p) ⟶ D.X.M.Z, y ≫ D.q = c.y ∧ y (cPt p) = z₂
  swap
  · refine ⟨fun μ _ => c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ^ (qW W c.T.β μ).toNat,
      fun μ _ => by rw [norm_pow, hs], fun μ => ⟨0, by rw [norm_pow, hs]⟩, fun y h hy => (hex ⟨y, h, hy⟩).elim⟩
  obtain ⟨y₀, h₀, hy₀⟩ := hex
  obtain ⟨yy₀, hlab₀, hcomp₀⟩ :=
    GLift.labels_lift g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c yy₁ hlab y₀ h₀
  choose a ha using onto_of_isLab hlab₀
  have hpart : ∀ b κ, GSum.part D z₁ z₂ b κ ∈ D.X.M.O z₂ := fun b κ => by
    rw [GSum.part, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_mem ((D.X.M.O z₂).algebraMap_mem _)
      (GlobalTheory.T.weightParts_over_dividing_thetaConstant_integral g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ _ j z₂ hz)
  have hnorm : ∀ b κ, ‖D.X.M.val (gPt p ≫ y₀) (U κ * GSum.part D z₁ z₂ b κ)‖ =
      ‖D.X.M.val (gPt p ≫ y₀) (GSum.part D z₁ z₂ b κ)‖ := fun b κ => by
    obtain ⟨k, hk, hu⟩ := hU κ
    exact norm_val_root_mul (haveI := D.X.normal; GlobalTheory.IsNormalScheme.pred _) hy₀ hk hu (hpart b κ)
  have hsc := c.scale_pos
  obtain ⟨t, ht1, ht2, ht3⟩ := GlobalTheory.T.lattice_class_sums_of_terms_prescribed_norms p (Fin 8 → c.T.D.toPre.X) (X₁.S.HH X₁.M z₁) D.m
    (fun ν => c.sc * (qW W c.T.β ν : ℤ)) _ _ (tendsto_of_isLab hlab) hs
    (fun ν κ => D.X.M.val (gPt p ≫ y₀) (U κ * GSum.part D z₁ z₂ (a ν) κ))
    (fun ν ν' κ h => hgeq p c yy₁ hlab y₀ h₀ hy₀ yy₀ hlab₀ hcomp₀ y₀ h₀ hy₀ yy₀ hlab₀ hcomp₀ _ _ ν ν' κ (ha ν) (ha ν') h)
    (fun ν κ h => by
      rw [hnorm]
      refine GlobalTheory.T.weightPart_least_vector_norm_le_exp g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ z₂ hz p c yy₁ hlab y₀ h₀ hy₀ yy₀
        hlab₀ hcomp₀ _ ν κ (ha ν) fun χ hχ => ?_
      exact_mod_cast le_of_mul_le_mul_left (h χ hχ) hsc)
    (fun ν h => by
      simp only [hnorm]
      refine GlobalTheory.T.weightPart_unique_least_vector_attains_exp g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ z₂ hz p c yy₁ hlab y₀ h₀ hy₀ yy₀
        hlab₀ hcomp₀ _ ν (ha ν) fun χ hχ hne => ?_
      exact_mod_cast lt_of_mul_lt_mul_left (h χ hχ hne) hsc.le)
  refine ⟨t, ht1, ht2, fun y h hy yy hl hc b ν κ hb δ hδ => ?_⟩
  obtain ⟨S₀, hS₀⟩ := ht3 ν κ δ hδ
  refine ⟨S₀, fun S h1 h2 => ?_⟩
  rw [hgeq p c yy₁ hlab y h hy yy hl hc y₀ h₀ hy₀ yy₀ hlab₀ hcomp₀ b (a ν) ν ν κ hb (ha ν) ⟨0, by simp⟩]
  exact hS₀ S (fun χ hχ => (congMod_iff _ _ _).2 (h1 χ hχ)) fun χ hχ hcg => h2 χ hχ ((congMod_iff _ _ _).1 hcg)

end GlobalTheory.Poinc.GSumCls
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperLevelValuesEqClassSumsPrescribedNormsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deeperLevelValues_eq_classSums_prescribedNorms : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ := by
  first | exact @GlobalTheory.Poinc.GSumCls.main | exact GlobalTheory.Poinc.GSumCls.main | (intros; apply GlobalTheory.Poinc.GSumCls.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaClassSumTermsRootsOfUnity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.GSum.terms_and_sums : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ :=
  GlobalTheory.T.deeperLevelValues_eq_classSums_prescribedNorms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaClassSumTermsRootsOfUnityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaClassSum_terms_rootsOfUnity : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ) := by
  first | exact @GlobalTheory.Poinc.GSum.terms_and_sums | exact GlobalTheory.Poinc.GSum.terms_and_sums | (intros; apply GlobalTheory.Poinc.GSum.terms_and_sums <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

theorem mem_O_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) (z : M.Z) {u : Ω} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) : u ∈ M.O z := by
  haveI := RatModel.isIntegrallyClosed_O hn z
  have hint : IsIntegral (M.O z) u :=
    ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ (f : D.X.S.Gam → X₁.S.HH X₁.M z₁ → D.X.Ω₁) (t : ∀ (c : CTrait X₁ p z₁) (_ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p), (∀ a κ (z' : D.X.M.Z), D.q z' = z₁ → f a κ ∈ D.X.M.O z') ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → (∀ μ κ, ‖t c yy₁ μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t c yy₁ μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t c yy₁ μ κ‖ ≤ δ := by
  intro g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D p _ z₁ z₂ hz
  obtain ⟨U, hU, hB⟩ := GlobalTheory.T.exists_thetaClassSum_terms_rootsOfUnity g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D p z₁ z₂ hz
  classical
  refine ⟨fun a κ => U κ * part D z₁ z₂ a κ,
    fun c yy₁ => if h : IsLab X₁ ε₁ c yy₁ then (hB c yy₁ h).choose else fun _ _ => 0, ?_, ?_⟩
  · intro a κ z' hz'
    obtain ⟨k, hk, hUk⟩ := hU κ
    have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := fun z => by
      haveI := D.X.normal
      exact ⟨D.X.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩
    refine mul_mem (mem_O_of_pow_eq_one D.X.M hN z' hk hUk) ?_
    rw [part, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) (GlobalTheory.T.weightParts_over_dividing_thetaConstant_integral g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D z₁ _ j z' hz')
  · intro c yy₁ hl
    simp only [dif_pos hl]
    exact (hB c yy₁ hl).choose_spec

end GlobalTheory.Poinc.GSum
