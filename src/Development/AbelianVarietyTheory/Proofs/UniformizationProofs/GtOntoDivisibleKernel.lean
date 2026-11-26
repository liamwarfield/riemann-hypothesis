module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT
open GlobalTheory.TorusExt

theorem isTor_iff {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (t : Multiplicative D.X →* Fˣ) (g : GtPtF D F) :
    IsTor t g ↔ IsTorusPtF g fun χ => t (Multiplicative.ofAdd χ) := by
  rw [isTorusPtF_iff_val]
  refine and_congr Iff.rfl (forall_congr' fun χ => forall_congr' fun y => forall_congr' fun J => forall_congr' fun _ => ?_)
  have e : ∀ x : F, cst (R := R) F y x = stalkConst (F := F) y x := fun x =>
    gs_eq (𝟙 _) y ⊤ trivial _
  rw [e]

theorem gt_onto_divisible_kernel : LL → AllD fun {R} _ _ {I} D F _ _ => (∀ b : TF (R := R) F ⟶ D.toPre.P.A, ∃ g : GtPtF D.toPre F, g.b = b) ∧ (∀ n, 1 ≤ n → ∀ g : GtPtF D.toPre F, ∃ g', GtPtF.IsNsmul n g' g) ∧ (∀ t, ∃! g : GtPtF D.toPre F, IsTor t g) ∧ (∀ g : GtPtF D.toPre F, g.b = 1 → ∃! t, IsTor t g) ∧ ∀ t t' (g g' g'' : GtPtF D.toPre F), IsTor t g → IsTor t' g' → (g.IsAdd g' g'' ↔ IsTor (t * t') g'') := by
  intro hL R _ _ _ I hA D F _ _ _
  refine ⟨exists_lift, fun n hn g => ?_, fun t => ?_, fun g hb => ?_, fun t t' g g' g'' h h' => ?_⟩
  · letI := gtGroup D.toPre F
    exact (exists_nsmul_eq hL.1.mulN (Or.inl hA.1) (by omega) g).imp fun _ e => (isNsmul_iff_eq _ _ _).2 e.symm
  · exact ⟨_, (isTor_iff _ _).2 (isTorusPtF_torusPt t), fun g h => (isTorusPtF_iff_eq g t).1 ((isTor_iff _ _).1 h)⟩
  · obtain ⟨t, ht⟩ := exists_isTorusPtF_of_b hb
    refine ⟨t, (isTor_iff _ _).2 ht, fun t' ht' => MonoidHom.ext fun χ => Units.ext ?_⟩
    exact congrFun (((isTor_iff _ _).1 ht').fun_unique ht) χ.toAdd
  · letI := gtGroup D.toPre F
    have a := ((isTor_iff _ _).1 h).add ((isTor_iff _ _).1 h')
    rw [isTor_iff]
    exact (isAdd_iff_eq _ _ _).trans ⟨fun e => e ▸ a, fun e => e.unique a⟩

end GlobalTheory.UT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicBaseEmbedsValuationAlgebraicClosure
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

section RationalValues

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem le_iff_of_pow_eq_zpow {t a b : Γ} (h0 : 0 < t) (h1 : t < 1) {n n' : ℕ} (hn : 0 < n)
    (hn' : 0 < n') {m m' : ℤ} (ha : a ^ n = t ^ m) (hb : b ^ n' = t ^ m') :
    b ≤ a ↔ (m : ℚ) / n ≤ (m' : ℚ) / n' := by
  have e1 : a ^ (n * n') = t ^ (m * n') := by rw [pow_mul, ha, zpow_mul, zpow_natCast]
  have e2 : b ^ (n * n') = t ^ (m' * n) := by rw [mul_comm n, pow_mul, hb, zpow_mul, zpow_natCast]
  rw [← pow_le_pow_iff_left₀ zero_le' zero_le' (Nat.mul_pos hn hn').ne', e1, e2,
    zpow_le_zpow_iff_right_of_lt_one₀ h0 h1, div_le_div_iff₀ (by exact_mod_cast hn)
      (by exact_mod_cast hn')]
  norm_cast

theorem exists_ratAddValuation_of_pow_eq_zpow {F : Type*} [Field F] (w : Valuation F Γ) {t : Γ}
    (h0 : 0 < t) (h1 : t < 1) (h : ∀ x : F, x ≠ 0 → ∃ (n : ℕ) (m : ℤ), 0 < n ∧ w x ^ n = t ^ m) :
    ∃ v : AddValuation F (WithTop ℚ), ∀ (x : F) (m : ℤ), w x = t ^ m →
      v x = ((m : ℚ) : WithTop ℚ) := by
  classical
  choose! n m hn hnm using h
  let f : F → WithTop ℚ := fun x => if x = 0 then ⊤ else (((m x : ℚ) / n x : ℚ) : WithTop ℚ)
  have f0 : f 0 = ⊤ := if_pos rfl
  have key : ∀ (x : F) (a : ℕ) (b : ℤ), 0 < a → w x ^ a = t ^ b →
      f x = (((b : ℚ) / a : ℚ) : WithTop ℚ) := by
    intro x a b ha hab
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_pow ha.ne'] at hab
      exact (zpow_pos h0 b).ne hab
    simp only [f, if_neg hx, WithTop.coe_inj]
    exact le_antisymm ((le_iff_of_pow_eq_zpow h0 h1 (hn x hx) ha (hnm x hx) hab).1 le_rfl)
      ((le_iff_of_pow_eq_zpow h0 h1 ha (hn x hx) hab (hnm x hx)).1 le_rfl)
  have mono : ∀ x y : F, w y ≤ w x → f x ≤ f y := by
    intro x y hxy
    by_cases hy : y = 0
    · rw [hy, f0]; exact le_top
    have hx : x ≠ 0 := by
      rintro rfl
      rw [map_zero, le_zero_iff, Valuation.zero_iff] at hxy
      exact hy hxy
    simp only [f, if_neg hx, if_neg hy, WithTop.coe_le_coe]
    exact (le_iff_of_pow_eq_zpow h0 h1 (hn x hx) (hn y hy) (hnm x hx) (hnm y hy)).1 hxy
  refine ⟨AddValuation.of f f0 ?_ ?_ ?_, fun x b hb => ?_⟩
  · rw [key 1 1 0 one_pos (by simp)]
    simp
  · intro x y
    rcases le_max_iff.1 (w.map_add x y) with h | h
    · exact min_le_of_left_le (mono _ _ h)
    · exact min_le_of_right_le (mono _ _ h)
  · intro x y
    by_cases hx : x = 0
    · rw [hx, MulZeroClass.zero_mul, f0, top_add]
    by_cases hy : y = 0
    · rw [hy, MulZeroClass.mul_zero, f0, add_top]
    have hx' := hn x hx
    have hy' := hn y hy
    rw [key (x * y) (n x * n y) (m x * n y + m y * n x) (Nat.mul_pos hx' hy') (by
      rw [map_mul, mul_pow, pow_mul, mul_comm (n x), pow_mul, hnm x hx, hnm y hy,
        zpow_add₀ h0.ne', zpow_mul, zpow_mul, zpow_natCast, zpow_natCast])]
    simp only [f, if_neg hx, if_neg hy, ← WithTop.coe_add, WithTop.coe_inj]
    have : (n x : ℚ) ≠ 0 := by exact_mod_cast hx'.ne'
    have : (n y : ℚ) ≠ 0 := by exact_mod_cast hy'.ne'
    push_cast
    field_simp
  · change f x = _
    rw [key x 1 b one_pos (by simpa using hb)]
    simp

theorem exists_valuation_pow_eq_of_isAlgebraic {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Valuation F Γ) {x : F} (hx : IsAlgebraic K x) (hx0 : x ≠ 0) :
    ∃ (n : ℕ) (c : K), 0 < n ∧ c ≠ 0 ∧ w x ^ n = w (algebraMap K F c) := by
  classical
  obtain ⟨p, hp0, hp⟩ := hx
  let g : ℕ → F := fun i => algebraMap K F (p.coeff i) * x ^ i
  have hsum : ∑ i ∈ p.support, g i = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hp
    exact hp
  have hc : ∀ i ∈ p.support, w (algebraMap K F (p.coeff i)) ≠ 0 := fun i hi => by
    simpa using hi
  have hw : w x ≠ 0 := by simpa using hx0
  have aux : ∀ i ∈ p.support, ∀ j ∈ p.support, j < i → w (g i) = w (g j) →
      ∃ (n : ℕ) (c : K), 0 < n ∧ c ≠ 0 ∧ w x ^ n = w (algebraMap K F c) := by
    intro i hi j hj hji e
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hji
    refine ⟨d + 1, p.coeff j / p.coeff (j + d + 1), Nat.succ_pos d,
      div_ne_zero (Polynomial.mem_support_iff.1 hj) (Polynomial.mem_support_iff.1 hi), ?_⟩
    simp only [g, map_mul, map_pow] at e
    rw [map_div₀, map_div₀, eq_div_iff (hc _ hi)]
    apply mul_right_cancel₀ (pow_ne_zero j hw)
    rw [← e, _root_.add_assoc j, pow_add (w x) j]
    ac_rfl
  obtain ⟨i, hi, hmax⟩ := p.support.exists_max_image (fun i => w (g i))
    (Polynomial.support_nonempty.2 hp0)
  by_contra hne
  have hlt : ∀ j ∈ p.support \ {i}, w (g j) < w (g i) := by
    intro j hj
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    refine lt_of_le_of_ne (hmax j hj.1) fun e => hne ?_
    rcases lt_or_gt_of_ne hj.2 with h | h
    · exact aux i hi j hj.1 h e.symm
    · exact aux j hj.1 i hi h e
  have hgi : w (g i) ≠ 0 := by
    simp only [g, map_mul, map_pow]
    exact mul_ne_zero (hc i hi) (pow_ne_zero i hw)
  have := w.map_sum_eq_of_lt hi hlt
  rw [hsum, map_zero] at this
  exact hgi this.symm

end RationalValues

theorem exists_valOver_of_isAlgebraic {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) (F : Type) [Field F]
    [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] :
    ∃ v : AddValuation F (WithTop ℚ), ValOver ϖ F v := by
  let K := FractionRing V
  let f : V →+* F := (algebraMap K F).comp (algebraMap V K)
  have hf : Function.Injective f := (algebraMap K F).injective.comp (IsFractionRing.injective V K)
  obtain ⟨W, hW⟩ := (LocalSubring.range f).exists_le_valuationSubring
  obtain ⟨hW1, hW2⟩ := (localSubring_range_le_valuationSubring_iff f W).1 hW
  let w := W.valuation
  have h0 : 0 < w (f ϖ) := by
    rw [Valuation.pos_iff]
    exact (map_ne_zero_iff _ hf).2 hϖ.ne_zero
  have h1 : w (f ϖ) < 1 := (W.mem_nonunits_iff).1 (hW2 ϖ hϖ.not_isUnit)
  have hu : ∀ u : Vˣ, w (f u) = 1 := fun u =>
    W.valuation_unit (Units.map (f.codRestrict W hW1 : V →* W) u)
  have hval : ∀ (c : K) (n : ℤ), HasVal ϖ c n → w (algebraMap K F c) = w (f ϖ) ^ n := by
    rintro c n ⟨u, rfl⟩
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀]
    change w (f ϖ) ^ n * w (f u) = _
    rw [hu, _root_.mul_one]
  obtain ⟨v, hv⟩ := exists_ratAddValuation_of_pow_eq_zpow w h0 h1 fun x hx => by
    obtain ⟨n, c, hn, hc, e⟩ := exists_valuation_pow_eq_of_isAlgebraic (K := K) w
      (Algebra.IsAlgebraic.isAlgebraic x) hx
    obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hc
    exact ⟨n, m, hn, e.trans (hval c m hm)⟩
  exact ⟨v, fun c n hc => hv _ n (hval c n hc)⟩

theorem exists_complete_discreteValuationRing_map_le {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊤) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V),
      IsAdicComplete (maximalIdeal V) V ∧ Function.Injective φ ∧ I.map φ ≤ maximalIdeal V := by
  by_cases h : I = ⊥
  · let K := FractionRing R
    refine ⟨PowerSeries K, inferInstance, inferInstance, inferInstance,
      (PowerSeries.C (R := K)).comp (algebraMap R K), ?_,
      PowerSeries.C_injective.comp (IsFractionRing.injective R K), by simp [h]⟩
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  · obtain ⟨p, hp, hIp⟩ := I.exists_le_maximal hI
    have := hp.isPrime
    obtain ⟨O, _, _, _, hO, φ, h1, h2⟩ := exists_complete_discreteValuationRing_of_prime_lt
      (⊥ : Ideal R) p (lt_of_lt_of_le (bot_lt_iff_ne_bot.2 h) hIp)
    exact ⟨O, inferInstance, inferInstance, inferInstance, φ, hO,
      (RingHom.injective_iff_ker_eq_bot φ).2 h1, Ideal.map_le_iff_le_comap.2 (h2 ▸ hIp)⟩

theorem adic_base_embeds_valuation_algebraic_closure :
    (∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : R →+* V), IsAdicComplete (maximalIdeal V) V ∧ Function.Injective φ ∧ I.map φ ≤ maximalIdeal V) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∃ v : AddValuation (AlgebraicClosure (FractionRing V)) (WithTop ℚ), ValOver ϖ (AlgebraicClosure (FractionRing V)) v := by
  refine ⟨fun R _ _ _ I hR => ?_, fun V _ _ _ ϖ hϖ => exists_valOver_of_isAlgebraic hϖ _⟩
  obtain ⟨hN, -, -, hc⟩ := hR
  refine exists_complete_discreteValuationRing_map_le ?_
  rintro rfl
  exact not_subsingleton R (IsHausdorff.subsingleton hc.toIsHausdorff)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamCoefVal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefUnit
open GlobalTheory.UT.CoefBasic

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem point_ext {X : Scheme.{0}} [X.IsSeparated] (x₁ x₂ : (TWM.TO hϖ hv).left ⟶ X)
    (h : (TWM.ιS hϖ hv).left ≫ x₁ = (TWM.ιS hϖ hv).left ≫ x₂) : x₁ = x₂ := by
  have hU : ValuativeCriterion.Uniqueness (terminal.from X) := IsSeparated.valuativeCriterion _
  let S : ValuativeCommSq (terminal.from X) :=
    { R := TWO.Ov v, K := F, i₁ := (TWM.ιS hϖ hv).left ≫ x₁, i₂ := terminal.from _,
      commSq := ⟨terminal.hom_ext _ _⟩ }
  have := (hU S).elim ⟨x₁, rfl, terminal.hom_ext _ _⟩ ⟨x₂, h.symm, terminal.hom_ext _ _⟩
  exact congrArg CommSq.LiftStruct.l this

theorem exists_ratio_nonneg {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((TWM.TO hϖ hv).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TWM.TO hϖ hv).left ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ x : F, 0 ≤ v x ∧ ∀ z J, Good L z J →
      (val t (TWM.ιS hϖ hv).left z J).val = cst (R := V) F z x * (val t' (TWM.ιS hϖ hv).left z J).val := by
  obtain ⟨s, hs⟩ := exists_sec hL h (Geo.Tor.genSec t ht)
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.TwistUnit.exists_ratio_local (R := TWO.Ov v) hL s t' ht'
  refine ⟨TWM.ιr (v := v) x₀, TWM.v_ιr x₀, fun z J hJ => ?_⟩
  have e := gs_pull (𝟙 _) (TWM.ιS hϖ hv).left z ⊤ trivial x₀
  rw [Category.id_comp] at e
  have e' := e.symm.trans (congrArg (gs (𝟙 _) z ⊤)
    (TWM.appTop_specMap (CommRingCat.ofHom (algebraMap (TWO.Ov v) F)) x₀))
  exact (sval_genSec t ht _ z hJ).symm.trans ((hs _ _ z J hJ).symm.trans
    ((hx₀ _ _ z J hJ).trans (congrArg (· * _) e')))

theorem exists_ratio_zero {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((TWM.TO hϖ hv).left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((TWM.TO hϖ hv).left ⟶ X)} {ε' : K' → ℤ}
    (h : FormEq φ ε φ' ε') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht' : t'.IsGen) : ∃ x : F, v x = 0 ∧ ∀ z J, Good L z J →
      (val t (TWM.ιS hϖ hv).left z J).val = cst (R := V) F z x * (val t' (TWM.ιS hϖ hv).left z J).val := by
  obtain ⟨x, hx, e⟩ := exists_ratio_nonneg hϖ hv hL h t ht t' ht'
  obtain ⟨y, hy, e'⟩ := exists_ratio_nonneg hϖ hv hL (fun U _ g => (h U g).symm) t' ht' t ht
  refine ⟨x, le_antisymm (TWO.le_zero_of_add_eq_zero_nonneg ?_ hy) hx, e⟩
  obtain ⟨z⟩ := exists_pt (R := V) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' hL z
  have a := e z J hJ
  rw [e' z J hJ, ← _root_.mul_assoc, cst_eq, cst_eq, ← map_mul] at a
  have b : cstH z (x * y) = 1 := by
    rw [← Units.mul_left_inj (val t (TWM.ιS hϖ hv).left z J), _root_.one_mul]; exact a.symm
  rw [← AddValuation.map_mul, cstH_inj z (b.trans (map_one _).symm), AddValuation.map_one]

theorem v_of_isCoef {D : DegData V (maximalIdeal V)} {k : ℕ} {g : GtPtF D.toPre F} {w : Frm D.toPre F k g.b}
    {χ : D.toPre.X} {l ω : ℚ} (hg : GenV hϖ hv (g.s χ) l) (hw : GenV hϖ hv w ω)
    (m : TWM.TO hϖ hv ⟶ D.toPre.P.A) (hm : TWM.ιS hϖ hv ≫ m = g.b)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)))
    (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => m.left ≫ DegPre.famφB D.toPre χ i) (DegPre.famε k)))
    (hG₀ : G₀.IsGen) (x : F)
    (hs : ∀ z J, Good D.toPre.P.L z J → sval s (lift (𝟙 (TF (R := V) F)) g.b).left z J =
      cst (R := V) F z x * (val G₀ (TWM.ιS hϖ hv).left z J).val) :
    ∃ c, IsCoef k g w χ s c ∧ v c = v x + ((l + ω : ℚ) : WithTop ℚ) := by
  have hL := D.toPre.P.isLB
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  have : D.toPre.P.A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from D.toPre.P.A.hom]; infer_instance⟩
  obtain ⟨φ₁, h₁, t₁, ht₁, x₁, v₁, e₁⟩ := hg
  obtain ⟨φ₂, h₂, t₂, ht₂, x₂, v₂, e₂⟩ := hw
  have c₁ : TWM.ιS hϖ hv ≫ cP D.toPre _ χ = cP D.toPre _ χ := comp_cP D.toPre _ χ
  have c₂ : TWM.ιS hϖ hv ≫ (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A) = 1 := MonObj.comp_one _
  have c₃ : TWM.ιS hϖ hv ≫ (cP D.toPre _ χ * m) = cP D.toPre _ χ * g.b := by
    rw [MonObj.comp_mul, c₁, hm]
  obtain rfl : φ₁ = TWM.gtφO hϖ hv m χ := funext fun i => point_ext hϖ hv _ _ ((h₁ i).symm.trans (by
    fin_cases i
    exacts [congrArg (·.left) c₃.symm, congrArg (·.left) c₁.symm, congrArg (·.left) hm.symm,
      congrArg (·.left) c₂.symm]))
  obtain rfl : φ₂ = TWM.lineφO hϖ hv m := funext fun i => point_ext hϖ hv _ _ ((h₂ i).symm.trans (by
    fin_cases i
    exacts [congrArg (·.left) c₂.symm, congrArg (·.left) hm.symm]))
  obtain ⟨u, hu, eu⟩ := exists_ratio_zero hϖ hv hL (fun U _ h => by
      have p := SectionScalarValuation.prod_famB D.toPre m χ k h
      have q : (TWM.TO hϖ hv).hom ≫ eSec D.toPre.P.A = (1 : TWM.TO hϖ hv ⟶ D.toPre.P.A).left := rfl
      have r : m * SectionScalarValuation.cQ D.toPre _ χ = cP D.toPre _ χ * m := mul_comm _ _
      have r' : SectionScalarValuation.cQ D.toPre (TWM.TO hϖ hv) χ = cP D.toPre _ χ := rfl
      rw [r, r'] at p
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [p, Fintype.prod_unique (_ : PUnit → U), q]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, TWM.gtφO, TWM.lineφO, DegPre.gtε, DegPre.lineε, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ G₀ t₁) t₂)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ hG₀ ht₁) ht₂)
    (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1)
      D.toPre.rig k) (TWM.TO hϖ hv).hom)
    (DVR.pullGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ D.toPre.rig_gen k) _)
  refine ⟨x * x₁ * x₂ * u, fun z J hJ => ?_, ?_⟩
  · have a := eu z J hJ
    rw [val_mul hJ, val_mul hJ, val_pull hJ, Over.w (TWM.ιS hϖ hv)] at a
    have b : val (GeneratorPullback.powGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1)
      D.toPre.rig k) (TF (R := V) F).hom z J = rigV D.toPre (TF (R := V) F).hom z J ^ k := map_pow _ _ _
    rw [b, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val] at a
    rw [hs z J hJ, e₁ z J hJ, e₂ z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination (-(cstH z x * cstH z x₁ * cstH z x₂)) * a
  · rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, hu, v₁, v₂, add_zero, add_assoc,
      WithTop.coe_add]

end

theorem exists_fam_coef_val : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 4 ≤ k → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b) l ω, w.IsGen → GtV hϖ hv g l → GenV hϖ hv w ω → ∀ a₀ : D.toPre.X, ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ (∀ β, (∀ z : D.toPre.X, β ≠ a₀ + k • z) → ∀ j, (s.s β).f j = 0) ∧ v (coef s g w a₀) = (((Q a₀ : ℚ) / k + l a₀ + ω : ℚ) : WithTop ℚ) := by
  intro hLL hT _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk g w l ω hw hg hω a₀
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv g.b
  obtain ⟨σ, hσ, G₀, hG₀, x, hx, hs⟩ :=
    GlobalTheory.exists_integral_section_unit_at hLL.1 hT V ϖ hϖ D Q hQ F v hv k hk a₀ m
  rw [hm] at hs
  obtain ⟨c, hc, vc⟩ := v_of_isCoef hϖ hv (hg a₀) hω m hm σ G₀ hG₀ x hs
  obtain ⟨s₀, rfl, h₀⟩ := GlobalTheory.FamFree.exists_fam_single hLL.1.globalFns D.tau_bimult (by omega : 1 ≤ k) a₀ σ
  obtain ⟨ζ, hζ⟩ : ∃ ζ : F, v ζ = (((Q a₀ : ℚ) / k : ℚ) : WithTop ℚ) := by
    by_cases h : a₀ = 0
    · exact ⟨1, by rw [h, QForm.Q_zero hϖ D hQ, AddValuation.map_one]; simp⟩
    · have h1 := QForm.Q_pos hϖ D hQ h
      obtain ⟨ζ, -, e⟩ := exists_val_eq hv (r := (Q a₀ : ℚ) / k)
        (div_pos (by exact_mod_cast (by omega : (0 : ℤ) < Q a₀)) (by exact_mod_cast (by omega : 0 < k)))
      exact ⟨ζ, e⟩
  have hsm : Fam.IsSmul D.toPre F ζ s₀ (ζ • s₀) := (isSmul_iff _ _ _).2 rfl
  have hz : ∀ β, (∀ z : D.toPre.X, β ≠ a₀ + k • z) → ∀ j, ((ζ • s₀).s β).f j = 0 := fun β hβ j => by
    rw [hsm β j, h₀ β (fun mu e => hβ mu e.symm) j]; exact mul_zero _
  refine ⟨ζ • s₀, fun χ => ?_, hz, ?_⟩
  · by_cases h : ∃ z : D.toPre.X, χ = a₀ + k • z
    · obtain ⟨z, rfl⟩ := h
      have H := SectionScalarValuation.fe_move hϖ hQ hv k z a₀ (ζ • s₀) (hσ.smul hζ.ge (hsm a₀))
      have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      have e : 0 + (Q a₀ : ℚ) / k + ((k * Q z + QForm.bOf D.toPre Q z a₀ : ℤ) : ℚ) =
          0 + (Q (a₀ + k • z) : ℚ) / k := by
        rw [q_shift hϖ hQ a₀ z k]; push_cast; field_simp; ring
      rwa [e] at H
    · exact vge_of_zero (hz χ fun z e => h ⟨z, e⟩) _
  · have e : ζ • s₀ = (ζ - 1) • s₀ + s₀ := by rw [sub_smul, one_smul, sub_add_cancel]
    rw [e, ((coef_basic V D.toPre F k g).2.2 w hw).2.1, coef_eq hc, show (ζ - 1) * c + c = ζ * c by ring,
      AddValuation.map_mul, hζ, vc, hx, ← WithTop.coe_add, ← WithTop.coe_add, zero_add, add_assoc]

end GlobalTheory.UT.CoefUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UT.ExactTerm
open GlobalTheory.ThetaPtMove

theorem gs_zero' {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : gs r z U 0 = 0 := by
  rw [gs_eq r z U h, map_zero, map_zero]

theorem isUnit_top_of_ne_zero {K : Type} [Field K] {v : Γ(Spec (CommRingCat.of K), ⊤)} (hv : v ≠ 0) : IsUnit v := by
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2 v
  have hc : c ≠ 0 := fun h => hv (by rw [h, map_zero])
  exact (IsUnit.mk0 c hc).map _

theorem exists_good_point (hG : GoodPtSt) (hB : PolBaseChangeSt) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K]
    [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) {n : ℕ} (hn : 2 ≤ n) (hK : (n : K) ≠ 0)
    (th₀ : LB.Sec (LPow P.A P.L 1 (Over.mk t))) (h₀ : SecM.ofSec P.A th₀ ≠ 0) (a : Over.mk t ⟶ P.A) :
    ∃ x : Over.mk t ⟶ P.A, x ^ n = 1 ∧ ∀ z J, Good P.L z J →
      IsUnit (VVRank.sv P.A th₀ (ptSecT P.A (a * x)).left z J) := by
  obtain ⟨Q, g, hg, -, hm, t', ht'⟩ := hB S _ t P
  have hp : IsGrpPullback Q.A P.A t g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    have ex : x₀ = Out.toBase hg.w x := Over.OverMorphism.ext hx
    have ey : y₀ = Out.toBase hg.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hm]; rfl⟩
  obtain ⟨w, hw⟩ := LBIso.symm (⟨t', ht'⟩ : LBIso _ _)
  let τ : (baseOver (Spec (CommRingCat.of K))).left ⟶ (Over.mk t).left := 𝟙 _
  have : IsIso τ := inferInstanceAs (IsIso (𝟙 (Spec (CommRingCat.of K))))
  have hτ : τ ≫ (Over.mk t).hom = (baseOver (Spec (CommRingCat.of K))).hom ≫ t := rfl
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw P.isLB Q.isLB th₀
  have hne : SecM.ofSec Q.A th ≠ 0 := fun e => h₀ (ThetaAct.sv_ext P.isLB fun y J hJ => by
    obtain ⟨χ, -, h₂⟩ := WeilPull.exists_psi_inv hp τ hτ
    have h₂' : χ ≫ psi hp τ hτ = 𝟙 _ := h₂
    obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' Q.isLB y
    have q := hth _ χ y J J' hJ hJ'
    have q₀ : VVRank.sv Q.A th χ y J' = 0 :=
      (congrArg (fun u => ThetaAct.sv u χ y J') e).trans
        (gs_zero' χ y _ (hJ'.mem (fun _ : Fin 1 => (snd _ Q.A).left) χ))
    rw [h₂', q₀, MulZeroClass.mul_zero] at q
    exact q.trans (gs_zero' _ y _ (hJ.mem (fun _ : Fin 1 => (snd _ P.A).left) (𝟙 _))).symm)
  let a' : baseOver (Spec (CommRingCat.of K)) ⟶ Q.A :=
    Over.homMk (hg.lift a.left (𝟙 _) ((Over.w a).trans (Category.id_comp t).symm)) (hg.lift_snd _ _ _)
  have ha : τ ≫ a.left = a'.left ≫ g := (Category.id_comp _).trans (hg.lift_fst _ _ _).symm
  obtain ⟨x', hx', ρ, v, -, hv, hv₀⟩ := hG K Q n hn hK th hne a'
  let x : Over.mk t ⟶ P.A := Over.homMk (x'.left ≫ g) (by
    rw [Category.assoc, hg.w, ← Category.assoc, Over.w x']; exact Category.id_comp _)
  have hx : τ ≫ x.left = x'.left ≫ g := Category.id_comp _
  refine ⟨x, ?_, fun z J hJ => ?_⟩
  · have e₁ := over_pow hp τ hτ hx n
    rw [hx', ← over_one hp τ hτ] at e₁
    exact Over.OverMorphism.ext ((cancel_epi τ).1 e₁)
  · obtain ⟨J', hJ'⟩ := CoefBasic.exists_good' Q.isLB z
    have q := hth _ (𝟙 _ ≫ (ptSecT Q.A (a' * x')).left) z J J' hJ hJ'
    rw [sv_of_isValueAt hv (𝟙 _) z hJ', Category.assoc, psi_ptSec hp τ hτ (over_mul hp τ hτ ha hx)] at q
    have e : 𝟙 _ ≫ τ ≫ (ptSecT P.A (a * x)).left = (ptSecT P.A (a * x)).left :=
      (Category.id_comp _).trans (Category.id_comp _)
    rw [e] at q
    rw [q, gs_eq _ z ⊤ trivial]
    exact (Units.isUnit _).mul ((((isUnit_top_of_ne_zero hv₀).map _).map _).mul (Units.isUnit _))

theorem exists_generator_ne_zero (hS : SecBaseChangeSt) {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) :
    ∃ β : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 1)),
      (∀ s : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 1)), ∃ c : R,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) (J), Good P.L z J →
          sval s r z J = Geo.Tor.cst (r ≫ P.A.hom) z c * sval β r z J) ∧
      ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
        ∃ th : LB.Sec (LPow P.A P.L 1 (Over.mk t)), SecM.ofSec P.A th ≠ 0 ∧
          ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk t ⊗ P.A).left) (z : Z) (J), Good P.L z J →
            VVRank.sv P.A th r z J = sval β (r ≫ (snd (Over.mk t) P.A).left) z J := by
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of R)) P 1 le_rfl (closedPoint R)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).left :=
    (Spec (CommRingCat.of R)).topIso.inv
  have hi : i₀ ≫ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).hom = 𝟙 _ := by
    show (Spec (CommRingCat.of R)).topIso.inv ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.inv_hom_id
  have hi' : (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).hom ≫ i₀ = 𝟙 _ := by
    show (Scheme.Opens.ι ⊤ ≫ 𝟙 _) ≫ (Spec (CommRingCat.of R)).topIso.inv = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.hom_inv_id
  let u : P.A ⟶ overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤ :=
    Over.homMk (P.A.hom ≫ i₀) (by rw [Category.assoc, hi, Category.comp_id])
  have uniq : ∀ {T : Over (Spec (CommRingCat.of R))} (p q : T ⟶ overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤),
      p = q := fun p q => Over.OverMorphism.ext (by
    rw [← Category.comp_id p.left, ← Category.comp_id q.left, ← hi', ← Category.assoc, ← Category.assoc, Over.w p,
      Over.w q])
  let β : LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 1)) :=
    VVRank.pullTo (φ := fun _ : Fin 1 => (snd (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤) P.A).left)
      (ε := fun _ => 1) (b hq.default) (lift u (𝟙 P.A)).left
      (fun _ => congrArg (fun q => q.left) (lift_snd u (𝟙 P.A)))
  have key : ∀ (R' : Type) [CommRing R'] (t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)),
      ∃ th : LB.Sec (LPow P.A P.L 1 (Over.mk t)),
        (∀ r : Γ((Over.mk t).left, ⊤), r • (SecM.ofSec P.A th : SecM P.A P.L 1 (Over.mk t)) = 0 → r = 0) ∧
        (∀ s : SecM P.A P.L 1 (Over.mk t), ∃ r : Γ((Over.mk t).left, ⊤), r • SecM.ofSec P.A th = s) ∧
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (Over.mk t ⊗ P.A).left) (z : Z) (J), Good P.L z J →
          VVRank.sv P.A th r z J = sval β (r ≫ (snd (Over.mk t) P.A).left) z J := by
    intro R' _ t
    obtain ⟨t', rfl⟩ : ∃ t' : Spec (CommRingCat.of R') ⟶ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).left,
        t' ≫ (overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤).hom = t :=
      ⟨t ≫ i₀, by rw [Category.assoc, hi, Category.comp_id]⟩
    obtain ⟨hli, hsp⟩ := hb R' t' (fun i => VVRank.pullS P.A _ (homAt t') (b i)) fun i =>
      VVRank.isPullSec_pullS _ _ _ _
    refine ⟨VVRank.pullS P.A _ (homAt t') (b hq.default), fun r hr => ?_, fun s => ?_, fun Z r z J hJ => ?_⟩
    · exact Fintype.linearIndependent_iff.1 hli (fun _ => r) (by rw [Fintype.sum_unique]; exact hr) hq.default
    · rw [Set.range_unique] at hsp
      exact Submodule.mem_span_singleton.1 (hsp.ge Submodule.mem_top)
    · have e : homAt t' ▷ P.A = snd (baseAt t') P.A ≫ lift u (𝟙 P.A) :=
        CartesianMonoidalCategory.hom_ext _ _ (uniq _ _) (by
          rw [whiskerRight_snd, Category.assoc, lift_snd, Category.comp_id])
      refine (VVRank.sv_pullS P.A _ (homAt t') _ r z hJ).trans (Eq.trans ?_ (VVRank.sval_pullTo _ _ _ _ z hJ).symm)
      rw [e, Over.comp_left, Category.assoc]
  refine ⟨β, fun s => ?_, fun K _ t => ?_⟩
  · obtain ⟨th, -, hsp, hv⟩ := key R (𝟙 _)
    obtain ⟨c, hc⟩ := hsp (SecM.ofSec P.A (VVRank.pullTo (φ' := fun _ : Fin 1 => (snd (Over.mk (𝟙 _)) P.A).left) s
      (snd (Over.mk (𝟙 _)) P.A).left fun _ => Category.comp_id _))
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 c
    refine ⟨c, fun Z r z J hJ => ?_⟩
    let u' : P.A ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) := Over.homMk P.A.hom (Category.comp_id _)
    have e₁ : (r ≫ (lift u' (𝟙 P.A)).left) ≫ (snd (Over.mk (𝟙 _)) P.A).left = r := by
      rw [Category.assoc, ← Over.comp_left, lift_snd]; exact Category.comp_id _
    have e₂ : (r ≫ (lift u' (𝟙 P.A)).left) ≫ (fst (Over.mk (𝟙 _)) P.A).left = r ≫ P.A.hom := by
      rw [Category.assoc, ← Over.comp_left, lift_fst]; rfl
    have q := (congrArg (fun w => ThetaAct.sv w (r ≫ (lift u' (𝟙 P.A)).left) z J) hc).symm.trans
      (ThetaAct.sv_smul _ _ _ z hJ)
    have q₁ := (VVRank.sval_pullTo s _ (fun _ => Category.comp_id _) _ z hJ).symm.trans
      (q.trans (congrArg₂ (· * ·) rfl (hv Z _ z J hJ)))
    rw [e₁, e₂] at q₁
    exact q₁
  · obtain ⟨th, hli, -, hv⟩ := key K t
    refine ⟨th, fun e => ?_, hv⟩
    have h1 := hli 1 (by rw [e, smul_zero])
    have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom h1
    exact one_ne_zero ((map_one _).symm.trans (h2.trans (map_zero _)))

theorem exists_secB_good (hL : Laws) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (D : DegPre R) (χ : D.X) : ∃ b : D.SecB 1 χ,
      (∀ σ : D.SecB 1 χ, ∃ c : R, ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
          sval σ r z J = Geo.Tor.cst (r ≫ D.P.A.hom) z c * sval b r z J) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (n : ℕ), 2 ≤ n →
        (n : K) ≠ 0 → ∀ a : Over.mk t ⟶ D.P.A, ∃ x : Over.mk t ⟶ D.P.A, x ^ n = 1 ∧
          ∀ z J, Good D.P.L z J → IsUnit (sval b (a * x).left z J) := by
  have hM := D.P.isLB
  obtain ⟨β, hβ, hβ'⟩ := exists_generator_ne_zero hL.secBaseChange D.P
  obtain ⟨ξ₀, hξ₀⟩ := exists_gen_of_local D.P.L hM (K := Fin 2)
    ![(D.c χ).left, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left] ![-1, 1]
  obtain ⟨ξ, hξ, vξ⟩ := VVRank.exists_gen_pullTo (φ' := ![(SectionScalarValuation.cQ D D.P.A χ).left, (1 : D.P.A ⟶ D.P.A).left]) ξ₀ hξ₀
    D.P.A.hom (fun i => by
      fin_cases i
      · rfl
      · exact congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toUnit D.P.A)))
  let τ : D.P.A ⟶ D.P.A := 𝟙 _ * SectionScalarValuation.cQ D D.P.A χ
  let τ' : D.P.A ⟶ D.P.A := 𝟙 _ * (SectionScalarValuation.cQ D D.P.A χ)⁻¹
  have hτ : ∀ {T : Over (Spec (CommRingCat.of R))} (y : T ⟶ D.P.A), y ≫ τ = y * SectionScalarValuation.cQ D T χ := fun y => by
    rw [MonObj.comp_mul, Category.comp_id, SectionScalarValuation.comp_cQ]
  have hττ : τ ≫ τ' = 𝟙 _ := by
    rw [MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, SectionScalarValuation.comp_cQ, mul_inv_cancel_right]
  obtain ⟨b, hb⟩ := exists_sec hM (φ' := D.famφB χ) (ε' := DegPre.famε 1) (fun U _ h => by
    have p := SectionScalarValuation.prod_famB D (𝟙 D.P.A) χ 1 h
    simp only [Over.id_left, Category.id_comp] at p
    rw [p, Fintype.prod_sum_type, Fin.prod_univ_one, Fin.prod_univ_two]
    simp [τ, _root_.mul_assoc]) (pullMulSec β τ.left ξ hξ)
  have vb : ∀ (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      sval b r z J = sval β (r ≫ τ.left) z J * (val ξ r z J).val := fun Z r z J hJ =>
    (hb Z r z J hJ).trans (sval_pullMulSec _ _ _ hξ r z hJ)
  refine ⟨b, fun σ => ?_, fun K _ _ t n hn hK a => ?_⟩
  · obtain ⟨s, hs⟩ := exists_sec hM (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left) (ε' := fun _ => 1) (fun U _ h => by
      have p := SectionScalarValuation.prod_famB D τ' χ 1 h
      have e : τ' * SectionScalarValuation.cQ D D.P.A χ = 𝟙 _ := inv_mul_cancel_right _ _
      rw [e] at p
      rw [Fintype.prod_sum_type, Fin.prod_univ_one, Fin.prod_univ_two]
      refine (congrArg₂ (· * ·) p rfl).trans ?_
      simp [_root_.mul_assoc, mul_left_comm]) (pullMulSec σ τ'.left _ (invGen_isGen _ _ _ _ hξ))
    obtain ⟨c, hc⟩ := hβ s
    refine ⟨c, fun Z r z J hJ => ?_⟩
    have q := (hc Z (r ≫ τ.left) z J hJ).symm.trans ((hs Z _ z J hJ).trans (sval_pullMulSec _ _ _ _ _ z hJ))
    rw [val_inv, vξ _ _ z J hJ, Category.assoc, Category.assoc, ← Over.comp_left, hττ, Over.w τ, Over.id_left,
      Category.comp_id, ← vξ _ _ z J hJ] at q
    rw [vb Z r z J hJ, ← _root_.mul_assoc, q, Units.inv_mul_cancel_right]
  · obtain ⟨th, h₀, hth⟩ := hβ' K t
    obtain ⟨x, hx, hu⟩ := exists_good_point hL.goodPt hL.polBaseChange D.P t hn hK th h₀ (a * SectionScalarValuation.cQ D _ χ)
    refine ⟨x, hx, fun z J hJ => ?_⟩
    have q := hu z J hJ
    rw [hth _ _ z J hJ, ptSecT_snd, mul_right_comm, ← hτ, Over.comp_left] at q
    rw [vb _ _ z J hJ]
    exact q.mul (Units.isUnit _)

theorem isUnit_gs_iff {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h]
  refine (Z.mem_basicOpen ((r.app U).hom a) z h).symm.trans ?_
  exact Iff.of_eq (congrArg (z ∈ ·) (Scheme.preimage_basicOpen r a).symm)

theorem exists_gen_of_isUnit {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) {O : Type} [CommRing O] [IsLocalRing O]
    (m : Spec (CommRingCat.of O) ⟶ Y)
    (h : ∀ z J, Good L z J → IsUnit (sval s (Spec.map (CommRingCat.ofHom (residue O)) ≫ m) z J)) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of O)) (z : Z) (J), Good L z J →
        (val t r z J).val = sval s (r ≫ m) z J := by
  let s' := pullSec L φ ε s m
  let z₀ : Spec (CommRingCat.of (ResidueField O)) := closedPoint (ResidueField O)
  obtain ⟨J₀, hJ₀⟩ := CoefBasic.exists_good' hL z₀
  have h₀ := h z₀ J₀ hJ₀
  rw [← SectionScalarValuation.sval_pullSec φ ε s m _ z₀ hJ₀] at h₀
  have h₁ := (isUnit_gs_iff _ z₀ _ (hJ₀.mem (fun k => m ≫ φ k) _) _).1 h₀
  have e : Spec.map (CommRingCat.ofHom (residue O)) z₀ = closedPoint O := IsLocalRing.comap_closedPoint (residue O)
  rw [e] at h₁
  have h₂ := eq_top_of_closedPoint_mem _ h₁
  have hu : ∀ j, IsUnit (s'.f j) := fun j => (Spec (CommRingCat.of O)).toRingedSpace.isUnit_of_isUnit_germ _ _
    fun y hy => by
      have hy₀ := h₂.ge (Set.mem_univ y)
      have hy₁ := Scheme.basicOpen_le _ _ hy₀
      have q := sec_trans s' (𝟙 _) y hy hy₁
      exact (congrArg IsUnit ((gs_eq (𝟙 _) y (LB.wchart L (fun k => m ≫ φ k) j) hy _).symm.trans q)).mpr
        ((Units.isUnit _).mul ((isUnit_gs_iff (𝟙 _) y _ hy₁ _).2 hy₀))
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s'.compat i j), fun Z r z J hJ => ?_⟩
  exact (gs_unit r z _ (hJ.mem (fun k => m ≫ φ k) r) _).symm.trans (SectionScalarValuation.sval_pullSec φ ε s m r z hJ)

end GlobalTheory.UT.ExactTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimGenerator
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.PrimGen

open GlobalTheory.FieldBaseChange

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_lower (v : AddValuation F (WithTop ℚ)) {n : ℕ} (c : Fin n → F) :
    ∃ r : ℚ, ∀ i, (r : WithTop ℚ) ≤ v (c i) := by
  obtain ⟨m, hm⟩ := (Set.finite_range fun i => (v (c i)).untopD 0).bddBelow
  refine ⟨m, fun i => ?_⟩
  have h := hm ⟨i, rfl⟩
  cases e : v (c i) with
  | top => exact le_top
  | coe y =>
    simp only [e, WithTop.untopD_coe] at h
    exact WithTop.coe_le_coe.2 h

theorem exists_vge (U : UnifPre (maximalIdeal V) D A G) (v : AddValuation F (WithTop ℚ)) {k : ℕ}
    {σ : U.SecGF F k} {s : Fam D.toPre F k} (h : U.ExpandsG F k σ s) (α : D.toPre.X) :
    ∃ r : ℚ, VGe D F v k α (s.s α) r := by
  obtain ⟨n, c, x, -, -, hs⟩ := (expandsG_iff U F k σ s).1 h
  obtain ⟨r, hr⟩ := exists_lower v c
  refine ⟨r, n, c, fun i => (x i).2 α,
    fun i => termPull D.toPre (FractionRing V) F k α (genericTerm D k α ((x i).2 α)), fun i => ?_, hr, fun j => ?_⟩
  · exact SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ =>
      ((sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval ((x i).2 α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing V) F))))))).symm
  · exact (congrArg (chartLin (famBase D.toPre F) _ j) (hs α)).trans (map_sum (chartLin (famBase D.toPre F) _ j) _ _)

theorem exists_prim_span (hU : UUStatement) {ϖ : V} (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ}
    (hQ : QForm.IsQ D.toPre ϖ Q) [IsAlgClosed F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v) :
    ∃ ϑ : Fam D.toPre F 1, Prim D Q v ϑ ∧
      ∀ s : Fam D.toPre F 1, (∃ r : ℚ, VGe D F v 1 0 (s.s 0) r) → ∃ c : F, s = c • ϑ := by
  classical
  obtain ⟨b, hli, hb, hsp⟩ := hU V ϖ hϖ D Q hQ F v hv (Or.inl inferInstance) 1 le_rfl
  have : Subsingleton (Fin (1 ^ (D.toPre.rank + D.toPre.P.g))) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ (D.toPre.rank + D.toPre.P.g)) := ⟨0, by rw [one_pow]; exact one_pos⟩
  have hsp' : ∀ s, NuGe D Q F v 1 s 0 → ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ s = c • b i₀ := fun s hs => by
    obtain ⟨c, hc, e⟩ := (hsp s).1 hs
    exact ⟨c i₀, hc i₀, e.trans (Fintype.sum_subsingleton _ i₀)⟩
  refine ⟨b i₀, ⟨hb i₀, fun r hr h => ?_⟩, ?_⟩
  · obtain ⟨ζ, s', hζ, hs', e⟩ := (n1c V ϖ hϖ D Q hQ F v hv 1 le_rfl (b i₀) (hb i₀)).1 ⟨r, hr, h⟩
    obtain ⟨c, hc, rfl⟩ := hsp' s' hs'
    rw [isSmul_iff, smul_smul] at e
    have e1 : ζ * c = 1 := smul_left_injective F (hli.ne_zero i₀) (e.symm.trans (one_smul F _).symm)
    have h0 : (0 : WithTop ℚ) < v (ζ * c) := by
      rw [AddValuation.map_mul]
      exact lt_add_of_lt_of_nonneg hζ hc
    rw [e1, AddValuation.map_one] at h0
    exact lt_irrefl _ h0
  · rintro s ⟨r, hr⟩
    have h1 : NuGe D Q F v 1 s (-(|r| + 1)) := by
      rw [n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {0} (fun χ => ⟨0, Finset.mem_singleton_self _, χ, by simp⟩) s]
      intro α hα
      obtain rfl := Finset.mem_singleton.1 hα
      refine hr.mono ?_
      rw [QForm.Q_zero hϖ D hQ]
      have := neg_abs_le r
      simp only [Int.cast_zero, zero_div, add_zero]
      linarith
    obtain ⟨ζ, hζ0, hζ⟩ := exists_val_eq hv (r := |r| + 1) (by positivity)
    have h2 := NuGe.smul Q hζ.ge ((isSmul_iff ζ s _).2 rfl) h1
    rw [neg_add_cancel] at h2
    obtain ⟨c, -, e⟩ := hsp' _ h2
    exact ⟨ζ⁻¹ * c, by rw [mul_smul, ← e, inv_smul_smul₀ hζ0]⟩

end GlobalTheory.UT.PrimGen

namespace GlobalTheory.UT

open GlobalTheory.FieldBaseChange

theorem exists_prim_generator : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ : W0 U.toUnifPre, w₀.IsGen → ∃ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ ∧ Prim D Q v ϑ ∧ IsGenSec A.A A.L 1 th := by
  intro hL _ _ _ hU V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ _ U w₀ hw
  obtain ⟨ϑ, hp, hsp⟩ := PrimGen.exists_prim_span hU hϖ hQ hv
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U F (k := 1) le_rfl w₀ hw
  refine ⟨e.symm ϑ, ϑ, (he _ _).2 (e.apply_symm_apply ϑ), hp, fun t => ?_⟩
  obtain ⟨σ, -, hσ⟩ := (he t _).2 rfl
  obtain ⟨c, hc⟩ := hsp _ (PrimGen.exists_vge U.toUnifPre v hσ 0)
  have ht : t = (c • e.symm ϑ : SecOver (abelianBase A F) _) :=
    e.injective (hc.trans (by rw [map_smul, e.apply_symm_apply]))
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c, fun j => ?_⟩
  rw [ht]
  rfl

end GlobalTheory.UT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLeOnFinset
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.AdicValSum

theorem nullV_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) : NullV v x := by
  classical
  intro q
  obtain ⟨S, hS⟩ := h q
  refine S.finite_toSet.subset fun i hi => ?_
  by_contra hiS
  have h1 := hS S subset_rfl
  have h2 := hS (insert i S) (Finset.subset_insert i S)
  have hx : x i = (s - ∑ j ∈ S, x j) - (s - ∑ j ∈ insert i S, x j) := by
    rw [Finset.sum_insert hiS]
    ring
  have h3 : (q : WithTop ℚ) ≤ v (x i) := by
    rw [hx]
    exact le_trans (le_min h1 h2) (AddValuation.map_sub v _ _)
  exact absurd hi (not_lt.mpr h3)

theorem exists_le_on_finset {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (t : Finset F) :
    ∃ c : ℚ, ∀ y ∈ t, (c : WithTop ℚ) ≤ v y := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a t ha ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ : ∃ d : ℚ, (d : WithTop ℚ) ≤ v a := by
      by_cases htop : v a = ⊤
      · exact ⟨0, htop ▸ le_top⟩
      · exact ⟨(v a).untop htop, by rw [WithTop.coe_untop]⟩
    refine ⟨min c d, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact le_trans (WithTop.coe_le_coe.mpr (min_le_right c d)) hd
    · exact le_trans (WithTop.coe_le_coe.mpr (min_le_left c d)) (hc y hy)

theorem sumV_of_sumI {V : Type} [CommRing V] (I : Ideal V) {F : Type} [Field F] [Module V F] (φ : V → F)
    (hφ : ∀ (a : V) (y : F), a • y = φ a * y) (v : AddValuation F (WithTop ℚ))
    (hv : ∀ (n : ℕ) (a : V), a ∈ I ^ n → ((n : ℚ) : WithTop ℚ) ≤ v (φ a))
    {Ix : Type} {x : Ix → F} {s : F} (h : SumI I x s) : SumV v x s := by
  obtain ⟨N, hNfg, -, -, hconv⟩ := h
  obtain ⟨G, rfl⟩ := hNfg
  obtain ⟨c, hc⟩ := exists_le_on_finset v G
  have h0 : ∀ a : V, (0 : WithTop ℚ) ≤ v (φ a) := by
    intro a
    have := hv 0 a (by simp)
    simpa using this
  have hN : ∀ y ∈ Submodule.span V (G : Set F), (c : WithTop ℚ) ≤ v y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simp
    | add y z _ _ hy hz => exact le_trans (le_min hy hz) (AddValuation.map_add v y z)
    | smul a y _ hy =>
      rw [hφ, AddValuation.map_mul]
      simpa using add_le_add (h0 a) hy
  have hIN : ∀ n : ℕ, ∀ z ∈ I ^ n • Submodule.span V (G : Set F), (((n : ℚ) + c : ℚ) : WithTop ℚ) ≤ v z := by
    intro n z hz
    refine Submodule.smul_induction_on hz (fun r hr y hy => ?_) (fun y z hy hz => ?_)
    · rw [hφ, AddValuation.map_mul, WithTop.coe_add]
      exact add_le_add (hv n r hr) (hN y hy)
    · exact le_trans (le_min hy hz) (AddValuation.map_add v y z)
  intro q
  obtain ⟨S, hS⟩ := hconv ⌈q - c⌉₊
  refine ⟨S, fun T hT => le_trans ?_ (hIN _ _ (hS T hT))⟩
  have : q ≤ (⌈q - c⌉₊ : ℚ) + c := by linarith [Nat.le_ceil (q - c)]
  exact WithTop.coe_le_coe.mpr this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (Ix : Type) (x : Ix → F) (s : F), SumF (maximalIdeal V) F x s → SumV v x s ∧ NullV v x := by
  intro V _ _ _ ϖ hϖ F _ _ v hval Ix x s hsum
  letI : Module V F := Module.compHom F (algebraMap V (FractionRing V))
  have hI : SumI (maximalIdeal V) x s := hsum
  have hV : SumV v x s := by
    refine sumV_of_sumI (maximalIdeal V) (fun a => algebraMap (FractionRing V) F (algebraMap V (FractionRing V) a))
      (fun a y => Algebra.smul_def _ _) v ?_ hI
    intro n a ha
    by_cases ha0 : a = 0
    · subst ha0
      simp
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    have hdvd : ϖ ^ n ∣ ϖ ^ k := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
      exact (Units.dvd_mul_left).mp ha
    have hnk : n ≤ k := (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp hdvd
    have hhv : HasVal ϖ (algebraMap V (FractionRing V) (↑u * ϖ ^ k)) (k : ℤ) :=
      ⟨u, by rw [map_mul, map_pow, zpow_natCast, mul_comm]⟩
    rw [hval _ _ hhv, WithTop.coe_le_coe]
    exact_mod_cast hnk
  exact ⟨hV, nullV_of_sumV hV⟩

end GlobalTheory.UT.AdicValSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenMulPullPowUnif
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem exists_gen_mulPull_pow_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (n k k' : ℕ), k' = k * n ^ 2 → ∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, (𝟙 G ^ n).left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen := by
  intro R _ _ I D A G _ _ U n k k' hk
  have hL := U.LG.isLB
  have hcube : GlobalTheory.MulPull.HasGen U.LG.L (thφ G (x3 G)) thε := ⟨U.cubG.t, U.cubG.isGen⟩
  have hrig : GlobalTheory.MulPull.HasGen U.LG.L (K := PUnit) (fun _ => eSec G) (fun _ => 1) :=
    ⟨U.LG.rig, U.LG.rigGen⟩
  have hneg : GlobalTheory.MulPull.HasGen U.LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] :=
    ⟨U.symG, U.symG_gen⟩
  have main : GlobalTheory.MulPull.HasGen U.LG.L (K := Fin 2) ![(𝟙 G : G ⟶ G).left, (𝟙 G ^ n).left]
      ![(n : ℤ) ^ 2, -1] := by
    refine GlobalTheory.MulPull.hasGen_pow hL hcube (𝟙 G) ?_ ?_ n
    · refine (hrig.pull (toUnit G).left).of_formEq hL (fun W _ h => ?_)
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl
    · refine hneg.inv.of_formEq hL (fun W _ h => ?_)
      have e : ((𝟙 G : G ⟶ G)⁻¹) = ι[G] := Category.id_comp _
      rw [e]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        _root_.mul_one, neg_neg]
      exact _root_.mul_comm _ _
  obtain ⟨t, ht⟩ := main
  have hp : GlobalTheory.MulPull.HasGen U.LG.L (K := Fin 2) ![(𝟙 G : G ⟶ G).left, (𝟙 G ^ n).left]
      (fun i => (k : ℤ) * (![(n : ℤ) ^ 2, -1] : Fin 2 → ℤ) i) := ⟨_, powGen_isGen _ _ _ t ht k⟩
  refine hp.of_formEq hL (fun W _ h => ?_)
  subst hk
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    _root_.mul_one, mul_neg]
  push_cast
  rfl

end GlobalTheory.UT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordAdd
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem GlobalTheory.UU.torus_coord_add : (GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y : T ⟶ thickObj R I e G) (χ : D.X) (z : T.left) (J), Good D.P.L z J → val (g.t χ) (x * y).left z J * @id (T.left.presheaf.stalk z)ˣ (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J (toUnit _ ≫ D.c χ) ((Over.map (thick R I e)).map x ≫ g.pG) ((Over.map (thick R I e)).map y ≫ g.pG)) = val (g.t χ) x.left z J * val (g.t χ) y.left z J) :=
  fun hG _ _ _ _ _ _ _ _ _ g _ x y χ z J hJ => GlobalTheory.TorusCoord.val_t_mul_points g hG χ x y z J hJ
end
