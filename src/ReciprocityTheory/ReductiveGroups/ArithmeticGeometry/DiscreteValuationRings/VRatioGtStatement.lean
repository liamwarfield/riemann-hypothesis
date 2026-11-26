module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing TWO SectionScalarValuation QForm

def VRatioGtStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ)
    (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v)
      (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (m : TO hϖ hv ⟶ D.toPre.P.A), ιS hϖ hv ≫ m = p.g.b →
      ∀ (α : D.toPre.X) (G₀ : LB.Gen (LB.LinComb D.toPre.P.L (gtφO hϖ hv m α) DegPre.gtε)), G₀.IsGen → ∀ t : F,
      (∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := V) F).left) (z : Z) (J), Good D.toPre.P.L z J →
        (val (p.g.s α) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom t) *
          (val G₀ (r ≫ (ιS hϖ hv).left) z J).val) →
      ∃ q : ℚ, v t = (q : WithTop ℚ) ∧ (k : ℚ) * q = bOf D.toPre Q p.y α

section Ratio

variable {V : Type} [CommRing V] [IsDomain V] {F : Type} [Field F] [Algebra (FractionRing V) F] {X : Scheme.{0}}
  {L : LB X}

theorem exists_ratio (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Spec (CommRingCat.of F) ⟶ X)}
    {ε : K → ℤ} {φ' : K' → (Spec (CommRingCat.of F) ⟶ X)} {ε' : K' → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb L φ' ε')) (ht' : t'.IsGen) (hf : FormEq φ ε φ' ε') :
    ∃ c : F, c ≠ 0 ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (J), Good L z J →
      (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val t' r z J).val := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of F)))) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (Spec (CommRingCat.of F))) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const L hL (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ t')) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ ht'))
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [hf U h, mul_inv_cancel])
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (J), Good L z J →
      (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * (val t' r z J).val := by
    intro Z r z J hJ
    have e := ha Z r z J hJ
    rw [val_mul hJ, val_inv, Category.comp_id, ← hc] at e
    rw [← e, Units.val_mul, _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.mul_one]
  refine ⟨c, ?_, key⟩
  rintro rfl
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  choose I hI' using fun χ : Spec (CommRingCat.of F) ⟶ X => exists_chart hL (χ z)
  have e := key _ (𝟙 _) z I hI'
  have g0 : gs (𝟙 (Spec (CommRingCat.of F))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom 0) = 0 := by
    rw [map_zero]
    have := gs_add (𝟙 (Spec (CommRingCat.of F))) z ⊤ trivial (0 : Γ(Spec (CommRingCat.of F), ⊤)) 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  rw [g0, MulZeroClass.zero_mul] at e
  exact Units.ne_zero _ e

end Ratio

section Main

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem trO_one : trO hϖ hv (D := D) 1 = 𝟙 _ := by
  unfold trO
  rw [MonObj.comp_one, padd, ← Hom.mul_def, _root_.mul_one, lift_fst_snd]

theorem trO_mul (m m' : TO hϖ hv ⟶ D.toPre.P.A) : trO hϖ hv m ≫ trO hϖ hv m' = trO hϖ hv (m * m') := by
  unfold trO
  simp only [padd, ← Hom.mul_def, comp_lift, lift_fst, lift_snd, MonObj.comp_mul, lift_fst_assoc]
  rw [_root_.mul_assoc]

theorem wt_coe_of_ne {x : F} (hx : x ≠ 0) : ∃ q : ℚ, v x = (q : WithTop ℚ) := by
  have h : v x ≠ ⊤ := fun h => hx ((AddValuation.top_iff v).mp h)
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp h
  exact ⟨q, hq.symm⟩

theorem v_inv_coe {x : F} (hx : x ≠ 0) {q : ℚ} (hq : v x = q) : v x⁻¹ = ((-q : ℚ) : WithTop ℚ) := by
  rw [AddValuation.map_inv, hq]
  rfl

end Main

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

section Basic

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem vge_of_zero {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))}
    (h : ∀ j, s.f j = 0) (r : ℚ) : VGe D F v k α s r := by
  unfold VGe
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun j => ?_⟩
  rw [h j, Fin.sum_univ_zero]

end Basic

theorem n4 : ValuationBoundAtZero := by
  intro V _ _ _ ϖ hϖ D Q _ F _ _ v hv m _ R' β s hsupp hnu w hw q hq
  classical
  obtain ⟨x, hx, hsum⟩ := hw
  have hxq : ∀ α, ((q : ℚ) : WithTop ℚ) ≤ v (x α) := by
    intro α
    by_cases h : ∃ z, α = β + R' • z
    · obtain ⟨z, rfl⟩ := h
      have h1 := GC.valuation_ge_at_zero hϖ hv (hnu (β + R' • z)) (hx _)
      refine le_trans (WithTop.coe_le_coe.2 ?_) h1
      rw [zero_add]; exact hq z
    · push Not at h
      exact GC.valuation_ge_at_zero hϖ hv (vge_of_zero (v := v) (hsupp α h) q) (hx α)
  obtain ⟨S, hS⟩ := hsum q
  have h1 := hS S le_rfl
  have h2 : ((q : ℚ) : WithTop ℚ) ≤ v (∑ α ∈ S, x α) := AddValuation.map_le_sum v fun α _ => hxq α
  have h3 := AddValuation.map_le_add v h1 h2
  rwa [sub_add_cancel] at h3

section Q

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ}

theorem bOf_zero_left (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (b : D.toPre.X) : bOf D.toPre Q 0 b = 0 := by
  simp [bOf, QForm.Q_zero hϖ D hQ]

theorem bOf_nsmul_left (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (n : ℕ) (a b : D.toPre.X) :
    bOf D.toPre Q (n • a) b = n * bOf D.toPre Q a b := by
  induction n with
  | zero => simp [bOf_zero_left hϖ hQ]
  | succ n ih => rw [succ_nsmul, QForm.bOf_add_left hϖ D hQ, ih]; push_cast; ring

theorem Q_nsmul (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (n : ℕ) (a : D.toPre.X) : Q (n • a) = n ^ 2 * Q a := by
  induction n with
  | zero => simp [QForm.Q_zero hϖ D hQ]
  | succ n ih =>
    have h2 := QForm.two_Q_eq hϖ D hQ a
    have hb := bOf_nsmul_left hϖ hQ n a a
    have e : Q (n • a + a) = Q (n • a) + Q a + bOf D.toPre Q (n • a) a := by simp only [bOf]; ring
    rw [succ_nsmul, e, ih, hb, ← h2]; push_cast; ring

theorem q_shift (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (α m : D.toPre.X) (k : ℕ) :
    Q (α + k • m) = Q α + k * (k * Q m + bOf D.toPre Q m α) := by
  have e1 : Q (α + k • m) = Q α + Q (k • m) + bOf D.toPre Q α (k • m) := by simp only [bOf]; ring
  rw [e1, QForm.bOf_comm D α (k • m), bOf_nsmul_left hϖ hQ, Q_nsmul hϖ hQ]; ring

end Q

theorem n1a : ValuationMinRepresentatives := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv k hk S hS s r
  refine ⟨fun h α _ => h α, fun h χ => ?_⟩
  obtain ⟨α, hα, m0, rfl⟩ := hS χ
  have H := SectionScalarValuation.fe_move hϖ hQ hv k m0 α s (h α hα)
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have e : r + (Q α : ℚ) / k + ((k * Q m0 + bOf D.toPre Q m0 α : ℤ) : ℚ) = r + (Q (α + k • m0) : ℚ) / k := by
    rw [q_shift hϖ hQ α m0 k]; push_cast; field_simp; ring
  rwa [e] at H

theorem exists_val_eq {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {r : ℚ} (hr : 0 < r) : ∃ ζ : F, ζ ≠ 0 ∧ v ζ = ((r : ℚ) : WithTop ℚ) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ ^ r.num)) r.den_pos
  have hv1 : v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ ^ r.num)) =
      ((r.num : ℚ) : WithTop ℚ) := hv _ _ ⟨1, by simp⟩
  have hpow : v (ζ ^ r.den) = r.den • v ζ := AddValuation.map_pow v ζ r.den
  rw [hζ, hv1] at hpow
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero r.den_nz
  have hne : v ζ ≠ ⊤ := by
    intro h
    rw [h, hk, succ_nsmul, WithTop.add_top] at hpow
    exact WithTop.coe_ne_top hpow
  obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hx, ← WithTop.coe_nsmul, WithTop.coe_eq_coe, nsmul_eq_mul] at hpow
  have hq : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
  have hxr : x = r := by
    have h2 : x = (r.num : ℚ) / (r.den : ℚ) := eq_div_of_mul_eq hq (by rw [mul_comm]; exact hpow.symm)
    rw [h2, Rat.num_div_den]
  exact ⟨ζ, fun h0 => hne (by rw [h0, AddValuation.map_zero]), by rw [← hx, hxr]⟩

theorem n1c : PositiveValuationMaximalIdeal := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv k hk s hs0
  constructor
  · rintro ⟨r, hr, hs⟩
    obtain ⟨ζ, hζ0, hvζ⟩ := exists_val_eq hv hr
    refine ⟨ζ, ζ⁻¹ • s, by rw [hvζ]; exact_mod_cast hr, ?_,
      (isSmul_iff ζ (ζ⁻¹ • s) s).2 (by rw [smul_smul, mul_inv_cancel₀ hζ0, one_smul])⟩
    have h := NuGe.smul Q (q := -r) (by rw [AddValuation.map_inv, hvζ]; rfl) ((isSmul_iff _ _ _).2 rfl) hs
    rwa [add_neg_cancel] at h
  · rintro ⟨ζ, s', hvζ, hs', hsm⟩
    obtain ⟨q, hq, hqle⟩ : ∃ q : ℚ, 0 < q ∧ ((q : ℚ) : WithTop ℚ) ≤ v ζ := by
      cases h : v ζ with
      | top => exact ⟨1, one_pos, le_top⟩
      | coe y => rw [h] at hvζ; exact ⟨y, by exact_mod_cast hvζ, le_rfl⟩
    exact ⟨0 + q, by linarith, NuGe.smul Q hqle hsm hs'⟩

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
