module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfEq
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntegralCoord

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

theorem lin_of_sval {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {s : LB.Sec (LB.LinComb L φ ε)}
    {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (H : ∀ (y : Y) (J : (Y ⟶ X) → L.ι), Good L y J →
      sval s (𝟙 Y) y J = ∑ i, gs (𝟙 Y) y ⊤ (b i) * sval (t i) (𝟙 Y) y J) (j : K → L.ι) :
    s.f j = ∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j) := by
  refine fn_ext fun x hx => ?_
  obtain ⟨J, hJ, -⟩ := sval_trans hL s x j hx
  have hx₀ : (𝟙 Y : Y ⟶ Y) x ∈ LB.wchart L φ j := hx
  have hx' := hJ.mem φ (𝟙 Y)
  change gs (𝟙 Y) x (LB.wchart L φ j) (s.f j) =
    gs (𝟙 Y) x (LB.wchart L φ j) (∑ i, resTop (LB.wchart L φ j) (b i) * (show Γ(Y, LB.wchart L φ j) from (t i).f j))
  have key : ∀ u : LB.Sec (LB.LinComb L φ ε), gs (𝟙 Y) x (LB.wchart L φ j) (u.f j) =
      (trF φ ε (𝟙 Y) x j (fun k => J (𝟙 Y ≫ φ k))).val * sval u (𝟙 Y) x J :=
    fun u => sec_trans u (𝟙 Y) x hx₀ hx'
  rw [key s, H x J hJ, SectionScalarValuation.gs_sum (𝟙 Y) x _ hx₀, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold resTop
  rw [gs_mul (𝟙 Y) x _ hx₀, key (t i), gs_res (𝟙 Y) x le_top hx₀]
  ring

theorem exists_basis_of_eq {S : Scheme.{0}} {A T : Over S} {L : LB A.left} {K : Type} [Fintype K]
    {φ : K → (A.left ⟶ A.left)} {ε : K → ℤ} {m : ℕ} (b₀ : Fin m → LB.Sec (LB.LinComb L φ ε))
    (hb : IsSecBasis (T := T) (A := A) _ (fun i => DVR.pullSec L φ ε (b₀ i) (snd T A).left))
    (φ' : K → ((T ⊗ A).left ⟶ A.left)) (h : φ' = fun k => (snd T A).left ≫ φ k) :
    ∃ b : Fin m → LB.Sec (LB.LinComb L φ' ε), IsSecBasis (T := T) (A := A) _ b ∧
      ∀ i (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
        sval (b i) r z J = sval (b₀ i) (r ≫ (snd T A).left) z J := by
  subst h
  exact ⟨_, hb, fun i Z r z J hJ => sval_pullSec φ ε (b₀ i) (snd T A).left r z hJ⟩

theorem gs_appTop {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (a : Γ(X, ⊤)) :
    gs f z ⊤ (g.appTop.hom a) = gs (f ≫ g) z ⊤ a :=
  gs_pull f g z ⊤ trivial a

theorem specMap_appTop {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (c : Γ(Spec (CommRingCat.of A), ⊤)) :
    (Spec.map (CommRingCat.ofHom f)).appTop.hom c =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c)) := by
  have h2 := congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← h2]
  simp

private theorem famφ_eq_snd_TF {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (α : D.toPre.X) :
    DegPre.famφ D.toPre F α = fun i => (snd (TF (R := V) F) D.toPre.P.A).left ≫ D.toPre.famφB α i := by
  have e1 : padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c α) =
      snd (TF (R := V) F) D.toPre.P.A ≫ padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ D.toPre.c α) := by
    simp only [padd, DegPre.prB, DegPre.BF]
    rw [← Category.assoc]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e2 : ∀ {Z : Over (Spec (CommRingCat.of V))} (h : 𝟙_ (Over (Spec (CommRingCat.of V))) ⟶ Z),
      toUnit (DegPre.BF D.toPre F) ≫ h = snd (TF (R := V) F) D.toPre.P.A ≫ toUnit D.toPre.P.A ≫ h := by
    intro Z h
    simp [DegPre.BF]
  funext i
  fin_cases i
  · show (DegPre.prB D.toPre F).left = (snd (TF (R := V) F) D.toPre.P.A).left ≫ 𝟙 _
    rw [Category.comp_id]
  · show (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c α)).left =
      (snd (TF (R := V) F) D.toPre.P.A).left ≫ (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ D.toPre.c α)).left
    rw [← Over.comp_left, e1]
  · show (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c α).left =
      (snd (TF (R := V) F) D.toPre.P.A).left ≫ (toUnit D.toPre.P.A ≫ D.toPre.c α).left
    rw [← Over.comp_left, e2]
  · show (toUnit (DegPre.BF D.toPre F) ≫ η).left =
      (snd (TF (R := V) F) D.toPre.P.A).left ≫ (toUnit D.toPre.P.A ≫ η).left
    rw [← Over.comp_left, e2]

private theorem jFK_eq_fractionRing {V : Type} [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F] :
    jFK (R := V) F ≫ jK V = Spec.map (CommRingCat.ofHom
      ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))) := by
  simp only [jFK, jK, CommRingCat.ofHom_comp, Spec.map_comp]

private theorem TF_eq_fractionRing {V : Type} [CommRing V] [IsDomain V] (F : Type) [Field F] [Algebra (FractionRing V) F] :
    TF (R := V) F = Over.mk (Spec.map (CommRingCat.ofHom
      ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))))) := by
  unfold TF
  rw [jFK_eq_fractionRing]

private theorem valuation_nonneg_of_valOver {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) (e : V) :
    (0 : WithTop ℚ) ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) e)) := by
  rcases eq_or_ne e 0 with rfl | he
  · simp
  · obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible he hϖ
    rw [hv _ (n : ℤ) ⟨u, by rw [map_mul, map_pow, zpow_natCast, mul_comm]⟩]
    exact WithTop.coe_nonneg.2 (by positivity)

private theorem gs_gF_eq_gs_fst_TF {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
    (y : (DegPre.BF D.toPre F).left) (c : F) :
    gs (𝟙 _) y ⊤ (gF D.toPre F c) = gs (fst (TF (R := V) F) D.toPre.P.A).left y ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) := by
  show gs (𝟙 _) y ⊤ ((fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c)) = _
  rw [gs_appTop, Category.id_comp]

private theorem gs_gF_sum_mul_eq_sum_mul_gs_gF {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
    (y : (DegPre.BF D.toPre F).left) {n : ℕ} (x z : Fin n → F) :
    gs (𝟙 _) y ⊤ (gF D.toPre F (∑ i, x i * z i)) =
      ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (x i)) * gs (𝟙 _) y ⊤ (gF D.toPre F (z i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, SectionScalarValuation.gs_sum (𝟙 _) y ⊤ trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, gs_mul (𝟙 _) y ⊤ trivial]

theorem main : TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (k : ℕ), 1 ≤ k → ∀ α : D.toPre.X, ∃ b : Fin (k ^ D.toPre.P.g) → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k)), (∀ s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k)), ∃! a : Fin (k ^ D.toPre.P.g) → F, ∀ j, s.f j = ∑ i, DegPre.constBF D.toPre F (a i) _ * (b i).f j) ∧ ∀ (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) (a : Fin (k ^ D.toPre.P.g) → F), (∀ j, s.f j = ∑ i, DegPre.constBF D.toPre F (a i) _ * (b i).f j) → ∀ r : ℚ, VGe D F v k α s r ↔ ∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (a i) := by
  intro hT V _ _ _ ϖ hϖ D F _ _ v hv k hk α
  obtain ⟨m, b₀, hm, hb⟩ := hT V D.toPre k hk α
  subst hm
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  have hbF := hb F ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))
  rw [← TF_eq_fractionRing (V := V) F] at hbF
  obtain ⟨b, hbB, hbv⟩ := exists_basis_of_eq b₀
    (hbF (fun i => DVR.pullSec D.toPre.P.L (D.toPre.famφB α) (DegPre.famε k) (b₀ i)
      (snd (TF (R := V) F) D.toPre.P.A).left) (fun i j => rfl))
    (DegPre.famφ D.toPre F α) (famφ_eq_snd_TF D F α)
  have coord : ∀ s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k)),
      ∃! a : Fin (k ^ D.toPre.P.g) → F, ∀ j, s.f j = ∑ i, DegPre.constBF D.toPre F (a i) _ * (b i).f j := by
    intro s
    obtain ⟨c, hc, hu⟩ := hbB s
    refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom (c i), fun j => ?_, fun a ha => ?_⟩
    · rw [hc j]
      simp [DegPre.constBF]
    · have e := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i)) (fun j => by rw [ha j]; rfl)
      funext i
      rw [← e]
      simp
  refine ⟨b, coord, fun s a ha r => ⟨fun hs => ?_, fun hr => ⟨_, a, b₀, b,
    fun i => secScal_of_sval hL (fun y J hJ => (hbv i _ (𝟙 _) y J hJ).symm), hr, ha⟩⟩⟩
  obtain ⟨n, a', σ, σF, hsc, hr, hsum⟩ := hs
  have hb0 := hb V (RingHom.id V) (fun l => DVR.pullSec D.toPre.P.L (D.toPre.famφB α) (DegPre.famε k) (b₀ l)
    (snd (Over.mk (Spec.map (CommRingCat.ofHom (RingHom.id V)))) D.toPre.P.A).left) (fun i j => rfl)
  choose d hd _ using fun i => hb0 (DVR.pullSec D.toPre.P.L (D.toPre.famφB α) (DegPre.famε k) (σ i)
    (snd (Over.mk (Spec.map (CommRingCat.ofHom (RingHom.id V)))) D.toPre.P.A).left)
  let u : TF (R := V) F ⟶ Over.mk (Spec.map (CommRingCat.ofHom (RingHom.id V))) :=
    Over.homMk (jFK (R := V) F ≫ jK V) (by
      show _ ≫ Spec.map (CommRingCat.ofHom (RingHom.id V)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
      rfl)
  let g := (lift (fst (TF (R := V) F) D.toPre.P.A ≫ u) (snd (TF (R := V) F) D.toPre.P.A)).left
  have hg2 : g ≫ (snd (Over.mk (Spec.map (CommRingCat.ofHom (RingHom.id V)))) D.toPre.P.A).left =
      (snd (TF (R := V) F) D.toPre.P.A).left := by
    rw [← Over.comp_left, lift_snd]
  have hg1 : g ≫ (fst (Over.mk (Spec.map (CommRingCat.ofHom (RingHom.id V)))) D.toPre.P.A).left =
      (fst (TF (R := V) F) D.toPre.P.A).left ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))) := by
    rw [← Over.comp_left, lift_fst, Over.comp_left, ← jFK_eq_fractionRing]
    rfl
  let fK := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  let e : Fin n → Fin (k ^ D.toPre.P.g) → V := fun i l => (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (d i l)
  have hσ : ∀ i y J, Good D.toPre.P.L y J → sval (σF i) (𝟙 _) y J =
      ∑ l, gs (𝟙 _) y ⊤ (gF D.toPre F (fK (e i l))) * sval (b l) (𝟙 _) y J := by
    intro i y J hJ
    rw [← secScal_sval (hsc i) (𝟙 _) y hJ]
    have h1 : 𝟙 _ ≫ (DegPre.prB D.toPre F).left =
        g ≫ (snd (Over.mk (Spec.map (CommRingCat.ofHom (RingHom.id V)))) D.toPre.P.A).left := by
      rw [Category.id_comp, hg2]
    rw [h1, ← sval_pullSec _ _ (σ i) _ g y hJ,
      sval_lin (fun l => (fst (Over.mk (Spec.map (CommRingCat.ofHom (RingHom.id V)))) D.toPre.P.A).left.appTop.hom
        (d i l)) _ (hd i) g y hJ]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    · rw [gs_appTop, hg1, ← gs_appTop, specMap_appTop, gs_gF_eq_gs_fst_TF]
    · rw [sval_pullSec _ _ (b₀ l) _ g y hJ, hg2, ← Category.id_comp (snd (TF (R := V) F) D.toPre.P.A).left]
      exact (hbv l _ (𝟙 _) y J hJ).symm
  have hsv : ∀ y J, Good D.toPre.P.L y J → sval s (𝟙 _) y J =
      ∑ l, gs (𝟙 _) y ⊤ (gF D.toPre F (∑ i, a' i * fK (e i l))) * sval (b l) (𝟙 _) y J := by
    intro y J hJ
    rw [sval_lin (fun i => gF D.toPre F (a' i)) σF (fun j => by rw [hsum j]; rfl) (𝟙 _) y hJ]
    simp only [hσ _ y J hJ, gs_gF_sum_mul_eq_sum_mul_gs_gF, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hs2 : ∀ j, s.f j = ∑ l, DegPre.constBF D.toPre F (∑ i, a' i * fK (e i l)) _ * (b l).f j := by
    intro j
    rw [lin_of_sval hL _ _ hsv j]
    rfl
  rw [(coord s).unique ha hs2]
  intro l
  apply AddValuation.map_le_sum
  intro i _
  rw [AddValuation.map_mul]
  calc ((r : ℚ) : WithTop ℚ) = (r : WithTop ℚ) + 0 := (add_zero _).symm
    _ ≤ v (a' i) + v (fK (e i l)) := add_le_add (hr i) (valuation_nonneg_of_valOver hϖ hv _)

end GlobalTheory.IntegralCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThickDiv

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem resTop_scal {V : Type} [CommRing V] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of V)) (W : Y.Opens) (a : V) :
    Out.resTop W (scal p a) = constFn p W a := rfl

theorem thick_appTop {V : Type} [CommRing V] (I : Ideal V) (e : ℕ) (a : V) :
    (thick V I e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ I ^ (e + 1)))).inv.hom (Ideal.Quotient.mk (I ^ (e + 1)) a) := by
  have h := congrArg (fun g => g.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  exact h.symm

theorem app_constFn_eq_zero {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) (e : ℕ)
    (X : Over (Spec (CommRingCat.of V))) (W : X.left.Opens) {a : V} (ha : a ∈ I ^ (e + 1)) :
    ((fstG I e X).left.app W).hom (constFn X.hom W a) = 0 := by
  have h0 : ((thick V I e).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) = 0 := by
    rw [thick_appTop, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hc := congrArg (fun φ => (φ.appLE ⊤ ((pullback.fst X.hom (thick V I e)) ⁻¹ᵁ W) (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)) (pullback.condition (f := X.hom) (g := thick V I e))
  have h1 : ((pullback.snd X.hom (thick V I e) ≫ thick V I e).appLE ⊤
      ((pullback.fst X.hom (thick V I e)) ⁻¹ᵁ W) (by simp)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) = 0 := by
    change ((pullback X.hom (thick V I e)).presheaf.map _).hom
      (((pullback.snd X.hom (thick V I e)).app _).hom
        (((thick V I e).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a))) = 0
    rw [h0, map_zero, map_zero]
  have hn := congrArg (fun φ => φ.hom ((X.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)))
    ((pullback.fst X.hom (thick V I e)).naturality (homOfLE (show W ≤ X.hom ⁻¹ᵁ ⊤ by simp)).op)
  exact hn.trans (hc.trans h1)

private theorem ker_thick_appTop_le_span_pow_succ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) (e : ℕ) :
    RingHom.ker (thick V (maximalIdeal V) e).appTop.hom ≤
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom (ϖ ^ (e + 1))} := by
  intro x hx
  obtain ⟨b, rfl⟩ : ∃ b, (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b = x :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom x, by simp⟩
  rw [RingHom.mem_ker, thick_appTop] at hx
  have hb : Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)) b = 0 := by
    simpa using congrArg (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ maximalIdeal V ^ (e + 1)))).hom.hom hx
  rw [Ideal.Quotient.eq_zero_iff_mem, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hb
  obtain ⟨c, rfl⟩ := hb
  exact Ideal.mem_span_singleton.2 ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom c, map_mul _ _ _⟩

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem dvd_of_app_eq_zero_of_isAffineOpen (hϖ : Irreducible ϖ) (X : Over (Spec (CommRingCat.of V))) [Flat X.hom]
    (e : ℕ) {U : X.left.Opens} (hU : IsAffineOpen U) (f : Γ(X.left, U))
    (hf : ((fstG (maximalIdeal V) e X).left.app U).hom f = 0) : constFn X.hom U (ϖ ^ (e + 1)) ∣ f := by
  have hm := GlobalTheory.ProperFunctions.mem_map_ker_of_app_eq_zero
    (IsPullback.of_hasPullback X.hom (thick V (maximalIdeal V) e)) hU f hf
  have hm2 := Ideal.map_mono (ker_thick_appTop_le_span_pow_succ hϖ e) hm
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hm2
  exact hm2

theorem cst_dvd_gs_of_app_eq_zero (hϖ : Irreducible ϖ) (X : Over (Spec (CommRingCat.of V))) [Flat X.hom]
    (e : ℕ) (W : X.left.Opens) (f : Γ(X.left, W))
    (hf : ((fstG (maximalIdeal V) e X).left.app W).hom f = 0) (x : X.left) (hx : x ∈ W) :
    cst X.hom x (ϖ ^ (e + 1)) ∣ gs (𝟙 X.left) x W f := by
  obtain ⟨U, hU, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.left.isBasis_affineOpens hx
  have hr : ((fstG (maximalIdeal V) e X).left.app U).hom
      ((X.left.presheaf.map (homOfLE hUW).op).hom f) = 0 := by
    have hn := congrArg (fun φ => φ.hom f) ((fstG (maximalIdeal V) e X).left.naturality (homOfLE hUW).op)
    refine hn.trans ?_
    change (_ : _ →+* _) (((fstG (maximalIdeal V) e X).left.app W).hom f) = 0
    rw [hf, map_zero]
  obtain ⟨g, hg⟩ := dvd_of_app_eq_zero_of_isAffineOpen hϖ X e hU _ hr
  have hgerm := gs_appLE (𝟙 X.left) W U hUW (𝟙 X.left) x hxU f
  rw [Category.id_comp] at hgerm
  have hres : (Scheme.Hom.appLE (𝟙 X.left) W U hUW).hom f = (X.left.presheaf.map (homOfLE hUW).op).hom f := rfl
  rw [← hgerm, hres, hg, gs_mul _ _ _ hxU, gs_constFn _ _ _ _ hxU, Category.id_comp]
  exact dvd_mul_right _ _

theorem app_eq_zero_iff (hϖ : Irreducible ϖ) (X : Over (Spec (CommRingCat.of V))) [Flat X.hom]
    (e : ℕ) (W : X.left.Opens) (f : Γ(X.left, W)) :
    ((fstG (maximalIdeal V) e X).left.app W).hom f = 0 ↔
      ∃ g : Γ(X.left, W), f = Out.resTop W (scal X.hom (ϖ ^ (e + 1))) * g := by
  rw [resTop_scal]
  constructor
  · intro hf
    exact exists_div X.hom (pow_ne_zero _ hϖ.ne_zero) W f
      (fun x hx => cst_dvd_gs_of_app_eq_zero hϖ X e W f hf x hx)
  · rintro ⟨g, rfl⟩
    rw [map_mul, app_constFn_eq_zero (maximalIdeal V) e X W
      (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) _), zero_mul]

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (X : Over (Spec (CommRingCat.of V))) [Flat X.hom] (N : LB X.left) (σ : LB.Sec N) (e : ℕ), (∀ j, ((fstG (maximalIdeal V) e X).left.app _).hom (σ.f j) = 0) ↔ ∃ τ : LB.Sec N, SecIsMul X.hom (ϖ ^ (e + 1)) σ τ := by
  intro V _ _ _ ϖ hϖ X _ N σ e
  constructor
  · intro h
    obtain ⟨τ, hτ⟩ := exists_div_sec X.hom (pow_ne_zero (e + 1) hϖ.ne_zero) σ
      (fun j x hx => cst_dvd_gs_of_app_eq_zero hϖ X e (N.U j) (σ.f j) (h j) x hx)
    exact ⟨τ, fun j => by rw [hτ j, resTop_scal]⟩
  · rintro ⟨τ, hτ⟩ j
    exact (app_eq_zero_iff hϖ X e (N.U j) (σ.f j)).2 ⟨τ.f j, hτ j⟩

end GlobalTheory.ThickDiv
end
