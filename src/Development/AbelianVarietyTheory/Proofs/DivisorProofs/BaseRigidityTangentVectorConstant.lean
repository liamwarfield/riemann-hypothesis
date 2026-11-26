module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNsmulEqOfEqClosedPointDualNumbers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNsmulEqOfEqClosedPointDualNumbers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem eq_of_pow_eq_of_eq_at_closed : ∀ (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → ∀ x x' : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B, x ^ n = x' ^ n → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x'.left → x = x' := by
  intro k _ B _ hB n hn x x' hpow h0
  haveI : IsCommMonObj B := hB.comm
  haveI hloc : IsLocalRing (DualNumber k) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, isUnit_iff_ne_zero]
    by_cases ha : a.fst = 0
    · right; rw [ha, sub_zero]; exact one_ne_zero
    · left; exact ha
  have hnD : IsUnit (n : DualNumber k) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_natCast]
    exact hn.isUnit
  have hnΓ : IsUnit (n : Γ(Sp (DualNumber k), ⊤)) := by
    simpa using hnD.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
  haveI : PreconnectedSpace (Sp (DualNumber k)) := by
    have : PreconnectedSpace (PrimeSpectrum (DualNumber k)) := by
      refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint (DualNumber k)) fun y _ =>
        ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
      exact (IsLocalRing.specializes_closedPoint y).mem_closure
    exact this
  haveI : PreconnectedSpace (𝟙_ (Over (Sp (DualNumber k)))).left := ‹PreconnectedSpace (Sp (DualNumber k))›
  let T : Over (Sp (DualNumber k)) := Over.mk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
  haveI : Nonempty T.left := inferInstanceAs (Nonempty (Sp k))
  have hw : (x * x'⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hpow, mul_inv_cancel]
  obtain ⟨C, hC, hz⟩ := GlobalTheory.TorsionCover.exists_clopen_eq_one B hB hnΓ (x * x'⁻¹) hw
  have hT : toUnit T ≫ x = toUnit T ≫ x' := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, GlobalTheory.ObjPull.toUnit_left']
    exact h0
  have h1 : toUnit T ≫ (x * x'⁻¹) = 1 := by
    show (preHom (toUnit T)) (x * x'⁻¹) = 1
    rw [map_mul, map_inv]
    show (toUnit T ≫ x) * (toUnit T ≫ x')⁻¹ = 1
    rw [hT, mul_inv_cancel]
  have hsub := (hz T (toUnit T)).1 h1
  obtain ⟨p⟩ := ‹Nonempty T.left›
  have hne : C.Nonempty := ⟨_, hsub ⟨p, rfl⟩⟩
  have huniv : C = Set.univ := hC.eq_univ hne
  have h2 : 𝟙 _ ≫ (x * x'⁻¹) = 1 := (hz _ (𝟙 _)).2 (by rw [huniv]; exact Set.subset_univ _)
  rw [Category.id_comp] at h2
  exact mul_inv_eq_one.1 h2

end GlobalTheory.UCanon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNsmulEqOfEqClosedPointDualNumbersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_nsmul_eq_of_eq_closedPoint_dualNumbers : ∀ (k : Type) [Field k] (B : Over (Sp (DualNumber k))) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : k) ≠ 0 → ∀ x x' : 𝟙_ (Over (Sp (DualNumber k))) ⟶ B, x ^ n = x' ^ n → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x'.left → x = x' := by
  first | exact @GlobalTheory.UCanon.eq_of_pow_eq_of_eq_at_closed | exact GlobalTheory.UCanon.eq_of_pow_eq_of_eq_at_closed | (intros; apply GlobalTheory.UCanon.eq_of_pow_eq_of_eq_at_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjectMapsOfDualNumberIdentifications
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberTorsionSectionLiesOverSecondMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberTorsionSectionLiesOverSecondMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UCanon

theorem torsion_sec_over_second : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₁ g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₁ = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₂ → ∀ (n : ℕ), (n : k) ≠ 0 → ∀ (σ : 𝟙_ (Over S) ⟶ G), σ ^ n = 1 → ∀ (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ G'), x ^ n = 1 → x.left ≫ φ₁ = g₁ ≫ σ.left → x.left ≫ φ₂ = g₂ ≫ σ.left := by
  intro k _ S G' _ hab G _ g₁ g₂ φ₁ φ₂ h₂ h0 hg n hn σ hσ x hx hx₁
  let T := 𝟙_ (Over (Sp (DualNumber k)))
  have hsq : ∀ y : T ⟶ G', (y.left ≫ φ₂) ≫ G.hom = T.hom ≫ g₂ := by
    intro y
    rw [Category.assoc, h₂.1.w, ← Category.assoc, Over.w y]
  let ψ : (T ⟶ G') → (Over.mk (T.hom ≫ g₂) ⟶ G) := fun y => Over.homMk (y.left ≫ φ₂) (hsq y)
  have ψmul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    apply Over.OverMorphism.ext
    exact (h₂.2 T a b (ψ a) (ψ b) rfl rfl).symm
  let Ψ : (T ⟶ G') →* (Over.mk (T.hom ≫ g₂) ⟶ G) := MonoidHom.mk' ψ ψmul
  have Ψinj : ∀ a b : T ⟶ G', Ψ a = Ψ b → a = b := by
    intro a b hab'
    apply Over.OverMorphism.ext
    exact h₂.1.hom_ext (congrArg CommaMorphism.left hab') (by rw [Over.w a, Over.w b])
  have hw : (g₂ ≫ σ.left) ≫ G.hom = 𝟙 (Sp (DualNumber k)) ≫ g₂ := by
    rw [Category.assoc, Over.w σ]; simp
  let x' : T ⟶ G' := Over.homMk (h₂.1.lift (g₂ ≫ σ.left) (𝟙 _) hw) (by simp [T])
  have hx'φ : x'.left ≫ φ₂ = g₂ ≫ σ.left := h₂.1.lift_fst _ _ _
  let u : Over.mk (T.hom ≫ g₂) ⟶ 𝟙_ (Over S) := toUnit _
  have hu : u.left = g₂ := by
    have := Over.w u
    simpa [T] using this
  have hΨx' : Ψ x' = u ≫ σ := by
    apply Over.OverMorphism.ext
    show x'.left ≫ φ₂ = u.left ≫ σ.left
    rw [hx'φ, hu]
  have hpow : ∀ m : ℕ, u ≫ σ ^ m = (u ≫ σ) ^ m := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
    | succ m ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]
  have hx'n : x' ^ n = 1 := by
    apply Ψinj
    rw [map_pow, map_one, hΨx', ← hpow, hσ, MonObj.comp_one]
  have hb : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x'.left := by
    apply h₂.1.hom_ext
    · have h1 := h0 (Sp k) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x.left) (𝟙 _)
        (by rw [Category.assoc, Over.w x]; simp [T])
      rw [← h1, Category.assoc, Category.assoc, hx₁, ← Category.assoc, hg, Category.assoc, hx'φ]
    · rw [Category.assoc, Category.assoc, Over.w x, Over.w x']
  have key := GlobalTheory.T.eq_of_nsmul_eq_of_eq_closedPoint_dualNumbers k G' hab n hn x x' (by rw [hx, hx'n]) hb
  rw [key]
  exact hx'φ

end GlobalTheory.UCanon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberTorsionSectionLiesOverSecondMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumber_torsionSection_lies_over_second_map : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₁ g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₁ = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₂ → ∀ (n : ℕ), (n : k) ≠ 0 → ∀ (σ : 𝟙_ (Over S) ⟶ G), σ ^ n = 1 → ∀ (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ G'), x ^ n = 1 → x.left ≫ φ₁ = g₁ ≫ σ.left → x.left ≫ φ₂ = g₂ ≫ σ.left := by
  first | exact @GlobalTheory.UCanon.torsion_sec_over_second | exact GlobalTheory.UCanon.torsion_sec_over_second | (intros; apply GlobalTheory.UCanon.torsion_sec_over_second <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesOfCommutesDualNumberAgreeClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesOfCommutesDualNumberAgreeClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EpsRigid

theorem fst_ker_le_nilradical (k : Type) [Field k] :
    RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom ≤ nilradical (DualNumber k) := by
  intro x hx
  have h0 : TrivSqZeroExt.fst x = 0 := hx
  have hx' : x = TrivSqZeroExt.inr (TrivSqZeroExt.snd x) := by
    ext
    · simp [h0]
    · simp
  rw [mem_nilradical]
  refine ⟨2, ?_⟩
  rw [pow_two, hx', TrivSqZeroExt.inr_mul_inr]

theorem quot_mk_eq (k : Type) [Field k] :
    ∃ e : k →+* DualNumber k ⧸ RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom,
      Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) = e.comp (TrivSqZeroExt.fstHom k k k).toRingHom := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, by simp⟩
  refine ⟨(RingHom.quotientKerEquivOfSurjective hs).symm.toRingHom, ?_⟩
  refine RingHom.ext fun x => ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [RingEquiv.eq_symm_apply]
  rfl

theorem comm_of_comm :
    ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → ∀ (u : G' ⟶ G') [IsMonHom u] (v : G ⟶ G) [IsMonHom v], u.left ≫ φ₁ = φ₁ ≫ v.left → u.left ≫ φ₂ = φ₂ ≫ v.left := by
  intro k _ S G' _ hG G _ g₂ φ₁ φ₂ h₂ h0 u _ v _ hu
  have hsq : (φ₂ ≫ v.left) ≫ G.hom = G'.hom ≫ g₂ := by
    rw [Category.assoc, Over.w v, h₂.1.w]
  let w : G' ⟶ G' := Over.homMk (h₂.1.lift (φ₂ ≫ v.left) G'.hom hsq) (h₂.1.lift_snd _ _ _)
  have hw : w.left ≫ φ₂ = φ₂ ≫ v.left := h₂.1.lift_fst _ _ _
  suffices huw : u = w by rw [huw, hw]
  obtain ⟨e, he⟩ := quot_mk_eq k
  have hsp : spMap (Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom)) =
      spMap e ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := by
    rw [he, spMap, spMap, spMap, ← Spec.map_comp]
    rfl
  refine GlobalTheory.NilRigidity.eq_of_eq_on_quotient _ (fst_ker_le_nilradical k) G' G' hG u w ?_ ?_
  · have hj : ∀ x : pullback G'.hom (spMap (Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom))) ⟶ G'.left,
        x ≫ G'.hom = pullback.fst G'.hom (spMap (Ideal.Quotient.mk (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom))) ≫ G'.hom →
        x ≫ φ₁ = x ≫ φ₂ := by
      intro x hx
      refine h0 _ x (pullback.snd _ _ ≫ spMap e) ?_
      rw [hx, pullback.condition, Category.assoc, hsp]
    apply h₂.1.hom_ext
    · have a1 := hj (pullback.fst _ _ ≫ u.left) (by rw [Category.assoc, Over.w u])
      have a2 := hj (pullback.fst _ _) rfl
      simp only [Category.assoc] at a1 a2 ⊢
      rw [hw, ← a1, hu, ← Category.assoc, a2, Category.assoc]
    · rw [Category.assoc, Category.assoc, Over.w u, Over.w w]
  · rw [IsMonHom.one_hom]
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    apply h₂.1.hom_ext
    · rw [Category.assoc, hw, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h₂,
        Category.assoc, ← Over.comp_left, IsMonHom.one_hom]
    · rw [Category.assoc, Over.w w]

end GlobalTheory.EpsRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesOfCommutesDualNumberAgreeClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutes_of_commutes_dualNumber_agree_closed : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → ∀ (u : G' ⟶ G') [IsMonHom u] (v : G ⟶ G) [IsMonHom v], u.left ≫ φ₁ = φ₁ ≫ v.left → u.left ≫ φ₂ = φ₂ ≫ v.left := by
  first | exact @GlobalTheory.EpsRigid.comm_of_comm | exact GlobalTheory.EpsRigid.comm_of_comm | (intros; apply GlobalTheory.EpsRigid.comm_of_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjectMapsOfDualNumberIdentifications
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.EpsObj

theorem act_comm_eps : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → ∀ (u : G' ⟶ G') [IsMonHom u] (v : G ⟶ G) [IsMonHom v], u.left ≫ φ₁ = φ₁ ≫ v.left → u.left ≫ φ₂ = φ₂ ≫ v.left := GlobalTheory.T.commutes_of_commutes_dualNumber_agree_closed

theorem sec_eps : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₁ g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₁ = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ g₂ → ∀ (n : ℕ), (n : k) ≠ 0 → ∀ (σ : 𝟙_ (Over S) ⟶ G), σ ^ n = 1 → ∀ (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ G'), x ^ n = 1 → x.left ≫ φ₁ = g₁ ≫ σ.left → x.left ≫ φ₂ = g₂ ≫ σ.left := GlobalTheory.T.dualNumber_torsionSection_lies_over_second_map

theorem spMap_comp_eps {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem eta_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) (n : ℕ) :
    p.eta a ^ n = p.eta (n • a) := by
  induction n with
  | zero =>
    have h := p.eta_add 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | succ n ih => rw [pow_succ, ih, succ_nsmul, p.eta_add]

theorem etaA_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) (n : ℕ) :
    p.etaA a ^ n = p.etaA (n • a) := by
  induction n with
  | zero =>
    have h := p.etaA_add 0 0
    rw [add_zero] at h
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)).symm
  | succ n ih => rw [pow_succ, ih, succ_nsmul, p.etaA_add]

theorem eta_pow_M {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) :
    p.eta a ^ l.M = 1 := by
  rw [eta_pow]
  apply p.eta_ker
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at this
    first | exact Ideal.mul_le_left this | exact Ideal.mul_le_right this
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hM Submodule.mem_top

theorem etaA_pow_A {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {bb : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (p : Obj D l bb s) (a : D.La) :
    p.etaA a ^ l.A = 1 := by
  rw [etaA_pow]
  exact p.etaA_ker a

theorem exists_objMaps : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (W : Type) [CommRing W] (b : c.F →+* W) (o : LowObj D' c b) (k : Type) [Field k] (f : W →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ o.t.G.left), IsGrpPullback B' o.t.G (spMap f) π₁ → IsGrpPullback B' o.t.G (spMap (GlobalTheory.RigChart.constHom f)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → LBIso (o.t.PP.L.pull π₁) (o.t.PP.L.pull π₂) → ∃ (o' : LowObj D' c (f.comp b)) (m₁ : ObjMap o' o (spMap f)) (m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f))) (io : o'.t.G.left ≅ B'.left), io.hom ≫ B'.hom = o'.t.G.hom ∧ m₁.toSABMap.φ = io.hom ≫ π₁ ∧ m₂.toSABMap.φ = io.hom ≫ π₂ := by
  intro E _ _ _ H D' l c W _ b o k _ f B' _ π₁ π₂ h₁ h₂ h0 hL
  have hlow : lowMap c (f.comp b) = spMap f ≫ lowMap c b := by
    unfold lowMap
    rw [RingHom.comp_assoc, spMap_comp_eps]
  obtain ⟨o', ⟨m₀⟩⟩ : ∃ o' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (lowMap c (f.comp b)),
      Nonempty (ObjMap o' o (spMap f)) := by
    rw [hlow]
    exact GlobalTheory.LevelGroup.pull_univ o (spMap f)
  let io : o'.t.G.left ≅ B'.left := IsPullback.isoIsPullback _ _ m₀.cart.1 h₁.1
  have io₁ : io.hom ≫ π₁ = m₀.toSABMap.φ := IsPullback.isoIsPullback_hom_fst _ _ _ _
  have io₂ : io.hom ≫ B'.hom = o'.t.G.hom := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have hio : IsGrpPullback o'.t.G B' (𝟙 _) io.hom :=
    IsGrpPullback.cancel h₁ (by rw [Category.id_comp, io₁]; exact m₀.cart) (by rw [io₂, Category.comp_id])
  have hψc : IsGrpPullback o'.t.G o.t.G (spMap (GlobalTheory.RigChart.constHom f)) (io.hom ≫ π₂) := by
    have := hio.comp h₂
    rwa [Category.id_comp] at this
  have h0' : ∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k),
      x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
        x ≫ m₀.toSABMap.φ = x ≫ io.hom ≫ π₂ := by
    intro Z x y hx
    rw [← io₁, ← Category.assoc, ← Category.assoc]
    exact h0 Z (x ≫ io.hom) y (by rw [Category.assoc, io₂, hx])
  have hA' : IsAbelianScheme o'.t.G :=
    ⟨o'.t.semi.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  have hact : ∀ a, (o'.t.act.act a).left ≫ io.hom ≫ π₂ = (io.hom ≫ π₂) ≫ (o.t.act.act a).left := fun a => by
    haveI := o'.t.act.hom a
    haveI := o.t.act.hom a
    exact act_comm_eps k o'.t.G hA' o.t.G _ _ _ hψc h0' (o'.t.act.act a) (o.t.act.act a) (m₀.act a)
  have hLB : LBIso o'.t.PP.L (o.t.PP.L.pull (io.hom ≫ π₂)) := by
    obtain ⟨w, hw, -⟩ := m₀.lin
    have e₁ : LBIso o'.t.PP.L (o.t.PP.L.pull (io.hom ≫ π₁)) := by
      rw [io₁]
      exact ⟨w, hw⟩
    have e₂ : LBIso (o.t.PP.L.pull (io.hom ≫ π₁)) (o.t.PP.L.pull (io.hom ≫ π₂)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp io.hom rfl rfl hL
    exact LBIso.trans o'.t.PP.isLB (pull_isLB o.t.PP.isLB _) (pull_isLB o.t.PP.isLB _) e₁ e₂
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_sabMap_of_grpPullback_respecting_action_bundle o'.t o.t (spMap (GlobalTheory.RigChart.constHom f)) (io.hom ≫ π₂) o.proper hψc hact hLB
  have hg : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap f =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (GlobalTheory.RigChart.constHom f) := by
    rw [← spMap_comp_eps, ← spMap_comp_eps]
    congr 1
  have hunit : ∀ n : ℕ, 0 < n → (n : k) ≠ 0 := by
    intro n hn
    have := ((baseKA (LowDat.lowLevel l)).unit n hn).map
      (((TrivSqZeroExt.fstHom k k k).toRingHom.comp (f.comp b)).comp
        (IntermediateField.inclusion (LowDat.ka_le l c)).toRingHom)
    rw [map_natCast] at this
    exact this.ne_zero
  have hsec : ∀ (σ : 𝟙_ (Over (Sp W)) ⟶ o.t.G) (x : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G) (n : ℕ), 0 < n →
      σ ^ n = 1 → x ^ n = 1 → x.left ≫ m₀.toSABMap.φ = spMap f ≫ σ.left →
        x.left ≫ io.hom ≫ π₂ = spMap (GlobalTheory.RigChart.constHom f) ≫ σ.left :=
    fun σ x n hn hσ hx hx₁ => sec_eps k o'.t.G hA' o.t.G _ _ _ _ hψc h0' hg n (hunit n hn) σ hσ x hx hx₁
  have hMpos : 0 < (LowDat.lowLevel l).M := by have := (LowDat.lowLevel l).three_le; omega
  let m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f)) :=
    { toSABMap := m
      eta := fun a => by
        show (o'.eta a).left ≫ m.φ = _
        rw [hm]
        exact hsec _ _ _ hMpos (eta_pow_M o a) (eta_pow_M o' a) (m₀.eta a)
      etaA := fun a => by
        show (o'.etaA a).left ≫ m.φ = _
        rw [hm]
        exact hsec _ _ _ (LowDat.lowLevel l).A_pos (etaA_pow_A o a) (etaA_pow_A o' a) (m₀.etaA a) }
  exact ⟨o', m₀, m₂, io, io₂, io₁.symm, hm⟩

end GlobalTheory.UCanon.EpsObj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjectMapsOfDualNumberIdentificationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_objectMaps_of_dualNumber_identifications : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (W : Type) [CommRing W] (b : c.F →+* W) (o : LowObj D' c b) (k : Type) [Field k] (f : W →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ o.t.G.left), IsGrpPullback B' o.t.G (spMap f) π₁ → IsGrpPullback B' o.t.G (spMap (GlobalTheory.RigChart.constHom f)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → LBIso (o.t.PP.L.pull π₁) (o.t.PP.L.pull π₂) → ∃ (o' : LowObj D' c (f.comp b)) (m₁ : ObjMap o' o (spMap f)) (m₂ : ObjMap o' o (spMap (GlobalTheory.RigChart.constHom f))) (io : o'.t.G.left ≅ B'.left), io.hom ≫ B'.hom = o'.t.G.hom ∧ m₁.toSABMap.φ = io.hom ≫ π₁ ∧ m₂.toSABMap.φ = io.hom ≫ π₂ := by
  first | exact @GlobalTheory.UCanon.EpsObj.exists_objMaps | exact GlobalTheory.UCanon.EpsObj.exists_objMaps | (intros; apply GlobalTheory.UCanon.EpsObj.exists_objMaps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointsPulledBackObjectFromBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointsPulledBackObjectFromBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.EpsPts

variable {S S₀ : Scheme.{0}}

theorem unit_hom (X : Scheme.{0}) : (𝟙_ (Over X)).hom = 𝟙 X := rfl

theorem exists_pt {G : Over S} {G₀ A : Over S₀} {g : S ⟶ S₀} {φ : G.left ⟶ G₀.left} {φB : G₀.left ⟶ A.left}
    (h₁ : IsPullback φ G.hom G₀.hom g) (h₂ : IsPullback φB G₀.hom A.hom (𝟙 S₀)) (a : S₀ ⟶ A.left)
    (ha : a ≫ A.hom = 𝟙 S₀) : ∃ x : S ⟶ G.left, x ≫ φ ≫ φB = g ≫ a ∧ x ≫ G.hom = 𝟙 S := by
  let P := h₂.lift (g ≫ a) g (by rw [Category.assoc, ha, Category.comp_id])
  refine ⟨h₁.lift P (𝟙 S) (by rw [h₂.lift_snd, Category.id_comp]), ?_, h₁.lift_snd _ _ _⟩
  rw [← Category.assoc, h₁.lift_fst, h₂.lift_fst]

theorem pt_unique {G : Over S} {G₀ A : Over S₀} {g : S ⟶ S₀} {φ : G.left ⟶ G₀.left} {φB : G₀.left ⟶ A.left}
    (h₁ : IsPullback φ G.hom G₀.hom g) (h₂ : IsPullback φB G₀.hom A.hom (𝟙 S₀)) {Z : Scheme.{0}} (r : Z ⟶ S)
    (x x' : Z ⟶ G.left) (hφ : x ≫ φ ≫ φB = x' ≫ φ ≫ φB) (hx : x ≫ G.hom = r) (hx' : x' ≫ G.hom = r) : x = x' := by
  apply h₁.hom_ext
  · apply h₂.hom_ext
    · simpa only [Category.assoc] using hφ
    · rw [Category.assoc, Category.assoc, h₁.w, ← Category.assoc, hx, ← Category.assoc, hx']
  · rw [hx, hx']

theorem pow_left {G : Over S} {G₀ A : Over S₀} [GrpObj G] [GrpObj G₀] [GrpObj A] {g : S ⟶ S₀}
    {φ : G.left ⟶ G₀.left} {φB : G₀.left ⟶ A.left}
    (h₁ : IsGrpPullback G G₀ g φ) (h₂ : IsGrpPullback G₀ A (𝟙 S₀) φB) (X : 𝟙_ (Over S) ⟶ G)
    (a : 𝟙_ (Over S₀) ⟶ A) (hX : X.left ≫ φ ≫ φB = g ≫ a.left) (n : ℕ) :
    (X ^ n).left ≫ φ ≫ φB = g ≫ (a ^ n).left := by
  let p₁ := pushHom h₁ (𝟙_ (Over S))
  let p₂ := pushHom h₂ (Over.mk ((𝟙_ (Over S)).hom ≫ g))
  let U : Over.mk (((𝟙_ (Over S)).hom ≫ g) ≫ 𝟙 S₀) ⟶ 𝟙_ (Over S₀) := toUnit _
  have hU : U.left = g := by
    have := Over.w U
    simpa [unit_hom] using this
  have e : p₂ (p₁ X) = preHom U a := by
    apply Over.OverMorphism.ext
    show (X.left ≫ φ) ≫ φB = U.left ≫ a.left
    rw [Category.assoc, hX, hU]
  have e' : p₂ (p₁ (X ^ n)) = preHom U (a ^ n) := by
    rw [map_pow, map_pow, e, map_pow]
  have := congrArg (fun z => z.left) e'
  rw [← Category.assoc]
  refine this.trans ?_
  show U.left ≫ (a ^ n).left = _
  rw [hU]

theorem c_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (y : D.X) (n : ℕ) :
    D.c (n • y) = D.c y ^ n := by
  have hpadd : ∀ a b, D.c (a + b) = D.c a * D.c b := fun a b => by
    rw [D.c_add, Hom.mul_def]; rfl
  induction n with
  | zero =>
    have h := hpadd 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact (mul_eq_left.1 h.symm)
  | succ n ih => rw [succ_nsmul, hpadd, ih, pow_succ]

end GlobalTheory.UCanon.EpsPts

namespace GlobalTheory.UCanon


open GlobalTheory.UCanon.EpsPts in
theorem pts_eps_of_mul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (k : Type) [Field k] (f : L.W →+* DualNumber k) (o' : LowObj D' c (f.comp L.b)) (m₁ : ObjMap o' L.o (spMap f)) (m₂ : ObjMap o' L.o (spMap (GlobalTheory.RigChart.constHom f))) (n : ℕ), (n : k) ≠ 0 → (∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k), x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ) → ∀ u : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, u y ≫ o'.t.G.hom = 𝟙 _) → (∀ y, u y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c (n • y)).left) → (∀ y, u y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c (n • y)).left) → ∃ x : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, x y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ o'.t.G.hom = 𝟙 _) := by
  intro E _ _ _ H D' l c L k _ f o' m₁ m₂ n hn h0 u hu hu₁ hu₂
  have hc : ∀ y, (L.D.c y).left ≫ L.D.P.A.hom = 𝟙 _ := fun y => Over.w (L.D.c y)
  have ex₁ := fun y => exists_pt m₁.cart.1 L.ab.1.1 (L.D.c y).left (hc y)
  have ex₂ := fun y => exists_pt m₂.cart.1 L.ab.1.1 (L.D.c y).left (hc y)
  choose x hx₁ hxG using ex₁
  choose x₂ hx₂ hx₂G using ex₂
  haveI : IsCommMonObj o'.t.G := o'.t.comm
  have hAb : IsAbelianScheme o'.t.G := ⟨o'.t.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  let r : Sp k ⟶ Sp (DualNumber k) := spMap (TrivSqZeroExt.fstHom k k k).toRingHom
  have hr : r ≫ spMap f = r ≫ spMap (GlobalTheory.RigChart.constHom f) := by
    simp only [r, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    all_goals (ext z; simp [GlobalTheory.RigChart.constHom])
  have heq : ∀ y, x y = x₂ y := by
    intro y
    let X : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G := Over.homMk (x y) (hxG y)
    let X₂ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G := Over.homMk (x₂ y) (hx₂G y)
    have hpow : X ^ n = X₂ ^ n := by
      apply Over.OverMorphism.ext
      have e₁ : (X ^ n).left = u y := by
        apply pt_unique m₁.cart.1 L.ab.1.1 (𝟙 _) _ _ _ (Over.w (X ^ n)) (hu y)
        rw [pow_left m₁.cart L.ab.1 X (L.D.c y) (hx₁ y) n, hu₁ y, c_nsmul]
      have e₂ : (X₂ ^ n).left = u y := by
        apply pt_unique m₂.cart.1 L.ab.1.1 (𝟙 _) _ _ _ (Over.w (X₂ ^ n)) (hu y)
        rw [pow_left m₂.cart L.ab.1 X₂ (L.D.c y) (hx₂ y) n, hu₂ y, c_nsmul]
      rw [e₁, e₂]
    have h0' : r ≫ X.left = r ≫ X₂.left := by
      show r ≫ x y = r ≫ x₂ y
      have hh := h0 (Sp k) (r ≫ x₂ y) (𝟙 _) (by rw [Category.assoc, hx₂G, Category.comp_id, Category.id_comp])
      have hh' : r ≫ x₂ y ≫ m₁.cm.F = r ≫ x₂ y ≫ m₂.cm.F := by simpa only [Category.assoc] using hh
      have w₁ : x y ≫ m₁.cm.F ≫ L.o.t.G.hom = spMap f := by
        rw [m₁.cart.1.w, ← Category.assoc, hxG y, Category.id_comp]
      have w₂ : x₂ y ≫ m₂.cm.F ≫ L.o.t.G.hom = spMap (GlobalTheory.RigChart.constHom f) := by
        rw [m₂.cart.1.w, ← Category.assoc, hx₂G y, Category.id_comp]
      apply m₁.cart.1.hom_ext
      · simp only [Category.assoc]
        rw [hh']
        apply L.ab.1.1.hom_ext
        · simp only [Category.assoc]
          rw [hx₁ y, hx₂ y, ← Category.assoc, hr, Category.assoc]
        · simp only [Category.assoc]
          rw [w₁, w₂, hr]
      · simp only [Category.assoc]
        rw [hxG y, hx₂G y]
    exact congrArg (fun z => z.left) (eq_of_pow_eq_of_eq_at_closed k o'.t.G hAb n hn X X₂ hpow h0')
  exact ⟨x, hx₁, fun y => heq y ▸ hx₂ y, hxG⟩

end GlobalTheory.UCanon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointsPulledBackObjectFromBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumber_points_pulledBack_object_from_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (k : Type) [Field k] (f : L.W →+* DualNumber k) (o' : LowObj D' c (f.comp L.b)) (m₁ : ObjMap o' L.o (spMap f)) (m₂ : ObjMap o' L.o (spMap (GlobalTheory.RigChart.constHom f))) (n : ℕ), (n : k) ≠ 0 → (∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k), x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ) → ∀ u : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, u y ≫ o'.t.G.hom = 𝟙 _) → (∀ y, u y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c (n • y)).left) → (∀ y, u y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c (n • y)).left) → ∃ x : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, x y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ o'.t.G.hom = 𝟙 _) := by
  first | exact @GlobalTheory.UCanon.pts_eps_of_mul | exact GlobalTheory.UCanon.pts_eps_of_mul | (intros; apply GlobalTheory.UCanon.pts_eps_of_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseRigidityTangentVectorConstant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigBase

theorem grp_through {S S₁ S₂ : Scheme.{0}} {B' : Over S₂} {Q : Over S₁} {D O : Over S} [GrpObj B'] [GrpObj Q]
    [GrpObj D] [GrpObj O] {g : S₂ ⟶ S} {π : B'.left ⟶ Q.left} {β : Q.left ⟶ D.left} {φB : O.left ⟶ D.left}
    {ρ₁ : S₂ ⟶ S₁} {j : S₁ ⟶ S} (hπ : IsGrpPullback B' Q ρ₁ π) (hβ : IsGrpPullback Q D j β)
    (hφ : IsGrpPullback O D (𝟙 S) φB) (hg : ρ₁ ≫ j = g) :
    ∃ π' : B'.left ⟶ O.left, π' ≫ φB = π ≫ β ∧ π' ≫ O.hom = B'.hom ≫ g ∧ IsGrpPullback B' O g π' := by
  have hc := (hπ.comp hβ).congr hg rfl
  have w : (π ≫ β) ≫ D.hom = (B'.hom ≫ g) ≫ 𝟙 S := by rw [Category.comp_id]; exact hc.1.w
  exact ⟨hφ.1.lift (π ≫ β) (B'.hom ≫ g) w, hφ.1.lift_fst _ _ _, hφ.1.lift_snd _ _ _,
    hφ.cancel (hc.congr (Category.comp_id g).symm (hφ.1.lift_fst _ _ _).symm) (hφ.1.lift_snd _ _ _)⟩

theorem lb_through {X Y Z T : Scheme.{0}} {L₀ : LB X} {L : LB Y} {M : LB Z} (hL₀ : L₀.IsLB) (hL : L.IsLB)
    (hM : M.IsLB) {φB : X ⟶ Y} {β : Z ⟶ Y} {π₁ π₂ : T ⟶ Z} {π₁' π₂' : T ⟶ X} (h₀ : LBIso L₀ (L.pull φB))
    (hβ : LBIso M (L.pull β)) (h : LBIso (M.pull π₁) (M.pull π₂)) (e₁ : π₁' ≫ φB = π₁ ≫ β)
    (e₂ : π₂' ≫ φB = π₂ ≫ β) : LBIso (L₀.pull π₁') (L₀.pull π₂') := by
  have key : ∀ {A : Scheme.{0}} {L' : LB A} {F : A ⟶ Y}, LBIso L' (L.pull F) → ∀ j : T ⟶ A,
      LBIso (L'.pull j) (L.pull (j ≫ F)) := fun H j =>
    LBIso.chartPull (chartPullPull _ _) (chartPullSame L _ _ _ j fun _ => rfl) H
  have a₁ := key h₀ π₁'
  have a₂ := key h₀ π₂'
  have b₁ := key hβ π₁
  have b₂ := key hβ π₂
  rw [e₁] at a₁
  rw [e₂] at a₂
  exact LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL _) (pull_isLB hL₀ _) (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hM _) (pull_isLB hL _)
    (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hM _) (pull_isLB hM _) (LBIso.trans (pull_isLB hL₀ _) (pull_isLB hL _) (pull_isLB hM _) a₁ b₁.symm) h) b₂) a₂.symm

theorem const_on_base : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ _ C Cn k _ ρ a hC
  obtain ⟨B', _, π₁, π₂, w, c', h₁, h₂, h0, hw, hc', -⟩ := hC
  obtain ⟨g, hD, -, hxe, -⟩ := Cn.data
  haveI := hD.e_hom
  have hβ : IsGrpPullback C.P.D.toPre.P.A Cn.L.D.P.A (specOf (Cn.ψ.comp MvPolynomial.C))
      (hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C))) :=
    ((isGrpPullback_of_iso hD.e).comp (isGrpPullback_pullback _ _)).congr (Category.id_comp _) rfl
  have hsp : ∀ ρ' : R →+* DualNumber k, spMap ρ' ≫ specOf (Cn.ψ.comp MvPolynomial.C) = spMap (ρ'.comp (Cn.ψ.comp MvPolynomial.C)) := fun ρ' => by
    rw [← Spec.map_comp]; rfl
  obtain ⟨π₁', e₁, w₁, g₁⟩ := grp_through h₁ hβ Cn.L.ab.1 (hsp ρ)
  obtain ⟨π₂', e₂, w₂, g₂⟩ := grp_through h₂ hβ Cn.L.ab.1
    (hsp _ : _ = spMap (GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C))))
  have hfst : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (ρ.comp (Cn.ψ.comp MvPolynomial.C)) =
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C))) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have agree : ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k),
      x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁' = x ≫ π₂' := by
    intro Z x y hx
    apply Cn.L.ab.1.1.hom_ext
    · rw [Category.assoc, Category.assoc, e₁, e₂, ← Category.assoc, ← Category.assoc, h0 Z x y hx]
    · rw [Category.assoc, Category.assoc, w₁, w₂, ← Category.assoc, ← Category.assoc, hx, Category.assoc,
        Category.assoc, hfst]
  obtain ⟨w₀, hw₀⟩ := Cn.L.ab.2.2
  have hLB : LBIso (Cn.L.o.t.PP.L.pull π₁') (Cn.L.o.t.PP.L.pull π₂') :=
    lb_through Cn.L.o.t.PP.isLB Cn.L.D.P.isLB C.P.D.toPre.P.isLB ⟨w₀, hw₀⟩ ⟨hD.w, hD.w_gen⟩ ⟨w, hw⟩ e₁ e₂
  obtain ⟨o', m₁, m₂, io, hio, hm₁, hm₂⟩ :=
    GlobalTheory.T.exists_objectMaps_of_dualNumber_identifications c Cn.L.W Cn.L.b Cn.L.o k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) B' π₁' π₂' g₁ g₂ agree hLB
  have hn : ((l.M' : ℕ) : k) ≠ 0 := by
    intro h0'
    have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
    have hk : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ((ρ.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b))
        (l.M' : c.F) = 0 := by rw [map_natCast]; exact h0'
    rw [map_eq_zero_iff _ (RingHom.injective _)] at hk
    exact hM (by exact_mod_cast hk)
  have agree' : ∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k),
      x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom →
        x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ := by
    intro Z x y hx
    rw [hm₁, hm₂, ← Category.assoc, ← Category.assoc]
    exact agree Z _ y (by rw [Category.assoc, hio, hx])
  have hinv : io.inv ≫ o'.t.G.hom = B'.hom := by rw [← hio, Iso.inv_hom_id_assoc]
  have hc : ∀ y, (C.P.D.toPre.c (Cn.e.symm y)).left ≫ hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C)) =
      specOf (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • y)).left := fun y => by
    have := hD.c_pr (Cn.e.symm y)
    rw [hxe, LinearEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨x, hx₁, hx₂, hx₀⟩ := GlobalTheory.T.dualNumber_points_pulledBack_object_from_base Cn.L k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) o' m₁ m₂ l.M' hn agree'
    (fun y => c' (Cn.e.symm y) ≫ io.inv)
    (fun y => by rw [Category.assoc, hinv, (hc' _).1])
    (fun y => by
      rw [hm₁]; simp only [Category.assoc, Iso.inv_hom_id_assoc]; rw [e₁, ← Category.assoc, (hc' _).2.1, Category.assoc, hc,
        ← Category.assoc, hsp])
    (fun y => by
      rw [hm₂]; simp only [Category.assoc, Iso.inv_hom_id_assoc]; rw [e₂, ← Category.assoc, (hc' _).2.2, Category.assoc, hc,
        ← Category.assoc, hsp]; rfl)
  exact Cn.L.fineEps k (ρ.comp (Cn.ψ.comp MvPolynomial.C)) o' m₁ m₂ x hx₁ hx₂ hx₀

end GlobalTheory.RigBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseRigidityTangentVectorConstantStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_rigidity_tangent_vector_constant : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k) (a : Fin C.m → k), GlobalTheory.RigChart.IsConstAlong C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ρ a → ρ.comp (Cn.ψ.comp MvPolynomial.C) = GlobalTheory.RigChart.constHom (ρ.comp (Cn.ψ.comp MvPolynomial.C)) := by
  first | exact @GlobalTheory.RigBase.const_on_base | exact GlobalTheory.RigBase.const_on_base | (intros; apply GlobalTheory.RigBase.const_on_base <;> assumption)
end
