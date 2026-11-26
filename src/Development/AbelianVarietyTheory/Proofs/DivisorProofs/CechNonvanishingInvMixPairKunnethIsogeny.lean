module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiMapFst
set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGen

def psiMap {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (a₁ b₁ a₂ b₂ : ℤ) : A ⊗ A ⟶ A ⊗ A :=
  lift (fst A A ^ a₁ * snd A A ^ b₁) (fst A A ^ a₂ * snd A A ^ b₂)

theorem psiMap_fst {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (a₁ b₁ a₂ b₂ : ℤ) :
    psiMap A a₁ b₁ a₂ b₂ ≫ fst A A = fst A A ^ a₁ * snd A A ^ b₁ := lift_fst _ _

theorem psiMap_snd {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (a₁ b₁ a₂ b₂ : ℤ) :
    psiMap A a₁ b₁ a₂ b₂ ≫ snd A A = fst A A ^ a₂ * snd A A ^ b₂ := lift_snd _ _

end GlobalTheory.AmpleGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowEqMumfordFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowEqMumfordFormula
set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowPull

theorem tri_succ (n : ℤ) : tri (n + 1) = tri n + (n + 1) := by
  unfold tri
  have : (n + 1) * (n + 1) + (n + 1) = n * n + n + (n + 1) * 2 := by ring
  rw [this, Int.add_mul_ediv_right _ _ two_ne_zero]

theorem tri_neg (n : ℤ) : tri (-n) = tri n - n := by
  unfold tri
  have : n * n + n = -n * -n + -n + n * 2 := by ring
  rw [this, Int.add_mul_ediv_right _ _ two_ne_zero]
  ring

theorem eq_of_rec {M : Type*} [AddCommGroup M] (f : ℤ → M) (a l : M) (h0 : f 0 = 0)
    (hs : ∀ n, f (n + 1) = f n + a + n • l) (n : ℤ) : f n = n • a + tri (-n) • l := by
  have step : ∀ n : ℤ, tri (-(n + 1)) = tri (-n) + n := fun n => by
    rw [tri_neg, tri_neg, tri_succ]; ring
  induction n using Int.induction_on with
  | zero => simp [h0, tri]
  | succ n ih => rw [hs, ih, step]; module
  | pred n ih =>
    have h := hs (-(n : ℤ) - 1)
    have h' := step (-(n : ℤ) - 1)
    rw [sub_add_cancel] at h h'
    rw [ih, h'] at h
    rw [eq_sub_of_add_eq (eq_sub_of_add_eq h.symm)]
    module


open GlobalTheory.CechPic in
theorem pull_zpow : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (z : T ⟶ A) (n : ℤ), GlobalTheory.CechPic.pull (z ^ n).left (GlobalTheory.CechPic.cls L hL) = tri n • GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls L hL) + tri (-n) • GlobalTheory.CechPic.pull (z⁻¹).left (GlobalTheory.CechPic.cls L hL) := by
  intro K _ A _ hA L hL T z n
  have := hA.comm
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen :=
    GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have h1 : pull (1 : T ⟶ A).left (cls L hL) = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local, map_zero]
  let φ : (T ⟶ A) →* Multiplicative (Pic T.left) :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (lam (cls L hL) x z)) fun x y => by
      rw [lam_mul_left hL hΘ, ofAdd_add]
  have hz : ∀ m : ℤ, lam (cls L hL) (z ^ m) z = m • lam (cls L hL) z z := fun m =>
    congrArg Multiplicative.toAdd (map_zpow φ z m)
  have key := eq_of_rec (fun m => pull (z ^ m).left (cls L hL)) (pull z.left (cls L hL)) (lam (cls L hL) z z)
    (by rw [zpow_zero, h1]) (fun m => by
      rw [← hz, zpow_add_one, lam, h1]; abel)
  have k1 := key (-1)
  have t1 : tri (- -1) = 1 := by decide
  rw [zpow_neg_one, t1] at k1
  rw [key n, k1, tri_neg]
  module

end GlobalTheory.PowPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowEqMumfordFormulaStatement
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardPullback_zpow_eq_mumford_formula : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (z : T ⟶ A) (n : ℤ), GlobalTheory.CechPic.pull (z ^ n).left (GlobalTheory.CechPic.cls L hL) = tri n • GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls L hL) + tri (-n) • GlobalTheory.CechPic.pull (z⁻¹).left (GlobalTheory.CechPic.cls L hL) := by
  first | exact @GlobalTheory.PowPull.pull_zpow | exact GlobalTheory.PowPull.pull_zpow | (intros; apply GlobalTheory.PowPull.pull_zpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowMulMixedSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowMulMixedSplit
set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeMixed

open GlobalTheory.CechPic

theorem lam_zpow_left {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) (n : ℤ) :
    lam (cls L hL) (x ^ n) z = n • lam (cls L hL) x z := by
  cases n with
  | ofNat k =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, natCast_zsmul]
    exact lam_pow_left hL hΘ x z k
  | negSucc k =>
    have h := lam_mul_left hL hΘ (x ^ (k + 1)) (x ^ (k + 1))⁻¹ z
    rw [mul_inv_cancel, lam_one_left, lam_pow_left hL hΘ] at h
    rw [zpow_negSucc, negSucc_zsmul]
    exact eq_neg_of_add_eq_zero_right h.symm

theorem lam_zpow_zpow {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB)
    (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x y : T ⟶ G) (m n : ℤ) :
    lam (cls L hL) (x ^ m) (y ^ n) = (m * n) • lam (cls L hL) x y := by
  rw [lam_zpow_left hL hΘ, lam_comm, lam_zpow_left hL hΘ, lam_comm, smul_smul]

theorem pull_one_eq_zero {K : Type} [Field K] {A T : Over (Sp K)} [GrpObj A] (c : CechPic.Pic A.left) :
    CechPic.pull (1 : T ⟶ A).left c = 0 := by
  change CechPic.pull ((toUnit T).left ≫ (η : 𝟙_ (Over (Sp K)) ⟶ A).left) c = 0
  rw [pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) _ c, map_zero]

theorem mixed_mul : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (x y : T ⟶ A) (m n a b : ℤ), a • GlobalTheory.CechPic.pull (x ^ m * y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m * y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL) = (a • GlobalTheory.CechPic.pull (x ^ m).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + (a • GlobalTheory.CechPic.pull (y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + ((a + b) * (m * n)) • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x y := by
  intro K _ A _ hA L hL T x y m n a b
  have : IsCommMonObj A := hA.comm
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen := GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have key : ∀ (c : CechPic.Pic A.left) (u v : T ⟶ A),
      CechPic.pull (u * v).left c = CechPic.pull u.left c + CechPic.pull v.left c + lam c u v := by
    intro c u v
    unfold lam
    rw [pull_one_eq_zero]
    abel
  rw [mul_inv, key, key, ← zpow_neg, ← zpow_neg, lam_zpow_zpow hL hΘ, lam_zpow_zpow hL hΘ, neg_mul_neg]
  module

end GlobalTheory.CubeMixed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowMulMixedSplitStatement
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (x y : T ⟶ A) (m n a b : ℤ), a • GlobalTheory.CechPic.pull (x ^ m * y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m * y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL) = (a • GlobalTheory.CechPic.pull (x ^ m).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + (a • GlobalTheory.CechPic.pull (y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + ((a + b) * (m * n)) • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x y := by
  intro K _ A _ hA L hL T x y m n a b
  have : IsCommMonObj A := hA.comm
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen :=
    GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have lam_zpow_left (x z : T ⟶ A) (n : ℤ) :
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ^ n) z =
        n • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x z := by
    open GlobalTheory.CechPic in
    cases n with
    | ofNat k =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, natCast_zsmul]
      exact lam_pow_left hL hΘ x z k
    | negSucc k =>
      have h := lam_mul_left hL hΘ (x ^ (k + 1)) (x ^ (k + 1))⁻¹ z
      rw [mul_inv_cancel, lam_one_left, lam_pow_left hL hΘ] at h
      rw [zpow_negSucc, negSucc_zsmul]
      exact eq_neg_of_add_eq_zero_right h.symm
  have lam_zpow_zpow (x y : T ⟶ A) (m n : ℤ) :
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ^ m) (y ^ n) =
        (m * n) • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x y := by
    rw [lam_zpow_left, GlobalTheory.CechPic.lam_comm, lam_zpow_left,
      GlobalTheory.CechPic.lam_comm, smul_smul]
  have pull_one_eq_zero (c : GlobalTheory.CechPic.Pic A.left) :
      GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0 := by
    change GlobalTheory.CechPic.pull ((toUnit T).left ≫ (η : 𝟙_ (Over (Sp K)) ⟶ A).left) c = 0
    rw [GlobalTheory.CechPic.pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) _ c, map_zero]
  have key : ∀ (c : GlobalTheory.CechPic.Pic A.left) (u v : T ⟶ A),
      GlobalTheory.CechPic.pull (u * v).left c = GlobalTheory.CechPic.pull u.left c +
        GlobalTheory.CechPic.pull v.left c + GlobalTheory.CechPic.lam c u v := by
    intro c u v
    unfold GlobalTheory.CechPic.lam
    rw [pull_one_eq_zero]
    abel
  rw [mul_inv, key, key, ← zpow_neg, ← zpow_neg, lam_zpow_zpow, lam_zpow_zpow, neg_mul_neg]
  module
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySquareLinearEndomorphismFiniteLoca
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySquareLinearEndomorphismFiniteLoca
set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGen

theorem zpow_two_var {G : Type*} [CommGroup G] (x y : G) (a b c d a' b' : ℤ) :
    (x ^ a * y ^ b) ^ a' * (x ^ c * y ^ d) ^ b' = x ^ (a * a' + c * b') * y ^ (b * a' + d * b') := by
  simp only [mul_zpow, ← zpow_mul, zpow_add]
  exact _root_.mul_mul_mul_comm _ _ _ _

theorem comp_zpow_hom {C : Type*} [Category C] [CartesianMonoidalCategory C] {G X Y : C} [GrpObj G]
    (f : X ⟶ Y) (g : Y ⟶ G) (n : ℤ) : f ≫ g ^ n = (f ≫ g) ^ n := by
  cases n with
  | ofNat n => simp only [Int.ofNat_eq_natCast, zpow_natCast, comp_pow]
  | negSucc n => simp only [zpow_negSucc, GrpObj.comp_inv, comp_pow]

theorem psiMap_comp {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (a b c d a' b' c' d' : ℤ) :
    psiMap A a b c d ≫ psiMap A a' b' c' d' =
      psiMap A (a * a' + c * b') (b * a' + d * b') (a * c' + c * d') (b * c' + d * d') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, psiMap_fst, psiMap_fst, comp_mul, comp_zpow_hom, comp_zpow_hom, psiMap_fst,
      psiMap_snd, zpow_two_var]
  · rw [Category.assoc, psiMap_snd, psiMap_snd, comp_mul, comp_zpow_hom, comp_zpow_hom, psiMap_fst,
      psiMap_snd, zpow_two_var]

theorem psiMap_diag {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (n : ℕ) :
    psiMap A n 0 0 n = Out.mulA (A ⊗ A) n := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [psiMap_fst, Out.mulA, pow_comp, Category.id_comp, zpow_zero, _root_.mul_one, zpow_natCast]
  · rw [psiMap_snd, Out.mulA, pow_comp, Category.id_comp, zpow_zero, _root_.one_mul, zpow_natCast]

theorem finite_etale_of_comp_eq {X S : Scheme.{0}} (p : X ⟶ S) [IsSeparated p]
    [LocallyOfFiniteType p] (f g m : X ⟶ X) [IsFinite m] [Etale m] (hg : g ≫ p = p)
    (h1 : f ≫ g = m) (h2 : g ≫ f = m) : IsFinite f ∧ Etale f := by
  have hgs : IsSeparated g :=
    MorphismProperty.of_postcomp (W' := ⊤) @IsSeparated g p trivial (by rw [hg]; infer_instance)
  haveI : LocallyOfFiniteType (g ≫ p) := by rw [hg]; infer_instance
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g p
  haveI : FormallyUnramified (g ≫ f) := by rw [h2]; infer_instance
  haveI : FormallyUnramified g := FormallyUnramified.of_comp g f
  haveI : Etale (f ≫ g) := by rw [h1]; infer_instance
  haveI : IsFinite (f ≫ g) := by rw [h1]; infer_instance
  exact ⟨MorphismProperty.of_postcomp @IsFinite (W' := @IsSeparated) f g hgs inferInstance,
    Etale.of_comp f g⟩

theorem exists_sign_mul (d : ℤ) : ∃ s : ℤ, s * d = (d.natAbs : ℤ) := by
  rcases Int.natAbs_eq d with h | h
  · exact ⟨1, by rw [_root_.one_mul]; exact h⟩
  · exact ⟨-1, by rw [h]; ring_nf; simp⟩

theorem psiMap_finite_locallyFree : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K))
    [GrpObj A], IsAbelianScheme A → ∀ a₁ b₁ a₂ b₂ : ℤ, ((a₁ * b₂ - b₁ * a₂ : ℤ) : K) ≠ 0 →
    IsFinite (psiMap A a₁ b₁ a₂ b₂).left ∧ Flat (psiMap A a₁ b₁ a₂ b₂).left ∧
      LocallyOfFinitePresentation (psiMap A a₁ b₁ a₂ b₂).left ∧
      ∃ r : ℕ, (∀ y, (psiMap A a₁ b₁ a₂ b₂).left.finrank y = r) ∧ (r : K) ≠ 0 := by
  intro K _ _ A _ hA a₁ b₁ a₂ b₂ hd
  haveI := hA.comm
  set n := (a₁ * b₂ - b₁ * a₂).natAbs with hn_def
  have hn : (n : K) ≠ 0 := by
    rcases Int.natAbs_eq (a₁ * b₂ - b₁ * a₂) with h | h
    · rw [h, Int.cast_natCast] at hd; exact hd
    · rw [h, Int.cast_neg, Int.cast_natCast, neg_ne_zero] at hd; exact hd
  haveI hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨hfin, -, het, r, hr0, -, hall, -⟩ :=
    GlobalTheory.AbelianMulFin.mulA_finite_locallyFree K (A ⊗ A) n hn
  obtain ⟨s, hs⟩ := exists_sign_mul (a₁ * b₂ - b₁ * a₂)
  rw [← hn_def] at hs
  set ψ := psiMap A a₁ b₁ a₂ b₂ with hψ
  set ψ' := psiMap A (s * b₂) (-(s * b₁)) (-(s * a₂)) (s * a₁) with hψ'
  have h1 : ψ ≫ ψ' = Out.mulA (A ⊗ A) n := by
    rw [hψ, hψ', psiMap_comp, ← psiMap_diag]
    congr 1 <;> push_cast <;> first | ring1 | linear_combination hs
  have h2 : ψ' ≫ ψ = Out.mulA (A ⊗ A) n := by
    rw [hψ, hψ', psiMap_comp, ← psiMap_diag]
    congr 1 <;> push_cast <;> first | ring1 | linear_combination hs
  have h1' : ψ.left ≫ ψ'.left = (Out.mulA (A ⊗ A) n).left := by rw [← Over.comp_left, h1]
  have h2' : ψ'.left ≫ ψ.left = (Out.mulA (A ⊗ A) n).left := by rw [← Over.comp_left, h2]
  haveI := hAA.proper
  haveI := hAA.smooth
  haveI := hAA.geomConnected
  obtain ⟨hψfin, hψet⟩ := finite_etale_of_comp_eq (A ⊗ A).hom ψ.left ψ'.left _ (Over.w ψ') h1' h2'
  obtain ⟨hψ'fin, hψ'et⟩ := finite_etale_of_comp_eq (A ⊗ A).hom ψ'.left ψ.left _ (Over.w ψ) h2' h1'
  haveI : ConnectedSpace (A ⊗ A).left :=
    GeometricallyConnected.connectedSpace (A ⊗ A).hom (A ⊗ A).hom.isOpenMap
  let o : (A ⊗ A).left := Classical.arbitrary _
  set r' := ψ.left.finrank o with hr'
  have hall' : ∀ y, ψ.left.finrank y = r' := fun y =>
    (Scheme.Hom.isLocallyConstant_finrank ψ.left).apply_eq_of_preconnectedSpace y o
  refine ⟨hψfin, inferInstance, inferInstance, r', hall', fun h0 => hr0 ?_⟩
  have e := GlobalTheory.FinrankComp.finrank_comp_of_const ψ.left ψ'.left r' hall' o
  rw [h1', hall o] at e
  rw [e, Nat.cast_mul, h0, zero_mul]

end GlobalTheory.AmpleGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySquareLinearEndomorphismFiniteLocaStatement
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVarietySquareLinearEndomorphism_finiteLocallyFree : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ a₁ b₁ a₂ b₂ : ℤ, ((a₁ * b₂ - b₁ * a₂ : ℤ) : K) ≠ 0 → IsFinite (psiMap A a₁ b₁ a₂ b₂).left ∧ Flat (psiMap A a₁ b₁ a₂ b₂).left ∧ LocallyOfFinitePresentation (psiMap A a₁ b₁ a₂ b₂).left ∧ ∃ r : ℕ, (∀ y, (psiMap A a₁ b₁ a₂ b₂).left.finrank y = r) ∧ (r : K) ≠ 0 := by
  first | exact @GlobalTheory.AmpleGen.psiMap_finite_locallyFree | exact GlobalTheory.AmpleGen.psiMap_finite_locallyFree | (intros; apply GlobalTheory.AmpleGen.psiMap_finite_locallyFree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinFreeAwayOfFinitePresentation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FinTrace

open GlobalTheory.FiniteAmple GlobalTheory.LB

section Algebra

variable {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

def tr (φ : A →+* B) : B →+ A := letI := φ.toAlgebra; (Algebra.trace A B).toAddMonoidHom

theorem tr_mul (φ : A →+* B) (a : A) (b : B) : tr φ (φ a * b) = a * tr φ b := by
  letI := φ.toAlgebra
  change Algebra.trace A B (algebraMap A B a * b) = a * Algebra.trace A B b
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem tr_of_isPushout {φ : A →+* B} {α : A →+* A'} {β : B →+* B'} {φ' : A' →+* B'}
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β)
      (CommRingCat.ofHom φ'))
    (h : FinFree φ) (b : B) : tr φ' (β b) = α (tr φ b) := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  haveI : Module.Finite A B := h.1
  haveI : Module.Free A B := h.2
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  change LinearMap.trace A' B' (Algebra.lmul A' B' (β b)) =
    algebraMap A A' (LinearMap.trace A B (Algebra.lmul A B b))
  rw [← LinearMap.trace_baseChange, ← LinearMap.trace_conj' _ hb.equiv]
  congr 1
  ext y
  obtain ⟨t, rfl⟩ := hb.equiv.surjective y
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [IsBaseChange.equiv_tmul]; rfl
  | add s t hs ht => simp only [map_add (f := _), hs, ht]

theorem tr_map (φ : A →+* B) (h : FinFree φ) (r : ℕ)
    (hr : Nontrivial A → (letI := φ.toAlgebra; Module.finrank A B) = r) (a : A) :
    tr φ (φ a) = r * a := by
  letI := φ.toAlgebra
  haveI : Module.Finite A B := h.1
  haveI : Module.Free A B := h.2
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  · change Algebra.trace A B (algebraMap A B a) = _
    rw [Algebra.trace_algebraMap, hr hA, nsmul_eq_mul]

theorem exists_finFree_away_of_finitePresentation {φ : A →+* B} (hf : φ.Finite) (hfl : φ.Flat)
    (hfp : φ.FinitePresentation) (p : PrimeSpectrum A) :
    ∃ r ∉ p.asIdeal, ∀ {A' B' : Type} [CommRing A'] [CommRing B'] {α : A →+* A'} {β : B →+* B'}
      {φ' : A' →+* B'},
      IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β)
        (CommRingCat.ofHom φ') → IsUnit (α r) → FinFree φ' := by
  algebraize [φ]
  have : Module.FinitePresentation A B := Module.FinitePresentation.of_finite_of_finitePresentation A B
  have : Module.Free (Localization p.asIdeal.primeCompl) (LocalizedModule p.asIdeal.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl B)
    (Localization p.asIdeal.primeCompl)
  refine ⟨r, hr, ?_⟩
  intro A' B' _ _ α β φ' H hu
  algebraize [α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  refine ⟨Module.Finite.equiv hb.equiv, ?_⟩
  letI : Algebra (Localization.Away r) A' := (IsLocalization.Away.lift r (g := α) hu).toAlgebra
  have : IsScalarTower A (Localization.Away r) A' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq r hu x).symm
  have h₁ : Module.Free (Localization.Away r) (TensorProduct A (Localization.Away r) B) :=
    Module.Free.of_equiv (IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (.powers r) B)).equiv.symm
  exact Module.Free.of_equiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A (Localization.Away r) A' A' B).trans hb.equiv)

end Algebra

section Geometry

open GlobalTheory.FlatNorm (FreeOpen)

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

theorem resG_app_eq {V W : Y.Opens} (h : W ≤ V) (a : Γ(Y, V)) :
    resG X (f.preimage_mono h) ((f.app V).hom a) = (f.app W).hom (resG Y h a) := by
  exact congr($(f.naturality (homOfLE h).op).hom a).symm

theorem resG_tr [IsFinite f] {V W : Y.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    (hF : FinFree (f.app V).hom) (b : Γ(X, f ⁻¹ᵁ V)) :
    resG Y h (tr (f.app V).hom b) = tr (f.app W).hom (resG X (f.preimage_mono h) b) :=
  (tr_of_isPushout (isPushout_app f hV hW h) hF b).symm

variable [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]


theorem exists_finFree_app_of_finitePresentation {y : Y} {U : Y.Opens} (hy : y ∈ U) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V ∧ V ≤ U ∧ FinFree (f.app V).hom := by
  obtain ⟨V, hV, hyV, hle⟩ := exists_isAffineOpen_mem_and_subset hy
  have hfl : (f.app V).hom.Flat := by
    rw [Scheme.Hom.app_eq_appLE]
    exact f.flat_appLE hV (hV.preimage f) _
  have hfp : (f.app V).hom.FinitePresentation := by
    rw [Scheme.Hom.app_eq_appLE]
    exact f.finitePresentation_appLE hV (hV.preimage f) _
  obtain ⟨r, hr, H⟩ := exists_finFree_away_of_finitePresentation
    (f.finite_app V hV) hfl hfp (hV.primeIdealOf ⟨y, hyV⟩)
  refine ⟨Y.basicOpen r, hV.basicOpen r, ?_, (Y.basicOpen_le r).trans hle,
    H (isPushout_app f hV (hV.basicOpen r) (Y.basicOpen_le r)) (Y.toRingedSpace.isUnit_res_basicOpen r)⟩
  have e := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
  have h₁ : hV.primeIdealOf ⟨y, hyV⟩ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen r := by
    rw [hV.fromSpec_preimage_basicOpen]
    exact hr
  exact (congrArg (· ∈ Y.basicOpen r) e).mp h₁

theorem le_iSup_freeOpen (V : Y.Opens) : V ≤ ⨆ W : FreeOpen f V, W.1 := fun _ hx => by
  obtain ⟨W, h₁, h₂, h₃, h₄⟩ := exists_finFree_app_of_finitePresentation f hx
  exact Opens.mem_iSup.2 ⟨⟨W, h₁, h₃, h₄⟩, h₂⟩

theorem ext_freeOpen {V : Y.Opens} {a b : Γ(Y, V)}
    (h : ∀ W : FreeOpen f V, resG Y W.2.2.1 a = resG Y W.2.2.1 b) : a = b :=
  fun_ext_of_cover _ (fun W : FreeOpen f V => W.2.2.1) (le_iSup_freeOpen f V) h

theorem finrank_app_of_finrank (r : ℕ) (hr : ∀ y, f.finrank y = r) (V : Y.Opens) (hV : IsAffineOpen V)
    (hF : FinFree (f.app V).hom) (hN : Nontrivial Γ(Y, V)) :
    (letI := (f.app V).hom.toAlgebra; Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) = r := by
  letI := (f.app V).hom.toAlgebra
  haveI : Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hF.2
  haveI : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hF.1
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum Γ(Y, V)) := inferInstance
  have e := (GlobalTheory.AbelianMulFin.affine_finite_projective_rankAtStalk f r hr V hV).2.2.2 p
  rw [Module.rankAtStalk_eq_finrank_of_free] at e
  exact e

theorem exists_trFun (V : Y.Opens) (b : Γ(X, f ⁻¹ᵁ V)) : ∃ a : Γ(Y, V), ∀ W : FreeOpen f V,
    resG Y W.2.2.1 a = tr (f.app W.1).hom (resG X (f.preimage_mono W.2.2.1) b) :=
  exists_fun_of_cover _ (fun W : FreeOpen f V => W.2.2.1) (le_iSup_freeOpen f V) _ fun W W' =>
    ext_freeOpen f fun O => by
      rw [resG_resG, resG_resG, resG_tr f W.2.1 O.2.1 _ W.2.2.2, resG_tr f W'.2.1 O.2.1 _ W'.2.2.2,
        resG_resG, resG_resG]

def trFun (V : Y.Opens) : Γ(X, f ⁻¹ᵁ V) →+ Γ(Y, V) where
  toFun b := (exists_trFun f V b).choose
  map_zero' := ext_freeOpen f fun W => by
    rw [(exists_trFun f V 0).choose_spec W, map_zero, map_zero, map_zero]
  map_add' a b := ext_freeOpen f fun W => by
    rw [(exists_trFun f V _).choose_spec W, map_add (f := _), map_add (f := _), map_add (f := _),
      (exists_trFun f V a).choose_spec W, (exists_trFun f V b).choose_spec W]

theorem resG_trFun_free {V : Y.Opens} (b : Γ(X, f ⁻¹ᵁ V)) (W : FreeOpen f V) :
    resG Y W.2.2.1 (trFun f V b) = tr (f.app W.1).hom (resG X (f.preimage_mono W.2.2.1) b) :=
  (exists_trFun f V b).choose_spec W

theorem resG_trFun {V W : Y.Opens} (h : W ≤ V) (b : Γ(X, f ⁻¹ᵁ V)) :
    resG Y h (trFun f V b) = trFun f W (resG X (f.preimage_mono h) b) :=
  ext_freeOpen f fun O => by
    rw [resG_trFun_free, resG_resG, resG_resG]
    exact resG_trFun_free f b ⟨O.1, O.2.1, O.2.2.1.trans h, O.2.2.2⟩

theorem trFun_mul {V : Y.Opens} (a : Γ(Y, V)) (b : Γ(X, f ⁻¹ᵁ V)) :
    trFun f V ((f.app V).hom a * b) = a * trFun f V b :=
  ext_freeOpen f fun W => by
    rw [resG_trFun_free, map_mul (resG X _), map_mul (resG Y _), resG_app_eq, tr_mul, resG_trFun_free]

theorem trFun_app (r : ℕ) (hr : ∀ V : Y.Opens, IsAffineOpen V → FinFree (f.app V).hom →
      Nontrivial Γ(Y, V) → (letI := (f.app V).hom.toAlgebra; Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) = r)
    {V : Y.Opens} (a : Γ(Y, V)) : trFun f V ((f.app V).hom a) = r * a :=
  ext_freeOpen f fun W => by
    rw [resG_trFun_free, resG_app_eq, tr_map _ W.2.2.2 r (hr W.1 W.2.1 W.2.2.2), map_mul, map_natCast]

end Geometry

end GlobalTheory.FinTrace

namespace GlobalTheory.FinTrace

open GlobalTheory.FiniteAmple GlobalTheory.LB GlobalTheory.AbLaw

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

section Sections

variable {L : LB Y}

abbrev pj (L : LB Y) (i : L.ι) : (L.pull f).ι := fun _ => i

theorem preimage_inf_le (V : Y.Opens) (i : L.ι) :
    f ⁻¹ᵁ (V ⊓ L.U i) ≤ f ⁻¹ᵁ V ⊓ (L.pull f).U (pj f L i) :=
  fun _ hx => ⟨hx.1, (pull_U f (pj f L i)).ge hx.2⟩

def trCoord (V : Y.Opens) (s : SecOn (L.pull f) (f ⁻¹ᵁ V)) (i : L.ι) : Γ(Y, V ⊓ L.U i) :=
  trFun f (V ⊓ L.U i) (resG X (preimage_inf_le f V i) (coord s (pj f L i)))

theorem trCoord_mem (V : Y.Opens) (s : SecOn (L.pull f) (f ⁻¹ᵁ V)) : trCoord f V s ∈ secOn L V := by
  intro i j
  have e := coord_rel s (pj f L i) (pj f L j) (W := f ⁻¹ᵁ (V ⊓ L.U i ⊓ L.U j))
    (fun _ hx => ⟨hx.1.1, (pull_U f (pj f L i)).ge hx.1.2⟩)
    (fun _ hx => ⟨hx.1.1, (pull_U f (pj f L j)).ge hx.2⟩)
    (fun _ hx => ⟨(pull_U f (pj f L i)).ge hx.1.2, (pull_U f (pj f L j)).ge hx.2⟩)
  erw [resG_pull_g] at e
  simp only [trCoord, resG_trFun, resG_resG]
  rw [← trFun_mul, ← resG_app_eq, resG_app]
  exact congrArg (trFun f _) e

def trSec (V : Y.Opens) : SecOn (L.pull f) (f ⁻¹ᵁ V) →+ SecOn L V where
  toFun s := mkSec (trCoord f V s) (trCoord_mem f V s)
  map_zero' := sec_ext fun i => by simp [trCoord]
  map_add' s t := sec_ext fun i => by simp [trCoord]

@[simp] theorem coord_trSec (V : Y.Opens) (s : SecOn (L.pull f) (f ⁻¹ᵁ V)) (i : L.ι) :
    coord (trSec f V s) i = trFun f (V ⊓ L.U i) (resG X (preimage_inf_le f V i) (coord s (pj f L i))) :=
  rfl

theorem trSec_smul (V : Y.Opens) (a : Γ(Y, V)) (s : SecOn (L.pull f) (f ⁻¹ᵁ V)) :
    trSec f V ((f.app V).hom a • s) = a • trSec f V s :=
  sec_ext fun i => by
    rw [coord_trSec, coord_smul, coord_smul, coord_trSec, map_mul, resG_resG, ← trFun_mul,
      resG_app_eq]

theorem trSec_restrict {V W : Y.Opens} (h : W ≤ V) (s : SecOn (L.pull f) (f ⁻¹ᵁ V)) :
    trSec f W (SecOn.restrict (L.pull f) (f.preimage_mono h) s) = SecOn.restrict L h (trSec f V s) :=
  sec_ext fun i => by
    rw [coord_trSec, SecOn.coord_restrict, SecOn.coord_restrict, coord_trSec]
    erw [resG_trFun, resG_resG, resG_resG]

theorem trSec_pull (r : ℕ) (hr : ∀ V : Y.Opens, IsAffineOpen V → FinFree (f.app V).hom →
      Nontrivial Γ(Y, V) → (letI := (f.app V).hom.toAlgebra; Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) = r)
    (V : Y.Opens) (s : SecOn L V) :
    trSec f V (SecOn.pull L f V s) = (r : Γ(Y, V)) • s :=
  sec_ext fun i => by
    rw [coord_trSec, coord_smul]
    erw [coord_pullSec, resG_appLE]
    rw [map_natCast, ← trFun_app f r hr (coord s i), Scheme.Hom.app_eq_appLE]

end Sections

end GlobalTheory.FinTrace

namespace GlobalTheory.FinTrace

open GlobalTheory.FiniteAmple GlobalTheory.LB GlobalTheory.AbLaw

section Cech

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {R : Type} [CommRing R] (q : Y ⟶ Spec (CommRingCat.of R))

theorem comp_eq_comp_id : f ≫ q = (f ≫ q) ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]

theorem resG_cst_comp {V : Y.Opens} {V' : X.Opens} (e : f ⁻¹ᵁ V ≤ V') (r : R) :
    resG X e (cst (f ≫ q) V' r) = (f.app V).hom (cst q V r) := by
  rw [Scheme.Hom.app_eq_appLE, appLE_cst (comp_eq_comp_id f q) (le_refl (f ⁻¹ᵁ V)) r]
  exact rs_cst (f ≫ q) e r

variable [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] {L : LB Y}


variable (L) in
def trR (V : Y.Opens) (V' : X.Opens) (e : f ⁻¹ᵁ V ≤ V') :
    SecOnR (f ≫ q) (L.pull f) V' →ₗ[R] SecOnR q L V where
  toFun x := SecOnR.of q L V (trSec f V (SecOn.restrict (L.pull f) e ((SecOnR.of (f ≫ q) _ V').symm x)))
  map_add' x y := by simp only [map_add (f := _)]
  map_smul' r x := by
    rw [SecOnR.smul_def, LinearEquiv.map_smul, (SecOn.restrict (L.pull f) e).map_smulₛₗ]
    erw [resG_cst_comp f q e r, trSec_smul]
    rfl


variable (L) in
def trCube {κ : Type} (D : κ → Y.Opens) :
    secCube (f ≫ q) (L.pull f) (fun i => f ⁻¹ᵁ D i) ⟶ secCube q L D :=
  GlobalTheory.Cube.homMk κ R
    (fun s => trR f q L (⨅ i ∈ s, D i) (⨅ i ∈ s, f ⁻¹ᵁ D i) (preimage_biInf D f s).le)
    fun {s t} h x => by
      show trSec f _ (SecOn.restrict (L.pull f) (preimage_biInf D f t).le
          (SecOn.restrict (L.pull f) (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) x)) =
        SecOn.restrict L (iInf_le_iInf_of_subset D h)
          (trSec f _ (SecOn.restrict (L.pull f) (preimage_biInf D f s).le x))
      rw [← trSec_restrict]
      congr 1
      exact (SecOn.restrict_restrict (M := L.pull f) _ _ (x : SecOn (L.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i))).trans
        (SecOn.restrict_restrict _ _ _).symm


variable (L) in
def pullCube {κ : Type} (D : κ → Y.Opens) :
    secCube q L D ⟶ secCube (f ≫ q) (L.pull f) (fun i => f ⁻¹ᵁ D i) :=
  GlobalTheory.Cube.homMk κ R (fun s => secCubePull L D (comp_eq_comp_id f q) s)
    fun h x => secCubePull_res D (comp_eq_comp_id f q) h x

end Cech

end GlobalTheory.FinTrace

namespace GlobalTheory.FinTrace

open GlobalTheory.FiniteAmple GlobalTheory.LB GlobalTheory.AbLaw

theorem exactAt_of_isIso_comp {R : Type} [CommRing R] {C D : CochainComplex (ModuleCat.{0} R) ℕ}
    (i : C ⟶ D) (p : D ⟶ C) [IsIso (i ≫ p)] {n : ℕ} (hD : D.ExactAt n) : C.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hD ⊢
  rw [IsZero.iff_id_eq_zero]
  have e : 𝟙 (C.homology n) = HomologicalComplex.homologyMap i n ≫
      HomologicalComplex.homologyMap p n ≫ inv (HomologicalComplex.homologyMap (i ≫ p) n) := by
    rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, IsIso.hom_inv_id]
  rw [e, hD.eq_of_tgt (HomologicalComplex.homologyMap i n) 0, zero_comp]

section Cech

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {R : Type} [CommRing R] (q : Y ⟶ Spec (CommRingCat.of R))
  [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]


omit [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] in
def funCube (a : Γ(Y, ⊤)) (L : LB Y) {κ : Type} (D : κ → Y.Opens) : secCube q L D ⟶ secCube q L D :=
  GlobalTheory.Cube.homMk κ R
    (fun s => SecOnR.lin q (LinearMap.lsmul Γ(Y, ⨅ i ∈ s, D i) (SecOn L (⨅ i ∈ s, D i))
      (rs Y le_top a))) fun {s t} h x => by
      let e := iInf_le_iInf_of_subset D h
      let y : SecOn L (⨅ i ∈ s, D i) := x
      change rs Y (le_top : (⨅ i ∈ t, D i) ≤ ⊤) a • SecOn.restrict L e y =
        SecOn.restrict L e (rs Y (le_top : (⨅ i ∈ s, D i) ≤ ⊤) a • y)
      rw [map_smulₛₗ, rs_rs]

def cechPull (L : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) :
    cechLB q L D ⟶ cechLB (f ≫ q) (L.pull f) (fun i => f ⁻¹ᵁ D i) :=
  (cechFunctor κ R).map (pullCube f q L D)

def cechTr (L : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) :
    cechLB (f ≫ q) (L.pull f) (fun i => f ⁻¹ᵁ D i) ⟶ cechLB q L D :=
  (cechFunctor κ R).map (trCube f q L D)

def cechSMul (a : Γ(Y, ⊤)) (L : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) :
    cechLB q L D ⟶ cechLB q L D :=
  (cechFunctor κ R).map (funCube q a L D)

theorem pullCube_trCube_inv (r : ℕ) (hr : ∀ y, f.finrank y = r) (hu : IsUnit (r : Γ(Y, ⊤)))
    (L : LB Y) {κ : Type} (D : κ → Y.Opens) :
    pullCube f q L D ≫ trCube f q L D ≫ funCube q (hu.unit⁻¹).val L D = 𝟙 _ := by
  ext s x
  obtain ⟨y, rfl⟩ : ∃ y : SecOn L (⨅ i ∈ s, D i), y = x := ⟨x, rfl⟩
  change rs Y (le_top : (⨅ i ∈ s, D i) ≤ ⊤) (hu.unit⁻¹).val •
    trSec f _ (SecOn.restrict (L.pull f) (preimage_biInf D f s).le
      (SecOn.pullLE L f _ _ (preimage_biInf D f s).ge y)) = y
  rw [SecOn.restrict_pullLE]
  erw [SecOn.pullLE_self, trSec_pull f r (finrank_app_of_finrank f r hr)]
  rw [smul_smul, ← map_natCast (rs Y (le_top : (⨅ i ∈ s, D i) ≤ ⊤)) r, ← map_mul, IsUnit.val_inv_mul,
    map_one, one_smul]

theorem cechLB_retract (r : ℕ) (hr : ∀ y, f.finrank y = r) (hu : IsUnit (r : Γ(Y, ⊤)))
    (L : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) :
    cechPull f q L D ≫ (cechTr f q L D ≫ cechSMul q (hu.unit⁻¹).val L D) = 𝟙 (cechLB q L D) := by
  have e := congrArg (cechFunctor κ R).map (pullCube_trCube_inv f q r hr hu L D)
  rw [Functor.map_comp, Functor.map_comp, CategoryTheory.Functor.map_id] at e
  exact e

theorem cechLB_retract_and_exactAt (r : ℕ) (hr : ∀ y, f.finrank y = r) (hu : IsUnit (r : Γ(Y, ⊤)))
    (L : LB Y) {κ : Type} [LinearOrder κ] (D : κ → Y.Opens) :
    cechPull f q L D ≫ (cechTr f q L D ≫ cechSMul q (hu.unit⁻¹).val L D) = 𝟙 (cechLB q L D) ∧
      ∀ n : ℕ, (cechLB (f ≫ q) (L.pull f) (fun i => f ⁻¹ᵁ D i)).ExactAt n → (cechLB q L D).ExactAt n := by
  refine ⟨cechLB_retract f q r hr hu L D, fun n h => ?_⟩
  haveI : IsIso (cechPull f q L D ≫ (cechTr f q L D ≫ cechSMul q (hu.unit⁻¹).val L D)) := by
    rw [cechLB_retract f q r hr hu]
    infer_instance
  exact exactAt_of_isIso_comp (cechPull f q L D) (cechTr f q L D ≫ cechSMul q (hu.unit⁻¹).val L D) h

end Cech

end GlobalTheory.FinTrace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingInvMixPairKunnethIsogeny
set_option autoImplicit false

noncomputable section

section Lemmas
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGen


open GlobalTheory.CechPic in
theorem cls_tw_one {X : Scheme.{0}} {M H : LB X} (hM : M.IsLB) (hH : H.IsLB) :
    cls (GlobalTheory.AbLaw.tw M H 1) (GlobalTheory.AbLaw.isLB_tw hM hH 1) = cls M hM + cls H hH := by
  refine (cls_div (A := M) (B := GlobalTheory.AbLaw.pw H (-1)) hM (GlobalTheory.AbLaw.isLB_pw hH _) (GlobalTheory.AbLaw.isLB_tw hM hH 1)).trans ?_
  rw [GlobalTheory.AmpleStabFinite.cls_pw hH]
  simp


open GlobalTheory.CechPic in
theorem cls_mix_pull {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    {T : Over (Sp K)} (z : T ⟶ A) (a b : ℤ) :
    cls ((mix A L a b).pull z.left) (LB.isLB_pull (LB.isLB_linComb hL _ _) _) =
      a • pull z.left (cls L hL) + b • pull (z⁻¹).left (cls L hL) := by
  refine (cls_pull (L := LB.LinComb L ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![a, b])
    (LB.isLB_linComb hL _ _) _ _).trans ?_
  rw [cls_linComb hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add (f := _), map_zsmul, pull_id, ← pull_comp,
    ← Over.comp_left, Hom.inv_def]

end GlobalTheory.AmpleGen
end Lemmas

section RowLatticeBoundForBasis
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AmpleGen

open GlobalTheory.CechPic in
theorem lbIso_pull_psiMap {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (a₁ b₁ a₂ b₂ : ℤ) (hs : a₁ * b₁ + a₂ * b₂ = 0) {L : LB A.left} (hL : L.IsLB) (a b : ℤ) :
    LBIso ((GlobalTheory.AbLaw.tw ((mix A L a b).pull (fst A A).left) ((mix A L a b).pull (snd A A).left) 1).pull
        (psiMap A a₁ b₁ a₂ b₂).left)
      (GlobalTheory.AbLaw.tw ((mix A L (a * tri a₁ + b * tri (-a₁) + a * tri a₂ + b * tri (-a₂))
                   (a * tri (-a₁) + b * tri a₁ + a * tri (-a₂) + b * tri a₂)).pull (fst A A).left)
        ((mix A L (a * tri b₁ + b * tri (-b₁) + a * tri b₂ + b * tri (-b₂))
          (a * tri (-b₁) + b * tri b₁ + a * tri (-b₂) + b * tri b₂)).pull (snd A A).left) 1) := by
  haveI := hA.comm
  have hP' : ∀ a b : ℤ, (mix A L a b).IsLB := fun _ _ => LB.isLB_linComb hL _ _
  have h₁ := GlobalTheory.AbLaw.isLB_tw (LB.isLB_pull (hP' a b) (fst A A).left) (LB.isLB_pull (hP' a b) (snd A A).left) 1
  refine (cls_eq_iff (LB.isLB_pull h₁ _) (GlobalTheory.AbLaw.isLB_tw (LB.isLB_pull (hP' _ _) _)
    (LB.isLB_pull (hP' _ _) _) 1)).1 ?_
  rw [cls_pull h₁, cls_tw_one, cls_tw_one, cls_mix_pull A hL, cls_mix_pull A hL, cls_mix_pull A hL,
    cls_mix_pull A hL]
  simp only [map_add (f := _), map_zsmul, ← pull_comp, ← Over.comp_left, GrpObj.comp_inv, psiMap, lift_fst, lift_snd]
  set c := cls L hL
  set x := fst A A
  set y := snd A A
  have e₁ := GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split K A hA L hL _ x y a₁ b₁ a b
  have e₂ := GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split K A hA L hL _ x y a₂ b₂ a b
  have f (z : A ⊗ A ⟶ A) (n : ℤ) := GlobalTheory.T.cechPicardPullback_zpow_eq_mumford_formula K A hA L hL _ z n
  have g (z : A ⊗ A ⟶ A) (n : ℤ) : pull ((z ^ n)⁻¹).left c = tri (-n) • pull z.left c + tri n • pull (z⁻¹).left c := by
    rw [← zpow_neg, f, neg_neg]
  rw [e₁, e₂, f x a₁, g x a₁, f x a₂, g x a₂, f y b₁, g y b₁, f y b₂, g y b₂]
  have hl : ((a + b) * (a₁ * b₁)) • lam c x y + ((a + b) * (a₂ * b₂)) • lam c x y = 0 := by
    rw [← add_smul, ← mul_add, hs, mul_zero, zero_smul]
  linear_combination (norm := module) hl
  all_goals exact LB.isLB_pull (hP' _ _) _
end GlobalTheory.AmpleGen
end RowLatticeBoundForBasis

section MainAux
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AmpleGen

theorem finrank_pos_of_not_exactAt {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M : LB X} {κ : Type} [LinearOrder κ] {D : κ → X.Opens} {n : ℕ}
    [Module.Finite K ((cechLB f M D).homology n)] (h : ¬ (cechLB f M D).ExactAt n) :
    0 < Module.finrank K ((cechLB f M D).homology n) := by
  have : Nontrivial ((cechLB f M D).homology n) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact h ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (ModuleCat.isZero_of_subsingleton _))
  exact Module.finrank_pos

theorem exists_nonvanishing_invMix_pair_isogeny (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (a₁ b₁ a₂ b₂ : ℤ) (hs : a₁ * b₁ + a₂ * b₂ = 0) (hd : ((a₁ * b₂ - b₁ * a₂ : ℤ) : K) ≠ 0)
    (L : LB A.left) (hL : L.IsLB) (a b j : ℕ) (hN : NV A (mix A L a b) j) :
    ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧
      NV A (mix A L (a * tri a₁ + b * tri (-a₁) + a * tri a₂ + b * tri (-a₂))
        (a * tri (-a₁) + b * tri a₁ + a * tri (-a₂) + b * tri a₂)) j₁ ∧
      NV A (mix A L (a * tri b₁ + b * tri (-b₁) + a * tri b₂ + b * tri (-b₂))
        (a * tri (-b₁) + b * tri b₁ + a * tri (-b₂) + b * tri b₂)) j₂ := by
  haveI := hA.comm
  haveI := hA.proper
  obtain ⟨κ, _, _, W, hW, hWc, hne⟩ := hN
  have hP' : ∀ a b : ℤ, (mix A L a b).IsLB := fun _ _ => LB.isLB_linComb hL _ _
  have hsep : IsSeparated A.hom := inferInstance
  have hproj := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K A hA
  have fin : ∀ M : LB A.left, M.IsLB → ∀ n, Module.Finite K ((cechLB A.hom M W).homology n) :=
    fun M hM => cechLB_homology_finite_of_affine_cover K _ A.hom M κ W hM hsep hproj hW hWc
  have h₀ : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback A.hom A.hom
  have hAA := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  haveI := hAA.comm
  haveI := hAA.proper
  have hsepAA : IsSeparated (A ⊗ A).hom := inferInstance
  have hprojAA := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K (A ⊗ A) hAA
  haveI : CompactSpace (A ⊗ A).left := QuasiCompact.compactSpace_of_compactSpace (A ⊗ A).hom
  obtain ⟨k, E, hE, hEc⟩ := GlobalTheory.PicZeroVan.exists_fin_affine_cover (A ⊗ A).left
  obtain ⟨hfin, hflat, hlfp, r, hr, hr0⟩ := GlobalTheory.T.abelianVarietySquareLinearEndomorphism_finiteLocallyFree K A hA a₁ b₁ a₂ b₂ hd
  set ψ := psiMap A a₁ b₁ a₂ b₂ with hψ
  set P := mix A L a b with hPdef
  have hP := hP' a b
  have hf₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w (fst A A)
  have hfψ : ψ.left ≫ (A ⊗ A).hom = (A ⊗ A).hom := Over.w ψ

  have k₀ := finrank_cechLB_homology_extProd K _ _ _ A.hom A.hom (fst A A).left (snd A A).left P P h₀ hP hP
    hsep hsep κ W κ W (Fin k) E hW hWc hW hWc hE hEc (fin P hP) (fin P hP) (2 * j)
  have hpos : 0 < Module.finrank K ((cechLB A.hom P W).homology j) := by
    haveI := fin P hP j
    exact finrank_pos_of_not_exactAt hne
  have hM : ¬ (cechLB ((fst A A).left ≫ A.hom) (tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1) E).ExactAt
      (2 * j) := by
    intro hex
    have hz : Module.finrank K ((cechLB ((fst A A).left ≫ A.hom)
        (tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1) E).homology (2 * j)) = 0 := by
      have : Subsingleton ((cechLB ((fst A A).left ≫ A.hom)
          (tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1) E).homology (2 * j)) :=
        ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hex)
      exact Module.finrank_zero_of_subsingleton
    rw [k₀] at hz
    have := (Finset.sum_eq_zero_iff.1 hz) (j, j) (by simp [two_mul])
    exact (Nat.mul_pos hpos hpos).ne' this

  have hu : IsUnit ((r : ℕ) : Γ((A ⊗ A).left, ⊤)) := by
    have := (GlobalTheory.AbelianMulFin.isUnit_natCast_Sp (K := K) hr0).map (A ⊗ A).hom.appTop.hom
    rwa [map_natCast] at this
  rw [hf₁] at hM
  have hM' : ¬ (cechLB (ψ.left ≫ (A ⊗ A).hom)
      ((tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1).pull ψ.left) (fun i => ψ.left ⁻¹ᵁ E i)).ExactAt
      (2 * j) := fun h => hM ((GlobalTheory.FinTrace.cechLB_retract_and_exactAt ψ.left (A ⊗ A).hom r hr hu _ E).2 _ h)
  rw [hfψ] at hM'
  set P₁ := mix A L (a * tri a₁ + b * tri (-a₁) + a * tri a₂ + b * tri (-a₂))
        (a * tri (-a₁) + b * tri a₁ + a * tri (-a₂) + b * tri a₂) with hP₁def
  set P₂ := mix A L (a * tri b₁ + b * tri (-b₁) + a * tri b₂ + b * tri (-b₂))
        (a * tri (-b₁) + b * tri b₁ + a * tri (-b₂) + b * tri b₂) with hP₂def
  have hP₁ : P₁.IsLB := hP' _ _
  obtain ⟨w, hw⟩ := lbIso_pull_psiMap A hA a₁ b₁ a₂ b₂ hs hL a b
  have hP₂ : P₂.IsLB := hP' _ _
  have hTw : (tw (P₁.pull (fst A A).left) (P₂.pull (snd A A).left) 1).IsLB :=
    isLB_tw (LB.isLB_pull hP₁ _) (LB.isLB_pull hP₂ _) 1
  have hN₂ : ¬ (cechLB (A ⊗ A).hom (tw (P₁.pull (fst A A).left) (P₂.pull (snd A A).left) 1)
      (fun i => ψ.left ⁻¹ᵁ E i)).ExactAt (2 * j) := fun h =>
    hM' (h.of_iso (cechLBCongr _ _ (LB.isLB_pull (isLB_tw (LB.isLB_pull hP _) (LB.isLB_pull hP _) 1) _)
      hTw w hw).symm)

  have hD : ∀ i, IsAffineOpen (ψ.left ⁻¹ᵁ E i) := fun i => (hE i).preimage ψ.left
  have hDc : ⨆ i, ψ.left ⁻¹ᵁ E i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hEc]; rfl
  have k₁ := finrank_cechLB_homology_extProd K _ _ _ A.hom A.hom (fst A A).left (snd A A).left P₁ P₂ h₀ hP₁ hP₂
    hsep hsep κ W κ W (Fin k) (fun i => ψ.left ⁻¹ᵁ E i) hW hWc hW hWc hD hDc (fin P₁ hP₁) (fin P₂ hP₂) (2 * j)
  rw [hf₁] at k₁
  haveI := cechLB_homology_finite_of_affine_cover K _ (A ⊗ A).hom _ (Fin k) (fun i => ψ.left ⁻¹ᵁ E i) hTw hsepAA
    hprojAA hD hDc (2 * j)
  have hpos₂ := finrank_pos_of_not_exactAt hN₂
  rw [k₁] at hpos₂
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos₂.ne'
  have hx' : x.1 + x.2 = 2 * j := by simpa using hx
  refine ⟨x.1, x.2, hx', ⟨κ, inferInstance, inferInstance, W, hW, hWc, fun h => hx0 ?_⟩,
    ⟨κ, inferInstance, inferInstance, W, hW, hWc, fun h => hx0 ?_⟩⟩
  · haveI := fin P₁ hP₁ x.1
    have : Subsingleton ((cechLB A.hom P₁ W).homology x.1) :=
      ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h)
    rw [Module.finrank_zero_of_subsingleton, zero_mul]
  · haveI := fin P₂ hP₂ x.2
    have : Subsingleton ((cechLB A.hom P₂ W).homology x.2) :=
      ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h)
    rw [Module.finrank_zero_of_subsingleton (R := K) (M := (cechLB A.hom P₂ W).homology x.2), mul_zero]

end GlobalTheory.AmpleGen
end MainAux

section Target
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem GlobalTheory.AmpleGen.nv_mix_pair_of_nv : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ α β γ δ : ℤ, α * β + γ * δ = 0 → ((α * δ - β * γ : ℤ) : K) ≠ 0 → ∀ L : LB A.left, L.IsLB → ∀ a b j : ℕ, NV A (mix A L a b) j → ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (a * tri α + b * tri (-α) + a * tri γ + b * tri (-γ)) (a * tri (-α) + b * tri α + a * tri (-γ) + b * tri γ)) j₁ ∧ NV A (mix A L (a * tri β + b * tri (-β) + a * tri δ + b * tri (-δ)) (a * tri (-β) + b * tri β + a * tri (-δ) + b * tri δ)) j₂ := by
  intro K _ _ A _ hA α β γ δ hs hd L hL a b j h
  exact exists_nonvanishing_invMix_pair_isogeny K A hA α β γ δ hs hd L hL a b j h

end Target
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingInvMixPairKunnethIsogenyStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_nonvanishing_invMix_pair_kunneth_isogeny : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ α β γ δ : ℤ, α * β + γ * δ = 0 → ((α * δ - β * γ : ℤ) : K) ≠ 0 → ∀ L : LB A.left, L.IsLB → ∀ a b j : ℕ, NV A (mix A L a b) j → ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (a * tri α + b * tri (-α) + a * tri γ + b * tri (-γ)) (a * tri (-α) + b * tri α + a * tri (-γ) + b * tri γ)) j₁ ∧ NV A (mix A L (a * tri β + b * tri (-β) + a * tri δ + b * tri (-δ)) (a * tri (-β) + b * tri β + a * tri (-δ) + b * tri δ)) j₂ := by
  first | exact @GlobalTheory.AmpleGen.nv_mix_pair_of_nv | exact GlobalTheory.AmpleGen.nv_mix_pair_of_nv | (intros; apply GlobalTheory.AmpleGen.nv_mix_pair_of_nv <;> assumption)
end
