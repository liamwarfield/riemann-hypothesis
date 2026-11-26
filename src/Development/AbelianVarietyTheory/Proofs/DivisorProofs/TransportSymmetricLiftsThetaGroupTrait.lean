module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaMove

variable {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT}
  {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG}

def tf (wA : LB.Iso LA (LP.pull α)) (ℓ : LB.Iso LG (LP.pull β)) (w : LB.Iso LT (LG.pull c)) (f : Y' ⟶ Y)
    (sA : Y ⟶ XA) (sT : Y' ⟶ XT) {Z : Scheme.{0}} (q : Z ⟶ Y') (z : Z) (JP : (Z ⟶ XP) → LP.ι)
    (JA : (Z ⟶ XA) → LA.ι) (JG : (Z ⟶ XG) → LG.ι) (Jt : (Z ⟶ XT) → LT.ι) : (Z.presheaf.stalk z)ˣ :=
  (gw wA (q ≫ f ≫ sA) z (JP (q ≫ sT ≫ c ≫ β)) (JA (q ≫ f ≫ sA)))⁻¹ *
    gw ℓ (q ≫ sT ≫ c) z (JP (q ≫ sT ≫ c ≫ β)) (JG (q ≫ sT ≫ c)) *
    gw w (q ≫ sT) z (JG (q ≫ sT ≫ c)) (Jt (q ≫ sT))

end GlobalTheory.ThetaMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMovedToTraitSide
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMovedToTraitSide
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem exists_down_three {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT}
    (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG}
    (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen)
    (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y')
    (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ)
    (u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k])) (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k]), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt,
      Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt →
      val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt *
        (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  have hm : f ≫ mA ≫ α = mT ≫ c ≫ β := by
    rw [← h₂, Category.assoc, ← h₁, ← Category.assoc f mA, ← h₃]
    simp only [Category.assoc]
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up ((isGen_iff wA).1 hwA) hP hA (φ' := ![sA, mA]) (ε := ![k, -k]) u hu
  obtain ⟨t₂, ht₂, v₂⟩ := GlobalTheory.ArcPull.exists_down_om hℓ hP hG (φ' := ![sT ≫ c, mT ≫ c]) f (fun i => by
      fin_cases i
      · simpa using h₁.symm
      · simpa using hm.symm) t₁ ht₁
  obtain ⟨u', hu', v₃⟩ := GlobalTheory.ArcPull.exists_down_om hw hG hT (φ' := ![sT, mT]) (φ := ![sT ≫ c, mT ≫ c]) (𝟙 Y')
    (fun i => by fin_cases i <;> simp) t₂ ht₂
  refine ⟨u', hu', fun Z q z JP JA JG Jt hP' hA' hG' hT' => ?_⟩
  have e₁ : val t₁ (q ≫ f) z JP = pw wA ![sA, mA] ![k, -k] (q ≫ f) z (fun i => JP ((q ≫ f) ≫ ![sA, mA] i ≫ α))
      (fun i => JA ((q ≫ f) ≫ ![sA, mA] i)) * val u (q ≫ f) z JA :=
    v₁ Z (q ≫ f) z _ _ (hP'.mem _ _) (hA'.mem _ _)
  have e₂ := v₂ Z q z JP JG hP' hG'
  have e₃ := v₃ Z q z JG Jt hG' hT'
  rw [Category.comp_id] at e₃
  rw [e₂, e₃] at e₁
  simp only [pw, GlobalTheory.ArcPull.om, tf, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Category.assoc] at e₁ ⊢
  simp only [reassoc_of% h₁, reassoc_of% hm, reassoc_of% h₂, reassoc_of% h₃, h₁, hm, h₂, h₃] at e₁ ⊢
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e₁
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
  linear_combination (norm := module) -e'

end GlobalTheory.ThetaMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMovedToTraitSideStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_moved_to_trait_side : ∀ {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT} (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG} (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen) (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y') (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ) (u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k])) (hu : u.IsGen), ∃ u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k]), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt, Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt → val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt * (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  first | exact @GlobalTheory.ThetaMove.exists_down_three | exact GlobalTheory.ThetaMove.exists_down_three | (intros; apply GlobalTheory.ThetaMove.exists_down_three <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitFibreIsoCommNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitFibreIsoCommNeg
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem negT_fibre_comm : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β), f ≫ (negT C.A.A (TFK (R := R) F)).left = (negT T.A.A (TFK (R := W) F)).left ≫ f := by
  intro R _ _ _ D C W _ _ _ T F _ _ _ f hf1 hf2
  have gB : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ)
      (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) :=
    ((GlobalTheory.ThetaBaseChange.grp_generic T.U.toUnifPre).comp T.cart).congr rfl (by simp only [Category.assoc])
  have gA := C.α_cart
  have nfA : negT C.A.A (TFK (R := R) F) ≫ fst (TFK (R := R) F) C.A.A = fst _ _ := by unfold negT; exact lift_fst _ _
  have nsA : negT C.A.A (TFK (R := R) F) ≫ snd (TFK (R := R) F) C.A.A = snd _ _ ≫ GrpObj.inv := by
    unfold negT; exact lift_snd _ _
  have nfB : negT T.A.A (TFK (R := W) F) ≫ fst (TFK (R := W) F) T.A.A = fst _ _ := by unfold negT; exact lift_fst _ _
  have nsB : negT T.A.A (TFK (R := W) F) ≫ snd (TFK (R := W) F) T.A.A = snd _ _ ≫ GrpObj.inv := by
    unfold negT; exact lift_snd _ _
  have hw : f ≫ (TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp = (TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ := by
    have e := congrArg (· ≫ C.G.hom) hf2
    have wB := gB.1.w
    simp only [Category.assoc] at e wB
    rw [gA.1.w, wB, ← Category.assoc (snd (TFK (R := R) F) C.A.A).left, ← Category.assoc (snd (TFK (R := W) F) T.A.A).left,
      Over.w, Over.w] at e
    exact e
  let ρ : Over.mk ((TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ) ⟶ Over.mk ((TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp) :=
    Over.homMk f hw
  have key : ρ ≫ pushHom gA _ (snd _ _) = pushHom gB _ (snd _ _) :=
    Over.OverMorphism.ext (by
      show f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ _
      exact hf2)
  have keyi : ρ ≫ pushHom gA _ (snd _ _ ≫ GrpObj.inv) = pushHom gB _ (snd _ _ ≫ GrpObj.inv) := by
    have i1 : (snd (TFK (R := R) F) C.A.A ≫ GrpObj.inv) = (snd _ _)⁻¹ := rfl
    have i2 : (snd (TFK (R := W) F) T.A.A ≫ GrpObj.inv) = (snd _ _)⁻¹ := rfl
    rw [i1, i2, map_inv, map_inv, GrpObj.comp_inv, key]
  apply pullback.hom_ext
  · change (f ≫ (negT C.A.A (TFK (R := R) F)).left) ≫ (fst (TFK (R := R) F) C.A.A).left =
      ((negT T.A.A (TFK (R := W) F)).left ≫ f) ≫ (fst (TFK (R := R) F) C.A.A).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, nfA, hf1, ← Over.comp_left, nfB]
  · change (f ≫ (negT C.A.A (TFK (R := R) F)).left) ≫ (snd (TFK (R := R) F) C.A.A).left =
      ((negT T.A.A (TFK (R := W) F)).left ≫ f) ≫ (snd (TFK (R := R) F) C.A.A).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, nsA]
    apply gA.1.hom_ext
    · have k : f ≫ (snd (TFK (R := R) F) C.A.A ≫ GrpObj.inv).left ≫ C.α =
          (snd (TFK (R := W) F) T.A.A ≫ GrpObj.inv).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β :=
        congrArg Over.Hom.left keyi
      rw [Category.assoc, k]
      simp only [Category.assoc]
      rw [hf2, ← Category.assoc (negT T.A.A (TFK (R := W) F)).left, ← Over.comp_left, nsB]
    · rw [Category.assoc, Over.w, Category.assoc, Category.assoc, Over.w]
      rw [← Over.w (fst (TFK (R := R) F) C.A.A), ← Category.assoc, hf1,
        ← Category.assoc (negT T.A.A (TFK (R := W) F)).left, ← Over.comp_left, nfB]

end GlobalTheory.ThetaMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitFibreIsoCommNegStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitFibreIso_comm_neg : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β), f ≫ (negT C.A.A (TFK (R := R) F)).left = (negT T.A.A (TFK (R := W) F)).left ≫ f := by
  first | exact @GlobalTheory.ThetaMove.negT_fibre_comm | exact GlobalTheory.ThetaMove.negT_fibre_comm | (intros; apply GlobalTheory.ThetaMove.negT_fibre_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupPowValueEqOfConjugateTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupPowValueEqOfConjugateTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaPowConj

theorem prod_telescope {U : Type} [CommGroup U] (F G : ℕ → U) (n : ℕ) :
    ∏ i ∈ Finset.range n, (F i * G i * (F (i + 1))⁻¹) = F 0 * (∏ i ∈ Finset.range n, G i) * (F n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
    group

theorem val_powGen_transport : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (N : ℕ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : ∀ i : ℕ, f ≫ (translT A (θ.pt ^ i)).left = (translT A' (θ'.pt ^ i)).left ≫ f) (hN : θ'.pt ^ N = 1) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (powGen A L k θ N) (q ≫ f) z J = val (powGen A' L' k θ' N) q z J' := by
  intro S S' A A' _ _ L L' T T' f k N θ θ' Ψ hT hN H Z q z J J' hJ hJ'
  rw [GlobalTheory.ConjPull.val_thetaPow θ N (q ≫ f) z hJ, GlobalTheory.ConjPull.val_thetaPow θ' N q z hJ']
  have step : ∀ i ∈ Finset.range N,
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        ((q ≫ f) ≫ (translT A (θ.pt ^ i)).left) z J =
      Ψ (q ≫ (translT A' (θ'.pt ^ i)).left) z J J' ^ k *
        val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ
          (q ≫ (translT A' (θ'.pt ^ i)).left) z J' *
        (Ψ (q ≫ (translT A' (θ'.pt ^ (i + 1))).left) z J J' ^ k)⁻¹ := by
    intro i _
    have e1 : (q ≫ f) ≫ (translT A (θ.pt ^ i)).left = (q ≫ (translT A' (θ'.pt ^ i)).left) ≫ f := by
      rw [Category.assoc, hT i, Category.assoc]
    have e2 : (q ≫ (translT A' (θ'.pt ^ i)).left) ≫ (translT A' θ'.pt).left =
        q ≫ (translT A' (θ'.pt ^ (i + 1))).left := by
      rw [Category.assoc, ← Over.comp_left, GlobalTheory.PullMove.translT_mul, pow_succ']
    rw [e1, H Z _ z J J' hJ hJ', e2]
  rw [Finset.prod_congr rfl step,
    prod_telescope (fun i => Ψ (q ≫ (translT A' (θ'.pt ^ i)).left) z J J' ^ k)
      (fun i => val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ
          (q ≫ (translT A' (θ'.pt ^ i)).left) z J')]
  simp only [hN, pow_zero]
  rw [mul_comm, ← _root_.mul_assoc, inv_mul_cancel, _root_.one_mul]

end GlobalTheory.ThetaPowConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupPowValueEqOfConjugateTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (N : ℕ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : ∀ i : ℕ, f ≫ (translT A (θ.pt ^ i)).left = (translT A' (θ'.pt ^ i)).left ≫ f) (hN : θ'.pt ^ N = 1) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (powGen A L k θ N) (q ≫ f) z J = val (powGen A' L' k θ' N) q z J' := by
  first | exact @GlobalTheory.ThetaPowConj.val_powGen_transport | exact GlobalTheory.ThetaPowConj.val_powGen_transport | (intros; apply GlobalTheory.ThetaPowConj.val_powGen_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMovedToCoverSide
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMovedToCoverSide
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem exists_gen_up : ∀ {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT} (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG} (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen) (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) [IsIso f] (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y') (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ) (u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k])) (hu' : u'.IsGen), ∃ u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt, Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt → val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt * (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  intro XA XP XG XT Y Y' LA LP LG LT hA hP hG hT α β c wA hwA ℓ hℓ w hw f _ sA mA sT mT e' h₁ h₂ h₃ k u' hu'
  obtain ⟨t1, ht1, v1⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff w).1 hw) hG hT (φ' := ![sT, mT])
    (ε := ![k, -k]) u' hu'
  obtain ⟨t2, ht2, v2⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff ℓ).1 hℓ) hP hG
    (φ' := fun i => ![sT, mT] i ≫ c) (ε := ![k, -k]) t1 ht1
  have ht3 := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen LP _ _ t2 ht2 (inv f)
  have hfe : ∀ i, inv f ≫ (![sT, mT] i ≫ c) ≫ β = ![sA, mA] i ≫ α := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, Category.assoc, ← h₁, IsIso.inv_hom_id_assoc]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Category.assoc]
      rw [← h₂, Category.assoc, ← h₁, reassoc_of% h₃, IsIso.inv_hom_id_assoc]
  obtain ⟨t4, ht4, v4⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hP (φ' := fun i => ![sA, mA] i ≫ α) (ε' := ![k, -k])
    (fun U _ h => by simp only [hfe]) _ ht3
  obtain ⟨u, hu, v5⟩ := GlobalTheory.ArcPull.exists_down_om hwA hP hA (φ' := ![sA, mA]) (φ := fun i => ![sA, mA] i ≫ α)
    (𝟙 Y) (fun i => (Category.id_comp _).symm) t4 ht4
  refine ⟨u, hu, fun Z q z JP JA JG Jt gP gA gG gT => ?_⟩
  have e5 := v5 Z (q ≫ f) z JP JA gP gA
  have e4 := v4 Z ((q ≫ f) ≫ 𝟙 Y) z JP gP
  have e3 := ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull gP t2 (inv f) ((q ≫ f) ≫ 𝟙 Y)
  have hq : ((q ≫ f) ≫ 𝟙 Y) ≫ inv f = q := by simp
  rw [hq] at e3
  have e2 : val t2 q z JP = pw ℓ (fun i => ![sT, mT] i ≫ c) ![k, -k] q z _ _ * val t1 q z JG :=
    v2 Z q z _ _ (gP.mem _ q) (gG.mem _ q)
  have e1 : val t1 q z JG = pw w ![sT, mT] ![k, -k] q z _ _ * val u' q z Jt := v1 Z q z _ _ (gG.mem _ q) (gT.mem _ q)
  have h₄ : f ≫ mA ≫ α = mT ≫ c ≫ β := by rw [← reassoc_of% h₃, h₁, reassoc_of% h₂]
  simp only [pw, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, GlobalTheory.ArcPull.om, tf, Category.assoc, Category.comp_id] at e1 e2 e3 e4 e5 ⊢
  have p₁ : q ≫ f ≫ sA ≫ α = q ≫ sT ≫ c ≫ β := by rw [h₁]
  have p₄ : q ≫ f ≫ mA ≫ α = q ≫ mT ≫ c ≫ β := by rw [h₄]
  have p₃ : q ≫ e' ≫ f ≫ sA = q ≫ f ≫ mA := by rw [h₃]
  have p₂ : q ≫ e' ≫ sT = q ≫ mT := by rw [h₂]
  have p₂' : q ≫ e' ≫ sT ≫ c = q ≫ mT ≫ c := by rw [reassoc_of% h₂]
  have p₂'' : q ≫ e' ≫ sT ≫ c ≫ β = q ≫ mT ≫ c ≫ β := by rw [reassoc_of% h₂]
  rw [e4, e3, e2, e1, p₁, p₄] at e5
  rw [p₃, p₂'', p₂', p₂]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e5
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
  linear_combination (norm := module) -e'

end GlobalTheory.ThetaMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMovedToCoverSideStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_moved_to_cover_side : ∀ {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT} (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG} (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen) (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) [IsIso f] (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y') (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ) (u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k])) (hu' : u'.IsGen), ∃ u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt, Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt → val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt * (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  first | exact @GlobalTheory.ThetaMove.exists_gen_up | exact GlobalTheory.ThetaMove.exists_gen_up | (intros; apply GlobalTheory.ThetaMove.exists_gen_up <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetryValueEqOfConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetryValueEqOfConjugate
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaSymTransport

theorem val_symGen_eq : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (ν : LB.Gen (negLB A L k T)) (ν' : LB.Gen (negLB A' L' k T')) (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt⁻¹).left = (translT A' θ'.pt⁻¹).left ≫ f) (hneg : f ≫ (negT A T).left = (negT A' T').left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Hν : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (snd T' A' ≫ (GrpObj.inv : A' ⟶ A')).left]) (ε := ![k, -k]) ν' q z J' * (Ψ (q ≫ (negT A' T').left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (symGen A L k θ ν) (q ≫ f) z J = val (symGen A' L' k θ' ν') q z J' := by
  intro S S' A A' _ _ _ L L' T T' f k θ θ' ν ν' Ψ hT hneg H Hν Z q z J J' hJ hJ'
  have c₁ : (translT A' θ'.pt⁻¹).left ≫ (translT A' θ'.pt).left = 𝟙 _ := by
    rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, mul_inv_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]
  have c₂ : (negT A' T').left ≫ (translT A' θ'.pt).left = (translT A' θ'.pt⁻¹).left ≫ (negT A' T').left := by
    rw [← Over.comp_left, ← Over.comp_left, GlobalTheory.PullMove.negT_translT]
  have e₁ := H Z (q ≫ (translT A' θ'.pt⁻¹).left) z J J' hJ hJ'
  have e₂ := H Z (q ≫ (negT A' T').left) z J J' hJ hJ'
  have e₃ := Hν Z q z J J' hJ hJ'
  have e₄ := Hν Z (q ≫ (translT A' θ'.pt⁻¹).left) z J J' hJ hJ'
  simp only [Category.assoc, c₁, c₂, Category.comp_id, ← hT, ← hneg] at e₁ e₂ e₄
  rw [GlobalTheory.ConjPull.val_thetaSym _ _ _ _ hJ, GlobalTheory.ConjPull.val_thetaSym _ _ _ _ hJ']
  simp only [Category.assoc]
  rw [e₁, e₂, e₃, e₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  abel

end GlobalTheory.ThetaSymTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupSymmetryValueEqOfConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A'] {L : LB A.left} {L' : LB A'.left} {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (ν : LB.Gen (negLB A L k T)) (ν' : LB.Gen (negLB A' L' k T')) (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt⁻¹).left = (translT A' θ'.pt⁻¹).left ≫ f) (hneg : f ≫ (negT A T).left = (negT A' T').left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (Hν : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (snd T' A' ≫ (GrpObj.inv : A' ⟶ A')).left]) (ε := ![k, -k]) ν' q z J' * (Ψ (q ≫ (negT A' T').left) z J J' ^ k)⁻¹) (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J' (hJ : Good L z J) (hJ' : Good L' z J'), val (symGen A L k θ ν) (q ≫ f) z J = val (symGen A' L' k θ' ν') q z J' := by
  first | exact @GlobalTheory.ThetaSymTransport.val_symGen_eq | exact GlobalTheory.ThetaSymTransport.val_symGen_eq | (intros; apply GlobalTheory.ThetaSymTransport.val_symGen_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionCompatFibreIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionCompatFibreIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem isActOf_of_fibreIso : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) [IsIso f] (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt).left = (translT A' θ'.pt).left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (σ σ' : LB.Sec (LPow A' L' k T')) (τ τ' : LB.Sec (LPow A L k T)) (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ q z J') (hσ' : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ' (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ' q z J') (hact : IsActOf A' L' k θ' σ σ'), IsActOf A L k θ τ τ' := by
  intro S S' A A' _ _ L L' hL hL' T T' f _ k θ θ' Ψ hT H σ σ' τ τ' hσ hσ' hact
  refine GlobalTheory.ThetaNu.isActOf_of_sval hL fun y J hJ => ?_
  choose J' hJ' using fun χ : (T ⊗ A).left ⟶ A'.left => exists_chart hL' (χ y)
  have gJ' : Good L' y J' := hJ'
  have e1 := hσ' _ (inv f) y J J' hJ gJ'
  have e2 := twist_val hact (inv f) y gJ'
  have e3 := H _ (inv f) y J J' hJ gJ'
  have e4 := hσ _ (inv f ≫ (translT A' θ'.pt).left) y J J' hJ gJ'
  have c : (inv f ≫ (translT A' θ'.pt).left) ≫ f = 𝟙 _ ≫ (translT A θ.pt).left := by
    rw [Category.assoc, ← hT, ← Category.assoc, IsIso.inv_hom_id]
  rw [IsIso.inv_hom_id] at e1 e3
  rw [c] at e4
  rw [e1, e2, e4, e3]
  generalize Ψ (inv f ≫ (translT A' θ'.pt).left) y J J' ^ k = a
  generalize Ψ (inv f) y J J' ^ k = b
  generalize val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ (inv f) y J' = v
  generalize sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ
    (inv f ≫ (translT A' θ'.pt).left) y J' = w
  rw [Units.val_mul, Units.val_mul]
  linear_combination (-(b.val * v.val * w)) * a.mul_inv

end GlobalTheory.ThetaMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionCompatFibreIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroupAction_compat_fibreIso : ∀ {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) {T : Over S} {T' : Over S'} (f : (T' ⊗ A').left ⟶ (T ⊗ A).left) [IsIso f] (k : ℤ) (θ : ThetaGrp A L k T) (θ' : ThetaGrp A' L' k T') (Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (T' ⊗ A').left) → ∀ z : Z, ((Z ⟶ A.left) → L.ι) → ((Z ⟶ A'.left) → L'.ι) → (Z.presheaf.stalk z)ˣ) (hT : f ≫ (translT A θ.pt).left = (translT A' θ'.pt).left ≫ f) (H : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (q ≫ f) z J = Ψ q z J J' ^ k * val (L := L') (φ := ![(snd T' A').left, (translPt A' θ'.pt).left]) (ε := ![k, -k]) θ'.φ q z J' * (Ψ (q ≫ (translT A' θ'.pt).left) z J J' ^ k)⁻¹) (σ σ' : LB.Sec (LPow A' L' k T')) (τ τ' : LB.Sec (LPow A L k T)) (hσ : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ q z J') (hσ' : ∀ (Z : Scheme.{0}) (q : Z ⟶ (T' ⊗ A').left) (z : Z) J J', Good L z J → Good L' z J' → sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) τ' (q ≫ f) z J = (Ψ q z J J' ^ k).val * sval (L := L') (φ := fun _ : Fin 1 => (snd T' A').left) (ε := fun _ => k) σ' q z J') (hact : IsActOf A' L' k θ' σ σ'), IsActOf A L k θ τ τ' := by
  first | exact @GlobalTheory.ThetaMove.isActOf_of_fibreIso | exact GlobalTheory.ThetaMove.isActOf_of_fibreIso | (intros; apply GlobalTheory.ThetaMove.isActOf_of_fibreIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoRestrictAlongSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoRestrictAlongSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

noncomputable section

namespace GlobalTheory.IsoRes

variable {XG XT Pb : Scheme.{0}} {LG : LB XG} {LT : LB XT} {c : Pb ⟶ XG} {g : Pb ⟶ XT} {gi : XT ⟶ Pb}

theorem comp_pt {A B C : Scheme.{0}} (f : A ⟶ B) (h : B ⟶ C) (x : A) : (f ≫ h) x = h (f x) := by
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply]

theorem sec_apply (hgi : gi ≫ g = 𝟙 XT) (x : XT) : g (gi x) = x := by
  rw [← comp_pt, hgi]; rfl

theorem chart_le (hgi : gi ≫ g = 𝟙 XT) (J : PUnit → LG.ι) (k : LT.ι) :
    (LG.pull (gi ≫ c)).U J ⊓ LT.U k ≤ gi ⁻¹ᵁ ((LG.pull c).U J ⊓ (LT.pull g).U (fun _ => k)) := by
  intro x hx
  refine ⟨mem_pull.2 ?_, mem_pull.2 ?_⟩
  · have := mem_pull.1 hx.1
    rwa [comp_pt] at this
  · rw [sec_apply hgi]; exact hx.2

def resIso (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) : LB.Iso LT (LG.pull (gi ≫ c)) where
  s := fun p => res (chart_le hgi p.1 p.2) (pullU gi _ (w₀.s (p.1, fun _ => p.2)))

theorem gw_resIso (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) {Z : Scheme.{0}} (r : Z ⟶ XT) (z : Z)
    (j : LG.ι) (k : LT.ι) : gw (resIso hgi w₀) r z j k = gw w₀ (r ≫ gi) z j (fun _ => k) := by
  by_cases h : r z ∈ (LG.pull (gi ≫ c)).U (fun _ => j) ⊓ LT.U k
  · have h' : gi (r z) ∈ (LG.pull c).U (fun _ => j) ⊓ (LT.pull g).U (fun _ => k) := chart_le hgi _ _ h
    exact (gm_res r z _ h _).trans (gm_pull r gi z _ h' _)
  · have h' : ¬ (r ≫ gi) z ∈ (LG.pull c).U (fun _ => j) ⊓ (LT.pull g).U (fun _ => k) := by
      intro hm
      apply h
      rw [comp_pt] at hm
      refine ⟨mem_pull.2 ?_, ?_⟩
      · rw [comp_pt]; exact mem_pull.1 hm.1
      · have := mem_pull.1 hm.2
        rwa [sec_apply hgi] at this
    show gm r z _ _ = gm (r ≫ gi) z _ _
    rw [gm, gm, dite_eq_right h, dite_eq_right h']; rfl

theorem resIso_pgen (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) (hw₀ : PGen w₀) :
    PGen (resIso hgi w₀) := by
  intro Y f y j j' k k' hj hj' hk hk'
  rw [gw_resIso, gw_resIso]
  rw [comp_pt] at hj hj'
  have hj0 : c ((f ≫ gi) y) ∈ LG.U j := by rw [comp_pt]; exact hj
  have hj0' : c ((f ≫ gi) y) ∈ LG.U j' := by rw [comp_pt]; exact hj'
  have hk0 : (f ≫ gi) y ∈ (LT.pull g).U (fun _ => k) := mem_pull.2 (by rw [comp_pt, sec_apply hgi]; exact hk)
  have hk0' : (f ≫ gi) y ∈ (LT.pull g).U (fun _ => k') := mem_pull.2 (by rw [comp_pt, sec_apply hgi]; exact hk')
  have e := hw₀ Y (f ≫ gi) y j j' (fun _ => k) (fun _ => k') hj0 hj0' hk0 hk0'
  have e2 : gm (f ≫ gi) y ((LT.pull g).U (fun _ => k) ⊓ (LT.pull g).U (fun _ => k'))
      ((LT.pull g).g (fun _ => k) (fun _ => k')) = gm f y _ (LT.g k k') := by
    show gm (f ≫ gi) y _ (∏ _k : PUnit, (res _ (pullU g _ (LT.g k k'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_res (f ≫ gi) y _
      (show (f ≫ gi) y ∈ (LT.pull g).U (fun _ => k) ⊓ (LT.pull g).U (fun _ => k') from ⟨hk0, hk0'⟩) _).trans
      ((gm_pull (f ≫ gi) g y (LT.U k ⊓ LT.U k') ⟨mem_pull.1 hk0, mem_pull.1 hk0'⟩ _).trans ?_)
    rw [Category.assoc, hgi, Category.comp_id]
  rw [e, e2, Category.assoc]

theorem exists_iso_restrict : ∀ {XG XT Pb : Scheme.{0}} {LG : LB XG} {LT : LB XT} (hG : LG.IsLB) (hT : LT.IsLB) {c : Pb ⟶ XG} {g : Pb ⟶ XT} {gi : XT ⟶ Pb} (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) (hw₀ : w₀.IsGen), ∃ w : LB.Iso LT (LG.pull (gi ≫ c)), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ XT) (z : Z) (j : LG.ι) (k : LT.ι), gw w r z j k = gw w₀ (r ≫ gi) z j (fun _ => k) := by
  intro XG XT Pb LG LT hG hT c g gi hgi w₀ hw₀
  exact ⟨resIso hgi w₀, (isGen_iff _).2 (resIso_pgen hgi w₀ ((isGen_iff _).1 hw₀)),
    fun Z r z j k => gw_resIso hgi w₀ r z j k⟩

end GlobalTheory.IsoRes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoRestrictAlongSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleIso_restrict_along_section : ∀ {XG XT Pb : Scheme.{0}} {LG : LB XG} {LT : LB XT} (hG : LG.IsLB) (hT : LT.IsLB) {c : Pb ⟶ XG} {g : Pb ⟶ XT} {gi : XT ⟶ Pb} (hgi : gi ≫ g = 𝟙 XT) (w₀ : LB.Iso (LT.pull g) (LG.pull c)) (hw₀ : w₀.IsGen), ∃ w : LB.Iso LT (LG.pull (gi ≫ c)), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ XT) (z : Z) (j : LG.ι) (k : LT.ι), gw w r z j k = gw w₀ (r ≫ gi) z j (fun _ => k) := by
  first | exact @GlobalTheory.IsoRes.exists_iso_restrict | exact GlobalTheory.IsoRes.exists_iso_restrict | (intros; apply GlobalTheory.IsoRes.exists_iso_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitFibreIsoCommTranslation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitFibreIsoCommTranslation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

noncomputable section

namespace GlobalTheory.Mum

theorem tensorLeft_hom_ext {S : Scheme.{0}} {X Y : Over S} {Z : Scheme.{0}} {a b : Z ⟶ (X ⊗ Y).left}
    (h1 : a ≫ (fst X Y).left = b ≫ (fst X Y).left) (h2 : a ≫ (snd X Y).left = b ≫ (snd X Y).left) : a = b :=
  pullback.hom_ext h1 h2

theorem trait_transl_comm : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A) (hx : (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left), f ≫ (translT C.A.A x).left = (translT T.A.A x').left ≫ f := by
  intro R _ _ _ D C W _ _ _ T F _ _ _ f hf1 hf2 x' x hx
  have gT : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ)
      (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) := by
    have := (ThetaBaseChange.grp_generic T.U.toUnifPre).comp T.cart
    simpa only [Category.assoc] using this
  have gC := C.α_cart
  have hxx : x.left ≫ C.α = x'.left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
    have e1 : x.left = (ptSecT C.A.A x).left ≫ (snd (TFK (R := R) F) C.A.A).left := by
      rw [← Over.comp_left, ptSecT, lift_snd]
    have e2 : x'.left = (ptSecT T.A.A x').left ≫ (snd (TFK (R := W) F) T.A.A).left := by
      rw [← Over.comp_left, ptSecT, lift_snd]
    rw [e1, ← hx, Category.assoc, Category.assoc, hf2, ← Category.assoc, ← Category.assoc, ← e2]
    simp only [Category.assoc]
  have hbase : f ≫ (TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp = (TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ := by
    have a1 : (TFK (R := R) F ⊗ C.A.A).hom = (snd (TFK (R := R) F) C.A.A).left ≫ C.A.A.hom := (Over.w _).symm
    have a2 : (TFK (R := W) F ⊗ T.A.A).hom = (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom := (Over.w _).symm
    have w := gT.1.w
    simp only [Category.assoc] at w
    rw [a1, a2, Category.assoc, Category.assoc, ← gC.1.w, reassoc_of% hf2, w]
  apply tensorLeft_hom_ext
  · simp only [Category.assoc, ← Over.comp_left, translT, lift_fst, hf1]
  · rw [Category.assoc, Category.assoc]
    apply gC.1.hom_ext
    · have eL : (translT C.A.A x).left ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α =
          ((pushPt gC.1.w (fst (TFK (R := R) F) C.A.A ≫ x)) * (pushPt gC.1.w (snd (TFK (R := R) F) C.A.A))).left := by
        rw [gC.2 _ _ _ _ _ rfl rfl, ← Category.assoc, ← Over.comp_left, translT, lift_snd, translPt_eq]
      have eR : (translT T.A.A x').left ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫
          pullback.fst T.G.hom (jK W) ≫ T.β =
          ((pushPt gT.1.w (fst (TFK (R := W) F) T.A.A ≫ x')) * (pushPt gT.1.w (snd (TFK (R := W) F) T.A.A))).left := by
        rw [gT.2 _ _ _ _ _ rfl rfl, ← Category.assoc, ← Over.comp_left, translT, lift_snd, translPt_eq]
      let ρ : Over.mk ((TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ) ⟶ Over.mk ((TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp) :=
        Over.homMk f hbase
      have e0 : ρ ≫ pushPt gC.1.w (fst (TFK (R := R) F) C.A.A ≫ x) = pushPt gT.1.w (fst (TFK (R := W) F) T.A.A ≫ x') := by
        ext
        show f ≫ (fst (TFK (R := R) F) C.A.A ≫ x).left ≫ C.α = (fst (TFK (R := W) F) T.A.A ≫ x').left ≫ _
        simp only [Over.comp_left, Category.assoc]
        rw [hxx, reassoc_of% hf1]
      have e1 : ρ ≫ pushPt gC.1.w (snd (TFK (R := R) F) C.A.A) = pushPt gT.1.w (snd (TFK (R := W) F) T.A.A) := by
        ext
        exact hf2
      simp only [Category.assoc]
      rw [eL, hf2, eR, ← e0, ← e1, ← MonObj.comp_mul]
      rfl
    · simp only [Category.assoc]
      rw [Over.w (snd (TFK (R := R) F) C.A.A), Over.w (translT C.A.A x), ← Over.w (fst (TFK (R := R) F) C.A.A),
        reassoc_of% hf1, ← Category.assoc, ← Over.comp_left, translT, lift_fst]

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitFibreIsoCommTranslationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitFibreIso_comm_translation : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A) (hx : (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left), f ≫ (translT C.A.A x).left = (translT T.A.A x').left ≫ f := by
  first | exact @GlobalTheory.Mum.trait_transl_comm | exact GlobalTheory.Mum.trait_transl_comm | (intros; apply GlobalTheory.Mum.trait_transl_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTrait
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem GlobalTheory.ThetaMove.ptSec_transl' {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (p x : T ⟶ A) :
    (ptSecT A p).left ≫ (translT A x).left = (ptSecT A (x * p)).left := by
  rw [← Over.comp_left]
  congr 1
  rw [ptSecT, translT, comp_lift, lift_fst, ptSecT, translPt_eq, MonObj.comp_mul, lift_fst_assoc, Category.id_comp,
    lift_snd]

theorem GlobalTheory.ThetaMove.translT_inv {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (x : T ⟶ A) :
    (translT A x).left ≫ (translT A x⁻¹).left = 𝟙 _ ∧ (translT A x⁻¹).left ≫ (translT A x).left = 𝟙 _ := by
  constructor
  · rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, inv_mul_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]
  · rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, mul_inv_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]

theorem GlobalTheory.ThetaMove.transport_symLift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A), (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left → x' ^ (C.n ^ j) = 1 → ((∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ') → ∃ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ) ∧ ∀ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ → ∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ' ∧ ∀ (σ σ' : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j)) (τ τ' : SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ' p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ' q z Jt) → IsActOf T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) θ' σ σ' → IsActOf C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) θ τ τ' := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ hφ f hf hf1 hf2 w₀ hw₀ x' x hx hx'
  have hPL := C.P.L.isLB
  have hAL := C.A.isLB
  have hGL := T.U.LG.isLB
  have hTL := T.A.isLB
  have hgi : T.U.gen.inv.left ≫ T.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  obtain ⟨w, hw, hgw⟩ := GlobalTheory.T.exists_lineBundleIso_restrict_along_section hGL hTL hgi w₀ hw₀
  have h₁ : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α =
      (snd (TFK (R := W) F) T.A.A).left ≫ (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.β := by
    rw [Category.assoc]; exact hf2
  have hT1 := GlobalTheory.T.traitFibreIso_comm_translation C T F f hf1 hf2 x' x hx
  have hneg := GlobalTheory.T.traitFibreIso_comm_neg C T F f hf1 hf2
  have hinv : f ≫ (translT C.A.A x⁻¹).left = (translT T.A.A x'⁻¹).left ≫ f := by
    calc f ≫ (translT C.A.A x⁻¹).left
        = ((translT T.A.A x'⁻¹).left ≫ (translT T.A.A x').left) ≫ f ≫ (translT C.A.A x⁻¹).left := by
          rw [(translT_inv x').2, Category.id_comp]
      _ = (translT T.A.A x'⁻¹).left ≫ (f ≫ (translT C.A.A x).left) ≫ (translT C.A.A x⁻¹).left := by
          rw [hT1]; simp only [Category.assoc]
      _ = (translT T.A.A x'⁻¹).left ≫ f := by
          rw [Category.assoc, (translT_inv x).1, Category.comp_id]
  have hpt : ∀ i : ℕ, (ptSecT T.A.A (x' ^ i)).left ≫ f = (ptSecT C.A.A (x ^ i)).left := by
    intro i
    induction i with
    | zero =>
      rw [pow_zero, pow_zero, ← inv_mul_cancel x', ← inv_mul_cancel x, ← ptSec_transl', ← ptSec_transl',
        Category.assoc, ← hinv, ← Category.assoc, hx]
    | succ i ih =>
      rw [pow_succ', pow_succ', ← ptSec_transl', ← ptSec_transl', Category.assoc, ← hT1, ← Category.assoc, ih]
  have hpow : ∀ i : ℕ, f ≫ (translT C.A.A (x ^ i)).left = (translT T.A.A (x' ^ i)).left ≫ f :=
    fun i => GlobalTheory.T.traitFibreIso_comm_translation C T F f hf1 hf2 _ _ (hpt i)
  have hG0 : ((snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.G.hom =
      (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    have e1 : T.U.gen.inv.left ≫ pullback.snd T.G.hom (jK W) = T.A.A.hom := Over.w T.U.gen.inv
    have e2 : (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom = (fst (TFK (R := W) F) T.A.A).left ≫ jFK (R := W) F :=
      (Over.w (snd (TFK (R := W) F) T.A.A)).trans (Over.w (fst (TFK (R := W) F) T.A.A)).symm
    have e3 : jFK (R := W) F ≫ jK W = spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
      unfold jFK jK spMap
      rw [← Spec.map_comp]
      rfl
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc T.U.gen.inv.left, e1, ← Category.assoc,
      e2, Category.assoc, e3]
  let JPc : ∀ {Z : Scheme.{0}} (z : Z), (Z ⟶ C.G.left) → C.P.L.L.ι := fun z ψ => (exists_chart hPL (ψ z)).choose
  have gJP : ∀ {Z : Scheme.{0}} (z : Z), Good C.P.L.L z (JPc z) := fun z ψ => (exists_chart hPL (ψ z)).choose_spec
  let JGc : ∀ {Z : Scheme.{0}} (z : Z), (Z ⟶ T.G.left) → T.U.LG.L.ι := fun z ψ => (exists_chart hGL (ψ z)).choose
  have gJG : ∀ {Z : Scheme.{0}} (z : Z), Good T.U.LG.L z (JGc z) := fun z ψ => (exists_chart hGL (ψ z)).choose_spec
  let Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (TFK (R := W) F ⊗ T.A.A).left) → ∀ z : Z, ((Z ⟶ C.A.A.left) → C.A.L.ι) →
      ((Z ⟶ T.A.A.left) → T.A.L.ι) → (Z.presheaf.stalk z)ˣ := fun q z JA Jt =>
    tf wA T.ℓ w f (snd (TFK (R := R) F) C.A.A).left (snd (TFK (R := W) F) T.A.A).left q z (JPc z) JA (JGc z) Jt
  have conv : ∀ (σ : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j))
      (τ : SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) →
      ∀ (Z : Scheme.{0}) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left) (z : Z) JA Jt, Good C.A.L z JA → Good T.A.L z Jt →
        sval τ (q ≫ f) z JA = (Ψ q z JA Jt ^ ((C.n ^ j : ℕ) : ℤ)).val * sval σ q z Jt := by
    intro σ τ hr Z q z JA Jt hJA hJt
    have e := hr Z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) (q ≫ f) q
      rfl (by simp only [Category.assoc]; rw [hf2]) (by rw [Category.assoc, hG0]) z (JPc z) JA (JGc z) Jt (gJP z) hJA
      (gJG z) hJt
    simp only [Category.assoc] at e
    show sval τ (q ≫ f) z JA = ((tf wA T.ℓ w f (snd (TFK (R := R) F) C.A.A).left (snd (TFK (R := W) F) T.A.A).left
      q z (JPc z) JA (JGc z) Jt) ^ ((C.n ^ j : ℕ) : ℤ)).val * sval σ q z Jt
    simp only [tf, hgw, Category.assoc]
    rw [zpow_natCast, mul_pow, mul_pow, inv_pow, Units.val_mul, Units.val_mul]
    calc sval τ (q ≫ f) z JA
        = (((gw wA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left) z
            (JPc z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β))
            (JA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left))) ^ (C.n ^ j))⁻¹).val *
          ((gw wA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left) z
            (JPc z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β))
            (JA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ (q ≫ f) z JA) := by
          rw [← _root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.one_mul]
      _ = _ := by rw [e]; ring
  have hs₂ : ∀ p : TFK (R := W) F ⟶ T.A.A, (translT T.A.A p).left ≫ (snd (TFK (R := W) F) T.A.A).left =
      (translPt T.A.A p).left := fun p => by rw [← Over.comp_left, translT, lift_snd]
  have hn₂ : (negT T.A.A (TFK (R := W) F)).left ≫ (snd (TFK (R := W) F) T.A.A).left =
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left := by rw [← Over.comp_left, negT, lift_snd]
  have hn₃ : (negT T.A.A (TFK (R := W) F)).left ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left =
      f ≫ (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left := by
    rw [← Category.assoc, ← hneg, Category.assoc, ← Over.comp_left, negT, lift_snd]
  have hs₃ : (translT T.A.A x').left ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left = f ≫ (translPt C.A.A x).left := by
    rw [← Category.assoc, ← hT1, Category.assoc, ← Over.comp_left, translT, lift_snd]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨pt', φ', hφ'⟩, hs'⟩
    have e0 : pt' = x' := hs'.pt_eq
    subst e0
    obtain ⟨u, hu, hvu⟩ := GlobalTheory.T.exists_generator_moved_to_cover_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (translPt C.A.A x).left (snd (TFK (R := W) F) T.A.A).left (translPt T.A.A pt').left (translT T.A.A pt').left h₁
      (hs₂ pt') hs₃ ((C.n ^ j : ℕ) : ℤ) φ' hφ'
    obtain ⟨ν', hν', hsym'⟩ := hs'.sym
    obtain ⟨ν, hν, hvν⟩ := GlobalTheory.T.exists_generator_moved_to_cover_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left (snd (TFK (R := W) F) T.A.A).left
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left (negT T.A.A (TFK (R := W) F)).left h₁ hn₂ hn₃
      ((C.n ^ j : ℕ) : ℤ) ν' hν'
    have Hu := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvu Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    have Hν := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvν Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    refine ⟨⟨x, u, hu⟩, ⟨rfl, corr_of_val hAL fun y J hJ => ?_, ν, hν, corr_of_val hAL fun y J hJ => ?_⟩⟩
    · have hJt : Good T.A.L y (fun ψ => (exists_chart hTL (ψ y)).choose) := fun ψ => (exists_chart hTL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion f _ (C.n ^ j) ⟨x, u, hu⟩ ⟨pt', φ', hφ'⟩ Ψ hpow hx' Hu _ (inv f) y J _ hJ hJt
      rw [IsIso.inv_hom_id] at e
      rw [e, val_corr hJt hs'.pow_eq (inv f), val_one, val_one]
    · have hJt : Good T.A.L y (fun ψ => (exists_chart hTL (ψ y)).choose) := fun ψ => (exists_chart hTL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate f _ ⟨x, u, hu⟩ ⟨pt', φ', hφ'⟩ ν ν' Ψ hinv hneg Hu Hν _ (inv f) y J _ hJ hJt
      rw [IsIso.inv_hom_id] at e
      rw [e, val_corr hJt hsym' (inv f), val_one, val_one]
  · rintro ⟨pt, φ, hφ⟩ hs
    have e0 : pt = x := hs.pt_eq
    subst e0
    obtain ⟨u', hu', hvu'⟩ := GlobalTheory.T.exists_generator_moved_to_trait_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (translPt C.A.A pt).left (snd (TFK (R := W) F) T.A.A).left (translPt T.A.A x').left (translT T.A.A x').left h₁
      (hs₂ x') hs₃ ((C.n ^ j : ℕ) : ℤ) φ hφ
    obtain ⟨ν, hν, hsym⟩ := hs.sym
    obtain ⟨ν', hν', hvν'⟩ := GlobalTheory.T.exists_generator_moved_to_trait_side hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left (snd (TFK (R := W) F) T.A.A).left
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left (negT T.A.A (TFK (R := W) F)).left h₁ hn₂ hn₃
      ((C.n ^ j : ℕ) : ℤ) ν hν
    have Hu := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvu' Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    have Hν := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvν' Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    refine ⟨⟨x', u', hu'⟩, ⟨rfl, corr_of_val hTL fun y J' hJ' => ?_, ν', hν', corr_of_val hTL fun y J' hJ' => ?_⟩, ?_⟩
    · have hJA : Good C.A.L y (fun ψ => (exists_chart hAL (ψ y)).choose) := fun ψ => (exists_chart hAL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion f _ (C.n ^ j) ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ Ψ hpow hx' Hu _ (𝟙 _) y _ J' hJA hJ'
      rw [← e, val_corr hJA hs.pow_eq, val_one, val_one]
    · have hJA : Good C.A.L y (fun ψ => (exists_chart hAL (ψ y)).choose) := fun ψ => (exists_chart hAL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate f _ ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ ν ν' Ψ hinv hneg Hu Hν _ (𝟙 _) y _ J' hJA hJ'
      rw [← e, val_corr hJA hsym, val_one, val_one]
    · intro σ σ' τ τ' hr hr' hact
      exact GlobalTheory.T.thetaGroupAction_compat_fibreIso hAL hTL f _ ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ Ψ hT1 Hu σ σ' τ τ' (conv σ τ hr) (conv σ' τ' hr') hact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_symmetric_lifts_theta_group_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A), (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left → x' ^ (C.n ^ j) = 1 → ((∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ') → ∃ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ) ∧ ∀ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ → ∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ' ∧ ∀ (σ σ' : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j)) (τ τ' : SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ' p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ' q z Jt) → IsActOf T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) θ' σ σ' → IsActOf C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) θ τ τ' := by
  first | exact @GlobalTheory.ThetaMove.transport_symLift | exact GlobalTheory.ThetaMove.transport_symLift | (intros; apply GlobalTheory.ThetaMove.transport_symLift <;> assumption)
end
