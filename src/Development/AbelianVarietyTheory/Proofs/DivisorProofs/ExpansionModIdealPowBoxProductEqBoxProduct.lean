module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorPeriodsProjectionPeriodPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomTorsionCompatiblePeriodsLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgClosedFieldTorsionMapsCommuteHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantPointDescendsToSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionModIdealPowBoxProductEqBoxProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionModIdealPowBoxProductEqBoxProduct
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)

theorem fam_mul_Oinv {H : Type} [CommGroup H] (Ω : ((thickObj R I e G).left ⟶ D.toPre.P.A.left) → H)
    (α : D.toPre.X) :
    (∏ a, Ω (pGl U e ≫ D.toPre.famφB α a) ^ DegPre.famε k a) * ∏ a, Ω (Oφl U e α a) ^ Oinvε a =
      Ω (pGl U e) ^ k := by
  have a₀ : (pGl U e) ≫ D.toPre.famφB α 0 = (pGl U e) := Category.comp_id _
  have a₁ : (pGl U e) ≫ D.toPre.famφB α 1 = Oφl U e α 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U.gt e).pG (𝟙 _) (cP D.toPre _ α)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D.toPre _ α)))
  have a₂ : (pGl U e) ≫ D.toPre.famφB α 2 = Oφl U e α 1 :=
    congrArg (fun z => z.left) (comp_cP D.toPre (U.gt e).pG α)
  have a₃ : (pGl U e) ≫ D.toPre.famφB α 3 = Oφl U e α 3 :=
    congrArg (fun z : _ ⟶ D.toPre.P.A => z.left) (MonObj.comp_one (M := D.toPre.P.A) (U.gt e).pG)
  have a₄ : Oφl U e α 2 = (pGl U e) := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

theorem sval_eq_sv (σ : H0 U.LG.L k) {Z : Scheme.{0}} (q : Z ⟶ G.left) (z : Z) (N : (Z ⟶ G.left) → U.LG.L.ι) :
    sval σ q z N = sv U k σ q z (N q) :=
  sval_of σ q z N (fun _ => N q) (fun _ => congrArg N (Category.comp_id _))

end

theorem exp_alg {A X X₁ X₂ : Type} [CommRing A] (k : ℕ) (E : X ≃ X₁ × X₂) (S₁ : Finset X₁) (S₂ : Finset X₂)
    {oM oL W W₁ W₂ : Aˣ} {s s₁ s₂ : A} {f : X → A} {f₁ : X₁ → A} {f₂ : X₂ → A} {t a b : X → Aˣ} {t₁ : X₁ → Aˣ}
    {t₂ : X₂ → Aˣ} (hW : oM * W = W₁ * W₂ * oL) (hs : (oL ^ k).val * s = s₁ * s₂)
    (hf : ∀ x, (a x).val * f x = f₁ (E x).1 * f₂ (E x).2) (ht : ∀ x, b x * t x = t₁ (E x).1 * t₂ (E x).2)
    (ho : ∀ x, a x * b x = oM ^ k) (H₁ : (W₁ ^ k).val * s₁ = ∑ x ∈ S₁, f₁ x * (t₁ x).val)
    (H₂ : (W₂ ^ k).val * s₂ = ∑ x ∈ S₂, f₂ x * (t₂ x).val) :
    (W ^ k).val * s = ∑ x ∈ (S₁ ×ˢ S₂).map E.symm.toEmbedding, f x * (t x).val := by
  refine (oM ^ k).mul_right_inj.1 ?_
  rw [← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, hW, mul_pow, Units.val_mul, _root_.mul_assoc, hs, mul_pow,
    Units.val_mul, _root_.mul_mul_mul_comm, H₁, H₂, Finset.sum_mul_sum, ← Finset.sum_product', Finset.sum_map,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨y, rfl⟩ := E.surjective x
  have e₀ : E.symm.toEmbedding (E y) = y := E.symm_apply_apply y
  rw [e₀, _root_.mul_mul_mul_comm, ← hf, ← Units.val_mul, ← ht, ← ho y, Units.val_mul, Units.val_mul,
    _root_.mul_mul_mul_comm]


set_option maxHeartbeats 1600000 in
theorem expandsAt_boxProd : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)), Function.Bijective (q₁.prod q₂) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (wL : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)) (e k : ℕ), (U.gt e).pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → (U.gt e).pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → (∀ x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left) (Y₂ := (thickObj R I e G₂).left) wM ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ((U.gt e).t x) ((U₁.gt e).t (q₁ x)) ((U₂.gt e).t (q₂ x))) → BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL (U.w e) (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → ∀ (σ : H0 U.LG.L k) (σ₁ : H0 U₁.LG.L k) (σ₂ : H0 U₂.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (f₁ : ∀ α : D₁.toPre.X, D₁.toPre.SecB k α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB k α), IsBoxSec wL (fst G₁ G₂).left (snd G₁ G₂).left σ σ₁ σ₂ → (∀ α, IsBoxSec wM p₁.left p₂.left (f α) (f₁ (q₁ α)) (f₂ (q₂ α))) → U₁.ExpandsAt e k σ₁ f₁ → U₂.ExpandsAt e k σ₂ f₂ → U.ExpandsAt e k σ f := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D p₁ p₂ q₁ q₂ A U hq wM wL e k hp₁ hp₂ hT hW σ σ₁ σ₂ f f₁ f₂ hσ hf
    hE₁ hE₂
  classical
  obtain ⟨S₁, hS₁⟩ := expandsAt_val U₁ e k σ₁ f₁ hE₁
  obtain ⟨S₂, hS₂⟩ := expandsAt_val U₂ e k σ₂ f₂ hE₂
  have hg₁ := thick_fstG I e (fst G₁ G₂)
  have hg₂ := thick_fstG I e (snd G₁ G₂)
  revert hp₁ hp₂ hT hW hg₁ hg₂
  generalize ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left = ρ₁
  generalize ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left = ρ₂
  intro hp₁ hp₂ hT hW hg₁ hg₂
  change (thickObj R I e (G₁ ⊗ G₂)).left ⟶ (thickObj R I e G₁).left at ρ₁
  change (thickObj R I e (G₁ ⊗ G₂)).left ⟶ (thickObj R I e G₂).left at ρ₂
  change pGl U e ≫ p₁.left = ρ₁ ≫ pGl U₁ e at hp₁
  change pGl U e ≫ p₂.left = ρ₂ ≫ pGl U₂ e at hp₂
  change fGl I (G₁ ⊗ G₂) e ≫ (fst G₁ G₂).left = ρ₁ ≫ fGl I G₁ e at hg₁
  change fGl I (G₁ ⊗ G₂) e ≫ (snd G₁ G₂).left = ρ₂ ≫ fGl I G₂ e at hg₂
  let E : D.toPre.X ≃ D₁.toPre.X × D₂.toPre.X := Equiv.ofBijective _ hq
  refine expandsAt_of_val U e k σ f ((S₁ ×ˢ S₂).map E.symm.toEmbedding) fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.toPre.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.toPre.P.isLB y
  have hF : ∀ α, (∏ a, om wM y J₁ J₂ J (pGl U e ≫ D.toPre.famφB α a) ^ DegPre.famε k a).val *
      sval (f α) (pGl U e) y J =
      sval (f₁ (E α).1) (ρ₁ ≫ pGl U₁ e) y J₁ * sval (f₂ (E α).2) (ρ₂ ≫ pGl U₂ e) y J₂ := fun α => by
    rw [← hp₁, ← hp₂]
    exact hf α _ (pGl U e) y J₁ J₂ J hJ₁ hJ₂ hJ
  refine ⟨fun α hα => ?_, fun jL hL => ?_⟩
  · refine (Units.mul_right_eq_zero _).1 ((hF α).trans ?_)
    by_cases h₁ : (E α).1 ∈ S₁
    · have h₂ : (E α).2 ∉ S₂ := fun h₂ =>
        hα (Finset.mem_map.2 ⟨E α, Finset.mem_product.2 ⟨h₁, h₂⟩, E.symm_apply_apply α⟩)
      rw [(hS₂ _ ρ₂ y J₂ hJ₂).1 _ h₂, mul_zero]
    · rw [(hS₁ _ ρ₁ y J₁ hJ₁).1 _ h₁, zero_mul]
  · obtain ⟨N, hN, eN⟩ := exists_good U.LG.L U.LG.isLB y (K := PUnit) (fun _ => fGl I (G₁ ⊗ G₂) e) (fun _ => jL)
      (fun _ _ _ => rfl) (fun _ => hL)
    obtain rfl : N (fGl I (G₁ ⊗ G₂) e) = jL := eN ⟨⟩
    obtain ⟨N₁, hN₁⟩ := BoxFamily.exists_good_at U₁.LG.isLB y
    obtain ⟨N₂, hN₂⟩ := BoxFamily.exists_good_at U₂.LG.isLB y
    have hT' : ∀ α, (∏ a, om wM y J₁ J₂ J (Oφl U e α a) ^ Oinvε a) * val (tG U e α) (𝟙 _) y J =
        val (tG U₁ e (E α).1) ρ₁ y J₁ * val (tG U₂ e (E α).2) ρ₂ y J₂ := fun α => by
      have := hT α _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
      simp only [Category.id_comp] at this
      exact this
    have hW' : om wM y J₁ J₂ J (pGl U e) * wv U e (𝟙 _) y (J (pGl U e)) (N (fGl I (G₁ ⊗ G₂) e)) =
        wv U₁ e ρ₁ y (J₁ (ρ₁ ≫ pGl U₁ e)) (N₁ (ρ₁ ≫ fGl I G₁ e)) *
          wv U₂ e ρ₂ y (J₂ (ρ₂ ≫ pGl U₂ e)) (N₂ (ρ₂ ≫ fGl I G₂ e)) * om wL y N₁ N₂ N (fGl I (G₁ ⊗ G₂) e) := by
      have := hW _ (𝟙 _) y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      simp only [Category.id_comp] at this
      rw [← hp₁, ← hp₂, ← hg₁, ← hg₂]
      exact this
    have hσ' : (om wL y N₁ N₂ N (fGl I (G₁ ⊗ G₂) e) ^ k).val *
        sv U k σ (fGl I (G₁ ⊗ G₂) e) y (N (fGl I (G₁ ⊗ G₂) e)) =
        sv U₁ k σ₁ (ρ₁ ≫ fGl I G₁ e) y (N₁ (ρ₁ ≫ fGl I G₁ e)) *
          sv U₂ k σ₂ (ρ₂ ≫ fGl I G₂ e) y (N₂ (ρ₂ ≫ fGl I G₂ e)) := by
      have := hσ _ (fGl I (G₁ ⊗ G₂) e) y N₁ N₂ N hN₁ hN₂ hN
      rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast] at this
      rw [← sval_eq_sv, ← sval_eq_sv, ← sval_eq_sv, ← hg₁, ← hg₂]
      exact this
    exact exp_alg k E S₁ S₂ hW' hσ' hF hT' (fun α => fam_mul_Oinv U e k (om wM y J₁ J₂ J) α)
      ((hS₁ _ ρ₁ y J₁ hJ₁).2 _ (hN₁ (ρ₁ ≫ fGl I G₁ e))) ((hS₂ _ ρ₂ y J₂ hJ₂).2 _ (hN₂ (ρ₂ ≫ fGl I G₂ e)))

end GlobalTheory.ProdUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionModIdealPowBoxProductEqBoxProductStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansionModIdealPow_boxProduct_eq_boxProduct : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)), Function.Bijective (q₁.prod q₂) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (wL : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)) (e k : ℕ), (U.gt e).pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → (U.gt e).pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → (∀ x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left) (Y₂ := (thickObj R I e G₂).left) wM ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ((U.gt e).t x) ((U₁.gt e).t (q₁ x)) ((U₂.gt e).t (q₂ x))) → BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL (U.w e) (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → ∀ (σ : H0 U.LG.L k) (σ₁ : H0 U₁.LG.L k) (σ₂ : H0 U₂.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (f₁ : ∀ α : D₁.toPre.X, D₁.toPre.SecB k α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB k α), IsBoxSec wL (fst G₁ G₂).left (snd G₁ G₂).left σ σ₁ σ₂ → (∀ α, IsBoxSec wM p₁.left p₂.left (f α) (f₁ (q₁ α)) (f₂ (q₂ α))) → U₁.ExpandsAt e k σ₁ f₁ → U₂.ExpandsAt e k σ₂ f₂ → U.ExpandsAt e k σ f := by
  first | exact @GlobalTheory.ProdUnif.expandsAt_boxProd | exact GlobalTheory.ProdUnif.expandsAt_boxProd | (intros; apply GlobalTheory.ProdUnif.expandsAt_boxProd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationDataIsoOfMumfordBundleIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationDataIsoOfMumfordBundleIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.SameLam

section Comp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ D₃ : DegData R I}
  {A₁ A₂ A₃ : PolAV (Sp (FractionRing R))} {G₁ G₂ G₃ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
  [IsCommMonObj G₂] [GrpObj G₃] [IsCommMonObj G₃] {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}
  {U₃ : UnifPre I D₃ A₃ G₃} {a : G₁ ⟶ G₂} {a' : G₂ ⟶ G₃}

theorem over_comp {b : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {b' : D₂.toPre.P.A ⟶ D₃.toPre.P.A} (h : Over₀ U₁ U₂ a b)
    (h' : Over₀ U₂ U₃ a' b') : Over₀ U₁ U₃ (a ≫ a') (b ≫ b') := fun e => by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, h' e, ← Category.assoc, h e, Category.assoc]

theorem over_id : Over₀ U₁ U₁ (𝟙 _) (𝟙 _) := fun e => by
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

theorem onTorus_comp {h : D₂.toPre.X → D₁.toPre.X} {h' : D₃.toPre.X → D₂.toPre.X} (H : OnTorus U₁ U₂ a h)
    (H' : OnTorus U₂ U₃ a' h') : OnTorus U₁ U₃ (a ≫ a') (h ∘ h') := fun e => by
  obtain ⟨t, ht, et⟩ := H e
  obtain ⟨t', ht', et'⟩ := H' e
  refine ⟨t ≫ t', fun χ => unit_ext fun z _ => ?_, by
    rw [Functor.map_comp, ← Category.assoc, et, Category.assoc, et', Category.assoc]⟩
  have e₁ := congrArg (gm (𝟙 _) z ⊤) (ht (h' χ))
  have e₂ := congrArg (gm (𝟙 _ ≫ t.left) z ⊤) (ht' χ)
  refine Eq.trans ?_ e₁
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) (t ≫ t').left z ⊤ trivial _)).trans
    (Eq.trans ?_ ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) t.left z ⊤ trivial _)).symm)
  refine Eq.trans ?_ e₂
  refine Eq.trans ?_ ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _ ≫ t.left) t'.left z ⊤ trivial _)).symm
  rw [Over.comp_left, Category.assoc]

theorem onTorus_id : OnTorus U₁ U₁ (𝟙 _) id := fun e =>
  ⟨𝟙 _, fun χ => unit_ext fun z _ => ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans
    (gm_pull (𝟙 _) (𝟙 _) z ⊤ trivial _)).trans (by rw [Category.comp_id]; rfl), by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]⟩

end Comp


set_option maxHeartbeats 1000000 in
theorem iso_of_lbIso_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ [Module O D'.toPre.X] (o' : D'.toPre.OAct O) (oA' : A'.OAct O), U'.toUnifPre.OLinear O o' oA' oG → LBIso (abelian₂ G U'.LG.L) (abelian₂ G U.LG.L) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (xe : D'.toPre.X ≃+ D.toPre.X), IsMonHom Φ.hom ∧ Over₀ U'.toUnifPre U.toUnifPre (𝟙 G) Φ.hom ∧ OnTorus U'.toUnifPre U.toUnifPre (𝟙 G) xe.symm ∧ (∀ a, o'.onB.act a ≫ Φ.hom = Φ.hom ≫ o.onB.act a) ∧ (∀ (a : O) x, xe (a • x) = a • xe x) ∧ (∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x)) ∧ ∃ wΛ : (letI := D.toPre.P.isAb.comm; letI := D'.toPre.P.isAb.comm; LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) ((abelian₂ D.toPre.P.A D.toPre.P.L).pull (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) : G2 D'.toPre.P.A ⟶ G2 D.toPre.P.A).left)), wΛ.IsGen ∧ ∀ a b z J J', Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' * val (D.toPre.tau (xe a) (xe b)) (𝟙 _) z J := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG lin D' A' U' _ o' oA' lin' H
  have := hR.2
  have hA := hR.1
  have := U.gen_hom
  have := U'.gen_hom
  obtain ⟨prB, hprB, qpr⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G)
    inferInstance
  obtain ⟨incB, hincB, qinc⟩ := GlobalTheory.Mum.Two.exists_abelian_hom R _ hA D' D A' A G G U'.toUnifPre U.toUnifPre (𝟙 G)
    inferInstance
  obtain ⟨h, th⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G)
    inferInstance
  obtain ⟨k, tk⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D' D A' A G G U'.toUnifPre U.toUnifPre (𝟙 G)
    inferInstance
  have un := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre (𝟙 G)
  have un' := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D' D' A' A' G G U'.toUnifPre U'.toUnifPre (𝟙 G)
  have ipB : incB ≫ prB = 𝟙 _ := un'.1 _ _ (by have := over_comp qinc qpr; rwa [Category.comp_id] at this) over_id
  have piB : prB ≫ incB = 𝟙 _ := un.1 _ _ (by have := over_comp qpr qinc; rwa [Category.comp_id] at this) over_id
  have kh : ∀ χ, k (h χ) = χ := congrFun (un'.2 _ _ (by have := onTorus_comp tk th; rwa [Category.comp_id] at this)
    onTorus_id)
  have hk : ∀ χ, h (k χ) = χ := congrFun (un.2 _ _ (by have := onTorus_comp th tk; rwa [Category.comp_id] at this)
    onTorus_id)
  have hinj : Function.Injective h := Function.LeftInverse.injective kh
  let xe : D'.toPre.X ≃+ D.toPre.X :=
    { toFun := h, invFun := k, left_inv := kh, right_inv := hk, map_add' := h.map_add }

  have ql : ∀ x, Over₀ U.toUnifPre U.toUnifPre (oG.act x) (o.onB.act x) := fun x e => lin.q_lin e x
  have ql' : ∀ x, Over₀ U'.toUnifPre U'.toUnifPre (oG.act x) (o'.onB.act x) := fun x e => lin'.q_lin e x
  have il : ∀ x, OnTorus U.toUnifPre U.toUnifPre (oG.act x) (fun χ => star x • χ) := fun x e => lin.i_lin e x
  have il' : ∀ x, OnTorus U'.toUnifPre U'.toUnifPre (oG.act x) (fun χ => star x • χ) := fun x e => lin'.i_lin e x
  have linB : ∀ a, o'.onB.act a ≫ incB = incB ≫ o.onB.act a := fun a =>
    (GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D' D A' A G G U'.toUnifPre U.toUnifPre (oG.act a)).1 _ _
      (by have := over_comp (ql' a) qinc; rwa [Category.comp_id] at this)
      (by have := over_comp qinc (ql a); rwa [Category.id_comp] at this)
  have linS : ∀ (b : O) χ, star b • h χ = h (star b • χ) := fun b => congrFun
    ((GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (oG.act b)).2 _ _
      (by have := onTorus_comp (il b) th; rwa [Category.comp_id] at this)
      (by have := onTorus_comp th (il' b); rwa [Category.id_comp] at this))
  have linX : ∀ (a : O) x, h (a • x) = a • h x := fun a x => by
    have := linS (star a) x
    rw [star_star] at this
    exact this.symm

  have L : Lin U.toUnifPre U'.toUnifPre (𝟙 G) prB h := ⟨inferInstance, hprB, qpr, th⟩
  have C := GlobalTheory.Mum.Two.coord_of_lin R _ hA D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G) prB h L
  obtain ⟨c, hc, gc⟩ : ∃ c : A.A ⟶ A'.A, IsMonHom c ∧ Gen₀ U.toUnifPre U'.toUnifPre (𝟙 G) c :=
    ⟨U.gen.inv ≫ (Over.pullback (jK R)).map (𝟙 G) ≫ U'.gen.hom, inferInstance, by simp [Gen₀]⟩
  obtain ⟨E, eG, -⟩ := (GlobalTheory.UT.functorial_of_unif R _ hA D A G hG U).1 (𝟙 G) (𝟙 A.A) inferInstance inferInstance
    (by simp)
  have eh : ∀ y, E.h y = y := fun y =>
    congrFun (un.2 _ _ (eG ▸ (lin_of_endU E).1.2.2.2) onTorus_id) y
  have adj : LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E.aG] U.LG.L) := by
    rw [eG]
    simp only [Category.comp_id]
    exact GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_linComb U.LG.isLB _ _)
  have H₂ := GlobalTheory.Mum.Two.lbIso_cubeLB_generic R _ D D' A A' G G U.toUnifPre U'.toUnifPre (𝟙 G) (𝟙 G) E.aG (𝟙 G) c c
    E.aA (𝟙 _) gc gc E.ext (by simp [Gen₀]) (by rw [eG]; simp only [Category.comp_id]; exact H)
  obtain ⟨Ω, _, _, _, K⟩ := GlobalTheory.Mum.Two.exists_key R _ hA D D' A A' G G hG hG U U' (𝟙 G) c prB h hc gc L C hinj
  obtain ⟨φ, hφ, hhφ⟩ := GlobalTheory.Mum.Two.periods_of_key R _ hA D D' A A' G G hG hG U U' (𝟙 G) c prB h hc gc L C E E
    adj H₂ Ω K
  have H' : LBIso (abelian₂ G U'.LG.L) ((abelian₂ G U.LG.L).pull (lift (fst G G ≫ 𝟙 G) (snd G G ≫ 𝟙 G) : G2 G ⟶ G2 G).left) := by
    simp only [Category.comp_id, lift_fst_snd, Over.id_left]
    exact LBIso.chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) H
  have H₃ := GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart R hA D' D A' A G G hG hG U' U (𝟙 G) (𝟙 G) incB incB inferInstance inferInstance hincB hincB
    qinc qinc H'
  have key := GlobalTheory.Mum.Two.Fac.periods_of_factor R D'.toPre D.toPre D.tau_bimult O o 1 1 incB prB h φ hincB hprB
    (by rw [piB, o.onB.map_one]) (fun χ => (C χ).imp fun _ => And.left)
    (by rw [o.onB.map_one, Category.comp_id]; exact H₃) Ω hφ
    (fun y => by rw [hhφ, eh, star_one, one_smul, one_smul, one_smul])
  rw [o.onB.map_one, Category.comp_id] at key
  obtain ⟨cφ, w, hw, ht⟩ := key
  have φh : ∀ x, φ (h x) = x := fun x => hinj ((hhφ (h x)).trans (eh _))
  refine ⟨⟨incB, prB, ipB, piB⟩, xe, hincB, qinc, tk, linB, linX, fun x => ?_, w, hw, fun a b z J J' hJ hJ' => ?_⟩
  · show D'.toPre.c x ≫ incB = D.toPre.c (h x)
    have := cφ (h x)
    rw [φh] at this
    rw [this, Category.assoc, piB, Category.comp_id]
  · have := ht (h a) (h b) z J J' hJ hJ'
    rw [φh, φh, one_smul, one_smul, one_smul] at this
    exact this

end GlobalTheory.Mum.SameLam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationDataIsoOfMumfordBundleIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedDegenerationData_iso_of_mumfordBundle_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ [Module O D'.toPre.X] (o' : D'.toPre.OAct O) (oA' : A'.OAct O), U'.toUnifPre.OLinear O o' oA' oG → LBIso (abelian₂ G U'.LG.L) (abelian₂ G U.LG.L) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (xe : D'.toPre.X ≃+ D.toPre.X), IsMonHom Φ.hom ∧ Over₀ U'.toUnifPre U.toUnifPre (𝟙 G) Φ.hom ∧ OnTorus U'.toUnifPre U.toUnifPre (𝟙 G) xe.symm ∧ (∀ a, o'.onB.act a ≫ Φ.hom = Φ.hom ≫ o.onB.act a) ∧ (∀ (a : O) x, xe (a • x) = a • xe x) ∧ (∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x)) ∧ ∃ wΛ : (letI := D.toPre.P.isAb.comm; letI := D'.toPre.P.isAb.comm; LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) ((abelian₂ D.toPre.P.A D.toPre.P.L).pull (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) : G2 D'.toPre.P.A ⟶ G2 D.toPre.P.A).left)), wΛ.IsGen ∧ ∀ a b z J J', Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' * val (D.toPre.tau (xe a) (xe b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.Mum.SameLam.iso_of_lbIso_lam | exact GlobalTheory.Mum.SameLam.iso_of_lbIso_lam | (intros; apply GlobalTheory.Mum.SameLam.iso_of_lbIso_lam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionProductOverThickeningOfSumData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionProductOverThickeningOfSumData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdTorusExt

section Torus

variable {S : Scheme.{0}} {X X' X'' : Type} [AddCommGroup X] [AddCommGroup X'] [AddCommGroup X'']

theorem torusMap_comp' (a : X →+ X') (b : X'' →+ X) :
    GlobalTheory.SplitTorusPow.torusMap S a ≫ GlobalTheory.SplitTorusPow.torusMap S b = GlobalTheory.SplitTorusPow.torusMap S (a.comp b) := by
  apply (GlobalTheory.splitTorusPointsEquiv S X'' _).injective
  conv_rhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S (a.comp b))]
  conv_lhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S a)]
  rw [Category.assoc, ← Category.assoc (𝟙 _), GlobalTheory.SplitTorusPow.points_comp_torusMap,
    GlobalTheory.SplitTorusPow.points_comp_torusMap, GlobalTheory.SplitTorusPow.points_comp_torusMap]
  rfl

theorem torusMap_id' : GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.id X) = 𝟙 _ := by
  apply (GlobalTheory.splitTorusPointsEquiv S X _).injective
  conv_lhs => rw [← Category.id_comp (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.id X))]
  rw [GlobalTheory.SplitTorusPow.points_comp_torusMap]
  rfl

theorem isIso_lift_torusMap {X₁ X₂ : Type} [AddCommGroup X₁] [AddCommGroup X₂] (E : X ≃+ X₁ × X₂) :
    IsIso (lift (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inl X₁ X₂)))
      (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inr X₁ X₂)))) := by
  haveI := GlobalTheory.SemiProd.torus_prod_iso S X₁ X₂
  have e : lift (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inl X₁ X₂)))
      (GlobalTheory.SplitTorusPow.torusMap S (E.symm.toAddMonoidHom.comp (AddMonoidHom.inr X₁ X₂))) =
      GlobalTheory.SplitTorusPow.torusMap S E.symm.toAddMonoidHom ≫
        lift (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
          (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) := by
    rw [comp_lift, torusMap_comp', torusMap_comp']
  haveI : IsIso (GlobalTheory.SplitTorusPow.torusMap S E.symm.toAddMonoidHom) :=
    ⟨GlobalTheory.SplitTorusPow.torusMap S E.toAddMonoidHom, by
      rw [torusMap_comp', show E.symm.toAddMonoidHom.comp E.toAddMonoidHom = AddMonoidHom.id X from by ext; simp,
        torusMap_id'], by
      rw [torusMap_comp', show E.toAddMonoidHom.comp E.symm.toAddMonoidHom = AddMonoidHom.id (X₁ × X₂) from by
        ext <;> simp, torusMap_id']⟩
  rw [e]
  infer_instance

end Torus

end GlobalTheory.ProdTorusExt

namespace GlobalTheory.ProdTorusExt

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (q : thickObj R I e (G₁ ⊗ G₂) ⟶ thickObj R I e D.P.A) (i : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ thickObj R I e (G₁ ⊗ G₂)), IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsMonHom i ∧ IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) ∧ q ≫ (Over.pullback (thick R I e)).map p₁ = ((Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ g₁.q ∧ q ≫ (Over.pullback (thick R I e)).map p₂ = ((Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ g₂.q ∧ (∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (fst G₁ G₂)) = τ ≫ g₁.i) ∧ (∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (snd G₁ G₂)) = τ ≫ g₂.i) := by
  intro R _ _ I e D D₁ D₂ p₁ p₂ q₁ q₂ G₁ G₂ _ _ _ _ g₁ g₂ hD
  let F := Over.pullback (thick R I e)
  let S₀ := Sp (R ⧸ I ^ (e + 1))
  haveI := hD.hom₁
  haveI := hD.hom₂
  haveI := g₁.q_hom
  haveI := g₂.q_hom
  haveI := g₁.i_hom
  haveI := g₂.i_hom
  let E : D.X ≃+ D₁.X × D₂.X := AddEquiv.ofBijective (q₁.prod q₂) hD.xsum
  let j₁ : D₁.X →+ D.X := E.symm.toAddMonoidHom.comp (AddMonoidHom.inl D₁.X D₂.X)
  let j₂ : D₂.X →+ D.X := E.symm.toAddMonoidHom.comp (AddMonoidHom.inr D₁.X D₂.X)
  let τ₁ := GlobalTheory.SplitTorusPow.torusMap S₀ j₁
  let τ₂ := GlobalTheory.SplitTorusPow.torusMap S₀ j₂
  have hτmon {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (φ : X →+ X') :
      IsMonHom (GlobalTheory.SplitTorusPow.torusMap S₀ φ) := by
    refine ⟨?_, ?_⟩
    · have h : (1 : 𝟙_ (Over S₀) ⟶ splitTorus S₀ X') ≫
          GlobalTheory.SplitTorusPow.torusMap S₀ φ = 1 := by
        apply (GlobalTheory.splitTorusPointsEquiv S₀ X _).injective
        rw [GlobalTheory.SplitTorusPow.points_comp_torusMap, map_one, map_one, MonoidHom.one_comp]
      simpa [Hom.one_def] using h
    · have h {Z : Over S₀} (a b : Z ⟶ splitTorus S₀ X') :
          (a * b) ≫ GlobalTheory.SplitTorusPow.torusMap S₀ φ =
            (a ≫ GlobalTheory.SplitTorusPow.torusMap S₀ φ) *
              (b ≫ GlobalTheory.SplitTorusPow.torusMap S₀ φ) := by
        apply (GlobalTheory.splitTorusPointsEquiv S₀ X Z).injective
        rw [map_mul, GlobalTheory.SplitTorusPow.points_comp_torusMap,
          GlobalTheory.SplitTorusPow.points_comp_torusMap,
          GlobalTheory.SplitTorusPow.points_comp_torusMap, map_mul, MonoidHom.mul_comp]
      simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] using
        h (fst (splitTorus S₀ X') (splitTorus S₀ X')) (snd _ _)
  haveI : IsMonHom τ₁ := hτmon j₁
  haveI : IsMonHom τ₂ := hτmon j₂
  haveI hτ : IsIso (lift τ₁ τ₂) := isIso_lift_torusMap E

  haveI hG : IsIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) :=
    isIso_prodComparison_of_preservesLimit_pair F G₁ G₂
  haveI := hD.lim
  have eB : lift (F.map p₁) (F.map p₂) = F.map (lift p₁ p₂) ≫ Functor.OplaxMonoidal.δ F D₁.P.A D₂.P.A :=
    (Functor.OplaxMonoidal.lift_δ F p₁ p₂).symm
  haveI hB : IsIso (lift (F.map p₁) (F.map p₂)) := by rw [eB]; infer_instance
  haveI : IsMonHom (inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))) :=
    inferInstanceAs (IsMonHom (asIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))).inv)
  haveI : IsMonHom (inv (lift (F.map p₁) (F.map p₂))) :=
    inferInstanceAs (IsMonHom (asIso (lift (F.map p₁) (F.map p₂))).inv)
  let q := lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)) ≫ (g₁.q ⊗ₘ g₂.q) ≫ inv (lift (F.map p₁) (F.map p₂))
  let i := lift τ₁ τ₂ ≫ (g₁.i ⊗ₘ g₂.i) ≫ inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange],
      P g₁.q.left → P g₂.q.left → P q.left := by
    intro P _ _ h₁ h₂
    haveI : IsIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))))
    haveI : IsIso (inv (lift (F.map p₁) (F.map p₂))).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (inv (lift (F.map p₁) (F.map p₂)))))
    rw [Over.comp_left, Over.comp_left]
    exact P.comp_mem _ _ (P.of_isIso _)
      (P.comp_mem _ _ (GlobalTheory.SemiProd.tensorHom_prop _ P _ _ _ _ _ _ h₁ h₂) (P.of_isIso _))
  have hq₁ : q ≫ F.map p₁ = F.map (fst G₁ G₂) ≫ g₁.q := by
    have : inv (lift (F.map p₁) (F.map p₂)) ≫ F.map p₁ = fst _ _ := by
      rw [IsIso.inv_comp_eq, lift_fst]
    rw [Category.assoc, Category.assoc, this, tensorHom_fst, lift_fst_assoc]
  have hq₂ : q ≫ F.map p₂ = F.map (snd G₁ G₂) ≫ g₂.q := by
    have : inv (lift (F.map p₁) (F.map p₂)) ≫ F.map p₂ = snd _ _ := by
      rw [IsIso.inv_comp_eq, lift_snd]
    rw [Category.assoc, Category.assoc, this, tensorHom_snd, lift_snd_assoc]
  have hi₁ : i ≫ F.map (fst G₁ G₂) = τ₁ ≫ g₁.i := by
    have : inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) ≫ F.map (fst G₁ G₂) = fst _ _ := by
      rw [IsIso.inv_comp_eq, lift_fst]
    rw [Category.assoc, Category.assoc, this, tensorHom_fst, lift_fst_assoc]
  have hi₂ : i ≫ F.map (snd G₁ G₂) = τ₂ ≫ g₂.i := by
    have : inv (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂))) ≫ F.map (snd G₁ G₂) = snd _ _ := by
      rw [IsIso.inv_comp_eq, lift_snd]
    rw [Category.assoc, Category.assoc, this, tensorHom_snd, lift_snd_assoc]

  have key := GlobalTheory.SemiProd.kernel_tensor _ _ _ _ _ _ _ g₁.i g₂.i g₁.q g₂.q g₁.isKernel g₂.isKernel
  have hK : IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) := by
    refine IsPullback.of_iso key (asIso (lift τ₁ τ₂)).symm
      (asIso (lift (F.map (fst G₁ G₂)) (F.map (snd G₁ G₂)))).symm (Iso.refl _)
      (asIso (lift (F.map p₁) (F.map p₂))).symm ?_ ?_ ?_ ?_
    · simp only [i, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
    · exact toUnit_unique _ _
    · simp only [q, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
    · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv]
      rw [IsIso.comp_inv_eq, IsMonHom.one_hom]

  have hE₁ : ∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → h = j₁ := by
    intro h h₁ h₂
    funext y
    apply E.injective
    change (q₁.prod q₂) (h y) = E (E.symm (y, 0))
    rw [AddEquiv.apply_symm_apply]
    exact Prod.ext (h₁ y) (h₂ y)
  have hE₂ : ∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → h = j₂ := by
    intro h h₁ h₂
    funext y
    apply E.injective
    change (q₁.prod q₂) (h y) = E (E.symm (0, y))
    rw [AddEquiv.apply_symm_apply]
    exact Prod.ext (h₁ y) (h₂ y)
  refine ⟨q, i, inferInstance, hP @Flat g₁.q_flat g₂.q_flat, hP @Surjective g₁.q_surj g₂.q_surj,
    hP @IsAffineHom g₁.q_affine g₂.q_affine, inferInstance, hK, hq₁, hq₂, fun h h₁ h₂ => ?_, fun h h₁ h₂ => ?_⟩
  · refine ⟨τ₁, ?_, hi₁⟩
    rw [hE₁ h h₁ h₂]
    exact GlobalTheory.MumProd.torusHomOf_torusMap j₁
  · refine ⟨τ₂, ?_, hi₂⟩
    rw [hE₂ h h₁ h₂]
    exact GlobalTheory.MumProd.torusHomOf_torusMap j₂

end GlobalTheory.ProdTorusExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionProductOverThickeningOfSumDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_product_over_thickening_of_sumData : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (q : thickObj R I e (G₁ ⊗ G₂) ⟶ thickObj R I e D.P.A) (i : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ thickObj R I e (G₁ ⊗ G₂)), IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsMonHom i ∧ IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) ∧ q ≫ (Over.pullback (thick R I e)).map p₁ = ((Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ g₁.q ∧ q ≫ (Over.pullback (thick R I e)).map p₂ = ((Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ g₂.q ∧ (∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (fst G₁ G₂)) = τ ≫ g₁.i) ∧ (∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (snd G₁ G₂)) = τ ≫ g₂.i) := by
  first | exact @GlobalTheory.ProdTorusExt.main | exact GlobalTheory.ProdTorusExt.main | (intros; apply GlobalTheory.ProdTorusExt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosureClosedSubscheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableAgainstMixedChernFormIffPullIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableAgainstMixedChernFormIffPullIso
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixIso

theorem map_chartMeas {A B : Type} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] {n : ℕ} (Φ : A ≃ᵐ B)
    (e' : OpenPartialHomeomorph A (ReciprocityTheory.L2DbarEstimates.V n)) (e : OpenPartialHomeomorph B (ReciprocityTheory.L2DbarEstimates.V n))
    (ρ' : A → ℝ≥0∞) (ρ : B → ℝ≥0∞) (ht : e'.target = e.target)
    (hs : ∀ v ∈ e.target, Φ (e'.symm v) = e.symm v) (hρ : ∀ v ∈ e.target, ρ' (e'.symm v) = ρ (e.symm v)) :
    Measure.map Φ (chartMeas e' ρ') = chartMeas e ρ := by
  unfold chartMeas
  have hae : AEMeasurable e'.symm ((volume.restrict e'.target).withDensity (ρ' ∘ e'.symm)) :=
    (e'.continuousOn_symm.aemeasurable e'.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [AEMeasurable.map_map_of_aemeasurable Φ.measurable.aemeasurable hae, ht]
  have h1 : (volume.restrict e.target).withDensity (ρ' ∘ e'.symm) =
      (volume.restrict e.target).withDensity (ρ ∘ e.symm) :=
    withDensity_congr_ae ((ae_restrict_iff' e.open_target.measurableSet).2
      (Eventually.of_forall fun v hv => hρ v hv))
  rw [h1]
  exact Measure.map_congr ((withDensity_absolutelyContinuous _ _).ae_le
    ((ae_restrict_iff' e.open_target.measurableSet).2 (Eventually.of_forall fun v hv => hs v hv)))

theorem le_map_symm_iff {A B : Type} [MeasurableSpace A] [MeasurableSpace B] (Φ : A ≃ᵐ B)
    (μ : Measure A) (ν : Measure B) : μ ≤ Measure.map Φ.symm ν ↔ Measure.map Φ μ ≤ ν := by
  constructor
  · intro h
    simpa only [MeasurableEquiv.map_map_symm] using Measure.map_mono h Φ.measurable
  · intro h
    simpa only [MeasurableEquiv.map_symm_map] using Measure.map_mono h Φ.symm.measurable

end GlobalTheory.MixIso

namespace GlobalTheory.MixIso

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem inv_comp (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) : inv π ≫ q = p := by
  rw [IsIso.inv_comp_eq, hπ]

def ptH (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (σ : k →+* ℂ) : CxPts q σ ≃ₜ CxPts p σ where
  toFun := ptMap π hπ σ
  invFun := ptMap (inv π) (inv_comp π hπ) σ
  left_inv y := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  continuous_toFun := CxPts.continuous_of_comp (f := π) fun _ => rfl
  continuous_invFun := CxPts.continuous_of_comp (f := inv π) fun _ => rfl

variable {σ : k →+* ℂ} {D : ℕ}

def pullChart (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (c : AlgChart p σ D) : AlgChart q σ D where
  e := (ptH π hπ σ).transOpenPartialHomeomorph c.e
  U := π ⁻¹ᵁ c.U
  affine := c.affine.preimage_of_isIso π
  x a := π.app c.U (c.x a)
  etale := GlobalTheory.Mean4O.CoverExc.etale_app π hπ c.etale
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso (π.app c.U)))
  source_subset y hy := (mem_ptsIn_preimage (m := ptMap π hπ σ) (fun _ => rfl)).2 (c.source_subset hy)
  apply_eq y hy a := (c.apply_eq _ hy a).trans (ev_of_comp (m := ptMap π hπ σ) (fun _ => rfl) _ _ _)
  holo W f := by
    refine (c.holo (inv π ⁻¹ᵁ W) ((inv π).app W f)).congr_mono ?_ ?_
    · intro v _
      exact ev_of_comp (m := ptMap (inv π) (inv_comp π hπ) σ) (f := inv π) (fun _ => rfl) W f _
    · intro v hv
      exact ⟨hv.1, (mem_ptsIn_preimage (m := ptMap (inv π) (inv_comp π hπ) σ)
        (f := inv π) (fun _ => rfl)).2 hv.2⟩

theorem pullChart_symm (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (c : AlgChart p σ D) (v : ReciprocityTheory.L2DbarEstimates.V D) :
    (pullChart π hπ c).e.symm v = ptMap (inv π) (inv_comp π hπ) σ (c.e.symm v) := rfl

end GlobalTheory.MixIso

namespace GlobalTheory.MixIso

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem map_chartMeas_dens (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (ε : ℤˣ)
    (c : AlgChart p σ D) (c' : AlgChart q σ D) (ht : c'.e.target = c.e.target)
    (hs : ∀ v, ptMap π hπ σ (c'.e.symm v) = c.e.symm v) :
    Measure.map (ptH π hπ σ).toMeasurableEquiv
      (chartMeas c'.e fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c' y)) =
      chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L c y) := by
  refine map_chartMeas _ _ _ _ _ ht (fun v _ => hs v) fun v hv => ?_
  rw [← hs v, GlobalTheory.MixPull.dens_pull k X Y p q σ D π hπ L c c' (fun w hw => ?_) _ (c'.e.map_target (ht ▸ hv))]
  have hw' : c'.e w ∈ c.e.target := ht ▸ c'.e.map_source hw
  have e : ptMap π hπ σ w = c.e.symm (c'.e w) := by rw [← hs, c'.e.left_inv hw]
  rw [e]
  exact ⟨c.e.map_target hw', (c.e.right_inv hw').symm⟩

theorem map_part (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (ε : ℤˣ) :
    Measure.map (ptH π hπ σ).toMeasurableEquiv (part (fun i => (L i).pull π hπ) ε) = part L ε := by
  unfold part glueMeas
  refine le_antisymm ((le_map_symm_iff _ _ _).1 (iSup_le fun c' => (le_map_symm_iff _ _ _).2 ?_))
    (iSup_le fun c => ?_)
  · rw [map_chartMeas_dens π hπ L ε (pullChart (inv π) (inv_comp π hπ) c') c' rfl fun v =>
      Subtype.ext (by simp [pullChart_symm])]
    exact le_iSup (fun c : AlgChart p σ D => chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) _
  · rw [← map_chartMeas_dens π hπ L ε c (pullChart π hπ c) rfl fun v => (ptH π hπ σ).right_inv _]
    exact Measure.map_mono (le_iSup (fun c' : AlgChart q σ D => chartMeas c'.e fun y =>
      ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c' y)) _) (MeasurableEquiv.measurable _)

theorem intg_int_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (D : ℕ) (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), (Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) = Mix.int L f := by
  intro k _ X Y p q σ _ π _ hπ D L f
  simp only [Intg, Mix.int, ← map_part π hπ L, integrable_map_equiv, integral_map_equiv]
  exact ⟨Iff.rfl, rfl⟩

end GlobalTheory.MixIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableAgainstMixedChernFormIffPullIsoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableAgainstMixedChernForm_iff_pull_iso : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsIso π] (hπ : π ≫ p = q) (D : ℕ) (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), (Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) = Mix.int L f := by
  first | exact @GlobalTheory.MixIso.intg_int_pull | exact GlobalTheory.MixIso.intg_int_pull | (intros; apply GlobalTheory.MixIso.intg_int_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosureClosedSubscheme
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem cycInt_of_closedImmersion : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
    (σ : k →+* ℂ), IsProjOver p → ∀ [IsIntegral Y] (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (D : ℕ)
    (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ),
    (CycIntg L f (π (genericPoint Y)) ↔ Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y))) ∧
      cycInt L f (π (genericPoint Y)) = Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) := by
  intro k _ X Y p q σ hp _ π _ hπ D L f
  generalize hz : π (genericPoint Y) = z
  obtain ⟨_, -, -, hY⟩ := GlobalTheory.ClosFacts.clos_facts X z
  obtain ⟨g, hgπ, -, -, hiso⟩ := hY Y π hz
  have : IsIso g := hiso inferInstance
  subst hgπ
  have hpz : IsProjOver (closι z ≫ p) := ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
  have hq : IsProjOver q := hπ ▸ ProjSpace.isProjOver_comp_of_isClosedImmersion (g ≫ closι z) hp
  have hg : g ≫ (closι z ≫ p) = q := by rw [← Category.assoc]; exact hπ
  obtain ⟨hI, hE⟩ := GlobalTheory.T.integrableAgainstMixedChernForm_iff_pull_iso k (clos z) Y (closι z ≫ p) q σ hpz g hg D (fun i => (L i).pull (closι z) rfl)
    (fun y => f (ptMap (closι z) rfl σ y))
  have hiso' : ∀ i, (((L i).pull (closι z) rfl).pull g hg).Isom ((L i).pull (g ≫ closι z) hπ) := fun i =>
    (GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus k X (clos z) p (closι z ≫ p) σ (closι z) rfl).2.2.2.2.2 Y q g hg hπ (L i)
  have hpart : ∀ ε, part (fun i => ((L i).pull (closι z) rfl).pull g hg) ε = part (fun i => (L i).pull (g ≫ closι z) hπ) ε :=
    GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver k Y q σ hq D _ _ hiso'
  have hfun : (fun y => f (ptMap (closι z) rfl σ (ptMap g hg σ y))) = fun y => f (ptMap (g ≫ closι z) hπ σ y) := by
    funext y; exact congrArg f (PtsOver.map_map _ _ _ _ _ y)
  have hI' : Intg (fun i => ((L i).pull (closι z) rfl).pull g hg) (fun y => f (ptMap (closι z) rfl σ (ptMap g hg σ y))) ↔
      Intg (fun i => (L i).pull (g ≫ closι z) hπ) (fun y => f (ptMap (g ≫ closι z) hπ σ y)) := by
    rw [hfun]; simp only [Intg, hpart]
  have hE' : Mix.int (fun i => ((L i).pull (closι z) rfl).pull g hg) (fun y => f (ptMap (closι z) rfl σ (ptMap g hg σ y))) =
      Mix.int (fun i => (L i).pull (g ≫ closι z) hπ) (fun y => f (ptMap (g ≫ closι z) hπ σ y)) := by
    rw [hfun]; simp only [Mix.int, hpart]
  exact ⟨hI.symm.trans hI', hE.symm.trans hE'⟩

end GlobalTheory.Mix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosureClosedSubschemeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_chern_integral_point_closure_closed_subscheme : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ [IsIntegral Y] (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (D : ℕ) (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), (CycIntg L f (π (genericPoint Y)) ↔ Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y))) ∧ cycInt L f (π (genericPoint Y)) = Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) := by
  first | exact @GlobalTheory.Mix.cycInt_of_closedImmersion | exact GlobalTheory.Mix.cycInt_of_closedImmersion | (intros; apply GlobalTheory.Mix.cycInt_of_closedImmersion <;> assumption)
end
end
