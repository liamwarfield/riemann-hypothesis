module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TermExpansionWeightCorrespondenceAtLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationExpansionSumsEqTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationExpansionSumsEqTransport
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR in
set_option maxHeartbeats 1600000 in
theorem expansion_sums_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ (σ : H0 U.LG.L 2) (σ' : H0 U'.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') → (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') → ∀ e : ℕ, ∃ S : Finset D'.toPre.X, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → (∀ α' ∉ S, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J = 0) ∧ (∀ α' ∉ S, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' = 0) ∧ ∑ α' ∈ S, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)).val * ∑ α' ∈ S, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val := by
  intro R _ _ _ _ G _ _ _ D D' A A' U U' Φ w wL _ _ _ hlev xe _ σ σ' f f' hE hE' hσ e
  classical
  obtain ⟨S₁, hS₁⟩ := expandsAt_val U.toUnifPre e 2 σ f (hE e)
  obtain ⟨S₂, hS₂⟩ := expandsAt_val U'.toUnifPre e 2 σ' f' (hE' e)
  refine ⟨S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂, fun Z r z J J' hJ hJ' => ?_⟩
  obtain ⟨A₁, B₁⟩ := hS₁ Z r z J hJ
  obtain ⟨A₂, B₂⟩ := hS₂ Z r z J' hJ'
  have z₁ : ∀ α' ∉ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J = 0 := by
    intro α' hα
    refine A₁ _ fun hc => hα (Finset.mem_union_left _ (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩))
  have z₂ : ∀ α' ∉ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f' α') (r ≫ (U'.gt e).pG.left) z J' = 0 := by
    intro α' hα
    exact A₂ _ fun hc => hα (Finset.mem_union_right _ hc)
  refine ⟨z₁, z₂, ?_⟩

  have E₁ : ∑ α' ∈ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val =
      ∑ α ∈ S₁, sval (f α) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t α) r z J).val := by
    rw [← Finset.sum_subset (Finset.subset_union_left) (fun α' _ hα => by
      rw [A₁ (xe α') fun hc => hα (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩), zero_mul]),
      Finset.sum_map]
    refine Finset.sum_congr rfl fun α _ => ?_
    have h₀ : xe (xe.symm.toEquiv.toEmbedding α) = α := xe.apply_symm_apply α
    rw [h₀]
  have E₂ : ∑ α' ∈ S₁.map xe.symm.toEquiv.toEmbedding ∪ S₂,
      sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val =
      ∑ α' ∈ S₂, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val :=
    (Finset.sum_subset (Finset.subset_union_right) (fun α' _ hα => by rw [A₂ α' hα, zero_mul])).symm
  rw [E₁, E₂]
  obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB ((fstG (maximalIdeal R) e G).left (r z))
  obtain ⟨jL', hL'⟩ := exists_chart U'.LG.isLB ((fstG (maximalIdeal R) e G).left (r z))
  rw [← B₁ jL hL, ← B₂ jL' hL']
  obtain ⟨J₀, hJ₀, k₀⟩ := exists_good U.LG.L U.LG.isLB z (fun _ : PUnit => r ≫ (fstG (maximalIdeal R) e G).left)
    (fun _ => jL) (fun _ _ _ => rfl) (fun _ => hL)
  obtain ⟨J₀', hJ₀', k₀'⟩ := exists_good U'.LG.L U'.LG.isLB z (fun _ : PUnit => r ≫ (fstG (maximalIdeal R) e G).left)
    (fun _ => jL') (fun _ _ _ => rfl) (fun _ => hL')
  have c₀ : J₀ (r ≫ (fstG (maximalIdeal R) e G).left) = jL := k₀ PUnit.unit
  have c₀' : J₀' (r ≫ (fstG (maximalIdeal R) e G).left) = jL' := k₀' PUnit.unit
  have hS : sv U.toUnifPre 2 σ (r ≫ (fstG (maximalIdeal R) e G).left) z jL =
      (gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')).val *
        sv U'.toUnifPre 2 σ' (r ≫ (fstG (maximalIdeal R) e G).left) z jL' := by
    have H := hσ Z (r ≫ (fstG (maximalIdeal R) e G).left) z J₀ J₀' hJ₀ hJ₀'
    rw [sval_of σ _ z J₀ (fun _ => jL) (fun _ => by rw [Category.comp_id]; exact c₀),
      sval_of σ' _ z J₀' (fun _ => jL') (fun _ => by rw [Category.comp_id]; exact c₀'), c₀, c₀'] at H
    exact H
  have W : gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) *
        wv U'.toUnifPre e r z (J' (r ≫ (U'.gt e).pG.left)) jL' ^ 2 =
      wv U.toUnifPre e r z (J (r ≫ (U.gt e).pG.left)) jL ^ 2 *
        gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') :=
    (hlev e).2 Z r z (J (r ≫ (U.gt e).pG.left)) (J' (r ≫ (U'.gt e).pG.left)) jL jL' (hJ _) (hJ' _) hL hL'
  have hO : ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left) =
      gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left)) := by
    show gw w (r ≫ (U'.gt e).pG.left) z (fun _ => J ((r ≫ (U'.gt e).pG.left) ≫ Φ.hom.left))
      (fun _ => J' (r ≫ (U'.gt e).pG.left)) = _
    rw [Category.assoc, (hlev e).1]
  rw [hS, hO, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, W]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationExpansionSumsEqTransportStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationExpansion_sums_eq_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ (σ : H0 U.LG.L 2) (σ' : H0 U'.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') → (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') → ∀ e : ℕ, ∃ S : Finset D'.toPre.X, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → (∀ α' ∉ S, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J = 0) ∧ (∀ α' ∉ S, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' = 0) ∧ ∑ α' ∈ S, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)).val * ∑ α' ∈ S, sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val := by
  first | exact @GlobalTheory.expansion_sums_transport | exact GlobalTheory.expansion_sums_transport | (intros; apply GlobalTheory.expansion_sums_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSecondPresentationWeightEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSecondPresentationWeightEq
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.WtSecond

lemma left_eq {S : Scheme.{0}} {A B C : Over S} {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C} (H : f ≫ g = h) :
    f.left ≫ g.left = h.left :=
  (Over.comp_left _ _ _ f g).symm.trans (congrArg (fun k => k.left) H)

lemma appLE_congr {A B : Scheme.{0}} {f g : A ⟶ B} (h : f = g) {U : B.Opens} {W : A.Opens}
    (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ g ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W e' := by
  subst h; rfl

section Core

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def chg (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    WeightPf.Te D I e ⊗ thickObj R I e G ⟶ WeightPf.Te D' I e ⊗ thickObj R I e G :=
  lift (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ θ.inv) (snd (WeightPf.Te D I e) (thickObj R I e G))

lemma chg_fst (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ fst (WeightPf.Te D' I e) (thickObj R I e G) =
      fst (WeightPf.Te D I e) (thickObj R I e G) ≫ θ.inv :=
  lift_fst _ _

lemma chg_snd (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ snd (WeightPf.Te D' I e) (thickObj R I e G) = snd (WeightPf.Te D I e) (thickObj R I e G) :=
  lift_snd _ _

lemma chg_chg (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ chg (G := G) θ.symm = 𝟙 _ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, chg_fst, ← Category.assoc, chg_fst, Category.assoc, Iso.symm_inv, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · rw [Category.assoc, chg_snd, chg_snd, Category.id_comp]

lemma chg_act (g : GtCoord I D e G) (g' : GtCoord I D' e G) (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e)
    (hi : θ.hom ≫ g.i = g'.i) : chg θ ≫ WeightPf.act g' = WeightPf.act g := by
  have hgi : θ.inv ≫ g'.i = g.i := (Iso.inv_comp_eq θ).2 hi.symm
  have h1 : chg θ ≫ lift (fst (WeightPf.Te D' I e) (thickObj R I e G) ≫ g'.i) (snd _ _) =
      lift (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ g.i) (snd _ _) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, chg_fst, Category.assoc, hgi]
    · rw [Category.assoc, lift_snd, lift_snd, chg_snd]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ μ[thickObj R I e G]) h1)

end Core

section Weight

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma chg_weight (g : GtCoord I D e G) (g' : GtCoord I D' e G) (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e)
    (hi : θ.hom ≫ g.i = g'.i) (x₀ : D'.X → D.X)
    (hx : ∀ x, θ.hom.left.appTop.hom (charUnit (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X (x₀ x)).val =
      (charUnit (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.X x).val)
    (α' : D'.X) (jt : Fin 4 → D'.P.L.ι) (hjt : LB.Coh D'.P.L (D'.Oφ g'.pG α') jt)
    (W' : (WeightPf.Te D I e ⊗ thickObj R I e G).left.Opens) (hs : W' ≤ (snd (WeightPf.Te D I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt)
    (ha : W' ≤ (WeightPf.act g).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt) :
    ((WeightPf.act g).left.appLE _ W' ha).hom ((g'.t α').s jt).val =
      ((WeightPf.Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP D.X (thickObj R I e G) (x₀ α')) *
      ((snd (WeightPf.Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom ((g'.t α').s jt).val := by
  have hΨs : chg (G := G) θ.symm ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)) = (snd (WeightPf.Te D' I e) (thickObj R I e G)) := chg_snd θ.symm
  have hact' : chg (G := G) θ.symm ≫ WeightPf.act g = WeightPf.act g' :=
    chg_act g' g θ.symm (by rw [Iso.symm_hom, ← hi, Iso.inv_hom_id_assoc])
  have hs'' : (chg (G := G) θ.symm).left ⁻¹ᵁ W' ≤ (snd (WeightPf.Te D' I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt := by
    have h1 : (snd (WeightPf.Te D' I e) (thickObj R I e G)).left = (chg (G := G) θ.symm).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left :=
      (left_eq hΨs).symm
    rw [h1, Scheme.Hom.comp_preimage]
    exact fun y hy => hs hy
  have ha'' : (chg (G := G) θ.symm).left ⁻¹ᵁ W' ≤ (WeightPf.act g').left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt := by
    have h1 : (WeightPf.act g').left = (chg (G := G) θ.symm).left ≫ (WeightPf.act g).left :=
      (left_eq hact').symm
    rw [h1, Scheme.Hom.comp_preimage]
    exact fun y hy => ha hy
  have hΦW : W' ≤ (chg (G := G) θ).left ⁻¹ᵁ ((chg (G := G) θ.symm).left ⁻¹ᵁ W') := by
    have h2 : (chg (G := G) θ).left ≫ (chg (G := G) θ.symm).left = 𝟙 _ :=
      (left_eq (chg_chg θ)).trans (Over.id_left _)
    rw [← Scheme.Hom.comp_preimage, h2]
    exact fun y hy => hy
  have key := WeightPf.t_act g' α' jt hjt _ hs'' ha''
  have k2 := congrArg ((chg (G := G) θ).left.appLE _ W' hΦW).hom key
  have e0 : (chg (G := G) θ).left ≫ (WeightPf.act g').left = (WeightPf.act g).left :=
    left_eq (chg_act g g' θ hi)
  have e1 : (chg (G := G) θ).left ≫ (snd (WeightPf.Te D' I e) (thickObj R I e G)).left = (snd (WeightPf.Te D I e) (thickObj R I e G)).left :=
    left_eq (chg_snd θ)
  have L : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((WeightPf.act g').left.appLE _ _ ha'').hom x) =
      ((WeightPf.act g).left.appLE _ W' ha).hom x := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun φ => φ.hom x) (appLE_congr e0 _ ha)
  have S : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((snd (WeightPf.Te D' I e) (thickObj R I e G)).left.appLE _ _ hs'').hom x) =
      ((snd (WeightPf.Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom x := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun φ => φ.hom x) (appLE_congr e1 _ hs)
  have hres : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((WeightPf.Te D' I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom x) =
      ((WeightPf.Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom ((chg (G := G) θ).left.appTop.hom x) := by
    intro x
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    first | erw [Scheme.Hom.appLE_map] | rfl
  have hchi : (chg (G := G) θ).left.appTop.hom (TorusInj.chiP D'.X (thickObj R I e G) α') =
      TorusInj.chiP D.X (thickObj R I e G) (x₀ α') := by
    unfold TorusInj.chiP
    rw [← SplitTorusHom.appTop_comp, chg_fst, SplitTorusHom.appTop_comp, ← hx α',
      ← SplitTorusHom.appTop_comp θ.inv θ.hom, Iso.inv_hom_id, SplitTorusHom.appTop_id]
  rw [map_mul] at k2
  exact (L _).symm.trans (k2.trans (congrArg₂ (· * ·) ((hres _).trans (congrArg _ hchi)) (S _)))

end Weight

theorem wt_second : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (e : ℕ) (xe : D'.toPre.X ≃+ D.toPre.X), GlobalTheory.CharAgree.Match (U.gt e) (U'.gt e) xe → ∀ (α' : D'.toPre.X) (jt : Fin 4 → D'.toPre.P.L.ι), LB.Coh D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt → ∀ (W' : (WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.Opens) (hs : W' ≤ (snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt) (ha : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt), ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom (((U'.gt e).t α').s jt).val = ((WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP D.toPre.X (thickObj R (maximalIdeal R) e G) (xe α')) * ((snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.appLE _ W' hs).hom (((U'.gt e).t α').s jt).val := by
  intro R _ _ _ hCN G _ _ hG D D' A A' U U' e xe hM α' jt hjt W' hs ha
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  obtain ⟨hN, -, -, -⟩ := hR
  have hI : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  obtain ⟨θ, hθ, hi⟩ := CharAgree.exists_torus_iso hI (U.gt e) (U'.gt e)
  have := CharAgree.connected_thick hI e
  obtain ⟨x₀, hx⟩ := exists_addEquiv_of_splitTorus_iso _ D.toPre.X D'.toPre.X θ hθ

  have hM₀ : CharAgree.Match (U.gt e) (U'.gt e) x₀ := by
    intro Z r z J J' hJ hJ' _ h' x
    let FinalForm : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :=
      Over.mk (r ≫ (thickObj R (maximalIdeal R) e G).hom)
    let a : FinalForm ⟶ thickObj R (maximalIdeal R) e G := Over.homMk r rfl
    let τ := (U'.gt e).isKernel.lift a (toUnit _) ((CharAgree.comp_q_eq_one_iff (U'.gt e) a).2 h')
    have hτ : τ ≫ (U'.gt e).i = a := (U'.gt e).isKernel.lift_fst _ _ _
    have hτ' : (τ ≫ θ.hom) ≫ (U.gt e).i = a := by rw [Category.assoc, hi, hτ]
    have k := (TorusCoord.val_torus_point_and_translate R (maximalIdeal R) D.toPre e G (U.gt e) FinalForm
      (τ ≫ θ.hom) 1 z J hJ (x₀ x)).1
    have k' := (TorusCoord.val_torus_point_and_translate R (maximalIdeal R) D'.toPre e G (U'.gt e) FinalForm
      τ 1 z J' hJ' x).1
    rw [hτ'] at k
    rw [hτ] at k'
    refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
    rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
    refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
    exact (SplitTorusHom.appTop_comp τ θ.hom _).trans (congrArg τ.left.appTop.hom (hx x))
  have hxe : (xe : D'.toPre.X → D.toPre.X) = x₀ := CharAgree.match_unique hI _ _ hM hM₀
  rw [congrFun hxe α']
  exact chg_weight (U.gt e) (U'.gt e) θ hi x₀ hx α' jt hjt W' hs ha

end GlobalTheory.WtSecond
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSecondPresentationWeightEqStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCoord_secondPresentation_weight_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (e : ℕ) (xe : D'.toPre.X ≃+ D.toPre.X), GlobalTheory.CharAgree.Match (U.gt e) (U'.gt e) xe → ∀ (α' : D'.toPre.X) (jt : Fin 4 → D'.toPre.P.L.ι), LB.Coh D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt → ∀ (W' : (WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.Opens) (hs : W' ≤ (snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt) (ha : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt), ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom (((U'.gt e).t α').s jt).val = ((WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP D.toPre.X (thickObj R (maximalIdeal R) e G) (xe α')) * ((snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.appLE _ W' hs).hom (((U'.gt e).t α').s jt).val := by
  first | exact @GlobalTheory.WtSecond.wt_second | exact GlobalTheory.WtSecond.wt_second | (intros; apply GlobalTheory.WtSecond.wt_second <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TermExpansionWeightCorrespondenceAtLevel
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TermMatch

theorem gs_sub' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_sum' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (S : Finset κ)
    (a : κ → Γ(X, U)) : gs f y U (∑ i ∈ S, a i) = ∑ i ∈ S, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) : gs f y U 0 = 0 := by
  simp only [gs_eq f y U h, map_zero]

theorem exists_good_ext {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (z : Z) (c : (Z ⟶ X) → L.ι) :
    ∃ J, Good L z J ∧ ∀ ψ, ψ z ∈ L.U (c ψ) → J ψ = c ψ := by
  classical
  choose d hd using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  refine ⟨fun ψ => if ψ z ∈ L.U (c ψ) then c ψ else d ψ, fun ψ => ?_, fun ψ h => if_pos h⟩
  by_cases h : ψ z ∈ L.U (c ψ)
  · simpa only [if_pos h] using h
  · simpa only [if_neg h] using hd ψ

theorem pull_inv {P Y B : Scheme.{0}} {a b : P ⟶ Y} {p : Y ⟶ B} (h : a ≫ p = b ≫ p) {W : B.Opens}
    {V : Y.Opens} (hV : V ≤ p ⁻¹ᵁ W) (ha : b ⁻¹ᵁ V ≤ a ⁻¹ᵁ V) (x : Γ(B, W)) :
    (a.appLE V (b ⁻¹ᵁ V) ha).hom ((Y.presheaf.map (homOfLE hV).op).hom ((p.app W).hom x)) =
      (b.app V).hom ((Y.presheaf.map (homOfLE hV).op).hom ((p.app W).hom x)) := by
  have m : p.app W ≫ Y.presheaf.map (homOfLE hV).op ≫ a.appLE V _ ha =
      p.app W ≫ Y.presheaf.map (homOfLE hV).op ≫ b.app V := by
    rw [Scheme.Hom.app_eq_appLE b, Scheme.Hom.map_appLE, Scheme.Hom.map_appLE,
      Scheme.Hom.app_eq_appLE p, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
      Semi.TorusInj.appLE_of_eq h]
  exact congrArg (fun φ => φ.hom x) m

end GlobalTheory.TermMatch


open GlobalTheory.TermMatch ReciprocityTheory.ChartRestriction.G.Out.WeightPf in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.termMatch_at_level : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ (σ : H0 U.LG.L 2) (σ' : H0 U'.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') → (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → ∀ α' : D'.toPre.X, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)).val * sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val := by
  intro R _ _ _ hCN G _ _ hSA D D' A A' U U' Φ w wL hw hwL hΦ hlev xe hM σ σ' f f' hE hE' hσ e Z r z J J'
    hJ hJ' α'
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.T.uniformisationExpansion_sums_eq_transport R hCN G hSA D D' A A' U U' Φ w wL hw hwL hΦ hlev xe hM σ σ' f f' hE hE' hσ e
  obtain ⟨h0, h0', -⟩ := hS Z r z J J' hJ hJ'
  by_cases hα : α' ∉ S
  · rw [h0 α' hα, h0' α' hα, zero_mul, mul_zero, zero_mul]
  push_neg at hα

  have hq : (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left := (hlev e).1
  let c : ((thickObj R (maximalIdeal R) e G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun ψ => J (r ≫ ψ)
  let c' : ((thickObj R (maximalIdeal R) e G).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι := fun ψ => J' (r ≫ ψ)
  let jf : D'.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β k => c ((U.gt e).pG.left ≫ D.toPre.famφB (xe β) k)
  let jt : D'.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β k => c (D.toPre.Oφ (U.gt e).pG (xe β) k)
  let jf' : D'.toPre.X → Fin 4 → D'.toPre.P.L.ι := fun β k => c' ((U'.gt e).pG.left ≫ D'.toPre.famφB β k)
  let jt' : D'.toPre.X → Fin 4 → D'.toPre.P.L.ι := fun β k => c' (D'.toPre.Oφ (U'.gt e).pG β k)
  let jM : Fin 1 → D.toPre.P.L.ι := fun _ => c ((U'.gt e).pG.left ≫ Φ.hom.left)
  let jM' : Fin 1 → D'.toPre.P.L.ι := fun _ => c' (U'.gt e).pG.left
  let Wo : D'.toPre.P.A.left.Opens :=
    ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left).U
      (fun _ => jM) ⊓ (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)).U jM'
  let Vst : (thickObj R (maximalIdeal R) e G).left.Opens :=
    ((U'.gt e).pG.left ⁻¹ᵁ Wo ⊓ (((U'.gt e).pG.left ≫ Φ.hom.left) ⁻¹ᵁ D.toPre.P.L.U (jM 0) ⊓
      (U'.gt e).pG.left ⁻¹ᵁ D'.toPre.P.L.U (jM' 0))) ⊓
    S.inf (fun β => ((U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB (xe β)) (jf β) ⊓
      LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (xe β)) (jt β)) ⊓
      ((U'.gt e).pG.left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.famφB β) (jf' β) ⊓
      LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG β) (jt' β)))
  have hVo : Vst ≤ (U'.gt e).pG.left ⁻¹ᵁ Wo := inf_le_left.trans inf_le_left
  have hVm : Vst ≤ ((U'.gt e).pG.left ≫ Φ.hom.left) ⁻¹ᵁ D.toPre.P.L.U (jM 0) :=
    inf_le_left.trans (inf_le_right.trans inf_le_left)
  have hVm' : Vst ≤ (U'.gt e).pG.left ⁻¹ᵁ D'.toPre.P.L.U (jM' 0) :=
    inf_le_left.trans (inf_le_right.trans inf_le_right)
  have hVf : ∀ β ∈ S, Vst ≤ (U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB (xe β)) (jf β) :=
    fun β hβ => inf_le_right.trans ((Finset.inf_le hβ).trans (inf_le_left.trans inf_le_left))
  have hVt : ∀ β ∈ S, Vst ≤ LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (xe β)) (jt β) :=
    fun β hβ => inf_le_right.trans ((Finset.inf_le hβ).trans (inf_le_left.trans inf_le_right))
  have hVf' : ∀ β ∈ S, Vst ≤ (U'.gt e).pG.left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.famφB β) (jf' β) :=
    fun β hβ => inf_le_right.trans ((Finset.inf_le hβ).trans (inf_le_right.trans inf_le_left))
  have hVt' : ∀ β ∈ S, Vst ≤ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG β) (jt' β) :=
    fun β hβ => inf_le_right.trans ((Finset.inf_le hβ).trans (inf_le_right.trans inf_le_right))
  have hx0 : r z ∈ Vst := by
    have hc : ∀ ψ, ψ (r z) ∈ D.toPre.P.L.U (c ψ) := fun ψ => by
      have := hJ (r ≫ ψ); rwa [Scheme.Hom.comp_apply] at this
    have hc' : ∀ ψ, ψ (r z) ∈ D'.toPre.P.L.U (c' ψ) := fun ψ => by
      have := hJ' (r ≫ ψ); rwa [Scheme.Hom.comp_apply] at this
    refine ⟨⟨⟨mem_pull.2 (Set.mem_iInter.2 fun _ => ?_), Set.mem_iInter.2 fun _ => ?_⟩, ?_, ?_⟩,
      mem_finset_inf _ _ _ fun β _ => ⟨⟨Set.mem_iInter.2 fun k => ?_, Set.mem_iInter.2 fun k => ?_⟩,
        ⟨Set.mem_iInter.2 fun k => ?_, Set.mem_iInter.2 fun k => ?_⟩⟩⟩
    · have := hc ((U'.gt e).pG.left ≫ Φ.hom.left); rwa [Scheme.Hom.comp_apply] at this
    · exact hc' (U'.gt e).pG.left
    · exact hc _
    · exact hc' _
    · have := hc ((U.gt e).pG.left ≫ D.toPre.famφB (xe β) k); rwa [Scheme.Hom.comp_apply] at this
    · exact hc _
    · have := hc' ((U'.gt e).pG.left ≫ D'.toPre.famφB β k); rwa [Scheme.Hom.comp_apply] at this
    · exact hc' _

  let Fv : ∀ β ∈ S, Γ((thickObj R (maximalIdeal R) e G).left, Vst) := fun β hβ =>
    ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVf β hβ)).op).hom (((U.gt e).pG.left.app _).hom ((f (xe β)).f (jf β)))
  let Tv : ∀ β ∈ S, Γ((thickObj R (maximalIdeal R) e G).left, Vst) := fun β hβ =>
    ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVt β hβ)).op).hom (((U.gt e).t (xe β)).s (jt β)).val
  let Fv' : ∀ β ∈ S, Γ((thickObj R (maximalIdeal R) e G).left, Vst) := fun β hβ =>
    ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVf' β hβ)).op).hom (((U'.gt e).pG.left.app _).hom ((f' β).f (jf' β)))
  let Tv' : ∀ β ∈ S, Γ((thickObj R (maximalIdeal R) e G).left, Vst) := fun β hβ =>
    ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVt' β hβ)).op).hom (((U'.gt e).t β).s (jt' β)).val
  let Ωv : Γ((thickObj R (maximalIdeal R) e G).left, Vst) :=
    ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE hVo).op).hom (((U'.gt e).pG.left.app Wo).hom (w.s (fun _ => jM, jM')).val)
  let Hv : ∀ β ∈ S, Γ((thickObj R (maximalIdeal R) e G).left, Vst) := fun β hβ => Fv β hβ * Tv β hβ - Ωv * Fv' β hβ * Tv' β hβ
  have hterm : ∀ (Z0 : Scheme.{0}) (r0 : Z0 ⟶ (thickObj R (maximalIdeal R) e G).left) (z0 : Z0) (J0 : (Z0 ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
      (J0' : (Z0 ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), r0 z0 ∈ Vst →
      (∀ ψ, ψ (r0 z0) ∈ D.toPre.P.L.U (c ψ) → J0 (r0 ≫ ψ) = c ψ) →
      (∀ ψ, ψ (r0 z0) ∈ D'.toPre.P.L.U (c' ψ) → J0' (r0 ≫ ψ) = c' ψ) → ∀ β (hβ : β ∈ S),
      gs r0 z0 Vst (Hv β hβ) = sval (f (xe β)) (r0 ≫ (U.gt e).pG.left) z0 J0 * (val ((U.gt e).t (xe β)) r0 z0 J0).val -
        (ExpTrans.om w z0 (fun q _ => J0 q) (fun q _ => J0' q) (r0 ≫ (U'.gt e).pG.left)).val *
          sval (f' β) (r0 ≫ (U'.gt e).pG.left) z0 J0' * (val ((U'.gt e).t β) r0 z0 J0').val := by
    intro Z0 r0 z0 J0 J0' hz0 hc0 hc0' β hβ
    have hjf : ∀ k, J0 ((r0 ≫ (U.gt e).pG.left) ≫ D.toPre.famφB (xe β) k) = jf β k := fun k => by
      rw [Category.assoc]
      refine hc0 _ ?_
      have := Set.mem_iInter.1 (hVf β hβ hz0) k
      rwa [← Scheme.Hom.comp_apply] at this
    have hjf' : ∀ k, J0' ((r0 ≫ (U'.gt e).pG.left) ≫ D'.toPre.famφB β k) = jf' β k := fun k => by
      rw [Category.assoc]
      refine hc0' _ ?_
      have := Set.mem_iInter.1 (hVf' β hβ hz0) k
      rwa [← Scheme.Hom.comp_apply] at this
    have eF : gs r0 z0 Vst (Fv β hβ) = sval (f (xe β)) (r0 ≫ (U.gt e).pG.left) z0 J0 :=
      (gs_res r0 z0 (hVf β hβ) hz0 _).trans ((gs_pull r0 (U.gt e).pG.left z0 _ (hVf β hβ hz0) _).trans
        (sval_of _ _ _ _ (jf β) hjf).symm)
    have eT : gs r0 z0 Vst (Tv β hβ) = (val ((U.gt e).t (xe β)) r0 z0 J0).val :=
      (gs_res r0 z0 (hVt β hβ) hz0 _).trans ((gs_unit r0 z0 _ (hVt β hβ hz0) _).trans
        (congrArg Units.val (val_of _ r0 z0 J0 (jt β) (fun k => hc0 _ (Set.mem_iInter.1 (hVt β hβ hz0) k))).symm))
    have eF' : gs r0 z0 Vst (Fv' β hβ) = sval (f' β) (r0 ≫ (U'.gt e).pG.left) z0 J0' :=
      (gs_res r0 z0 (hVf' β hβ) hz0 _).trans ((gs_pull r0 (U'.gt e).pG.left z0 _ (hVf' β hβ hz0) _).trans
        (sval_of _ _ _ _ (jf' β) hjf').symm)
    have eT' : gs r0 z0 Vst (Tv' β hβ) = (val ((U'.gt e).t β) r0 z0 J0').val :=
      (gs_res r0 z0 (hVt' β hβ) hz0 _).trans ((gs_unit r0 z0 _ (hVt' β hβ hz0) _).trans
        (congrArg Units.val (val_of _ r0 z0 J0' (jt' β) (fun k => hc0' _ (Set.mem_iInter.1 (hVt' β hβ hz0) k))).symm))
    have ej : (fun (_ : Fin 1) => J0 ((r0 ≫ (U'.gt e).pG.left) ≫ Φ.hom.left)) = jM := funext fun _ => by
      rw [Category.assoc]
      exact hc0 _ (hVm hz0)
    have ek : (fun (_ : Fin 1) => J0' (r0 ≫ (U'.gt e).pG.left)) = jM' := funext fun _ => hc0' _ (hVm' hz0)
    have eO : (ExpTrans.om w z0 (fun q _ => J0 q) (fun q _ => J0' q) (r0 ≫ (U'.gt e).pG.left)) =
        gm (r0 ≫ (U'.gt e).pG.left) z0 Wo (w.s (fun _ => jM, jM')) := by
      have key : ∀ (j1 : Fin 1 → D.toPre.P.L.ι) (k1 : Fin 1 → D'.toPre.P.L.ι), j1 = jM → k1 = jM' →
          gw w (r0 ≫ (U'.gt e).pG.left) z0 j1 k1 = gm (r0 ≫ (U'.gt e).pG.left) z0 Wo (w.s (fun _ => jM, jM')) := by
        rintro _ _ rfl rfl; rfl
      exact key _ _ ej ek
    have eΩ : gs r0 z0 Vst Ωv = (ExpTrans.om w z0 (fun q _ => J0 q) (fun q _ => J0' q) (r0 ≫ (U'.gt e).pG.left)).val :=
      (gs_res r0 z0 hVo hz0 _).trans ((gs_pull r0 (U'.gt e).pG.left z0 Wo (hVo hz0) _).trans
        ((gs_unit (r0 ≫ (U'.gt e).pG.left) z0 Wo (hVo hz0) _).trans (congrArg Units.val eO.symm)))
    have e1 : gs r0 z0 Vst (Hv β hβ) = gs r0 z0 Vst (Fv β hβ) * gs r0 z0 Vst (Tv β hβ) -
        gs r0 z0 Vst Ωv * gs r0 z0 Vst (Fv' β hβ) * gs r0 z0 Vst (Tv' β hβ) := by
      simp only [Hv, gs_sub' r0 z0 Vst hz0, gs_mul r0 z0 Vst hz0]
    rw [e1, eF, eT, eF', eT', eΩ]

  have hsum0 : ∑ β ∈ S.attach, Hv β.1 β.2 = 0 := by
    refine fn_ext fun y hy => ?_
    obtain ⟨Jy, hJy, eJy⟩ := exists_good_ext D.toPre.P.L D.toPre.P.isLB y c
    obtain ⟨J'y, hJ'y, eJ'y⟩ := exists_good_ext D'.toPre.P.L D'.toPre.P.isLB y c'
    obtain ⟨-, -, E⟩ := hS _ (𝟙 _) y Jy J'y hJy hJ'y
    have ht := hterm _ (𝟙 _) y Jy J'y hy (fun ψ h => by rw [Category.id_comp]; exact eJy ψ h)
      (fun ψ h => by rw [Category.id_comp]; exact eJ'y ψ h)
    rw [gs_sum' _ y _ hy, gs_zero' _ y _ hy, Finset.sum_congr rfl (fun β _ => ht β.1 β.2),
      Finset.sum_attach S (fun β => sval (f (xe β)) (𝟙 (thickObj R (maximalIdeal R) e G).left ≫ (U.gt e).pG.left) y Jy * (val ((U.gt e).t (xe β)) (𝟙 (thickObj R (maximalIdeal R) e G).left) y Jy).val -
        (ExpTrans.om w y (fun q _ => Jy q) (fun q _ => J'y q) (𝟙 (thickObj R (maximalIdeal R) e G).left ≫ (U'.gt e).pG.left)).val *
          sval (f' β) (𝟙 (thickObj R (maximalIdeal R) e G).left ≫ (U'.gt e).pG.left) y J'y * (val ((U'.gt e).t β) (𝟙 (thickObj R (maximalIdeal R) e G).left) y J'y).val),
      Finset.sum_sub_distrib]
    rw [Finset.mul_sum] at E
    rw [E, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun β _ => by rw [_root_.mul_assoc, sub_self]
  have hpG : (act (U.gt e)).left ≫ (U.gt e).pG.left =
      (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ (U.gt e).pG.left :=
    act_left_pG (U.gt e)
  have hinv : Φ.hom.left ≫ Φ.inv.left = 𝟙 _ := by rw [← Over.comp_left, Φ.hom_inv_id, Over.id_left]
  have hq' : (U'.gt e).pG.left = (U.gt e).pG.left ≫ Φ.inv.left := by
    rw [← hq, Category.assoc, hinv, Category.comp_id]
  have hpG' : (act (U.gt e)).left ≫ (U'.gt e).pG.left =
      (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ (U'.gt e).pG.left := by
    rw [hq', ← Category.assoc, hpG, Category.assoc]
  have hpGΦ : (act (U.gt e)).left ≫ (U'.gt e).pG.left ≫ Φ.hom.left =
      (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ (U'.gt e).pG.left ≫ Φ.hom.left := by
    rw [← Category.assoc, hpG', Category.assoc]
  have hOφ' : ∀ β k, (act (U.gt e)).left ≫ D'.toPre.Oφ (U'.gt e).pG β k =
      (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ D'.toPre.Oφ (U'.gt e).pG β k := by
    intro β k
    have hm : (Over.map (thick R (maximalIdeal R) e)).map (act (U.gt e)) ≫ (U'.gt e).pG =
        (Over.map (thick R (maximalIdeal R) e)).map (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)) ≫
          (U'.gt e).pG :=
      Over.OverMorphism.ext (by simpa only [Over.comp_left, Over.map_map_left] using hpG')
    have h1 := Oφ_comp ((Over.map (thick R (maximalIdeal R) e)).map (act (U.gt e))) (U'.gt e).pG β k
    have h2 := Oφ_comp ((Over.map (thick R (maximalIdeal R) e)).map
      (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G))) (U'.gt e).pG β k
    simp only [Over.map_map_left] at h1 h2
    rw [h1, h2, hm]
  let W' : (Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.Opens :=
    (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ Vst
  have mv : ∀ {B : Scheme.{0}} (ψ : (thickObj R (maximalIdeal R) e G).left ⟶ B) (O : B.Opens),
      (act (U.gt e)).left ≫ ψ = (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ ψ →
      ∀ y, (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left y ∈ ψ ⁻¹ᵁ O →
        (act (U.gt e)).left y ∈ ψ ⁻¹ᵁ O :=
    fun ψ O h y hy => (congrArg (· ∈ O) (comp_base_eq h y)).mpr hy
  have mw : ∀ {L : LB D'.toPre.P.A.left} {φ : Fin 4 → ((thickObj R (maximalIdeal R) e G).left ⟶ D'.toPre.P.A.left)}
      (j : Fin 4 → L.ι), (∀ k, (act (U.gt e)).left ≫ φ k =
        (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ φ k) →
      ∀ y, (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left y ∈ LB.wchart L φ j →
        (act (U.gt e)).left y ∈ LB.wchart L φ j :=
    fun {L φ} j h y hy => Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy k
      simp only [Set.mem_preimage] at this ⊢
      rw [comp_base_eq (h k) y]; exact this
  have mw0 : ∀ {L : LB D.toPre.P.A.left} {φ : Fin 4 → ((thickObj R (maximalIdeal R) e G).left ⟶ D.toPre.P.A.left)}
      (j : Fin 4 → L.ι), (∀ k, (act (U.gt e)).left ≫ φ k =
        (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ≫ φ k) →
      ∀ y, (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left y ∈ LB.wchart L φ j →
        (act (U.gt e)).left y ∈ LB.wchart L φ j :=
    fun {L φ} j h y hy => Set.mem_iInter.2 fun k => by
      have := Set.mem_iInter.1 hy k
      simp only [Set.mem_preimage] at this ⊢
      rw [comp_base_eq (h k) y]; exact this
  have ha : W' ≤ (act (U.gt e)).left ⁻¹ᵁ Vst := by
    intro y hy
    refine ⟨⟨mv _ _ hpG' y hy.1.1, mv _ _ hpGΦ y hy.1.2.1, mv _ _ hpG' y hy.1.2.2⟩,
      mem_finset_inf _ _ _ fun β hβ => ⟨⟨mv _ _ hpG y (mem_of_finset_inf hy.2 hβ).1.1,
        mw0 _ (fun k => act_Oφ (U.gt e) (xe β) k) y (mem_of_finset_inf hy.2 hβ).1.2⟩,
        ⟨mv _ _ hpG' y (mem_of_finset_inf hy.2 hβ).2.1, mw _ (hOφ' β) y (mem_of_finset_inf hy.2 hβ).2.2⟩⟩⟩

  have keyF : ∀ β (hβ : β ∈ S), ((act (U.gt e)).left.appLE Vst W' ha).hom (Fv β hβ) =
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (Fv β hβ) :=
    fun β hβ => pull_inv hpG (hVf β hβ) ha _
  have keyF' : ∀ β (hβ : β ∈ S), ((act (U.gt e)).left.appLE Vst W' ha).hom (Fv' β hβ) =
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (Fv' β hβ) :=
    fun β hβ => pull_inv hpG' (hVf' β hβ) ha _
  have keyΩ : ((act (U.gt e)).left.appLE Vst W' ha).hom Ωv =
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom Ωv :=
    pull_inv hpG' hVo ha _
  let chi : D.toPre.X → Γ((Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left, W') := fun χ =>
    ((Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE le_top).op).hom
      (TorusInj.chiP D.toPre.X (thickObj R (maximalIdeal R) e G) χ)
  have keyT : ∀ β (hβ : β ∈ S), ((act (U.gt e)).left.appLE Vst W' ha).hom (Tv β hβ) =
      chi (xe β) * ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (Tv β hβ) := by
    intro β hβ
    have hs : W' ≤ (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (xe β)) (jt β) := fun z hz => hVt β hβ hz
    have ha' : W' ≤ (act (U.gt e)).left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG (xe β)) (jt β) :=
      fun z hz => hVt β hβ (ha hz)
    have T := t_act (U.gt e) (xe β) (jt β) (fun k1 k2 h => congrArg c h) W' hs ha'
    have m1 : (thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVt β hβ)).op ≫
        (act (U.gt e)).left.appLE Vst W' ha = (act (U.gt e)).left.appLE _ W' ha' := Scheme.Hom.map_appLE _ _ _
    have m2 : (thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVt β hβ)).op ≫
        (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst =
        (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.appLE _ W' hs := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
    exact (congrArg (fun φ => φ.hom (((U.gt e).t (xe β)).s (jt β)).val) m1).trans
      (T.trans (congrArg (_ * ·) (congrArg (fun φ => φ.hom (((U.gt e).t (xe β)).s (jt β)).val) m2).symm))
  have keyT' : ∀ β (hβ : β ∈ S), ((act (U.gt e)).left.appLE Vst W' ha).hom (Tv' β hβ) =
      chi (xe β) * ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (Tv' β hβ) := by
    intro β hβ
    have hs : W' ≤ (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ
        LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG β) (jt' β) := fun z hz => hVt' β hβ hz
    have ha' : W' ≤ (act (U.gt e)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG β) (jt' β) :=
      fun z hz => hVt' β hβ (ha hz)
    have T := GlobalTheory.T.torusCoord_secondPresentation_weight_eq R hCN G hSA D D' A A' U U' e xe (hM e) β (jt' β) (fun k1 k2 h => congrArg c' h) W' hs ha'
    have m1 : (thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVt' β hβ)).op ≫
        (act (U.gt e)).left.appLE Vst W' ha = (act (U.gt e)).left.appLE _ W' ha' := Scheme.Hom.map_appLE _ _ _
    have m2 : (thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (hVt' β hβ)).op ≫
        (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst =
        (snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.appLE _ W' hs := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
    exact (congrArg (fun φ => φ.hom (((U'.gt e).t β).s (jt' β)).val) m1).trans
      (T.trans (congrArg (_ * ·) (congrArg (fun φ => φ.hom (((U'.gt e).t β).s (jt' β)).val) m2).symm))
  have hact : ∀ β (hβ : β ∈ S), ((act (U.gt e)).left.appLE Vst W' ha).hom (Hv β hβ) =
      chi (xe β) * ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (Hv β hβ) := by
    intro β hβ
    have e1 : Hv β hβ = Fv β hβ * Tv β hβ - Ωv * Fv' β hβ * Tv' β hβ := rfl
    rw [e1, map_sub, map_mul, map_mul, map_mul, keyF β hβ, keyT β hβ, keyF' β hβ, keyT' β hβ, keyΩ, map_sub,
      map_mul, map_mul, map_mul]
    ring
  have hZ : ∑ β ∈ S.attach, chi (xe β.1) *
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (Hv β.1 β.2) = 0 :=
    (Finset.sum_congr rfl fun β _ => (hact β.1 β.2).symm).trans
      ((map_sum _ _ _).symm.trans ((congrArg _ hsum0).trans (map_zero _)))
  let hfun : D'.toPre.X → Γ((thickObj R (maximalIdeal R) e G).left, Vst) := fun β =>
    if hβ : β ∈ S then Hv β hβ else 0
  have hd : ∀ β (hβ : β ∈ S), hfun β = Hv β hβ := fun β hβ => dif_pos hβ
  have hsum : ∑ β ∈ S, chi (xe β) *
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (hfun β) = 0 :=
    (Finset.sum_attach S (fun β => chi (xe β) *
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (hfun β))).symm.trans
      ((Finset.sum_congr rfl fun β _ => congrArg (fun z => chi (xe β.1) *
        ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom z) (hd β.1 β.2)).trans hZ)
  have hs' : ∑ χ ∈ S.map xe.toEquiv.toEmbedding, chi χ *
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (hfun (xe.symm χ)) = 0 := by
    rw [Finset.sum_map]
    refine (Finset.sum_congr rfl fun β _ => ?_).trans hsum
    exact congrArg (fun t => chi (xe β) *
      ((snd (Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.app Vst).hom (hfun t))
      (xe.symm_apply_apply β)
  have h0 := TorusInj.eq_zero_of_sum D.toPre.X (thickObj R (maximalIdeal R) e G) (S.map xe.toEquiv.toEmbedding)
    (fun χ => hfun (xe.symm χ)) hs' (xe α') (Finset.mem_map_of_mem _ hα)
  have h1 : hfun α' = 0 := by simpa only [AddEquiv.symm_apply_apply] using h0
  have hH : Hv α' hα = 0 := (hd α' hα).symm.trans h1
  have fin := hterm Z r z J J' hx0 (fun ψ _ => rfl) (fun ψ _ => rfl) α' hα
  rw [hH, gs_zero' r z Vst hx0] at fin
  exact sub_eq_zero.1 fin.symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TermExpansionWeightCorrespondenceAtLevelStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termExpansion_weight_correspondence_at_level : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ (σ : H0 U.LG.L 2) (σ' : H0 U'.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') → (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → ∀ α' : D'.toPre.X, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)).val * sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val := by
  first | exact @GlobalTheory.termMatch_at_level | exact GlobalTheory.termMatch_at_level | (intros; apply GlobalTheory.termMatch_at_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbelianPartSectionSqEqOfThickeningPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbelianPartSectionSqEqOfThickeningPoints
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqDescend

variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem wchart_sq_le (φ : K → (Y ⟶ X)) (p : K → Fin 1 → L.ι) :
    LB.wchart (SqLB.sq L) φ p ≤ LB.wchart L φ (fun k => p k 0) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0

theorem gm_sq_g' (f : Y ⟶ X) (y : Y) (j j' : Fin 1 → L.ι) (hj : f y ∈ (SqLB.sq L).U j)
    (hj' : f y ∈ (SqLB.sq L).U j') :
    gm f y ((SqLB.sq L).U j ⊓ (SqLB.sq L).U j') ((SqLB.sq L).g j j') =
      gm f y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ (2 : ℤ) := by
  obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨b, rfl⟩ : ∃ b, j' = fun _ => b := ⟨j' 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  exact SqLB.gm_sq_g f y (Set.mem_iInter.1 hj 0) (Set.mem_iInter.1 hj' 0)

theorem gs_sub (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_zero (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem trF_sq (φ : K → (Y ⟶ X)) (ε : K → ℤ) (y : Y) (p p' : K → Fin 1 → L.ι)
    (hy : y ∈ LB.wchart (SqLB.sq L) φ p ⊓ LB.wchart (SqLB.sq L) φ p') :
    (∏ k, gm (𝟙 Y ≫ φ k) y ((SqLB.sq L).U (p k) ⊓ (SqLB.sq L).U (p' k)) ((SqLB.sq L).g (p k) (p' k)) ^ ε k) =
      trF φ ε (𝟙 Y) y (fun k => p k 0) (fun k => p' k 0) ^ 2 := by
  simp only [trF]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gm_sq_g' (𝟙 Y ≫ φ k) y (p k) (p' k) (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k), ← zpow_mul, ← zpow_natCast,
    ← zpow_mul]
  congr 1
  push_cast
  ring

def sqSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb (SqLB.sq L) φ ε) where
  f := fun p => (Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0)) *
    (Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0))
  compat := fun p p' => fn_ext fun y hy => by
    have h₁ := wchart_sq_le φ p hy.1
    have h₂ := wchart_sq_le φ p' hy.2
    have eA : gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0))) =
        gs (𝟙 Y) y (LB.wchart L φ (fun k => p k 0)) (s.f (fun k => p k 0)) := gs_res (𝟙 Y) y _ hy.1 _
    have eB : gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (wchart_sq_le φ p')).op).hom (s.f (fun k => p' k 0))) =
        gs (𝟙 Y) y (LB.wchart L φ (fun k => p' k 0)) (s.f (fun k => p' k 0)) := gs_res (𝟙 Y) y _ hy.2 _
    have eL := (gs_res (𝟙 Y) y inf_le_left hy _).trans ((gs_mul (𝟙 Y) y _ hy.1 _ _).trans (congrArg₂ (· * ·) eA eA))
    have eR := (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val ((gm_linComb (SqLB.sq L) φ ε (𝟙 Y) y p p' hy.1 hy.2).trans (trF_sq φ ε y p p' hy))))
      ((gs_res (𝟙 Y) y inf_le_right hy _).trans ((gs_mul (𝟙 Y) y _ hy.2 _ _).trans (congrArg₂ (· * ·) eB eB))))
    refine eL.trans (Eq.trans ?_ eR.symm)
    rw [sec_trans s (𝟙 Y) y h₁ h₂, Units.val_pow_eq_pow_val]
    ring

theorem good_sq {J : (Z ⟶ X) → L.ι} {z : Z} (hJ : Good L z J) : Good (SqLB.sq L) z (fun q _ => J q) :=
  fun ψ => Set.mem_iInter.2 fun _ => hJ ψ

theorem sval_sqSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (sqSec s) r z (fun q _ => J q) = sval s r z J ^ 2 := by
  have h0 := hJ.mem φ r
  have hm : r z ∈ LB.wchart (SqLB.sq L) φ (fun k _ => J (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h0 k
  exact (gs_mul r z _ hm _ _).trans ((congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _)).trans
    (pow_two _).symm)

def secSub {M : LB Y} (a b : LB.Sec M) : LB.Sec M where
  f := fun i => a.f i - b.f i
  compat := fun i j => by rw [map_sub, map_sub, a.compat, b.compat, mul_sub]

theorem sval_secSub {M : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb M φ ε)) (r : Z ⟶ Y)
    (z : Z) {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) :
    sval (secSub a b) r z J = sval a r z J - sval b r z J :=
  gs_sub r z _ (hJ.mem φ r) _ _

end GlobalTheory.SqDescend


open GlobalTheory.SqDescend in
theorem GlobalTheory.sq_corr_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ (α : D.toPre.X) (α' : D'.toPre.X), (∀ κ, D'.toPre.famφB α' κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB α κ) → ∀ (s : D.toPre.SecB 2 α) (s' : D'.toPre.SecB 2 α'), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (r ≫ (U.gt e).pG.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' (r ≫ (U'.gt e).pG.left) z J' ^ 2) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' ρ z J' ^ 2 := by
  intro R _ _ _ hCN G _ _ hSA D D' A A' U U' Φ w hw hpG α α' hφ s s' hE Z ρ z J J' hJ hJ'
  classical
  have hL := D.toPre.P.isLB
  have hL' := D'.toPre.P.isLB
  have hM : (SqLB.sq D.toPre.P.L).IsLB := DVR.linComb_isLB _ hL _ _
  have hM' : (SqLB.sq D'.toPre.P.L).IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ _ _ Φ.hom.left hM hM' w hw (Fin 4)
    (D'.toPre.famφB α') (D.toPre.famφB α) (DegPre.famε 2) Φ.hom.left hφ (sqSec s)
  have hT : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
      (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' →
      sval s (r ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
        (r ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval a r z (fun q _ => J' q) := by
    intro Z r z J J' hJ hJ'
    rw [← sval_sqSec s _ z hJ]
    exact ExpTrans.sec_val w _ _ _ Φ.hom.left hφ (sqSec s) a r z (ha Z r z) (good_sq hJ) (good_sq hJ')
  have hvan : ∀ (e : ℕ) (q : Fin 4 → Fin 1 → D'.toPre.P.L.ι),
      ((U'.gt e).pG.left.app _).hom ((secSub a (sqSec s')).f q) = 0 := by
    intro e q
    refine fn_ext fun y hy => ?_
    choose J₁ hJ₁ using fun ψ : (thickObj R (maximalIdeal R) e G).left ⟶ D.toPre.P.A.left =>
      exists_chart hL (ψ y)
    choose J₂ hJ₂ using fun ψ : (thickObj R (maximalIdeal R) e G).left ⟶ D'.toPre.P.A.left =>
      exists_chart hL' (ψ y)
    have g₁ : Good D.toPre.P.L y J₁ := hJ₁
    have g₂ : Good D'.toPre.P.L y J₂ := hJ₂
    have e1 := hE e _ (𝟙 _) y J₁ J₂ g₁ g₂
    have e2 := hT _ (U'.gt e).pG.left y J₁ J₂ g₁ g₂
    simp only [Category.id_comp] at e1
    rw [hpG e, e1, ← sval_sqSec s' _ y g₂] at e2
    have e3 := (Units.mul_right_inj _).1 e2
    have hΔ : sval (secSub a (sqSec s')) (U'.gt e).pG.left y (fun q _ => J₂ q) = 0 := by
      rw [sval_secSub a (sqSec s') _ y (good_sq g₂), e3, sub_self]
    refine (gs_pull (𝟙 _) (U'.gt e).pG.left y _ hy _).trans ?_
    rw [Category.id_comp, gs_zero]
    refine (sec_trans (secSub a (sqSec s')) (U'.gt e).pG.left y (j := q) hy ((good_sq g₂).mem _ _)).trans ?_
    change _ * sval (secSub a (sqSec s')) (U'.gt e).pG.left y (fun q _ => J₂ q) = 0
    rw [hΔ, mul_zero]
  obtain ⟨hN, -, -, -⟩ := TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have := D'.toPre.P.isAb.smooth
  have := D'.toPre.P.isAb.geomConnected
  have h0 := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) hI D'.toPre.P.A).1 _
    (DVR.linComb_isLB _ hM' _ _) (secSub a (sqSec s'))
    fun e q => (ExtDiv.pG_app_eq_zero_iff (U'.gt e) _ _).1 (hvan e q)
  have key : sval a ρ z (fun q _ => J' q) = sval (sqSec s') ρ z (fun q _ => J' q) := by
    have h1 : sval (secSub a (sqSec s')) ρ z (fun q _ => J' q) = 0 := by
      show gs _ _ _ _ = 0
      exact (congrArg (gs ρ z _) (h0 _)).trans (gs_zero _ _ _)
    have h2 := sval_secSub a (sqSec s') ρ z (good_sq hJ')
    rw [h1] at h2
    exact sub_eq_zero.1 h2.symm
  rw [hT Z ρ z J J' hJ hJ', key, sval_sqSec s' ρ z hJ']
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbelianPartSectionSqEqOfThickeningPointsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_section_sq_eq_of_thickening_points : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ (α : D.toPre.X) (α' : D'.toPre.X), (∀ κ, D'.toPre.famφB α' κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB α κ) → ∀ (s : D.toPre.SecB 2 α) (s' : D'.toPre.SecB 2 α'), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (r ≫ (U.gt e).pG.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' (r ≫ (U'.gt e).pG.left) z J' ^ 2) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' ρ z J' ^ 2 := by
  first | exact @GlobalTheory.sq_corr_of_thickenings | exact GlobalTheory.sq_corr_of_thickenings | (intros; apply GlobalTheory.sq_corr_of_thickenings <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBundleSquareSectionTransportExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBundleSquareSectionTransportExpansion
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqTransport


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem exists_transport_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen → ∀ (σ : H0 U.LG.L 2), ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') := by
  intro R _ _ _ hCN G _ _ _ D D' A A' U U' wL hwL σ
  have hR := TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  haveI : IsNoetherianRing R := hR.1
  have hL := linComb_isLB U.LG.L U.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  have hL' := linComb_isLB U'.LG.L U'.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  let σ' : H0 U'.LG.L 2 := secOfIso σ hwL hL' hL
  obtain ⟨s, hs⟩ := exists_sec U'.LG.isLB (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R))
    (ε' := fun _ => ((2 : ℕ) : ℤ)) (fun _ _ h => by simp only [Category.comp_id])
    (H1.SectionArithmetic.pullSec σ' (pullback.fst G.hom (jK R)))
  obtain ⟨E, hsE, -⟩ := (U'.expand 2 (by norm_num)).1 s
  obtain ⟨f', hf', -⟩ := IntegralExpansionLocal.main R (maximalIdeal R) le_rfl D' A' G U'.toUnifPre 2 σ' s
    (SectionScalarValuation.secScal_of_sval U'.LG.isLB fun y J hJ =>
      ((hs _ _ y J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm) E hsE
  refine ⟨σ', f', hf', fun Z r z J J' hJ hJ' => ?_⟩
  have hm : r z ∈ (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)).U (fun _ => J' r) ⊓
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)).U (fun _ => J r) :=
    ⟨Set.mem_iInter.2 fun _ => hJ' r, Set.mem_iInter.2 fun _ => hJ r⟩
  have e := gs_secOfIso_eq wL σ hwL hL' hL (fun _ => J' r) (fun _ => J r) r z hm
  rw [sval_of σ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id]),
    sval_of σ' r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
  show _ = (gm r z _ (wL.s ((fun _ => J r), (fun _ => J' r)))).val * _
  have e' : gs r z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J' r) (σ'.f fun _ => J' r) =
      ((gm r z _ (wL.s ((fun _ => J r), (fun _ => J' r))))⁻¹).val *
        gs r z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J r) (σ.f fun _ => J r) := e
  rw [e', ← _root_.mul_assoc, ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, _root_.one_mul]

end GlobalTheory.SqTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBundleSquareSectionTransportExpansionStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundleSquare_section_transport_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen → ∀ (σ : H0 U.LG.L 2), ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') := by
  first | exact @GlobalTheory.SqTransport.exists_transport_expansion | exact GlobalTheory.SqTransport.exists_transport_expansion | (intros; apply GlobalTheory.SqTransport.exists_transport_expansion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiSquareEvenTermsCorrespondTransport
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqCorr

theorem psi_sq_terms_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)))  → ∀ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ ∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2 := by
  intro R _ _ _ hR G _ _ hsa D D' A A' U U' Φ w wL hw hwL hΦ hlev xe ht hc σ f hE
  obtain ⟨σ', f', hE', hrel⟩ := GlobalTheory.T.exists_bundleSquare_section_transport_expansion R hR G hsa D D' A A' U U' wL hwL σ
  refine ⟨σ', f', hE', fun β Z ρ z J J' hJ hJ' => ?_⟩
  have hφ : ∀ κ, D'.toPre.famφB (2 • β) κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB (xe (2 • β)) κ :=
    PsiCompare.famφB_comp Φ.hom (hc β)
  refine GlobalTheory.T.abelianPart_section_sq_eq_of_thickening_points R hR G hsa D D' A A' U U' Φ w hw (fun e => (hlev e).1) _ _ hφ (f _) (f' _)
    (fun e Z r z J J' hJ hJ' => ?_) Z ρ z J J' hJ hJ'
  have hB := GlobalTheory.T.termExpansion_weight_correspondence_at_level R hR G hsa D D' A A' U U' Φ w wL hw hwL hΦ hlev xe ht σ σ' f f' hE hE' hrel e Z r z J J' hJ hJ' (2 • β)
  have hC := GlobalTheory.T.torus_coord_squares_correspond' R hR G hsa D D' A A' U U' Φ w hw hΦ (fun e => (hlev e).1) xe ht β (hc β) e Z r z J J' hJ hJ'
  have hP := ExpTrans.prod_fam U'.toUnifPre e 2 (fun ψ => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ ψ)) (2 • β)

  set a := sval (f (xe (2 • β))) (r ≫ (U.gt e).pG.left) z J
  set b := sval (f' (2 • β)) (r ≫ (U'.gt e).pG.left) z J'
  set T := val ((U.gt e).t (xe (2 • β))) r z J
  set T' := val ((U'.gt e).t (2 • β)) r z J'
  set O := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)
  set P := ∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ
  set F := ∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ
  have hP' : F * P = O ^ 2 := hP
  have key : a ^ 2 * (P * T' ^ 2).val = F.val * b ^ 2 * (P * T' ^ 2).val := by
    calc a ^ 2 * (P * T' ^ 2).val = a ^ 2 * (T ^ 2).val := by rw [hC]
      _ = (a * T.val) ^ 2 := by simp only [Units.val_pow_eq_pow_val]; ring
      _ = (O.val * b * T'.val) ^ 2 := by rw [hB]
      _ = (O ^ 2).val * b ^ 2 * (T' ^ 2).val := by simp only [Units.val_pow_eq_pow_val]; ring
      _ = (F * P).val * b ^ 2 * (T' ^ 2).val := by rw [hP']
      _ = F.val * b ^ 2 * (P * T' ^ 2).val := by simp only [Units.val_mul, Units.val_pow_eq_pow_val]; ring
  exact (Units.mul_left_inj (P * T' ^ 2)).1 key

end GlobalTheory.SqCorr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiSquareEvenTermsCorrespondTransportStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_square_even_terms_correspond_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)))  → ∀ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ ∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2 := by
  first | exact @GlobalTheory.SqCorr.psi_sq_terms_correspond | exact GlobalTheory.SqCorr.psi_sq_terms_correspond | (intros; apply GlobalTheory.SqCorr.psi_sq_terms_correspond <;> assumption)
end
