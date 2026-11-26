module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermFrobeniusTorsionSection
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartIdealLocalizationMap

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleGeneratorCorrespondence
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleGeneratorCorrespondence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Nfold

theorem nfold_first_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (n : ℕ), ∃ κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I))), κ.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) ∧ ∀ (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (m : ℕ), ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (pow1 g.B n) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (jptG t x d g.x m (0 : Fin 2)) (jptG t x d g.x m (1 : Fin 2))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x d g.x g.e m ![fun j => psIn d m ![0] (g.B.A.act (n : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (LB.invGen t.PP.L _ _ (genPowG t _ _ (g.e m) n)))) :=
  @PositivityTheory.HtPt.Ca.nfold_law

end GlobalTheory.CompanionTheory.Ar.Nfold
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleGeneratorCorrespondenceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_generator_correspondence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (n : ℕ), ∃ κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I))), κ.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) ∧ ∀ (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (m : ℕ), ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (pow1 g.B n) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (jptG t x d g.x m (0 : Fin 2)) (jptG t x d g.x m (1 : Fin 2))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x d g.x g.e m ![fun j => psIn d m ![0] (g.B.A.act (n : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (LB.invGen t.PP.L _ _ (genPowG t _ _ (g.e m) n)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Nfold.nfold_first_law | exact GlobalTheory.CompanionTheory.Ar.Nfold.nfold_first_law | (intros; apply GlobalTheory.CompanionTheory.Ar.Nfold.nfold_first_law <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusTorsionGeneratorRelation
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusTorsionGeneratorRelation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem exists_gen_pfold : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), y ^ p = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), κ.IsGen → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), τ.IsGen → ∃ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), C.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p := by
  intro E _ _ _ H X0 t k _ x p y hy κ hκ τ hτ
  have hpow : (fst (Tm x p) t.G ≫ y) ^ p = 1 := by
    have e := map_pow (Formalism.L2.Pj.preHom (fst (Tm x p) t.G)) y p
    rw [hy, map_one] at e
    exact e.symm
  have e₁ : ∀ I : ULift.{0} (Finset (Fin 2)), (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left ≫ cφG t ![fst t.G t.G ^ p, snd t.G t.G] I =
      (psum t.G ![1, snd (Tm x p) t.G] I.down).left := by
    intro I
    refine congrArg (fun q => q.left) ((psum_hom (Formalism.L2.Pj.preHom (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G))) _ I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => ?_)))
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      refine (map_pow (Formalism.L2.Pj.preHom _) _ p).trans ?_
      simpa [Formalism.L2.Pj.preHom] using hpow
    · simp [Formalism.L2.Pj.preHom]
  have e₂ : ∀ I : ULift.{0} (Finset (Fin 2)), (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left ≫ cφG t ![fst t.G t.G, snd t.G t.G] I =
      (psum t.G ![fst (Tm x p) t.G ≫ y, snd (Tm x p) t.G] I.down).left := by
    intro I
    refine congrArg (fun q => q.left) ((psum_hom (Formalism.L2.Pj.preHom (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G))) _ I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => ?_)))
    fin_cases i <;> simp [Formalism.L2.Pj.preHom]
  refine Exists.elim (exists_gen t.PP.isLB (φ' := ![pa t.G x y, pb t.G x p]) (ε' := ![(p : ℤ), -(p : ℤ)]) ?_
    (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ κ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left))
      (genPowG t _ _ (LB.pullGen t.PP.L _ _ τ (fst (Tm x p) t.G).left) p))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hκ _))
      (GermD.genPowG_isGen t _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _) p))) ?_
  · intro U _ f
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    have h₁ : ∏ a₁ : ULift.{0} (Finset (Fin 2)), f ((lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left ≫
          cφG t ![fst t.G t.G ^ p, snd t.G t.G] a₁) ^ (-cε 2 a₁) =
        (∏ I : ULift.{0} (Finset (Fin 2)), f (psum t.G ![1, snd (Tm x p) t.G] I.down).left ^
          ((-1 : ℤ) ^ (2 - I.down.card)))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [e₁ I, zpow_neg]
      rfl
    have h₂ : ∏ a₂ : ULift.{0} (Finset (Fin 2)), f ((lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left ≫
          cφG t ![fst t.G t.G, snd t.G t.G] a₂) ^ (- -((p : ℤ) * cε 2 a₂)) =
        (∏ I : ULift.{0} (Finset (Fin 2)), f (psum t.G ![fst (Tm x p) t.G ≫ y, snd (Tm x p) t.G] I.down).left ^
          ((-1 : ℤ) ^ (2 - I.down.card))) ^ (p : ℤ) := by
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [e₂ I, neg_neg, _root_.mul_comm, zpow_mul]
      rfl
    have h₃ : (fst (Tm x p) t.G).left ≫ (1 : Tm x p ⟶ t.G).left = (1 : Tm x p ⊗ t.G ⟶ t.G).left :=
      by
        have e : fst (Tm x p) t.G ≫ (1 : Tm x p ⟶ t.G) = 1 := map_one (Formalism.L2.Pj.preHom (fst (Tm x p) t.G))
        rw [← Over.comp_left, e]
    have h₄ : pa t.G x y = (fst (Tm x p) t.G ≫ y * snd (Tm x p) t.G).left := rfl
    have h₅ : pb t.G x p = (snd (Tm x p) t.G).left := rfl
    rw [h₁, h₂, prod_cube₂, prod_cube₂, Fin.prod_univ_two, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, _root_.one_mul, h₃, h₄, h₅, ← Over.comp_left]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  · rintro C ⟨hC, hv⟩
    refine ⟨C, hC, fun Z' r z J hJ => ?_⟩
    rw [hv Z' r z J hJ, val_mul hJ, val_inv, val_pull hJ, GermD.val_genPowG, val_pull hJ]

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusTorsionGeneratorRelationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_torsion_generator_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), y ^ p = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), κ.IsGen → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), τ.IsGen → ∃ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), C.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_pfold | exact GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_pfold | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_pfold <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermTorsionLiftCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetPointComposition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.JetPts

section
variable {X0 : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X0)

theorem homAt_comp_homAt {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (g : A →ₐ[k] B) (f : B →ₐ[k] C) : homAt x f ≫ homAt x g = homAt x (f.comp g) := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.comp_left, Over.homMk_left, spMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem homAt_id_eq {A : Type} [CommRing A] [Algebra k A] : homAt x (AlgHom.id k A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.homMk_left, spMap]
  exact Spec.map_id _

def trJ (κ : Type) {n M : ℕ} (h : n ≤ M) : Jet k κ M →ₐ[k] Jet k κ n :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

theorem trJ_mk (κ : Type) {n M : ℕ} (h : n ≤ M) (P : MvPolynomial κ k) :
    trJ (k := k) κ h (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ P := rfl

theorem x_eq_of_trunc {Y : Over X0} {κ : Type} (z : ∀ m, overAt x (Jet k κ m) ⟶ Y)
    (hz : ∀ m, homAt x (jetTrunc : Jet k κ (m + 1) →ₐ[k] Jet k κ m) ≫ z (m + 1) = z m) {n M : ℕ} (h : n ≤ M) :
    homAt x (trJ κ h) ≫ z M = z n := by
  induction M, h using Nat.le_induction with
  | base =>
    have e : trJ (k := k) κ (le_refl n) = AlgHom.id k _ := by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      rfl
    rw [e, homAt_id_eq, Category.id_comp]
  | succ M h ih =>
    have e : (trJ (k := k) κ (Nat.le_succ_of_le h)) = (trJ κ h).comp jetTrunc := by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      rfl
    rw [← ih, ← hz M, e, ← homAt_comp_homAt, Category.assoc]

end

section
variable {k : Type} [Field k] {d : ℕ}

theorem liftJet_mk_eq {κ B : Type} [CommRing B] [Algebra k B] {n : ℕ} (f : MvPolynomial κ k →ₐ[k] B)
    (h : Ideal.span (Set.range fun i => f (MvPolynomial.X i)) ^ (n + 1) = ⊥) (P : MvPolynomial κ k) :
    liftJet f h (Ideal.Quotient.mk _ P) = f P := rfl

theorem jetMap_mk_eq {κ κ' : Type} {n : ℕ} (φ : κ → MvPolynomial κ' k) (hφ : ∀ i, φ i ∈ orig k κ') (P : MvPolynomial κ k) :
    (jetMap φ hφ : Jet k κ n →ₐ[k] Jet k κ' n) (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ (MvPolynomial.aeval φ P) := rfl

theorem jq_mk_zero (w : Fin d → k) (p m : ℕ) (j : Fin d) :
    jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 2), j))) =
      algebraMap k _ (w j) * dQ (Jet k (Fin 1 × Fin d) m) p := by
  rw [jq, liftJet_mk_eq]
  simp

theorem jq_mk_one (w : Fin d → k) (p m : ℕ) (j : Fin d) :
    jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X ((1 : Fin 2), j))) =
      inR (k := k) (Jet k (Fin 1 × Fin d) m) p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) := by
  rw [jq, liftJet_mk_eq]
  simp

theorem inL_mk (B : Type) [CommRing B] [Algebra k B] (p : ℕ) :
    inL (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ())) = dQ B p := by
  rw [inL, liftJet_mk_eq]
  simp

theorem ring_zero (w : Fin d → k) (p m : ℕ) :
    (jq w p m).comp (jetCopy d (p + m + 1) (0 : Fin 2)) =
      (inL (k := k) (Jet k (Fin 1 × Fin d) m) p).comp
        ((jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()).comp
          (trJ (Fin 1 × Fin d) (show p ≤ p + m + 1 by omega))) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨a, j⟩
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  have h1 : jetCopy (S := k) d (p + m + 1) (0 : Fin 2) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 2), j)) := by
    rw [jetCopy, jetMap_mk_eq]
    simp
  have h2 : jetSubstP (S := k) p (fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ())
      (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      algebraMap k _ (w j) * Ideal.Quotient.mk _ (MvPolynomial.X ()) := by
    rw [jetSubstP, jetMap_mk_eq]
    simp only [MvPolynomial.aeval_X, map_mul, MvPolynomial.constantCoeff_C, MvPolynomial.constantCoeff_X, mul_zero,
      map_zero, sub_zero]
    rfl
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, trJ_mk, h1, h2, jq_mk_zero, map_mul, AlgHom.commutes, inL_mk]

theorem ring_one (w : Fin d → k) (p m : ℕ) :
    (jq w p m).comp (jetCopy d (p + m + 1) (1 : Fin 2)) =
      (inR (k := k) (Jet k (Fin 1 × Fin d) m) p).comp
        (trJ (Fin 1 × Fin d) (show m ≤ p + m + 1 by omega)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨a, j⟩
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  have h1 : jetCopy (S := k) d (p + m + 1) (1 : Fin 2) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((1 : Fin 2), j)) := by
    rw [jetCopy, jetMap_mk_eq]
    simp
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, trJ_mk, h1, jq_mk_one]

end

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), homAt x (jq w p m) ≫ jptG t x d g.x (p + m + 1) (0 : Fin 2) = homAt x (inL (k := k) (Jet k (Fin 1 × Fin d) m) p) ≫ homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p ∧ homAt x (jq w p m) ≫ jptG t x d g.x (p + m + 1) (1 : Fin 2) = homAt x (inR (k := k) (Jet k (Fin 1 × Fin d) m) p) ≫ g.x m := by
  intro E _ _ _ H _ X0 t k _ p x d g w m
  constructor
  · have hx := x_eq_of_trunc x g.x g.chart.trunc (show p ≤ p + m + 1 by omega)
    show homAt x (jq w p m) ≫ homAt x (jetCopy d (p + m + 1) (0 : Fin 2)) ≫ g.x (p + m + 1) = _
    rw [← hx, ← Category.assoc, homAt_comp_homAt, ring_zero, ← homAt_comp_homAt, ← homAt_comp_homAt]
    simp only [Category.assoc]
  · have hx := x_eq_of_trunc x g.x g.chart.trunc (show m ≤ p + m + 1 by omega)
    show homAt x (jq w p m) ≫ homAt x (jetCopy d (p + m + 1) (1 : Fin 2)) ≫ g.x (p + m + 1) = _
    rw [← hx, ← Category.assoc, homAt_comp_homAt, ring_one, ← homAt_comp_homAt]
    simp only [Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Coc.JetPts
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermTorsionLiftCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc.TestPair

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ) (y : Tm x p ⟶ t.G), y = homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p → rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left = (homAt x (jq w p m)).left ≫ (lift (jptG t x d g.x (p + m + 1) (0 : Fin 2)) (jptG t x d g.x (p + m + 1) (1 : Fin 2))).left := by
  intro E _ _ _ H _ X0 t k _ p _ _ x d g w m y hy
  subst hy
  obtain ⟨h0, h1⟩ := GlobalTheory.CompanionTheory.Ar.Coc.JetPts.main E H X0 t k p x d g w m
  unfold rQ
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, comp_lift, lift_fst_assoc, lift_snd, h0, h1]

end GlobalTheory.CompanionTheory.Ar.Coc.TestPair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermTorsionLiftCompatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_torsion_lift_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ) (y : Tm x p ⟶ t.G), y = homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p → rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left = (homAt x (jq w p m)).left ≫ (lift (jptG t x d g.x (p + m + 1) (0 : Fin 2)) (jptG t x d g.x (p + m + 1) (1 : Fin 2))).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.TestPair.main | exact GlobalTheory.CompanionTheory.Ar.Coc.TestPair.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.TestPair.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetUnitOnChart
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetUnitOnChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

section Ring

variable {k : Type} [Field k] {d : ℕ}

theorem homAt_comp_homAt {X : Scheme.{0}} (x : Sp k ⟶ X) {A B C : Type} [CommRing A] [Algebra k A] [CommRing B]
    [Algebra k B] [CommRing C] [Algebra k C] (f : A →ₐ[k] B) (h : B →ₐ[k] C) :
    homAt x h ≫ homAt x f = homAt x (h.comp f) := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem jetAug_comp_copy (n M : ℕ) (i : Fin n) :
    (jetAug : Jet k (Fin n × Fin d) M →ₐ[k] k).comp (jetCopy d M i) = jetAug := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro q
  have e : jetCopy (S := k) d M i (Ideal.Quotient.mk _ (MvPolynomial.X q)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, q.2)) :=
    congrArg (Ideal.Quotient.mk _) (MvPolynomial.aeval_X _ q)
  have a₁ : (jetAug : Jet k (Fin n × Fin d) M →ₐ[k] k) (Ideal.Quotient.mk _ (MvPolynomial.X (i, q.2))) = 0 :=
    MvPolynomial.aeval_X _ _
  have a₂ : (jetAug : Jet k (Fin 1 × Fin d) M →ₐ[k] k) (Ideal.Quotient.mk _ (MvPolynomial.X q)) = 0 :=
    MvPolynomial.aeval_X _ _
  show (jetAug : Jet k (Fin n × Fin d) M →ₐ[k] k) (jetCopy (S := k) d M i (Ideal.Quotient.mk _ (MvPolynomial.X q))) =
    (jetAug : Jet k (Fin 1 × Fin d) M →ₐ[k] k) (Ideal.Quotient.mk _ (MvPolynomial.X q))
  rw [e, a₁, a₂]

def sub₀ (M : ℕ) : Jet k (Fin 2 × Fin d) M →ₐ[k] Jet k (Fin 1 × Fin d) M :=
  jetSubstP M fun p : Fin 2 × Fin d =>
    (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) p.1 p.2

def trJ (m M : ℕ) (h : m ≤ M) : Jet k (Fin 1 × Fin d) M →ₐ[k] Jet k (Fin 1 × Fin d) m :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

theorem aug_jq (w : Fin d → k) (p m : ℕ) :
    ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) :
        Jet (Jet k (Fin 1 × Fin d) m) Unit p →+* Jet k (Fin 1 × Fin d) m).comp
      ((jq w p m : _ →ₐ[k] _) : Jet k (Fin 2 × Fin d) (p + m + 1) →+* Jet (Jet k (Fin 1 × Fin d) m) Unit p) =
    ((trJ m (p + m + 1) (by omega)).comp (sub₀ (p + m + 1)) :
      Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] Jet k (Fin 1 × Fin d) m).toRingHom := by
  have key : ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m).restrictScalars k).comp
      (jq w p m) = (trJ m (p + m + 1) (by omega)).comp (sub₀ (p + m + 1)) := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    have hq : jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))) =
        if i = 0 then algebraMap k _ (w j) * dQ (Jet k (Fin 1 × Fin d) m) p
        else inR (k := k) (Jet k (Fin 1 × Fin d) m) p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) :=
      MvPolynomial.aeval_X _ _
    have hs : sub₀ (k := k) (d := d) (p + m + 1) (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))) =
        Ideal.Quotient.mk _ ((![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) i j - MvPolynomial.C (MvPolynomial.constantCoeff
            ((![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] :
              Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k) i j))) :=
      congrArg (Ideal.Quotient.mk _) (MvPolynomial.aeval_X _ _)
    have hd : (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m)
        (dQ (Jet k (Fin 1 × Fin d) m) p) = 0 := MvPolynomial.aeval_X _ _
    show (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m)
        (jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X (i, j)))) =
      trJ m (p + m + 1) (by omega) (sub₀ (p + m + 1) (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))))
    rw [hq, hs]
    fin_cases i
    · simp only [Fin.zero_eta, if_true, map_mul, hd, mul_zero]
      simp [trJ]
    · simp [trJ, inR]
  exact congrArg AlgHom.toRingHom key

end Ring

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem comp_psum_one {T T' : Over X0} (U : T' ⟶ T) {n : ℕ} (xs : Fin n → (T ⟶ t.G)) (h : ∀ i, U ≫ xs i = 1)
    (I : Finset (Fin n)) : U ≫ psum t.G xs I = 1 := by
  have e := psum_hom (Formalism.L2.Pj.preHom (G := t.G) U) xs I
  have e' : (fun i => Formalism.L2.Pj.preHom (G := t.G) U (xs i)) = fun _ => (1 : T' ⟶ t.G) := funext h
  rw [e'] at e
  refine e.trans ?_
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => rfl
  | cons a l ih => exact (congrArg ((1 : T' ⟶ t.G) * ·) ih).trans (_root_.one_mul _)

end Pts


set_option maxHeartbeats 1000000 in
theorem frame_test_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ) (j₀ : t.PP.L.ι), ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ e₀ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ, (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) e₀ = 1 ∧ ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)) (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val (g.e (p + m + 1)) (homAt x (jq w p m)).left z J = gm (𝟙 _) z ⊤ (unitΓ e₀) := by
  intro E _ _ _ H _ X0 t k _ p x d g w m j₀ hj₀
  have hpt : ∀ (I : ULift.{0} (Finset (Fin 2))) q, ((homAt x (jq w p m)).left ≫
      cφG t ![jptG t x d g.x (p + m + 1) (0 : Fin 2), jptG t x d g.x (p + m + 1) (1 : Fin 2)] I) q ∈ t.PP.L.U j₀ := by
    intro I q
    have h0 : ∀ i : Fin 2, homAt x (jetAug : Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] k) ≫
        jptG t x d g.x (p + m + 1) i = 1 := by
      intro i
      rw [jptG, ← Category.assoc, homAt_comp_homAt, jetAug_comp_copy]
      exact g.chart.zero _
    have hz := comp_psum_one t (homAt x (jetAug : Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] k))
      ![jptG t x d g.x (p + m + 1) (0 : Fin 2), jptG t x d g.x (p + m + 1) (1 : Fin 2)]
      (by intro i; fin_cases i; exacts [h0 0, h0 1]) I.down
    rw [Scheme.Hom.comp_apply]
    exact jet_left_mem t x j₀ hj₀ _ hz _
  have hred : ∀ (z' : Sp (Jet k (Fin 1 × Fin d) m)) (J' : (Sp (Jet k (Fin 1 × Fin d) m) ⟶ t.G.left) → t.PP.L.ι),
      Good t.PP.L z' J' → val (g.e (p + m + 1))
        (spMap ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) :
          Jet (Jet k (Fin 1 × Fin d) m) Unit p →+* Jet k (Fin 1 × Fin d) m) ≫ (homAt x (jq w p m)).left) z' J' = 1 := by
    intro z' J' hJ'
    have e : spMap ((jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) :
          Jet (Jet k (Fin 1 × Fin d) m) Unit p →+* Jet k (Fin 1 × Fin d) m) ≫ (homAt x (jq w p m)).left =
        spMap ((trJ m (p + m + 1) (by omega) : Jet k (Fin 1 × Fin d) (p + m + 1) →ₐ[k] _) :
          Jet k (Fin 1 × Fin d) (p + m + 1) →+* Jet k (Fin 1 × Fin d) m) ≫ (homAt x (sub₀ (p + m + 1))).left := by
      have := aug_jq w p m
      simp only [homAt, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [this]
      rfl
    rw [e, ← val_pull hJ' (g.e (p + m + 1)) (homAt x (sub₀ (p + m + 1))).left]
    exact (val_corr hJ' (g.axes (p + m + 1)).1 _).trans (val_one _)
  have exists_unitΓ_eq {A : Type} [CommRing A] (u : Γ(Sp A, ⊤)ˣ) : ∃ e : Aˣ, unitΓ e = u := by
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom u, Units.ext ?_⟩
    exact congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id

  have val_eq_unit_of_red : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (B : Type) [CommRing B] (p : ℕ) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (Jet B Unit p) ⟶ Y) (j₀ : L.ι), (∀ κ q, (r ≫ φ κ) q ∈ L.U j₀) → (∀ (z' : Sp B) (J' : (Sp B ⟶ X) → L.ι), Good L z' J' → (∀ κ, J' (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r ≫ φ κ) = j₀) → val t (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r) z' J' = 1) → ∃ e₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) e₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ X) → L.ι), Good L z J → (∀ κ, J (r ≫ φ κ) = j₀) → val t r z J = gm (𝟙 _) z ⊤ (unitΓ e₀) := by
    intro X Y L hL B _ p K _ φ ε t r j₀ h₁ h₂
    have hW : (⊤ : (Sp (Jet B Unit p)).Opens) ≤ r ⁻¹ᵁ LB.wchart L φ (fun _ => j₀) :=
      fun q _ => Set.mem_iInter.2 fun κ => h₁ κ q
    obtain ⟨e₀, he₀⟩ := exists_unitΓ_eq (res hW (pullU r _ (t.s fun _ => j₀)))
    have key : ∀ (Z : Scheme.{0}) (f : Z ⟶ Sp (Jet B Unit p)) (z : Z),
        gm f z ⊤ (unitΓ e₀) = gm (f ≫ r) z (LB.wchart L φ (fun _ => j₀)) (t.s fun _ => j₀) := by
      intro Z f z
      rw [he₀, gm_res f z hW (Set.mem_univ _)]
      exact gm_pull f r z _ (hW (Set.mem_univ _)) _
    refine ⟨e₀, ?_, ?_⟩
    · have hv : pullU (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B)) ⊤ (unitΓ e₀) = 1 := by
        apply unit_ext
        intro z' _
        obtain ⟨J', hJ', e⟩ := exists_good L hL z'
          (fun κ => spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫ r ≫ φ κ) (fun _ => j₀)
          (fun _ _ _ => rfl) (fun κ => h₁ κ _)
        have hv := h₂ z' J' hJ' e
        rw [val_of t _ z' J' (fun _ => j₀) (fun κ => by rw [Category.assoc]; exact e κ), ← key] at hv
        have hp := gm_pull (𝟙 _) (spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B)) z' ⊤ (Set.mem_univ _)
          (unitΓ e₀)
        rw [Category.id_comp] at hp
        rw [map_one]
        exact hp.trans hv
      apply toΓ_inj
      rw [map_one]
      exact (spMap_toΓ _ _).symm.trans (congrArg Units.val hv)
    · intro z J _ hc
      rw [val_of t r z J (fun _ => j₀) hc, key, Category.id_comp]
  obtain ⟨e₀, he, hv⟩ := val_eq_unit_of_red t.G.left (Sp (Jet k (Fin 2 × Fin d) (p + m + 1))) t.PP.L t.PP.isLB
    (Jet k (Fin 1 × Fin d) m) p (ULift (Finset (Fin 2)))
    (cφG t ![jptG t x d g.x (p + m + 1) (0 : Fin 2), jptG t x d g.x (p + m + 1) (1 : Fin 2)]) (cε 2) (g.e (p + m + 1))
    (homAt x (jq w p m)).left j₀ hpt (fun z' J' hJ' _ => hred z' J' hJ')
  exact ⟨e₀, he, fun z J hJ hc => hv z J hJ fun I => hc _ (hpt I z)⟩

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetUnitOnChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_jet_unit_on_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ) (j₀ : t.PP.L.ι), ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ e₀ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ, (jetAug : Jet (Jet k (Fin 1 × Fin d) m) Unit p →ₐ[Jet k (Fin 1 × Fin d) m] Jet k (Fin 1 × Fin d) m) e₀ = 1 ∧ ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)) (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val (g.e (p + m + 1)) (homAt x (jq w p m)).left z J = gm (𝟙 _) z ⊤ (unitΓ e₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.Pf.frame_test_unit | exact GlobalTheory.CompanionTheory.Ar.Coc.Pf.frame_test_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.Pf.frame_test_unit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetSectionGeneratorValue
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetSectionGeneratorValue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem aug_comp_inL (k : Type) [Field k] (B : Type) [CommRing B] [Algebra k B] (p : ℕ) :
    ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B).comp
        ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) =
      (algebraMap k B).comp ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    have h0 : (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.C a) : Jet k Unit p) =
        algebraMap k (Jet k Unit p) a := rfl
    simp only [RingHom.comp_apply, h0, RingHom.coe_coe, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply k B (Jet B Unit p), AlgHom.commutes]
    rfl
  · intro i
    have h1 : (inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p)
        (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.X i)) = dQ B p := by
      change (MvPolynomial.aeval fun _ => dQ B p) (MvPolynomial.X i : MvPolynomial Unit k) = _
      simp
    have h2 : (jetAug : Jet B Unit p →ₐ[B] B) (dQ B p) = 0 := by
      change (MvPolynomial.aeval fun _ => (0 : B)) (MvPolynomial.X () : MvPolynomial Unit B) = _
      simp
    have h3 : (jetAug : Jet k Unit p →ₐ[k] k)
        (Ideal.Quotient.mk (orig k Unit ^ (p + 1)) (MvPolynomial.X i)) = 0 := by
      change (MvPolynomial.aeval fun _ => (0 : k)) (MvPolynomial.X i : MvPolynomial Unit k) = _
      simp
    simp only [RingHom.comp_apply, RingHom.coe_coe, h1, h2, h3, map_zero]

theorem red_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G) (B : Type) [CommRing B] [Algebra k B], homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ j₀ : t.PP.L.ι, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ τ₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) τ₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet B Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val τ (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) z J = gm (𝟙 _) z ⊤ (unitΓ τ₀) := by
  intro E _ _ _ H X0 t k _ x p y B _ _ hy τ hτ j₀ hj₀
  have h1 : ∀ (κ : Fin 2) (q : Sp (Jet B Unit p)),
      (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) ≫
        (![y.left, (1 : Tm x p ⟶ t.G).left] : Fin 2 → _) κ) q ∈ t.PP.L.U j₀ := by
    intro κ q
    rw [Scheme.Hom.comp_apply]
    fin_cases κ
    · exact jet_left_mem t x j₀ hj₀ y hy _
    · exact jet_left_mem t x j₀ hj₀ 1 (by simp [Hom.one_def]) _
  have hc : spMap ((jetAug : Jet B Unit p →ₐ[B] B) : Jet B Unit p →+* B) ≫
        spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) =
      spMap (algebraMap k B) ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [aug_comp_inL]
  obtain ⟨e₀, he, hall⟩ := val_eq_unit_of_red t.G.left (Sp (Jet k Unit p)) t.PP.L t.PP.isLB B p (Fin 2)
    ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1] τ
    (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) j₀ h1
    (fun z' J' hG _ => by rw [hc]; exact hτ _ _ z' J' hG)
  exact ⟨e₀, he, fun z J hG hJ => hall z J hG fun κ => hJ _ (h1 κ z)⟩

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetSectionGeneratorValueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_section_generator_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G) (B : Type) [CommRing B] [Algebra k B], homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ j₀ : t.PP.L.ι, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∃ τ₀ : (Jet B Unit p)ˣ, (jetAug : Jet B Unit p →ₐ[B] B) τ₀ = 1 ∧ ∀ (z : Sp (Jet B Unit p)) (J : (Sp (Jet B Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → (∀ ψ : Sp (Jet B Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) → val τ (spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p)) z J = gm (𝟙 _) z ⊤ (unitΓ τ₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_unit | exact GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_unit <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusGeneratorCorrespondence
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusGeneratorCorrespondence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem secZ_lift {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] {k : Type} [Field k] (x : Sp k ⟶ X0) {m : ℕ}
    (y : Tm x m ⟶ G) (hy : homAt x (jetAug : Jet k Unit m →ₐ[k] k) ≫ y = 1) :
    secZ G x m ≫ (lift (fst (Tm x m) G ≫ y) (snd (Tm x m) G)).left =
      pullback.fst G.hom x ≫ (lift (1 : G ⟶ G) (𝟙 G)).left := by
  have hf : (Over.homMk (pullback.snd G.hom x ≫ spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) (by
      dsimp
      rw [Category.assoc, ← Category.assoc (spMap _), spMap_comp_alg]
      simp [spMap]) : FinalForm G x ⟶ Tm x m) ≫ y = 1 := by
    have e : (Over.homMk (pullback.snd G.hom x ≫ spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) (by
        dsimp
        rw [Category.assoc, ← Category.assoc (spMap _), spMap_comp_alg]
        simp [spMap]) : FinalForm G x ⟶ Tm x m) =
        (Over.homMk (pullback.snd G.hom x) (by simp [spMap]) : FinalForm G x ⟶ overAt x k) ≫ homAt x (jetAug : Jet k Unit m →ₐ[k] k) := by
      ext1
      rfl
    rw [e, Category.assoc, hy]
    simp [Hom.one_def]
  have e₂ : pullback.fst G.hom x ≫ (lift (1 : G ⟶ G) (𝟙 G)).left =
      ((Over.homMk (pullback.fst G.hom x) pullback.condition : FinalForm G x ⟶ G) ≫ lift (1 : G ⟶ G) (𝟙 G)).left := rfl
  rw [e₂, secZ, ← Over.comp_left, comp_lift, comp_lift, lift_fst_assoc, lift_snd, hf]
  simp [Hom.one_def]

theorem red_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p) → ∀ (j : t.PP.L.ι) (h : pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j ≤ secZ t.G x p ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j)), ((secZ t.G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1 := by
  intro E _ _ _ H X0 t k _ x p y hy κ hκ τ hτ C hC j h
  refine fn_ext fun z hz => ?_
  refine (gs_appLE (secZ t.G x p) _ _ h z hz (C.s fun _ => j).val).trans ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good t.PP.L t.PP.isLB z (K := Unit) (fun _ => pullback.fst t.G.hom x) (fun _ => j)
    (fun _ _ _ => rfl) (fun _ => hz)
  have eJ' : J (pullback.fst t.G.hom x) = j := eJ ()
  have hv := val_of C (secZ t.G x p) z J (fun _ => j) (Fin.forall_fin_two.2
    ⟨(congrArg J (secZ_pa t.G x y hy)).trans eJ', (congrArg J (secZ_snd t.G x p)).trans eJ'⟩)
  have h₁ : val κ (secZ t.G x p ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J = 1 := by
    rw [secZ_lift t.G x y hy, ← val_pull hJ, val_corr hJ hκ, val_one]
  have h₂ : val τ (secZ t.G x p ≫ (fst (Tm x p) t.G).left) z J = 1 := by
    rw [secZ_fst, hτ _ _ z J hJ]
  have hm : (secZ t.G x p) z ∈ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j) := h hz
  have hval : val C (secZ t.G x p) z J = 1 := by
    rw [hC _ _ z J hJ, h₁, h₂]
    simp
  refine (gs_unit _ z _ hm (C.s fun _ => j)).trans ((congrArg Units.val (hv.symm.trans hval)).trans ?_)
  rw [gs_eq (𝟙 _) z _ (show (𝟙 (pullback t.G.hom x)) z ∈ pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j from hz), map_one, map_one,
    Units.val_one]

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusGeneratorCorrespondenceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_generator_correspondence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1) → ∀ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), (∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p) → ∀ (j : t.PP.L.ι) (h : pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j ≤ secZ t.G x p ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j)), ((secZ t.G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_one | exact GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.Pf.red_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetAugmentationOnePthPower
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetAugmentationOnePthPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc.QAlg

theorem exists_const_add_dQ_mul (B : Type) [CommRing B] (m : ℕ) (x : Jet B Unit m) :
    ∃ (b : B) (y : Jet B Unit m), x = algebraMap B _ b + dQ B m * y := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig B Unit ^ (m + 1)) x
  have hmem := sub_const_mem_orig P
  have hr : Set.range (MvPolynomial.X : Unit → MvPolynomial Unit B) = {MvPolynomial.X ()} :=
    Set.range_unique
  rw [orig, hr, Ideal.mem_span_singleton'] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  refine ⟨MvPolynomial.constantCoeff P, Ideal.Quotient.mk _ Q, ?_⟩
  have hP : P = MvPolynomial.C (MvPolynomial.constantCoeff P) + Q * MvPolynomial.X () := by
    rw [hQ]; ring
  conv_lhs => rw [hP]
  rw [map_add (f := _), map_mul, mul_comm]
  rfl

theorem jetAug_dQ (B : Type) [CommRing B] (m : ℕ) :
    (jetAug : Jet B Unit m →ₐ[B] B) (dQ B m) = 0 := by
  show (jetAug : Jet B Unit m →ₐ[B] B)
    (Ideal.Quotient.mk (orig B Unit ^ (m + 1)) (MvPolynomial.X ())) = 0
  simp [jetAug, liftJet, Ideal.Quotient.liftₐ_apply]

theorem add_pow_of_natCast_eq_zero {A : Type} [CommRing A] (p : ℕ) (hp : p.Prime)
    (h : (p : A) = 0) (x y : A) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq hp, h]
  simp

theorem pow_eq_one_add (B : Type) [CommRing B] (p : ℕ) [hp : Fact p.Prime] (h0 : (p : B) = 0)
    (e : Jet B Unit p) (he : (jetAug : Jet B Unit p →ₐ[B] B) e = 1) :
    ∃ v : B, e ^ p = 1 + dQ B p ^ p * algebraMap B _ (v ^ p) := by
  have hpJ : ((p : ℕ) : Jet B Unit p) = 0 := by
    rw [← map_natCast (algebraMap B (Jet B Unit p)) p, h0, map_zero]
  obtain ⟨b, y, rfl⟩ := exists_const_add_dQ_mul B p e
  have hb : b = 1 := by
    simpa only [map_add (f := _), map_mul, jetAug_dQ, zero_mul, add_zero, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply] using he
  subst hb
  obtain ⟨c, z, rfl⟩ := exists_const_add_dQ_mul B p y
  refine ⟨c, ?_⟩
  have h2 : dQ B p ^ p * dQ B p ^ p = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (by have := hp.out.one_lt; omega) (dQ_pow B p)
  rw [map_one, add_pow_of_natCast_eq_zero p hp.out hpJ, one_pow, mul_pow,
    add_pow_of_natCast_eq_zero p hp.out hpJ, mul_pow, map_pow]
  linear_combination (z ^ p) * h2

end GlobalTheory.CompanionTheory.Ar.Coc.QAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetAugmentationOnePthPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_augmentation_one_pth_power : ∀ (B : Type) [CommRing B] (p : ℕ) [Fact p.Prime], (p : B) = 0 → ∀ e : Jet B Unit p, (jetAug : Jet B Unit p →ₐ[B] B) e = 1 → ∃ v : B, e ^ p = 1 + dQ B p ^ p * algebraMap B _ (v ^ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.QAlg.pow_eq_one_add | exact GlobalTheory.CompanionTheory.Ar.Coc.QAlg.pow_eq_one_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.QAlg.pow_eq_one_add <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleSectionDifferenceGenerator
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleSectionDifferenceGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

section TauGen

variable {X Y Z : Scheme.{0}} (L : LB X)

def gUnit (h : Y ⟶ X) (a b : L.ι) {V : Y.Opens} (hV : V ≤ h ⁻¹ᵁ (L.U a ⊓ L.U b)) : Γ(Y, V)ˣ :=
  res hV (pullU h _ (L.g a b))

theorem gm_gUnit (h : Y ⟶ X) (a b : L.ι) {V : Y.Opens} (hV : V ≤ h ⁻¹ᵁ (L.U a ⊓ L.U b)) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ V) : gm r z V (gUnit L h a b hV) = gm (r ≫ h) z _ (L.g a b) :=
  (gm_res r z hV hz _).trans (gm_pull r h z _ (hV hz) _)

def chartGen (f f' : Y ⟶ X) (b : L.ι) (hb : ∀ y, f y ∈ L.U b) (hb' : ∀ y, f' y ∈ L.U b) :
    LB.Gen (LB.LinComb L (K := Fin 2) ![f, f'] ![1, -1]) where
  s := fun i =>
    gUnit L f (i 0) b (V := LB.wchart L ![f, f'] i) (fun y hy => ⟨LB.wchart_le L ![f, f'] i 0 hy, hb y⟩) *
    (gUnit L f' (i 1) b (V := LB.wchart L ![f, f'] i) (fun y hy => ⟨LB.wchart_le L ![f, f'] i 1 hy, hb' y⟩))⁻¹

theorem gm_chartGen (f f' : Y ⟶ X) (b : L.ι) (hb : ∀ y, f y ∈ L.U b) (hb' : ∀ y, f' y ∈ L.U b)
    (i : Fin 2 → L.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ LB.wchart L ![f, f'] i) :
    gm r z (LB.wchart L ![f, f'] i) ((chartGen L f f' b hb hb').s i) =
      gm (r ≫ f) z _ (L.g (i 0) b) * (gm (r ≫ f') z _ (L.g (i 1) b))⁻¹ :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_gUnit L f _ _ _ r z hz)
    ((map_inv _ _).trans (congrArg _ (gm_gUnit L f' _ _ _ r z hz))))

theorem chartGen_isGen (hL : L.IsLB) (f f' : Y ⟶ X) (b : L.ι) (hb : ∀ y, f y ∈ L.U b) (hb' : ∀ y, f' y ∈ L.U b) :
    (chartGen L f f' b hb hb').IsGen := by
  intro (i : Fin 2 → L.ι) (j : Fin 2 → L.ι)
  refine unit_ext fun y hy => ?_
  have hi : (𝟙 Y) y ∈ LB.wchart L ![f, f'] i := hy.1
  have hj : (𝟙 Y) y ∈ LB.wchart L ![f, f'] j := hy.2
  have hi0 : (𝟙 Y ≫ f) y ∈ L.U (i 0) := LB.wchart_le L ![f, f'] i 0 hy.1
  have hi1 : (𝟙 Y ≫ f') y ∈ L.U (i 1) := LB.wchart_le L ![f, f'] i 1 hy.1
  have hj0 : (𝟙 Y ≫ f) y ∈ L.U (j 0) := LB.wchart_le L ![f, f'] j 0 hy.2
  have hj1 : (𝟙 Y ≫ f') y ∈ L.U (j 1) := LB.wchart_le L ![f, f'] j 1 hy.2
  have hb0 : (𝟙 Y ≫ f) y ∈ L.U b := hb y
  have hb1 : (𝟙 Y ≫ f') y ∈ L.U b := hb' y
  have A := gm_chartGen L f f' b hb hb' i (𝟙 Y) y hi
  have B := gm_chartGen L f f' b hb hb' j (𝟙 Y) y hj
  have C := gm_linComb L ![f, f'] ![1, -1] (𝟙 Y) y i j hi hj
  refine ((gm_res _ y _ hy _).trans A).trans (Eq.symm ((map_mul _ _ _).trans
    ((congrArg₂ (· * ·) C ((gm_res _ y _ hy _).trans B)).trans ?_)))
  have T : (∏ k, gm (𝟙 Y ≫ (![f, f'] : Fin 2 → (Y ⟶ X)) k) y (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)) ^
      (![1, -1] : Fin 2 → ℤ) k) = gm (𝟙 Y ≫ f) y _ (L.g (i 0) (j 0)) * (gm (𝟙 Y ≫ f') y _ (L.g (i 1) (j 1)))⁻¹ :=
    (Fin.prod_univ_two _).trans (congrArg₂ (· * ·) (zpow_one _) (zpow_neg_one _))
  rw [T, ← gm_cocycle hL (𝟙 Y ≫ f) y hi0 hj0 hb0, ← gm_cocycle hL (𝟙 Y ≫ f') y hi1 hj1 hb1, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

end TauGen

theorem jetPair_gen : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (k : Type) [Field k] (p : ℕ) (f f' : Sp (Jet k Unit p) ⟶ X), spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f = spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f' → ∃ τ : LB.Gen (LB.LinComb L (K := Fin 2) ![f, f'] ![1, -1]), τ.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1 := by
  intro X L hL k _ p f f' e
  obtain ⟨s₀⟩ : Nonempty (Sp k) := inferInstance
  set w₀ : Sp (Jet k Unit p) := (spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) s₀ with hw
  have hq : ∀ q : Sp (Jet k Unit p), q = w₀ := fun q => (jet_pt p q s₀).symm
  have e₀ : f' w₀ = f w₀ := by
    have := congrArg (fun m => m s₀) e
    simpa using this.symm
  obtain ⟨b, hb₀⟩ := exists_chart hL (f w₀)
  have hb : ∀ y, f y ∈ L.U b := fun y => by rw [hq y]; exact hb₀
  have hb' : ∀ y, f' y ∈ L.U b := fun y => by rw [hq y, e₀]; exact hb₀
  refine ⟨chartGen L f f' b hb hb', chartGen_isGen L hL f f' b hb hb', ?_⟩
  intro Z' r z J hJ
  set ρ := r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) with hρ
  have eρ : ρ ≫ f = ρ ≫ f' := by rw [hρ, Category.assoc, Category.assoc, e]
  have hz := hJ.mem ![f, f'] ρ
  rw [val]
  refine (gm_chartGen L f f' b hb hb' _ ρ z hz).trans ?_
  have key : ∀ ψ ψ' : Z' ⟶ X, ψ = ψ' → gm ψ z (L.U (J ψ) ⊓ L.U b) (L.g (J ψ) b) =
      gm ψ' z (L.U (J ψ') ⊓ L.U b) (L.g (J ψ') b) := by
    rintro _ _ rfl
    rfl
  exact mul_inv_eq_one.2 (key _ _ eρ)

end GlobalTheory.CompanionTheory.Ar.Coc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleSectionDifferenceGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_section_difference_generator : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (k : Type) [Field k] (p : ℕ) (f f' : Sp (Jet k Unit p) ⟶ X), spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f = spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ f' → ∃ τ : LB.Gen (LB.LinComb L (K := Fin 2) ![f, f'] ![1, -1]), τ.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Sp k) (z : Z') (J : (Z' ⟶ X) → L.ι), Good L z J → val τ (r ≫ spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k)) z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.jetPair_gen | exact GlobalTheory.CompanionTheory.Ar.Coc.jetPair_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.jetPair_gen <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem units_mul_relation_rearrange_commRing {Q : Type} [CommRing Q] (D F V : Q) (h : D * D = 0) :
    (1 + D * F) * (1 + D * (V - F)) = 1 + D * V := by
  linear_combination (F * (V - F)) * h


set_option maxHeartbeats 4000000 in
theorem pfold : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (gs : Germ.PS k 2 d), AxOne gs → pow1 g.B p = Germ.ev (n := 2) ![ptPow k d p 0, Germ.pt k d 1] gs → ∀ y : Tm x p ⟶ t.G, y = homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p → homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ y = 1 → y ^ p = 1 → ∃ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), C.IsGen ∧ (∀ (j : t.PP.L.ι) (h : pullback.fst t.G.hom x ⁻¹ᵁ t.PP.L.U j ≤ secZ t.G x p ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j)), ((secZ t.G x p).appLE _ _ h).hom (C.s fun _ => j).val = 1) ∧ ∀ j₀ : t.PP.L.ι, ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀ → ∀ m : ℕ, ∃ v : Jet k (Fin 1 × Fin d) m, ∀ h : ⊤ ≤ rQ t.G x p (g.x m) ⁻¹ᵁ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j₀), ((rQ t.G x p (g.x m)).appLE _ ⊤ h).hom (C.s fun _ => j₀).val = toΓ _ (1 + dQ _ p ^ p * algebraMap _ _ (v ^ p - psJet m (dSer gs fun i => w i ^ p))) := by
  intro E _ _ _ H _ hstar X0 t k _ p _ _ x d g w gs hax hpow y hy hy0 hyp
  obtain ⟨κ, hκ, hκ2, hκ3⟩ := GlobalTheory.T.line_bundle_generator_correspondence E H hstar X0 t p
  have hy1 : spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ y.left =
      spMap ((jetAug : Jet k Unit p →ₐ[k] k) : Jet k Unit p →+* k) ≫ (1 : Tm x p ⟶ t.G).left := by
    have e₁ := congrArg (fun q => q.left) hy0
    have e₂ : homAt x (jetAug : Jet k Unit p →ₐ[k] k) ≫ (1 : Tm x p ⟶ t.G) = 1 := by simp [Hom.one_def]
    exact e₁.trans (congrArg (fun q => q.left) e₂).symm
  obtain ⟨τ, hτ, hτ1⟩ := GlobalTheory.T.line_bundle_section_difference_generator t.G.left t.PP.L t.PP.isLB k p y.left (1 : Tm x p ⟶ t.G).left hy1
  obtain ⟨C, hC, hCv⟩ := GlobalTheory.T.frobenius_torsion_generator_relation E H X0 t k x p y hyp κ hκ τ hτ
  refine ⟨C, hC, GlobalTheory.T.frobenius_generator_correspondence E H X0 t k x p y hy0 κ hκ2 τ hτ1 C hCv, fun j₀ hj₀ m => ?_⟩
  obtain ⟨u, hu, hκ3'⟩ := hκ3 k x d g (p + m + 1)
  obtain ⟨e₀, he₀, hve⟩ := GlobalTheory.T.germ_jet_unit_on_chart E H X0 t k p x d g w m j₀ hj₀
  obtain ⟨τ₀, hτ₀, hvτ⟩ := GlobalTheory.T.jet_section_generator_value E H X0 t k x p y (Jet k (Fin 1 × Fin d) m) hy0 τ hτ1 j₀ hj₀
  have hp0 : ((p : ℕ) : Jet k (Fin 1 × Fin d) m) = 0 := by
    have : ((p : ℕ) : k) = 0 := CharP.cast_eq_zero k p
    rw [← map_natCast (algebraMap k (Jet k (Fin 1 × Fin d) m)), this, map_zero]
  obtain ⟨v, hv⟩ := GlobalTheory.T.jet_augmentation_one_pth_power (Jet k (Fin 1 × Fin d) m) p hp0 ((e₀ * τ₀ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ) : Jet (Jet k (Fin 1 × Fin d) m) Unit p) (by
    rw [Units.val_mul, map_mul, he₀, hτ₀, _root_.one_mul])
  refine ⟨v, fun h => ?_⟩
  have hju : jq w p m (u : Jet k (Fin 2 × Fin d) (p + m + 1)) = 1 + dQ _ p ^ p * algebraMap _ _ (psJet m (dSer gs fun i => w i ^ p)) := by
    rw [hu, hpow]
    exact GlobalTheory.T.germ_jet_quotient_formula k p d m w gs hax
  let f : Jet k (Fin 2 × Fin d) (p + m + 1) →+* Jet (Jet k (Fin 1 × Fin d) m) Unit p := (jq w p m : Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] _)
  let ν : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ := Units.map (f : _ →* Jet (Jet k (Fin 1 × Fin d) m) Unit p) u
  let U : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ := ν⁻¹ * (e₀ * τ₀) ^ p
  have hU : (U : Jet (Jet k (Fin 1 × Fin d) m) Unit p) = 1 + dQ _ p ^ p * algebraMap _ _ (v ^ p - psJet m (dSer gs fun i => w i ^ p)) := by
    have h2p : dQ (Jet k (Fin 1 × Fin d) m) p ^ p * dQ (Jet k (Fin 1 × Fin d) m) p ^ p = 0 := by
      rw [← pow_add]
      exact pow_eq_zero_of_le (by have := (Fact.out : p.Prime).one_lt; omega) (dQ_pow _ p)
    have e := units_mul_relation_rearrange_commRing (dQ (Jet k (Fin 1 × Fin d) m) p ^ p) (algebraMap _ _ (psJet m (dSer gs fun i => w i ^ p))) (algebraMap _ _ (v ^ p)) h2p
    rw [← hju, ← hv, ← RingHom.map_sub (algebraMap (Jet k (Fin 1 × Fin d) m) (Jet (Jet k (Fin 1 × Fin d) m) Unit p))] at e
    show ((ν⁻¹ * (e₀ * τ₀) ^ p : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ) : Jet (Jet k (Fin 1 × Fin d) m) Unit p) = _
    rw [Units.val_mul, Units.val_pow_eq_pow_val, ← e]
    exact Units.inv_mul_cancel_left ν _
  have hval : ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p))
      (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      (∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀) →
      val C (rQ t.G x p (g.x m)) z J = gm (𝟙 _) z ⊤ (unitΓ U) := by
    intro z J hJ hJ₀
    have hk : val κ (rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J =
        gm (𝟙 _) z ⊤ (unitΓ ν) * (gm (𝟙 _) z ⊤ (unitΓ e₀) ^ p)⁻¹ := by
      have e₁ : val κ (rQ t.G x p (g.x m) ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J =
          val (LB.pullGen t.PP.L _ _ κ (lift (jptG t x d g.x (p + m + 1) (0 : Fin 2)) (jptG t x d g.x (p + m + 1) (1 : Fin 2))).left) (homAt x (jq w p m)).left z J := by
        rw [GlobalTheory.T.germ_torsion_lift_compat E H X0 t k p x d g w m y hy]
        exact (val_pull hJ _ _ _).symm
      refine e₁.trans ((val_corr hJ hκ3' _).trans ((Pf.val_scale t _ _ _ _ _ z hJ).trans ?_))
      refine (congrArg (gm (spMap f) z ⊤ (unitΓ u) * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (GlobalTheory.T.germ_frobenius_torsion_section E H hstar X0 t k p x d g w m (hy ▸ hyp) z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹)
          ((Pf.val_genPow t _ _ _ p _ z J).trans (congrArg (· ^ p) (hve z J hJ hJ₀)))))))).trans ?_
      rw [_root_.one_mul]
      exact congrArg (· * _) (Pf.gm_spMap f u z)
    have ht : val τ (rQ t.G x p (g.x m) ≫ (fst (Tm x p) t.G).left) z J = gm (𝟙 _) z ⊤ (unitΓ τ₀) := by
      rw [rQ_fst]
      exact hvτ z J hJ hJ₀
    rw [hCv _ _ z J hJ, hk, ht]
    let Φ : (Jet (Jet k (Fin 1 × Fin d) m) Unit p)ˣ →* ((Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)).presheaf.stalk z)ˣ :=
      (gm (𝟙 _) z ⊤).comp (Units.map (toΓ _).toMonoidHom)
    show (Φ ν * (Φ e₀ ^ p)⁻¹)⁻¹ * Φ τ₀ ^ p = Φ (ν⁻¹ * (e₀ * τ₀) ^ p)
    rw [map_mul Φ, map_inv Φ, map_pow Φ, map_mul Φ, mul_pow, mul_inv, inv_inv, _root_.mul_assoc]
  apply fn_ext
  intro z _
  have hz : rQ t.G x p (g.x m) z ∈ LB.wchart t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] (fun _ => j₀) := h trivial
  classical
  choose c hc using fun χ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left => exists_chart t.PP.isLB (χ z)
  let J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι := fun ψ => if ψ z ∈ t.PP.L.U j₀ then j₀ else c ψ
  have hJ₀ : ∀ ψ : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left, ψ z ∈ t.PP.L.U j₀ → J ψ = j₀ := fun ψ e => if_pos e
  have hJ : Good t.PP.L z J := fun ψ => by
    by_cases e : ψ z ∈ t.PP.L.U j₀
    · rw [hJ₀ ψ e]; exact e
    · show ψ z ∈ t.PP.L.U (if ψ z ∈ t.PP.L.U j₀ then j₀ else c ψ)
      rw [if_neg e]; exact hc ψ
  have e := val_of C (rQ t.G x p (g.x m)) z J (fun _ => j₀) (fun i => hJ₀ _ (Set.mem_iInter.1 hz i))
  refine (Pf.gs_appLE _ _ _ h z trivial _).trans ((gs_unit _ z _ hz _).trans ?_)
  refine (congrArg Units.val (e.symm.trans (hval z J hJ hJ₀))).trans ?_
  rw [← hU]
  exact (gs_unit (𝟙 _) z ⊤ trivial (unitΓ U)).symm

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
