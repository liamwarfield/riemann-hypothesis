module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateFaceOfOneCocycleEqZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionLoweringDerivationFormula

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionLinearInFunctional
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionLinearInFunctional
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem con_add_form {R : Type} [CommRing R] {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] (M : Type) [AddCommGroup M] [Module R M] (Ξ Ξ' : (∀ i, V i) →ₗ[R] R)
    (u : ∀ i, V i ⊗[R] M) : con V M (Ξ + Ξ') u = con V M Ξ u + con V M Ξ' u := by
  refine GlobalTheory.CompanionTheory.HopfC.pure_induction V M
    (P := fun u => GlobalTheory.CompanionTheory.HopfC.con V M (Ξ + Ξ') u = GlobalTheory.CompanionTheory.HopfC.con V M Ξ u + GlobalTheory.CompanionTheory.HopfC.con V M Ξ' u)
    ?_ ?_ ?_ u
  · simp only [map_zero, add_zero]
  · intro f m
    simp only [GlobalTheory.CompanionTheory.HopfC.con_pure, LinearMap.add_apply, add_smul]
  · intro u v hu hv
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]
    abel

theorem con_smul_form {R : Type} [CommRing R] {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] (M : Type) [AddCommGroup M] [Module R M] (r : R) (Ξ : (∀ i, V i) →ₗ[R] R)
    (u : ∀ i, V i ⊗[R] M) : con V M (r • Ξ) u = r • con V M Ξ u := by
  refine GlobalTheory.CompanionTheory.HopfC.pure_induction V M
    (P := fun u => GlobalTheory.CompanionTheory.HopfC.con V M (r • Ξ) u = r • GlobalTheory.CompanionTheory.HopfC.con V M Ξ u)
    ?_ ?_ ?_ u
  · simp only [map_zero, smul_zero]
  · intro f m
    simp only [GlobalTheory.CompanionTheory.HopfC.con_pure, LinearMap.smul_apply, smul_eq_mul, mul_smul]
  · intro u v hu hv
    rw [map_add (f := _), map_add (f := _), hu, hv, smul_add]

theorem Con_linear_form {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ Ξ' : Cn F p →ₗ[R] R) (r : R) (B : Bi F p q) :
    Con F (Ξ + Ξ') q B = Con F Ξ q B + Con F Ξ' q B ∧ Con F (r • Ξ) q B = r • Con F Ξ q B := by
  have key : ∀ (Θ : MainStatements.Hodge.Cn F p →ₗ[R] R) (b : Fin (q + 1) ⥤ C),
      GlobalTheory.CompanionTheory.HopfC.Con F Θ q B b =
        GlobalTheory.CompanionTheory.HopfC.con (fun a : Fin (p + 1) ⥤ C => (F.obj (a.obj (Fin.last p)) : Type))
          (F.obj (b.obj (Fin.last q)) : Type) Θ (fun a => B a b) := fun _ _ => rfl
  refine ⟨funext fun b => ?_, funext fun b => ?_⟩
  · rw [key, GlobalTheory.CompanionTheory.HopfC.con_add_form]
    rfl
  · rw [key, GlobalTheory.CompanionTheory.HopfC.con_smul_form]
    rfl

end GlobalTheory.CompanionTheory.HopfC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionLinearInFunctionalStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_linear_in_functional : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q : ℕ} [Finite (Fin (p + 1) ⥤ C)] (Ξ Ξ' : Cn F p →ₗ[R] R) (r : R) (B : Bi F p q), Con F (Ξ + Ξ') q B = Con F Ξ q B + Con F Ξ' q B ∧ Con F (r • Ξ) q B = r • Con F Ξ q B := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.Con_linear_form | exact GlobalTheory.CompanionTheory.HopfC.Con_linear_form | (intros; apply GlobalTheory.CompanionTheory.HopfC.Con_linear_form <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCoboundaryDegreeZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCoboundaryDegreeZero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem Sh_dn_zero {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (v : Cn (box F) 0) :
    Sh F 0 (dn (box F) 0 v) = prA F (dl 0) (S0 F 0 v) - prA F (dl 1) (S0 F 0 v) := by
  have e0 : bv F ((sI (0 : Fin 1)).comp (dl 0)) ((Fin.predAboveOrderHom (0 : Fin 1)).comp (dl 0)) v =
      bv F ((dl (0 : Fin 2)).comp (cst 0 0)) OrderHom.id v :=
    bv_congr (fun i ↦ by
      fin_cases i
      rfl) (fun i ↦ Subsingleton.elim (α := Fin 1) _ _) v
  have e1 : bv F ((sI (0 : Fin 1)).comp (dl 1)) ((Fin.predAboveOrderHom (0 : Fin 1)).comp (dl 1)) v =
      bv F ((dl (1 : Fin 2)).comp (cst 0 0)) OrderHom.id v :=
    bv_congr (fun i ↦ by
      fin_cases i
      rfl) (fun i ↦ Subsingleton.elim (α := Fin 1) _ _) v
  have hS : Sh F 0 = (bv F (sI (0 : Fin 1)) (Fin.predAboveOrderHom (0 : Fin 1))).toLinearMap :=
    (Fin.sum_univ_one (M := Cn (box F) 1 →ₗ[R] Bi F 1 0)
      fun i : Fin 1 ↦ ((-1 : R) ^ (i : ℕ)) • (bv F (sI i) (Fin.predAboveOrderHom i)).toLinearMap).trans (by simp)
  have hd : dn (box F) 0 v = pr (box F) (dl 0) v - pr (box F) (dl 1) v := by
    rw [dn_eq]
    refine (Fin.sum_univ_two (M := Cn (box F) 1)
      fun i : Fin 2 ↦ ((-1 : R) ^ (i : ℕ)) • pr (box F) (dl i) v).trans ?_
    simp [sub_eq_add_neg]
  simp only [S0, prA_bv]
  rw [← e0, ← e1, hS, hd, AlgHom.toLinearMap_apply, map_sub, bv_pr, bv_pr]

end GlobalTheory.CompanionTheory.HopfC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCoboundaryDegreeZeroStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_coboundary_degree_zero : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (v : Cn (box F) 0), Sh F 0 (dn (box F) 0 v) = prA F (dl 0) (S0 F 0 v) - prA F (dl 1) (S0 F 0 v) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.Sh_dn_zero | exact GlobalTheory.CompanionTheory.HopfC.Sh_dn_zero | (intros; apply GlobalTheory.CompanionTheory.HopfC.Sh_dn_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCup1DegreeZeroFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCup1DegreeZeroFormula
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem shuffle_cup1_degree_zero {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (u : Cn (box F) 1) (w : Cn (box F) 0) :
    Sh F 0 (cup1 (box F) 0 u w) = bv F OrderHom.id (cst 1 0) u * bv F (cst 0 1) OrderHom.id w := by
  have hsum : GlobalTheory.CompanionTheory.HopfC.Sh F 0 = AlgHom.toLinearMap
      (GlobalTheory.CompanionTheory.HopfC.bv F (N := 0 + 1) (p := 1) (q := 0)
        (GlobalTheory.CompanionTheory.HopfC.sI 0) (Fin.predAboveOrderHom 0)) := by
    rw [GlobalTheory.CompanionTheory.HopfC.Sh]
    first
    | (rw [Fin.sum_univ_one]; simp)
    | simp
    | (ext; simp)
  rw [hsum, AlgHom.toLinearMap_apply, GlobalTheory.CompanionTheory.HopfC.cup1_apply, map_mul,
    GlobalTheory.CompanionTheory.HopfC.bv_pr, GlobalTheory.CompanionTheory.HopfC.bv_pr]
  congr 1
  all_goals
    first
    | rfl
    | (refine GlobalTheory.CompanionTheory.HopfC.bv_congr (fun i => ?_) (fun i => ?_) _ <;>
        fin_cases i <;> first | rfl | decide | exact Subsingleton.elim (α := Fin 1) _ _)

end GlobalTheory.CompanionTheory.HopfC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCup1DegreeZeroFormulaStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_cup1_degree_zero_formula : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (u : Cn (box F) 1) (w : Cn (box F) 0), Sh F 0 (cup1 (box F) 0 u w) = bv F OrderHom.id (cst 1 0) u * bv F (cst 0 1) OrderHom.id w := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.shuffle_cup1_degree_zero | exact GlobalTheory.CompanionTheory.HopfC.shuffle_cup1_degree_zero | (intros; apply GlobalTheory.CompanionTheory.HopfC.shuffle_cup1_degree_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupProductCompatibleWithComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupProductCompatibleWithComparison
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.DictCup

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem mp_val_congr (x : Cn F 1) {c c' : Fin (1 + 1) ⥤ C} (hc : c = c') {T : C}
    (g : c.obj (Fin.last 1) ⟶ T) (g' : c'.obj (Fin.last 1) ⟶ T) (hg : HEq g g') :
    mp F g (x c) = mp F g' (x c') := by
  subst hc
  obtain rfl := eq_of_heq hg
  rfl

theorem blockDecomposition_mk₂_fact {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : (0 : Fin 3) ⟶ 1) :
    (ComposableArrows.mk₂ φ ψ).map h = φ := by
  rw [show h = homOfLE (by decide) from Subsingleton.elim _ _]
  rfl

theorem composableArrows_mk₂_map_one_two {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : (1 : Fin 3) ⟶ 2) :
    (ComposableArrows.mk₂ φ ψ).map h = ψ := by
  rw [show h = homOfLE (by decide) from Subsingleton.elim _ _]
  rfl

theorem front_chain {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (fr 1).monotone.functor ⋙ ComposableArrows.mk₂ φ ψ = ComposableArrows.mk₁ φ := by
  refine ComposableArrows.ext₁ rfl rfl ?_
  show _ = 𝟙 _ ≫ φ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact blockDecomposition_mk₂_fact φ ψ (homOfLE (by decide))

theorem face_chain {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (dl (0 : Fin (1 + 1 + 1))).monotone.functor ⋙ ComposableArrows.mk₂ φ ψ = ComposableArrows.mk₁ ψ := by
  refine ComposableArrows.ext₁ rfl rfl ?_
  show _ = 𝟙 _ ≫ ψ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  exact composableArrows_mk₂_map_one_two φ ψ (homOfLE (by decide))

theorem cup1_mk₂_eq_mp_mul (x x' : Cn F 1) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'')
    (y : F.obj T') (y' : F.obj T'') (hy : x (ComposableArrows.mk₁ φ) = y)
    (hy' : x' (ComposableArrows.mk₁ ψ) = y') :
    cup1 F 1 x x' (ComposableArrows.mk₂ φ ψ) = mp F ψ y * y' := by
  have e₁ : pr F (fr 1) x (ComposableArrows.mk₂ φ ψ) = mp F ψ y := by
    rw [pr_apply, ← hy]
    refine mp_val_congr x (front_chain φ ψ) _ ψ (heq_of_eq (composableArrows_mk₂_map_one_two φ ψ _))
  have e₂ : pr F (dl 0) x' (ComposableArrows.mk₂ φ ψ) = y' := by
    rw [pr_apply, ← hy']
    refine (mp_val_congr x' (face_chain φ ψ) _ (𝟙 T'') (heq_of_eq ?_)).trans (mp_id F _ _)
    exact (ComposableArrows.mk₂ φ ψ).map_id _
  rw [cup1_apply]
  exact congrArg₂ (· * ·) e₁ e₂

end GlobalTheory.CompanionTheory.HopfC.DictCup

namespace GlobalTheory.CompanionTheory.HopfC

theorem dict_cup : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (u₁ : H1 F →ₗ[R] HH F 1) (u₂ : H2 F →ₗ[R] HH F 2), IsIdealValuedLiftSystemCocycle F u₁ → IsDegreeTwoComparison F u₂ → (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) → ∀ a b, u₂ (cup F a b) = Lc F 1 (u₁ a) (u₁ b) := by
  intro R _ C _ F u₁ u₂ h₁ h₂ hx a b
  obtain ⟨f, rfl⟩ := H1.mk_surjective F a
  obtain ⟨f', rfl⟩ := H1.mk_surjective F b
  obtain ⟨x, hf⟩ := hx f
  obtain ⟨x', hf'⟩ := hx f'
  rw [h₁ f x hf, h₁ f' x' hf', Lc_mk, cup_mk]
  refine h₂ (cupZ F f f') (cz F 1 x x') fun T T' T'' φ ψ ↦ ?_
  rw [cz_val, cupZ_apply]
  exact DictCup.cup1_mk₂_eq_mp_mul x.1 x'.1 φ ψ _ _ (hf T T' φ) (hf' T' T'' ψ)

end GlobalTheory.CompanionTheory.HopfC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupProductCompatibleWithComparisonStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_product_compatible_with_comparison : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (u₁ : H1 F →ₗ[R] HH F 1) (u₂ : H2 F →ₗ[R] HH F 2), IsIdealValuedLiftSystemCocycle F u₁ → IsDegreeTwoComparison F u₂ → (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) → ∀ a b, u₂ (cup F a b) = Lc F 1 (u₁ a) (u₁ b) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.dict_cup | exact GlobalTheory.CompanionTheory.HopfC.dict_cup | (intros; apply GlobalTheory.CompanionTheory.HopfC.dict_cup <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFunctorCategoryOfMeetLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFunctorCategoryOfMeetLattice
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem finite_chains_semilattice : ∀ {P : Type} [SemilatticeInf P] [Finite P] (p : ℕ),
    Finite (Fin (p + 1) ⥤ Pᵒᵖ) := by
  intro P _ _ p
  haveI : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  refine Finite.of_injective (fun F : Fin (p + 1) ⥤ Pᵒᵖ => F.obj) ?_
  intro F G h
  exact CategoryTheory.Functor.ext (fun i => congrFun h i)
    (fun i j f => Quiver.Hom.unop_inj (Subsingleton.elim _ _))

end GlobalTheory.CompanionTheory.HopfC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFunctorCategoryOfMeetLatticeStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_functor_category_of_meet_lattice : ∀ {P : Type} [SemilatticeInf P] [Finite P] (p : ℕ), Finite (Fin (p + 1) ⥤ Pᵒᵖ) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.finite_chains_semilattice | exact GlobalTheory.CompanionTheory.HopfC.finite_chains_semilattice | (intros; apply GlobalTheory.CompanionTheory.HopfC.finite_chains_semilattice <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareTransportAlongEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareTransportAlongEquiv
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem wedge_transport {R : Type} [CommRing R] {V V' W W' : Type} [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V'] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W'] (u : V ≃ₗ[R] V') (v : W ≃ₗ[R] W') (c : V →ₗ[R] V →ₗ[R] W) (c' : V' →ₗ[R] V' →ₗ[R] W') (h : ∀ a b, v (c a b) = c' (u a) (u b)) (e : ⋀[R]^2 V' ≃ₗ[R] W') (he : ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = c' a b) : ∃ e' : ⋀[R]^2 V ≃ₗ[R] W, ∀ a b, e' (exteriorPower.ιMulti R 2 ![a, b]) = c a b := by
  have h₁ : (u : V →ₗ[R] V') ∘ₗ (u.symm : V' →ₗ[R] V) = LinearMap.id :=
    LinearMap.ext fun x => by simp
  have h₂ : (u.symm : V' →ₗ[R] V) ∘ₗ (u : V →ₗ[R] V') = LinearMap.id :=
    LinearMap.ext fun x => by simp
  let A : ⋀[R]^2 V ≃ₗ[R] ⋀[R]^2 V' :=
    LinearEquiv.ofLinear (exteriorPower.map 2 (u : V →ₗ[R] V'))
      (exteriorPower.map 2 (u.symm : V' →ₗ[R] V))
      (by rw [← exteriorPower.map_comp, h₁, exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, h₂, exteriorPower.map_id])
  refine ⟨A.trans (e.trans v.symm), fun a b => ?_⟩
  have hu : (⇑(u : V →ₗ[R] V') ∘ ![a, b]) = ![u a, u b] := by
    funext i
    fin_cases i <;> rfl
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.ofLinear_apply,
    exteriorPower.map_apply_ιMulti, hu, he, ← h, LinearEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.HopfC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorSquareTransportAlongEquivStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorSquare_transport_along_equiv : ∀ {R : Type} [CommRing R] {V V' W W' : Type} [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V'] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W'] (u : V ≃ₗ[R] V') (v : W ≃ₗ[R] W') (c : V →ₗ[R] V →ₗ[R] W) (c' : V' →ₗ[R] V' →ₗ[R] W') (_ : ∀ a b, v (c a b) = c' (u a) (u b)) (e : ⋀[R]^2 V' ≃ₗ[R] W') (_ : ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = c' a b), ∃ e' : ⋀[R]^2 V ≃ₗ[R] W, ∀ a b, e' (exteriorPower.ιMulti R 2 ![a, b]) = c a b := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.wedge_transport | exact GlobalTheory.CompanionTheory.HopfC.wedge_transport | (intros; apply GlobalTheory.CompanionTheory.HopfC.wedge_transport <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeComparisonIndependentOfChoice
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeComparisonIndependentOfChoice
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem mk₁_comp_functor {C D : Type} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) {T T' : C} (φ : T ⟶ T') :
    (ComposableArrows.mk₁ φ ⋙ G : ComposableArrows D 1) = ComposableArrows.mk₁ (G.map φ) :=
  ComposableArrows.ext₁ rfl rfl (by show G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _; simp)

theorem mk₂_comp_functor {C D : Type} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) {T T' T'' : C}
    (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (ComposableArrows.mk₂ φ ψ ⋙ G : ComposableArrows D 2) = ComposableArrows.mk₂ (G.map φ) (G.map ψ) :=
  ComposableArrows.ext₂ rfl rfl rfl (by show G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _; simp)
    (by show G.map ψ = 𝟙 _ ≫ G.map ψ ≫ 𝟙 _; simp)

theorem dictionary_pull : ∀ {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (F' : C' ⥤ CommAlgCat.{0} R) (m : CoefMap (RingHom.id R) F F') (u₁ : H1 F →ₗ[R] HH F 1) (u₁' : H1 F' →ₗ[R] HH F' 1) (u₂ : H2 F →ₗ[R] HH F 2) (u₂' : H2 F' →ₗ[R] HH F' 2), IsIdealValuedLiftSystemCocycle F u₁ → IsIdealValuedLiftSystemCocycle F' u₁' → IsDegreeTwoComparison F u₂ → IsDegreeTwoComparison F' u₂' → (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) → (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) → (∀ c, u₁' (m.pull1 c) = pullH m 1 (u₁ c)) ∧ (∀ c, u₂' (m.pull2 c) = pullH m 2 (u₂ c)) := by
  intro R _ C C' _ _ F F' m u₁ u₁' u₂ u₂' h1 h1' h2 h2' e1 e2
  refine ⟨fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    obtain ⟨x, hx⟩ := e1 f
    rw [h1 f x hx, pullH_mk, CoefMap.pullCohomologyOne_class]
    refine h1' _ _ fun T T' φ ↦ ?_
    have e : x.1 (ComposableArrows.mk₁ φ ⋙ m.G) = x.1 (ComposableArrows.mk₁ (m.G.map φ)) :=
      eq_of_heq (congr_arg_heq x.1 (mk₁_comp_functor m.G φ))
    exact (congrArg (m.α T') (e.trans (hx _ _ _)))
  · obtain ⟨f, rfl⟩ := H2.mk_surjective F c
    obtain ⟨x, hx⟩ := e2 f
    rw [h2 f x hx, pullH_mk, CoefMap.pullCohomologyTwo_class]
    refine h2' _ _ fun T T' T'' φ ψ ↦ ?_
    have e : x.1 (ComposableArrows.mk₂ φ ψ ⋙ m.G) = x.1 (ComposableArrows.mk₂ (m.G.map φ) (m.G.map ψ)) :=
      eq_of_heq (congr_arg_heq x.1 (mk₂_comp_functor m.G φ ψ))
    exact (congrArg (m.α T'') (e.trans (hx _ _ _ _ _)))

end GlobalTheory.CompanionTheory.HopfC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeComparisonIndependentOfChoiceStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_degree_comparison_independent_of_choice : ∀ {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (F' : C' ⥤ CommAlgCat.{0} R) (m : CoefMap (RingHom.id R) F F') (u₁ : H1 F →ₗ[R] HH F 1) (u₁' : H1 F' →ₗ[R] HH F' 1) (u₂ : H2 F →ₗ[R] HH F 2) (u₂' : H2 F' →ₗ[R] HH F' 2), IsIdealValuedLiftSystemCocycle F u₁ → IsIdealValuedLiftSystemCocycle F' u₁' → IsDegreeTwoComparison F u₂ → IsDegreeTwoComparison F' u₂' → (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) → (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) → (∀ c, u₁' (m.pull1 c) = pullH m 1 (u₁ c)) ∧ (∀ c, u₂' (m.pull2 c) = pullH m 2 (u₂ c)) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.dictionary_pull | exact GlobalTheory.CompanionTheory.HopfC.dictionary_pull | (intros; apply GlobalTheory.CompanionTheory.HopfC.dictionary_pull <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeCocyclesLiftToNerve
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeCocyclesLiftToNerve
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.LowDict

theorem exists_quot_equiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (K : Submodule R M) (Z : Submodule R N) (hK : ∀ x, x ∈ K ↔ e x ∈ Z)
    (BK : Submodule R K) (BZ' : Submodule R Z)
    (hB : ∀ (x : K) (f : Z), e x.1 = f.1 → (x ∈ BK ↔ f ∈ BZ')) :
    ∃ u : (Z ⧸ BZ') ≃ₗ[R] (K ⧸ BK),
      (∀ (f : Z) (x : K), e x.1 = f.1 → u (BZ'.mkQ f) = BK.mkQ x) ∧ ∀ f : Z, ∃ x : K, e x.1 = f.1 := by
  have hmap : K.map (e : M →ₗ[R] N) = Z := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hK x).1 hx
    · intro hy
      exact ⟨e.symm y, (hK _).2 (by simpa using hy), by simp⟩
  let v : K ≃ₗ[R] Z := e.ofSubmodules K Z hmap
  have hv : ∀ x : K, (v x).1 = e x.1 := fun _ ↦ rfl
  have hq : BZ'.map (v.symm : Z →ₗ[R] K) = BK := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine (hB _ f ?_).2 hf
      rw [← hv]
      simp
    · intro hx
      exact ⟨v x, (hB x (v x) (hv x).symm).1 hx, by simp⟩
  refine ⟨Submodule.Quotient.equiv BZ' BK v.symm hq, fun f x h ↦ ?_, fun f ↦ ⟨v.symm f, ?_⟩⟩
  · have hx : v.symm f = x := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext h.symm
    rw [← hx]
    rfl
  · rw [← hv]
    simp

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem d2_apply (z : C2 F) {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    d2 F z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ + z T T' T''' φ (ψ ≫ χ) -
      mp F χ (z T T' T'' φ ψ) := rfl

theorem Z2_eq_ker : Z2 F = LinearMap.ker (d2 F) := by
  ext z
  refine ⟨fun h ↦ ?_, fun h T T' T'' T''' φ ψ χ ↦ ?_⟩
  · refine LinearMap.mem_ker.2 ?_
    funext T T' T'' T''' φ ψ χ
    rw [d2_apply]
    have := h φ ψ χ
    simp only [Pi.zero_apply]
    linear_combination -this
  · have := congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (LinearMap.mem_ker.1 h) T) T') T'') T''') φ) ψ) χ
    rw [d2_apply] at this
    simp only [Pi.zero_apply] at this
    linear_combination -this

theorem dict_low : DictSt → ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    ∃ (u₁ : H1 F ≃ₗ[R] HH F 1) (u₂ : H2 F ≃ₗ[R] HH F 2), IsIdealValuedLiftSystemCocycle F u₁.toLinearMap ∧ IsDegreeTwoComparison F u₂.toLinearMap ∧
      (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) ∧
      (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
        x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) := by
  intro hD R _ C _ F
  obtain ⟨e₀, e₁, e₂, e₃, v₀, v₁, v₂, -, h₀, h₁, h₂⟩ := hD R C F
  have k₁ : ∀ x, x ∈ Zc F 1 ↔ e₁ x ∈ Z1 F := fun x ↦ by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, LinearMap.mem_ker, ← h₁, LinearEquiv.map_eq_zero_iff]
  have k₂ : ∀ x, x ∈ Zc F 2 ↔ e₂ x ∈ Z2 F := fun x ↦ by
    rw [Z2_eq_ker, LinearMap.mem_ker, LinearMap.mem_ker, ← h₂, LinearEquiv.map_eq_zero_iff]
  have b₁ : ∀ (x : Zc F 1) (f : Z1 F), e₁ x.1 = f.1 →
      (x ∈ BZ F 1 ↔ f ∈ LinearMap.range ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F))) := fun x f hxf ↦ by
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨e₀ g, Subtype.ext ?_⟩
      rw [LinearMap.codRestrict_apply, ← h₀, hg]
      exact hxf
    · rintro ⟨g, hg⟩
      refine ⟨e₀.symm g, e₁.injective ?_⟩
      rw [h₀, LinearEquiv.apply_symm_apply]
      exact (congrArg Subtype.val hg).trans hxf.symm
  have b₂ : ∀ (x : Zc F 2) (f : Z2 F), e₂ x.1 = f.1 →
      (x ∈ BZ F 2 ↔ f ∈ LinearMap.range ((d1 F).codRestrict (Z2 F) (differential_one_mem_scaled_lattice F))) := fun x f hxf ↦ by
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨e₁ g, Subtype.ext ?_⟩
      rw [LinearMap.codRestrict_apply, ← h₁, hg]
      exact hxf
    · rintro ⟨g, hg⟩
      refine ⟨e₁.symm g, e₂.injective ?_⟩
      rw [h₁, LinearEquiv.apply_symm_apply]
      exact (congrArg Subtype.val hg).trans hxf.symm
  obtain ⟨u₁, c₁, s₁⟩ := exists_quot_equiv e₁ (Zc F 1) (Z1 F) k₁ (BZ F 1) _ b₁
  obtain ⟨u₂, c₂, s₂⟩ := exists_quot_equiv e₂ (Zc F 2) (Z2 F) k₂ (BZ F 2) _ b₂
  refine ⟨u₁, u₂, fun f x hx ↦ c₁ f x ?_, fun f x hx ↦ c₂ f x ?_, fun f ↦ ?_, fun f ↦ ?_⟩
  · funext T T' φ
    exact (v₁ x.1 T T' φ).trans (hx T T' φ)
  · funext T T' T'' φ ψ
    exact (v₂ x.1 T T' T'' φ ψ).trans (hx T T' T'' φ ψ)
  · obtain ⟨x, hx⟩ := s₁ f
    exact ⟨x, fun T T' φ ↦ (v₁ x.1 T T' φ).symm.trans (congrFun (congrFun (congrFun hx T) T') φ)⟩
  · obtain ⟨x, hx⟩ := s₂ f
    exact ⟨x, fun T T' T'' φ ψ ↦ (v₂ x.1 T T' T'' φ ψ).symm.trans
      (congrFun (congrFun (congrFun (congrFun (congrFun hx T) T') T'') φ) ψ)⟩

end GlobalTheory.CompanionTheory.HopfC.LowDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeCocyclesLiftToNerveStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_degree_cocycles_lift_to_nerve : DictSt → ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∃ (u₁ : H1 F ≃ₗ[R] HH F 1) (u₂ : H2 F ≃ₗ[R] HH F 2), IsIdealValuedLiftSystemCocycle F u₁.toLinearMap ∧ IsDegreeTwoComparison F u₂.toLinearMap ∧ (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) ∧ (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.LowDict.dict_low | exact GlobalTheory.CompanionTheory.HopfC.LowDict.dict_low | (intros; apply GlobalTheory.CompanionTheory.HopfC.LowDict.dict_low <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HopfC

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

section Slant

theorem Con_prB {p q q' : ℕ} [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (e : Fin (q + 1) →o Fin (q' + 1))
    (B : Bi F p q) : Con F Ξ q' (prB F e B) = pr F e (Con F Ξ q B) :=
  (GlobalTheory.T.contraction_natural_in_face_maps F Ξ Ξ e OrderHom.id).1 B

theorem Con_prA {p p' q : ℕ} [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ : Cn F p' →ₗ[R] R)
    (e : Fin (p + 1) →o Fin (p' + 1)) (B : Bi F p q) :
    Con F Ξ q (prA F e B) = Con F (Ξ ∘ₗ (pr F e).toLinearMap) q B :=
  (GlobalTheory.T.contraction_natural_in_face_maps (q := q) (q' := q) F (Ξ ∘ₗ (pr F e).toLinearMap) Ξ OrderHom.id e).2 B

theorem Con_dn {p n : ℕ} [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (B : Bi F p n) :
    Con F Ξ (n + 1) (∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) B) = dn F n (Con F Ξ n B) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, GlobalTheory.CompanionTheory.HopfC.dn_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, GlobalTheory.CompanionTheory.HopfC.Con_prB]

theorem cup1_one (x : Cn F 1) : cup1 F 0 x 1 = x := by
  rw [GlobalTheory.CompanionTheory.HopfC.cup1_apply, _root_.map_one, _root_.mul_one]
  first
    | exact (GlobalTheory.CompanionTheory.HopfC.pr_congr (n := 1) (m := 1) (e := GlobalTheory.CompanionTheory.HopfC.fr 0) (e' := OrderHom.id)
        (fun i => Fin.ext rfl) x).trans (GlobalTheory.CompanionTheory.HopfC.pr_id x)
    | exact (GlobalTheory.CompanionTheory.HopfC.pr_congr (n := 1) (m := 1) (e := GlobalTheory.CompanionTheory.HopfC.fr 0) (e' := OrderHom.id)
        (fun i => by ext; simp [GlobalTheory.CompanionTheory.HopfC.fr]) x).trans (GlobalTheory.CompanionTheory.HopfC.pr_id x)
    | exact calc GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.fr 0) x = GlobalTheory.CompanionTheory.HopfC.pr F OrderHom.id x :=
          GlobalTheory.CompanionTheory.HopfC.pr_congr (fun i => Fin.ext rfl) x
        _ = x := GlobalTheory.CompanionTheory.HopfC.pr_id x

variable [Finite (Fin (0 + 1) ⥤ C)] [Finite (Fin (1 + 1) ⥤ C)]

theorem UU_comp_dn (Ξ : Cn F 1 →ₗ[R] R) (n : ℕ) (w : Cn (box F) n) :
    UU F (Ξ ∘ₗ dn F 0) n w =
      Con F Ξ n (prA F (dl 0) (S0 F n w)) - Con F Ξ n (prA F (dl 1) (S0 F n w)) := by
  have hΞ : Ξ ∘ₗ MainStatements.Hodge.dn F 0 =
      Ξ ∘ₗ (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.dl 0)).toLinearMap + (-1 : R) • (Ξ ∘ₗ (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.dl 1)).toLinearMap) := by
    refine LinearMap.ext fun f => ?_
    rw [LinearMap.comp_apply, GlobalTheory.CompanionTheory.HopfC.dn_eq, Fin.sum_univ_two]
    simp
  change GlobalTheory.CompanionTheory.HopfC.Con F (Ξ ∘ₗ MainStatements.Hodge.dn F 0) n (GlobalTheory.CompanionTheory.HopfC.S0 F n w) = _
  rw [hΞ, (GlobalTheory.T.contraction_linear_in_functional F (Ξ ∘ₗ (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.dl 0)).toLinearMap)
      ((-1 : R) • (Ξ ∘ₗ (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.dl 1)).toLinearMap)) (-1 : R) (GlobalTheory.CompanionTheory.HopfC.S0 F n w)).1,
    (GlobalTheory.T.contraction_linear_in_functional F (Ξ ∘ₗ (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.dl 1)).toLinearMap)
      (Ξ ∘ₗ (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.dl 1)).toLinearMap) (-1 : R) (GlobalTheory.CompanionTheory.HopfC.S0 F n w)).2,
    GlobalTheory.CompanionTheory.HopfC.Con_prA, GlobalTheory.CompanionTheory.HopfC.Con_prA, neg_one_smul, sub_eq_add_neg]

theorem transfer_coboundary_degree_zero (Ξ : Cn F 1 →ₗ[R] R) (v : Cn (box F) 0) :
    TT F Ξ 0 (dn (box F) 0 v) = UU F (Ξ ∘ₗ dn F 0) 0 v := by
  change GlobalTheory.CompanionTheory.HopfC.Con F Ξ 0 (GlobalTheory.CompanionTheory.HopfC.Sh F 0 (MainStatements.Hodge.dn (MainStatements.Hodge.box F) 0 v)) = _
  rw [GlobalTheory.T.shuffle_coboundary_degree_zero, map_sub, GlobalTheory.CompanionTheory.HopfC.UU_comp_dn]

theorem TT_dn (Ξ : Cn F 1 →ₗ[R] R) (n : ℕ) (w : Cn (box F) (n + 1)) :
    TT F Ξ (n + 1) (dn (box F) (n + 1) w) = UU F (Ξ ∘ₗ dn F 0) (n + 1) w - dn F n (TT F Ξ n w) := by
  change GlobalTheory.CompanionTheory.HopfC.Con F Ξ (n + 1) (GlobalTheory.CompanionTheory.HopfC.Sh F (n + 1) (MainStatements.Hodge.dn (MainStatements.Hodge.box F) (n + 1) w)) =
    GlobalTheory.CompanionTheory.HopfC.UU F (Ξ ∘ₗ MainStatements.Hodge.dn F 0) (n + 1) w - MainStatements.Hodge.dn F n (GlobalTheory.CompanionTheory.HopfC.Con F Ξ n (GlobalTheory.CompanionTheory.HopfC.Sh F n w))
  rw [GlobalTheory.T.shuffle_coboundary_formula, map_sub, map_sub, GlobalTheory.CompanionTheory.HopfC.Con_dn, GlobalTheory.CompanionTheory.HopfC.UU_comp_dn]

theorem bv_cst_one (n : ℕ) (w : Cn (box F) n) :
    bv F (cst n 1) OrderHom.id w = prA F (dl 0) (S0 F n w) := by
  rw [GlobalTheory.CompanionTheory.HopfC.S0, GlobalTheory.CompanionTheory.HopfC.prA_bv]
  exact GlobalTheory.CompanionTheory.HopfC.bv_congr (fun _ => rfl) (fun _ => rfl) w

theorem bvL_front {x : Cn F 1} (n : ℕ) :
    bv F OrderHom.id (cst 1 0) (pulln (boxL F) 1 x) = (fun a _ ↦ x a ⊗ₜ[R] 1 : Bi F 1 n) := by
  rw [(GlobalTheory.T.bisimplicial_value_of_factor_pullbacks F OrderHom.id (cst 1 0) x).1, pr_id]

theorem bvL_back {x : Cn F 1} (hx : dn F 1 x = 0) (n : ℕ) :
    bv F (cst 1 (0 : Fin (1 + 1))) (fr n) (pulln (boxL F) 1 x) = (0 : Bi F 1 (n + 1)) := by
  rw [(GlobalTheory.T.bisimplicial_value_of_factor_pullbacks F _ _ x).1,
    GlobalTheory.T.degenerate_face_of_one_cocycle_eq_zero F x hx (GlobalTheory.CompanionTheory.HopfC.cst 1 (0 : Fin (1 + 1))) rfl]
  funext a b
  exact TensorProduct.zero_tmul _ _

theorem bvR_front {x : Cn F 1} (hx : dn F 1 x = 0) (n : ℕ) :
    bv F OrderHom.id (cst 1 0) (pulln (boxR F) 1 x) = (0 : Bi F 1 n) := by
  rw [(GlobalTheory.T.bisimplicial_value_of_factor_pullbacks F _ _ x).2,
    GlobalTheory.T.degenerate_face_of_one_cocycle_eq_zero F x hx (GlobalTheory.CompanionTheory.HopfC.cst 1 (0 : Fin (n + 1))) rfl]
  funext a b
  exact TensorProduct.tmul_zero _ _

theorem TT_p {x : Cn F 1} (hx : dn F 1 x = 0) (Ξ : Cn F 1 →ₗ[R] R) (n : ℕ) (w : Cn (box F) n) :
    TT F Ξ n (cup1 (box F) n (pulln (boxL F) 1 x) w) = UU F (Ξ ∘ₗ mulx F x) n w := by
  cases n with
  | zero =>
    change GlobalTheory.CompanionTheory.HopfC.Con F Ξ 0 (GlobalTheory.CompanionTheory.HopfC.Sh F 0 (GlobalTheory.CompanionTheory.HopfC.cup1 (MainStatements.Hodge.box F) 0 (MainStatements.Hodge.pulln (MainStatements.Hodge.boxL F) 1 x) w)) =
      GlobalTheory.CompanionTheory.HopfC.Con F ((Ξ ∘ₗ LinearMap.mulLeft R x) ∘ₗ (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.dl 0)).toLinearMap) 0 (GlobalTheory.CompanionTheory.HopfC.S0 F 0 w)
    rw [GlobalTheory.T.shuffle_cup1_degree_zero_formula, GlobalTheory.CompanionTheory.HopfC.bvL_front, GlobalTheory.CompanionTheory.HopfC.bv_cst_one,
      (GlobalTheory.T.contraction_mul_left_right_and_one F Ξ x (0 : MainStatements.Hodge.Cn F 0) _).1, GlobalTheory.CompanionTheory.HopfC.Con_prA]
  | succ n =>
    change GlobalTheory.CompanionTheory.HopfC.Con F Ξ (n + 1) (GlobalTheory.CompanionTheory.HopfC.Sh F (n + 1) (GlobalTheory.CompanionTheory.HopfC.cup1 (MainStatements.Hodge.box F) (n + 1) (MainStatements.Hodge.pulln (MainStatements.Hodge.boxL F) 1 x) w)) =
      GlobalTheory.CompanionTheory.HopfC.Con F ((Ξ ∘ₗ LinearMap.mulLeft R x) ∘ₗ (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.dl 0)).toLinearMap) (n + 1) (GlobalTheory.CompanionTheory.HopfC.S0 F (n + 1) w)
    rw [GlobalTheory.T.shuffle_cup1_formula_positive_degree, GlobalTheory.CompanionTheory.HopfC.bvL_front, GlobalTheory.CompanionTheory.HopfC.bv_cst_one,
      GlobalTheory.CompanionTheory.HopfC.bvL_back hx, zero_mul, sub_zero,
      (GlobalTheory.T.contraction_mul_left_right_and_one F Ξ x (0 : MainStatements.Hodge.Cn F (n + 1)) _).1, GlobalTheory.CompanionTheory.HopfC.Con_prA]

theorem TT_q {x : Cn F 1} (hx : dn F 1 x = 0) (Ξ : Cn F 1 →ₗ[R] R) (n : ℕ) (w : Cn (box F) (n + 1)) :
    TT F Ξ (n + 1) (cup1 (box F) (n + 1) (pulln (boxR F) 1 x) w) = -cup1 F n x (TT F Ξ n w) := by
  change GlobalTheory.CompanionTheory.HopfC.Con F Ξ (n + 1) (GlobalTheory.CompanionTheory.HopfC.Sh F (n + 1) (GlobalTheory.CompanionTheory.HopfC.cup1 (MainStatements.Hodge.box F) (n + 1) (MainStatements.Hodge.pulln (MainStatements.Hodge.boxR F) 1 x) w)) =
    -GlobalTheory.CompanionTheory.HopfC.cup1 F n x (GlobalTheory.CompanionTheory.HopfC.Con F Ξ n (GlobalTheory.CompanionTheory.HopfC.Sh F n w))
  rw [GlobalTheory.T.shuffle_cup1_formula_positive_degree, GlobalTheory.CompanionTheory.HopfC.bvR_front hx, zero_mul, zero_sub,
    (GlobalTheory.T.bisimplicial_value_of_factor_pullbacks F _ _ x).2, map_neg,
    (GlobalTheory.T.contraction_mul_left_right_and_one F Ξ (0 : MainStatements.Hodge.Cn F 1) _ _).2.1, GlobalTheory.CompanionTheory.HopfC.Con_prB, GlobalTheory.CompanionTheory.HopfC.cup1_apply]

theorem transfer_cup_product_degree_zero {x : Cn F 1} (hx : dn F 1 x = 0) (Ξ : Cn F 1 →ₗ[R] R) (w : Cn (box F) 0) :
    TT F Ξ 0 (cup1 (box F) 0 (pulln (boxR F) 1 x) w) = 0 := by
  show Con F Ξ 0 (Sh F 0 (cup1 (box F) 0 (pulln (boxR F) 1 x) w)) = _
  rw [GlobalTheory.T.shuffle_cup1_degree_zero_formula, bvR_front hx, zero_mul, map_zero]

theorem UU_one (Θ : Cn F 0 →ₗ[R] R) : UU F Θ 0 1 = Θ 1 • 1 := by
  change GlobalTheory.CompanionTheory.HopfC.Con F Θ 0 (GlobalTheory.CompanionTheory.HopfC.S0 F 0 1) = _
  rw [_root_.map_one, (GlobalTheory.T.contraction_mul_left_right_and_one F (q := 0) Θ 0 0 1).2.2]

theorem transfer_sum_projections_degree_zero {x : Cn F 1} (hx : dn F 1 x = 0) (Ξ : Cn F 1 →ₗ[R] R) :
    TT F Ξ 0 (pulln (boxL F) 1 x + pulln (boxR F) 1 x) = Ξ x • 1 := by
  rw [map_add (f := _), ← GlobalTheory.CompanionTheory.HopfC.cup1_one (MainStatements.Hodge.pulln (MainStatements.Hodge.boxL F) 1 x),
    ← GlobalTheory.CompanionTheory.HopfC.cup1_one (MainStatements.Hodge.pulln (MainStatements.Hodge.boxR F) 1 x),
    GlobalTheory.CompanionTheory.HopfC.TT_p hx, GlobalTheory.CompanionTheory.HopfC.transfer_cup_product_degree_zero hx, add_zero, GlobalTheory.CompanionTheory.HopfC.UU_one]
  congr 1
  simp [GlobalTheory.CompanionTheory.HopfC.mulx]

theorem UU_zero (n : ℕ) (w : Cn (box F) n) : UU F (0 : Cn F 0 →ₗ[R] R) n w = 0 := by
  have h := (GlobalTheory.T.contraction_linear_in_functional F (0 : Cn F 0 →ₗ[R] R) 0 (0 : R) (S0 F n w)).2
  rw [zero_smul, zero_smul] at h
  exact h

end Slant

theorem exists_ext (hR : IsField R) {V : Type} [AddCommGroup V] [Module R V] (p : Submodule R V) (f : p →ₗ[R] R) :
    ∃ g : V →ₗ[R] R, g ∘ₗ p.subtype = f := by
  letI := hR.toField
  exact LinearMap.exists_extend f

theorem exists_factor (hR : IsField R) {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (d : V →ₗ[R] W) (Θ : V →ₗ[R] R) (h : ∀ f, d f = 0 → Θ f = 0) : ∃ Ξ : W →ₗ[R] R, Ξ ∘ₗ d = Θ := by
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.HopfC.exists_ext hR (LinearMap.range d)
    ((LinearMap.ker d).liftQ Θ (fun v hv => LinearMap.mem_ker.mpr (h v (LinearMap.mem_ker.mp hv))) ∘ₗ
      (d.quotKerEquivRange).symm.toLinearMap)
  refine ⟨g, LinearMap.ext fun v => ?_⟩
  have h1 := LinearMap.congr_fun hg ⟨d v, LinearMap.mem_range_self d v⟩
  have h2 : (d.quotKerEquivRange).symm ⟨d v, LinearMap.mem_range_self d v⟩ = Submodule.Quotient.mk v := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (by rw [LinearMap.quotKerEquivRange_apply_mk])
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe, h2, Submodule.liftQ_apply] at h1
  simpa using h1

section Cohomology

variable [Finite (Fin (0 + 1) ⥤ C)] [Finite (Fin (1 + 1) ⥤ C)]

theorem UU_key (hR : IsField R) (hS : ∀ f : Cn F 0, dn F 0 f = 0 → ∃ r : R, f = r • (1 : Cn F 0)) (T₀ : C)
    (ε : F.obj T₀ →ₐ[R] R) (Θ : Cn F 0 →ₗ[R] R) (n : ℕ) (w : Zc (box F) (n + 1)) :
    UU F Θ (n + 1) w.1 - Θ 1 • UU F (evF F T₀ ε) (n + 1) w.1 ∈ Bd F (n + 1) := by
  have hε : GlobalTheory.CompanionTheory.HopfC.evF F T₀ ε 1 = 1 := _root_.map_one ε
  obtain ⟨Ξ, hΞ⟩ := GlobalTheory.CompanionTheory.HopfC.exists_factor hR (MainStatements.Hodge.dn F 0)
    (Θ - Θ 1 • GlobalTheory.CompanionTheory.HopfC.evF F T₀ ε) (fun f hf => by
      obtain ⟨r, rfl⟩ := hS f hf
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, map_smul, hε, smul_eq_mul]
      ring)
  have hΘ : Θ - Θ 1 • GlobalTheory.CompanionTheory.HopfC.evF F T₀ ε = Θ + (-Θ 1) • GlobalTheory.CompanionTheory.HopfC.evF F T₀ ε := by
    rw [neg_smul, ← sub_eq_add_neg]
  have e1 := (GlobalTheory.T.contraction_linear_in_functional F Θ ((-Θ 1) • GlobalTheory.CompanionTheory.HopfC.evF F T₀ ε) (-Θ 1) (GlobalTheory.CompanionTheory.HopfC.S0 F (n + 1) w.1)).1
  have e2 := (GlobalTheory.T.contraction_linear_in_functional F (GlobalTheory.CompanionTheory.HopfC.evF F T₀ ε) (GlobalTheory.CompanionTheory.HopfC.evF F T₀ ε) (-Θ 1) (GlobalTheory.CompanionTheory.HopfC.S0 F (n + 1) w.1)).2
  have hlin : GlobalTheory.CompanionTheory.HopfC.UU F (Θ - Θ 1 • GlobalTheory.CompanionTheory.HopfC.evF F T₀ ε) (n + 1) w.1 =
      GlobalTheory.CompanionTheory.HopfC.UU F Θ (n + 1) w.1 - Θ 1 • GlobalTheory.CompanionTheory.HopfC.UU F (GlobalTheory.CompanionTheory.HopfC.evF F T₀ ε) (n + 1) w.1 := by
    change GlobalTheory.CompanionTheory.HopfC.Con F (Θ - Θ 1 • GlobalTheory.CompanionTheory.HopfC.evF F T₀ ε) (n + 1) (GlobalTheory.CompanionTheory.HopfC.S0 F (n + 1) w.1) =
      GlobalTheory.CompanionTheory.HopfC.Con F Θ (n + 1) (GlobalTheory.CompanionTheory.HopfC.S0 F (n + 1) w.1) - Θ 1 • GlobalTheory.CompanionTheory.HopfC.Con F (GlobalTheory.CompanionTheory.HopfC.evF F T₀ ε) (n + 1) (GlobalTheory.CompanionTheory.HopfC.S0 F (n + 1) w.1)
    rw [hΘ, e1, e2, neg_smul, ← sub_eq_add_neg]
  have hd : MainStatements.Hodge.dn (MainStatements.Hodge.box F) (n + 1) w.1 = 0 := LinearMap.mem_ker.mp w.2
  have h7 := GlobalTheory.CompanionTheory.HopfC.TT_dn Ξ n w.1
  rw [hd, map_zero, hΞ, hlin] at h7
  show _ ∈ LinearMap.range (MainStatements.Hodge.dn F n)
  exact LinearMap.mem_range.mpr ⟨GlobalTheory.CompanionTheory.HopfC.TT F Ξ n w.1, (sub_eq_zero.mp h7.symm).symm⟩

theorem TT_mem (l : Cn F 1 →ₗ[R] R) (hl : l ∘ₗ dn F 0 = 0) (n : ℕ) (w : Zc (box F) (n + 1)) :
    TT F l n w.1 ∈ Zc F n := by
  have h7 := GlobalTheory.CompanionTheory.HopfC.TT_dn l n w.1
  rw [LinearMap.mem_ker.mp w.2, map_zero, hl, GlobalTheory.CompanionTheory.HopfC.UU_zero, zero_sub, eq_comm, neg_eq_zero] at h7
  exact LinearMap.mem_ker.mpr h7

theorem TT_Bd (l : Cn F 1 →ₗ[R] R) (hl : l ∘ₗ dn F 0 = 0) (n : ℕ) (w : Cn (box F) (n + 1))
    (hw : w ∈ Bd (box F) (n + 1)) : TT F l n w ∈ Bd F n := by
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
  cases n with
  | zero =>
    rw [GlobalTheory.CompanionTheory.HopfC.transfer_coboundary_degree_zero, hl, GlobalTheory.CompanionTheory.HopfC.UU_zero]
    exact Submodule.zero_mem _
  | succ m =>
    rw [GlobalTheory.CompanionTheory.HopfC.TT_dn, hl, GlobalTheory.CompanionTheory.HopfC.UU_zero, zero_sub]
    exact LinearMap.mem_range.mpr ⟨-GlobalTheory.CompanionTheory.HopfC.TT F l m v, map_neg _ _⟩

theorem exists_Tc (l : Cn F 1 →ₗ[R] R) (hl : l ∘ₗ dn F 0 = 0) :
    ∃ Tc : ∀ n, HH (box F) (n + 1) →ₗ[R] HH F n, ∀ n (w : Zc (box F) (n + 1)),
      Tc n (HH.mk _ _ w) = HH.mk F n ⟨TT F l n w.1, TT_mem l hl n w⟩ := by
  refine ⟨fun n => (GlobalTheory.CompanionTheory.HopfC.BZ (MainStatements.Hodge.box F) (n + 1)).mapQ (GlobalTheory.CompanionTheory.HopfC.BZ F n)
      (LinearMap.codRestrict (GlobalTheory.CompanionTheory.HopfC.Zc F n) (GlobalTheory.CompanionTheory.HopfC.TT F l n ∘ₗ (GlobalTheory.CompanionTheory.HopfC.Zc (MainStatements.Hodge.box F) (n + 1)).subtype)
        (fun w => GlobalTheory.CompanionTheory.HopfC.TT_mem l hl n w)) (by
          intro w hw
          exact GlobalTheory.CompanionTheory.HopfC.TT_Bd l hl n w.1 hw), fun n w => rfl⟩

end Cohomology

theorem bij_pullH {D : Type} [Category.{0} D] {G : D ⥤ CommAlgCat.{0} R} {E : Type} [Category.{0} E]
    {F' : E ⥤ CommAlgCat.{0} R} {π : CoefMap (RingHom.id R) F' G} (hπ : AllQIso π) (n : ℕ) :
    Function.Bijective (pullH π n) := by
  obtain ⟨h0, hs⟩ := hπ
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := GlobalTheory.CompanionTheory.HopfC.HH.mk_surjective F' n c
    rw [GlobalTheory.CompanionTheory.HopfC.pullH_mk, GlobalTheory.CompanionTheory.HopfC.HH.mk_eq_zero] at hc
    rw [GlobalTheory.CompanionTheory.HopfC.HH.mk_eq_zero]
    have hz : MainStatements.Hodge.dn F' n z.1 = 0 := LinearMap.mem_ker.mp z.2
    cases n with
    | zero =>
      have hc' : MainStatements.Hodge.pulln π 0 z.1 = 0 := (Submodule.mem_bot R).mp hc
      obtain ⟨y, hy⟩ := h0.1 z.1 hz ⟨0, by simp [hc']⟩
      show z.1 ∈ (⊥ : Submodule R _)
      rw [Submodule.mem_bot, ← hy, LinearMap.zero_apply]
    | succ k =>
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hc
      obtain ⟨y', hy'⟩ := (hs k).1 z.1 hz ⟨y, hy⟩
      exact LinearMap.mem_range.mpr ⟨y', hy'⟩
  · intro c
    obtain ⟨z, rfl⟩ := GlobalTheory.CompanionTheory.HopfC.HH.mk_surjective G n c
    have hz : MainStatements.Hodge.dn G n z.1 = 0 := LinearMap.mem_ker.mp z.2
    cases n with
    | zero =>
      obtain ⟨x, y, hx, hxy⟩ := h0.2 z.1 hz
      refine ⟨GlobalTheory.CompanionTheory.HopfC.HH.mk F' 0 ⟨x, LinearMap.mem_ker.mpr hx⟩, ?_⟩
      rw [GlobalTheory.CompanionTheory.HopfC.pullH_mk, GlobalTheory.CompanionTheory.HopfC.HH.mk_eq_mk]
      show _ ∈ (⊥ : Submodule R _)
      rw [Submodule.mem_bot]
      rw [LinearMap.zero_apply] at hxy
      exact hxy
    | succ k =>
      obtain ⟨x, y, hx, hxy⟩ := (hs k).2 z.1 hz
      refine ⟨GlobalTheory.CompanionTheory.HopfC.HH.mk F' (k + 1) ⟨x, LinearMap.mem_ker.mpr hx⟩, ?_⟩
      rw [GlobalTheory.CompanionTheory.HopfC.pullH_mk, GlobalTheory.CompanionTheory.HopfC.HH.mk_eq_mk]
      exact LinearMap.mem_range.mpr ⟨y, hxy.symm⟩

theorem package (hR : IsField R) [∀ p, Finite (Fin (p + 1) ⥤ C)] (F : C ⥤ CommAlgCat.{0} R)
    (hdd : ∀ f : Cn F 0, dn F 1 (dn F 0 f) = 0) (hS : ∀ f : Cn F 0, dn F 0 f = 0 → ∃ r : R, f = r • (1 : Cn F 0))
    {D : Type} [Category.{0} D] (G : D ⥤ CommAlgCat.{0} R) (π : CoefMap (RingHom.id R) (box F) G)
    (m : CoefMap (RingHom.id R) F G) (hπ : AllQIso π)
    (hprim : ∀ x : HH F 1, pullH m 1 x = pullH π 1 (pullH (boxL F) 1 x + pullH (boxR F) 1 x))
    (T₀ : C) (ε : F.obj T₀ →ₐ[R] R)
    (hc : ∀ (y : HH F 2) (w : HH (box F) 2), pullH π 2 w = pullH m 2 y → pullH (boxE F T₀ ε) 2 w = y) :
    ∃ (one : HH F 0) (D' : ∀ n, Module.Dual R (HH F 1) → HH F (n + 1) →ₗ[R] HH F n) (τ : ∀ n, HH F n →ₗ[R] HH F n),
      one = HH.mk F 0 ⟨1, by rw [LinearMap.mem_ker, dn_eq, Fin.sum_univ_two]; simp⟩ ∧ (∀ x, Lc F 0 x one = x) ∧
      (∀ l x, D' 0 l x = l x • one) ∧
      (∀ n l x z, D' (n + 1) l (Lc F (n + 1) x z) = l x • τ (n + 1) z - Lc F n x (D' n l z)) ∧
      (∀ n x z, τ (n + 2) (Lc F (n + 1) x z) = Lc F (n + 1) x (τ (n + 1) z)) ∧ (∀ x, τ 1 x = x) ∧ ∀ y, τ 2 y = y := by
  have hbij := fun n => GlobalTheory.CompanionTheory.HopfC.bij_pullH hπ n
  obtain ⟨eπ, heπ⟩ : ∃ e : ∀ n, GlobalTheory.CompanionTheory.HopfC.HH (MainStatements.Hodge.box F) n ≃ₗ[R] GlobalTheory.CompanionTheory.HopfC.HH G n,
      ∀ n w, e n w = GlobalTheory.CompanionTheory.HopfC.pullH π n w :=
    ⟨fun n => LinearEquiv.ofBijective (GlobalTheory.CompanionTheory.HopfC.pullH π n) (hbij n), fun _ _ => rfl⟩
  have hsymm : ∀ n y w, (eπ n).symm y = w ↔ y = GlobalTheory.CompanionTheory.HopfC.pullH π n w := fun n y w => by
    rw [LinearEquiv.symm_apply_eq, heπ]
  have hmul : ∀ k (x : GlobalTheory.CompanionTheory.HopfC.HH F 1) (z : GlobalTheory.CompanionTheory.HopfC.HH F k),
      (eπ (k + 1)).symm (GlobalTheory.CompanionTheory.HopfC.pullH m (k + 1) (GlobalTheory.CompanionTheory.HopfC.Lc F k x z)) =
        GlobalTheory.CompanionTheory.HopfC.Lc (MainStatements.Hodge.box F) k ((eπ 1).symm (GlobalTheory.CompanionTheory.HopfC.pullH m 1 x)) ((eπ k).symm (GlobalTheory.CompanionTheory.HopfC.pullH m k z)) := by
    intro k x z
    rw [hsymm, GlobalTheory.CompanionTheory.HopfC.pullH_Lc, GlobalTheory.CompanionTheory.HopfC.pullH_Lc, ← heπ, ← heπ,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hext : ∀ l : Module.Dual R (GlobalTheory.CompanionTheory.HopfC.HH F 1), ∃ l' : MainStatements.Hodge.Cn F 1 →ₗ[R] R,
      l' ∘ₗ MainStatements.Hodge.dn F 0 = 0 ∧ ∀ x : GlobalTheory.CompanionTheory.HopfC.Zc F 1, l' x.1 = l (GlobalTheory.CompanionTheory.HopfC.HH.mk F 1 x) := by
    intro l
    obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.HopfC.exists_ext hR (GlobalTheory.CompanionTheory.HopfC.Zc F 1) (l ∘ₗ GlobalTheory.CompanionTheory.HopfC.HH.mk F 1)
    refine ⟨g, LinearMap.ext fun f => ?_, fun x => LinearMap.congr_fun hg x⟩
    have hmem : MainStatements.Hodge.dn F 0 f ∈ GlobalTheory.CompanionTheory.HopfC.Zc F 1 := LinearMap.mem_ker.mpr (hdd f)
    have h2 : GlobalTheory.CompanionTheory.HopfC.HH.mk F 1 ⟨_, hmem⟩ = 0 :=
      GlobalTheory.CompanionTheory.HopfC.HH.mk_eq_zero.mpr (LinearMap.mem_range.mpr ⟨f, rfl⟩)
    have h3 := LinearMap.congr_fun hg ⟨_, hmem⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h2, map_zero] at h3
    exact h3
  choose l' hl'd hl'z using hext
  have hTc' := fun l => GlobalTheory.CompanionTheory.HopfC.exists_Tc (l' l) (hl'd l)
  choose Tc hTc using hTc'
  have h1 : ∀ x : GlobalTheory.CompanionTheory.HopfC.Zc F 1, (eπ 1).symm (GlobalTheory.CompanionTheory.HopfC.pullH m 1 (GlobalTheory.CompanionTheory.HopfC.HH.mk F 1 x)) =
      GlobalTheory.CompanionTheory.HopfC.HH.mk (MainStatements.Hodge.box F) 1
        (GlobalTheory.CompanionTheory.HopfC.pullZ (MainStatements.Hodge.boxL F) 1 x + GlobalTheory.CompanionTheory.HopfC.pullZ (MainStatements.Hodge.boxR F) 1 x) := by
    intro x
    rw [hsymm, hprim]
    congr 1
  have hτ1 : ∀ x : GlobalTheory.CompanionTheory.HopfC.HH F 1,
      GlobalTheory.CompanionTheory.HopfC.pullH (MainStatements.Hodge.boxE F T₀ ε) 1 ((eπ 1).symm (GlobalTheory.CompanionTheory.HopfC.pullH m 1 x)) = x := by
    intro x
    obtain ⟨x, rfl⟩ := GlobalTheory.CompanionTheory.HopfC.HH.mk_surjective F 1 x
    have hx : MainStatements.Hodge.dn F 1 x.1 = 0 := LinearMap.mem_ker.mp x.2
    obtain ⟨hl0, hr0⟩ := GlobalTheory.T.box_evaluation_pullback_left_right F T₀ ε x.1 hx
    rw [h1 x, GlobalTheory.CompanionTheory.HopfC.pullH_mk]
    congr 1
    apply Subtype.ext
    show MainStatements.Hodge.pulln (MainStatements.Hodge.boxE F T₀ ε) 1 (MainStatements.Hodge.pulln (MainStatements.Hodge.boxL F) 1 x.1 + MainStatements.Hodge.pulln (MainStatements.Hodge.boxR F) 1 x.1) = x.1
    rw [map_add (f := _), hl0, hr0, zero_add]
  have hτ2 : ∀ y : GlobalTheory.CompanionTheory.HopfC.HH F 2,
      GlobalTheory.CompanionTheory.HopfC.pullH (MainStatements.Hodge.boxE F T₀ ε) 2 ((eπ 2).symm (GlobalTheory.CompanionTheory.HopfC.pullH m 2 y)) = y :=
    fun y => hc y _ (by rw [← heπ, LinearEquiv.apply_symm_apply])
  refine ⟨GlobalTheory.CompanionTheory.HopfC.HH.mk F 0 ⟨1, by rw [LinearMap.mem_ker, GlobalTheory.CompanionTheory.HopfC.dn_eq, Fin.sum_univ_two]; simp⟩,
    fun n l => Tc l n ∘ₗ (eπ (n + 1)).symm.toLinearMap ∘ₗ GlobalTheory.CompanionTheory.HopfC.pullH m (n + 1),
    fun n => GlobalTheory.CompanionTheory.HopfC.pullH (MainStatements.Hodge.boxE F T₀ ε) n ∘ₗ (eπ n).symm.toLinearMap ∘ₗ GlobalTheory.CompanionTheory.HopfC.pullH m n,
    rfl, ?_, ?_, ?_, ?_, fun x => hτ1 x, fun y => hτ2 y⟩
  · intro x
    obtain ⟨x, rfl⟩ := GlobalTheory.CompanionTheory.HopfC.HH.mk_surjective F 1 x
    rw [GlobalTheory.CompanionTheory.HopfC.Lc_mk]
    exact congrArg (GlobalTheory.CompanionTheory.HopfC.HH.mk F 1) (Subtype.ext (GlobalTheory.CompanionTheory.HopfC.cup1_one x.1))
  · intro l x
    obtain ⟨x, rfl⟩ := GlobalTheory.CompanionTheory.HopfC.HH.mk_surjective F 1 x
    have hx : MainStatements.Hodge.dn F 1 x.1 = 0 := LinearMap.mem_ker.mp x.2
    change Tc l 0 ((eπ 1).symm (GlobalTheory.CompanionTheory.HopfC.pullH m 1 (GlobalTheory.CompanionTheory.HopfC.HH.mk F 1 x))) = _
    rw [h1 x, hTc, ← hl'z l x, ← map_smul]
    congr 1
    exact Subtype.ext (GlobalTheory.CompanionTheory.HopfC.transfer_sum_projections_degree_zero hx (l' l))
  · intro n l x z
    obtain ⟨x, rfl⟩ := GlobalTheory.CompanionTheory.HopfC.HH.mk_surjective F 1 x
    have hx : MainStatements.Hodge.dn F 1 x.1 = 0 := LinearMap.mem_ker.mp x.2
    obtain ⟨w, hw⟩ := GlobalTheory.CompanionTheory.HopfC.HH.mk_surjective (MainStatements.Hodge.box F) (n + 1)
      ((eπ (n + 1)).symm (GlobalTheory.CompanionTheory.HopfC.pullH m (n + 1) z))
    change Tc l (n + 1) ((eπ (n + 1 + 1)).symm (GlobalTheory.CompanionTheory.HopfC.pullH m (n + 1 + 1) (GlobalTheory.CompanionTheory.HopfC.Lc F (n + 1) (GlobalTheory.CompanionTheory.HopfC.HH.mk F 1 x) z))) =
      l (GlobalTheory.CompanionTheory.HopfC.HH.mk F 1 x) • GlobalTheory.CompanionTheory.HopfC.pullH (MainStatements.Hodge.boxE F T₀ ε) (n + 1) ((eπ (n + 1)).symm (GlobalTheory.CompanionTheory.HopfC.pullH m (n + 1) z)) -
        GlobalTheory.CompanionTheory.HopfC.Lc F n (GlobalTheory.CompanionTheory.HopfC.HH.mk F 1 x) (Tc l n ((eπ (n + 1)).symm (GlobalTheory.CompanionTheory.HopfC.pullH m (n + 1) z)))
    rw [hmul, h1 x, ← hw, GlobalTheory.CompanionTheory.HopfC.Lc_mk, hTc, hTc, GlobalTheory.CompanionTheory.HopfC.pullH_mk, GlobalTheory.CompanionTheory.HopfC.Lc_mk, ← hl'z l x,
      ← map_smul, ← map_sub, GlobalTheory.CompanionTheory.HopfC.HH.mk_eq_mk]
    have hΘ1 : (l' l ∘ₗ GlobalTheory.CompanionTheory.HopfC.mulx F x.1) 1 = l' l x.1 := by
      simp [GlobalTheory.CompanionTheory.HopfC.mulx]
    have key := GlobalTheory.CompanionTheory.HopfC.UU_key hR hS T₀ ε (l' l ∘ₗ GlobalTheory.CompanionTheory.HopfC.mulx F x.1) n w
    rw [hΘ1, GlobalTheory.T.unitUniversal_eq_pullback_box_evaluation] at key
    convert key using 1
    change GlobalTheory.CompanionTheory.HopfC.TT F (l' l) (n + 1) (GlobalTheory.CompanionTheory.HopfC.cup1 (MainStatements.Hodge.box F) (n + 1)
        (MainStatements.Hodge.pulln (MainStatements.Hodge.boxL F) 1 x.1 + MainStatements.Hodge.pulln (MainStatements.Hodge.boxR F) 1 x.1) w.1) -
      (l' l x.1 • MainStatements.Hodge.pulln (MainStatements.Hodge.boxE F T₀ ε) (n + 1) w.1 - GlobalTheory.CompanionTheory.HopfC.cup1 F n x.1 (GlobalTheory.CompanionTheory.HopfC.TT F (l' l) n w.1)) = _
    rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), GlobalTheory.CompanionTheory.HopfC.TT_p hx, GlobalTheory.CompanionTheory.HopfC.TT_q hx]
    abel
  · intro n x z
    change GlobalTheory.CompanionTheory.HopfC.pullH (MainStatements.Hodge.boxE F T₀ ε) (n + 1 + 1) ((eπ (n + 1 + 1)).symm (GlobalTheory.CompanionTheory.HopfC.pullH m (n + 1 + 1) (GlobalTheory.CompanionTheory.HopfC.Lc F (n + 1) x z))) =
      GlobalTheory.CompanionTheory.HopfC.Lc F (n + 1) x (GlobalTheory.CompanionTheory.HopfC.pullH (MainStatements.Hodge.boxE F T₀ ε) (n + 1) ((eπ (n + 1)).symm (GlobalTheory.CompanionTheory.HopfC.pullH m (n + 1) z)))
    rw [hmul, GlobalTheory.CompanionTheory.HopfC.pullH_Lc, hτ1]

theorem hopfFieldSt : CxSt → DictSt → LowSt → HopfFieldSt := by
  intro hcc hdict _ R _ P _ _ F g hR hStein hfree hexact hHopf
  haveI : ∀ p, Finite (Fin (p + 1) ⥤ Pᵒᵖ) := fun p => GlobalTheory.T.finite_functor_category_of_meet_lattice p
  obtain ⟨D, _, G, π, m, hπ, hprimc, hb⟩ := hHopf
  obtain ⟨T₀, ε, hcc'⟩ := hb trivial
  obtain ⟨u₁, u₂, hF1, hF2, sF1, sF2⟩ := GlobalTheory.T.low_degree_cocycles_lift_to_nerve hdict F
  obtain ⟨u₁E, u₂E, hE1, hE2, conjLinearRankOne, sE2⟩ := GlobalTheory.T.low_degree_cocycles_lift_to_nerve hdict (MainStatements.Hodge.box F)
  obtain ⟨u₁G, u₂G, hG1, hG2, sG1, sG2⟩ := GlobalTheory.T.low_degree_cocycles_lift_to_nerve hdict G
  have nm := GlobalTheory.T.low_degree_comparison_independent_of_choice F G m u₁.toLinearMap u₁G.toLinearMap u₂.toLinearMap u₂G.toLinearMap
    hF1 hG1 hF2 hG2 sF1 sF2
  have nπ := GlobalTheory.T.low_degree_comparison_independent_of_choice (MainStatements.Hodge.box F) G π u₁E.toLinearMap u₁G.toLinearMap
    u₂E.toLinearMap u₂G.toLinearMap hE1 hG1 hE2 hG2 conjLinearRankOne sE2
  have nl := GlobalTheory.T.low_degree_comparison_independent_of_choice F (MainStatements.Hodge.box F) (MainStatements.Hodge.boxL F) u₁.toLinearMap
    u₁E.toLinearMap u₂.toLinearMap u₂E.toLinearMap hF1 hE1 hF2 hE2 sF1 sF2
  have nr := GlobalTheory.T.low_degree_comparison_independent_of_choice F (MainStatements.Hodge.box F) (MainStatements.Hodge.boxR F) u₁.toLinearMap
    u₁E.toLinearMap u₂.toLinearMap u₂E.toLinearMap hF1 hE1 hF2 hE2 sF1 sF2
  have ne := GlobalTheory.T.low_degree_comparison_independent_of_choice (MainStatements.Hodge.box F) F (MainStatements.Hodge.boxE F T₀ ε)
    u₁E.toLinearMap u₁.toLinearMap u₂E.toLinearMap u₂.toLinearMap hE1 hF1 hE2 hF2 conjLinearRankOne sE2
  have hcomm := GlobalTheory.T.cup_product_compatible_with_comparison F u₁.toLinearMap u₂.toLinearMap hF1 hF2 sF1
  simp only [LinearEquiv.coe_coe] at nm nπ nl nr ne hcomm
  have hcF := hcc R Pᵒᵖ F
  have hdd : ∀ f : MainStatements.Hodge.Cn F 0,
      MainStatements.Hodge.dn F 1 (MainStatements.Hodge.dn F 0 f) = 0 :=
    fun f => LinearMap.congr_fun (hcF.1 0) f
  obtain ⟨hS, hS0⟩ := GlobalTheory.T.stein_cocycles_degree_zero_are_constants hdict F hStein
  have hprim : ∀ x : GlobalTheory.CompanionTheory.HopfC.HH F 1, GlobalTheory.CompanionTheory.HopfC.pullH m 1 x =
      GlobalTheory.CompanionTheory.HopfC.pullH π 1 (GlobalTheory.CompanionTheory.HopfC.pullH (MainStatements.Hodge.boxL F) 1 x + GlobalTheory.CompanionTheory.HopfC.pullH (MainStatements.Hodge.boxR F) 1 x) := by
    intro x
    obtain ⟨c, rfl⟩ := u₁.surjective x
    rw [← nm.1 c, hprimc c, nπ.1]
    congr 1
    rw [map_add (f := _), nl.1, nr.1]
  have hcHH : ∀ (y : GlobalTheory.CompanionTheory.HopfC.HH F 2) (w : GlobalTheory.CompanionTheory.HopfC.HH (MainStatements.Hodge.box F) 2),
      GlobalTheory.CompanionTheory.HopfC.pullH π 2 w = GlobalTheory.CompanionTheory.HopfC.pullH m 2 y → GlobalTheory.CompanionTheory.HopfC.pullH (MainStatements.Hodge.boxE F T₀ ε) 2 w = y := by
    intro y w h
    obtain ⟨c, rfl⟩ := u₂.surjective y
    obtain ⟨d, rfl⟩ := u₂E.surjective w
    rw [← nπ.2 d, ← nm.2 c] at h
    rw [← ne.2 d, hcc' c d (u₂G.injective h)]
  obtain ⟨one, D', τ, hone_eq, hcup1, hD0, hDs, hτm, hτ1, hτ2⟩ :=
    GlobalTheory.CompanionTheory.HopfC.package hR F hdd hS G π m hπ hprim T₀ ε hcHH
  obtain ⟨b⟩ := GlobalTheory.T.vector_space_has_basis_of_dimension hR g hfree
  have hsub : Subsingleton (GlobalTheory.CompanionTheory.HopfC.HH F (g + 2)) := by
    refine ⟨fun a a' => ?_⟩
    obtain ⟨a, rfl⟩ := GlobalTheory.CompanionTheory.HopfC.HH.mk_surjective F (g + 2) a
    obtain ⟨a', rfl⟩ := GlobalTheory.CompanionTheory.HopfC.HH.mk_surjective F (g + 2) a'
    rw [GlobalTheory.CompanionTheory.HopfC.HH.mk_eq_mk]
    have ha : MainStatements.Hodge.dn F (g + 1 + 1) a.1 = 0 := LinearMap.mem_ker.mp a.2
    have ha' : MainStatements.Hodge.dn F (g + 1 + 1) a'.1 = 0 := LinearMap.mem_ker.mp a'.2
    obtain ⟨y, hy⟩ := (hexact (g + 1) (by omega) (a.1 - a'.1)).mp (by rw [map_sub, ha, ha', sub_zero])
    exact LinearMap.mem_range.mpr ⟨y, hy⟩
  have hone : ∀ r : R, r • one = 0 → r = 0 := by
    intro r hr
    apply hS0 r
    rw [hone_eq, ← map_smul, GlobalTheory.CompanionTheory.HopfC.HH.mk_eq_zero] at hr
    exact (Submodule.mem_bot R).mp hr
  obtain ⟨e, he⟩ := GlobalTheory.T.contraction_lowering_derivation_formula (GlobalTheory.CompanionTheory.HopfC.HH F) g (b.map u₁) one
    (fun n => GlobalTheory.CompanionTheory.HopfC.Lc F n) D' τ hone hcup1 hD0 hDs hτm hτ1 hτ2 hsub
  exact GlobalTheory.T.exteriorSquare_transport_along_equiv u₁ u₂ _ (GlobalTheory.CompanionTheory.HopfC.Lc F 1) hcomm e he

end GlobalTheory.CompanionTheory.HopfC
