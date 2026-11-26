module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalZeroOfMemHomogeneousIdeal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateFaceOfOneCocycleEqZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateFaceOfOneCocycleEqZero
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem pr_eq_zero_of_degenerate :
    ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {m : ℕ} (x : Cn F 1)
      (_ : dn F 1 x = 0) (e : Fin (1 + 1) →o Fin (m + 1)) (_ : e 0 = e 1), pr F e x = 0 := by
  intro R _ C _ F m x hx e h01
  have key : ∀ i : Fin (1 + 1 + 1),
      GlobalTheory.CompanionTheory.HopfC.pr F ((GlobalTheory.CompanionTheory.HopfC.cst (1 + 1) (e 0)).comp (GlobalTheory.CompanionTheory.HopfC.dl i)) x =
        GlobalTheory.CompanionTheory.HopfC.pr F e x := by
    intro i
    refine GlobalTheory.CompanionTheory.HopfC.pr_congr (fun j => ?_) x
    show e 0 = e j
    fin_cases j
    · rfl
    · exact h01
  have h := congrArg (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.cst (1 + 1) (e 0))) hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero (GlobalTheory.CompanionTheory.HopfC.pr F (GlobalTheory.CompanionTheory.HopfC.cst (1 + 1) (e 0))),
    GlobalTheory.CompanionTheory.HopfC.dn_eq, map_sum] at h
  simp only [map_smul, map_zsmul, GlobalTheory.CompanionTheory.HopfC.pr_pr] at h
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, key] at h
  norm_num at h
  exact h

end GlobalTheory.CompanionTheory.HopfC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateFaceOfOneCocycleEqZeroStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerate_face_of_one_cocycle_eq_zero : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {m : ℕ} (x : Cn F 1) (_ : dn F 1 x = 0) (e : Fin (1 + 1) →o Fin (m + 1)) (_ : e 0 = e 1), pr F e x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.pr_eq_zero_of_degenerate | exact GlobalTheory.CompanionTheory.HopfC.pr_eq_zero_of_degenerate | (intros; apply GlobalTheory.CompanionTheory.HopfC.pr_eq_zero_of_degenerate <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SteinCocyclesDegreeZeroAreConstants
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SteinCocyclesDegreeZeroAreConstants
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem stein_cn : DictSt → ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    Stein F → (∀ f : Cn F 0, dn F 0 f = 0 → ∃ r : R, f = r • (1 : Cn F 0)) ∧
      ∀ r : R, r • (1 : Cn F 0) = 0 → r = 0 := by
  intro hD R _ C _ F hS
  obtain ⟨hex, hinj⟩ := hS
  obtain ⟨e₀, e₁, -, -, h₀, -, -, -, h₀₁, -, -⟩ := hD R C F
  refine ⟨fun f hf => ?_, fun r hr => ?_⟩
  · have hz := h₀₁ f
    rw [hf, map_zero] at hz
    obtain ⟨r, hr⟩ := (hex (e₀ f)).1 hz.symm
    refine ⟨r, ?_⟩
    funext c
    obtain ⟨T, rfl⟩ : ∃ T, c = ComposableArrows.mk₀ T := ⟨_, ComposableArrows.ext₀ rfl⟩
    refine (h₀ f T).symm.trans ?_
    rw [← hr, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    rfl
  · apply hinj
    rw [map_zero]
    funext T
    rw [Algebra.algebraMap_eq_smul_one]
    exact congrFun hr (ComposableArrows.mk₀ T)

end GlobalTheory.CompanionTheory.HopfC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SteinCocyclesDegreeZeroAreConstantsStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stein_cocycles_degree_zero_are_constants : DictSt → ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), Stein F → (∀ f : Cn F 0, dn F 0 f = 0 → ∃ r : R, f = r • (1 : Cn F 0)) ∧ ∀ r : R, r • (1 : Cn F 0) = 0 → r = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.stein_cn | exact GlobalTheory.CompanionTheory.HopfC.stein_cn | (intros; apply GlobalTheory.CompanionTheory.HopfC.stein_cn <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainBaseChangeEquivalences
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainBaseChangeEquivalences
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CochainBC

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C]
    [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (m : BC F F'),
    ∃ (E₀ : R' ⊗[R] C0 F ≃ₗ[R'] C0 F') (E₁ : R' ⊗[R] C1 F ≃ₗ[R'] C1 F') (E₂ : R' ⊗[R] C2 F ≃ₗ[R'] C2 F'),
      (∀ c, E₀ (1 ⊗ₜ c) = fun T ↦ m.α T (c T)) ∧ (∀ c, E₁ (1 ⊗ₜ c) = fun T T' φ ↦ m.α T' (c T T' φ)) ∧
      (∀ c, E₂ (1 ⊗ₜ c) = fun T T' T'' φ ψ ↦ m.α T'' (c T T' T'' φ ψ)) ∧
      (∀ x, E₁ ((d0 F).baseChange R' x) = d0 F' (E₀ x)) ∧ ∀ x, E₂ ((d1 F).baseChange R' x) = d1 F' (E₁ x) := by
  intro R R' _ _ _ C _ _ _ F F' m
  obtain ⟨E₀, hE₀⟩ := GlobalTheory.CompanionTheory.PerfExt.ext0 m
  obtain ⟨E₁, hE₁⟩ := GlobalTheory.CompanionTheory.PerfExt.ext1 m
  obtain ⟨E₂, hE₂⟩ := GlobalTheory.CompanionTheory.PerfExt.ext2 m
  refine ⟨E₀, E₁, E₂, hE₀, hE₁, hE₂, fun x => ?_, fun x => ?_⟩
  · have h := GlobalTheory.CompanionTheory.PerfExt.bc_ext (E₁.toLinearMap ∘ₗ (d0 F).baseChange R') ((d0 F') ∘ₗ E₀.toLinearMap) (by
      intro n
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul, hE₁, LinearMap.comp_apply,
        LinearEquiv.coe_coe, hE₀]
      funext T T' φ
      dsimp only
      rw [amitsur_d0_apply, amitsur_d0_apply, map_sub, m.naturality])
    exact LinearMap.congr_fun h x
  · have h := GlobalTheory.CompanionTheory.PerfExt.bc_ext (E₂.toLinearMap ∘ₗ (d1 F).baseChange R') ((d1 F') ∘ₗ E₁.toLinearMap) (by
      intro n
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul, hE₂, LinearMap.comp_apply,
        LinearEquiv.coe_coe, hE₁]
      funext T T' T'' φ ψ
      dsimp only
      rw [d1_apply, d1_apply, map_add (f := _), map_sub, m.naturality])
    exact LinearMap.congr_fun h x

end GlobalTheory.CompanionTheory.CochainBC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainBaseChangeEquivalencesStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_base_change_equivalences : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (m : BC F F'), ∃ (E₀ : R' ⊗[R] C0 F ≃ₗ[R'] C0 F') (E₁ : R' ⊗[R] C1 F ≃ₗ[R'] C1 F') (E₂ : R' ⊗[R] C2 F ≃ₗ[R'] C2 F'), (∀ c, E₀ (1 ⊗ₜ c) = fun T ↦ m.α T (c T)) ∧ (∀ c, E₁ (1 ⊗ₜ c) = fun T T' φ ↦ m.α T' (c T T' φ)) ∧ (∀ c, E₂ (1 ⊗ₜ c) = fun T T' T'' φ ψ ↦ m.α T'' (c T T' T'' φ ψ)) ∧ (∀ x, E₁ ((d0 F).baseChange R' x) = d0 F' (E₀ x)) ∧ ∀ x, E₂ ((d1 F).baseChange R' x) = d1 F' (E₁ x) := by
  first | exact @GlobalTheory.CompanionTheory.CochainBC.main | exact GlobalTheory.CompanionTheory.CochainBC.main | (intros; apply GlobalTheory.CompanionTheory.CochainBC.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitUniversalEqPullbackBoxEvaluation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitUniversalEqPullbackBoxEvaluation
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem con_evF_eq_evL [Finite (Fin (0 + 1) ⥤ C)] (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (T : C)
    (u : ∀ a : Fin (0 + 1) ⥤ C, F.obj (a.obj (Fin.last 0)) ⊗[R] F.obj T) :
    con (fun a : Fin (0 + 1) ⥤ C ↦ F.obj (a.obj (Fin.last 0))) (F.obj T) (evF F T₀ ε) u =
      evL F T₀ T ε (u ((Functor.const (Fin (0 + 1))).obj T₀)) := by
  refine pure_induction (fun a : Fin (0 + 1) ⥤ C ↦ F.obj (a.obj (Fin.last 0))) (F.obj T)
    (P := fun u ↦ con (fun a : Fin (0 + 1) ⥤ C ↦ F.obj (a.obj (Fin.last 0))) (F.obj T) (evF F T₀ ε) u =
      evL F T₀ T ε (u ((Functor.const (Fin (0 + 1))).obj T₀))) ?_ ?_ ?_ u
  · rw [map_zero]
    exact (map_zero (evL F T₀ T ε)).symm
  · intro f m
    rw [con_pure]
    show evF F T₀ ε f • m = evL F T₀ T ε (f ((Functor.const (Fin (0 + 1))).obj T₀) ⊗ₜ m)
    simp only [evL, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.id_apply,
      Algebra.smul_def]
    rfl
  · intro u v hu hv
    rw [map_add (f := _), hu, hv]
    exact (map_add (evL F T₀ T ε) _ _).symm

theorem tmap_mp_id {T T' : C} (t : F.obj T ⊗[R] F.obj T') :
    Algebra.TensorProduct.map (mp F (𝟙 T)) (mp F (𝟙 T')) t = t := by
  induction t using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul x y => simp only [Algebra.TensorProduct.map_tmul, mp_id]
  | add x y hx hy => rw [map_add (f := _), hx, hy]

theorem UU_evF [Finite (Fin (0 + 1) ⥤ C)] (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (n : ℕ) (w : Cn (box F) n) :
    UU F (evF F T₀ ε) n w = pulln (boxE F T₀ ε) n w := by
  funext b
  have h1 : UU F (evF F T₀ ε) n w b = con (fun a : Fin (0 + 1) ⥤ C ↦ F.obj (a.obj (Fin.last 0)))
      (F.obj (b.obj (Fin.last n))) (evF F T₀ ε) (fun a ↦ S0 F n w a b) := rfl
  have hb : b.map (homOfLE (Fin.le_last (Fin.last n))) = 𝟙 _ := by
    rw [show homOfLE (Fin.le_last (Fin.last n)) = 𝟙 _ from Subsingleton.elim _ _, b.map_id]
  have h2 : S0 F n w ((Functor.const (Fin (0 + 1))).obj T₀) b = w (b ⋙ CategoryTheory.Prod.sectR T₀ C) := by
    show Algebra.TensorProduct.map (mp F (𝟙 T₀)) (mp F (b.map (homOfLE (Fin.le_last (Fin.last n)))))
      (w (b ⋙ CategoryTheory.Prod.sectR T₀ C)) = _
    rw [hb]
    exact tmap_mp_id F _
  rw [h1, con_evF_eq_evL, pulln_apply, h2]
  rfl

end GlobalTheory.CompanionTheory.HopfC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitUniversalEqPullbackBoxEvaluationStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitUniversal_eq_pullback_box_evaluation : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) [Finite (Fin (0 + 1) ⥤ C)] (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (n : ℕ) (w : Cn (box F) n), UU F (evF F T₀ ε) n w = pulln (boxE F T₀ ε) n w := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.UU_evF | exact GlobalTheory.CompanionTheory.HopfC.UU_evF | (intros; apply GlobalTheory.CompanionTheory.HopfC.UU_evF <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoxEvaluationPullbackLeftRight
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoxEvaluationPullbackLeftRight
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

private theorem cochainReindex_apply_const_obj (F : C ⥤ CommAlgCat.{0} R) {n m : ℕ}
    (e : Fin (n + 1) →o Fin (m + 1)) (x : MainStatements.Hodge.Cn F n) (T₀ : C) :
    GlobalTheory.CompanionTheory.HopfC.pr F e x ((Functor.const (Fin (m + 1))).obj T₀) =
      x ((Functor.const (Fin (n + 1))).obj T₀) := by
  first
  | exact GlobalTheory.CatCoh.mp_id F T₀ _
  | exact (GlobalTheory.CatCoh.mp_id F T₀ (x ((Functor.const (Fin (n + 1))).obj T₀)) : _)
  | (simp only [GlobalTheory.CompanionTheory.HopfC.pr]; exact GlobalTheory.CatCoh.mp_id F T₀ _)

theorem cocycle_const (F : C ⥤ CommAlgCat.{0} R) (T₀ : C) (x : Cn F 1) (hx : dn F 1 x = 0) :
    x ((Functor.const (Fin (1 + 1))).obj T₀) = 0 := by
  have h : MainStatements.Hodge.dn F 1 x ((Functor.const (Fin (1 + 1 + 1))).obj T₀) = 0 := by
    rw [hx]; rfl
  rw [GlobalTheory.CompanionTheory.HopfC.dn_eq] at h
  first
  | rw [Fin.sum_univ_three] at h
  | simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at h
  simp only [Pi.add_apply, Pi.smul_apply, cochainReindex_apply_const_obj] at h
  first
  | simpa using h
  | (norm_num at h; exact h)

theorem evL_tmul_one (F : C ⥤ CommAlgCat.{0} R) (T₀ T : C) (ε : F.obj T₀ →ₐ[R] R) (a : F.obj T₀) :
    evL F T₀ T ε (a ⊗ₜ[R] 1) = algebraMap R (F.obj T) (ε a) := by
  first
  | simp [MainStatements.Hodge.evL, Algebra.ofId_apply]
  | (rw [MainStatements.Hodge.evL, Algebra.TensorProduct.lift_tmul]; simp [Algebra.ofId_apply])

theorem evL_one_tmul (F : C ⥤ CommAlgCat.{0} R) (T₀ T : C) (ε : F.obj T₀ →ₐ[R] R) (b : F.obj T) :
    evL F T₀ T ε (1 ⊗ₜ[R] b) = b := by
  first
  | simp [MainStatements.Hodge.evL, Algebra.ofId_apply]
  | (rw [MainStatements.Hodge.evL, Algebra.TensorProduct.lift_tmul]; simp [Algebra.ofId_apply])

theorem boxE_pull_boxL_boxR (F : C ⥤ CommAlgCat.{0} R) (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (x : Cn F 1)
    (hx : dn F 1 x = 0) :
    pulln (boxE F T₀ ε) 1 (pulln (boxL F) 1 x) = 0 ∧ pulln (boxE F T₀ ε) 1 (pulln (boxR F) 1 x) = x := by
  have h0 := GlobalTheory.CompanionTheory.HopfC.cocycle_const F T₀ x hx
  refine ⟨?_, ?_⟩
  · funext c
    calc _ = MainStatements.Hodge.evL F T₀ (c.obj (Fin.last 1)) ε
          (x ((Functor.const (Fin (1 + 1))).obj T₀) ⊗ₜ[R] 1) := rfl
      _ = algebraMap R _ (ε (x ((Functor.const (Fin (1 + 1))).obj T₀))) :=
          GlobalTheory.CompanionTheory.HopfC.evL_tmul_one F T₀ _ ε _
      _ = 0 := by rw [h0, map_zero, map_zero]
  · funext c
    calc _ = MainStatements.Hodge.evL F T₀ (c.obj (Fin.last 1)) ε (1 ⊗ₜ[R] x c) := rfl
      _ = x c := GlobalTheory.CompanionTheory.HopfC.evL_one_tmul F T₀ _ ε _

end GlobalTheory.CompanionTheory.HopfC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoxEvaluationPullbackLeftRightStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.box_evaluation_pullback_left_right : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (x : Cn F 1) (_ : dn F 1 x = 0), pulln (boxE F T₀ ε) 1 (pulln (boxL F) 1 x) = 0 ∧ pulln (boxE F T₀ ε) 1 (pulln (boxR F) 1 x) = x := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.boxE_pull_boxL_boxR | exact GlobalTheory.CompanionTheory.HopfC.boxE_pull_boxL_boxR | (intros; apply GlobalTheory.CompanionTheory.HopfC.boxE_pull_boxL_boxR <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionMulLeftRightAndOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionMulLeftRightAndOne
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.ConMul

theorem con_mul_left {I : Type} [Finite I] {R : Type} [CommRing R] (V : I → Type) [∀ i, CommRing (V i)]
    [∀ i, Algebra R (V i)] (M : Type) [CommRing M] [Algebra R M] (Ξ : (∀ i, V i) →ₗ[R] R) (x : ∀ i, V i)
    (u : ∀ i, V i ⊗[R] M) :
    con V M Ξ (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * u i) = con V M (Ξ ∘ₗ LinearMap.mulLeft R x) u := by
  revert u
  refine GlobalTheory.CompanionTheory.HopfC.pure_induction V M ?_ ?_ ?_
  · have h : (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * (0 : ∀ i, V i ⊗[R] M) i) = 0 := by
      funext i
      simp
    rw [h, map_zero, map_zero]
  · intro f m
    have h : (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * (f i ⊗ₜ[R] m)) = fun i ↦ (x * f) i ⊗ₜ[R] m := by
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [h, GlobalTheory.CompanionTheory.HopfC.con_pure, GlobalTheory.CompanionTheory.HopfC.con_pure]
    rfl
  · intro u v hu hv
    have h : (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * (u + v) i) =
        (fun i ↦ (x i ⊗ₜ[R] (1 : M)) * u i) + fun i ↦ (x i ⊗ₜ[R] (1 : M)) * v i := by
      funext i
      simp [mul_add]
    rw [h, map_add (f := _), map_add (f := _), hu, hv]

theorem con_mul_right {I : Type} [Finite I] {R : Type} [CommRing R] (V : I → Type) [∀ i, CommRing (V i)]
    [∀ i, Algebra R (V i)] (M : Type) [CommRing M] [Algebra R M] (Ξ : (∀ i, V i) →ₗ[R] R) (y : M)
    (u : ∀ i, V i ⊗[R] M) :
    con V M Ξ (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * u i) = y * con V M Ξ u := by
  induction u using pure_induction with
  | h0 =>
    have h : (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * (0 : ∀ i, V i ⊗[R] M) i) = 0 := by
      funext i; simp
    rw [h, map_zero, mul_zero]
  | hp f m =>
    have h : (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * (f i ⊗ₜ[R] m)) = fun i ↦ f i ⊗ₜ[R] (y * m) := by
      funext i; simp
    rw [h, con_pure, con_pure, mul_smul_comm]
  | ha u v hu hv =>
    have h : (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * (u + v) i) =
        (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * u i) + (fun i ↦ ((1 : V i) ⊗ₜ[R] y) * v i) := by
      funext i; simp [mul_add]
    rw [h, map_add (f := _), map_add (f := _), hu, hv, mul_add]

theorem con_products {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (x : Cn F p) (y : Cn F q) (B : Bi F p q) :
    Con F Ξ q ((fun a _ ↦ x a ⊗ₜ[R] 1 : Bi F p q) * B) = Con F (Ξ ∘ₗ LinearMap.mulLeft R x) q B ∧
    Con F Ξ q ((fun _ b ↦ 1 ⊗ₜ[R] y b : Bi F p q) * B) = y * Con F Ξ q B ∧
    Con F Ξ q (1 : Bi F p q) = Ξ 1 • (1 : Cn F q) := by
  refine ⟨?_, ?_, ?_⟩
  · funext b
    exact GlobalTheory.CompanionTheory.HopfC.ConMul.con_mul_left (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p)))
      (F.obj (b.obj (Fin.last q))) Ξ x (fun a ↦ B a b)
  · funext b
    exact GlobalTheory.CompanionTheory.HopfC.ConMul.con_mul_right (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p)))
      (F.obj (b.obj (Fin.last q))) Ξ (y b) (fun a ↦ B a b)
  · funext b
    exact GlobalTheory.CompanionTheory.HopfC.con_pure (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p)))
      (F.obj (b.obj (Fin.last q))) Ξ 1 1

end GlobalTheory.CompanionTheory.HopfC.ConMul
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionMulLeftRightAndOneStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_mul_left_right_and_one : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q : ℕ} [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (x : Cn F p) (y : Cn F q) (B : Bi F p q), Con F Ξ q ((fun a _ ↦ x a ⊗ₜ[R] 1 : Bi F p q) * B) = Con F (Ξ ∘ₗ LinearMap.mulLeft R x) q B ∧ Con F Ξ q ((fun _ b ↦ 1 ⊗ₜ[R] y b : Bi F p q) * B) = y * Con F Ξ q B ∧ Con F Ξ q (1 : Bi F p q) = Ξ 1 • (1 : Cn F q) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.ConMul.con_products | exact GlobalTheory.CompanionTheory.HopfC.ConMul.con_products | (intros; apply GlobalTheory.CompanionTheory.HopfC.ConMul.con_products <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionNaturalInFaceMaps
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionNaturalInFaceMaps
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.HopfC.ConPr

theorem Con_apply {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (q : ℕ) (B : Bi F p q) (b : Fin (q + 1) ⥤ C) :
    Con F Ξ q B b = con (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p))) (F.obj (b.obj (Fin.last q))) Ξ
      (fun a ↦ B a b) := rfl

theorem con_lTensor {R : Type} [CommRing R] {I : Type} [Finite I] (V : I → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module R (V i)] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (Ξ : (∀ i, V i) →ₗ[R] R) (φ : M →ₗ[R] M') (u : ∀ i, V i ⊗[R] M) :
    con V M' Ξ (fun i ↦ LinearMap.lTensor (V i) φ (u i)) = φ (con V M Ξ u) := by
  induction u using pure_induction with
  | h0 =>
    have h : (fun i ↦ LinearMap.lTensor (V i) φ ((0 : ∀ i, V i ⊗[R] M) i)) = 0 := by
      funext i; simp
    rw [h]; simp
  | hp f m =>
    simp only [LinearMap.lTensor_tmul]
    rw [con_pure, con_pure, map_smul]
  | ha u v hu hv =>
    have h : (fun i ↦ LinearMap.lTensor (V i) φ ((u + v) i)) =
        (fun i ↦ LinearMap.lTensor (V i) φ (u i)) + (fun i ↦ LinearMap.lTensor (V i) φ (v i)) := by
      funext i; simp
    rw [h, map_add (f := _), map_add (f := _), map_add (f := _), hu, hv]

theorem tmap_id_eq {R : Type} [CommRing R] {A B B' : Type} [CommRing A] [CommRing B] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R B'] (g : B →ₐ[R] B') (t : A ⊗[R] B) :
    Algebra.TensorProduct.map (AlgHom.id R A) g t = LinearMap.lTensor A g.toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem Con_prB {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p q q' : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (e : Fin (q + 1) →o Fin (q' + 1)) (B : Bi F p q) :
    Con F Ξ q' (prB F e B) = pr F e (Con F Ξ q B) := by
  funext b
  rw [pr_apply, Con_apply, Con_apply]
  simp only [prB_apply, tmap_id_eq]
  exact con_lTensor (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p))) Ξ _ _

theorem con_prA {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p p' : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ' : Cn F p' →ₗ[R] R)
    (e : Fin (p + 1) →o Fin (p' + 1)) (M : Type) [AddCommGroup M] [Module R M]
    (u : ∀ a : Fin (p + 1) ⥤ C, F.obj (a.obj (Fin.last p)) ⊗[R] M) :
    con (fun a : Fin (p' + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p'))) M Ξ'
      (fun a ↦ LinearMap.rTensor M (mp F (a.map (homOfLE (Fin.le_last (e (Fin.last p)))))).toLinearMap
        (u (e.monotone.functor ⋙ a))) =
    con (fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p))) M (Ξ' ∘ₗ (pr F e).toLinearMap) u := by
  induction u using pure_induction with
  | h0 =>
    have h : (fun a : Fin (p' + 1) ⥤ C ↦ LinearMap.rTensor M (mp F (a.map (homOfLE (Fin.le_last (e (Fin.last p)))))).toLinearMap
        ((0 : ∀ a : Fin (p + 1) ⥤ C, F.obj (a.obj (Fin.last p)) ⊗[R] M) (e.monotone.functor ⋙ a))) = 0 := by
      funext a; exact map_zero _
    rw [h]; simp
  | hp f m =>
    simp only [LinearMap.rTensor_tmul]
    rw [con_pure (V := fun a : Fin (p + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p)))]
    exact con_pure (fun a : Fin (p' + 1) ⥤ C ↦ F.obj (a.obj (Fin.last p'))) M Ξ' (pr F e f) m
  | ha u v hu hv =>
    rw [map_add (f := _), ← hu, ← hv, ← map_add (f := _)]
    congr 1
    funext a
    exact map_add _ _ _

theorem tmap_id_eq' {R : Type} [CommRing R] {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra R A] [Algebra R A'] [Algebra R B] (g : A →ₐ[R] A') (t : A ⊗[R] B) :
    Algebra.TensorProduct.map g (AlgHom.id R B) t = LinearMap.rTensor B g.toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem Con_prA {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p p' q : ℕ}
    [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ' : Cn F p' →ₗ[R] R)
    (e : Fin (p + 1) →o Fin (p' + 1)) (B : Bi F p q) :
    Con F Ξ' q (prA F e B) = Con F (Ξ' ∘ₗ (pr F e).toLinearMap) q B := by
  funext b
  rw [Con_apply, Con_apply]
  simp only [prA_apply, tmap_id_eq']
  exact con_prA F Ξ' e _ (fun a ↦ B a b)

theorem con_pr : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p p' q q' : ℕ} [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (Ξ' : Cn F p' →ₗ[R] R) (e : Fin (q + 1) →o Fin (q' + 1)) (e' : Fin (p + 1) →o Fin (p' + 1)), (∀ B : Bi F p q, Con F Ξ q' (prB F e B) = pr F e (Con F Ξ q B)) ∧ (∀ B : Bi F p q, Con F Ξ' q (prA F e' B) = Con F (Ξ' ∘ₗ (pr F e').toLinearMap) q B) :=
  fun F _ _ _ _ _ _ Ξ Ξ' e e' ↦ ⟨Con_prB F Ξ e, Con_prA F Ξ' e'⟩

end GlobalTheory.CompanionTheory.HopfC.ConPr
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionNaturalInFaceMapsStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_natural_in_face_maps : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {p p' q q' : ℕ} [Finite (Fin (p + 1) ⥤ C)] [Finite (Fin (p' + 1) ⥤ C)] (Ξ : Cn F p →ₗ[R] R) (Ξ' : Cn F p' →ₗ[R] R) (e : Fin (q + 1) →o Fin (q' + 1)) (e' : Fin (p + 1) →o Fin (p' + 1)), (∀ B : Bi F p q, Con F Ξ q' (prB F e B) = pr F e (Con F Ξ q B)) ∧ (∀ B : Bi F p q, Con F Ξ' q (prA F e' B) = Con F (Ξ' ∘ₗ (pr F e').toLinearMap) q B) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.ConPr.con_pr | exact GlobalTheory.CompanionTheory.HopfC.ConPr.con_pr | (intros; apply GlobalTheory.CompanionTheory.HopfC.ConPr.con_pr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCup1FormulaPositiveDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCup1FormulaPositiveDegree
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.ShMul

theorem val_predAbove {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((Fin.predAboveOrderHom i t : Fin (n + 1)) : ℕ) = if i.1 < t.1 then t.1 - 1 else t.1 := by
  show ((Fin.predAbove i t : Fin (n + 1)) : ℕ) = _
  rw [Fin.predAbove]
  split_ifs with h₁ h₂ h₂
  · simp
  · exact absurd (by simpa [Fin.lt_def] using h₁) h₂
  · exact absurd (by simpa [Fin.lt_def] using h₂) h₁
  · simp

theorem val_sI {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((sI i t : Fin (1 + 1)) : ℕ) = if i.1 < t.1 then 1 else 0 := by
  show ((if i.castSucc < t then (1 : Fin (1 + 1)) else 0 : Fin (1 + 1)) : ℕ) = _
  by_cases h : i.1 < t.1
  · rw [if_pos (by simpa [Fin.lt_def] using h), if_pos h]; rfl
  · rw [if_neg (by simpa [Fin.lt_def] using h), if_neg h]; rfl

theorem shuffle_cup1_product_formula {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (n : ℕ)
    (u : Cn (box F) 1) (w : Cn (box F) (n + 1)) :
    Sh F (n + 1) (cup1 (box F) (n + 1) u w) =
      bv F OrderHom.id (cst 1 0) u * bv F (cst (n + 1) 1) OrderHom.id w -
        bv F (cst 1 0) (fr n) u * prB F (dl 0) (Sh F n w) := by
  have a1 : bv F (sI (0 : Fin (n + 1 + 1))) (Fin.predAboveOrderHom 0) (pr (box F) (fr (n + 1)) u) =
      bv F OrderHom.id (cst 1 0) u := by
    rw [bv_pr]
    refine bv_congr ?_ ?_ u
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if 0 < t.val then 1 else 0) = t.val
      have ht := t.isLt
      split_ifs <;> omega
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if 0 < t.val then t.val - 1 else t.val) = 0
      have ht := t.isLt
      split_ifs <;> omega
  have a2 : bv F (sI (0 : Fin (n + 1 + 1))) (Fin.predAboveOrderHom 0) (pr (box F) (dl 0) w) =
      bv F (cst (n + 1) 1) OrderHom.id w := by
    rw [bv_pr]
    refine bv_congr ?_ ?_ w
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if 0 < t.val + 1 then 1 else 0) = 1
      have ht := t.isLt
      split_ifs <;> omega
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if 0 < t.val + 1 then t.val + 1 - 1 else t.val + 1) = t.val
      have ht := t.isLt
      split_ifs <;> omega
  have b1 : ∀ j : Fin (n + 1), bv F (sI j.succ) (Fin.predAboveOrderHom j.succ) (pr (box F) (fr (n + 1)) u) =
      bv F (cst 1 0) (fr n) u := fun j ↦ by
    rw [bv_pr]
    refine bv_congr ?_ ?_ u
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if j.val + 1 < t.val then 1 else 0) = 0
      have ht := t.isLt
      split_ifs <;> omega
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if j.val + 1 < t.val then t.val - 1 else t.val) = t.val
      have ht := t.isLt
      split_ifs <;> omega
  have b2 : ∀ j : Fin (n + 1), bv F (sI j.succ) (Fin.predAboveOrderHom j.succ) (pr (box F) (dl 0) w) =
      prB F (dl 0) (bv F (sI j) (Fin.predAboveOrderHom j) w) := fun j ↦ by
    rw [bv_pr, prB_bv]
    refine bv_congr ?_ ?_ w
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if j.val + 1 < t.val + 1 then 1 else 0) = (if j.val < t.val then 1 else 0)
      have ht := t.isLt
      split_ifs <;> omega
    · intro t
      apply Fin.ext
      simp only [OrderHom.comp, OrderHom.coe_mk, Function.comp_apply, val_sI, val_predAbove]
      change (if j.val + 1 < t.val + 1 then t.val + 1 - 1 else t.val + 1) = (j.predAboveOrderHom t).succ.val
      rw [Fin.val_succ, val_predAbove]
      have ht := t.isLt
      split_ifs <;> omega
  simp only [Sh, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, cup1_apply, map_mul, map_sum,
    map_smul]
  rw [Fin.sum_univ_succ]
  simp only [a1, a2, b1, b2, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Finset.mul_sum, mul_smul_comm]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [pow_succ]

end GlobalTheory.CompanionTheory.HopfC.ShMul
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCup1FormulaPositiveDegreeStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_cup1_formula_positive_degree : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (u : Cn (box F) 1) (w : Cn (box F) (n + 1)), Sh F (n + 1) (cup1 (box F) (n + 1) u w) = bv F OrderHom.id (cst 1 0) u * bv F (cst (n + 1) 1) OrderHom.id w - bv F (cst 1 0) (fr n) u * prB F (dl 0) (Sh F n w) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.ShMul.shuffle_cup1_product_formula | exact GlobalTheory.CompanionTheory.HopfC.ShMul.shuffle_cup1_product_formula | (intros; apply GlobalTheory.CompanionTheory.HopfC.ShMul.shuffle_cup1_product_formula <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCoboundaryFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCoboundaryFormula
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.Prism

theorem prism_sum {R G : Type} [CommRing R] [AddCommGroup G] [Module R G] (N : ℕ) (a b : ℕ → ℕ → G)
    (h1 : ∀ k j, k < N → j ≤ k → a (k + 1) j = b k j)
    (h2 : ∀ k j, k < N → k < j → j < N + 1 → a k (j + 1) = b k j)
    (h3 : ∀ k, k < N → a k (k + 1) = a (k + 1) (k + 1)) :
    ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 2), ((-1 : R) ^ (i + j)) • a i j =
      a 0 0 - a N (N + 1) - ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (N + 1), ((-1 : R) ^ (k + j)) • b k j := by
  have row : ∀ i, i ≤ N → ∑ j ∈ Finset.range (N + 2), ((-1 : R) ^ (i + j)) • a i j =
      ∑ j ∈ Finset.range i, ((-1 : R) ^ (i + j)) • a i j + (a i i - a i (i + 1)) +
        ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) := by
    intro i hi
    have e1 := Finset.sum_range_add_sum_Ico (fun j ↦ ((-1 : R) ^ (i + j)) • a i j) (show i ≤ N + 2 by omega)
    have e2 : ∑ j ∈ Finset.Ico i (N + 2), ((-1 : R) ^ (i + j)) • a i j =
        ((-1 : R) ^ (i + i)) • a i i + ∑ j ∈ Finset.Ico i (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) := by
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_Ico_add' (fun j ↦ ((-1 : R) ^ (i + j)) • a i j) i (N + 1) 1]
    have e3 : ∑ j ∈ Finset.Ico i (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) =
        ((-1 : R) ^ (i + (i + 1))) • a i (i + 1) +
          ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) :=
      Finset.sum_eq_sum_Ico_succ_bot (by omega) _
    have s1 : ((-1 : R) ^ (i + i)) = 1 := Even.neg_one_pow ⟨i, rfl⟩
    have s2 : ((-1 : R) ^ (i + (i + 1))) = -1 := by rw [← add_assoc, pow_succ, s1]; simp
    rw [← e1, e2, e3, s1, s2, one_smul, neg_smul, one_smul]
    abel
  rw [Finset.sum_congr rfl (fun i hi ↦ row i (by have := Finset.mem_range.1 hi; omega))]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have tL : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range i, ((-1 : R) ^ (i + j)) • a i j =
      - ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ((-1 : R) ^ (k + j)) • b k j := by
    rw [Finset.sum_range_succ', Finset.range_zero, Finset.sum_empty, add_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [h1 k j (Finset.mem_range.1 hk) (by have := Finset.mem_range.1 hj; omega), ← neg_smul]
    congr 1
    ring
  have tR : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.Ico (i + 1) (N + 1), ((-1 : R) ^ (i + (j + 1))) • a i (j + 1) =
      - ∑ k ∈ Finset.range N, ∑ j ∈ Finset.Ico (k + 1) (N + 1), ((-1 : R) ^ (k + j)) • b k j := by
    rw [Finset.sum_range_succ, Finset.Ico_self, Finset.sum_empty, add_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have := Finset.mem_Ico.1 hj
    rw [h2 k j (Finset.mem_range.1 hk) (by omega) (by omega), ← neg_smul]
    congr 1
    ring
  have tD : ∑ i ∈ Finset.range (N + 1), (a i i - a i (i + 1)) = a 0 0 - a N (N + 1) := by
    rw [Finset.sum_range_succ, Finset.sum_congr rfl (fun k hk ↦ by rw [h3 k (Finset.mem_range.1 hk)]),
      Finset.sum_range_sub' (fun i ↦ a i i)]
    abel
  have tS : ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (N + 1), ((-1 : R) ^ (k + j)) • b k j =
      ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), ((-1 : R) ^ (k + j)) • b k j +
        ∑ k ∈ Finset.range N, ∑ j ∈ Finset.Ico (k + 1) (N + 1), ((-1 : R) ^ (k + j)) • b k j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have := Finset.mem_range.1 hk
    exact (Finset.sum_range_add_sum_Ico _ (by omega)).symm
  rw [tL, tR, tD, tS]
  abel

section

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem val_sI {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((sI i t : Fin (1 + 1)) : ℕ) = if i.1 < t.1 then 1 else 0 := by
  show (((if i.castSucc < t then 1 else 0 : Fin (1 + 1))) : ℕ) = _
  by_cases h : i.1 < t.1
  · rw [if_pos (show i.castSucc < t from h), if_pos h]; rfl
  · rw [if_neg (show ¬ i.castSucc < t from h), if_neg h]; rfl

theorem val_pa {n : ℕ} (i : Fin (n + 1)) (t : Fin (n + 1 + 1)) :
    ((Fin.predAboveOrderHom i t : Fin (n + 1)) : ℕ) = if i.1 < t.1 then t.1 - 1 else t.1 := by
  show ((Fin.predAbove i t : Fin (n + 1)) : ℕ) = _
  rw [Fin.predAbove]
  by_cases h : i.1 < t.1
  · rw [dite_eq_left (show i.castSucc < t from h), if_pos h]; simp
  · rw [dite_eq_right (show ¬ i.castSucc < t from h), if_neg h]; simp

def aT {n : ℕ} (w : Cn (box F) (n + 1)) (i j : ℕ) : Bi F 1 (n + 1) :=
  if h : i < n + 2 ∧ j < n + 3 then
    bv F ((sI (⟨i, h.1⟩ : Fin (n + 1 + 1))).comp (dl (⟨j, h.2⟩ : Fin (n + 1 + 1 + 1))))
      ((Fin.predAboveOrderHom (⟨i, h.1⟩ : Fin (n + 1 + 1))).comp (dl (⟨j, h.2⟩ : Fin (n + 1 + 1 + 1)))) w
  else 0

def bT {n : ℕ} (w : Cn (box F) (n + 1)) (k j : ℕ) : Bi F 1 (n + 1) :=
  if h : k < n + 1 ∧ j < n + 2 then
    bv F (sI (⟨k, h.1⟩ : Fin (n + 1)))
      ((dl (⟨j, h.2⟩ : Fin (n + 1 + 1))).comp (Fin.predAboveOrderHom (⟨k, h.1⟩ : Fin (n + 1)))) w
  else 0

variable {F}

theorem prism_term_lower_index {n : ℕ} (w : Cn (box F) (n + 1)) (k j : ℕ) (hk : k < n + 1) (hj : j ≤ k) :
    aT F w (k + 1) j = bT F w k j := by
  rw [aT, bT, dite_eq_left (by omega), dite_eq_left (by omega)]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl]
    grind

theorem prism_term_upper_index {n : ℕ} (w : Cn (box F) (n + 1)) (k j : ℕ) (hk : k < n + 1) (hkj : k < j) (hj : j < n + 2) :
    aT F w k (j + 1) = bT F w k j := by
  rw [aT, bT, dite_eq_left (by omega), dite_eq_left (by omega)]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl]
    grind

theorem prism_term_diagonal_equality {n : ℕ} (w : Cn (box F) (n + 1)) (k : ℕ) (hk : k < n + 1) :
    aT F w k (k + 1) = aT F w (k + 1) (k + 1) := by
  rw [aT, aT, dite_eq_left (by omega), dite_eq_left (by omega)]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl]
    grind

theorem aT_first {n : ℕ} (w : Cn (box F) (n + 1)) : aT F w 0 0 = prA F (dl 0) (S0 F (n + 1) w) := by
  rw [aT, dite_eq_left (by omega), S0, prA_bv]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl, cst_apply, Fin.val_zero]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl, Fin.val_zero, OrderHom.id_coe, id_eq]
    grind

theorem aT_last {n : ℕ} (w : Cn (box F) (n + 1)) :
    aT F w (n + 1) (n + 2) = prA F (dl 1) (S0 F (n + 1) w) := by
  rw [aT, dite_eq_left (by omega), S0, prA_bv]
  refine bv_congr (fun t ↦ ?_) (fun t ↦ ?_) w
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_sI, val_dl, cst_apply, Fin.val_zero, Fin.val_one]
    grind
  · apply Fin.ext
    simp only [OrderHom.comp_coe, Function.comp_apply, val_pa, val_dl, OrderHom.id_coe, id_eq]
    grind

theorem Sh_dn_expand {n : ℕ} (w : Cn (box F) (n + 1)) :
    Sh F (n + 1) (dn (box F) (n + 1) w) =
      ∑ i ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.range (n + 1 + 2), ((-1 : R) ^ (i + j)) • aT F w i j := by
  rw [dn_eq (n + 1)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_range, Sh, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum,
    map_smul, bv_pr, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [aT, dite_eq_left ⟨i.2, j.2⟩, pow_add, mul_comm]

theorem prB_Sh_expand {n : ℕ} (w : Cn (box F) (n + 1)) :
    ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) =
      ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 + 1), ((-1 : R) ^ (k + j)) • bT F w k j := by
  simp only [Finset.sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Sh, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum, map_smul, prB_bv]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [bT, dite_eq_left ⟨k.2, j.2⟩, smul_smul, pow_add, mul_comm]

theorem shuffle_coboundary_prism_identity {n : ℕ} (w : Cn (box F) (n + 1)) :
    Sh F (n + 1) (dn (box F) (n + 1) w) = prA F (dl 0) (S0 F (n + 1) w) - prA F (dl 1) (S0 F (n + 1) w) -
      ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) := by
  rw [Sh_dn_expand, prB_Sh_expand, ← aT_first, ← aT_last]
  exact prism_sum (n + 1) (aT F w) (bT F w) (fun k j hk hj ↦ prism_term_lower_index w k j hk hj)
    (fun k j hk hkj hj ↦ prism_term_upper_index w k j hk hkj hj) (fun k hk ↦ prism_term_diagonal_equality w k hk)

end

theorem Sh_dn : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (w : Cn (box F) (n + 1)), Sh F (n + 1) (dn (box F) (n + 1) w) = prA F (dl 0) (S0 F (n + 1) w) - prA F (dl 1) (S0 F (n + 1) w) - ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) :=
  fun _ _ w ↦ shuffle_coboundary_prism_identity w

end GlobalTheory.CompanionTheory.HopfC.Prism
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleCoboundaryFormulaStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_coboundary_formula : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (w : Cn (box F) (n + 1)), Sh F (n + 1) (dn (box F) (n + 1) w) = prA F (dl 0) (S0 F (n + 1) w) - prA F (dl 1) (S0 F (n + 1) w) - ∑ j : Fin (n + 1 + 1), ((-1 : R) ^ (j : ℕ)) • prB F (dl j) (Sh F n w) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.Prism.Sh_dn | exact GlobalTheory.CompanionTheory.HopfC.Prism.Sh_dn | (intros; apply GlobalTheory.CompanionTheory.HopfC.Prism.Sh_dn <;> assumption)
end
end
