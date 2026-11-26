module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PushComparisonBijectiveOfIsClosedEmbedding
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfAcyclic
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DehomogenisingEqZeroIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGrFreeFiniteAndExactAt
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem cubeComplex_grFree_finite_and_exactAt :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (r : ℕ) (d : Fin r → ℤ),
      (∀ n p, Module.Finite R ((cubeComplex (grCube ι (grFree ι R d) n)).homology p)) ∧
        ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p, (cubeComplex (grCube ι (grFree ι R d) n)).ExactAt p := by
  intro ι _ _ R _ r d
  refine ⟨fun n p => ?_, 1 + ∑ k, |d k|, fun n hn p => ?_⟩
  · have h (k : Fin r) : Module.Finite R
        ((cubeComplex (grCube ι (grShift (polyGrading ι R) (-d k)) n)).homology p) :=
      have : Module.Finite R (((cubeFunctor ι R).obj
          (grCube ι (polyGrading ι R) (n + -d k))).homology p) :=
        (GlobalTheory.T.finite_homology_and_exact_cubeComplex_polyGrading ι R (n + -d k)).1 p
      Module.Finite.equiv (HomologicalComplex.homologyMapIso ((cubeFunctor ι R).mapIso
        (grCubeShiftIso (polyGrading ι R) (-d k) n)) p).toLinearEquiv.symm
    exact Module.Finite.equiv
      (cubeHomologyDirectSumEquiv (fun k => grCube ι (grShift (polyGrading ι R) (-d k)) n) p ≪≫ₗ
        (HomologicalComplex.homologyMapIso ((cubeFunctor ι R).mapIso
          (grCubePiIso ι (fun k => grShift (polyGrading ι R) (-d k)) n)) p).toLinearEquiv.symm)
  · refine (cubeComplex_grPi_exactAt_iff (fun k => grShift (polyGrading ι R) (-d k)) n p).2
      fun k => ?_
    have h₁ : |d k| ≤ ∑ k, |d k| :=
      Finset.single_le_sum (f := fun k => |d k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h₂ := le_abs_self (d k)
    exact (exactAt_iff_of_quasiIsoAt ((cubeFunctor ι R).mapIso
      (grCubeShiftIso (polyGrading ι R) (-d k) n)).hom p).2
      ((GlobalTheory.T.finite_homology_and_exact_cubeComplex_polyGrading ι R (n + -d k)).2 (by omega) p)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

universe w t v u

noncomputable section

namespace GlobalTheory

section Space

open SheafPull SheafLES

attribute [-instance] hasSheafify_topCat hasExt_sheaf_topCat

variable {X Y : TopCat.{u}} [HasExt.{u} (AbSheaf X)] [HasExt.{u} (AbSheaf Y)] (f : Y ⟶ X)
  {F F' : AbSheaf X} {G G' : AbSheaf Y} (φ : F ⟶ (push f).obj G) (n : ℕ)
  {V V' : Opens X} {W W' : Opens Y}

theorem SheafPull.pull_map (s : F' ⟶ F) (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} F' n V) :
    pull.{u, u} f φ n i (map s n V x) = pull.{u, u} f (s ≫ φ) n i x :=
  sitePull_map _ _ _ n _ x

theorem SheafPull.map_pull (s : G ⟶ G') (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} F n V) :
    map s n W (pull.{u, u} f φ n i x) = pull.{u, u} f (φ ≫ (push f).map s) n i x :=
  map_sitePull _ _ _ n _ x

theorem SheafPull.pull_res (k : V' ⟶ V) (i : W ⟶ (Opens.map f).obj V') (x : Sheaf.H'.{u} F n V) :
    pull.{u, u} f φ n i (res F n k x) = pull.{u, u} f φ n (i ≫ (Opens.map f).map k) x :=
  sitePull_res _ _ n _ _ x

theorem SheafPull.equivZero_pull (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} F 0 V) :
    equivZero G W (pull.{u, u} f φ 0 i x) = G.obj.map i.op (φ.hom.app (op V) (equivZero F V x)) :=
  equivZero_sitePull _ _ _ x

theorem SheafPull.pull_δ {A : ShortComplex (AbSheaf X)} {B : ShortComplex (AbSheaf Y)}
    (hA : A.ShortExact) (hB : B.ShortExact) (ψ : A ⟶ B.map (push f))
    (i : W ⟶ (Opens.map f).obj V) (x : Sheaf.H'.{u} A.X₃ n V) :
    pull.{u, u} f (G := B.X₁) ψ.τ₁ (n + 1) i (δ hA n V x) =
      δ hB n W (pull.{u, u} f (G := B.X₃) ψ.τ₃ n i x) :=
  sitePull_δ _ hA hB ψ n i x

end Space

section Morphism

variable {X Y : Scheme.{u}} {g : Y ⟶ X}

theorem smulHom_pushforward (g : Y ⟶ X) (G : Y.Modules) (r : Γ(X, ⊤)) :
    smulHom ((Scheme.Modules.pushforward g).obj G) r =
      (Scheme.Modules.pushforward g).map (smulHom G (g.appTop r)) := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  ext x
  have h : g.app W (restrictGlobal X W r) = restrictGlobal Y (g ⁻¹ᵁ W) (g.appTop r) :=
    ConcreteCategory.congr_hom (g.naturality (homOfLE le_top : W ⟶ ⊤).op) r
  exact congrArg (fun a : Γ(Y, g ⁻¹ᵁ W) => (a • (show Γ(G, g ⁻¹ᵁ W) from x) : Γ(G, g ⁻¹ᵁ W))) h

section Pull

variable {F F' : X.Modules} {G G' : Y.Modules}

def toAbSheafPush (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) :
    (toAbSheaf (X := X)).obj F ⟶ (SheafPull.push g.base).obj ((toAbSheaf (X := Y)).obj G) :=
  (toAbSheaf (X := X)).map φ

theorem toAbSheafPush_comp (s : F' ⟶ F) (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) :
    toAbSheafPush (s ≫ φ) = (toAbSheaf (X := X)).map s ≫ toAbSheafPush φ := rfl

theorem toAbSheafPush_comp_map (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) (s : G ⟶ G') :
    toAbSheafPush (φ ≫ (Scheme.Modules.pushforward g).map s) =
      toAbSheafPush φ ≫ (SheafPull.push g.base).map ((toAbSheaf (X := Y)).map s) := rfl

variable {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)] {S : Type t} [CommRing S]
  [Algebra S Γ(Y, ⊤)] {σ : R →+* S}
  (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))

def cohOn.pull (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) {V : X.Opens} {W : Y.Opens}
    (h : W ≤ g ⁻¹ᵁ V) (n : ℕ) : cohOn F V n →ₛₗ[σ] cohOn G W n where
  toFun x := (cohOn.toH' G W n).symm (SheafPull.pull.{u, u} g.base
    (toAbSheafPush φ) n (homOfLE h) (cohOn.toH' F V n x))
  map_add' x y := by rw [map_add (f := _), map_add (f := _), map_add (f := _)]
  map_smul' r x := by
    have e : smulHom F (algebraMap R Γ(X, ⊤) r) ≫ φ = φ ≫ (Scheme.Modules.pushforward g).map
        (smulHom G (algebraMap S Γ(Y, ⊤) (σ r))) := by
      rw [smulHom_comp, smulHom_pushforward, hσ]
    have h₁ := SheafPull.pull_map g.base (toAbSheafPush φ) n
      ((toAbSheaf (X := X)).map (smulHom F (algebraMap R Γ(X, ⊤) r))) (homOfLE h) (cohOn.toH' F V n x)
    have h₂ := SheafPull.map_pull g.base (toAbSheafPush φ) n
      ((toAbSheaf (X := Y)).map (smulHom G (algebraMap S Γ(Y, ⊤) (σ r)))) (homOfLE h) (cohOn.toH' F V n x)
    rw [← toAbSheafPush_comp, e] at h₁
    rw [← toAbSheafPush_comp_map] at h₂
    apply (cohOn.toH' G W n).injective
    rw [AddEquiv.apply_symm_apply, cohOn.toH'_smul, cohOn.toH'_smul, AddEquiv.apply_symm_apply]
    exact h₁.trans h₂.symm

variable (φ : F ⟶ (Scheme.Modules.pushforward g).obj G) {V V' : X.Opens} {W W' : Y.Opens} {n : ℕ}

theorem cohOn.toH'_pull (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F V n) :
    cohOn.toH' G W n (cohOn.pull hσ φ h n x) =
      SheafPull.pull.{u, u} g.base (toAbSheafPush φ) n (homOfLE h) (cohOn.toH' F V n x) :=
  (cohOn.toH' G W n).apply_symm_apply _

theorem cohOn.pull_map (s : F' ⟶ F) (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F' V n) :
    cohOn.pull hσ φ h n (cohOn.map R s V n x) = cohOn.pull hσ (s ≫ φ) h n x := by
  apply (cohOn.toH' G W n).injective
  rw [cohOn.toH'_pull, cohOn.toH'_pull, cohOn.toH'_map, toAbSheafPush_comp]
  exact SheafPull.pull_map g.base (toAbSheafPush φ) n ((toAbSheaf (X := X)).map s) (homOfLE h) _

theorem cohOn.map_pull (s : G ⟶ G') (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F V n) :
    cohOn.map S s W n (cohOn.pull hσ φ h n x) =
      cohOn.pull hσ (φ ≫ (Scheme.Modules.pushforward g).map s) h n x := by
  apply (cohOn.toH' G' W n).injective
  rw [cohOn.toH'_map, cohOn.toH'_pull, cohOn.toH'_pull, toAbSheafPush_comp_map]
  exact SheafPull.map_pull g.base (toAbSheafPush φ) n ((toAbSheaf (X := Y)).map s) (homOfLE h) _

theorem cohOn.pull_res (k : V' ≤ V) (h : W ≤ g ⁻¹ᵁ V') (x : cohOn F V n) :
    cohOn.pull hσ φ h n (cohOn.res R F k n x) =
      cohOn.pull hσ φ (h.trans (g.preimage_mono k)) n x := by
  apply (cohOn.toH' G W n).injective
  rw [cohOn.toH'_pull, cohOn.toH'_pull, cohOn.toH'_res]
  exact SheafPull.pull_res g.base (toAbSheafPush φ) n (homOfLE k) (homOfLE h) _

theorem cohOn.zeroEquiv_pull (h : W ≤ g ⁻¹ᵁ V) (x : cohOn F V 0) :
    cohOn.zeroEquiv S G W (cohOn.pull hσ φ h 0 x) =
      sectionsOn.res S G h (sectionsOn.mapOver hσ φ V (cohOn.zeroEquiv R F V x)) := by
  apply (sectionsOn.toΓ G W).injective
  rw [cohOn.toΓ_zeroEquiv, cohOn.toH'_pull, sectionsOn.toΓ_res, sectionsOn.toΓ_mapOver,
    cohOn.toΓ_zeroEquiv]
  exact SheafPull.equivZero_pull g.base (toAbSheafPush φ) (homOfLE h) _

theorem cohOn.pull_bijective_of_toAbSheaf (h : W ≤ g ⁻¹ᵁ V)
    (H : Function.Bijective (SheafPull.pull.{u, u} g.base (toAbSheafPush φ) n (homOfLE h))) :
    Function.Bijective (cohOn.pull hσ φ h n) :=
  (cohOn.toH' G W n).symm.bijective.comp (H.comp (cohOn.toH' F V n).bijective)

theorem higherDirectImagesVanish_of_isAffineHom (g : Y ⟶ X) [IsAffineHom g] (G : Y.Modules)
    [G.IsQuasicoherent] :
    SheafPull.HigherDirectImagesVanish.{u} g.base ((toAbSheaf (X := Y)).obj G) :=
  SheafPull.higherDirectImagesVanish_of_basis _ _ fun V x hx => by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
    refine ⟨W, hWV, hxW, fun n hn => ?_⟩
    have := cohOn.subsingleton_of_isAffineOpen G (IsAffineOpen.preimage hW g) hn
    exact (cohOn.toH' G (g ⁻¹ᵁ W) n).symm.injective.subsingleton


variable (G V n) in
theorem cohOn.pull_id_bijective [IsAffineHom g] [G.IsQuasicoherent] :
    Function.Bijective (cohOn.pull hσ (𝟙 ((Scheme.Modules.pushforward g).obj G))
      (le_refl (g ⁻¹ᵁ V)) n) :=
  cohOn.pull_bijective_of_toAbSheaf hσ _ _
    (SheafPull.pushComparison_bijective.{u, u} (higherDirectImagesVanish_of_isAffineHom g G) n V)


variable (F n) in
theorem cohOn.pull_restrict_bijective [IsOpenImmersion g] (h : W ≤ g ⁻¹ᵁ V) (h' : V ≤ g ''ᵁ W) :
    Function.Bijective
      (cohOn.pull hσ (G := F.restrict g) ((Scheme.Modules.restrictAdjunction g).unit.app F) h n) :=
  cohOn.pull_bijective_of_toAbSheaf hσ _ _
    (SheafPull.pull_restrUnit_bijective.{u, u} g.isOpenEmbedding ((toAbSheaf (X := X)).obj F) n
      (homOfLE h) h')

end Pull

section Linear

variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)] [Algebra R Γ(Y, ⊤)]
  (hg : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r)

section Push

variable [IsAffineHom g] (G : Y.Modules) [G.IsQuasicoherent]

def cohOn.pushforwardEquiv (V : X.Opens) (n : ℕ) :
    cohOn ((Scheme.Modules.pushforward g).obj G) V n ≃ₗ[R] cohOn G (g ⁻¹ᵁ V) n :=
  LinearEquiv.ofBijective _ (cohOn.pull_id_bijective (G := G) (σ := RingHom.id R) (V := V) (n := n) hg)

theorem cohOn.pushforwardEquiv_apply (V : X.Opens) (n : ℕ)
    (x : cohOn ((Scheme.Modules.pushforward g).obj G) V n) :
    cohOn.pushforwardEquiv R hg G V n x =
      cohOn.pull (σ := RingHom.id R) hg (𝟙 _) (le_refl (g ⁻¹ᵁ V)) n x := rfl


variable {G} in
theorem cohOn.pushforwardEquiv_map {G' : Y.Modules} [G'.IsQuasicoherent] (s : G ⟶ G')
    (V : X.Opens) (n : ℕ) (x : cohOn ((Scheme.Modules.pushforward g).obj G) V n) :
    cohOn.pushforwardEquiv R hg G' V n
        (cohOn.map R ((Scheme.Modules.pushforward g).map s) V n x) =
      cohOn.map R s (g ⁻¹ᵁ V) n (cohOn.pushforwardEquiv R hg G V n x) := by
  rw [cohOn.pushforwardEquiv_apply, cohOn.pushforwardEquiv_apply, cohOn.pull_map, cohOn.map_pull,
    Category.comp_id, Category.id_comp]

theorem cohOn.zeroEquiv_pushforwardEquiv (V : X.Opens)
    (x : cohOn ((Scheme.Modules.pushforward g).obj G) V 0) :
    sectionsOn.toΓ G (g ⁻¹ᵁ V) (cohOn.zeroEquiv R G _ (cohOn.pushforwardEquiv R hg G V 0 x)) =
      sectionsOn.toΓ _ V (cohOn.zeroEquiv R _ V x) := by
  rw [cohOn.pushforwardEquiv_apply, cohOn.zeroEquiv_pull, sectionsOn.res_refl]
  rfl

def coh.pushforwardEquiv (n : ℕ) :
    coh ((Scheme.Modules.pushforward g).obj G) n ≃ₗ[R] coh G n :=
  cohOn.pushforwardEquiv R hg G ⊤ n


variable {G} in
theorem coh.pushforwardEquiv_map {G' : Y.Modules} [G'.IsQuasicoherent] (s : G ⟶ G')
    (n : ℕ) (x : coh ((Scheme.Modules.pushforward g).obj G) n) :
    coh.pushforwardEquiv R hg G' n (cohOn.map R ((Scheme.Modules.pushforward g).map s) ⊤ n x) =
      cohOn.map R s ⊤ n (coh.pushforwardEquiv R hg G n x) :=
  cohOn.pushforwardEquiv_map R hg s ⊤ n x

end Push

section Restrict

variable [IsOpenImmersion g] (F : X.Modules)

def cohOn.restrictEquiv {V : X.Opens} {W : Y.Opens} (h : g ''ᵁ W = V) (n : ℕ) :
    cohOn F V n ≃ₗ[R] cohOn (F.restrict g) W n :=
  LinearEquiv.ofBijective _ (cohOn.pull_restrict_bijective (F := F) (σ := RingHom.id R) (n := n) hg
    ((g.preimage_image_eq W).ge.trans (g.preimage_mono h.le)) h.ge)

end Restrict

end Linear

theorem hdim_pushforward (k : Type v) [Field k] [Algebra k Γ(X, ⊤)] [Algebra k Γ(Y, ⊤)]
    (hg : ∀ r, g.appTop (algebraMap k Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) r) [IsAffineHom g]
    (G : Y.Modules) [G.IsQuasicoherent] (n : ℕ) :
    hdim k ((Scheme.Modules.pushforward g).obj G) n = hdim k G n :=
  (coh.pushforwardEquiv k hg G n).finrank_eq

theorem appTop_algebraΓOfHom {R : Type u} [CommRing R] (g : Y ⟶ X) (p : X ⟶ Spec (.of R))
    {q : Y ⟶ Spec (.of R)} (w : g ≫ p = q) (r : R) :
    letI := algebraΓOfHom p
    letI := algebraΓOfHom q
    g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r := by
  subst w
  simp only [algebraΓOfHom_algebraMap, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]

end Morphism

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exactAt_quot_of_shortExact {R : Type} [CommRing R]
    {S : ShortComplex (CochainComplex (ModuleCat.{0} R) ℕ)} (hS : S.ShortExact) (p : ℕ)
    (h₂ : S.X₂.ExactAt p) (h₁ : S.X₁.ExactAt (p + 1)) : S.X₃.ExactAt p := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h₁ h₂ ⊢
  exact (hS.homology_exact₃ p (p + 1) rfl).isZero_X₂ (h₂.eq_of_src _ _) (h₁.eq_of_tgt _ _)

theorem cubeComplex_grCube_exactAt_of_card_lt (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] [IsNoetherianRing R] (q : ℕ) :
    ∀ (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p, Fintype.card ι < p + q →
        (cubeComplex (grCube ι ℳ n)).ExactAt p := by
  induction q with
  | zero =>
    intro M _ _ _ _ ℳ _ _ _
    exact ⟨0, fun n _ p hp => (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_cubeComplex_homology _ hp)⟩
  | succ q ih =>
    intro M _ _ _ _ ℳ _ _ _
    obtain ⟨r, d, f, hf, hs⟩ := exists_graded_surjection (ι := ι) ℳ
    letI : Decomposition (grSub (grFree ι R d) (LinearMap.ker f)) :=
      grSubDecomposition _ hf.isHomogeneous_ker
    obtain ⟨a, ha⟩ := ih (LinearMap.ker f) (grSub (grFree ι R d) (LinearMap.ker f)) inferInstance
    obtain ⟨b, hb⟩ := (cubeComplex_grFree_finite_and_exactAt ι R r d).2
    refine ⟨max a b, fun n hn p hp => ?_⟩
    exact exactAt_quot_of_shortExact ((hf.shortExact_ker hs).cubeComplex_shortExact n) p
      (hb n (le_of_max_le_right hn) p) (ha n (le_of_max_le_left hn) (p + 1) (by omega))

theorem cubeComplex_grCube_exactAt_of_finite :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R]
      (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p, (cubeComplex (grCube ι ℳ n)).ExactAt p := by
  intro ι _ _ R _ _ M _ _ _ _ ℳ _ _ hM
  obtain ⟨n₀, h⟩ := cubeComplex_grCube_exactAt_of_card_lt ι R (Fintype.card ι + 1) M ℳ hM
  exact ⟨n₀, fun n hn p => h n hn p (by omega)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegreeStatement
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeComplex_gradedModule_exactAt_of_large_degree : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ p, (cubeComplex (grCube ι ℳ n)).ExactAt p := by
  first | exact @GlobalTheory.cubeComplex_grCube_exactAt_of_finite | exact GlobalTheory.cubeComplex_grCube_exactAt_of_finite | (intros; apply GlobalTheory.cubeComplex_grCube_exactAt_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteGrCechHomology
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteHomologyCubeComplexGradedModule
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteHomologyCubeComplexGradedModule
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

private theorem finite_of_exact_of_finite {R A B C : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : Function.Exact f g) (hA : Module.Finite R A)
    (hC : Module.Finite R C) : Module.Finite R B :=
  have := isNoetherian_of_range_eq_ker f g h.linearMap_ker_eq.symm
  inferInstance

theorem finite_cubeComplex_grCube_homology :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R]
      (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∀ n p, Module.Finite R ((cubeComplex (grCube ι ℳ n)).homology p) := by
  intro ι _ _ R _ _
  suffices key : ∀ (j p : ℕ), Fintype.card ι < p + j →
      ∀ (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
      [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
      [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∀ n, Module.Finite R ((cubeComplex (grCube ι ℳ n)).homology p) by
    intro M _ _ _ _ ℳ _ _ hM n p
    exact key (Fintype.card ι + 1) p (by omega) M ℳ hM n
  intro j
  induction j with
  | zero =>
    intro p hp M _ _ _ _ ℳ _ _ _ n
    have := ModuleCat.subsingleton_of_isZero
      (isZero_cubeComplex_homology (grCube ι ℳ n) (p := p) hp)
    infer_instance
  | succ j ih =>
    intro p hp M _ _ _ _ ℳ _ _ hM n
    obtain ⟨r, d, g, hg, hs⟩ := exists_graded_surjection (ι := ι) ℳ
    let _ := grSubDecomposition (grFree ι R d) hg.isHomogeneous_ker
    have hK := ih (p + 1) (by omega) _ (grSub (grFree ι R d) (LinearMap.ker g)) inferInstance n
    have hF := (cubeComplex_grFree_finite_and_exactAt ι R r d).1 n p
    have hse := (hg.shortExact_ker hs).cubeComplex_shortExact n
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hse.homology_exact₃ p (p + 1) rfl)
    exact finite_of_exact_of_finite hex hF hK

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteHomologyCubeComplexGradedModuleStatement
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_homology_cubeComplex_gradedModule : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∀ n p, Module.Finite R ((cubeComplex (grCube ι ℳ n)).homology p) := by
  first | exact @GlobalTheory.finite_cubeComplex_grCube_homology | exact GlobalTheory.finite_cubeComplex_grCube_homology | (intros; apply GlobalTheory.finite_cubeComplex_grCube_homology <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteCechHomologyOfFiniteCubeHomology
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem finite_cycles_of_finite_homology {R : Type} [Ring R] {α : Type} {c : ComplexShape α}
    (K : HomologicalComplex (ModuleCat.{0} R) c) (i j : α) (hij : c.prev j = i)
    [Module.Finite R (K.X i)] [Module.Finite R (K.homology j)] :
    Module.Finite R (K.cycles j) := by
  have hex : (ShortComplex.mk (K.toCycles i j) (K.homologyπ j)
      (K.toCycles_comp_homologyπ i j)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel i j hij)
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hex
  exact Module.Finite.of_exact hex
    ((ModuleCat.epi_iff_surjective (K.homologyπ j)).1 inferInstance)

theorem finite_cechHomology_of_finite_cubeHomology (ι : Type) [LinearOrder ι] (R : Type)
    [CommRing R] [IsNoetherianRing R] (A : Cube.{0} ι R) (h₀ : Module.Finite R (A.obj ∅))
    (h : ∀ p, Module.Finite R ((cubeComplex A).homology p)) (p : ℕ) :
    Module.Finite R ((cechComplex A).homology p) := by
  cases p with
  | zero =>
    have h1 := h 1
    have h2 : Module.Finite R ((cubeComplex A).X 0) :=
      Module.Finite.equiv (Cube.termZeroEquiv A).symm
    have h3 := finite_cycles_of_finite_homology (cubeComplex A) 0 1 (by simp)
    exact Module.Finite.equiv
      (cubeCyclesIso A 1 ≪≫ (cechHomologyZeroIso A).symm).toLinearEquiv
  | succ p =>
    have h1 := h (p + 2)
    exact Module.Finite.equiv (cechHomologySuccIso A p).symm.toLinearEquiv

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinitePieceOfPolyGradedSMul
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem finite_piece_of_polyGradedSMul : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∀ n, Module.Finite R (ℳ n) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ _ n
  refine GradedHilbert.finite_piece (ι := ι) ℳ (fun i k m hm => ?_) n
  have := grSMul_mem ℳ (X_mem_polyGrading i) hm
  first
    | exact this
    | exact add_comm k 1 ▸ this
    | simpa [add_comm] using this

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem finite_grCech_homology : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R]
    [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M →
      ∀ n p, Module.Finite R ((cechComplex (grCube ι ℳ n)).homology p) := by
  intro ι _ _ R _ _ M _ _ _ _ ℳ _ _ hM n p
  have h₀ : Module.Finite R (ℳ n) := finite_piece_of_polyGradedSMul ι R M ℳ hM n
  have h₁ : Module.Finite R ((grCube ι ℳ n).obj ∅) :=
    Module.Finite.equiv (homLocEmptyEquiv ι ℳ n)
  exact finite_cechHomology_of_finite_cubeHomology ι R (grCube ι ℳ n) h₁
    (GlobalTheory.T.finite_homology_cubeComplex_gradedModule ι R M ℳ hM n) p

end GlobalTheory
end
