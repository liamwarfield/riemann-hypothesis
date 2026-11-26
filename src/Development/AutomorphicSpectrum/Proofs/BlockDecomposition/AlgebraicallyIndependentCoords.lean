module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalZeroOfMemHomogeneousIdeal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicallyIndependentCoords
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicallyIndependentCoords
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoAlgInd

open MvPolynomial

def shiftE {d : ℕ} (D : ℕ) (α : Fin d →₀ ℕ) : Fin (d + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons (D - α.degree) α : Fin (d + 1) → ℕ)

theorem shiftE_zero {d : ℕ} (D : ℕ) (α : Fin d →₀ ℕ) : shiftE D α 0 = D - α.degree := rfl

theorem shiftE_succ {d : ℕ} (D : ℕ) (α : Fin d →₀ ℕ) (k : Fin d) : shiftE D α k.succ = α k := rfl

def homogP {K : Type} [Field K] {d : ℕ} (D : ℕ) (P : MvPolynomial (Fin d) K) : MvPolynomial (Fin (d + 1)) K :=
  ∑ α ∈ P.support, monomial (shiftE D α) (AddMonoidAlgebra.coeff P α)

theorem degree_le_of_mem {K : Type} [Field K] {d D : ℕ} {P : MvPolynomial (Fin d) K} (hD : P.totalDegree ≤ D)
    {α : Fin d →₀ ℕ} (hα : α ∈ P.support) : α.degree ≤ D := by
  have h := le_totalDegree hα
  rw [Finsupp.sum_fintype _ _ (by simp)] at h
  rw [Finsupp.degree_eq_sum]
  exact h.trans hD

theorem homogenize_isHomogeneous₂ {K : Type} [Field K] {d D : ℕ} {P : MvPolynomial (Fin d) K} (hD : P.totalDegree ≤ D) :
    (homogP D P).IsHomogeneous D := by
  refine IsHomogeneous.sum _ _ _ fun α hα => isHomogeneous_monomial _ ?_
  have h := degree_le_of_mem hD hα
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_succ, shiftE_zero]
  simp only [shiftE_succ]
  rw [← Finsupp.degree_eq_sum]
  omega

theorem aeval_homogP {K : Type} [Field K] {d D : ℕ} {P : MvPolynomial (Fin d) K} (hD : P.totalDegree ≤ D)
    {R : Type} [CommRing R] [Algebra K R] (u : R) (t : Fin d → R) :
    aeval (Fin.cons u (fun k => u * t k) : Fin (d + 1) → R) (homogP D P) = u ^ D * aeval t P := by
  conv_rhs => rw [← support_sum_monomial_coeff P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [homogP, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have h := degree_le_of_mem hD hα
  rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
    Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, shiftE_zero, shiftE_succ, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← Finsupp.degree_eq_sum]
  have e : u ^ D = u ^ (D - α.degree) * u ^ α.degree := by rw [← pow_add]; congr 1; omega
  rw [e]; ring

section Scalars

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem map_map_apply {Y : Scheme.{0}} {A B C : Y.Opens} (f : Opposite.op C ⟶ Opposite.op B)
    (g : Opposite.op B ⟶ Opposite.op A) (s : Γ(Y, C)) :
    Y.presheaf.map g (Y.presheaf.map f s) = Y.presheaf.map (f ≫ g) s := by
  rw [Functor.map_comp, CommRingCat.comp_apply]

theorem ι_appTop_toZero (z : 𝒜 0) :
    (Proj.basicOpen 𝒜 1).ι.appTop ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) =
      (Proj.basicOpen 𝒜 1).topIso.inv
        (Proj.awayToSection 𝒜 1 (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z)) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  have h1 : (Proj.basicOpen 𝒜 1).ι ≫ (Proj 𝒜).topIso.inv ≫
      ((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv = 𝟙 _ := by
    rw [← cancel_mono (Proj.basicOpen 𝒜 1).ι]
    simp
  have h : (Proj.basicOpen 𝒜 1).ι ≫ Proj.toSpecZero 𝒜 = Proj.basicOpenToSpec 𝒜 1 ≫
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 _)) := by
    rw [Proj.toSpecZero, reassoc_of% h1]
  rw [h, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, Scheme.Hom.appTop, Proj.basicOpenToSpec_app_top]
  simp

theorem awayToSection_one_zero (z : 𝒜 0) :
    Proj.awayToSection 𝒜 1 (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z) =
      (Proj 𝒜).presheaf.map (homOfLE le_top).op
        ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) := by
  have h := congrArg (fun s => (Proj.basicOpen 𝒜 1).topIso.hom s) (ι_appTop_toZero 𝒜 z)
  simp only [CategoryTheory.Iso.inv_hom_id_apply] at h
  rw [← h, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact map_map_apply _ _ _

theorem awayToSection_zero {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) (z : 𝒜 0) :
    Proj.awayToSection 𝒜 f (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z) =
      (Proj 𝒜).presheaf.map (homOfLE le_top).op
        ((Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso _).inv z)) := by
  have h := congrArg (fun φ => φ.hom (HomogeneousLocalization.fromZeroRingHom 𝒜 _ z))
    (Proj.awayMap_awayToSection 𝒜 hf (one_mul f).symm)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    HomogeneousLocalization.awayMap_fromZeroRingHom] at h
  rw [h, awayToSection_one_zero, map_map_apply]
  rfl

end Scalars

abbrev cst {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin (N + 1)) K) :
    K →+* HomogeneousLocalization.Away (grK K N) g :=
  (HomogeneousLocalization.fromZeroRingHom (grK K N) _).comp (algebraMap K (grK K N 0))

theorem evV_cst {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    (q : X ⟶ Spec (CommRingCat.of K)) (hq : i ≫ PSpace.str K N = q) {g : MvPolynomial (Fin (N + 1)) K} {m : ℕ}
    (hg : g ∈ grK K N m) (V : X.Opens) (h : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (a : K) :
    evV i g V h (cst g a) = strV q V a := by
  subst hq
  simp only [evV, cst, RingHom.comp_apply]
  rw [awayToSection_zero _ hg]
  have e1 : (i ≫ PSpace.str K N).appLE ⊤ V le_top =
      (spMap (algebraMap K (grK K N 0))).appTop ≫ (Proj.toSpecZero (grK K N)).appTop ≫ i.appLE ⊤ V le_top := by
    rw [PSpace.str, ← Scheme.Hom.comp_appTop_assoc]
    exact (Scheme.Hom.appLE_comp_appLE i _ ⊤ ⊤ V (by simp) le_top).symm
  have e2 : (Proj (grK K N)).presheaf.map (homOfLE (le_top : Proj.basicOpen (grK K N) g ≤ ⊤)).op ≫
      i.appLE _ V h = i.appLE ⊤ V le_top := Scheme.Hom.map_appLE _ _ _
  have key : CommRingCat.ofHom (algebraMap K (grK K N 0)) ≫ (Scheme.ΓSpecIso _).inv ≫
      (Proj.toSpecZero (grK K N)).appTop ≫ (Proj (grK K N)).presheaf.map (homOfLE le_top).op ≫ i.appLE _ V h =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (i ≫ PSpace.str K N).appLE ⊤ V le_top := by
    rw [e2, e1, ← Category.assoc, ← Category.assoc (Scheme.ΓSpecIso _).inv, Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (fun φ => φ.hom a) key

def tau {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (k : Fin d) : HomogeneousLocalization.Away (grK K N) (y 0) :=
  HomogeneousLocalization.Away.mk _ ((mem_homogeneousSubmodule e (y 0)).2 (hy 0)) 1 (y k.succ)
    (by simpa using (mem_homogeneousSubmodule e (y k.succ)).2 (hy k.succ))

def tauL {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (k : Fin d) : Localization (Submonoid.powers (y 0)) :=
  (tau y hy k).val

theorem val_cst {K : Type} [Field K] {N : ℕ} (g : MvPolynomial (Fin (N + 1)) K) (a : K) :
    (cst g a).val = algebraMap K (Localization (Submonoid.powers g)) a := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers g)),
    ← Localization.mk_one_eq_algebraMap]
  exact HomogeneousLocalization.val_mk _

theorem val_mul {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {f a : A} {m : ℕ} (hf : f ∈ 𝒜 m) (ha : a ∈ 𝒜 (1 • m)) :
    algebraMap A (Localization (Submonoid.powers f)) a =
      algebraMap A (Localization (Submonoid.powers f)) f * (HomogeneousLocalization.Away.mk 𝒜 hf 1 a ha).val := by
  have h : (HomogeneousLocalization.Away.mk 𝒜 hf 1 a ha).val * algebraMap A (Localization (Submonoid.powers f)) (f ^ 1) =
      algebraMap A (Localization (Submonoid.powers f)) a := by
    rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ _ _
  rw [pow_one] at h
  rw [← h, mul_comm]

theorem val_eval {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (Q : MvPolynomial (Fin d) K) :
    (eval₂Hom (cst (y 0)) (tau y hy) Q).val =
      aeval (tauL y hy) Q := by
  have h : (algebraMap (HomogeneousLocalization.Away (grK K N) (y 0)) (Localization (Submonoid.powers (y 0)))).comp
      (eval₂Hom (cst (y 0)) (tau y hy)) =
      (aeval (tauL y hy)).toRingHom := by
    refine ringHom_ext (fun a => ?_) (fun k => ?_)
    · simp only [RingHom.comp_apply, eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
      exact val_cst (y 0) a
    · simp only [RingHom.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      rfl
  exact RingHom.congr_fun h Q

theorem away_key {K : Type} [Field K] {N e d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K)
    (hy : ∀ k, (y k).IsHomogeneous e) (P : MvPolynomial (Fin d) K) {D : ℕ} (hD : P.totalDegree ≤ D)
    (hf : aeval y (homogP D P) ∈ grK K N (D • e)) :
    HomogeneousLocalization.Away.mk (grK K N) ((mem_homogeneousSubmodule e (y 0)).2 (hy 0)) D
      (aeval y (homogP D P)) hf = eval₂Hom (cst (y 0)) (tau y hy) P := by
  apply HomogeneousLocalization.val_injective
  have hc : (algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) ∘ y : Fin (d + 1) → _) =
      (Fin.cons (algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) (y 0)) (fun k => algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) (y 0) * tauL y hy k) : Fin (d + 1) → _) :=
    funext (Fin.cases rfl fun k => val_mul (grK K N) _ _)
  have h1 : algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) (aeval y (homogP D P)) =
      algebraMap (MvPolynomial (Fin (N + 1)) K) (Localization (Submonoid.powers (y 0))) (y 0) ^ D * aeval (tauL y hy) P := by
    rw [← aeval_homogP hD, ← hc, aeval_algebraMap_apply]
  rw [HomogeneousLocalization.Away.val_mk, val_eval, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul, h1,
    map_pow, mul_comm]

theorem algebraicIndependent_tV : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), IsIntegral X → 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → (AlgebraicIndependent K fun k => Ideal.Quotient.mk (homIdeal i) (y k)) → (V : Set X).Nonempty → letI := (strV q V).toAlgebra; AlgebraicIndependent K (tV i y hy V hV) := by
  intro K _ X N d e i y hy V hV hX he q hq hind hne
  letI := (strV q V).toAlgebra
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro P hP
  have h0 : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0) :=
    hV.trans (iInf_le (fun k => i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) 0)
  have hy0 : y 0 ∈ grK K N e := (mem_homogeneousSubmodule e (y 0)).2 (hy 0)
  have hFh : (homogP P.totalDegree P).IsHomogeneous P.totalDegree := homogenize_isHomogeneous₂ le_rfl
  have hf : aeval y (homogP P.totalDegree P) ∈ grK K N (P.totalDegree • e) := by
    rw [mem_homogeneousSubmodule, smul_eq_mul, mul_comm]
    exact hFh.aeval y hy
  have hev : evV i (y 0) V h0 (HomogeneousLocalization.Away.mk (grK K N) hy0 P.totalDegree
      (aeval y (homogP P.totalDegree P)) hf) = 0 := by
    rw [away_key y hy P le_rfl hf]
    have h : (evV i (y 0) V h0).comp (eval₂Hom (cst (y 0)) (tau y hy)) =
        (aeval (tV i y hy V hV) : MvPolynomial (Fin d) K →ₐ[K] Γ(X, V)).toRingHom := by
      refine ringHom_ext (fun a => ?_) (fun k => ?_)
      · simp only [RingHom.comp_apply, eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
        exact evV_cst i q hq hy0 V h0 a
      · simp only [RingHom.comp_apply, eval₂Hom_X', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        rfl
    exact (RingHom.congr_fun h P).trans hP
  have hmem : aeval y (homogP P.totalDegree P) ∈ homIdeal i :=
    GlobalTheory.CompanionTheory.GeoVan.mem_homIdeal_of_vanish i hX he hy0 hf V hne h0 hev
  have hz : aeval (fun k => Ideal.Quotient.mk (homIdeal i) (y k)) (homogP P.totalDegree P) = 0 := by
    have h := aeval_algebraMap_apply (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) y (homogP P.totalDegree P)
    exact h.trans (Ideal.Quotient.eq_zero_iff_mem.2 hmem)
  have hF : homogP P.totalDegree P = 0 :=
    (injective_iff_map_eq_zero _).1 ((algebraicIndependent_iff_injective_aeval).1 hind) _ hz
  have h := aeval_homogP (le_refl P.totalDegree) (1 : MvPolynomial (Fin d) K) MvPolynomial.X
  rw [hF] at h
  simpa using h.symm

end GlobalTheory.CompanionTheory.GeoAlgInd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicallyIndependentCoordsStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraically_independent_coords : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N) (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens} (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)), IsIntegral X → 0 < e → ∀ (q : X ⟶ Spec (CommRingCat.of K)), i ≫ PSpace.str K N = q → (AlgebraicIndependent K fun k => Ideal.Quotient.mk (homIdeal i) (y k)) → (V : Set X).Nonempty → letI := (strV q V).toAlgebra; AlgebraicIndependent K (tV i y hy V hV) := by
  first | exact @GlobalTheory.CompanionTheory.GeoAlgInd.algebraicIndependent_tV | exact GlobalTheory.CompanionTheory.GeoAlgInd.algebraicIndependent_tV | (intros; apply GlobalTheory.CompanionTheory.GeoAlgInd.algebraicIndependent_tV <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NerveCechDegreeZeroCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NerveCechDegreeZeroCompatible
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero

variable {R : Type} [CommRing R]

section Chains

variable {C : Type} [Category.{0} C]

abbrev pt (a : C) : Fin (0 + 1) ⥤ C := (Functor.const _).obj a

theorem exists_pt (c : Fin (0 + 1) ⥤ C) : ∃ a, c = pt a := by
  have hX : ∀ X : Fin (0 + 1), X = 0 := fun X => Fin.ext (by have := X.isLt; simp only [Fin.val_zero]; omega)
  have hobj : ∀ X, c.obj X = (pt (c.obj 0)).obj X := fun X => congrArg c.obj (hX X)
  refine ⟨c.obj 0, CategoryTheory.Functor.ext hobj (fun X Y f => ?_)⟩
  obtain rfl := hX X
  obtain rfl := hX Y
  obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
  simp

theorem eval_chain (G : C ⥤ ModuleCat.{0} R) (x : NC G 0) (c : Fin (0 + 1) ⥤ C) :
    x c = x (pt (c.obj (Fin.last 0))) := by
  obtain ⟨a, rfl⟩ := exists_pt c
  rfl

theorem pull_last (G : C ⥤ ModuleCat.{0} R) (x : NC G 0) (c : Fin (0 + 1 + 1) ⥤ C) :
    pullNC G (Fin.succAboveOrderEmb (0 : Fin (0 + 2))).toOrderHom x c = x (pt (c.obj (Fin.last (0 + 1)))) := by
  rw [pullNC_apply]
  show (G.map (c.map (homOfLE (le_refl (Fin.last (0 + 1)))))).hom
    (x ((Fin.succAboveOrderEmb (0 : Fin (0 + 2))).toOrderHom.monotone.functor ⋙ c)) = _
  rw [show homOfLE (le_refl (Fin.last (0 + 1))) = 𝟙 (Fin.last (0 + 1) : Fin (0 + 1 + 1)) from
    Subsingleton.elim _ _, c.map_id, G.map_id]
  exact eval_chain G x _

theorem pull_first (G : C ⥤ ModuleCat.{0} R) (x : NC G 0) (c : Fin (0 + 1 + 1) ⥤ C) :
    pullNC G (Fin.succAboveOrderEmb (1 : Fin (0 + 2))).toOrderHom x c =
      (G.map (c.map (homOfLE (Fin.le_last 0)))).hom (x (pt (c.obj 0))) := by
  rw [pullNC_apply]
  exact congrArg (G.map (c.map (homOfLE (Fin.le_last 0)))).hom (eval_chain G x _)

theorem dNC_zero_apply (G : C ⥤ ModuleCat.{0} R) (x : NC G 0) (c : Fin (0 + 1 + 1) ⥤ C) :
    dNC G 0 x c = (show G.obj (c.obj (Fin.last (0 + 1))) from x (pt (c.obj (Fin.last (0 + 1))))) -
      (G.map (c.map (homOfLE (Fin.le_last 0)))).hom (x (pt (c.obj 0))) := by
  have hsum : dNC G 0 x c = pullNC G (Fin.succAboveOrderEmb (0 : Fin (0 + 2))).toOrderHom x c -
      pullNC G (Fin.succAboveOrderEmb (1 : Fin (0 + 2))).toOrderHom x c := by
    simp only [dNC, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply]
    show ∑ i : Fin 2, (-1 : R) ^ (i : ℕ) • (pullNC G (Fin.succAboveOrderEmb i).toOrderHom) x c = _
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul, sub_eq_add_neg] <;> rfl
  rw [hsum, pull_last, pull_first] <;> rfl

end Chains

section Semilattice

variable {P : Type} [SemilatticeInf P] {κ : Type} (e : κ → P) (G : Pᵒᵖ ⥤ ModuleCat.{0} R)

def epsLin : NC G 0 →ₗ[R] Cube.Term (cubeOf e G) 1 where
  toFun x s hs := x (pt (op (s.1.inf' hs.down e)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev val (x : NC G 0) (a : P) : G.obj (op a) := x (pt (op a))

def Compat (x : NC G 0) : Prop :=
  ∀ ⦃a b : P⦄ (h : b ≤ a), val G x b = (G.map (homOfLE h).op).hom (val G x a)

theorem dNC_zero_iff (x : NC G 0) : dNC G 0 x = 0 ↔ Compat G x := by
  constructor
  · intro hx a b h
    have h1 := congrFun hx (ComposableArrows.mk₁ (homOfLE h).op)
    have hm : (ComposableArrows.mk₁ (homOfLE h).op).map (homOfLE (Fin.le_last (0 : Fin (0 + 1 + 1)))) =
        (homOfLE h).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [dNC_zero_apply, Pi.zero_apply, sub_eq_zero, hm] at h1
    exact h1
  · intro hc
    funext c
    rw [dNC_zero_apply, Pi.zero_apply, sub_eq_zero]
    have h : (c.obj (Fin.last (0 + 1))).unop ≤ (c.obj 0).unop := leOfHom (c.map (homOfLE (Fin.le_last 0))).unop
    have hm : c.map (homOfLE (Fin.le_last 0)) = (homOfLE h).op := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [hm]
    exact hc h

theorem epsLin_injective (he : Function.Surjective e) : Function.Injective (epsLin e G) := by
  intro x y hxy
  funext c
  rw [eval_chain G x c, eval_chain G y c]
  obtain ⟨k, hk⟩ := he (c.obj (Fin.last 0)).unop
  have h1 : x (pt (op (({k} : Finset κ).inf' (Finset.singleton_nonempty k) e))) =
      y (pt (op (({k} : Finset κ).inf' (Finset.singleton_nonempty k) e))) :=
    congrFun (congrFun hxy ⟨{k}, Finset.card_singleton k⟩) ⟨Finset.singleton_nonempty k⟩
  rw [Finset.inf'_singleton, hk] at h1
  exact h1

private theorem map_eqToHom_singleton_eq (z : Cube.Term (cubeOf e G) 1) {k' k : κ} (h : k' = k)
    (pr : op (({k'} : Finset κ).inf' (Finset.singleton_nonempty k') e) =
      op (({k} : Finset κ).inf' (Finset.singleton_nonempty k) e)) :
    (G.map (eqToHom pr)).hom (z ⟨{k'}, Finset.card_singleton k'⟩ ⟨Finset.singleton_nonempty k'⟩) =
      z ⟨{k}, Finset.card_singleton k⟩ ⟨Finset.singleton_nonempty k⟩ := by
  subst h
  rw [eqToHom_refl, G.map_id] <;> rfl

theorem epsLin_surjective (he : Function.Injective e) (he' : Function.Surjective e) :
    Function.Surjective (epsLin e G) := by
  intro z
  choose f hf using he'
  have hop : ∀ p : P, op (({f p} : Finset κ).inf' (Finset.singleton_nonempty (f p)) e) = op p := by
    intro p
    rw [Finset.inf'_singleton, hf]
  refine ⟨fun c => (G.map (eqToHom (hop (c.obj (Fin.last 0)).unop))).hom
      (z ⟨{f (c.obj (Fin.last 0)).unop}, Finset.card_singleton _⟩ ⟨Finset.singleton_nonempty _⟩), ?_⟩
  funext s hs
  obtain ⟨s, hs1⟩ := s
  obtain ⟨k, rfl⟩ := Finset.card_eq_one.mp hs1
  have hk : f (({k} : Finset κ).inf' hs.down e) = k := by
    apply he
    rw [hf, Finset.inf'_singleton]
  exact map_eqToHom_singleton_eq e G z hk _

theorem d_pair (x : NC G 0) {κ : Type} [LinearOrder κ] (e : κ → P) {i j : κ} (hij : i < j)
    (hp : ({i, j} : Finset κ).Nonempty)
    (h1 : ({i, j} : Finset κ).inf' hp e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e)
    (h2 : ({i, j} : Finset κ).inf' hp e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e) :
    Cube.d (cubeOf e G) 1 (epsLin e G x) ⟨{i, j}, Finset.card_pair hij.ne⟩ ⟨hp⟩ =
      (G.map (homOfLE h1).op).hom (val G x _) - (G.map (homOfLE h2).op).hom (val G x _) := by
  erw [GlobalTheory.Cube.d_one_apply_pair (cubeOf e G) (epsLin e G x) hij, Pi.sub_apply]
  exact congrArg₂ (· - ·)
    (cubeRes_apply e G (by simp : ({j} : Finset κ) ⊆ {i, j}) (epsLin e G x ⟨{j}, Finset.card_singleton j⟩)
      (Finset.singleton_nonempty j) ⟨hp⟩)
    (cubeRes_apply e G (by simp : ({i} : Finset κ) ⊆ {i, j}) (epsLin e G x ⟨{i}, Finset.card_singleton i⟩)
      (Finset.singleton_nonempty i) ⟨hp⟩)

theorem step (x : NC G 0) {a a' b b' m : P} (ha : a' = a) (hb : b' = b) (hm : m = b) (h : b ≤ a)
    (h1 : m ≤ a') (h2 : m ≤ b')
    (E : (G.map (homOfLE h1).op).hom (val G x a') = (G.map (homOfLE h2).op).hom (val G x b')) :
    val G x b = (G.map (homOfLE h).op).hom (val G x a) := by
  subst ha hb hm
  have e2 : homOfLE h2 = 𝟙 _ := Subsingleton.elim _ _
  rw [e2, op_id, G.map_id] at E
  exact E.symm

theorem d_eps_zero_iff {κ : Type} [LinearOrder κ] (e : κ → P) (he : Function.Surjective e) (x : NC G 0) :
    Cube.d (cubeOf e G) 1 (epsLin e G x) = 0 ↔ Compat G x := by
  constructor
  · intro hd a b h
    obtain ⟨i, rfl⟩ := he a
    obtain ⟨j, rfl⟩ := he b
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hp : ({i, j} : Finset κ).Nonempty := Finset.insert_nonempty _ _
      have h1 : ({i, j} : Finset κ).inf' hp e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e :=
        Finset.inf'_mono e (by simp) _
      have h2 : ({i, j} : Finset κ).inf' hp e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e :=
        Finset.inf'_mono e (by simp) _
      have E0 : Cube.d (cubeOf e G) 1 (epsLin e G x) ⟨{i, j}, Finset.card_pair hij.ne⟩ ⟨hp⟩ = 0 := by
        rw [hd] <;> rfl
      rw [d_pair G x e hij hp h1 h2, sub_eq_zero] at E0
      exact step G x (by simp) (by simp) (by simp [Finset.inf'_insert, inf_eq_right.mpr h]) h h2 h1 E0.symm
    · have e2 : homOfLE h = 𝟙 _ := Subsingleton.elim _ _
      rw [e2, op_id, G.map_id] <;> rfl
    · have hp : ({j, i} : Finset κ).Nonempty := Finset.insert_nonempty _ _
      have h1 : ({j, i} : Finset κ).inf' hp e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e :=
        Finset.inf'_mono e (by simp) _
      have h2 : ({j, i} : Finset κ).inf' hp e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e :=
        Finset.inf'_mono e (by simp) _
      have E0 : Cube.d (cubeOf e G) 1 (epsLin e G x) ⟨{j, i}, Finset.card_pair hij.ne⟩ ⟨hp⟩ = 0 := by
        rw [hd] <;> rfl
      rw [d_pair G x e hij hp h1 h2, sub_eq_zero] at E0
      exact step G x (by simp) (by simp) (by simp [Finset.inf'_insert, inf_eq_left.mpr h]) h h1 h2 E0
  · intro hc
    have hc' : ∀ ⦃a b : P⦄ (h : b ≤ a), val G x b = (G.map (homOfLE h).op).hom (val G x a) := hc
    funext t ht
    obtain ⟨t, htc⟩ := t
    obtain ⟨i, j, hne, hs⟩ := Finset.card_eq_two.mp htc
    rcases lt_or_gt_of_ne hne with hij | hij
    · subst hs
      have h1 : ({i, j} : Finset κ).inf' ht.down e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e :=
        Finset.inf'_mono e (by simp) _
      have h2 : ({i, j} : Finset κ).inf' ht.down e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e :=
        Finset.inf'_mono e (by simp) _
      rw [d_pair G x e hij ht.down h1 h2, ← hc' h1, ← hc' h2, sub_self] <;> rfl
    · rw [Finset.pair_comm] at hs
      subst hs
      have h1 : ({j, i} : Finset κ).inf' ht.down e ≤ ({i} : Finset κ).inf' (Finset.singleton_nonempty i) e :=
        Finset.inf'_mono e (by simp) _
      have h2 : ({j, i} : Finset κ).inf' ht.down e ≤ ({j} : Finset κ).inf' (Finset.singleton_nonempty j) e :=
        Finset.inf'_mono e (by simp) _
      rw [d_pair G x e hij ht.down h1 h2, ← hc' h1, ← hc' h2, sub_self] <;> rfl

end Semilattice

theorem degZero {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P) :
    Function.Bijective e → ∃ ε : ∀ G : Pᵒᵖ ⥤ ModuleCat.{0} R, (nerveCx.obj G).X 0 ≅ ((cechOf e).obj G).X 0,
    (∀ {G G' : Pᵒᵖ ⥤ ModuleCat.{0} R} (φ : G ⟶ G'),
      (nerveCx.map φ).f 0 ≫ (ε G').hom = (ε G).hom ≫ ((cechOf e).map φ).f 0) ∧
    ∀ (G : Pᵒᵖ ⥤ ModuleCat.{0} R) (x : (nerveCx.obj G).X 0),
      ((nerveCx.obj G).d 0 1).hom x = 0 ↔ (((cechOf e).obj G).d 0 1).hom ((ε G).hom.hom x) = 0 := by
  intro hbij
  refine ⟨fun G => (LinearEquiv.ofBijective (epsLin e G)
      ⟨epsLin_injective e G hbij.2, epsLin_surjective e G hbij.1 hbij.2⟩).toModuleIso, ?_, ?_⟩
  · intro G G' φ
    ext x
    rfl
  · intro G x
    have hd1 : (nerveCx.obj G).d 0 1 = ModuleCat.ofHom (dNC G 0) := nerveCx_d G 0
    have hc1 : ((cechOf e).obj G).d 0 1 = ModuleCat.ofHom ((cubeOf e G).d 1) := GlobalTheory.cechComplex_d (cubeOf e G) 0
    rw [hd1, hc1]
    exact (dNC_zero_iff G x).trans (d_eps_zero_iff G e hbij.2 x).symm

end GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NerveCechDegreeZeroCompatibleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nerve_cech_degree_zero_compatible : ∀ {R : Type} [CommRing R] {P : Type} [SemilatticeInf P] {κ : Type} [LinearOrder κ] (e : κ → P),
    Function.Bijective e → ∃ ε : ∀ G : Pᵒᵖ ⥤ ModuleCat.{0} R, (nerveCx.obj G).X 0 ≅ ((cechOf e).obj G).X 0,
    (∀ {G G' : Pᵒᵖ ⥤ ModuleCat.{0} R} (φ : G ⟶ G'),
      (nerveCx.map φ).f 0 ≫ (ε G').hom = (ε G).hom ≫ ((cechOf e).map φ).f 0) ∧
    ∀ (G : Pᵒᵖ ⥤ ModuleCat.{0} R) (x : (nerveCx.obj G).X 0),
      ((nerveCx.obj G).d 0 1).hom x = 0 ↔ (((cechOf e).obj G).d 0 1).hom ((ε G).hom.hom x) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero.degZero | exact GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero.degZero | (intros; apply GlobalTheory.CompanionTheory.Hodge.Nerve.DegZero.degZero <;> assumption)
end
end
