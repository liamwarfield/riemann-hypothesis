module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerTwoDiagonalAdditiveEqZeroProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerTwoDiagonalAdditiveEqZeroProjective
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WedgeDiag

variable {R : Type} [CommRing R] {I : Type} [LinearOrder I]

noncomputable def lowerWedge :
    (I →₀ R) →ₗ[R] (I →₀ R) →ₗ[R] ⋀[R]^2 (I →₀ R) :=
  Finsupp.linearCombination R (fun i => Finsupp.linearCombination R (fun j =>
    if i < j then exteriorPower.ιMulti R 2 ![Finsupp.single i 1, Finsupp.single j 1] else 0))

noncomputable def wedgeBil {M : Type} [AddCommGroup M] [Module R M] :
    M →ₗ[R] M →ₗ[R] ⋀[R]^2 M :=
  LinearMap.mk₂ R (fun x y => exteriorPower.ιMulti R 2 ![x, y])
    (fun x x' y => by
      simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_add ![y] x x')
    (fun c x y => by
      simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_smul ![y] c x)
    (fun x y y' => by
      have h := fun a b : M => (exteriorPower.ιMulti R 2).map_swap ![a, b] (i := 0) (j := 1) (by decide)
      have e : ∀ a b : M, ![a, b] ∘ Equiv.swap 0 1 = ![b, a] := by
        intro a b; ext k; fin_cases k <;> rfl
      simp only [e] at h
      have h1 : exteriorPower.ιMulti R 2 ![y + y', x] = exteriorPower.ιMulti R 2 ![y, x] + exteriorPower.ιMulti R 2 ![y', x] := by
        simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_add ![x] y y'
      rw [h (y + y') x, h y x, h y' x, h1, neg_add])
    (fun c x y => by
      have h := fun a b : M => (exteriorPower.ιMulti R 2).map_swap ![a, b] (i := 0) (j := 1) (by decide)
      have e : ∀ a b : M, ![a, b] ∘ Equiv.swap 0 1 = ![b, a] := by
        intro a b; ext k; fin_cases k <;> rfl
      simp only [e] at h
      have h1 : exteriorPower.ιMulti R 2 ![c • y, x] = c • exteriorPower.ιMulti R 2 ![y, x] := by
        simpa using (exteriorPower.ιMulti R 2).toMultilinearMap.cons_smul ![x] c y
      rw [h (c • y) x, h y x, h1, smul_neg])

theorem wedgeBil_apply {M : Type} [AddCommGroup M] [Module R M] (x y : M) :
    wedgeBil x y = exteriorPower.ιMulti R 2 ![x, y] := rfl

theorem lowerWedge_sub_flip :
    lowerWedge (R := R) (I := I) - lowerWedge.flip = wedgeBil (M := I →₀ R) := by
  ext i j
  simp only [lowerWedge, LinearMap.sub_apply, LinearMap.flip_apply, LinearMap.coe_comp,
    Function.comp_apply, Finsupp.lsingle_apply, Finsupp.linearCombination_single, one_smul,
    LinearMap.smul_apply, wedgeBil_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.not_gt]
  · simp only [lt_irrefl, if_false, sub_zero]
    exact congrArg _ ((exteriorPower.ιMulti R 2 (M := I →₀ R)).map_eq_zero_of_eq ![Finsupp.single i 1, Finsupp.single i 1] (i := 0) (j := 1) rfl (by decide)).symm
  · have hs := (exteriorPower.ιMulti R 2).map_swap ![Finsupp.single j (1:R), Finsupp.single i 1] (i := 0) (j := 1) (by decide)
    have e : ![Finsupp.single j (1:R), Finsupp.single i 1] ∘ Equiv.swap 0 1 = ![Finsupp.single i 1, Finsupp.single j 1] := by
      ext k; fin_cases k <;> rfl
    rw [e] at hs
    simp [h, h.not_gt, hs]

end GlobalTheory.WedgeDiag

namespace GlobalTheory.WedgeDiag

variable {R : Type} [CommRing R] {I : Type} [LinearOrder I]

noncomputable def crossWedge :
    ((I →₀ R) × (I →₀ R)) [⋀^Fin 2]→ₗ[R] ⋀[R]^2 (I →₀ R) where
  toFun v := lowerWedge (v 0).1 (v 1).2 - lowerWedge (v 1).1 (v 0).2
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp [Function.update_of_ne, map_add (f := _), LinearMap.add_apply] <;> abel
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp [Function.update_of_ne, map_smul, LinearMap.smul_apply, smul_sub]
  map_eq_zero_of_eq' := by
    intro v i j h hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem crossWedge_apply (v : Fin 2 → (I →₀ R) × (I →₀ R)) :
    crossWedge v = lowerWedge (v 0).1 (v 1).2 - lowerWedge (v 1).1 (v 0).2 := rfl

noncomputable def crossWedgeLin : ⋀[R]^2 ((I →₀ R) × (I →₀ R)) →ₗ[R] ⋀[R]^2 (I →₀ R) :=
  exteriorPower.alternatingMapLinearEquiv crossWedge

theorem crossWedgeLin_inl :
    crossWedgeLin ∘ₗ exteriorPower.map 2 (LinearMap.inl R (I →₀ R) (I →₀ R)) = 0 := by
  ext v
  simp [crossWedgeLin, crossWedge_apply]

theorem crossWedgeLin_inr :
    crossWedgeLin ∘ₗ exteriorPower.map 2 (LinearMap.inr R (I →₀ R) (I →₀ R)) = 0 := by
  ext v
  simp [crossWedgeLin, crossWedge_apply]

theorem crossWedgeLin_diag :
    crossWedgeLin ∘ₗ exteriorPower.map 2
      (LinearMap.inl R (I →₀ R) (I →₀ R) + LinearMap.inr R (I →₀ R) (I →₀ R)) = LinearMap.id := by
  ext v
  have h := LinearMap.congr_fun₂ (lowerWedge_sub_flip (R := R) (I := I)) (v 0) (v 1)
  simp only [LinearMap.sub_apply, LinearMap.flip_apply, wedgeBil_apply] at h
  have hv : ![v 0, v 1] = v := by ext k; fin_cases k <;> rfl
  rw [hv] at h
  simp [crossWedgeLin, crossWedge_apply, h]

theorem free_case (t : ⋀[R]^2 (I →₀ R))
    (H : exteriorPower.map 2 (LinearMap.inl R (I →₀ R) (I →₀ R) + LinearMap.inr R (I →₀ R) (I →₀ R)) t =
      exteriorPower.map 2 (LinearMap.inl R (I →₀ R) (I →₀ R)) t +
        exteriorPower.map 2 (LinearMap.inr R (I →₀ R) (I →₀ R)) t) : t = 0 := by
  have h := congrArg crossWedgeLin H
  rw [map_add (f := _), ← LinearMap.comp_apply, ← LinearMap.comp_apply crossWedgeLin, ← LinearMap.comp_apply crossWedgeLin,
    crossWedgeLin_diag, crossWedgeLin_inl, crossWedgeLin_inr] at h
  simpa using h

end GlobalTheory.WedgeDiag

namespace GlobalTheory.WedgeDiag

theorem eq_zero_of_diag_additive : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] (t : ⋀[R]^2 M), exteriorPower.map 2 (LinearMap.inl R M M + LinearMap.inr R M M) t = exteriorPower.map 2 (LinearMap.inl R M M) t + exteriorPower.map 2 (LinearMap.inr R M M) t → t = 0 := by
  intro R M _ _ _ _ t H
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective R M)
  letI : LinearOrder M := IsWellOrder.linearOrder WellOrderingRel
  set p : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  have e0 : (LinearMap.inl R (M →₀ R) (M →₀ R) + LinearMap.inr R (M →₀ R) (M →₀ R)) ∘ₗ s =
      (s.prodMap s) ∘ₗ (LinearMap.inl R M M + LinearMap.inr R M M) := by
    ext x <;> simp
  have e1 : (s.prodMap s) ∘ₗ LinearMap.inl R M M = LinearMap.inl R (M →₀ R) (M →₀ R) ∘ₗ s := by
    ext x <;> simp
  have e2 : (s.prodMap s) ∘ₗ LinearMap.inr R M M = LinearMap.inr R (M →₀ R) (M →₀ R) ∘ₗ s := by
    ext x <;> simp
  have hu : exteriorPower.map 2 s t = 0 := by
    apply free_case
    have h := congrArg (exteriorPower.map 2 (s.prodMap s)) H
    rw [map_add (f := _)] at h
    simp only [← LinearMap.comp_apply, ← exteriorPower.map_comp] at h ⊢
    rw [e0, ← e1, ← e2]
    exact h
  have := congrArg (exteriorPower.map 2 p) hu
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hs, exteriorPower.map_id, map_zero] at this
  exact this

end GlobalTheory.WedgeDiag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorPowerTwoDiagonalAdditiveEqZeroProjectiveStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorPowerTwo_diagonal_additive_eq_zero_projective : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M] (t : ⋀[R]^2 M), exteriorPower.map 2 (LinearMap.inl R M M + LinearMap.inr R M M) t = exteriorPower.map 2 (LinearMap.inl R M M) t + exteriorPower.map 2 (LinearMap.inr R M M) t → t = 0 := by
  first | exact @GlobalTheory.WedgeDiag.eq_zero_of_diag_additive | exact GlobalTheory.WedgeDiag.eq_zero_of_diag_additive | (intros; apply GlobalTheory.WedgeDiag.eq_zero_of_diag_additive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanish
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.PrimitivePullback

variable {R : Type} [CommRing R]

theorem pullHO1_congr {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ ψ : X' ⟶ X} (e : φ = ψ)
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (h' : ψ ≫ s = s' ≫ spMap (RingHom.id R)) (c : HO1 s) :
    pullHO1 h c = pullHO1 h' c := by
  subst e; rfl

theorem isPullO_congr {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ ψ : X' ⟶ X} (e : φ = ψ)
    (h : φ ≫ s = s' ≫ spMap (RingHom.id R)) (h' : ψ ≫ s = s' ≫ spMap (RingHom.id R)) {c : HO1 s} {c' : HO1 s'} :
    IsPullO h c c' ↔ IsPullO h' c c' := by
  subst e; rfl

theorem pullHO1_self {X : Scheme.{0}} {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) (c : HO1 s) :
    pullHO1 h c = c :=
  (IsPullO.eq_pullHO1 h
    (CoefMap.pullCohomologyOne_eq_of_natTrans (pairPull h) (pairRes _ s) (pairIdTrans X) (fun _ _ ↦ rfl) c)).symm

theorem pullHO1_comp {A B C : Over (Sp R)} (f : B ⟶ C) (g : A ⟶ B) (a : HO1 C.hom) :
    pullHO1 (overW g) (pullHO1 (overW f) a) = pullHO1 (overW (g ≫ f)) a := by
  have h'' : (g.left ≫ f.left) ≫ C.hom = A.hom ≫ spMap (RingHom.id R) := by
    rw [← Over.comp_left]; exact overW (g ≫ f)
  have k := (GlobalTheory.T.structureSheaf_pullback_relations_basic R C.left B.left C.hom B.hom f.left (overW f)).2.2 A.left A.hom g.left (overW g) h'' a _ _
    (isPullO_pullHO1 _ a) (isPullO_pullHO1 _ _)
  exact IsPullO.eq_pullHO1 _ ((isPullO_congr (show g.left ≫ f.left = (g ≫ f).left from rfl) _ _).1 k)

theorem pullHO1_pull_self {A B : Over (Sp R)} (f : B ⟶ A) (g : A ⟶ B) (e : g ≫ f = 𝟙 A) (a : HO1 A.hom) :
    pullHO1 (overW g) (pullHO1 (overW f) a) = a := by
  rw [pullHO1_comp]
  have h' : 𝟙 A.left ≫ A.hom = A.hom ≫ spMap (RingHom.id R) := by
    rw [← Over.id_left]; exact overW (𝟙 A)
  rw [pullHO1_congr (show (g ≫ f).left = 𝟙 A.left by rw [e]; rfl) _ h', pullHO1_self]

theorem pullHO1_pull_one {A B : Over (Sp R)} [GrpObj A] (f : B ⟶ A) (g : A ⟶ B) (e : g ≫ f = 1) (a : HO1 A.hom) :
    pullHO1 (overW g) (pullHO1 (overW f) a) = 0 := by
  rw [pullHO1_comp]
  have h' : (toUnit A ≫ η[A]).left ≫ A.hom = A.hom ≫ spMap (RingHom.id R) := overW _
  rw [pullHO1_congr (show (g ≫ f).left = (toUnit A ≫ η[A]).left by rw [e, Hom.one_def]) _ h', ← pullHO1_comp]
  have : pullHO1 (overW η[A]) a = 0 := by
    haveI : IsAffine (𝟙_ (Over (Sp R))).left := by change IsAffine (Sp R); infer_instance
    exact (GlobalTheory.T.abelian_square_affine_h1_vanish R).2 _ _ _
  rw [this, map_zero]

variable (A : Over (Sp R)) [GrpObj A]

def sumPull : HO1 A.hom × HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom :=
  (pullHO1 (overW (fst A A))).coprod (pullHO1 (overW (snd A A)))

def axesPull : HO1 (A ⊗ A).hom →ₗ[R] HO1 A.hom × HO1 A.hom :=
  (pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A)))).prod (pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))))

theorem axesPull_sumPull (x : HO1 A.hom × HO1 A.hom) : axesPull A (sumPull A x) = x := by
  obtain ⟨a, b⟩ := x
  refine Prod.ext ?_ ?_
  · change pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) (pullHO1 (overW (fst A A)) a + pullHO1 (overW (snd A A)) b) = a
    rw [map_add (f := _), pullHO1_pull_self _ _ (lift_fst _ _), pullHO1_pull_one _ _ (lift_snd _ _), add_zero]
  · change pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) (pullHO1 (overW (fst A A)) a + pullHO1 (overW (snd A A)) b) = b
    rw [map_add (f := _), pullHO1_pull_one _ _ (lift_fst _ _), pullHO1_pull_self _ _ (lift_snd _ _), zero_add]

theorem axesPull_injective (hax : AxesVanishingStructureSheafDegOne) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Function.Injective (axesPull A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h1 : pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) x = 0 := congrArg Prod.fst hx
  have h2 : pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) x = 0 := congrArg Prod.snd hx
  refine hax R A g hA hg x ?_ ?_
  · have := isPullO_pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) x; rwa [h1] at this
  · have := isPullO_pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) x; rwa [h2] at this

theorem pullHO1_mul (hax : AxesVanishingStructureSheafDegOne) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (a : HO1 A.hom) : pullHO1 (overW μ[A]) a = sumPull A (a, a) := by
  apply axesPull_injective A hax g hA hg
  rw [axesPull_sumPull]
  refine Prod.ext ?_ ?_
  · change pullHO1 (overW (lift (𝟙 A) (1 : A ⟶ A))) (pullHO1 (overW μ[A]) a) = a
    exact pullHO1_pull_self _ _ (by rw [Hom.one_def, lift_comp_one_right]) a
  · change pullHO1 (overW (lift (1 : A ⟶ A) (𝟙 A))) (pullHO1 (overW μ[A]) a) = a
    exact pullHO1_pull_self _ _ (by rw [Hom.one_def, lift_comp_one_left]) a

theorem sumPull_bijective (hax : AxesVanishingStructureSheafDegOne) (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    Function.Bijective (sumPull A) :=
  ⟨Function.LeftInverse.injective (axesPull_sumPull A), fun c ↦
    ⟨axesPull A c, axesPull_injective A hax g hA hg (axesPull_sumPull A _)⟩⟩

end GlobalTheory.Obs.PrimitivePullback

namespace GlobalTheory.Obs.PrimitivePullback

variable {R : Type} [CommRing R] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R} {φ : X' ⟶ X}
  {h : φ ≫ s = s' ≫ spMap (RingHom.id R)}

theorem isPullO2_zero : IsPullbackH2Structure h (0 : CatCoh.H2 (OAff s)) (0 : CatCoh.H2 (OAff s')) := by
  unfold IsPullbackH2Structure; rw [map_zero, map_zero]

theorem isPullO2_add {a b : CatCoh.H2 (OAff s)} {a' b' : CatCoh.H2 (OAff s')} (ha : IsPullbackH2Structure h a a')
    (hb : IsPullbackH2Structure h b b') : IsPullbackH2Structure h (a + b) (a' + b') := by
  unfold IsPullbackH2Structure at *; rw [map_add (f := _), map_add (f := _), ha, hb]

theorem isPullO2_smul {a : CatCoh.H2 (OAff s)} {a' : CatCoh.H2 (OAff s')} (ha : IsPullbackH2Structure h a a') (r : R) :
    IsPullbackH2Structure h (r • a) (r • a') := by
  unfold IsPullbackH2Structure at *; rw [map_smulₛₗ, map_smulₛₗ, ha]

theorem isPullO2_unique {c : CatCoh.H2 (OAff s)} {x y : CatCoh.H2 (OAff s')} (hx : IsPullbackH2Structure h c x)
    (hy : IsPullbackH2Structure h c y) : x = y :=
  (GlobalTheory.T.structureSheaf_pullback_relations_basic R X X' s s' φ h).1.1 (hx.symm.trans hy)

theorem pullback_wedge_cup_square (h : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (e : ⋀[R]^2 (HO1 s) ≃ₗ[R] CatCoh.H2 (OAff s))
    (he : ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = CatCoh.cup (OAff s) a b)
    (e' : ⋀[R]^2 (HO1 s') ≃ₗ[R] CatCoh.H2 (OAff s'))
    (he' : ∀ a b, e' (exteriorPower.ιMulti R 2 ![a, b]) = CatCoh.cup (OAff s') a b) (t : ⋀[R]^2 (HO1 s)) :
    IsPullbackH2Structure h (e t) (e' (exteriorPower.map 2 (pullHO1 h) t)) := by
  have key : ∀ a b : HO1 s, IsPullbackH2Structure h (e (exteriorPower.ιMulti R 2 ![a, b]))
      (e' (exteriorPower.map 2 (pullHO1 h) (exteriorPower.ιMulti R 2 ![a, b]))) := by
    intro a b
    have hc : (pullHO1 h) ∘ ![a, b] = ![pullHO1 h a, pullHO1 h b] := by
      funext i; fin_cases i <;> try rfl
    rw [exteriorPower.map_apply_ιMulti, hc, he, he']
    exact (GlobalTheory.T.structureSheaf_pullback_relations_basic R X X' s s' φ h).2.1 a b _ _ (isPullO_pullHO1 h a) (isPullO_pullHO1 h b)
  have ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> try rfl
    have := key (v 0) (v 1)
    rwa [← hv] at this
  | zero => simp only [map_zero]; exact isPullO2_zero
  | add x y _ _ hx hy => simp only [map_add (f := _)]; exact isPullO2_add hx hy
  | smul r x _ hx => simp only [map_smul]; exact isPullO2_smul hx r

end GlobalTheory.Obs.PrimitivePullback


open GlobalTheory.Obs.PrimitivePullback in
theorem GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso
    (H : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom →
      (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
        ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
      ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom),
        ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b) : PrimitiveStructureSheafDegTwoVanish := by
  intro R _ A _ g hA hg c c₁ c₂ hm h1 h2
  have hax : AxesVanishingStructureSheafDegOne := GlobalTheory.T.axesO1_of_projective_rank_cup H
  obtain ⟨hAA, hgg⟩ := (GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg
  obtain ⟨⟨_, hproj, _⟩, e, he⟩ := H R A g hA hg
  obtain ⟨_, e', he'⟩ := H R (A ⊗ A) (g + g) hAA hgg
  obtain ⟨t, rfl⟩ := e.surjective c
  have km := pullback_wedge_cup_square (overW μ[A]) e he e' he' t
  have k1 := pullback_wedge_cup_square (overW (fst A A)) e he e' he' t
  have k2 := pullback_wedge_cup_square (overW (snd A A)) e he e' he' t
  have E : exteriorPower.map 2 (pullHO1 (overW μ[A])) t =
      exteriorPower.map 2 (pullHO1 (overW (fst A A))) t + exteriorPower.map 2 (pullHO1 (overW (snd A A))) t := by
    apply e'.injective
    rw [map_add (f := _), ← isPullO2_unique hm km, ← isPullO2_unique h1 k1, ← isPullO2_unique h2 k2]
  let P := LinearEquiv.ofBijective (sumPull A) (sumPull_bijective A hax g hA hg)
  have hμ : (pullHO1 (overW μ[A]) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) =
      sumPull A ∘ₗ (LinearMap.inl R (HO1 A.hom) (HO1 A.hom) + LinearMap.inr R (HO1 A.hom) (HO1 A.hom)) := by
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk,
      add_zero, zero_add]
    exact pullHO1_mul A hax g hA hg a
  have h₁ : (pullHO1 (overW (fst A A)) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) =
      sumPull A ∘ₗ LinearMap.inl R (HO1 A.hom) (HO1 A.hom) := by
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.inl_apply]
    simp only [sumPull, LinearMap.coprod_apply, map_zero, add_zero]
  have h₂ : (pullHO1 (overW (snd A A)) : HO1 A.hom →ₗ[R] HO1 (A ⊗ A).hom) =
      sumPull A ∘ₗ LinearMap.inr R (HO1 A.hom) (HO1 A.hom) := by
    refine LinearMap.ext fun a ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.inr_apply]
    simp only [sumPull, LinearMap.coprod_apply, map_zero, zero_add]
  simp only [hμ, h₁, h₂, exteriorPower.map_comp, LinearMap.comp_apply] at E
  rw [← map_add (exteriorPower.map 2 (sumPull A))] at E
  have hid : P.symm.toLinearMap ∘ₗ sumPull A = LinearMap.id :=
    LinearMap.ext fun x ↦ P.symm_apply_apply x
  have hinj : Function.Injective (exteriorPower.map 2 (sumPull A)) := by
    intro x y hxy
    have k : ∀ z, exteriorPower.map 2 P.symm.toLinearMap (exteriorPower.map 2 (sumPull A) z) = z := by
      intro z
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hid, exteriorPower.map_id, LinearMap.id_apply]
    rw [← k x, ← k y, hxy]
  haveI := hproj
  rw [GlobalTheory.T.exteriorPowerTwo_diagonal_additive_eq_zero_projective R (HO1 A.hom) t (hinj E), map_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanishStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧ ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom), ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b) → PrimitiveStructureSheafDegTwoVanish := by
  first | exact @GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso | exact GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso | (intros; apply GlobalTheory.Obs.primitiveStructureSheafDegTwoVanish_of_cup_iso <;> assumption)
end
