module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerBaseOfTraitAbelianPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPeriodsBasePeriodsConstForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnifAlongPullTo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnifAlongFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
open Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.TraitExt


open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear in
theorem exists_pull_gen {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
    (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g) (hI : I.map g ≤ I')
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (_ : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R')))
      (U' : Unif I' D' A' ((Over.pullback (spMap g)).obj G)) (gA : A'.A.left ⟶ A.A.left)
      (πK : pullback ((Over.pullback (spMap g)).obj G).hom (jK R') ⟶ pullback G.hom (jK R)),
      IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA ∧ LBIso A'.L (A.L.pull gA) ∧
      πK ≫ pullback.fst G.hom (jK R) =
        pullback.fst ((Over.pullback (spMap g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g) ∧
      U'.gen.hom.left ≫ gA = πK ≫ U.gen.hom.left := by
  have hP : PolBaseChangeSt := polBaseChange_holds
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  have sq : spMap (fracMap hg) ≫ jK R = jK R' ≫ spMap g := (fracMap_sq hg).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap (fracMap hg)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (fracMap hg)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap (fracMap hg) ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp
      (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) =
      pullback.fst G.hom (spMap g) := Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫
      pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec ((Over.pullback (specOf g)).obj G)) (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) :=
    ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
      rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig,
      pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, hU', -⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  refine ⟨D', hD, A', U', gA, eA.hom.left ≫ gA ≫ U.gen.inv.left, gpA, LBIso.symm tA, ?_, ?_⟩
  · simpa only [Category.assoc] using heA
  · rw [hU']; simp only [Category.assoc, hgi, Category.comp_id]

end GlobalTheory.TraitExt

namespace GlobalTheory.TraitExt

end GlobalTheory.TraitExt
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear

noncomputable section

namespace GlobalTheory.TraitExt


open GlobalTheory.ArcPull in
theorem exists_unifAlong_pullTo : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f : T.V →+* V₂), IsCN V₂ → IsDiscreteValuationRing V₂ → Function.Injective f → f.Finite → IsLocalHom f → ∃ (D' : DegData V₂ (maximalIdeal V₂)) (_ : IsPullDeg f T.D.toPre D'.toPre) (G' : Over (Sp V₂)) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V₂))) (U' : Unif (maximalIdeal V₂) D' A' G'), IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' := by
  intro g n F T V₂ _ _ _ f hCN _ hinj hfin hloc
  obtain ⟨hN, hIC, hW, hC⟩ := hCN
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have hR' : AdmBase V₂ (maximalIdeal V₂) := ⟨hN, inferInstance, hIC, hW⟩
  have hI : (maximalIdeal T.V).map f ≤ maximalIdeal V₂ :=
    Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit f a ha
  obtain ⟨D', hD, A', U', gA, πK, gpA, tA, hK, hgen⟩ := exists_pull_gen hR hR' f hinj hI T.semi T.U
  obtain ⟨β₂, hβ₂, hΛ⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ _ T.A.A A'.A gA gpA
  have sq : spMap (fracMap hinj) ≫ jK T.V = jK V₂ ≫ spMap f :=
    (fracMap_sq hinj).symm.trans (Category.id_comp _)
  refine ⟨D', hD, (Over.pullback (spMap f)).obj T.G, inferInstance, inferInstance, pullback.fst T.G.hom (spMap f),
    A', U', ?_⟩
  refine ⟨isGrpPullback_pullback T.G (spMap f), spMap (fracMap hinj), πK, gA ≫ T.α, β₂ ≫ T.α₂, sq, hK,
    gpA.comp T.cart, isSquare_comp hβ₂ T.sq, hΛ T.A.L A'.L _ F.univ.P T.α₂ T.A.isLB A'.isLB F.univ.isLB tA T.lb, ?_⟩
  rw [← Category.assoc, hgen, Category.assoc]

end GlobalTheory.TraitExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootsOfPeriods
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueNthRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoHom
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.MonoHom

variable {X : Type} [AddCommGroup X] {K : Type} [Field K]

def pform {ι : Type} (e : Module.Basis ι ℤ X) (i j : ι) : LinearMap.BilinForm ℤ X :=
  (e.coord i).smulRight (e.coord j)

@[simp] theorem pform_apply {ι : Type} (e : Module.Basis ι ℤ X) (i j : ι) (x y : X) :
    pform e i j x y = e.coord i x * e.coord j y := by
  simp [pform]

end GlobalTheory.MonoHom

namespace GlobalTheory.MonoHom

end GlobalTheory.MonoHom
end
end

open GlobalTheory.MonoHom

noncomputable section

namespace GlobalTheory.PerRoot

variable {X : Type} [AddCommGroup X]

def halfForm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j : Fin r) : LinearMap.BilinForm ℤ X :=
  if i < j then pform e i j + pform e j i else if i = j then pform e i i else 0

theorem halfForm_symm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j : Fin r) (x y : X) :
    halfForm e i j x y = halfForm e i j y x := by
  unfold halfForm; split_ifs <;> simp [pform_apply] <;> ring

theorem halfForm_basis {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j i₀ j₀ : Fin r) :
    halfForm e i j (e i₀) (e j₀) = if i = min i₀ j₀ ∧ j = max i₀ j₀ then 1 else 0 := by
  unfold halfForm
  rcases lt_trichotomy i₀ j₀ with h | rfl | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega
  · simp only [min_self, max_self]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega
  · rw [min_eq_right h.le, max_eq_left h.le]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega

theorem eq_sum_halfForm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ x y, β x y = β y x) :
    β = ∑ p : Fin r × Fin r, β (e p.1) (e p.2) • halfForm e p.1 p.2 := by
  refine LinearMap.ext_basis e e fun i₀ j₀ => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, halfForm_basis, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (min i₀ j₀, max i₀ j₀)]
  · simp only [and_self, if_true]
    rcases le_total i₀ j₀ with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, hβ]
  · intro p _ hp; rw [if_neg]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bimul_ext {G : Type} [CommGroup G] {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (f g : X → X → G)
    (hf : ∀ a a' b, f (a + a') b = f a b * f a' b) (hf' : ∀ a b b', f a (b + b') = f a b * f a b')
    (hg : ∀ a a' b, g (a + a') b = g a b * g a' b) (hg' : ∀ a b b', g a (b + b') = g a b * g a b')
    (h : ∀ i j, f (e i) (e j) = g (e i) (e j)) : f = g := by
  have key : ∀ (φ ψ : X → G), (∀ a a', φ (a + a') = φ a * φ a') → (∀ a a', ψ (a + a') = ψ a * ψ a') →
      (∀ i, φ (e i) = ψ (e i)) → φ = ψ := by
    intro φ ψ hφ hψ hi
    let Φ : X →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (φ a)) (fun a a' => by simp [hφ])
    let Ψ : X →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (ψ a)) (fun a a' => by simp [hψ])
    have hL : Φ.toIntLinearMap = Ψ.toIntLinearMap := e.ext fun i => by simp [Φ, Ψ, hi]
    funext a
    have := congrArg (fun L : X →ₗ[ℤ] Additive G => Additive.toMul (L a)) hL
    simpa [Φ, Ψ] using this
  have h1 : ∀ j a, f a (e j) = g a (e j) := fun j => congrFun
    (key (fun a => f a (e j)) (fun a => g a (e j)) (fun a a' => hf a a' _) (fun a a' => hg a a' _) (fun i => h i j))
  funext a
  exact key (f a) (g a) (hf' a) (hg' a) (fun j => h1 j a)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def IsSymBasis (ε : ι → LinearMap.BilinForm ℤ X) : Prop :=
  (∀ k x y, ε k x y = ε k y x) ∧ LinearIndependent ℤ ε ∧
    ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → β ∈ Submodule.span ℤ (Set.range ε)

theorem exists_coords {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) {r : ℕ} (e : Module.Basis (Fin r) ℤ X) :
    ∃ c : Fin r × Fin r → ι → ℤ, ∀ p, ∑ k, c p k • ε k = halfForm e p.1 p.2 := by
  have : ∀ p : Fin r × Fin r, ∃ c : ι → ℤ, ∑ k, c k • ε k = halfForm e p.1 p.2 := fun p =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hε.2.2 _ (halfForm_symm e p.1 p.2))
  choose c hc using this
  exact ⟨c, hc⟩

theorem dual_coords {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) {r : ℕ} (e : Module.Basis (Fin r) ℤ X)
    {c : Fin r × Fin r → ι → ℤ} (hc : ∀ p, ∑ k, c p k • ε k = halfForm e p.1 p.2) (k' k : ι) :
    ∑ p, ε k' (e p.1) (e p.2) * c p k = if k' = k then 1 else 0 := by
  have h1 : ε k' = ∑ k, (∑ p, ε k' (e p.1) (e p.2) * c p k) • ε k := by
    conv_lhs => rw [eq_sum_halfForm e (ε k') (hε.1 k')]
    simp_rw [← hc, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 : ε k' = ∑ k, (if k' = k then (1 : ℤ) else 0) • ε k := by simp
  have h3 : ∑ k, ((∑ p, ε k' (e p.1) (e p.2) * c p k) - (if k' = k then 1 else 0)) • ε k = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, ← h1, ← h2, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hε.2.1 _ h3 k)

variable {G : Type} [CommGroup G]

theorem zpow_sumF {κ : Type} (s : Finset κ) (a : G) (f : κ → ℤ) : a ^ (∑ p ∈ s, f p) = ∏ p ∈ s, a ^ f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

theorem eq_one_of_prod_zpow {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (u : ι → G) (h : ∀ x y, ∏ k, u k ^ ε k x y = 1) (k : ι) : u k = 1 := by
  let e := Module.finBasis ℤ X
  obtain ⟨c, hc⟩ := exists_coords hε e
  calc u k = ∏ k', u k' ^ (if k' = k then (1 : ℤ) else 0) := by simp
    _ = ∏ k', u k' ^ (∑ p, ε k' (e p.1) (e p.2) * c p k) := by simp_rw [dual_coords hε e hc]
    _ = ∏ p, (∏ k', u k' ^ ε k' (e p.1) (e p.2)) ^ c p k := by
      simp_rw [← Finset.prod_zpow, zpow_sumF, ← zpow_mul]
      exact Finset.prod_comm
    _ = 1 := by simp [h]

theorem existsUnique_coeff {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (q : X → X → G) (hsym : ∀ x y, q x y = q y x) (hadd : ∀ x x' y, q (x + x') y = q x y * q x' y) :
    ∃! σ : ι → G, ∀ x y, q x y = ∏ k, σ k ^ ε k x y := by
  let e := Module.finBasis ℤ X
  obtain ⟨c, hc⟩ := exists_coords hε e
  have hadd' : ∀ x y y', q x (y + y') = q x y * q x y' := fun x y y' => by
    rw [hsym, hadd, hsym y, hsym y']
  have hF : ∀ x y, ∏ k, (∏ p, q (e p.1) (e p.2) ^ c p k) ^ ε k x y =
      ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X), q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y := by
    intro x y
    simp_rw [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← zpow_sumF, ← hc p]
    simp [LinearMap.sum_apply, mul_comm]
  refine ⟨fun k => ∏ p, q (e p.1) (e p.2) ^ c p k, fun x y => ?_, fun σ hσ => funext fun k => ?_⟩
  · rw [hF]
    have := bimul_ext e q (fun x y => ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X),
        q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y) hadd hadd'
      (fun a a' b => by simp only [map_add (f := _), LinearMap.add_apply, zpow_add, Finset.prod_mul_distrib])
      (fun a b b' => by simp only [map_add (f := _), zpow_add, Finset.prod_mul_distrib])
      (fun i j => by
        simp only [halfForm_basis]
        rw [Finset.prod_eq_single (min i j, max i j)]
        · simp only [and_self, if_true, zpow_one]
          rcases le_total i j with h | h
          · rw [min_eq_left h, max_eq_right h]
          · rw [min_eq_right h, max_eq_left h, hsym]
        · intro p _ hp; rw [if_neg, zpow_zero]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
        · intro h; exact absurd (Finset.mem_univ _) h)
    exact congrFun (congrFun this x) y
  · have h0 : ∀ x y, ∏ k, (σ k / ∏ p, q (e p.1) (e p.2) ^ c p k) ^ ε k x y = 1 := fun x y => by
      simp_rw [div_zpow, Finset.prod_div_distrib, ← hσ, hF]
      rw [div_eq_one]
      have := bimul_ext e q (fun x y => ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X),
          q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y) hadd hadd'
        (fun a a' b => by simp only [map_add (f := _), LinearMap.add_apply, zpow_add, Finset.prod_mul_distrib])
        (fun a b b' => by simp only [map_add (f := _), zpow_add, Finset.prod_mul_distrib])
        (fun i j => by
          simp only [halfForm_basis]
          rw [Finset.prod_eq_single (min i j, max i j)]
          · simp only [and_self, if_true, zpow_one]
            rcases le_total i j with h | h
            · rw [min_eq_left h, max_eq_right h]
            · rw [min_eq_right h, max_eq_left h, hsym]
          · intro p _ hp; rw [if_neg, zpow_zero]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
          · intro h; exact absurd (Finset.mem_univ _) h)
      exact congrFun (congrFun this x) y
    exact div_eq_one.1 (eq_one_of_prod_zpow hε _ h0 k)

theorem eq_of_prod_zpow {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (s s' : ι → G) (h : ∀ x y, ∏ k, s k ^ ε k x y = ∏ k, s' k ^ ε k x y) : s = s' := by
  funext k
  refine div_eq_one.1 (eq_one_of_prod_zpow hε (fun k => s k / s' k) (fun x y => ?_) k)
  simp_rw [div_zpow, Finset.prod_div_distrib, h, div_self']

theorem pow_eq_pow_of_prod {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (n : ℕ) (s s' : ι → G) (h : ∀ x y, ∏ k, s k ^ ((n : ℤ) * ε k x y) = ∏ k, s' k ^ ((n : ℤ) * ε k x y)) (k : ι) :
    s k ^ n = s' k ^ n := by
  have := congrFun (eq_of_prod_zpow hε (fun k => s k ^ n) (fun k => s' k ^ n) fun x y => by
    simp_rw [← zpow_natCast, ← zpow_mul]; exact h x y) k
  exact this

theorem isSymBasis_mul : IsSymBasis (fun _ : Fin 1 => (LinearMap.mul ℤ ℤ : LinearMap.BilinForm ℤ ℤ)) := by
  refine ⟨fun _ x y => mul_comm x y, ?_, fun β _ => ?_⟩
  · rw [linearIndependent_unique_iff]
    intro h
    have := LinearMap.congr_fun₂ h 1 1
    simp at this
  · refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨fun _ => β 1 1, ?_⟩
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [Finset.univ_unique, Finset.sum_singleton, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    have hx : x = x • (1 : ℤ) := by simp
    have hy : y = y • (1 : ℤ) := by simp
    rw [hx, hy, LinearMap.map_smul₂, LinearMap.map_smul]
    simp only [smul_eq_mul]; ring

end GlobalTheory.PerRoot
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerRoot

open IsDedekindDomain Polynomial

theorem exists_ord (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    ∃ v : (FractionRing V)ˣ →* Multiplicative ℤ,
      (∀ x : (FractionRing V)ˣ, 0 ≤ (v x).toAdd → ∃ a : V, algebraMap V _ a = (x : FractionRing V)) ∧
      ∀ (x : (FractionRing V)ˣ) (a : V), algebraMap V _ a = (x : FractionRing V) →
        (0 < (v x).toAdd ↔ a ∈ maximalIdeal V) := by
  let w := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  have hw : ∀ x : (FractionRing V)ˣ, w x ≠ 0 := fun x => by simp [w]
  refine ⟨MonoidHom.mk' (fun x => Multiplicative.ofAdd (-WithZero.log (w x))) fun x y => ?_, fun x hx => ?_,
    fun x a ha => ?_⟩
  · rw [← ofAdd_add, Units.val_mul, map_mul, WithZero.log_mul (hw x) (hw y), neg_add]
  · refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
    simp only [MonoidHom.mk'_apply, toAdd_ofAdd, neg_nonneg] at hx
    exact (WithZero.log_le_log (hw x) one_ne_zero).1 (by simpa using hx)
  · simp only [MonoidHom.mk'_apply, toAdd_ofAdd, neg_pos]
    have h1 : WithZero.log (w x) < 0 ↔ w x < 1 := by
      simpa using WithZero.log_lt_log (hw x) one_ne_zero
    rw [h1, ← ha]
    exact HeightOneSpectrum.valuation_lt_one_iff_mem _ a

theorem exists_nthRoots_ext (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] {I : Type} [Fintype I] (a : I → V) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (f : V →+* W) (s : I → W),
      Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ ∀ k, s k ^ n = f (a k) := by
  classical
  let K := FractionRing V
  haveI : CharZero K := algebraRat.charZero _
  let p : I → K[X] := fun k => X ^ n - C (algebraMap V K (a k))
  have hp : ∀ k, (p k).Monic := fun k => monic_X_pow_sub_C _ (by omega)
  let L := (∏ k, p k).SplittingField
  have hsp : ((∏ k, p k).map (algebraMap K L)).Splits := SplittingField.splits _
  have hroot : ∀ k, ∃ t : L, t ^ n = algebraMap K L (algebraMap V K (a k)) := fun k => by
    have h0 : (∏ k, p k).map (algebraMap K L) ≠ 0 :=
      ((monic_prod_of_monic _ _ fun k _ => hp k).map _).ne_zero
    have h1 : ((p k).map (algebraMap K L)).Splits :=
      hsp.of_dvd h0 (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)))
    obtain ⟨t, ht⟩ := h1.exists_eval_eq_zero (by
      rw [(hp k).degree_map, degree_X_pow_sub_C (by omega)]
      exact_mod_cast (by omega : n ≠ 0))
    refine ⟨t, ?_⟩
    simpa [p, sub_eq_zero] using ht
  choose t ht using hroot
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V K L
  have hs : ∀ k, t k ∈ Set.range (algebraMap W L) := fun k => hint _
    ⟨X ^ n - C (a k), monic_X_pow_sub_C _ (by omega), by simp [ht]⟩
  choose s hs using hs
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, algebraMap V W, s, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, fun k => IsFractionRing.injective W L ?_⟩
  rw [map_pow, hs, ht]
  exact (RingHom.congr_fun hc (a k)).symm

theorem exists_form {G X : Type} [CommGroup G] [AddCommGroup X] (v : G →* Multiplicative ℤ) (q : X → X → G)
    (hsym : ∀ x y, q x y = q y x) (hadd : ∀ x x' y, q (x + x') y = q x y * q x' y) :
    ∃ β : LinearMap.BilinForm ℤ X, ∀ x y, β x y = (v (q x y)).toAdd := by
  have hadd' : ∀ x y y', q x (y + y') = q x y * q x y' := fun x y y' => by
    rw [hsym, hadd, hsym y, hsym y']
  let F : X → X →ₗ[ℤ] ℤ := fun x =>
    (AddMonoidHom.mk' (fun y => (v (q x y)).toAdd) fun y y' => by simp [hadd']).toIntLinearMap
  exact ⟨(AddMonoidHom.mk' F fun x x' => LinearMap.ext fun y => by simp [F, hadd]).toIntLinearMap,
    fun x y => rfl⟩

theorem isSymBasis_of_basis {X I : Type} [AddCommGroup X] (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) X)) :
    IsSymBasis fun k => (ε k : LinearMap.BilinForm ℤ X) := by
  refine ⟨fun k => mem_balForms_int.1 (ε k).2, ε.linearIndependent.map' (Submodule.subtype _) (by simp),
    fun β hβ => ?_⟩
  have h := Submodule.mem_map_of_mem (f := (balForms (id : ℤ → ℤ) X).subtype)
    (ε.mem_span ⟨β, mem_balForms_int.2 hβ⟩)
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h

theorem exists_roots_of_periods : ∀ (g n : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → 1 ≤ n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (r : ℕ), r ≤ g → ∀ (q : (Fin r → ℤ) → (Fin r → ℤ) → (FractionRing V)ˣ), (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V, w ≠ 0 ∧ (q a a : FractionRing V) = algebraMap V _ w) → ∃ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))), IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ)) x x) ∧ ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (fK : FractionRing V →+* FractionRing V') (s : Fin m ⊕ Fin N → V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ ∀ a b, fK (q a b : FractionRing V) = ∏ k, algebraMap V' _ (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) := by
  intro g n φ hφ hn V _ _ _ hV hD r hr q hsym hadd hpos
  obtain ⟨-, -, hcomp, hchar⟩ := hV
  obtain ⟨v, hv1, hv2⟩ := exists_ord V
  obtain ⟨β, hβ⟩ := exists_form v q hsym hadd
  have hβs : ∀ x y, β x y = β y x := fun x y => by rw [hβ, hβ, hsym]
  have hβp : ∀ x, x ≠ 0 → 0 < β x x := fun x hx => by
    obtain ⟨w, hw, -, h⟩ := hpos x hx
    rw [hβ]
    exact (hv2 _ w h.symm).2 hw
  have hβn : ∀ x, 0 ≤ β x x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hβp x hx).le
  obtain ⟨m, ga, c, hga, hc, hβc⟩ := GlobalTheory.ConeInterior.exists_pos_comb_int g φ hφ r hr β hβs
    (GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hβs) hβn)
  obtain ⟨N, ε, hε⟩ := hga.basis
  have hεga : ∀ k, (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ)) = ga k := fun k => by rw [hε]
  have hsb := isSymBasis_of_basis ε
  obtain ⟨u, hu, -⟩ := existsUnique_coeff hsb q hsym hadd
  have hβv : ∀ x y, β x y = ∑ j, (c j : ℤ) * ga j x y := fun x y => by
    rw [hβc]; simp [LinearMap.sum_apply]
  have hvu : (fun k => v (u k)) = fun k => Multiplicative.ofAdd (Sum.elim (fun j => (c j : ℤ)) 0 k) := by
    refine eq_of_prod_zpow hsb _ _ fun x y => ?_
    simp_rw [← map_zpow, ← map_prod, ← hu]
    apply Multiplicative.toAdd.injective
    rw [← hβ, hβv, toAdd_prod, Fintype.sum_sum_type]
    simp [hεga, mul_comm]
  have hvk : ∀ k, (v (u k)).toAdd = Sum.elim (fun j => (c j : ℤ)) 0 k := fun k => by
    rw [congrFun hvu k]; rfl
  choose a ha using fun k => hv1 (u k) (by rw [hvk]; cases k <;> simp)
  have ha0 : ∀ k, a k ≠ 0 := fun k h => (u k).ne_zero (by rw [← ha, h, map_zero])
  obtain ⟨W, _, _, _, _, f, s, hinj, hfin, hloc, hs⟩ := exists_nthRoots_ext V a hn
  have hinj' : Function.Injective ((algebraMap W (FractionRing W)).comp f) :=
    (IsFractionRing.injective W _).comp hinj
  have hfK : ∀ b, IsFractionRing.lift (K := FractionRing V) hinj' (algebraMap V _ b) =
      algebraMap W (FractionRing W) (f b) := fun b => IsFractionRing.lift_algebraMap hinj' b
  refine ⟨m, N, ε, by simpa only [hεga] using hga, fun x hx => ?_, W, inferInstance, inferInstance, inferInstance, f,
    IsFractionRing.lift hinj', s, ⟨inferInstance, inferInstance, inferInstance, ?_⟩, inferInstance, hinj, hfin, hloc,
    hfK, fun k => ⟨?_, fun h => ?_⟩, fun k => ?_, fun x y => ?_⟩
  · by_contra h
    push_neg at h
    have h1 := hβp x hx
    rw [hβv] at h1
    exact h1.not_ge (Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (hεga j ▸ h j))
  · exact charZero_of_injective_ringHom hinj
  · have h1 : a (.inl k) ∈ maximalIdeal V := (hv2 _ _ (ha _)).1 (by rw [hvk]; simpa using hc k)
    intro h
    exact h1 (isUnit_of_map_unit f _ (hs _ ▸ h.pow n))
  · refine ha0 (.inl k) (hinj ?_)
    rw [← hs, h, map_zero, zero_pow (by omega)]
  · have h1 : a (.inr k) ∉ maximalIdeal V := fun h => by
      have := (hv2 _ _ (ha _)).2 h
      rw [hvk] at this
      simp at this
    have h2 : IsUnit (s (.inr k) ^ n) := hs _ ▸ (not_not.1 h1 : IsUnit (a (.inr k))).map f
    exact (isUnit_pow_iff (by omega)).1 h2
  · rw [hu, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← ha, hfK, ← hs, map_pow, zpow_mul, zpow_natCast]

end GlobalTheory.PerRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataTautologicalChartOfTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_degFrom_of_trait : ∀ (g : ℕ), 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (b : cycAway n →+* T.V), T.y ≫ F.s = jK T.V ≫ spMap b → ∃ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : T.V →+* V') (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), L.h + L.T.r = g ∧ IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' ∧ DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e := by
  intro g hg φ hφ n hn hodd F T b hb
  have hV : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  let e₀ : (Fin (Module.finrank ℤ T.D.toPre.X) → ℤ) ≃+ T.D.toPre.X :=
    (Module.finBasis ℤ T.D.toPre.X).equivFun.symm.toAddEquiv
  have hc : ∀ a a', T.D.toPre.c (e₀ (a + a')) = T.D.toPre.c (e₀ a) * T.D.toPre.c (e₀ a') := fun a a' => by
    rw [map_add (f := _)]; exact T.D.toPre.c_add _ _
  obtain ⟨L, V₁, _, _, _, f₁, κ₁, e, hLh, hCN₁, hDVR₁, hi₁, hf₁, hl₁, hκ₁, hb₁, B', _, β', β'', β₂, β₂', p₁, p₂, s₁, s₂,
    lb, pts⟩ := GlobalTheory.T.exists_lower_base_of_trait_abelian_part n hn hodd T.V hV inferInstance b T.D.toPre.P _ (fun a => T.D.toPre.c (e₀ a)) hc
  have hr : L.T.r = Module.finrank ℤ T.D.toPre.X := by
    simpa using LinearEquiv.finrank_eq e.toIntLinearEquiv
  have hgen : L.h + L.T.r = g := by rw [hLh, hr]; exact GlobalTheory.Poinc.Trait.dim_add_rank (by omega) F T
  obtain ⟨q, hqs, hqa, hqp, hq⟩ := GlobalTheory.T.exists_pulledBack_periods_basePeriods_constForm n T.V T.D _ e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV inferInstance hCN₁ hDVR₁ hi₁ hf₁
    hl₁ hκ₁ p₁ p₂ s₁ s₂ lb pts
  obtain ⟨m, N, ε, hcone, hdef, V₂, _, _, _, f₂, fK, s, hCN₂, hDVR₂, hi₂, hf₂, hl₂, hfK, hs₁, hs₂, hqs'⟩ :=
    GlobalTheory.PerRoot.exists_roots_of_periods g n φ hφ (by omega) V₁ hCN₁ hDVR₁ L.T.r (by omega) q hqs hqa hqp
  have hl : IsLocalHom (f₂.comp f₁) := RingHom.isLocalHom_comp f₂ f₁
  have hlκ : IsLocalHom (f₂.comp κ₁) := RingHom.isLocalHom_comp f₂ κ₁
  obtain ⟨D', hD, G', _, _, π, A', U', hU⟩ :=
    GlobalTheory.TraitExt.exists_unifAlong_pullTo F T V₂ (f₂.comp f₁) hCN₂ hDVR₂ (hi₂.comp hi₁) (hf₂.comp hf₁) hl
  refine ⟨L, m, N, ε, V₂, inferInstance, inferInstance, inferInstance, f₂.comp f₁, f₂.comp κ₁, s, D',
    hD.xe.trans (e₀.symm.trans e.symm), G', inferInstance, inferInstance, π, A', U', hgen, hcone, hdef, hCN₂, hDVR₂,
    hi₂.comp hi₁, hf₂.comp hf₁, hl, hlκ, ?_, hs₁, hs₂, hU, ?_⟩
  · rw [RingHom.comp_assoc, hb₁, ← RingHom.comp_assoc]
  · exact hq V₂ f₂ fK s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) hCN₂ hi₂ hf₂ hl₂ hfK hqs' D' hD

end GlobalTheory.TChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataTautologicalChartOfTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degeneration_data_tautologicalChart_of_trait : ∀ (g : ℕ), 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (b : cycAway n →+* T.V), T.y ≫ F.s = jK T.V ≫ spMap b → ∃ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : T.V →+* V') (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), L.h + L.T.r = g ∧ IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' ∧ DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e := by
  first | exact @GlobalTheory.TChart.exists_degFrom_of_trait | exact GlobalTheory.TChart.exists_degFrom_of_trait | (intros; apply GlobalTheory.TChart.exists_degFrom_of_trait <;> assumption)
end
