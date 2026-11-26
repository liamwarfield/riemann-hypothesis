module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsStableEigenTangents
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFourth
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSectionsAffineModel
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSectionsAffineModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames.Chart

open GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.LieTangent

theorem ring_eq' {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) [Mono x] (z : Sp ℂ ⟶ X)
    (ψ : R →+* X.presheaf.stalk (centre z)) (hψ : spMap ψ ≫ x = X.fromSpecStalk (centre z)) (f : R →+* ℂ)
    (hf : spMap f ≫ x = z) : (Scheme.stalkClosedPointTo z).hom.comp ψ = f := by
  have h1 : spMap ((Scheme.stalkClosedPointTo z).hom.comp ψ) ≫ x = spMap f ≫ x := by
    have e1 : spMap ((Scheme.stalkClosedPointTo z).hom.comp ψ) =
        spMap (Scheme.stalkClosedPointTo z).hom ≫ spMap ψ := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e1, Category.assoc, hψ, hf]
    exact spec_centre z
  exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))

theorem exists_chart_values : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (A : X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(X, A) EB) (MB : LieModel G hA.fromSpec EB) (e : J → EB), p.1 ∈ A ∧ A ≤ N ∧ ∀ (y : Sp ℂ ⟶ X) (f : Γ(X, A) →+* ℂ), genPt ξ ⤳ centre y → y = spMap f ≫ hA.fromSpec → ∀ (i : J) (w : epsAt y ⟶ G), w.left = spMap (dualMap f) ≫ (MB.pt (e i)).left → M.ValAt y (c i) w := by
  intro X G _ _ _ Ω _ ξ E _ _ M p N J _ c hpN hc
  obtain ⟨R, _, x, _, F, _, _, MR, e, hpx, hxN, hext⟩ := GlobalTheory.T.local_lie_model_extends X G Ω ξ E M p N J c hpN hc
  obtain ⟨_, ⟨A, hA, rfl⟩, hpA, hAx⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hpx x.opensRange.isOpen
  replace hA : IsAffineOpen A := hA
  have hrange : Set.range hA.fromSpec ⊆ Set.range x := by
    rw [hA.range_fromSpec]
    exact hAx
  obtain ⟨a, ha⟩ : ∃ a : R →+* Γ(X, A), spMap a ≫ x = hA.fromSpec :=
    ⟨(Spec.preimage (IsOpenImmersion.lift x hA.fromSpec hrange)).hom, by
      change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x _ hrange)).hom) ≫ x = _
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  obtain ⟨EB, iEB, mEB, ⟨MB⟩⟩ := lieModel_exists X G Γ(X, A) hA.fromSpec
  have hex : ∀ i, ∃ b, MB.pt b = epsBase a ha ≫ MR.pt (e i) := fun i =>
    MB.onto _ (isTanAt_base a ha (MR.tan _))
  choose eB heB using hex
  refine ⟨A, hA, EB, iEB, mEB, MB, eB, hpA, fun t ht => hxN (hAx ht), ?_⟩
  intro y f hg hy i w hw
  let q : Cpt ξ := ⟨centre y, hg⟩
  have hqr : q.1 ∈ x.opensRange := by
    refine hrange ⟨spMap f (IsLocalRing.closedPoint ℂ), ?_⟩
    change _ = centre y
    simp only [centre, hy, Scheme.Hom.comp_apply]
    rfl
  have hqx : (X.fromSpecStalk q.1) (IsLocalRing.closedPoint (X.presheaf.stalk q.1)) ∈ x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hqr
  obtain ⟨ψ, hψ⟩ := exists_lift (A := X.presheaf.stalk q.1) x (X.fromSpecStalk q.1) hqx
  have hring : (Scheme.stalkClosedPointTo y).hom.comp ψ = f.comp a := by
    refine ring_eq' x y ψ hψ _ ?_
    have e2 : spMap (f.comp a) = spMap f ≫ spMap a := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e2, Category.assoc, ha, hy]
  let vq : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G := epsBase ψ hψ ≫ MR.pt (e i)
  refine ⟨hg, vq, hext q ψ hψ i vq rfl, ?_⟩
  rw [hw, heB]
  change spMap (dualMap f) ≫ spMap (dualMap a) ≫ (MR.pt (e i)).left =
    spMap (dualMap (Scheme.stalkClosedPointTo y).hom) ≫ spMap (dualMap ψ) ≫ (MR.pt (e i)).left
  rw [← Category.assoc, ← Category.assoc, spMap_dual_comp, spMap_dual_comp, hring]

end GlobalTheory.CompanionTheory.Ar.LocFrames.Chart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSectionsAffineModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sections_affine_model : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (A : X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(X, A) EB) (MB : LieModel G hA.fromSpec EB) (e : J → EB), p.1 ∈ A ∧ A ≤ N ∧ ∀ (y : Sp ℂ ⟶ X) (f : Γ(X, A) →+* ℂ), genPt ξ ⤳ centre y → y = spMap f ≫ hA.fromSpec → ∀ (i : J) (w : epsAt y ⟶ G), w.left = spMap (dualMap f) ≫ (MB.pt (e i)).left → M.ValAt y (c i) w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.Chart.exists_chart_values | exact GlobalTheory.CompanionTheory.Ar.LocFrames.Chart.exists_chart_values | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.Chart.exists_chart_values <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentComplexPointTangents
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentComplexPointTangents
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue

section Linear

theorem sum_smul_comb {R U : Type} [CommRing R] [AddCommGroup U] [Module R U] {n r : ℕ}
    (C : Matrix (Fin n) (Fin r) R) (b : Fin r → U) (a : Fin n → R) :
    ∑ i, a i • ∑ k, C i k • b k = ∑ k, (Matrix.vecMul a C) k • b k := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.vecMul, dotProduct, Finset.sum_smul]

theorem coef_eq {R U : Type} [CommRing R] [AddCommGroup U] [Module R U] {n : ℕ} {x : Fin n → U}
    (hx : LinearIndependent R x) (i : Fin n) (c : Fin n → R) (h : x i = ∑ l, c l • x l) :
    c = Pi.single i 1 := by
  funext l
  have h0 : ∑ m, (c m - (Pi.single i 1 : Fin n → R) m) • x m = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← h, Pi.single_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hx _ h0 l)

variable {A Ω T F V N : Type} [CommRing A] [Field Ω] [CommRing T] [AddCommGroup F] [Module A F]
  [AddCommGroup V] [Module Ω V] [AddCommGroup N] [Module T N]

theorem exists_coef {g : A →+* Ω} (j : F →ₛₗ[g] V) (hj : Function.Injective j) {r : ℕ} (f : Fin r → F) (e : F)
    (h : j e ∈ Submodule.span g.range (Set.range fun k => j (f k))) : ∃ C : Fin r → A, e = ∑ k, C k • f k := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
  choose C hC using fun k => (a k).2
  refine ⟨C, hj ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← ha, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [j.map_smulₛₗ, hC]
  rfl

theorem frame_change {g : A →+* Ω} (hg : Function.Injective g) {θ : A →+* T} (j : F →ₛₗ[g] V)
    (hj : Function.Injective j) (jy : F →ₛₗ[θ] N) {r n : ℕ} (f : Fin r → F) (e : Fin n → F)
    (hf : LinearIndependent Ω fun k => j (f k)) (he : LinearIndependent Ω fun i => j (e i))
    (hs : Submodule.span g.range (Set.range fun k => j (f k)) = Submodule.span g.range (Set.range fun i => j (e i)))
    (hu : LinearIndependent T fun k => jy (f k)) :
    LinearIndependent T (fun i => jy (e i)) ∧
      Submodule.span T (Set.range fun i => jy (e i)) = Submodule.span T (Set.range fun k => jy (f k)) := by
  choose C hC using fun i => exists_coef j hj f (e i) (hs ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose D hD using fun k => exists_coef j hj e (f k) (hs.symm ▸ Submodule.subset_span ⟨k, rfl⟩)
  let Cm : Matrix (Fin n) (Fin r) A := Matrix.of C
  let Dm : Matrix (Fin r) (Fin n) A := Matrix.of D
  have key : ∀ {a b : ℕ} (x : Fin a → F) (P : Matrix (Fin a) (Fin b) A) (Q : Matrix (Fin b) (Fin a) A) (y : Fin b → F),
      LinearIndependent Ω (fun i => j (x i)) → (∀ i, x i = ∑ k, P i k • y k) → (∀ k, y k = ∑ i, Q k i • x i) →
      P * Q = 1 := by
    intro a b x P Q y hx hP hQ
    ext i l
    have h1 : x i = ∑ m, (Matrix.vecMul (P i) Q) m • x m := by
      rw [← sum_smul_comb]
      conv_lhs => rw [hP i]
      exact Finset.sum_congr rfl fun k _ => by rw [hQ k]
    have h2 : j (x i) = ∑ m, g ((Matrix.vecMul (P i) Q) m) • j (x m) := by
      conv_lhs => rw [h1]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun m _ => j.map_smulₛₗ _ _
    have h3 := congrFun (coef_eq hx i _ h2) l
    have h4 : (Matrix.vecMul (P i) Q) l = (1 : Matrix (Fin a) (Fin a) A) i l := by
      apply hg
      rw [h3, Matrix.one_apply, Pi.single_apply]
      by_cases hh : i = l
      · simp [hh]
      · simp [hh, Ne.symm hh]
    rw [← h4, Matrix.mul_apply]
    simp only [Matrix.vecMul, dotProduct]
  have hCD : Cm * Dm = 1 := key e Cm Dm f he hC hD
  have hDC : Dm * Cm = 1 := key f Dm Cm e hf hD hC
  have hCDt : Cm.map θ * Dm.map θ = 1 := by
    rw [← Matrix.map_mul, hCD, Matrix.map_one _ (map_zero θ) (map_one θ)]
  have hDCt : Dm.map θ * Cm.map θ = 1 := by
    rw [← Matrix.map_mul, hDC, Matrix.map_one _ (map_zero θ) (map_one θ)]
  have hw : ∀ i, jy (e i) = ∑ k, (Cm.map θ) i k • jy (f k) := fun i => by
    conv_lhs => rw [hC i]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => jy.map_smulₛₗ _ _
  have hv : ∀ k, jy (f k) = ∑ i, (Dm.map θ) k i • jy (e i) := fun k => by
    conv_lhs => rw [hD k]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => jy.map_smulₛₗ _ _
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro a ha i
    simp_rw [hw] at ha
    rw [sum_smul_comb] at ha
    have h0 : Matrix.vecMul a (Cm.map θ) = 0 := by
      funext k
      exact Fintype.linearIndependent_iff.1 hu _ ha k
    have h1 : a = Matrix.vecMul (Matrix.vecMul a (Cm.map θ)) (Dm.map θ) := by
      rw [Matrix.vecMul_vecMul, hCDt, Matrix.vecMul_one]
    rw [h1, h0, Matrix.zero_vecMul]
    rfl
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show jy (e i) ∈ _
    rw [hw i]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    show jy (f k) ∈ _
    rw [hv k]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Linear

section Lie

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

theorem isEigFrame_of_frames {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {Ω : Type} [Field Ω]
    {ξ : Sp Ω ⟶ X} {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (p : Cpt ξ)
    (hinj : Function.Injective (genMap ξ p)) {T : Type} [CommRing T] (θ : X.presheaf.stalk p.1 →+* T) (y : Sp T ⟶ X)
    (hy : spMap θ ≫ X.fromSpecStalk p.1 = y) {Oe : Type} [CommRing Oe] (act : OAct Oe G) (τ : Oe →+* T) {r n : ℕ}
    (e : Fin r → (epsAt (X.fromSpecStalk p.1) ⟶ G)) (e' : Fin n → (epsAt (X.fromSpecStalk p.1) ⟶ G))
    (b : Fin r → V) (v : Fin n → V) (w : Fin n → (epsAt y ⟶ G))
    (hb : ∀ k, M.Extends p (b k) (e k)) (hv : ∀ i, M.Extends p (v i) (e' i))
    (hw : ∀ i, (w i).left = spMap (dualMap θ) ≫ (e' i).left)
    (hbl : LinearIndependent Ω b) (hvl : LinearIndependent Ω v)
    (hs : Submodule.span (regAt ξ p) (Set.range b) = Submodule.span (regAt ξ p) (Set.range v))
    (hu : ∀ u : Fin r → (epsAt y ⟶ G), (∀ k, (u k).left = spMap (dualMap θ) ≫ (e k).left) → IsEigFrame act y τ u) :
    IsEigFrame act y τ w := by
  obtain ⟨F, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk p.1) (X.fromSpecStalk p.1)
  obtain ⟨N, _, _, ⟨My⟩⟩ := lieModel_exists X G T y
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act X G T y N My Oe act.act act.hom act.one act.mul act.add
  obtain ⟨j, hj⟩ := exists_tr (A := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ξ (genMap ξ p) (spec_genMap ξ p) MA M
  obtain ⟨jy, hjy⟩ := exists_tr (A := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) y θ hy MA My
  choose f hf using fun k => MA.onto (e k) (hb k).1
  choose g hg using fun i => MA.onto (e' i) (hv i).1
  have hji : Function.Injective j := fun a a' h => MA.inj (tan_ext hinj (MA.tan a) (MA.tan a') (by
    rw [← hj, ← hj, h]))
  have hjf : ∀ k, j (f k) = b k := fun k => pt_left_inj M (by rw [hj, hf]; exact (hb k).2.symm)
  have hjg : ∀ i, j (g i) = v i := fun i => pt_left_inj M (by rw [hj, hg]; exact (hv i).2.symm)
  have hfr := ((GlobalTheory.T.lie_model_eigenvectors_action X T G y N My).2 Oe act ρ τ hρ).2
  obtain ⟨hul, hus⟩ := (hfr r _).1 (hu (fun k => My.pt (jy (f k))) fun k => by rw [hjy, hf])
  have hfb : (fun k => j (f k)) = b := funext hjf
  have hgv : (fun i => j (g i)) = v := funext hjg
  obtain ⟨h1, h2⟩ := frame_change hinj j hji jy f g (by rw [hfb]; exact hbl) (by rw [hgv]; exact hvl)
    (by rw [hfb, hgv]; exact hs) hul
  have hwe : w = fun i => My.pt (jy (g i)) := funext fun i => Over.OverMorphism.ext (by
    rw [hjy, hg, hw])
  rw [hwe]
  exact (hfr n _).2 ⟨h1, h2.trans hus⟩

end Lie

section Point

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.Flat.EigVb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}

theorem centre_mem_genFib (Z : CptOver Y U) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Y.X) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y)
    (hy : y ≫ Y.s = spMap (σ.comp β)) : (⟨centre y, h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := by
  have hc : y ≫ Y.s = spMap σ ≫ spMap β := by
    rw [hy]
    exact (spec_comp β σ).symm
  refine ⟨pullback.lift y (spMap σ) hc (IsLocalRing.closedPoint ℂ), ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  rfl

theorem exists_coeff_map (Z : CptOver Y U) (hβ : Function.Injective β)
    (hfr : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (p : Cpt (Z.ξ₀ ≫ Y.j)) (hp : p ∈ Z.genFib) :
    ∃ κ : c.F →+* Y.X.presheaf.stalk p.1, (genMap (Z.ξ₀ ≫ Y.j) p).comp κ = Z.inc := by
  have hm : ∀ x, Z.inc x ∈ (genMap (Z.ξ₀ ≫ Y.j) p).range := inc_mem_regAt Z hβ hfr p hp
  let e := RingEquiv.ofBijective (genMap (Z.ξ₀ ≫ Y.j) p).rangeRestrict
    ⟨fun a b h => Z.gen.inj p (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  refine ⟨(e.symm : _ →+* _).comp (Z.inc.codRestrict _ hm), RingHom.ext fun x => ?_⟩
  have h1 := e.apply_symm_apply (Z.inc.codRestrict _ hm x)
  exact congrArg Subtype.val h1

theorem comp_coeff_map (Z : CptOver Y U) (hfr : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (p : Cpt (Z.ξ₀ ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk p.1) (hκ : (genMap (Z.ξ₀ ≫ Y.j) p).comp κ = Z.inc)
    (θ : Y.X.presheaf.stalk p.1 →+* ℂ) (σ : c.F →+* ℂ) (hy : (spMap θ ≫ Y.X.fromSpecStalk p.1) ≫ Y.s = spMap (σ.comp β)) :
    θ.comp κ = σ := by
  let t : Spec (Y.X.presheaf.stalk p.1) ⟶ Spec (CommRingCat.of O) := Y.X.fromSpecStalk p.1 ≫ Y.s
  let θ₀ : O →+* Y.X.presheaf.stalk p.1 := (Spec.preimage t).hom
  have ht : Spec.map (CommRingCat.ofHom θ₀) = t := by
    simp only [θ₀, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hg : (genMap (Z.ξ₀ ≫ Y.j) p).comp θ₀ = Z.inc.comp β := by
    refine LieVB.spec_cancel (𝟙 _) ?_
    rw [Category.comp_id, Category.comp_id, ← LieVB.spec_comp', ht]
    refine Eq.trans ?_ (gen_over Z)
    show _ ≫ Y.X.fromSpecStalk p.1 ≫ Y.s = _
    rw [← Category.assoc, LieCarrier.genMap_fromSpecStalk p]
  have hκβ : ∀ o, κ (β o) = θ₀ o := fun o => Z.gen.inj p (by
    have h1 := congrArg (fun f : c.F →+* Z.Ω => f (β o)) hκ
    have h2 := congrArg (fun f : O →+* Z.Ω => f o) hg
    exact h1.trans h2.symm)
  have hθ : θ.comp θ₀ = σ.comp β := by
    have h1 : Spec.map (CommRingCat.ofHom (θ.comp θ₀)) = Spec.map (CommRingCat.ofHom (σ.comp β)) := by
      rw [← spec_comp, ht]
      exact (Category.assoc _ _ _).symm.trans hy
    exact congrArg (fun f => f.hom) (Spec.map_injective h1)
  have hv : ∀ o, θ (κ (β o)) = σ (β o) := fun o => by
    rw [hκβ]
    exact congrArg (fun f : O →+* ℂ => f o) hθ
  refine RingHom.ext fun x => ?_
  obtain ⟨a, b, hb, hx⟩ := hfr x
  have hne : σ (β b) ≠ 0 := (map_ne_zero σ).2 hb
  refine mul_right_cancel₀ hne ?_
  show θ (κ x) * σ (β b) = σ x * σ (β b)
  rw [← hv b, ← map_mul, ← map_mul, hx, hv a, hv b, ← map_mul, hx]

theorem isEigFrame_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (n : ℕ) (v : Fin n → Z.V) (y : Sp ℂ ⟶ Y.X) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y) (w : Fin n → (epsAt y ⟶ Y.t.G)), Function.Injective β → (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ Y.s = spMap (σ.comp β) → (Z.eig τ).IsFrameAt v ⟨centre y, h⟩ → (∀ i, Z.M.ValAt y (v i) (w i)) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) w := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ n v y h w hβ hfr hy hv hw
  have hq := centre_mem_genFib Z σ y h hy
  obtain ⟨κ, hκ⟩ := exists_coeff_map Z hβ hfr ⟨centre y, h⟩ hq
  have hs : spMap (Scheme.stalkClosedPointTo y).hom ≫ Y.X.fromSpecStalk (centre y) = y := spec_centre y
  have hθ := comp_coeff_map Z hfr ⟨centre y, h⟩ κ hκ (Scheme.stalkClosedPointTo y).hom σ (by
    show (spMap (Scheme.stalkClosedPointTo y).hom ≫ Y.X.fromSpecStalk (centre y)) ≫ Y.s = _
    rw [hs, hy])
  obtain ⟨r, e, he⟩ := GlobalTheory.T.exists_stable_eigen_tangents E H l c Y.X Y.t (Y.X.presheaf.stalk (centre y)) (Y.X.fromSpecStalk (centre y)) κ τ
  obtain ⟨b, hb, hbf⟩ := GlobalTheory.T.stable_eigen_at_component_stalk E H D l Xo c U O β Y Z ⟨centre y, h⟩ κ τ r e hκ he
  choose h' e' hE hwe using hw
  refine isEigFrame_of_frames Z.M ⟨centre y, h⟩ (Z.gen.inj _) (Scheme.stalkClosedPointTo y).hom y hs Y.t.act _ e e' b v w
    hb hE hwe hbf.1 hv.1 (hbf.2.symm.trans hv.2) fun u hu => ?_
  have := he ℂ (Scheme.stalkClosedPointTo y).hom y hs u hu
  rwa [hθ] at this

end Point

end GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentComplexPointTangentsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_complex_point_tangents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (n : ℕ) (v : Fin n → Z.V) (y : Sp ℂ ⟶ Y.X) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y) (w : Fin n → (epsAt y ⟶ Y.t.G)), Function.Injective β → (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ Y.s = spMap (σ.comp β) → (Z.eig τ).IsFrameAt v ⟨centre y, h⟩ → (∀ i, Z.M.ValAt y (v i) (w i)) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue.isEigFrame_value | exact GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue.isEigFrame_value | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue.isEigFrame_value <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameOpenCondition
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameOpenCondition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieVB

open GlobalTheory.CompanionTheory.Ar.LieTangent

theorem exists_open_forall {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (p : Cpt ξ) {I : Type} [Finite I]
    (P : I → Cpt ξ → Prop) (h : ∀ i, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → P i q) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i, P i q := by
  classical
  have := Fintype.ofFinite I
  have key : ∀ s : Finset I, ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ∀ i ∈ s, P i q := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨⊤, trivial, fun _ _ i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert a s _ ih =>
      obtain ⟨U, hU, HU⟩ := ih
      obtain ⟨V, hV, HV⟩ := h a
      refine ⟨U ⊓ V, ⟨hU, hV⟩, fun q hq i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact HV q hq.2
      · exact HU q hq.1 i hi
  obtain ⟨U, hU, HU⟩ := key Finset.univ
  exact ⟨U, hU, fun q hq i => HU q hq i (Finset.mem_univ i)⟩

theorem exists_open_mem_span {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {E : Type} [AddCommGroup E]
    [Module Ω E] (p : Cpt ξ) {n : ℕ} (w : Fin n → E) (e : E)
    (he : e ∈ Submodule.span (regAt ξ p) (Set.range w)) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → e ∈ Submodule.span (regAt ξ q) (Set.range w) := by
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
  obtain ⟨U, hU, HU⟩ := exists_open_forall p (fun (j : Fin n) (q : Cpt ξ) => (f j : Ω) ∈ regAt ξ q)
    fun j => exists_open_mem_regAt ξ p _ (f j).2
  refine ⟨U, hU, fun q hq => ?_⟩
  refine Submodule.sum_mem _ fun j _ => ?_
  have : f j • w j = (⟨(f j : Ω), HU q hq j⟩ : regAt ξ q) • w j := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem mem_span_field_of_mem_span_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X) {E : Type}
    [AddCommGroup E] [Module Ω E] (p : Cpt ξ) {n : ℕ} (w : Fin n → E) (e : E)
    (he : e ∈ Submodule.span (regAt ξ p) (Set.range w)) : e ∈ Submodule.span Ω (Set.range w) := by
  obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
  refine Submodule.sum_mem _ fun j _ => ?_
  have : f j • w j = (f j : Ω) • w j := rfl
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem isFrameAt_span_and_nhd : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E), M.lat.IsFrameAt b p → Submodule.span Ω (Set.range b) = ⊤ ∧ ∃ N : X.Opens, p.1 ∈ N ∧ ∀ q : Cpt ξ, q.1 ∈ N → M.lat.IsFrameAt b q := by
  intro X G _ _ _ Ω _ ξ E _ _ M p g b hb
  obtain ⟨R, _, x, hx, F, _, _, MR, n, bR, hp⟩ := exists_chart G p.1
  have hgen : genPt ξ ∈ x.opensRange := p.2.mem_open x.opensRange.isOpen hp
  obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
  obtain ⟨c, hli, hsp, hfr⟩ := frame_of_basis x MR bR ξ M φ hφ
  have hc : ∀ q : Cpt ξ, q.1 ∈ x.opensRange → M.lat.IsFrameAt c q := by
    intro q hq
    have hq' : (X.fromSpecStalk q.1) (IsLocalRing.closedPoint (X.presheaf.stalk q.1)) ∈ x.opensRange := by
      rw [Scheme.fromSpecStalk_closedPoint]
      exact hq
    obtain ⟨ψ, hψ⟩ := exists_lift (A := X.presheaf.stalk q.1) x (X.fromSpecStalk q.1) hq'
    refine hfr q ψ hψ ?_
    have h1 : spMap ((genMap ξ q).comp ψ) ≫ x = spMap φ ≫ x := by
      have e1 : spMap ((genMap ξ q).comp ψ) = spMap (genMap ξ q) ≫ spMap ψ := by
        simp only [spMap, ← Spec.map_comp]
        rfl
      calc spMap ((genMap ξ q).comp ψ) ≫ x = spMap (genMap ξ q) ≫ spMap ψ ≫ x := by
            rw [e1, Category.assoc]
        _ = spMap (genMap ξ q) ≫ X.fromSpecStalk q.1 := by rw [hψ]
        _ = ξ := spec_genMap ξ q
        _ = spMap φ ≫ x := hφ.symm
    have h2 := Spec.map_injective ((cancel_mono x).1 h1)
    exact congrArg (fun g => g.hom) h2
  have hbc : Submodule.span (regAt ξ p) (Set.range b) = Submodule.span (regAt ξ p) (Set.range c) :=
    hb.2.symm.trans (hc p hp).2
  have hbi : ∀ i, b i ∈ Submodule.span (regAt ξ p) (Set.range c) := fun i => by
    rw [← hbc]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hcj : ∀ j, c j ∈ Submodule.span (regAt ξ p) (Set.range b) := fun j => by
    rw [hbc]
    exact Submodule.subset_span ⟨j, rfl⟩
  refine ⟨top_le_iff.1 (hsp.ge.trans (Submodule.span_le.2 ?_)), ?_⟩
  · rintro _ ⟨j, rfl⟩
    exact mem_span_field_of_mem_span_regAt ξ p b _ (hcj j)
  obtain ⟨U, hU, HU⟩ := exists_open_forall p
    (fun (i : Fin g) (q : Cpt ξ) => b i ∈ Submodule.span (regAt ξ q) (Set.range c))
    fun i => exists_open_mem_span ξ p c _ (hbi i)
  obtain ⟨V, hV, HV⟩ := exists_open_forall p
    (fun (j : Fin n) (q : Cpt ξ) => c j ∈ Submodule.span (regAt ξ q) (Set.range b))
    fun j => exists_open_mem_span ξ p b _ (hcj j)
  refine ⟨x.opensRange ⊓ (U ⊓ V), ⟨hp, hU, hV⟩, fun q hq => ⟨hb.1, ?_⟩⟩
  rw [(hc q hq.1).2]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨j, rfl⟩
    exact HV q hq.2.2 j
  · rintro _ ⟨i, rfl⟩
    exact HU q hq.2.1 i

end GlobalTheory.CompanionTheory.Ar.LieVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameOpenConditionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frame_open_condition : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E), M.lat.IsFrameAt b p → Submodule.span Ω (Set.range b) = ⊤ ∧ ∃ N : X.Opens, p.1 ∈ N ∧ ∀ q : Cpt ξ, q.1 ∈ N → M.lat.IsFrameAt b q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieVB.isFrameAt_span_and_nhd | exact GlobalTheory.CompanionTheory.Ar.LieVB.isFrameAt_span_and_nhd | (intros; apply GlobalTheory.CompanionTheory.Ar.LieVB.isFrameAt_span_and_nhd <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineDomainGenericSpecializes
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineDomainGenericSpecializes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames

theorem mem_prime_germ_eq_zero {X : Scheme.{0}} {A : X.Opens} (hA : IsAffineOpen A) (x : A)
    (hF : IsField (X.presheaf.stalk x.1)) (f : Γ(X, A)) (hf : f ∈ (hA.primeIdealOf x).asIdeal) :
    X.presheaf.germ A x.1 x.2 f = 0 := by
  have hl := hA.isLocalization_stalk x
  have h1 : algebraMap Γ(X, A) (X.presheaf.stalk x.1) f ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x.1) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x.1)
      (hA.primeIdealOf x).asIdeal f).2 hf
  have h2 : ¬ IsUnit (algebraMap Γ(X, A) (X.presheaf.stalk x.1) f) := h1
  by_contra h0
  exact h2 (by
    let _ := hF.toField
    exact IsUnit.mk0 _ h0)

theorem germ_injective {X : Scheme.{0}} {A : X.Opens} (hA : IsAffineOpen A) [IsDomain Γ(X, A)] (x : A) :
    Function.Injective (X.presheaf.germ A x.1 x.2) := by
  have hl := hA.isLocalization_stalk x
  exact IsLocalization.injective (X.presheaf.stalk x.1)
    (M := (hA.primeIdealOf x).asIdeal.primeCompl)
    ((hA.primeIdealOf x).asIdeal.primeCompl_le_nonZeroDivisors)

theorem genPt_specializes_of_isDomain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (A : X.Opens) (hA : IsAffineOpen A) (p : Cpt ξ), IsCptGen ξ → IsDomain Γ(X, A) → p.1 ∈ A → ∀ z ∈ A, genPt ξ ⤳ z := by
  intro X Ω _ ξ A hA p hgen hdom hp z hz
  have hx : genPt ξ ∈ A := p.2.mem_open A.2 hp
  let x : A := ⟨genPt ξ, hx⟩
  let q : A := ⟨p.1, hp⟩
  have hF : IsField (X.presheaf.stalk x.1) :=
    MulEquiv.isField (Field.toIsField Ω) (RingEquiv.ofBijective _ hgen.bij).toMulEquiv
  have hbot : (hA.primeIdealOf x).asIdeal = ⊥ := by
    refine le_antisymm (fun f hf => ?_) bot_le
    have h0 := mem_prime_germ_eq_zero hA x hF f hf
    have h1 : X.presheaf.germ A p.1 hp f = 0 := by
      apply hgen.inj p
      have h2 : X.presheaf.stalkSpecializes p.2 (X.presheaf.germ A p.1 hp f) =
          X.presheaf.germ A (genPt ξ) hx f := by
        exact congr($(X.presheaf.germ_stalkSpecializes hp p.2).hom f)
      rw [map_zero]
      change (Scheme.stalkClosedPointTo ξ).hom
        (X.presheaf.stalkSpecializes p.2 (X.presheaf.germ A p.1 hp f)) = 0
      rw [h2]
      have h3 : X.presheaf.germ A (genPt ξ) hx f = 0 := h0
      rw [h3]
      exact map_zero (Scheme.stalkClosedPointTo ξ).hom
    exact germ_injective hA q (h1.trans (map_zero _).symm)
  obtain ⟨t, rfl⟩ : z ∈ Set.range hA.fromSpec := by rwa [hA.range_fromSpec]
  have hs : hA.primeIdealOf x ⤳ t := by
    refine (PrimeSpectrum.le_iff_specializes (hA.primeIdealOf x) t).1 ?_
    change (hA.primeIdealOf x).asIdeal ≤ _
    rw [hbot]
    exact bot_le
  have := hs.map hA.fromSpec.continuous
  rwa [hA.fromSpec_primeIdealOf] at this

end GlobalTheory.CompanionTheory.Ar.LocFrames
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineDomainGenericSpecializesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_domain_generic_specializes : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (A : X.Opens) (hA : IsAffineOpen A) (p : Cpt ξ), IsCptGen ξ → IsDomain Γ(X, A) → p.1 ∈ A → ∀ z ∈ A, genPt ξ ⤳ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain | exact GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.genPt_specializes_of_isDomain <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSubBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSubBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.SubFrame

theorem isFrameAt_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (q : Cpt ξ) (g n : ℕ) (b : Fin g → E) (ix : Fin n → Fin g), Function.Injective ix → LinearIndependent Ω b → L q = Submodule.span (regAt ξ q) (Set.range b) → V' = Submodule.span Ω (Set.range (b ∘ ix)) → (L.inter V').IsFrameAt (b ∘ ix) q := by
  intro X Ω _ ξ E _ _ L V' q g n b ix hix hb hL hV
  subst hV
  refine And.intro (hb.comp ix hix) ?_
  show L q ⊓ Submodule.restrictScalars (regAt ξ q) (Submodule.span Ω (Set.range (b ∘ ix))) = _
  rw [hL]
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have hx2' : x ∈ Submodule.span Ω (Set.range (b ∘ ix)) := hx2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx1
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 hx2'
    have hc' : ∑ i, (c i : Ω) • b i = x := hc
    have hD : ∑ i, (∑ j, if ix j = i then d j else 0) • b i = x := by
      rw [← hd]
      simp only [Finset.sum_smul, ite_smul, zero_smul]
      rw [Finset.sum_comm]
      simp [Finset.sum_ite_eq]
    have key : ∀ i, (c i : Ω) = ∑ j, if ix j = i then d j else 0 := by
      have h0 := Fintype.linearIndependent_iff.1 hb
        (fun i => (c i : Ω) - ∑ j, if ix j = i then d j else 0) (by
          simp only [sub_smul, Finset.sum_sub_distrib]
          rw [hc', hD, sub_self])
      intro i
      exact sub_eq_zero.1 (h0 i)
    rw [← hc]
    apply Submodule.sum_mem
    intro i _
    by_cases h : ∃ j, ix j = i
    · obtain ⟨j, rfl⟩ := h
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simp only [not_exists] at h
      have hci : c i = 0 := by
        apply Subtype.ext
        rw [key i]
        simp [h]
      rw [hci, zero_smul]
      exact Submodule.zero_mem _
  · apply le_inf
    · exact Submodule.span_mono (Set.range_comp_subset_range _ _)
    · exact Submodule.span_le_restrictScalars _ _ _

end GlobalTheory.CompanionTheory.Ar.SubFrame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSubBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frame_sub_basis : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (q : Cpt ξ) (g n : ℕ) (b : Fin g → E) (ix : Fin n → Fin g), Function.Injective ix → LinearIndependent Ω b → L q = Submodule.span (regAt ξ q) (Set.range b) → V' = Submodule.span Ω (Set.range (b ∘ ix)) → (L.inter V').IsFrameAt (b ∘ ix) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp | exact GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.SubFrame.isFrameAt_comp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeIntersectionFrameSubspace
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeIntersectionFrameSubspace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.LocalFrames

theorem span_eq_of_saturated : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E) (S : Finset (Fin g)), IsCptGen ξ → Submodule.span Ω (Set.range b) = ⊤ → L p = Submodule.span (regAt ξ p) (Set.range b) → (L.inter V') p = Submodule.span (regAt ξ p) (b '' S) → V' = Submodule.span Ω (b '' S) := by
  intro X Ω _ ξ E _ _ L V' p g b S h hspan hL hI
  haveI hfr : IsFractionRing (regAt ξ p) Ω := (RegAtRing.regAt_ring X Ω ξ h p).1
  have sm : ∀ (c : regAt ξ p) {m : E}, m ∈ L p → (c : Ω) • m ∈ L p := fun c _ hm => (L p).smul_mem c hm
  have key : ∀ x : E, ∃ d : regAt ξ p, (d : Ω) ≠ 0 ∧ (d : Ω) • x ∈ L p := by
    intro x
    have hx : x ∈ Submodule.span Ω (Set.range b) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      refine ⟨1, by simp, ?_⟩
      rw [hL]
      simpa using Submodule.subset_span hy
    | zero => exact ⟨1, by simp, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨d, hd, hdy⟩ := hy
      obtain ⟨e, he, hez⟩ := hz
      refine ⟨d * e, by rw [Subring.coe_mul]; exact mul_ne_zero hd he, ?_⟩
      have : ((d * e : regAt ξ p) : Ω) • (y + z) = (e : Ω) • ((d : Ω) • y) + (d : Ω) • ((e : Ω) • z) := by
        simp only [Subring.coe_mul, smul_add, smul_smul, mul_comm]
      rw [this]
      exact (L p).add_mem (sm e hdy) (sm d hez)
    | smul a y _ hy =>
      obtain ⟨d, hd, hdy⟩ := hy
      obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
      have hv0 : (v : Ω) ≠ 0 := by
        have := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := Ω) hv
        simpa using this
      refine ⟨v * d, by rw [Subring.coe_mul]; exact mul_ne_zero hv0 hd, ?_⟩
      have : ((v * d : regAt ξ p) : Ω) • ((algebraMap (regAt ξ p) Ω u / algebraMap (regAt ξ p) Ω v) • y) =
          (u : Ω) • ((d : Ω) • y) := by
        have hu : algebraMap (regAt ξ p) Ω u = (u : Ω) := rfl
        have hv' : algebraMap (regAt ξ p) Ω v = (v : Ω) := rfl
        rw [hu, hv', smul_smul, smul_smul, Subring.coe_mul]
        congr 1
        field_simp
      rw [this]
      exact sm u hdy
  apply le_antisymm
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := key x
    have h1 : (d : Ω) • x ∈ (L.inter V') p := ⟨hdx, V'.smul_mem _ hx⟩
    rw [hI] at h1
    have h2 : (d : Ω) • x ∈ Submodule.span Ω (b '' S) :=
      Submodule.span_subset_span (regAt ξ p) Ω (b '' S) h1
    exact (Submodule.smul_mem_iff _ hd).1 h2
  · rw [Submodule.span_le]
    intro y hy
    have h1 : y ∈ (L.inter V') p := by
      rw [hI]
      exact Submodule.subset_span hy
    exact h1.2

end GlobalTheory.CompanionTheory.Ar.LocalFrames
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeIntersectionFrameSubspaceStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_intersection_frame_subspace : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (V' : Submodule Ω E) (p : Cpt ξ) (g : ℕ) (b : Fin g → E) (S : Finset (Fin g)), IsCptGen ξ → Submodule.span Ω (Set.range b) = ⊤ → L p = Submodule.span (regAt ξ p) (Set.range b) → (L.inter V') p = Submodule.span (regAt ξ p) (b '' S) → V' = Submodule.span Ω (b '' S) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocalFrames.span_eq_of_saturated | exact GlobalTheory.CompanionTheory.Ar.LocalFrames.span_eq_of_saturated | (intros; apply GlobalTheory.CompanionTheory.Ar.LocalFrames.span_eq_of_saturated <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameAtComponentPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames

theorem exists_affine_eigenframes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (p₀ : Cpt (Z.ξ₀ ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → p₀ ∈ Z.genFib → ∃ (A : Y.X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(Y.X, A) EB) (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB) (e₂ : Fin D.q → EB) (v₁ : Fin D.p → Z.V) (v₂ : Fin D.q → Z.V), p₀.1 ∈ A ∧ (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 ∈ A → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧ IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → (∀ i, Z.M.ValAt y (v₁ i) (v i)) ∧ ∀ j, Z.M.ValAt y (v₂ j) (w j)) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ b₁ b₂ p₀ hO hτ h1 h2 h3 h4 hp₀
  obtain ⟨hinj, hnoeth, hfr⟩ := hO
  haveI := hnoeth
  have := projProper _ _ _ Y.proj
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨-, -, h3c, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ ⟨hinj, hnoeth, hfr⟩ hτ
  obtain ⟨g, b, hb, hS⟩ := h3c p₀ hp₀
  obtain ⟨S₁, hS₁⟩ := hS τ
  obtain ⟨S₂, hS₂⟩ := hS (ComplexEmbedding.conjugate τ)
  obtain ⟨hspan, N, hpN, hN⟩ := GlobalTheory.T.lattice_frame_open_condition Y.X Y.t.G Z.Ω _ Z.V Z.M p₀ g b hb
  have e₁ := GlobalTheory.T.lattice_intersection_frame_subspace Y.X Z.Ω _ Z.V Z.M.lat (eigSp Z.ρ (Z.inc.comp (tauIn c τ))) p₀ g b S₁ Z.gen hspan hb.2 hS₁
  have e₂ := GlobalTheory.T.lattice_intersection_frame_subspace Y.X Z.Ω _ Z.V Z.M.lat (eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) p₀ g b S₂
    Z.gen hspan hb.2 hS₂
  have card : ∀ (S : Finset (Fin g)) (n : ℕ) (u : Fin n → Z.V), LinearIndependent Z.Ω u →
      Submodule.span Z.Ω (Set.range u) = Submodule.span Z.Ω (b '' S) → S.card = n := by
    intro S n u hu hsp
    have a₁ := finrank_span_eq_card hu
    have a₂ := finrank_span_eq_card (hb.1.comp (Subtype.val : S → Fin g) Subtype.val_injective)
    have a₃ : Set.range (b ∘ (Subtype.val : S → Fin g)) = b '' S := by
      rw [Set.range_comp, Subtype.range_coe]
    rw [a₃, ← hsp, a₁] at a₂
    simpa using a₂.symm
  have c₁ := card S₁ D.p b₁ h1 (h2.trans e₁)
  have c₂ := card S₂ D.q b₂ h3 (h4.trans e₂)
  let ι₁ := S₁.orderEmbOfFin c₁
  let ι₂ := S₂.orderEmbOfFin c₂
  have r₁ : Set.range (b ∘ ι₁) = b '' S₁ := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  have r₂ : Set.range (b ∘ ι₂) = b '' S₂ := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  obtain ⟨W, hW, hWd⟩ := GlobalTheory.ModelChart.exists_open_isDomain Y.X p₀.1
  have hmem : ∀ i, b i ∈ Z.M.lat p₀ := fun i => by
    rw [hb.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨A, hA, EB, i₁, i₂, MB, e, hpA, hAN, hval⟩ := GlobalTheory.T.lattice_sections_affine_model Y.X Y.t.G Z.Ω _ Z.V Z.M p₀ (N ⊓ W) (Fin g) b ⟨hpN, hW⟩ hmem
  have hd : IsDomain Γ(Y.X, A) := hWd A hpA (hAN.trans inf_le_right)
  have hcl := GlobalTheory.T.affine_domain_generic_specializes Y.X Z.Ω _ A hA p₀ Z.gen hd hpA
  have hcA : ∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X), y = spMap f ≫ hA.fromSpec → centre y ∈ A := by
    intro f y hy
    have h5 : centre y ∈ Set.range hA.fromSpec := by
      subst hy
      exact ⟨spMap f (IsLocalRing.closedPoint ℂ), (Scheme.Hom.comp_apply _ _ _).symm⟩
    rwa [hA.range_fromSpec] at h5
  refine ⟨A, hA, EB, i₁, i₂, MB, e ∘ ι₁, e ∘ ι₂, b ∘ ι₁, b ∘ ι₂, hpA, fun q hq => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ q g D.p b ι₁ ι₁.injective hb.1 (hN q (hAN hq).1).2 (by rw [r₁]; exact e₁)
  · exact GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ q g D.q b ι₂ ι₂.injective hb.1 (hN q (hAN hq).1).2 (by rw [r₂]; exact e₂)
  · intro f y v w hy hs hv hw
    have hyA := hcA f y hy
    have h := hcl _ hyA
    have hq := (hN ⟨centre y, h⟩ (hAN hyA).1).2
    exact ⟨GlobalTheory.T.component_complex_point_tangents E H D l Xo c O β Y U Z τ σ D.p _ y h v hinj hfr hs
        (GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ _ g D.p b ι₁ ι₁.injective hb.1 hq (by rw [r₁]; exact e₁))
        (fun i => hval y f h hy (ι₁ i) (v i) (hv i)),
      GlobalTheory.T.component_complex_point_tangents E H D l Xo c O β Y U Z _ σ D.q _ y h w hinj hfr hs
        (GlobalTheory.T.lattice_frame_sub_basis Y.X Z.Ω _ Z.V Z.M.lat _ _ g D.q b ι₂ ι₂.injective hb.1 hq (by rw [r₂]; exact e₂))
        (fun j => hval y f h hy (ι₂ j) (w j) (hw j))⟩
  · intro f y v w hy h hv hw
    exact ⟨fun i => hval y f h hy (ι₁ i) (v i) (hv i), fun j => hval y f h hy (ι₂ j) (w j) (hw j)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameAtComponentPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_at_component_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (p₀ : Cpt (Z.ξ₀ ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → p₀ ∈ Z.genFib → ∃ (A : Y.X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(Y.X, A) EB) (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB) (e₂ : Fin D.q → EB) (v₁ : Fin D.p → Z.V) (v₂ : Fin D.q → Z.V), p₀.1 ∈ A ∧ (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 ∈ A → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧ IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) ∧ (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → (∀ i, Z.M.ValAt y (v₁ i) (v i)) ∧ ∀ j, Z.M.ValAt y (v₂ j) (w j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes | exact GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes <;> assumption)
end
