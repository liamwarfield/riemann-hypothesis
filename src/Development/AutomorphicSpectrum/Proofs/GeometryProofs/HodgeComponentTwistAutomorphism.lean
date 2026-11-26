module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtExistsBc
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingPullbackIff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LieModelTransportIsomorphism
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MvSecValComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration.Isomove

noncomputable section Move

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {f : X' ⟶ X} {φ : G'.left ⟶ G.left}

theorem mv_one_left {Y : Scheme.{0}} (y : Y ⟶ X) : (1 : Over.mk y ⟶ G).left = y ≫ (η[G]).left := by
  rw [Hom.one_def]
  simp

omit [GrpObj G] [GrpObj G'] in
theorem mv_push (w : φ ≫ G.hom = G'.hom ≫ f) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X} (hy : y' ≫ f = y)
    (a' : Over.mk y' ⟶ G') : ∃ a : Over.mk y ⟶ G, a'.left ≫ φ = a.left := by
  refine ⟨Over.homMk (a'.left ≫ φ) ?_, rfl⟩
  have hw := Over.w a'
  simp only [Over.mk_hom] at hw ⊢
  rw [Category.assoc, w, ← Category.assoc, hw, hy]

theorem mv_mul (h : IsGrpPullback G' G f φ) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X} (hy : y' ≫ f = y)
    {a' b' : Over.mk y' ⟶ G'} {a b : Over.mk y ⟶ G} (ha : a'.left ≫ φ = a.left) (hb : b'.left ≫ φ = b.left) :
    (a' * b').left ≫ φ = (a * b).left := by
  subst hy
  exact (h.2 (Over.mk y') a' b' a b ha.symm hb.symm).symm

private theorem mv_one_lemma (h : IsGrpPullback G' G f φ) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X}
    (hy : y' ≫ f = y) (e : Over.mk y ⟶ G) (he : (1 : Over.mk y' ⟶ G').left ≫ φ = e.left) : e = 1 := by
  have hm := mv_mul h hy he he
  rw [show (1 : Over.mk y' ⟶ G') * 1 = 1 from mul_one _, he] at hm
  have hee : e * e = e := (Over.OverMorphism.ext hm).symm
  simpa using congrArg (· * e⁻¹) hee

theorem mv_one (h : IsGrpPullback G' G f φ) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X} (hy : y' ≫ f = y) :
    (1 : Over.mk y' ⟶ G').left ≫ φ = (1 : Over.mk y ⟶ G).left := by
  obtain ⟨e, he⟩ := mv_push (φ := φ) h.1.w hy (1 : Over.mk y' ⟶ G')
  rw [he, mv_one_lemma h hy e he]

theorem mv_pow (h : IsGrpPullback G' G f φ) {Y : Scheme.{0}} {y' : Y ⟶ X'} {y : Y ⟶ X} (hy : y' ≫ f = y)
    {a' : Over.mk y' ⟶ G'} {a : Over.mk y ⟶ G} (ha : a'.left ≫ φ = a.left) {n : ℕ} (hn : a' ^ n = 1) :
    a ^ n = 1 := by
  have key : ∀ k : ℕ, (a' ^ k).left ≫ φ = (a ^ k).left := by
    intro k
    induction k with
    | zero => simpa only [pow_zero] using mv_one h hy
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mv_mul h hy ih ha
  apply Over.OverMorphism.ext
  rw [← key n, hn, mv_one h hy]

theorem mv_eta (h : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have := mv_one h (y' := 𝟙 X') (y := f) (Category.id_comp f)
  simpa [mv_one_left] using this

theorem mv_tan (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] {x' : Sp R ⟶ X'} {x : Sp R ⟶ X}
    (hx : x' ≫ f = x) {v' : epsAt x' ⟶ G'} {v : epsAt x ⟶ G} (hv : v'.left ≫ φ = v.left) (ht : IsTanAt G' x' v') :
    IsTanAt G x v := by
  unfold IsTanAt at ht ⊢
  rw [← hv, ← Category.assoc, ht]
  exact mv_one h hx

private theorem dualMap_lemma {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') (a : DualNumber R) :
    dualMap σ a = TrivSqZeroExt.inl (σ a.fst) + TrivSqZeroExt.inr (σ a.snd) := rfl

theorem mv_dual_alg {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') :
    spMap (dualMap σ) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap σ := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  ext <;> simp [dualMap_lemma, TrivSqZeroExt.algebraMap_eq_inl]

theorem mv_dual_fst {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMap σ) =
      spMap σ ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  simp [dualMap_lemma]

theorem mv_dual_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (σ : R →+* R') (τ : R' →+* R'') :
    spMap (dualMap τ) ≫ spMap (dualMap σ) = spMap (dualMap (τ.comp σ)) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap_lemma]

theorem mv_bc {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {x : Sp R ⟶ X} {x' : Sp R' ⟶ X}
    (hx : spMap σ ≫ x = x') (v : epsAt x ⟶ G) :
    ∃ v' : epsAt x' ⟶ G, v'.left = spMap (dualMap σ) ≫ v.left ∧ (IsTanAt G x v → IsTanAt G x' v') := by
  refine ⟨Over.homMk (spMap (dualMap σ) ≫ v.left) ?_, rfl, ?_⟩
  · have hw := Over.w v
    simp only [epsAt, Over.mk_hom] at hw ⊢
    rw [Category.assoc, hw, ← Category.assoc, mv_dual_alg, Category.assoc, hx]
  · intro ht
    unfold IsTanAt at ht ⊢
    simp only [Over.homMk_left]
    rw [← Category.assoc, mv_dual_fst, Category.assoc, ht, mv_one_left, mv_one_left, ← Category.assoc, hx]

variable {Ω : Type} [Field Ω]

theorem mv_stalk {ξ' : Sp Ω ⟶ X'} {ξ : Sp Ω ⟶ X} (hξ : ξ' ≫ f = ξ) (q' : Cpt ξ') (q : Cpt ξ) (hq : f q'.1 = q.1) :
    ∃ σ : X.presheaf.stalk q.1 →+* X'.presheaf.stalk q'.1,
      spMap σ ≫ X.fromSpecStalk q.1 = X'.fromSpecStalk q'.1 ≫ f ∧ (genMap ξ' q').comp σ = genMap ξ q ∧
      (IsIso f → Function.Bijective σ) := by
  obtain ⟨q, hqs⟩ := q
  obtain ⟨q', hq's⟩ := q'
  change f q' = q at hq
  subst hq hξ
  change ξ' (IsLocalRing.closedPoint Ω) ⤳ q' at hq's
  change f (ξ' (IsLocalRing.closedPoint Ω)) ⤳ f q' at hqs
  refine ⟨(f.stalkMap q').hom, ?_, ?_, ?_⟩
  · simp [spMap]
  · change (X'.presheaf.stalkSpecializes hq's ≫ Scheme.stalkClosedPointTo ξ').hom.comp (f.stalkMap q').hom =
      (X.presheaf.stalkSpecializes hqs ≫ Scheme.stalkClosedPointTo (ξ' ≫ f)).hom
    rw [← CommRingCat.hom_comp]
    apply congrArg CommRingCat.Hom.hom
    rw [Scheme.stalkClosedPointTo_comp]
    calc _ = (f.stalkMap q' ≫ X'.presheaf.stalkSpecializes hq's) ≫ Scheme.stalkClosedPointTo ξ' :=
          (Category.assoc _ _ _).symm
      _ = (X.presheaf.stalkSpecializes hqs ≫ f.stalkMap _) ≫ Scheme.stalkClosedPointTo ξ' := by
          congr 1
          exact (Scheme.Hom.stalkSpecializes_stalkMap f _ q' hq's).symm
      _ = _ := Category.assoc _ _ _
  · intro hf
    exact ConcreteCategory.bijective_of_isIso (f.stalkMap q')

theorem mv_regAt_le {ξ' : Sp Ω ⟶ X'} {ξ : Sp Ω ⟶ X} (hξ : ξ' ≫ f = ξ) (q' : Cpt ξ') (q : Cpt ξ)
    (hq : f q'.1 = q.1) : regAt ξ q ≤ regAt ξ' q' := by
  obtain ⟨σ, -, hσ, -⟩ := mv_stalk hξ q' q hq
  unfold regAt
  rw [← hσ]
  rintro _ ⟨r, rfl⟩
  exact ⟨σ r, rfl⟩

theorem mv_secVal_comp {B : Type} [CommRing B] {Z Z' : Scheme.{0}} (x : Sp B ⟶ Z) (ψ : Z ⟶ Z') (y : Sp B ⟶ Z')
    (hy : x ≫ ψ = y) (W : Z'.Opens) (s : Γ(Z', W)) (h : ⊤ ≤ x ⁻¹ᵁ ψ ⁻¹ᵁ W) (h' : ⊤ ≤ y ⁻¹ᵁ W) :
    secVal x (ψ ⁻¹ᵁ W) h ((ψ.app W).hom s) = secVal y W h' s := by
  subst hy
  unfold secVal
  congr 1

theorem mv_secVal_bc {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') {Z : Scheme.{0}} (x : Sp B ⟶ Z)
    (y : Sp B' ⟶ Z) (hy : spMap σ ≫ x = y) (W : Z.Opens) (s : Γ(Z, W)) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ y ⁻¹ᵁ W) :
    secVal y W h' s = σ (secVal x W h s) := by
  subst hy
  have key : Scheme.Hom.appLE (spMap σ ≫ x) W ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).hom =
      Scheme.Hom.appLE x W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom σ := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc]
    congr 1
  have := congrArg (fun g => g.hom s) key
  simpa [secVal] using this

end Move

end PositivityTheory.UnitarySelfGeneration.Isomove
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

open PositivityTheory.UnitarySelfGeneration.Isomove

namespace Isomove

variable {X X' : Scheme.{0}} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {f : X' ⟶ X} {φ : G'.left ⟶ G.left}
  {g : X ⟶ X'} {ψ : G.left ⟶ G'.left} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'}
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem extends_pull (hψ : IsGrpPullback G G' g ψ) (fg : f ≫ g = 𝟙 _) (hξ : ξ' ≫ f = ξ)
    {M : LieModel G ξ V} {M' : LieModel G' ξ' V} (hM : ∀ e, (M.pt e).left ≫ ψ = (M'.pt e).left)
    (q' : Cpt ξ') (q : Cpt ξ) (σ : X.presheaf.stalk q.1 →+* X'.presheaf.stalk q'.1)
    (h1 : spMap σ ≫ X.fromSpecStalk q.1 = X'.fromSpecStalk q'.1 ≫ f) (h2 : (genMap ξ' q').comp σ = genMap ξ q)
    (e : V) (v) (hv : M.Extends q e v) :
    ∃ v', M'.Extends q' e v' ∧ v'.left = spMap (dualMap σ) ≫ v.left ≫ ψ := by
  obtain ⟨v1, hv1, ht1⟩ := mv_bc (G := G) σ (x := X.fromSpecStalk q.1) (x' := X'.fromSpecStalk q'.1 ≫ f) h1 v
  have hw : (v1.left ≫ ψ) ≫ G'.hom = (epsAt (X'.fromSpecStalk q'.1)).hom := by
    rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w v1]
    simp [epsAt, fg]
    rfl
  let v' : epsAt (X'.fromSpecStalk q'.1) ⟶ G' := Over.homMk (v1.left ≫ ψ) hw
  have hgx : (X'.fromSpecStalk q'.1 ≫ f) ≫ g = X'.fromSpecStalk q'.1 := by
    rw [Category.assoc, fg, Category.comp_id]
  have key : spMap (dualMap (genMap ξ q)) = spMap (dualMap (genMap ξ' q')) ≫ spMap (dualMap σ) := by
    rw [mv_dual_comp, h2]
  refine ⟨v', ⟨mv_tan hψ hgx (v' := v1) (v := v') rfl (ht1 hv.1), ?_⟩, ?_⟩
  · rw [← hM e, hv.2]
    show spMap (dualMap (genMap ξ q)) ≫ v.left ≫ ψ = spMap (dualMap (genMap ξ' q')) ≫ v1.left ≫ ψ
    rw [key, hv1]
    simp only [Category.assoc]
  · show v1.left ≫ ψ = _
    rw [hv1, Category.assoc]

theorem lat_le (hψ : IsGrpPullback G G' g ψ) (fg : f ≫ g = 𝟙 _) (hξ : ξ' ≫ f = ξ)
    {M : LieModel G ξ V} {M' : LieModel G' ξ' V} (hM : ∀ e, (M.pt e).left ≫ ψ = (M'.pt e).left)
    (q' : Cpt ξ') (q : Cpt ξ) (hq : f q'.1 = q.1) (e : V) (he : e ∈ M.lat q) : e ∈ M'.lat q' := by
  obtain ⟨σ, h1, h2, -⟩ := mv_stalk hξ q' q hq
  induction he using Submodule.span_induction with
  | mem e he =>
    obtain ⟨v, hv⟩ := he
    obtain ⟨v', hv', -⟩ := extends_pull hψ fg hξ hM q' q σ h1 h2 e v hv
    exact Submodule.subset_span ⟨v', hv'⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact (M'.lat q').smul_mem ⟨c, mv_regAt_le hξ q' q hq c.2⟩ ha

theorem htAt_push (hψ : IsGrpPullback G G' g ψ) (fg : f ≫ g = 𝟙 _) (gf : g ≫ f = 𝟙 _)
    (φψ : φ ≫ ψ = 𝟙 _) (ψφ : ψ ≫ φ = 𝟙 _) (hξ : ξ' ≫ f = ξ)
    {M : LieModel G ξ V} {M' : LieModel G' ξ' V} (hM : ∀ e, (M.pt e).left ≫ ψ = (M'.pt e).left)
    {L : LB G.left} {L' : LB G'.left} {n : ℕ}
    (hW : ∀ (k : Type) [Field k] (z' : Sp k ⟶ X') (z : Sp k ⟶ X), z' ≫ f = z →
      ∀ (a' b' : Over.mk z' ⟶ G') (a b : Over.mk z ⟶ G) (c : kˣ), a'.left ≫ φ = a.left → b'.left ≫ φ = b.left →
      Out.WeilIs G L n a b (unitOn c) → Out.WeilIs G' L' n a' b' (unitOn c))
    (q' : Cpt ξ') (q : Cpt ξ) (hq : f q'.1 = q.1) (x' : Over.mk ξ' ⟶ G') (x : Over.mk ξ ⟶ G)
    (hx : x'.left ≫ φ = x.left) (w : Module.Dual Ω V) (hw : M'.IsHTAt L' n x' q' w) : M.IsHTAt L n x q w := by
  have hgq : g q.1 = q'.1 := by
    rw [← hq, ← Scheme.Hom.comp_apply, fg]
    rfl
  have hξg : ξ ≫ g = ξ' := by rw [← hξ, Category.assoc, fg, Category.comp_id]
  have hreg : regAt ξ' q' ≤ regAt ξ q := mv_regAt_le (f := g) hξg q q' hgq
  have hx' : x'.left = x.left ≫ ψ := by rw [← hx, Category.assoc, φψ, Category.comp_id]
  obtain ⟨hw0, W', s', hηW', htor', hext'⟩ := hw
  refine ⟨?_, ψ ⁻¹ᵁ W', ψ.app W' s', ?_, ?_, ?_⟩
  · intro e he
    exact hreg (hw0 e (lat_le hψ fg hξ hM q' q hq e he))
  · rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, mv_eta hψ, Scheme.Hom.comp_apply, hgq]
    exact hηW'
  · intro k _ _ i xk g0 c h hxk hpow hweil
    have hz : (spMap i ≫ ξ) ≫ g = spMap i ≫ ξ' := by rw [Category.assoc, hξg]
    have hz' : (spMap i ≫ ξ') ≫ f = spMap i ≫ ξ := by rw [Category.assoc, hξ]
    have comm : ∀ a : Over.mk (spMap i ≫ ξ) ⟶ G, (a.left ≫ ψ) ≫ G'.hom = (Over.mk (spMap i ≫ ξ')).hom := by
      intro a
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w a]
      simpa using hz
    let xk' : Over.mk (spMap i ≫ ξ') ⟶ G' := Over.homMk (xk.left ≫ ψ) (comm xk)
    let g0' : Over.mk (spMap i ≫ ξ') ⟶ G' := Over.homMk (g0.left ≫ ψ) (comm g0)
    have hback : ∀ a : Over.mk (spMap i ≫ ξ) ⟶ G, (a.left ≫ ψ) ≫ φ = a.left := by
      intro a
      rw [Category.assoc, ψφ, Category.comp_id]
    have hweil' := hW k (spMap i ≫ ξ') (spMap i ≫ ξ) hz' xk' g0' xk g0 c (hback xk) (hback g0) hweil
    have hxk' : xk'.left = spMap i ≫ x'.left := by
      show xk.left ≫ ψ = _
      rw [hx', hxk, Category.assoc]
    have hpow' : g0' ^ n = 1 := mv_pow hψ hz (a' := g0) (a := g0') rfl hpow
    have h' : ⊤ ≤ g0'.left ⁻¹ᵁ W' := by
      show ⊤ ≤ (g0.left ≫ ψ) ⁻¹ᵁ W'
      rw [Scheme.Hom.comp_preimage]
      exact h
    rw [← htor' k i xk' g0' c h' hxk' hpow' hweil']
    exact mv_secVal_comp g0.left ψ g0'.left rfl W' s' h h'
  · intro e v hv h
    obtain ⟨σ, h1, h2, -⟩ := mv_stalk hξ q' q hq
    obtain ⟨v', hv', hvl⟩ := extends_pull hψ fg hξ hM q' q σ h1 h2 e v hv
    have hh : ⊤ ≤ (spMap (dualMap σ) ≫ v.left) ⁻¹ᵁ (ψ ⁻¹ᵁ W') := fun p _ => h trivial
    have h' : ⊤ ≤ v'.left ⁻¹ᵁ W' := by
      rw [hvl]
      exact fun p _ => hh trivial
    obtain ⟨r, hr, hwe⟩ := hext' e v' hv' h'
    refine ⟨r, hreg hr, ?_⟩
    rw [hwe]
    congr 1
    have hcomp : (spMap (dualMap σ) ≫ v.left) ≫ ψ = v'.left := by
      rw [hvl]
      exact Category.assoc _ _ _
    have e1 := mv_secVal_comp (spMap (dualMap σ) ≫ v.left) ψ v'.left hcomp W' s' hh h'
    have e2 := mv_secVal_bc (dualMap σ) v.left (spMap (dualMap σ) ≫ v.left) rfl (ψ ⁻¹ᵁ W') (ψ.app W' s') h hh
    have hs : secVal v'.left W' h' s' = dualMap σ (secVal v.left (ψ ⁻¹ᵁ W') h (ψ.app W' s')) := e1.symm.trans e2
    rw [hs, ← h2]
    simp [dualMap]

theorem htOm_le (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback G G' g ψ) (fg : f ≫ g = 𝟙 _) (gf : g ≫ f = 𝟙 _)
    (φψ : φ ≫ ψ = 𝟙 _) (ψφ : ψ ≫ φ = 𝟙 _) (hξ : ξ' ≫ f = ξ)
    {M : LieModel G ξ V} {M' : LieModel G' ξ' V} (hM : ∀ e, (M.pt e).left ≫ ψ = (M'.pt e).left)
    {L : LB G.left} {L' : LB G'.left} {n : ℕ}
    (hW : ∀ (k : Type) [Field k] (z' : Sp k ⟶ X') (z : Sp k ⟶ X), z' ≫ f = z →
      ∀ (a' b' : Over.mk z' ⟶ G') (a b : Over.mk z ⟶ G) (c : kˣ), a'.left ≫ φ = a.left → b'.left ≫ φ = b.left →
      Out.WeilIs G L n a b (unitOn c) → Out.WeilIs G' L' n a' b' (unitOn c))
    (q' : Cpt ξ') (q : Cpt ξ) (hq : f q'.1 = q.1) (w : Module.Dual Ω V) (hw : w ∈ M'.htOm L' n q') :
    w ∈ M.htOm L n q := by
  have hξ' : ξ ≫ g = ξ' := by rw [← hξ, Category.assoc, fg, Category.comp_id]
  have hq' : g q.1 = q'.1 := by rw [← hq, ← Scheme.Hom.comp_apply, fg]; rfl
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x', hx', hw⟩ := hw
    obtain ⟨x, hx⟩ := mv_push hφ.1.w hξ x'
    exact Submodule.subset_span ⟨x, mv_pow hφ hξ hx hx',
      htAt_push hψ fg gf φψ ψφ hξ hM hW q' q hq x' x hx w hw⟩
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact (M.htOm L n q).smul_mem ⟨c, mv_regAt_le hξ' q q' hq' c.2⟩ ha

theorem model (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback G G' g ψ) (fg : f ≫ g = 𝟙 _)
    (φψ : φ ≫ ψ = 𝟙 _) (hξ : ξ' ≫ f = ξ) (M : LieModel G ξ V) [Mono ψ] :
    ∃ M' : LieModel G' ξ' V, ∀ e, (M.pt e).left ≫ ψ = (M'.pt e).left := by
  have hξg : ξ ≫ g = ξ' := by rw [← hξ, Category.assoc, fg, Category.comp_id]
  have hy : (Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ ξ) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ ξ' := by
    rw [Category.assoc, hξg]
  have hc : ∀ a : epsAt ξ ⟶ G, (a.left ≫ ψ) ≫ G'.hom = (epsAt ξ').hom := by
    intro a
    rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w a]
    simpa using hy
  let P : V → (epsAt ξ' ⟶ G') := fun e => Over.homMk ((M.pt e).left ≫ ψ) (hc (M.pt e))
  refine ⟨{ pt := P, tan := ?_, inj := ?_, onto := ?_, add := ?_, smul := ?_ }, fun e => rfl⟩
  · intro e
    exact mv_tan hψ hξg (v' := M.pt e) (v := P e) rfl (M.tan e)
  · intro e e' h
    apply M.inj
    have h1 : (M.pt e).left ≫ ψ = (M.pt e').left ≫ ψ := congrArg (fun a => Over.Hom.left a) h
    exact Over.OverMorphism.ext ((cancel_mono ψ).1 h1)
  · intro v hv
    have hφc : (v.left ≫ φ) ≫ G.hom = (epsAt ξ).hom := by
      rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w v]
      simp [hξ]
    let u : epsAt ξ ⟶ G := Over.homMk (v.left ≫ φ) hφc
    obtain ⟨e, he⟩ := M.onto u (mv_tan hφ hξ (v' := v) (v := u) rfl hv)
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    show (M.pt e).left ≫ ψ = v.left
    rw [he]
    show (v.left ≫ φ) ≫ ψ = v.left
    rw [Category.assoc, φψ, Category.comp_id]
  · intro e e'
    apply Over.OverMorphism.ext
    show (M.pt (e + e')).left ≫ ψ = _
    rw [M.add]
    exact mv_mul hψ hy (a' := M.pt e) (b' := M.pt e') (a := P e) (b := P e') rfl rfl
  · intro c e
    show (M.pt (c • e)).left ≫ ψ = _ ≫ (M.pt e).left ≫ ψ
    rw [M.smul, Category.assoc]

theorem grp_id (G : Over X) [GrpObj G] : IsGrpPullback G G (𝟙 X) (𝟙 G.left) := by
  refine ⟨IsPullback.id_horiz G.hom, ?_⟩
  intro T x y x₀ y₀ hx hy
  have key : ∀ (t : T.left ⟶ X), t = T.hom → ∀ (a b : Over.mk t ⟶ G),
      a.left = x.left → b.left = y.left → (a * b).left = (x * y).left := by
    intro t ht
    subst ht
    intro a b ha hb
    have e1 : a = x := Over.OverMorphism.ext ha
    have e2 : b = y := Over.OverMorphism.ext hb
    rw [e1, e2]
  exact (key _ (Category.comp_id _) x₀ y₀ (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans
    (Category.comp_id _).symm

end Isomove

theorem lie_model_transport_isomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (m : SABMap t' t e.hom) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V), ξ' ≫ e.hom = ξ → ∃ M' : LieModel t'.G ξ' V, (∀ v, (M'.pt v).left ≫ m.φ = (M.pt v).left) ∧ (∀ n, FullTorsion t.G ξ n → FullTorsion t'.G ξ' n) ∧ (IsCptGen ξ → IsCptGen ξ') ∧ ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩ ∧ (M'.lat q : Set V) = M.lat ⟨e.hom q.1, h⟩ ∧ ∀ n, (M'.htOm t'.PP.L n q : Set (Module.Dual Ω V)) = M.htOm t.PP.L n ⟨e.hom q.1, h⟩ := by
  intro E _ _ _ H X X' e Ω _ ξ ξ' t t' m V _ _ M hξ
  have hφ : IsGrpPullback t'.G t.G e.hom m.φ := m.cart
  haveI : IsIso m.φ := hφ.1.isIso_fst_of_isIso
  have φψ : m.φ ≫ inv m.φ = 𝟙 _ := IsIso.hom_inv_id _
  have ψφ : inv m.φ ≫ m.φ = 𝟙 _ := IsIso.inv_hom_id _
  have fg : e.hom ≫ e.inv = 𝟙 X' := e.hom_inv_id
  have gf : e.inv ≫ e.hom = 𝟙 X := e.inv_hom_id
  have hψw : inv m.φ ≫ t'.G.hom = t.G.hom ≫ e.inv := by
    rw [← cancel_mono e.hom, Category.assoc, Category.assoc, ← hφ.1.w, gf, Category.comp_id,
      ← Category.assoc, ψφ, Category.id_comp]
  have hψ : IsGrpPullback t.G t'.G e.inv (inv m.φ) := by
    refine IsGrpPullback.cancel hφ ?_ hψw
    rw [gf, ψφ]
    exact Isomove.grp_id t.G
  have hξ' : ξ ≫ e.inv = ξ' := by rw [← hξ, Category.assoc, fg, Category.comp_id]
  obtain ⟨M', hM⟩ := Isomove.model hφ hψ fg φψ hξ M
  have hM' : ∀ v, (M'.pt v).left ≫ m.φ = (M.pt v).left := by
    intro v
    rw [← hM v, Category.assoc, ψφ, Category.comp_id]
  have hW1 : ∀ (n : ℕ) (k : Type) [Field k] (z' : Sp k ⟶ X') (z : Sp k ⟶ X), z' ≫ e.hom = z →
      ∀ (a' b' : Over.mk z' ⟶ t'.G) (a b : Over.mk z ⟶ t.G) (c : kˣ), a'.left ≫ m.φ = a.left →
        b'.left ≫ m.φ = b.left → Out.WeilIs t.G t.PP.L (n : ℤ) a b (unitOn c) →
          Out.WeilIs t'.G t'.PP.L (n : ℤ) a' b' (unitOn c) := by
    intro n k _ z' z hz a' b' a b c ha hb hw
    subst hz
    exact (GlobalTheory.T.weil_pairing_pullback_iff E H X X' t t' e.hom m k z' a' b' a b n c ha hb).mpr hw
  have hW2 : ∀ (n : ℕ) (k : Type) [Field k] (z' : Sp k ⟶ X) (z : Sp k ⟶ X'), z' ≫ e.inv = z →
      ∀ (a' b' : Over.mk z' ⟶ t.G) (a b : Over.mk z ⟶ t'.G) (c : kˣ), a'.left ≫ inv m.φ = a.left →
        b'.left ≫ inv m.φ = b.left → Out.WeilIs t'.G t'.PP.L (n : ℤ) a b (unitOn c) →
          Out.WeilIs t.G t.PP.L (n : ℤ) a' b' (unitOn c) := by
    intro n k _ z' z hz a' b' a b c ha hb hw
    have hz2 : z' = z ≫ e.hom := by rw [← hz, Category.assoc, gf, Category.comp_id]
    subst hz2
    have ha' : a.left ≫ m.φ = a'.left := by rw [← ha, Category.assoc, ψφ, Category.comp_id]
    have hb' : b.left ≫ m.φ = b'.left := by rw [← hb, Category.assoc, ψφ, Category.comp_id]
    exact (GlobalTheory.T.weil_pairing_pullback_iff E H X X' t t' e.hom m k z a b a' b' n c ha' hb').mp hw
  refine ⟨M', hM', ?_, ?_, ?_⟩
  · intro n hT k _ i g' hpow
    have hy : (spMap i ≫ ξ') ≫ e.hom = spMap i ≫ ξ := by rw [Category.assoc, hξ]
    obtain ⟨a, ha⟩ := mv_push hφ.1.w hy g'
    obtain ⟨x, hx⟩ := hT k i a (mv_pow hφ hy ha hpow)
    obtain ⟨x', hx'⟩ := mv_push hψw hξ' x
    refine ⟨x', ?_⟩
    calc g'.left = (g'.left ≫ m.φ) ≫ inv m.φ := by rw [Category.assoc, φψ, Category.comp_id]
      _ = (spMap i ≫ x.left) ≫ inv m.φ := by rw [ha, hx]
      _ = spMap i ≫ x'.left := by rw [Category.assoc, hx']
  · intro hc
    have hsp : ∀ p : Cpt ξ', genPt ξ ⤳ e.hom p.1 := by
      intro p
      have h0 : genPt ξ = e.hom (genPt ξ') := by
        show ξ _ = e.hom (ξ' _)
        rw [← hξ]
        exact Scheme.Hom.comp_apply _ _ _
      rw [h0]
      exact p.2.map e.hom.continuous
    refine ⟨?_, ?_⟩
    · have key : ∀ ζ : Sp Ω ⟶ X, ξ' ≫ e.hom = ζ → Function.Bijective (Scheme.stalkClosedPointTo ζ).hom →
          Function.Bijective (Scheme.stalkClosedPointTo ξ').hom := by
        intro ζ hζ hb
        subst hζ
        rw [Scheme.stalkClosedPointTo_comp] at hb
        change Function.Bijective ((Scheme.stalkClosedPointTo ξ').hom ∘ (e.hom.stalkMap _).hom) at hb
        exact (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap _))).mp hb
      exact key ξ hξ hc.bij
    · intro p a b hab
      obtain ⟨σ, -, h2, hbij⟩ := mv_stalk hξ p ⟨e.hom p.1, hsp p⟩ rfl
      obtain ⟨a0, rfl⟩ := (hbij inferInstance).2 a
      obtain ⟨b0, rfl⟩ := (hbij inferInstance).2 b
      have hab' : genMap ξ ⟨e.hom p.1, hsp p⟩ a0 = genMap ξ ⟨e.hom p.1, hsp p⟩ b0 := by
        rw [← h2]
        exact hab
      rw [hc.inj _ hab']
  · intro q h
    have hq2 : e.inv (e.hom q.1) = q.1 := by
      rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    refine ⟨le_antisymm (mv_regAt_le (f := e.inv) hξ' ⟨e.hom q.1, h⟩ q hq2)
      (mv_regAt_le hξ q ⟨e.hom q.1, h⟩ rfl), ?_, ?_⟩
    · ext v
      constructor
      · intro hv
        exact Isomove.lat_le hφ gf hξ' hM' ⟨e.hom q.1, h⟩ q hq2 v hv
      · intro hv
        exact Isomove.lat_le hψ fg hξ hM q ⟨e.hom q.1, h⟩ rfl v hv
    · intro n
      ext w
      constructor
      · intro hw
        exact Isomove.htOm_le hφ hψ fg gf φψ ψφ hξ hM (hW1 n) q ⟨e.hom q.1, h⟩ rfl w hw
      · intro hw
        exact Isomove.htOm_le hψ hφ gf fg ψφ φψ hξ' hM' (hW2 n) ⟨e.hom q.1, h⟩ q hq2 w hw

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsoTransport
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsoTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.IsoMove

theorem lieModel_isoMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (m : SABMap t' t e.hom) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V), ξ' ≫ e.hom = ξ → ∃ M' : LieModel t'.G ξ' V, (∀ v, (M'.pt v).left ≫ m.φ = (M.pt v).left) ∧ (∀ n, FullTorsion t.G ξ n → FullTorsion t'.G ξ' n) ∧ (IsCptGen ξ → IsCptGen ξ') ∧ ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩ ∧ (M'.lat q : Set V) = M.lat ⟨e.hom q.1, h⟩ ∧ ∀ n, (M'.htOm t'.PP.L n q : Set (Module.Dual Ω V)) = M.htOm t.PP.L n ⟨e.hom q.1, h⟩ :=
  @PositivityTheory.UnitarySelfGeneration.lie_model_transport_isomorphism

end GlobalTheory.CompanionTheory.Ar.IsoMove
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsoTransportStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_iso_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (m : SABMap t' t e.hom) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V), ξ' ≫ e.hom = ξ → ∃ M' : LieModel t'.G ξ' V, (∀ v, (M'.pt v).left ≫ m.φ = (M.pt v).left) ∧ (∀ n, FullTorsion t.G ξ n → FullTorsion t'.G ξ' n) ∧ (IsCptGen ξ → IsCptGen ξ') ∧ ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩ ∧ (M'.lat q : Set V) = M.lat ⟨e.hom q.1, h⟩ ∧ ∀ n, (M'.htOm t'.PP.L n q : Set (Module.Dual Ω V)) = M.htOm t.PP.L n ⟨e.hom q.1, h⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IsoMove.lieModel_isoMove | exact GlobalTheory.CompanionTheory.Ar.IsoMove.lieModel_isoMove | (intros; apply GlobalTheory.CompanionTheory.Ar.IsoMove.lieModel_isoMove <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistModelsCommonPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistModelsCommonPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TwoModels

theorem generic_fibre_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (π' : Z ⟶ Y'.X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (x x' : Sp Ω ⟶ Xo.XF c), ξ ≫ π = x ≫ Y.j → ξ ≫ π' = x' ≫ Y'.j → x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → ∃ (t t' : SAB H Z) (tΩ : SAB H (Sp Ω)) (a : SABMap t Y.t π) (a' : SABMap t' Y'.t π') (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ) (u : SABMap tΩ Y.oF.t x) (u' : SABMap (twistSAB tΩ g) Y'.oF.t x'), m.φ ≫ a.φ = u.φ ≫ Y.m.φ ∧ m'.φ ≫ a'.φ = u'.φ ≫ Y'.m.φ ∧ u'.φ ≫ Y'.m0.toSABMap.φ = (twistMap u g).φ ≫ (twistMap Y.m0.toSABMap g).φ ≫ n.φ :=
  @PositivityTheory.UnitarySelfGeneration.two_models_common_cover_compare

end GlobalTheory.CompanionTheory.Ar.TwoModels
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistModelsCommonPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_models_common_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X) (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (π' : Z ⟶ Y'.X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (x x' : Sp Ω ⟶ Xo.XF c), ξ ≫ π = x ≫ Y.j → ξ ≫ π' = x' ≫ Y'.j → x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → ∃ (t t' : SAB H Z) (tΩ : SAB H (Sp Ω)) (a : SABMap t Y.t π) (a' : SABMap t' Y'.t π') (m : SABMap tΩ t ξ) (m' : SABMap (twistSAB tΩ g) t' ξ) (u : SABMap tΩ Y.oF.t x) (u' : SABMap (twistSAB tΩ g) Y'.oF.t x'), m.φ ≫ a.φ = u.φ ≫ Y.m.φ ∧ m'.φ ≫ a'.φ = u'.φ ≫ Y'.m.φ ∧ u'.φ ≫ Y'.m0.toSABMap.φ = (twistMap u g).φ ≫ (twistMap Y.m0.toSABMap g).φ ≫ n.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwoModels.generic_fibre_twist | exact GlobalTheory.CompanionTheory.Ar.TwoModels.generic_fibre_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.TwoModels.generic_fibre_twist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCompatibleLieModel
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCompatibleLieModel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem GlobalTheory.CompanionTheory.Ar.FrameModelsGeometry.main : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V), ∃ M' : LieModel G' ξ V, ∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left := by
  intro X Ω _ ξ G G' _ _ GΩ _ φ φ' h h' V _ _ M
  obtain ⟨M₀, h₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main Ω X ξ G GΩ φ V h).1 M
  obtain ⟨M', h₁⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main Ω X ξ G' GΩ φ' V h').2 M₀
  exact ⟨M', fun e => ⟨M₀.pt e, h₀ e, h₁ e⟩⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCompatibleLieModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_lie_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V), ∃ M' : LieModel G' ξ V, ∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FrameModelsGeometry.main | exact GlobalTheory.CompanionTheory.Ar.FrameModelsGeometry.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FrameModelsGeometry.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistAutomorphism
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FrameRebase

def sabRebase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') : SABMap t' t f' :=
  h ▸ m

theorem sabRebase_φ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f f' : S' ⟶ S} (m : SABMap t' t f) (h : f = f') :
    (sabRebase m h).φ = m.φ := by
  subst h; rfl

theorem tied_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∃ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA : SABMap tΩ A.t A.ξ) (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      mA.φ = m.φ ≫ k.φ ∧ mA.φ ≫ A.m.φ = u.φ ≫ Y.m.φ ∧ mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ ∧
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ ∧
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) ∧ (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) ∧ (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) ∧ (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' _ _ _ h4 h5 h6 h7 _ _ _ _
  have hπ : A'.ξ ≫ (e.hom ≫ A.f) = x ≫ Y.j := by rw [← Category.assoc, h4, h5]
  obtain ⟨t, t', tΩ, a, a', m, m', u, u', E1, E2, E3⟩ :=
    GlobalTheory.T.twist_models_common_point E H D l Xo c O O' β β' Y Y' g Φ n A'.X (e.hom ≫ A.f) A'.f Ω A'.ξ x x' hπ h6 h7
  obtain ⟨k, hk⟩ := sabCancel pullCubCancel E H _ _ _ Y.t A.t t A.f e.hom A.m a
  obtain ⟨k', hk'⟩ := sabCancel pullCubCancel E H _ _ _ Y'.t A'.t t' A'.f (𝟙 _) A'.m
    (sabRebase a' (Category.id_comp A'.f).symm)
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ A.t t tΩ e.hom A'.ξ k m
  obtain ⟨n₂, hn₂⟩ := sabComp pullCubComp E H _ _ _ A'.t t' (twistSAB tΩ g) (𝟙 _) A'.ξ k' m'
  let mA : SABMap tΩ A.t A.ξ := sabRebase n₁ h4
  let mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ := sabRebase n₂ (Category.comp_id _)
  have hmA : mA.φ = m.φ ≫ k.φ := (sabRebase_φ n₁ h4).trans hn₁
  have hmA' : mA'.φ = m'.φ ≫ k'.φ := (sabRebase_φ n₂ _).trans hn₂
  rw [sabRebase_φ] at hk'
  obtain ⟨M₁, P1, P2, -, P4⟩ := GlobalTheory.T.lie_model_iso_transport E H A.X A'.X e Ω A.ξ A'.ξ A.t t k A.Li A.M h4
  obtain ⟨M₂, Q⟩ := GlobalTheory.T.exists_compatible_lie_model A'.X Ω A'.ξ t.G A'.t.G tΩ.G m.φ mA'.φ m.cart mA'.cart A.Li M₁
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv A'.X A'.t.G Ω A'.ξ A.Li A'.Li M₂ A'.M
  refine ⟨t, tΩ, k, m, mA, mA', u, u', M₁, φ, hmA, ?_, ?_, E3, P1, ?_, P2, P4⟩
  · rw [hmA, Category.assoc, ← hk, E1]
  · rw [hmA', Category.assoc, ← hk', E2]
  · intro v
    obtain ⟨w, hw1, hw2⟩ := Q v
    exact ⟨w, hw1, by rw [hφ v]; exact hw2⟩

end GlobalTheory.CompanionTheory.Ar.FrameRebase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistAutomorphismStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_twist_automorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∃ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA : SABMap tΩ A.t A.ξ) (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      mA.φ = m.φ ≫ k.φ ∧ mA.φ ≫ A.m.φ = u.φ ≫ Y.m.φ ∧ mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ ∧
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ ∧
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) ∧ (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) ∧ (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) ∧ (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FrameRebase.tied_generic_fibre | exact GlobalTheory.CompanionTheory.Ar.FrameRebase.tied_generic_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.FrameRebase.tied_generic_fibre <;> assumption)
end
