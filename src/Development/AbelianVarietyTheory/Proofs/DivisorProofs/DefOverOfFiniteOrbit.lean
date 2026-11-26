module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Formalism.LocalToGlobal.CarriedPlMap
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem mem_of_finite_conj {K : Type} [Field K] [IsAlgClosed K] (k₀ : Subfield K) (hk : IsAlgClosed k₀)
    (a : K) (h : Set.Finite {b : K | ∃ σ : K ≃+* K, (∀ c ∈ k₀, σ c = c) ∧ b = σ a}) : a ∈ k₀ := by
  haveI := hk
  by_contra ha
  have htr : Transcendental k₀ a := by
    intro halg
    have hdeg := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible halg.isIntegral)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k₀ a hdeg
    exact ha (hc ▸ c.2)
  have hc : ∀ c : k₀, ∃ σ : K ≃ₐ[k₀] K, σ a = a + algebraMap k₀ K c := by
    intro c
    have htr' : Transcendental k₀ (a + algebraMap k₀ K c) := fun h' =>
      htr (by simpa using (h'.isIntegral.sub (isIntegral_algebraMap (x := c))).isAlgebraic)
    exact GroundTheory.Global.exists_algEquiv_apply_eq_of_transcendental htr htr'
  refine Set.infinite_of_injective_forall_mem (f := fun c : k₀ => a + algebraMap k₀ K c) ?_ ?_ h
  · intro c d hcd
    simpa using hcd
  · intro c
    obtain ⟨σ, hσ⟩ := hc c
    exact ⟨σ.toRingEquiv, fun b hb => σ.commutes ⟨b, hb⟩, hσ.symm⟩

theorem defOver_of_finite_orbit : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (Y : Scheme.{0}) (P : Sp K ⟶ Y),
    Set.Finite {P' : Sp K ⟶ Y | ∃ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) ∧ P' = spMap σ.toRingHom ≫ P} →
    DefOver k₀ P := by
  intro K _ _ k₀ hk Y P hfin
  classical
  let e := SpecToEquivOfLocalRing Y (CommRingCat.of K)
  let x := (e P).1
  let f := (e P).2.1
  have hP : P = Spec.map f ≫ Y.fromSpecStalk x := (e.left_inv P).symm
  let Φ : {g : Y.presheaf.stalk x ⟶ CommRingCat.of K // IsLocalHom g.hom} → (Sp K ⟶ Y) :=
    fun g => e.symm ⟨x, g⟩
  have hΦ : Function.Injective Φ := by
    intro g₁ g₂ h
    have := e.symm.injective h
    exact eq_of_heq (Sigma.mk.inj this).2
  have hloc : ∀ σ : K ≃+* K, IsLocalHom (f ≫ CommRingCat.ofHom σ.toRingHom).hom := by
    intro σ
    have : IsLocalHom f.hom := (e P).2.2
    show IsLocalHom (σ.toRingHom.comp f.hom)
    infer_instance
  let T : Set {g : Y.presheaf.stalk x ⟶ CommRingCat.of K // IsLocalHom g.hom} :=
    {g | ∃ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) ∧ g.1 = f ≫ CommRingCat.ofHom σ.toRingHom}
  have hT : T.Finite := by
    refine Set.Finite.of_finite_image (hfin.subset ?_) hΦ.injOn
    rintro _ ⟨g, ⟨σ, hσ, hg⟩, rfl⟩
    refine ⟨σ, hσ, ?_⟩
    show Spec.map g.1 ≫ Y.fromSpecStalk x = _
    rw [hg, Spec.map_comp, Category.assoc, ← hP]
  have hmem : ∀ s, f.hom s ∈ k₀ := by
    intro s
    refine mem_of_finite_conj k₀ hk _ ((hT.image fun g => g.1.hom s).subset ?_)
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨⟨f ≫ CommRingCat.ofHom σ.toRingHom, hloc σ⟩, ⟨σ, hσ, rfl⟩, rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom (f.hom.codRestrict k₀ hmem)) ≫ Y.fromSpecStalk x, ?_⟩
  refine Eq.trans ?_ hP.symm
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZbLeftWhiskerRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DescNorm

open GlobalTheory.LBDescent

section General

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def twist (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (u : Γ(pullback f f, ⊤)ˣ) :
    ∀ i j, Γ(pullback f f, chart f L i j)ˣ :=
  fun i j => φ i j * res le_top u

def Defect (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) : Prop :=
  ∀ (T : Scheme.{0}) (r : T ⟶ Triple f) (t : T) (i j k : L.ι),
    pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (r t)) ∈ L.U i →
    pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) (r t)) ∈ L.U j →
    pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) (r t)) ∈ L.U k →
    gm r t ⊤ D * gm (r ≫ pr13 f) t _ (φ i k) =
      gm (r ≫ pullback.fst (pullback.snd f f) (pullback.fst f f)) t _ (φ i j) *
        gm (r ≫ pullback.snd (pullback.snd f f) (pullback.fst f f)) t _ (φ j k)

end General

section Product

variable {S : Scheme.{0}} {A A' B : Over S} [GrpObj B]


variable (A B) in
def zb : A ⊗ B ⟶ A ⊗ B := lift (fst A B) (1 : A ⊗ B ⟶ B)

theorem zb_whiskerRight (q : A ⟶ A') : zb A B ≫ q ▷ B = q ▷ B ≫ zb A' B := by
  ext <;> simp [zb]

theorem zb_left_whiskerRight (q : A ⟶ A') :
    (q ▷ B).left ≫ (zb A' B).left = (zb A B).left ≫ (q ▷ B).left := by
  rw [← Over.comp_left, ← Over.comp_left, zb_whiskerRight]

def rhoZ (q : A ⟶ A') : pullback (q ▷ B).left (q ▷ B).left ⟶ pullback (q ▷ B).left (q ▷ B).left :=
  pullback.map (q ▷ B).left (q ▷ B).left (q ▷ B).left (q ▷ B).left (zb A B).left (zb A B).left (zb A' B).left
    (zb_left_whiskerRight q) (zb_left_whiskerRight q)

@[reassoc (attr := simp)]
theorem rhoZ_fst (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.fst (q ▷ B).left (q ▷ B).left =
    pullback.fst (q ▷ B).left (q ▷ B).left ≫ (zb A B).left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem rhoZ_snd (q : A ⟶ A') : rhoZ (B := B) q ≫ pullback.snd (q ▷ B).left (q ▷ B).left =
    pullback.snd (q ▷ B).left (q ▷ B).left ≫ (zb A B).left :=
  pullback.lift_snd _ _ _

def rhoW (q : A ⟶ A') : Triple (q ▷ B).left ⟶ Triple (q ▷ B).left :=
  pullback.map (pullback.snd (q ▷ B).left (q ▷ B).left) (pullback.fst (q ▷ B).left (q ▷ B).left)
    (pullback.snd (q ▷ B).left (q ▷ B).left) (pullback.fst (q ▷ B).left (q ▷ B).left) (rhoZ q) (rhoZ q) (zb A B).left
    (rhoZ_snd q).symm (rhoZ_fst q).symm

@[reassoc (attr := simp)]
theorem rhoW_fst (q : A ⟶ A') :
    rhoW (B := B) q ≫ pullback.fst (pullback.snd (q ▷ B).left (q ▷ B).left) (pullback.fst (q ▷ B).left (q ▷ B).left) =
      pullback.fst (pullback.snd (q ▷ B).left (q ▷ B).left) (pullback.fst (q ▷ B).left (q ▷ B).left) ≫ rhoZ q :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem rhoW_snd (q : A ⟶ A') :
    rhoW (B := B) q ≫ pullback.snd (pullback.snd (q ▷ B).left (q ▷ B).left) (pullback.fst (q ▷ B).left (q ▷ B).left) =
      pullback.snd (pullback.snd (q ▷ B).left (q ▷ B).left) (pullback.fst (q ▷ B).left (q ▷ B).left) ≫ rhoZ q :=
  pullback.lift_snd _ _ _

variable [GrpObj A]

def NormAlong (q : A ⟶ A') (P : LB (A ⊗ B).left) (τ : LB.Gen (ev P (𝟙 A) (1 : A ⟶ B)))
    (φ : ∀ i j, Γ(pullback (q ▷ B).left (q ▷ B).left, chart (q ▷ B).left P i j)ˣ) : Prop :=
  ∀ (T : Scheme.{0}) (r : T ⟶ pullback (q ▷ B).left (q ▷ B).left) (t : T) (i j : P.ι),
    pullback.fst (q ▷ B).left (q ▷ B).left (rhoZ q (r t)) ∈ P.U i →
    pullback.snd (q ▷ B).left (q ▷ B).left (rhoZ q (r t)) ∈ P.U j →
    gm (r ≫ rhoZ q) t _ (φ i j) =
      (gm (r ≫ pullback.fst (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) t _ (τ.s fun _ => i))⁻¹ *
        gm (r ≫ pullback.snd (q ▷ B).left (q ▷ B).left ≫ (fst A B).left) t _ (τ.s fun _ => j)

end Product

end GlobalTheory.DescNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlat
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.SigInj

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁)

def jj (i : I) : R₁ := Classical.choose (α.surj i.1 i.2)

theorem jj_q (i : I) : α.q (jj α i) = 0 := (Classical.choose_spec (α.surj i.1 i.2)).1

theorem jj_k (i : I) : α.k (jj α i) = i := (Classical.choose_spec (α.surj i.1 i.2)).2

theorem eq_jj {y : R₁} {i : I} (hq : α.q y = 0) (hk : α.k y = i) : y = jj α i := by
  have h := α.inj (y - jj α i) (by rw [map_sub, hq, jj_q, sub_zero]) (by rw [map_sub, hk, jj_k, sub_self])
  exact sub_eq_zero.mp h

theorem jj_add (i i' : I) : jj α (i + i') = jj α i + jj α i' :=
  (eq_jj α (by rw [map_add (f := _), jj_q, jj_q, add_zero]) (by rw [map_add (f := _), jj_k, jj_k]; rfl)).symm

theorem jj_smul (r : R) (i : I) : jj α (r • i) = π r • jj α i :=
  (eq_jj α (by rw [map_smul, jj_q, smul_zero]) (by rw [α.smul, jj_k]; rfl)).symm

variable {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀)

def tau (hs : SemiHom π p) : I ⊗[R] B →+ R₁ ⊗[R₀] B₀ :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun i ↦ AddMonoidHom.mk' (fun b ↦ jj α i ⊗ₜ[R₀] p b)
      (fun b b' ↦ by rw [map_add (f := _), TensorProduct.tmul_add]))
      (fun i i' ↦ by ext b; simp [jj_add, TensorProduct.add_tmul]))
    (fun r i b ↦ by
      simp only [AddMonoidHom.mk'_apply]
      rw [jj_smul, hs r b, TensorProduct.smul_tmul])

theorem tau_tmul (hs : SemiHom π p) (i : I) (b : B) : tau α p hs (i ⊗ₜ b) = jj α i ⊗ₜ[R₀] p b := by
  simp [tau, TensorProduct.liftAddHom_tmul]

end GlobalTheory.Obs.SigInj

open GlobalTheory.Obs.SigInj in
theorem GlobalTheory.Obs.sig_inj_of_flat : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) [Module.Flat R B] (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → ∀ y, α.KerQ y → σ y = 0 → y = 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker _ σ hσ y hy h0
  have hrange : ∀ y : R₁ ⊗[R₀] B₀, ∃ z, tau α p hs z =
      y - (1 : R₁) ⊗ₜ[R₀] TensorProduct.lid R₀ B₀ (Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x b₀ =>
      obtain ⟨b, rfl⟩ := hp b₀
      have hq' : α.q (x - algebraMap R₀ R₁ (α.q x)) = 0 := by simp
      refine ⟨⟨α.k (x - algebraMap R₀ R₁ (α.q x)), α.mem _⟩ ⊗ₜ b, ?_⟩
      rw [tau_tmul, ← eq_jj α hq' rfl, Algebra.TensorProduct.map_tmul, TensorProduct.lid_tmul,
        ← TensorProduct.smul_tmul, TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one]
      rfl
    | add a c ha hc =>
      obtain ⟨za, hza⟩ := ha
      obtain ⟨zc, hzc⟩ := hc
      exact ⟨za + zc, by rw [map_add (f := _), hza, hzc, map_add (f := _), map_add (f := _), TensorProduct.tmul_add]; abel⟩
  obtain ⟨z, hz⟩ := hrange y
  rw [show Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y = 0 from hy, map_zero,
    TensorProduct.tmul_zero, sub_zero] at hz
  have hμ : ∀ z, σ (tau α p hs z) = TensorProduct.lid R B (LinearMap.rTensor B I.subtype z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul i b => rw [tau_tmul, hσ, jj_k]; simp
    | add a c ha hc => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hc]
  have hinj : Function.Injective (fun z ↦ TensorProduct.lid R B (LinearMap.rTensor B I.subtype z)) :=
    (TensorProduct.lid R B).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hz0 : z = 0 := hinj (by
    show TensorProduct.lid R B (LinearMap.rTensor B I.subtype z) =
      TensorProduct.lid R B (LinearMap.rTensor B I.subtype 0)
    rw [map_zero, map_zero, ← hμ, hz, h0])
  rw [← hz, hz0, map_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlatStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_sigma_map_injective_of_flat : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) [Module.Flat R B] (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → ∀ y, α.KerQ y → σ y = 0 → y = 0 := by
  first | exact @GlobalTheory.Obs.sig_inj_of_flat | exact GlobalTheory.Obs.sig_inj_of_flat | (intros; apply GlobalTheory.Obs.sig_inj_of_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineEqDeRhamOfSmoothLiftComparison
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CrysLift

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def diagSec (X : Scheme.{0}) : AffOp X ⥤ (Pair (𝟙 X))ᵒᵖ :=
  (Monotone.functor (f := fun U : X.affineOpens ↦ (⟨(U, U), by simp⟩ : Pair (𝟙 X))) fun _ _ h ↦
      Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨h, h⟩)).op

def diagCoef (s : X ⟶ Sp R) : CoefMap (RingHom.id R) (OPair (𝟙 X) s) (OAff s) where
  G := diagSec X
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem diag_res_degree_one (s : X ⟶ Sp R) (c : HH1 s) :
    pullHyp1 (diagCoef s) (pullHyp1 (pairRes (𝟙 X) s) c) = c := by
  rw [← pullHyp1_comp]
  exact (pullHyp1_eq_of_natTrans _ (CoefMap.id _) { app U := 𝟙 U }
    (fun U b ↦ mp_id (OAff s) U b) c).trans (pullHyp1_id c)

theorem diag_res_degree_two (s : X ⟶ Sp R) (c : HH2 s) :
    pullHyp2 (diagCoef s) (pullHyp2 (pairRes (𝟙 X) s) c) = c := by
  rw [← pullHyp2_comp]
  exact (pullHyp2_eq_of_natTrans _ (CoefMap.id _) { app U := 𝟙 U }
    (fun U b ↦ mp_id (OAff s) U b) c).trans (pullHyp2_id c)

theorem eq_of_isPull1 {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) {c c' : HH1 s}
    (e : IsPull1 h c c') : c = c' := by
  have e' : pullHyp1 (pairRes (𝟙 X) s) c = pullHyp1 (pairRes (𝟙 X) s) c' :=
    (isPull1_id h c).symm.trans e
  rw [← diag_res_degree_one s c, e', diag_res_degree_one]

theorem eq_of_isPull2 {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) {c c' : HH2 s}
    (e : IsPull2 h c c') : c = c' := by
  have e' : pullHyp2 (pairRes (𝟙 X) s) c = pullHyp2 (pairRes (𝟙 X) s) c' :=
    (isPull2_id h c).symm.trans e
  rw [← diag_res_degree_two s c, e', diag_res_degree_two]

theorem red_of {R₀ : Type} [CommRing R₀] {I : Ideal R} {π : R →+* R₀} (hπ : Function.Surjective π)
    (hI : RingHom.ker π = I) {X₀ : Scheme.{0}} {s : X ⟶ Sp R} {s₀ : X₀ ⟶ Sp R₀} {i : X₀ ⟶ X}
    (hp : IsPullback i s₀ s (spMap π)) :
    ∃ s₀' : X₀ ⟶ Sp (R ⧸ I), IsPullback i s₀' s (spMap (Ideal.Quotient.mk I)) ∧
      s₀ ≫ spMap π = s₀' ≫ spMap (Ideal.Quotient.mk I) := by
  subst hI
  let e := RingHom.quotientKerEquivOfSurjective hπ
  have he : (e : R ⧸ RingHom.ker π →+* R₀).comp (Ideal.Quotient.mk _) = π := RingHom.ext fun _ ↦ rfl
  have hs : spMap π = spMap (e : R ⧸ RingHom.ker π →+* R₀) ≫ spMap (Ideal.Quotient.mk _) := by
    conv_lhs => rw [← he]
    show Spec.map _ = Spec.map _ ≫ Spec.map _; rw [← Spec.map_comp]; rfl
  have : IsIso (CommRingCat.ofHom (e : R ⧸ RingHom.ker π →+* R₀)) := e.toCommRingCatIso.isIso_hom
  refine ⟨s₀ ≫ spMap (e : R ⧸ RingHom.ker π →+* R₀), ?_, by rw [hs, Category.assoc]⟩
  exact hp.of_iso (Iso.refl _) (Iso.refl _) (asIso (spMap (e : R ⧸ RingHom.ker π →+* R₀))) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp [hs])

end GlobalTheory.CrysLift

namespace GlobalTheory.CrysLift

open GlobalTheory.SmoothLift

theorem crystallineDeRham_of_smoothLift : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.CrystallineDeRham := by
  rintro ⟨e₁, e₂, -, -, hnat⟩ R _ I κ hκ R₀ _ π hπ hI X X₀ s s₀ i hs hsep hqc hp m
  have hid : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  have : IsIso (spMap (RingHom.id R)) := by rw [hid]; infer_instance
  let D : Data :=
    { R := R, I := ⊥, κ := dp0 R, nil := isDPNilpotent_bot R, X := X, X₀ := X, s := s, t := s, i := 𝟙 X,
      smooth := hs, sep := hsep, qc := hqc,
      red := by
        obtain ⟨s', h1, h2⟩ := red_of (π := RingHom.id R) Function.surjective_id
          ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id)
          (IsPullback.of_horiz_isIso (fst := 𝟙 X) (g := spMap (RingHom.id R)) (snd := s) (f := s)
            ⟨by rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.comp_id]⟩)
        refine ⟨s', h1, ?_⟩
        rw [← h2, show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.comp_id] }
  let D' : Data :=
    { R := R, I := I, κ := κ, nil := hκ, X := X, X₀ := X₀, s := s, t := s₀ ≫ spMap π, i := i,
      smooth := hs, sep := hsep, qc := hqc,
      red := by
        obtain ⟨s', h1, h2⟩ := red_of hπ hI hp
        exact ⟨s', h1, h2⟩ }
  have h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R) := by
    rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.comp_id]
  obtain ⟨h1, h2⟩ := hnat D D' (RingHom.id R) (𝟙 X) i h m (by simp [D, D'])
  have k1 : ∀ c, m.pull1 c = ((e₁ D).trans (e₁ D').symm) c := fun c ↦
    ((e₁ D').symm_apply_apply _).symm.trans (congrArg (e₁ D').symm (eq_of_isPull1 h (h1 c)).symm)
  have k2 : ∀ c, m.pull2 c = ((e₂ D).trans (e₂ D').symm) c := fun c ↦
    ((e₂ D').symm_apply_apply _).symm.trans (congrArg (e₂ D').symm (eq_of_isPull2 h (h2 c)).symm)
  exact ⟨(funext k1 : (⇑m.pull1 : _ → _) = _) ▸ ((e₁ D).trans (e₁ D').symm).bijective,
    (funext k2 : (⇑m.pull2 : _ → _) = _) ▸ ((e₂ D).trans (e₂ D').symm).bijective⟩

end GlobalTheory.CrysLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedOfProper
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.AlgConn

theorem connectedSpace_specialFibre_of_morphisms : GlobalTheory.Published.FormalAlgebraisation.Morphisms →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)),
      IsProper f → ConnectedSpace ↑Y → ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f) := by
  intro H O _ _ _ hI Y f hP hY
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hT : Set.range (specialι f) = f ⁻¹' {IsLocalRing.closedPoint O} := by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    rw [range_residue] at h
    exact h
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hTn : ∀ n, Set.range (thickι f n) = f ⁻¹' {IsLocalRing.closedPoint O} := fun n => by
    have h := Scheme.Pullback.range_fst f (Spec.map (CommRingCat.ofHom (thickQ O n)))
    rw [range_thickQ] at h
    exact h
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hne : ∃ y : Y, f y = IsLocalRing.closedPoint O := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    have hsp : f y ⤳ IsLocalRing.closedPoint O :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (f y).2.ne_top)
    exact hsp.mem_closed hc ⟨y, rfl⟩
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  obtain ⟨y₀, hy₀⟩ := hne
  open GlobalTheory.SpecialConn GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in
  have hy₀' : y₀ ∈ Set.range (specialι f) := by rw [hT]; exact hy₀
  obtain ⟨z₀, -⟩ := hy₀'
  haveI : Nonempty (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f) := ⟨z₀⟩
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  haveI : IsClosedImmersion (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))))
  have hcl : Topology.IsClosedEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f) :=
    (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f).isClosedEmbedding
  refine { toPreconnectedSpace := preconnectedSpace_iff_clopen.2 fun U hU => ?_, toNonempty := ‹_› }
  by_contra hcon
  push_neg at hcon
  obtain ⟨hU0, hU1⟩ := hcon
  obtain ⟨u, hu⟩ := hU0
  obtain ⟨u', hu'⟩ : ∃ u', u' ∉ U := by
    by_contra h
    push_neg at h
    exact hU1 (Set.eq_univ_of_forall h)
  let A := GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f '' U
  let B := GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f '' Uᶜ
  have hA : IsClosed A := hcl.isClosedMap _ hU.1
  have hB : IsClosed B := hcl.isClosedMap _ hU.2.isClosed_compl
  have hpt : ∀ n (z : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre f), ∃ x, GlobalTheory.SpecialConn.thickι f n x =
      GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f z := fun n z => by
    have : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f z ∈ Set.range (GlobalTheory.SpecialConn.thickι f n) := by
      rw [hTn, ← hT]; exact ⟨z, rfl⟩
    exact this
  have hAB : ∀ n, (GlobalTheory.SpecialConn.thickι f n ⁻¹' A)ᶜ = GlobalTheory.SpecialConn.thickι f n ⁻¹' B := by
    intro n
    ext x
    obtain ⟨z, hz⟩ : GlobalTheory.SpecialConn.thickι f n x ∈ Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι f) := by
      rw [hT, ← hTn n]; exact ⟨x, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_preimage, A, B, Set.mem_image]
    constructor
    · intro h
      exact ⟨z, fun hzU => h ⟨z, hzU, hz⟩, hz⟩
    · rintro ⟨w, hw, hw'⟩ ⟨w', hw'U, hw''⟩
      exact hw (hcl.injective (hw''.trans hw'.symm) ▸ hw'U)
  have hclo : ∀ n, IsClopen (GlobalTheory.SpecialConn.thickι f n ⁻¹' A) := fun n =>
    ⟨hA.preimage (GlobalTheory.SpecialConn.thickι f n).continuous,
      by rw [← isClosed_compl_iff, hAB n]; exact hB.preimage (GlobalTheory.SpecialConn.thickι f n).continuous⟩
  choose h hhp hhU using fun n => GlobalTheory.T.exists_hom_specProdSelf_preimage_eq_clopen O (GlobalTheory.SpecialConn.thickFib f n)
    (GlobalTheory.SpecialConn.thickι f n ≫ f) _ (hclo n)
  haveI : IsProper (Over.mk f).hom := hP
  haveI : IsProper (Over.mk (twoπ O)).hom := isProper_twoπ O
  have hc : ∀ n, GlobalTheory.SpecialConn.thickTr f n ≫ h (n + 1) = h n := by
    intro n
    refine GlobalTheory.T.hom_ext_specProdSelf_of_basicOpen_preimage_eq O _ _ _ ?_ ?_
    · rw [Category.assoc, hhp, hhp, ← Category.assoc, GlobalTheory.SpecialConn.thickTr_ι]
    · refine TopologicalSpace.Opens.ext ?_
      rw [hhU n, Scheme.Hom.comp_preimage]
      change GlobalTheory.SpecialConn.thickTr f n ⁻¹' ((h (n + 1) ⁻¹ᵁ _ : (GlobalTheory.SpecialConn.thickFib f (n+1)).Opens) : Set _) = _
      rw [hhU (n + 1), ← Set.preimage_comp, ← GlobalTheory.SpecialConn.thickTr_ι f n]
      rfl
  obtain ⟨g, hg, -⟩ := GlobalTheory.Published.FormalAlgebraisation.Morphisms.existsUnique_thick H hI (Over.mk f)
    (Over.mk (twoπ O)) h (fun n => hhp n) hc
  have hW : IsClopen ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) :=
    (isClopen_basicOpen_specProdSelfFirstIdempotent O).preimage g.left.continuous
  have h0 : GlobalTheory.SpecialConn.thickι f 0 ⁻¹' ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) =
      GlobalTheory.SpecialConn.thickι f 0 ⁻¹' A := by
    rw [← hhU 0, ← hg 0]
    rfl
  obtain ⟨x, hx⟩ := hpt 0 u
  obtain ⟨x', hx'⟩ := hpt 0 u'
  rcases isClopen_iff.1 hW with hW0 | hW1
  · have hxA : x ∈ GlobalTheory.SpecialConn.thickι f 0 ⁻¹' A := ⟨u, hu, hx.symm⟩
    rw [← h0, hW0] at hxA
    simp at hxA
  · have hxA : x' ∈ GlobalTheory.SpecialConn.thickι f 0 ⁻¹'
        ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) := by
      rw [hW1]; trivial
    rw [h0] at hxA
    obtain ⟨w, hw, hw'⟩ := hxA
    exact hu' (hcl.injective (hw'.trans hx') ▸ hw)

end GlobalTheory.AlgConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TqOfGtCoord
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
open GlobalTheory.UU GlobalTheory.LN

def tqOfGtCoord {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (hB : IsAbelianScheme (thickObj R I e D.P.A)) : TQ (thickObj R I e G) D.X where
  B := thickObj R I e D.P.A
  isAb := hB
  q := g.q
  i := g.i
  q_hom := g.q_hom
  i_hom := g.i_hom
  q_flat := g.q_flat
  q_surj := g.q_surj
  q_affine := g.q_affine
  isKernel := g.isKernel
  loc b χ := by
    have := g.q_hom
    have := g.i_hom
    let ψ := D.Oφ (D.prBe I e) χ
    have hψ : ∀ k, D.Oφ g.pG χ k = g.q.left ≫ ψ k := fun k => by
      fin_cases k
      · show (padd _ _ _).left = ((Over.map (thick R I e)).map g.q ≫ padd _ _ _).left
        congr 1
        refine Eq.trans ?_ (MonObj.comp_mul _ _ _).symm
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]; rfl
      · show (_ ≫ _ : _ ⟶ D.P.A).left = ((Over.map (thick R I e)).map g.q ≫ _ ≫ _).left
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
      · rfl
      · show (_ ≫ _ : _ ⟶ D.P.A).left = ((Over.map (thick R I e)).map g.q ≫ _ ≫ _).left
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    choose j hj using fun k => exists_chart D.P.isLB (ψ k b)
    have hle : g.q.left ⁻¹ᵁ LB.wchart D.P.L ψ j ≤ LB.wchart D.P.L (D.Oφ g.pG χ) j := fun x hx =>
      Set.mem_iInter.2 fun k => by rw [hψ]; exact Set.mem_iInter.1 hx k
    refine ⟨LB.wchart D.P.L ψ j, Set.mem_iInter.2 hj, res hle ((g.t χ).s j), fun Z t x h₁ h₂ => ?_⟩
    have ap : ∀ (r : Z.left ⟶ (thickObj R I e G).left) (V) (h : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ((thickObj R I e G).left, V)ˣ)
        (z : Z.left), gm (𝟙 Z.left) z ⊤ (Units.map (r.appLE V ⊤ h).hom.toMonoidHom u) = gm r z V u :=
      fun r V h u z => (gm_res (𝟙 Z.left) z h trivial (pullU r V u)).trans ((gm_pull _ r z V (h trivial) u).trans
        (by rw [Category.id_comp]))
    have key : Units.map (((t ≫ g.i) * x).left.appLE _ ⊤ h₁).hom.toMonoidHom (res hle ((g.t χ).s j)) =
        chV t χ * Units.map (x.left.appLE _ ⊤ h₂).hom.toMonoidHom (res hle ((g.t χ).s j)) := unit_ext fun z _ => by
      obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
      have m₁ := h₁ (show z ∈ (⊤ : Z.left.Opens) from trivial)
      have m₂ := h₂ (show z ∈ (⊤ : Z.left.Opens) from trivial)
      have hq : ((t ≫ g.i) * x) ≫ g.q = x ≫ g.q := by
        rw [MonObj.mul_comp, Category.assoc, g.isKernel.w, ← Category.assoc,
          toUnit_unique (t ≫ toUnit _) (toUnit Z), ← Hom.one_def, _root_.one_mul]
      have hk : ∀ k, ((t ≫ g.i) * x).left ≫ D.Oφ g.pG χ k = x.left ≫ D.Oφ g.pG χ k := fun k => by
        rw [hψ, ← Category.assoc, ← Category.assoc, ← Over.comp_left, hq, Over.comp_left]
      rw [map_mul, ap, ap]
      refine ((gm_res _ z hle m₁ _).trans (gen_trans (g.t_gen χ) _ z (hle m₁) (hJ.mem _ _))).trans (Eq.trans ?_
        (congrArg (_ * ·) ((gm_res _ z hle m₂ _).trans (gen_trans (g.t_gen χ) _ z (hle m₂) (hJ.mem _ _)))).symm)
      have w := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (g.t_weight χ) (lift t x).left).trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))))
      rw [← Over.comp_left, ← Over.comp_left, lift_snd] at w
      have e₁ : lift t x ≫ lift (fst _ _ ≫ g.i) (snd _ _) ≫ μ[thickObj R I e G] = (t ≫ g.i) * x := by
        rw [Hom.mul_def, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
      have e₂ : val (charGen D.X (thickObj R I e G) D.P.L χ) (lift t x).left z J = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
        refine (gm_res _ z _ (hJ.mem _ _) _).trans ((gm_pull _ _ z ⊤ trivial _).trans ?_)
        rw [← Over.comp_left, lift_fst, gm_charUnit]
      rw [e₁, e₂] at w
      refine (congrArg₂ (· * ·) ?_ w).trans (mul_left_comm _ _ _)
      exact Finset.prod_congr rfl fun k _ => congrArg
        (fun q => gm q z (D.P.L.U (j k) ⊓ D.P.L.U (J q)) (D.P.L.g (j k) (J q)) ^ Oinvε k) (hk k)
    exact (congrArg Units.val key).trans (congrArg (· * _) (chV_val t χ))


set_option maxHeartbeats 2000000 in
theorem unif_evenOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ P : GlobalTheory.UU.CP G, P.L = U.LG ∧ EvenOn P := by
  intro R _ _ _ _ D A G _ _ hS U
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨w, hw⟩ := U.ext
  let U' := GlobalTheory.ValueForm.toPreU U.toUnifPre hL.globalFns hS w hw
  refine ⟨U'.P, rfl, ?_⟩
  obtain ⟨P₀, w₀, h₀⟩ := exists_isLevelCP (maximalIdeal R) 0 U'.P
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U'.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _
    (pull_isLB U'.P.L.isLB _) _ (pullIso_isGen U'.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))
  obtain ⟨w₁, k₁⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := GlobalTheory.ClosedPol.isCPMap_w hL.globalFns U' 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U'.gt 0).pG)
  obtain ⟨w₄, k₄⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _) (Category.id_comp _) k₃ (Over.w (U'.gt 0).pG)
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  let g := U'.gt 0
  have := g.q_hom
  let Q₀ := tqOfGtCoord g hB
  obtain ⟨M₀, v, hv⟩ := exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hL.globalFns D.toPre)
  have hw' : g.q.left ≫ (thickObj R (maximalIdeal R) 0 D.toPre.P.A).hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ 𝟙 _ :=
    (Over.w g.q).trans (Category.comp_id _).symm
  have hw'' : (g.q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) ≫ D.toPre.P.A.hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ 𝟙 _ ≫ thick R (maximalIdeal R) 0 := by
    exact (Over.w g.pG).trans (congrArg (_ ≫ ·) (Category.id_comp _).symm)
  obtain ⟨w₅, k₅⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm rfl k₄ hw''
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M₀ P₀ _ _ _ g.q.left hw' hw'' hv).2
    (toBase_mul_of_isMonHom g.q hw') w₅ k₅
  let Dsc : Q₀.Desc P₀ := ⟨M₀, w₆, k₆⟩
  obtain ⟨τ, hτ⟩ := Dsc.exists_even
  exact ⟨D.toPre.X, D.toPre.addX, D.toPre.freeX, D.toPre.finX, Q₀, P₀, ⟨w₀, h₀⟩, τ, hτ⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.GalAut

section General

variable {o Ω₁ Ω₂ : Type} [CommRing o] [Field Ω₁] [Algebra o Ω₁] [Field Ω₂] [Algebra o Ω₂]
  {M₁ : RatModel o Ω₁} {N : RatModel o Ω₂} {φ : Ω₁ →ₐ[o] Ω₂} {q : N.Z ⟶ M₁.Z} [IsFinite q]

theorem map_ringOn (hf : M₁.IsHom N φ q) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z) (τ : Ω₂ →ₐ[o] Ω₂) (hτ : ∀ a, τ (φ a) = φ a)
    {U₀ : M₁.Z.Opens} (hU₀ : IsAffineOpen U₀) (hne : ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z).Nonempty) :
    ∀ x ∈ N.ringOn ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z), τ x ∈ N.ringOn ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z) := by
  intro x hx
  obtain ⟨f, rfl⟩ := (RatModel.mem_ringOn_iff_exists hne).1 hx
  refine RatModel.mem_ringOn.2 fun z hz => ?_
  have hzU : q z ∈ U₀ := hz
  haveI := RatModel.isIntegrallyClosed_O hn z
  letI : Algebra Γ(M₁.Z, U₀) Γ(N.Z, q ⁻¹ᵁ U₀) := (q.app U₀).hom.toAlgebra
  have hi : IsIntegral Γ(M₁.Z, U₀) f := (IsFinite.finite_app q U₀ hU₀).to_isIntegral f
  have hmem : ∀ a : Γ(M₁.Z, U₀), φ.toRingHom (M₁.res U₀ ⟨_, hzU⟩ a) ∈ N.O z := fun a => by
    have e : φ.toRingHom (M₁.res U₀ ⟨_, hzU⟩ a) = φ (valF M₁.pt U₀ a) := congrArg φ (M₁.res_apply _ _ a)
    rw [e]
    exact hf.map_mem_O (z := z) (RatModel.valF_mem_O hzU a)
  let χ : Γ(M₁.Z, U₀) →+* N.O z :=
    RingHom.codRestrict (φ.toRingHom.comp (M₁.res U₀ ⟨_, hzU⟩)) (N.O z) hmem
  let ψ : Γ(N.Z, q ⁻¹ᵁ U₀) →+* Ω₂ := τ.toRingHom.comp (N.res (q ⁻¹ᵁ U₀) hne)
  have hc : (algebraMap (N.O z) Ω₂).comp χ = ψ.comp (algebraMap Γ(M₁.Z, U₀) Γ(N.Z, q ⁻¹ᵁ U₀)) := by
    ext a
    have e := hf.valF_app ⟨_, hzU⟩ a
    change φ (M₁.res U₀ ⟨_, hzU⟩ a) = τ (N.res (q ⁻¹ᵁ U₀) hne ((q.app U₀).hom a))
    calc φ (M₁.res U₀ ⟨_, hzU⟩ a) = φ (valF M₁.pt U₀ a) := congrArg φ (M₁.res_apply _ _ a)
      _ = τ (φ (valF M₁.pt U₀ a)) := (hτ _).symm
      _ = τ (valF N.pt (q ⁻¹ᵁ U₀) (q.app U₀ a)) := congrArg τ e.symm
      _ = τ (N.res (q ⁻¹ᵁ U₀) hne ((q.app U₀).hom a)) := congrArg τ (N.res_apply _ _ _).symm
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hi.map_of_comp_eq χ ψ hc)
  have e2 : ψ f = τ (valF N.pt (q ⁻¹ᵁ U₀) f) := congrArg τ (N.res_apply _ _ f)
  have e3 : τ (valF N.pt (q ⁻¹ᵁ U₀) f) = (w : Ω₂) := e2.symm.trans hw.symm
  rw [e3]
  exact w.2

theorem exists_isHom (hf : M₁.IsHom N φ q) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z) (τ : Ω₂ →ₐ[o] Ω₂)
    (hτ : ∀ a, τ (φ a) = φ a) : ∃ s : N.Z ⟶ N.Z, N.IsHom N τ s := by
  refine RatModel.exists_isHom_of_local fun z => ?_
  obtain ⟨U₀, hU₀, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := q z) trivial
  exact ⟨q ⁻¹ᵁ U₀, q ⁻¹ᵁ U₀, hz, hU₀.preimage q, ⟨z, hz⟩, map_ringOn hf hn τ hτ hU₀ ⟨z, hz⟩⟩

end General

section Over

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂]
  [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [Algebra o₁ Ω₂]

def overBase (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z) [IsFinite q]
    (hq : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt)
    (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) : RatModel o₁ Ω₂ where
  Z := M₂.Z
  s := q ≫ M₁.s
  sep := by haveI := M₁.sep; infer_instance
  lft := by haveI := M₁.lft; infer_instance
  qc := by haveI := M₁.qc; infer_instance
  pt := M₂.pt
  pt_s := by
    rw [← Category.assoc, hq, Category.assoc, M₁.pt_s, hA]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  gen := M₂.gen
  onto := M₂.onto

def incl (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) : Ω₁ →ₐ[o₁] Ω₂ :=
  { algebraMap Ω₁ Ω₂ with commutes' := fun r => by rw [hA]; rfl }

theorem autO_comm (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (r : o₁) : σ (algebraMap o₁ Ω₂ r) = algebraMap o₁ Ω₂ r := by
  rw [hA]
  exact σ.commutes (algebraMap o₁ Ω₁ r)

def autO (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) :
    Ω₂ →ₐ[o₁] Ω₂ :=
  { (σ : Ω₂ →+* Ω₂) with commutes' := fun r => autO_comm hA σ r }

theorem autO_apply (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (x : Ω₂) : autO hA σ x = σ x := rfl

end Over

theorem autAct : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ σ : Ω₂ ≃ₐ[Ω₁] Ω₂, ∃ s : M₂.Z ⟶ M₂.Z, M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ s ≫ q = q ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ M₂.Z) (b : Ω₂), M₂.val (y ≫ s) b = M₂.val y (σ b) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hn hfin hq σ
  haveI := hfin
  letI : Algebra o₁ Ω₂ := ((algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)).toAlgebra
  have hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) := rfl
  let N := overBase M₁ M₂ q hq hA
  haveI hfN : IsFinite (show N.Z ⟶ M₁.Z from q) := hfin
  have hqN : M₁.IsHom N (incl hA) q := hq
  have hnN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z := hn
  obtain ⟨s, hs⟩ := exists_isHom hqN hnN (autO hA σ) fun a => σ.commutes a
  obtain ⟨t, ht⟩ := exists_isHom hqN hnN (autO hA σ.symm) fun a => σ.symm.commutes a
  have hst : s ≫ t = 𝟙 N.Z := by
    have h1 := ht.comp hs
    have e : (autO hA σ).comp (autO hA σ.symm) = AlgHom.id o₁ Ω₂ := by
      ext x
      exact σ.apply_symm_apply x
    rw [e] at h1
    exact h1.unique (RatModel.isHom_id N)
  have hsq : s ≫ q = q := by
    have h1 := hqN.comp hs
    have e : (autO hA σ).comp (incl hA) = incl hA := by
      ext a
      exact σ.commutes a
    rw [e] at h1
    exact h1.unique hqN
  refine ⟨s, hs, hsq, fun K _ y b => ?_⟩
  let w : Sp K := IsLocalRing.closedPoint K
  have hts : ∀ z, t (s z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, hst]
    rfl
  by_cases hb : b ∈ N.O (s (y w))
  · exact hs.val_comp y w hb
  · have hb' : σ b ∉ N.O (y w) := by
      intro h
      apply hb
      have h2 := ht.map_mem_O (z := s (y w)) (x := σ b) (by
        have e : N.O (t (s (y w))) = N.O (y w) := congrArg N.O (hts (y w))
        rw [e]; exact h)
      simpa [autO_apply] using h2
    have e1 : M₂.val (y ≫ s) b = 0 := RatModel.val_of_notMem (M := N) (y := y ≫ s) w hb
    have e2 : M₂.val y (σ b) = 0 := RatModel.val_of_notMem (M := N) (y := y) w hb'
    rw [e1, e2]

end GlobalTheory.Poinc.GalAut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

def e8LB {S : Scheme.{0}} (G₀ : Over S) [GrpObj G₀] (L : LB G₀.left) (W : Matrix (Fin 8) (Fin 8) ℤ) :
    LB (powObj G₀ 8).left :=
  LB.LinComb L (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2) (fun k => -(W k.1.1 k.1.2 * negε k.2))

end GlobalTheory.PowE8
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleWitnessPlacesEqImage
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Div.PgTie


open Classical in
theorem image_congr {D : D7} {X X' : Formalism.L2.Col.Fields} (hX : X = X') {s : Formalism.L2.Ker.Seam D X} {s' : Formalism.L2.Ker.Seam D X'}
    (hs : HEq s s') {Pr : Formalism.L2.Col.Primes X} {Pr' : Formalism.L2.Col.Primes X'} (hP : HEq Pr Pr') :
    Pr.vGs.image (Formalism.L2.Host.CT.plMap s.iE) = Pr'.vGs.image (Formalism.L2.Host.CT.plMap s'.iE) := by
  subst hX
  cases hs
  cases hP
  rfl

theorem plMap_refl {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.Host.CT.plMap (RingEquiv.refl E) P = P := by
  ext x
  exact Formalism.L2.Host.CT.mem_plMap (RingEquiv.refl E) P x


open Classical in
theorem image_refl {E : Type} [Field E] [NumberField E] (f : E ≃+* E) (hf : f = RingEquiv.refl E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) : S.image (Formalism.L2.Host.CT.plMap f) = S := by
  subst hf
  rw [show Formalism.L2.Host.CT.plMap (RingEquiv.refl E) = id from funext plMap_refl, Finset.image_id]


end GlobalTheory.Div.PgTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffineCoverInfClosed
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_finite_affine_cover_infClosed : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    IsSeparated s → QuasiCompact s → ∃ (J : Type) (_ : Finite J) (_ : SemilatticeInf J)
      (U : J → X.affineOpens), Monotone U ∧ (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) ∧
        ⨆ i, (U i).1 = ⊤ := by
  intro R _ X s hsep hqc
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have hdiag : IsAffineHom (pullback.diagonal s) := inferInstance
  have hinf : ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
    fun U V hU hV => isAffineHom_diagonal_iff.mp hdiag ⊤ (isAffineOpen_top _) U (by simp) V
      (by simp) hU hV
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
    (by simpa using isCompact_univ)
  set A : Set X.Opens := infClosure ((fun i : X.affineOpens => i.1) '' S) with hAdef
  have hA : ∀ U ∈ A, IsAffineOpen U :=
    infClosure_min (t := {U | IsAffineOpen U}) (by rintro _ ⟨i, -, rfl⟩; exact i.2)
      (fun a ha b hb => hinf a b ha hb)
  letI inst : SemilatticeInf A :=
    Subtype.semilatticeInf (fun _ _ ha hb => infClosed_infClosure ha hb)
  haveI hfin : Finite A := ((hS.image _).infClosure).to_subtype
  refine ⟨A, hfin, inst, fun j => ⟨j.1, hA j.1 j.2⟩, fun a b h => h, fun i j => rfl, ?_⟩
  apply top_le_iff.mp
  rw [e]
  exact iSup₂_le fun i hi => le_iSup_of_le (⟨i.1, subset_infClosure ⟨i, hi, rfl⟩⟩ : A) le_rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def UnifTrait {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (G : Over (Sp R))
    [GrpObj G] (L : LB G.left) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (G' : Over (Sp W)) (_ : GrpObj G')
    (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
    (U' : Unif (maximalIdeal W) D' A' G'), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧
      IsGrpPullback G' G (spMap φ) β ∧ LBIso U'.LG.L (L.pull β) ∧ Nonempty (IsPullDeg φ D.toPre D'.toPre)

end GlobalTheory.Mum
end
end
