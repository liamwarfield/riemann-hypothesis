module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueTorusExtensionPointOfGroupPoint
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordAdditive
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EvenCubicUnitEqOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.CubicUnit
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def ev {Z Y : Over S} (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : Γ(Z.left, ⊤)ˣ :=
  Units.map x.left.appTop.hom.toMonoidHom u

theorem ev_val {Z Y : Over S} (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : (ev x u).val = x.left.appTop.hom u.val := rfl

theorem ev_comp {W Z Y : Over S} (p : W ⟶ Z) (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : ev p (ev x u) = ev (p ≫ x) u := by
  ext
  rw [ev_val, ev_val, ev_val, Over.comp_left, GlobalTheory.FunDescent.comp_appTop_apply]

theorem ev_mul {Z Y : Over S} (x : Z ⟶ Y) (u v : Γ(Y.left, ⊤)ˣ) : ev x (u * v) = ev x u * ev x v := by
  simp only [ev, map_mul]

theorem ev_inv {Z Y : Over S} (x : Z ⟶ Y) (u : Γ(Y.left, ⊤)ˣ) : ev x u⁻¹ = (ev x u)⁻¹ := by
  simp only [ev, map_inv]

theorem exists_char (Y : Over S) [ConnectedSpace Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (hρ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      ev (lift (t * t') y) ρ = ev (lift t y) ρ * ev (lift t' y) ρ) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y), ev (lift t y) ρ = chV t χ := by
  have hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ρ.val =
        (lift t y).left.appTop.hom ρ.val * (lift t' y).left.appTop.hom ρ.val := by
    intro Z t t' y
    have := congrArg Units.val (hρ Z t t' y)
    simpa [ev_val] using this
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.existsUnique_character_of_mul S X Y ρ hm
  refine ⟨χ, fun Z t y => ?_⟩
  ext
  rw [ev_val, chV_val, hχ, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left, lift_fst]

theorem eq_zero_of_chV (Y : Over S) [ConnectedSpace Y.left] (χ : X)
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t χ = 1) : χ = 0 := by
  have key : ∀ ψ : X, (∀ (Z : Over S) (t : Z ⟶ splitTorus S X), chV t ψ = 1) →
      ((1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) : Γ((splitTorus S X ⊗ Y).left, ⊤)) =
        (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X ψ).val := by
    intro ψ hψ
    have := congrArg Units.val (hψ _ (fst (splitTorus S X) Y))
    rw [chV_val] at this
    rw [this, Units.val_one]
  have hm : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ((1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) : Γ((splitTorus S X ⊗ Y).left, ⊤)) =
        (lift t y).left.appTop.hom (1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ).val *
          (lift t' y).left.appTop.hom (1 : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ).val := by
    intro Z t t' y
    simp
  obtain ⟨ψ, -, huniq⟩ := GlobalTheory.existsUnique_character_of_mul S X Y 1 hm
  rw [huniq χ (key χ h), huniq 0 (key 0 fun Z t => chV_zero t)]

private lemma mul_inv_inv_eq_of_mul_mul_mul_eq {M : Type*} [CommGroup M] (A AB a b y AY BY : M)
    (c : A * a * b * y = AB * AY * BY) :
    A * AB⁻¹ * y⁻¹ = AY * a⁻¹ * y⁻¹ * (BY * b⁻¹ * y⁻¹) := by
  apply Additive.ofMul.injective
  have c2 := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_inv] at c2 ⊢
  have hA : Additive.ofMul A = Additive.ofMul AB + Additive.ofMul AY + Additive.ofMul BY -
      (Additive.ofMul a + Additive.ofMul b + Additive.ofMul y) := by
    rw [← c2]
    abel
  rw [hA]
  abel

private lemma galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one {M : Type*} [CommGroup M] {p a b : M} (h : p * a⁻¹ * b⁻¹ = 1) : p = a * b := by
  rw [_root_.mul_assoc, ← _root_.mul_inv_rev, _root_.mul_inv_eq_one] at h
  rw [h, _root_.mul_comm]

end GlobalTheory.CubicUnit

namespace GlobalTheory
open CubicUnit

theorem even_cubic_unit_eq_one :
    (GlobalFnsSt → ∀ (S : Scheme.{0}) [ConnectedSpace S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] (G : Over S) [GrpObj G] [IsCommMonObj G] [ConnectedSpace G.left] (_ : TQ G X) (u : Γ(G.left, ⊤)ˣ), (∀ (T : Over S) (U : (T ⟶ G) → Γ(T.left, ⊤)), (∀ x, U x = x.left.appTop.hom u.val) → U 1 = 1 ∧ (∀ x, U x⁻¹ = U x) ∧ ∀ x y v, U (x * y * v) * U x * U y * U v = U (x * y) * U (x * v) * U (y * v)) → u = 1) := by
  intro hG S _ X _ _ G _ _ _ Q u hU
  haveI := Q.i_hom
  haveI := Q.q_hom
  haveI := Q.q_flat
  haveI := Q.q_surj
  haveI := Q.q_affine

  have hval : ∀ T : Over S, ∀ x : T ⟶ G, (fun x : T ⟶ G => (ev x u).val) x = x.left.appTop.hom u.val :=
    fun T x => ev_val x u
  have h1 : ∀ T : Over S, ev (1 : T ⟶ G) u = 1 := fun T =>
    Units.ext (by simpa using (hU T _ (hval T)).1)
  have hinv : ∀ (T : Over S) (x : T ⟶ G), ev x⁻¹ u = ev x u := fun T x =>
    Units.ext ((hU T _ (hval T)).2.1 x)
  have hcub : ∀ (T : Over S) (x y v : T ⟶ G),
      ev (x * y * v) u * ev x u * ev y u * ev v u = ev (x * y) u * ev (x * v) u * ev (y * v) u :=
    fun T x y v => Units.ext (by simpa only [Units.val_mul] using (hU T _ (hval T)).2.2 x y v)

  let ρ : Γ((splitTorus S X ⊗ G).left, ⊤)ˣ :=
    ev ((fst (splitTorus S X) G ≫ Q.i) * snd (splitTorus S X) G) u *
      (ev (fst (splitTorus S X) G ≫ Q.i) u)⁻¹ * (ev (snd (splitTorus S X) G) u)⁻¹
  have hρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev (lift t y) ρ = ev ((t ≫ Q.i) * y) u * (ev (t ≫ Q.i) u)⁻¹ * (ev y u)⁻¹ := by
    intro Z t y
    simp only [ρ, ev_mul, ev_inv, ev_comp, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have hmul : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev (lift (t * t') y) ρ = ev (lift t y) ρ * ev (lift t' y) ρ := by
    intro Z t t' y
    rw [hρ, hρ, hρ, MonObj.mul_comp]
    exact mul_inv_inv_eq_of_mul_mul_mul_eq _ _ _ _ _ _ _ (hcub Z (t ≫ Q.i) (t' ≫ Q.i) y)
  obtain ⟨χ, hχ⟩ := exists_char G ρ hmul

  have hsplit : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev ((t ≫ Q.i) * y) u = ev (t ≫ Q.i) u * ev y u := by
    intro Z t y
    have e1 := hχ Z t y
    have e0 := hχ Z t 1
    rw [hρ] at e1 e0
    simp only [_root_.mul_one, h1, _root_.inv_one, _root_.mul_inv_cancel] at e0
    rw [← e0] at e1
    exact galE_fst_snd_eq_one_of_mem_stabilizer_of_jacobiSym_eq_one e1

  let ρ₂ : Γ((splitTorus S X ⊗ G).left, ⊤)ˣ := ev (fst (splitTorus S X) G ≫ Q.i) u
  have hρ₂ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ G), ev (lift t y) ρ₂ = ev (t ≫ Q.i) u := by
    intro Z t y
    simp only [ρ₂, ev_comp, lift_fst_assoc]
  have hmul₂ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ G),
      ev (lift (t * t') y) ρ₂ = ev (lift t y) ρ₂ * ev (lift t' y) ρ₂ := by
    intro Z t t' y
    rw [hρ₂, hρ₂, hρ₂, MonObj.mul_comp, hsplit]
  obtain ⟨ψ, hψ⟩ := exists_char G ρ₂ hmul₂
  have hψ' : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), ev (t ≫ Q.i) u = chV t ψ := fun Z t => by
    rw [← hρ₂ Z t 1, hψ]
  have h2ψ : ψ + ψ = 0 := by
    refine eq_zero_of_chV G (ψ + ψ) fun Z t => ?_
    have e := hinv Z (t ≫ Q.i)
    rw [← GrpObj.inv_comp, hψ', hψ', chV_inv] at e
    rw [chV_add]
    calc chV t ψ * chV t ψ = (chV t ψ)⁻¹ * chV t ψ := by rw [e]
      _ = 1 := _root_.inv_mul_cancel _
  have hψ0 : ψ = 0 := by
    rw [← two_zsmul] at h2ψ
    exact (smul_eq_zero.mp h2ψ).resolve_left (by norm_num)
  have htor : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), ev (t ≫ Q.i) u = 1 := fun Z t => by
    rw [hψ', hψ0, chV_zero]
  have hsec : (1 : 𝟙_ (Over S) ⟶ G).left.appTop.hom u.val = 1 := by
    rw [← ev_val, h1, Units.val_one]

  have L : ∀ {Z : Scheme.{0}} (k : Z ⟶ G.left) (h : ⊤ ≤ k ⁻¹ᵁ (Q.q.left ⁻¹ᵁ ⊤))
      (f : Γ(G.left, Q.q.left ⁻¹ᵁ ⊤)), (k.appLE (Q.q.left ⁻¹ᵁ ⊤) ⊤ h).hom f = k.appTop.hom f := by
    intro Z k h f
    show (k.appLE _ (k ⁻¹ᵁ (Q.q.left ⁻¹ᵁ ⊤)) le_rfl).hom f = _
    rw [Scheme.Hom.appLE_eq_app]
    rfl
  obtain ⟨a, ha⟩ := (GlobalTheory.invariant_functions_descend S G Q.B (splitTorus S X) Q.q Q.i Q.q_hom Q.i_hom
    Q.q_flat Q.q_surj inferInstance Q.isKernel ⊤).2.2 u.val (fun Z t g h₁ h₂ => by
      have e := congrArg Units.val
        (show ev ((t ≫ Q.i) * g) u = ev g u by rw [hsplit, htor, _root_.one_mul])
      rw [ev_val, ev_val] at e
      exact (L _ _ _).trans (e.trans (L _ _ _).symm))
  have hq : Q.q.left.appTop.hom a = u.val := ha
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.WeilCube.surj_fst hG Q.isAb (𝟙_ (Over S))
    ((snd (𝟙_ (Over S)) Q.B).left.appTop.hom a)
  have hB : a = (toUnit Q.B).left.appTop.hom c₀ := by
    have e := congrArg (lift (toUnit Q.B) (𝟙 Q.B)).left.appTop.hom hc₀
    rw [← GlobalTheory.FunDescent.comp_appTop_apply, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left,
      ← Over.comp_left, lift_fst, lift_snd, Over.id_left] at e
    simpa using e.symm
  have hG0 : u.val = (toUnit G).left.appTop.hom c₀ := by
    rw [← hq, hB, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left,
      toUnit_unique (Q.q ≫ toUnit Q.B) (toUnit G)]
  have hc : c₀ = 1 := by
    have e := hsec
    rw [hG0, ← GlobalTheory.FunDescent.comp_appTop_apply, ← Over.comp_left,
      toUnit_unique ((1 : 𝟙_ (Over S) ⟶ G) ≫ toUnit G) (𝟙 _), Over.id_left] at e
    simpa using e
  exact Units.ext (by rw [hG0, hc, map_one, Units.val_one])

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompletedPointOfThickenings
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompletedPoint

theorem adicLevelMap_surjective {B : Type} [CommRing B] (J : Ideal B) (n : ℕ) :
    Function.Surjective (adicLevelMap J (Nat.succ_le_succ (Nat.zero_le n))) := by
  intro p
  have : Set.range (PrimeSpectrum.comap (Ideal.Quotient.factorPow J (Nat.succ_le_succ (Nat.zero_le n)))) = _ :=
    range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective _)
  refine this.ge ?_
  refine (PrimeSpectrum.mem_zeroLocus _ _).2 fun a ha => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hb : b ∈ J := by
    have h : Ideal.Quotient.mk (J ^ (0 + 1)) b = 0 := ha
    rwa [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at h
  refine p.isPrime.mem_of_pow_mem (n + 1) ?_
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hb _)]
  exact zero_mem _

theorem hom_ext_spec {B : Type} [CommRing B] (J : Ideal B) [IsHausdorff J B] {S : CommRingCat.{0}}
    {g g' : Spec (CommRingCat.of B) ⟶ Spec S}
    (h : ∀ n, adicLevelι J (n + 1) ≫ g = adicLevelι J (n + 1) ≫ g') : g = g' := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  obtain ⟨φ', rfl⟩ := Spec.map_surjective g'
  congr 1
  ext1
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' J (a := fun n => n + 1) (strictMono_id.add_const 1)
  intro n a
  have h1 := h n
  rw [← Spec.map_comp, ← Spec.map_comp] at h1
  exact congr($(Spec.map_injective h1).hom a)

theorem exists_of_isAdicFamily {B : Type} [CommRing B] (J : Ideal B) [IsAdicComplete J B] {X : Scheme.{0}}
    {V : X.Opens} (hV : IsAffineOpen V) {f : ∀ n : ℕ, Spec (CommRingCat.of (B ⧸ J ^ (n + 1))) ⟶ X}
    (hf : IsAdicFamily J f) (h₀ : ∀ p, f 0 p ∈ V) :
    ∃ g : Spec (CommRingCat.of B) ⟶ X, (∀ p, g p ∈ V) ∧ ∀ n, adicLevelι J (n + 1) ≫ g = f n := by
  have hr : ∀ n, Set.range (f n) ⊆ Set.range hV.fromSpec := fun n => by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := adicLevelMap_surjective J n p
    rw [hV.range_fromSpec, ← Scheme.Hom.comp_apply, hf.of_le (Nat.zero_le n)]
    exact h₀ q
  have hφ : ∀ n, ∃ φ : Γ(X, V) ⟶ CommRingCat.of (B ⧸ J ^ (n + 1)), Spec.map φ ≫ hV.fromSpec = f n := fun n => by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec (f n) (hr n))
    exact ⟨φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩
  choose φ hφ using hφ
  have ha : StrictMono fun n : ℕ => n + 1 := strictMono_id.add_const 1
  have hc : ∀ {m : ℕ}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp
      (φ (m + 1)).hom = (φ m).hom := by
    intro m
    have h1 : adicLevelMap J (Nat.le_succ (m + 1)) ≫ Spec.map (φ (m + 1)) = Spec.map (φ m) := by
      rw [← cancel_mono hV.fromSpec, Category.assoc, hφ, hφ, hf m]
    rw [← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom)
  refine ⟨Spec.map (CommRingCat.ofHom
    (IsAdicComplete.StrictMono.liftRingHom J ha (fun n => (φ n).hom) hc)) ≫ hV.fromSpec, fun p => ?_,
    fun n => ?_⟩
  · exact hV.range_fromSpec.le ⟨_, rfl⟩
  · rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      IsAdicComplete.StrictMono.mk_comp_liftRingHom J ha (fun n => (φ n).hom) hc (n := n)]
    exact hφ n

theorem exists_completion {A : Type} [CommRing A] [IsNoetherianRing A] (J : Ideal A) :
    ∃ (B : Type) (_ : CommRing B) (ψ : A →+* B), IsAdicComplete (J.map ψ) B ∧ ψ.Flat ∧
      ∀ p : PrimeSpectrum A, J ≤ p.asIdeal → p ∈ Set.range (PrimeSpectrum.comap ψ) := by
  refine ⟨AdicCompletion J A, inferInstance, algebraMap _ _, ?_, ?_, fun p hp => ?_⟩
  · rw [IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete J.fg_of_isNoetherianRing
  · exact RingHom.flat_algebraMap_iff.2 inferInstance
  · have h : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (J ^ 1))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, PrimeSpectrum.mem_zeroLocus,
        Ideal.mk_ker, pow_one]
      exact hp
    obtain ⟨q, rfl⟩ := h
    refine ⟨PrimeSpectrum.comap (AdicCompletion.evalₐ J 1).toRingHom q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply]
    congr 2


open GlobalTheory.FormalPoint in
theorem exists_completed_point {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (G G' : Over (Spec (CommRingCat.of R))) [Flat G'.hom] [LocallyOfFiniteType G'.hom]
    (j : ∀ e : ℕ, thickObj R I e G' ⟶ thickObj R I e G)
    (hj : ∀ e, thickMap R I e G' ≫ (j (e + 1)).left = (j e).left ≫ thickMap R I e G)
    (x : (thickObj R I 0 G').left) (W : G.left.Opens) (W' : G'.left.Opens)
    (hW : (fstG I 0 G).left ((j 0).left x) ∈ W) (hW' : (fstG I 0 G').left x ∈ W') :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (g' : Spec (CommRingCat.of B) ⟶ G'.left)
      (g : Spec (CommRingCat.of B) ⟶ G.left), IsAdicComplete (I.map (algebraMap R B)) B ∧ Module.Flat R B ∧
      Flat g' ∧ (fstG I 0 G').left x ∈ Set.range g' ∧
      g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧
      g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ W' ∧ ⊤ ≤ g ⁻¹ᵁ W ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
        r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).left ≫ (fstG I e G).left = ρ ≫ g := by
  have tf : ∀ (e : ℕ) (H : Over (Spec (CommRingCat.of R))),
      thickMap R I e H ≫ (fstG I (e + 1) H).left = (fstG I e H).left := fun e H =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have fh : ∀ (e : ℕ) (H : Over (Spec (CommRingCat.of R))),
      (fstG I e H).left ≫ H.hom = (thickObj R I e H).hom ≫ thick R I e := fun e H => pullback.condition
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open hW W.isOpen
  have hci : IsClosedImmersion (thick R I 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hci' : IsClosedImmersion (fstG I 0 G').left :=
    inferInstanceAs (IsClosedImmersion (pullback.fst G'.hom (thick R I 0)))
  obtain ⟨O, hO, hO'⟩ := (fstG I 0 G').left.isClosedEmbedding.isInducing.isOpen_iff.1
    (((j 0).left ≫ (fstG I 0 G).left) ⁻¹ᵁ V).isOpen
  have hxO : (fstG I 0 G').left x ∈ O := hO'.ge hxV
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hVO⟩ := G'.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show (fstG I 0 G').left x ∈ O ∩ W' from ⟨hxO, hW'⟩) (hO.inter W'.isOpen)
  replace hV' : IsAffineOpen V' := hV'
  have hln : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have hN : IsNoetherianRing Γ(G'.left, V') := IsLocallyNoetherian.component_noetherian ⟨V', hV'⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV'.fromSpec ≫ G'.hom)
  have hφf : φ.hom.Flat := by
    have : Flat (Spec.map φ) := by rw [hφ]; exact Flat.comp _ _
    exact Flat.SpecMap_iff.1 this
  obtain ⟨B, _, ψ, hB, hψ, hs⟩ := exists_completion (I.map φ.hom)
  letI : Algebra R B := (ψ.comp φ.hom).toAlgebra
  have hBc : IsAdicComplete (I.map (algebraMap R B)) B := by
    rw [Ideal.map_map] at hB; exact hB
  let g' : Spec (CommRingCat.of B) ⟶ G'.left := Spec.map (CommRingCat.ofHom ψ) ≫ hV'.fromSpec
  have hg' : g' ≫ G'.hom = spMap (algebraMap R B) := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp]; rfl
  have hg'V : ∀ p, g' p ∈ V' := fun p => hV'.range_fromSpec.le ⟨_, rfl⟩
  let y : Over.mk (spMap (algebraMap R B)) ⟶ G' := Over.homMk g' hg'
  have hy : ∀ e, reduction I y e ≫ (fstG I e G').left = adicLevelι (I.map (algebraMap R B)) (e + 1) ≫ g' :=
    fun e => reduction_fstG I y e
  have hf : IsAdicFamily (I.map (algebraMap R B)) fun e => reduction I y e ≫ (j e).left ≫ (fstG I e G).left := by
    intro e
    have h₁ : adicLevelMap (I.map (algebraMap R B)) (Nat.le_succ (e + 1)) ≫ reduction I y (e + 1) =
        reduction I y e ≫ thickMap R I e G' := by
      rw [← cancel_mono (fstG I (e + 1) G').left, Category.assoc, Category.assoc, hy, tf, hy, adicLevelMap_ι_assoc]
    show _ ≫ _ ≫ _ = _
    rw [reassoc_of% h₁, reassoc_of% (hj e), tf]
  obtain ⟨g, hgV, hg⟩ := exists_of_isAdicFamily _ hV hf fun p => by
    have h₁ : (fstG I 0 G').left (reduction I y 0 p) ∈ O := by
      have : (reduction I y 0 ≫ (fstG I 0 G').left) p ∈ V' := by rw [hy]; exact hg'V _
      exact (hVO this).1
    exact hO'.le h₁
  refine ⟨B, inferInstance, inferInstance, g', g, hBc, RingHom.Flat.comp hφf hψ, ?_, ?_, hg', ?_, fun p _ => (hVO (hg'V p)).2,
    fun p _ => hVW (hgV p), fun e Z ρ r h => ?_⟩
  · have : Flat (Spec.map (CommRingCat.ofHom ψ)) := Flat.SpecMap_iff.2 hψ
    exact Flat.comp _ _
  · obtain ⟨p, hp⟩ := hV'.range_fromSpec.ge hxV'
    obtain ⟨q, hq⟩ := hs p (by
      rw [Ideal.map_le_iff_le_comap]
      have h₁ : Spec.map φ p = thick R I 0 ((thickObj R I 0 G').hom x) := by
        rw [hφ, Scheme.Hom.comp_apply, hp, ← Scheme.Hom.comp_apply, fh]; rfl
      have h₂ : p.asIdeal.comap φ.hom = _ := congrArg PrimeSpectrum.asIdeal h₁
      rw [h₂]
      intro a ha
      show Ideal.Quotient.mk (I ^ (0 + 1)) a ∈ PrimeSpectrum.asIdeal _
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [zero_add, pow_one])]
      exact zero_mem _)
    exact ⟨q, (congrArg hV'.fromSpec hq).trans hp⟩
  · refine hom_ext_spec (I.map (algebraMap R B)) fun e => ?_
    rw [reassoc_of% (hg e), fh, ← Category.assoc (j e).left, Over.w, ← Category.assoc, reduction_hom,
      levelMap_thick]
  · have w : ρ ≫ spMap (algebraMap R B) = (r ≫ (thickObj R I e G').hom) ≫ thick R I e := by
      rw [← hg', ← Category.assoc, ← h, Category.assoc, fh, Category.assoc]
    obtain ⟨l, rfl⟩ := exists_factor_level I (algebraMap R B) ρ _ w
    obtain rfl : r = l ≫ reduction I y e := by
      rw [← cancel_mono (fstG I e G').left, Category.assoc, hy]
      exact h.trans (Category.assoc _ _ _)
    rw [Category.assoc, Category.assoc, hg]

end GlobalTheory.CompletedPoint

theorem GlobalTheory.exists_completed_point_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ x : (thickObj R I 0 G').left, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (g' : Spec (CommRingCat.of B) ⟶ G'.left) (g : Spec (CommRingCat.of B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), IsAdicComplete (I.map (algebraMap R B)) B ∧ Module.Flat R B ∧ Flat g' ∧ (fstG I 0 G').left x ∈ Set.range g' ∧ g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL' ∧ ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left), r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g := by
  intro R _ _ _ I _ _ D D' A A' G G' _ _ _ _ _ hG' U U' hD j hj x
  have := hG'.smooth
  obtain ⟨jL, h⟩ : ∃ i, (fstG I 0 G).left ((j 0).hom.left x) ∈ U.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U.LG.isLB.cover.ge trivial)
  obtain ⟨jL', h'⟩ : ∃ i, (fstG I 0 G').left x ∈ U'.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U'.LG.isLB.cover.ge trivial)
  obtain ⟨B, _, _, g', g, H⟩ := GlobalTheory.CompletedPoint.exists_completed_point I G G' (fun e => (j e).hom)
    (fun e => (hj e).2.1) x _ _ h h'
  exact ⟨B, _, _, g', g, jL, jL', H⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordEndRatioDescends
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordEndRatioDescends
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory


open CoordCompare TorusCoord in
theorem gtCoord_end_ratio_descends : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G) (aB : D.P.A ⟶ D.P.A) (h : D.X → D.X) (t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X), IsMonHom a → TorusEndOf D.X h t → g.i ≫ a = t ≫ g.i → a ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map aB → ∀ χ : D.X, ∃ u : LB.Gen (LB.LinComb D.P.L (Y := (thickObj R I e D.P.A).left) (fun k => pullback.fst D.P.A.hom (thick R I e) ≫ Sum.elim (D.Oφ (𝟙 _) (h χ)) (D.Oφ aB χ) k) (Sum.elim Oε Oinvε)), u.IsGen ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J → val (g.t χ) (x ≫ a.left) z J = val (g.t (h χ)) x z J * val u (x ≫ g.q.left) z J := by
  intro R _ _ I D e G _ _ g a aB h t ha ht hi hq χ
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hp : (Over.map (thick R I e)).map a ≫ g.pG = g.pG ≫ aB := by
    refine Over.OverMorphism.ext ?_
    have h1 : a.left ≫ g.q.left = g.q.left ≫ ((Over.pullback (thick R I e)).map aB).left :=
      congrArg (fun q => q.left) hq
    have h2 : ((Over.pullback (thick R I e)).map aB).left ≫ pullback.fst D.P.A.hom (thick R I e) =
        pullback.fst D.P.A.hom (thick R I e) ≫ aB.left := pullback.lift_fst _ _ _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))
  have e₁ : ∀ k, a.left ≫ D.Oφ g.pG χ k =
      g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) ≫ D.Oφ aB χ k := fun k =>
    (WeightPf.Oφ_comp ((Over.map (thick R I e)).map a) g.pG χ k).trans
      ((congrArg (D.Oφ · χ k) hp).trans
        ((WeightPf.Oφ_comp g.pG aB χ k).symm.trans (Category.assoc _ _ _)))
  have e₂ : ∀ k, D.Oφ g.pG (h χ) k =
      g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) ≫ D.Oφ (𝟙 _) (h χ) k := fun k =>
    (congrArg (D.Oφ · (h χ) k) (Category.comp_id g.pG).symm).trans
      ((WeightPf.Oφ_comp g.pG (𝟙 _) (h χ) k).symm.trans (Category.assoc _ _ _))
  obtain ⟨u, hu, hu'⟩ := exists_gen D.P.isLB
    (φ' := fun k => g.q.left ≫ pullback.fst D.P.A.hom (thick R I e) ≫
      Sum.elim (D.Oφ (𝟙 _) (h χ)) (D.Oφ aB χ) k) (ε' := Sum.elim Oε Oinvε)
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_sum_type _).symm)
      refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun k _ => ?_)
      · exact congrArg₂ (· ^ ·) (congrArg f (e₂ k)) (show -Oinvε k = Oε k by fin_cases k <;> rfl)
      · exact congrArg (fun ψ => f ψ ^ Oinvε k) (e₁ k))
    (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ (g.t (h χ))) (LB.pullGen D.P.L _ _ (g.t χ) a.left))
    (mulGen_isGen _ _ _ _ _ _ _ (invGen_isGen _ _ _ _ (g.t_gen _)) (pullGen_isGen _ _ _ _ (g.t_gen χ) _))
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J →
      val u r z J = (val (g.t (h χ)) r z J)⁻¹ * val (g.t χ) (r ≫ a.left) z J := fun Z r z J hJ =>
    (hu' Z r z J hJ).trans ((Geo.Tor.val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (Geo.Tor.val_inv _ _) (Geo.Tor.val_pull hJ _ _ _)))
  obtain ⟨v, hv₁, hv₂⟩ := exists_gen_of_val_eq D.P.isLB _ _ g.q.left u hu (fun Z r r' z J hJ hr => by
    rw [hv Z r z J hJ, hv Z r' z J hJ]
    have hw : r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom := by
      rw [← Over.w g.q, reassoc_of% hr]
    let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G).hom)
    let b : Z' ⟶ thickObj R I e G := Over.homMk r hw
    let b' : Z' ⟶ thickObj R I e G := Over.homMk r' rfl
    obtain ⟨τ, hτ⟩ := exists_torus g b b' (Over.OverMorphism.ext hr)
    have hτa : b ≫ a = ((τ ≫ t) ≫ g.i) * (b' ≫ a) := by
      rw [hτ, MonObj.mul_comp, Category.assoc, hi, Category.assoc]
    have v₁ := val_torus g (h χ) (Z := Z') hJ τ b'
    have v₂ := val_torus g χ (Z := Z') hJ (τ ≫ t) (b' ≫ a)
    rw [← hτ] at v₁
    rw [← hτa] at v₂
    have v₀ : gm (τ ≫ t).left z ⊤ (charUnit _ D.X χ) = gm τ.left z ⊤ (charUnit _ D.X (h χ)) :=
      (gm_pull τ.left t.left z ⊤ trivial _).symm.trans
        ((gm_res τ.left z (V := ⊤) (U := t.left ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).symm.trans (congrArg _ (ht χ)))
    refine (congrArg₂ (fun s s' => s⁻¹ * s') v₁ v₂).trans ?_
    rw [v₀, mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul]
    rfl)
  refine ⟨v, hv₁, fun Z x z J hJ => ?_⟩
  rw [hv₂ Z x z J hJ, hv Z x z J hJ, mul_inv_cancel_left]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordEndRatioDescendsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gen_of_torusEnd_compat : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G) (aB : D.P.A ⟶ D.P.A) (h : D.X → D.X) (t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X), IsMonHom a → TorusEndOf D.X h t → g.i ≫ a = t ≫ g.i → a ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map aB → ∀ χ : D.X, ∃ u : LB.Gen (LB.LinComb D.P.L (Y := (thickObj R I e D.P.A).left) (fun k => pullback.fst D.P.A.hom (thick R I e) ≫ Sum.elim (D.Oφ (𝟙 _) (h χ)) (D.Oφ aB χ) k) (Sum.elim Oε Oinvε)), u.IsGen ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J → val (g.t χ) (x ≫ a.left) z J = val (g.t (h χ)) x z J * val u (x ≫ g.q.left) z J := by
  first | exact @GlobalTheory.gtCoord_end_ratio_descends | exact GlobalTheory.gtCoord_end_ratio_descends | (intros; apply GlobalTheory.gtCoord_end_ratio_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointQk
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointQk
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionQk

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem val_cubAtT {T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) {y : T'.left} {J} (hJ : Good D.P.L y J)
    (χ : D.X) (x w : T ⟶ D.P.A) :
    val (DegPre.cubAtT D T (DegPre.cT D T χ) x w) ρ.left y J = th D y J (cP D _ χ) (ρ ≫ x) (ρ ≫ w) := by
  have := val_cub D.cub ρ hJ (cP D T χ) x w
  rwa [comp_cP] at this

theorem exists_pull (ρ : TF (R := R) F ⟶ T) (g : GtPt D T) :
    ∃ g' : GtPtF D F, g'.b = ρ ≫ g.b ∧
      ∀ χ y J, Good D.P.L y J → val (g'.s χ) (𝟙 _) y J = val (g.s χ) ρ.left y J := by
  have vp : ∀ χ y J, Good D.P.L y J →
      val (LB.pullGen D.P.L _ _ (g.s χ) ρ.left) (𝟙 _) y J = val (g.s χ) ρ.left y J := fun χ y J hJ => by
    rw [val_pull hJ, Category.id_comp]
  obtain ⟨g', hb, hv⟩ := exists_gt (D := D) (F := F) (ρ ≫ g.b) (fun χ => LB.pullGen D.P.L _ _ (g.s χ) ρ.left)
    (fun χ => pullGen_isGen _ _ _ _ (g.isGen χ) _) (fun χ U _ h => by
      refine Finset.prod_congr rfl fun i _ => congrArg (fun q => h q ^ DegPre.gtε i) ?_
      fin_cases i
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left)
          ((MonObj.comp_mul ρ (cP D T χ) g.b).trans (congrArg (· * (ρ ≫ g.b)) (comp_cP D ρ χ)))
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (comp_cP D ρ χ)
      · rfl
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ))
    (fun y J hJ => (vp 0 y J hJ).trans ((val_corr hJ g.s_zero _).trans (val_one _)))
    (fun χ χ' y J hJ => by
      rw [vp _ y J hJ, vp _ y J hJ, vp _ y J hJ]
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.mult χ χ') ρ.left).trans (val_mul hJ _ _ _))
      refine Eq.trans (congrArg₂ (· * ·) rfl ?_) e
      refine Eq.trans ?_ (val_cubAtT ρ hJ χ (cP D T χ') g.b).symm
      rw [comp_cP])
  exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vp χ y J hJ)⟩

theorem isIota_zero (hB : D.TauBimult) {h : GtPtF D F} (hh : h.IsZero) : GtPtF.IsIota 0 h := by
  obtain ⟨hb, hv⟩ := (isZero_iff h).1 hh
  refine (isIota_iff 0 h).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have t := tau_mul (𝟙 (TF (R := R) F)) hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact (hv χ y J hJ).trans (mul_eq_left.1 t.symm).symm

theorem exists_qk (hB : D.TauBimult) (ρ : TF (R := R) F ⟶ T) (k : ℕ) (g : GtPt D T) (gs : ℕ → GtPt D T)
    (h₀ : (gs 0).IsZero) (hs : ∀ i, GtPt.IsAdd (gs i) g (gs (i + 1))) (hk : (gs k).IsZero) :
    ∃ p : QkPt D F k, p.y = 0 ∧ GtPt.IsPullF F ρ.left g p.g := by
  choose pl hb hv using fun g : GtPt D T => exists_pull ρ g
  have zero : ∀ g : GtPt D T, g.IsZero → (pl g).IsZero := fun g hg =>
    (isZero_iff _).2 ⟨by rw [hb, hg.1]; exact MonObj.comp_one (M := D.P.A) ρ, fun χ y J hJ =>
      (hv g χ y J hJ).trans ((val_corr hJ (hg.2 χ) _).trans (val_one _))⟩
  have add : ∀ g g' g'' : GtPt D T, g.IsAdd g' g'' → (pl g).IsAdd (pl g') (pl g'') := fun g g' g'' h =>
    (isAdd_iff _ _ _).2 ⟨by rw [hb, hb, hb, h.1]; exact MonObj.comp_mul ρ g.b g'.b, fun χ y J hJ => by
      rw [hv _ _ y J hJ, hv _ _ y J hJ, hv _ _ y J hJ, hb, hb]
      have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) ρ.left).trans (val_mul hJ _ _ _))
      exact Eq.trans (congrArg₂ (· * ·) rfl (val_cubAtT ρ hJ χ g.b g'.b).symm) e⟩
  refine ⟨⟨0, pl g, pl (gs k), ⟨fun i => pl (gs i), zero _ h₀, fun i => add _ _ _ (hs i), rfl⟩,
    isIota_zero hB (zero _ hk)⟩, rfl, congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (hb g),
    fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (hv g χ y J hJ).trans ?_
  rw [val_pull hJ, Category.id_comp]

theorem base_pow (g : GtPt D T) (gs : ℕ → GtPt D T)
    (h₀ : (gs 0).IsZero) (hs : ∀ i, GtPt.IsAdd (gs i) g (gs (i + 1))) (i : ℕ) : (gs i).b = g.b ^ i := by
  induction i with
  | zero => rw [pow_zero]; exact h₀.1
  | succ i ih => rw [pow_succ, ← ih]; exact (hs i).1

theorem torsionPoint_qk : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → gp.b ^ k = 1 ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∃ p : QkPt D.toPre F k, p.y = 0 ∧ GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp p.g := by
  intro hG R _ _ _ I hI hne D A G _ _ U k x gp hx hm
  obtain ⟨hadd, hzero⟩ := GlobalTheory.gtCoord_additive hG R I hI hne D A G U
  choose gs hgs using fun i : ℕ => (GlobalTheory.T.existsUnique_torusExtensionPoint_of_groupPoint R I hI hne D A G U (x ^ i)).exists
  have h₀ : (gs 0).IsZero := hzero _ (by simpa only [pow_zero] using hgs 0)
  have hk : (gs k).IsZero := hzero _ (by simpa only [hx] using hgs k)
  have hs : ∀ i, GtPt.IsAdd (gs i) gp (gs (i + 1)) := fun i =>
    hadd (x ^ i) x _ _ _ (hgs i) hm (by simpa only [pow_succ] using hgs (i + 1))
  exact ⟨(base_pow gp gs h₀ hs k).symm.trans hk.1,
    fun F _ _ => exists_qk D.tau_bimult (toUnit _) k gp gs h₀ hs hk⟩

end GlobalTheory.TorsionQk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPointQkStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.torsionPoint_qk_alt : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → gp.b ^ k = 1 ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∃ p : QkPt D.toPre F k, p.y = 0 ∧ GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp p.g := by
  first | exact @GlobalTheory.TorsionQk.torsionPoint_qk | exact GlobalTheory.TorsionQk.torsionPoint_qk | (intros; apply GlobalTheory.TorsionQk.torsionPoint_qk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsPullDegId
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcData

theorem unit_ext_field {K F : Type} [Field K] [Field F] (ρ : Sp F ⟶ Sp K) (z : Sp F) {U : (Sp K).Opens}
    {a b : Γ(Sp K, U)ˣ} (h : ρ z ∈ U → gm ρ z U a = gm ρ z U b) : a = b := by
  have sK : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  by_cases hz : ρ z ∈ U
  · obtain rfl : U = ⊤ := top_le_iff.1 fun y _ => by rw [Subsingleton.elim y (ρ z)]; exact hz
    have e := congrArg Units.val (h hz)
    rw [gm_val ρ z ⊤ hz, gm_val ρ z ⊤ hz] at e
    have hK : IsField Γ(Sp K, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
    letI := hK.toField
    exact Units.ext (RingHom.injective
      (((Sp F).presheaf.germ (ρ ⁻¹ᵁ ⊤) z hz).hom.comp (ρ.app ⊤).hom) e)
  · exact unit_ext fun y hy => absurd (by rw [Subsingleton.elim (ρ z) y]; exact hy) hz

variable {R : Type} [CommRing R] [IsDomain R]

theorem mapsAt_of_genRel {D D' : DegPre R} {B₀ : Scheme.{0}} {M₀ : LB B₀} (hM₀ : M₀.IsLB) {φ : D.P.A.left ⟶ B₀}
    {Φ : D'.P.A.left ⟶ D.P.A.left} {w : LB.Iso D.P.L (M₀.pull φ)} {wD : LB.Iso D'.P.L (D.P.L.pull Φ)}
    {w' : LB.Iso D'.P.L (M₀.pull (Φ ≫ φ))} (T : Tri w wD w') {F : Type} [Field F] (ρ : Sp F ⟶ (TK R).left)
    (x : D'.X) (y : D.X) (hx : D'.xK x ≫ Φ = D.xK y) {pt₀ : PUnit → (Sp F ⟶ B₀)}
    (t₀ : LB.Gen (LB.LinComb M₀ pt₀ (fun _ => -1))) (s : F)
    (h : GenRel w (LB.pullGen _ _ _ (D.psi y) ρ) t₀ s) (h' : GenRel w' (LB.pullGen _ _ _ (D'.psi x) ρ) t₀ s) :
    ∃ b : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => D'.xK x ≫ Φ) (fun _ => -1)),
      GeneratorPullback.MapsAt D.P.L D'.P.L (J := PUnit) (fun _ => Φ) wD (D'.xK x) (-1) (D'.psi x) b ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J → val b r z J = val (D.psi y) r z J := by
  obtain ⟨b, -, vb⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => D'.xK x ≫ Φ) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) hx.symm) (D.psi y) (D.psi_gen y)
  refine ⟨b, fun jN jL => ?_, vb⟩
  have z : Sp F := (default : PrimeSpectrum F)
  refine unit_ext_field (K := FractionRing R) ρ z fun hz => ?_
  have mN : Φ (D'.xK x (ρ z)) ∈ D.P.L.U (jN PUnit.unit) := mem_pull.1 hz.1
  have mL : D'.xK x (ρ z) ∈ D'.P.L.U jL := hz.2
  have hp : (ρ ≫ D'.xK x) ≫ Φ = ρ ≫ D.xK y := by rw [Category.assoc, hx]
  have mN' : (ρ ≫ D.xK y) z ∈ D.P.L.U (jN PUnit.unit) := by rw [← hp]; exact mN
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (K := PUnit) (fun _ => ρ ≫ D.xK y) jN (fun _ _ _ => rfl)
    (fun _ => mN')
  obtain ⟨j₀, hj₀⟩ := exists_chart hM₀ (φ (Φ (D'.xK x (ρ z))))
  have hj₀' : φ ((ρ ≫ D.xK y) z) ∈ M₀.U j₀ := by rw [← hp]; exact hj₀
  have e := ((genRel_iff w _ t₀ s z).1 h).2 jN (fun _ => j₀) (fun _ => hj₀') (fun _ => mN')
  have e' := ((genRel_iff w' _ t₀ s z).1 h').2 (fun _ => jL) (fun _ => j₀) (fun _ => hj₀) (fun _ => mL)
  have E := Units.ext (e.trans e'.symm)
  rw [Fintype.prod_unique, Fintype.prod_unique, T _ (ρ ≫ D'.xK x) z j₀ (jN PUnit.unit) jL hj₀ mN mL, hp, mul_zpow,
    _root_.mul_assoc] at E
  have E' := mul_left_cancel E
  have a₁ := gm_pullGen D.P.L (fun _ : PUnit => D.xK y) _ (D.psi y) ρ (𝟙 _) z jN (Set.mem_iInter.2 fun _ => mN')
  have a₂ := gm_pullGen D'.P.L (fun _ : PUnit => D'.xK x) _ (D'.psi x) ρ (𝟙 _) z (fun _ => jL)
    (Set.mem_iInter.2 fun _ => mL)
  rw [Category.id_comp] at a₁ a₂
  have v := vb _ ρ z J hJ
  rw [val_of b ρ z J jN (fun k => by rw [hx]; exact eJ k), val_of (D.psi y) ρ z J jN eJ] at v
  refine (gm_res _ z _ hz _).trans (v.trans (a₁.symm.trans (E'.trans (Eq.symm ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ ((gm_res _ z _ hz _).trans a₂.symm)))))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull ρ _ z _ hz _))

theorem exists_isPullDeg_id (D D' : DegPre R) {S₀ : Scheme.{0}} {A₀ : Over S₀} [GrpObj A₀] {M₀ : LB A₀.left}
    (hM₀ : M₀.IsLB) (rig₀ : LB.Gen (M₀.pull (eSec A₀))) {f : Sp R ⟶ S₀} {φ : D.P.A.left ⟶ A₀.left}
    {φ' : D'.P.A.left ⟶ A₀.left} (p : IsGrpPullback D.P.A A₀ f φ) (p' : IsGrpPullback D'.P.A A₀ f φ')
    (w : LB.Iso D.P.L (M₀.pull φ)) (w' : LB.Iso D'.P.L (M₀.pull φ')) (g : PGen w) (g' : PGen w')
    (r : PMaps w (K := PUnit) (fun _ => eSec D.P.A) (fun _ => eSec A₀) (fun _ => 1) D.rig rig₀ f)
    (r' : PMaps w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec A₀) (fun _ => 1) D'.rig rig₀ f)
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ φ' = (D.c (xe x)).left ≫ φ)
    (Wo : (Spec (CommRingCat.of R)).Opens) (hWo : genericPoint (Spec (CommRingCat.of R)) ∈ Wo) (ψW : PsiOn D Wo)
    {F : Type} [Field F] (ρ : Sp F ⟶ (TK R).left)
    (hψ : ∀ x, ∃ (pt₀ : PUnit → (Sp F ⟶ A₀.left)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ (fun _ => -1))) (s : F),
      GenRel w (LB.pullGen _ _ _ (D.psi (xe x)) ρ) t₀ s ∧ GenRel w' (LB.pullGen _ _ _ (D'.psi x) ρ) t₀ s) :
    ∃ hD : IsPullDeg (RingHom.id R) D D',
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ = φ' ∧ (∀ x, hD.xe x = xe x) ∧
      ∃ w₁ : LB.Iso D'.P.L (M₀.pull ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) ≫ φ)),
        HEq w₁ w' ∧ Tri w hD.w w₁ := by
  have hs := specOf_id R
  have hsf : specOf (RingHom.id R) ≫ f = f := by rw [hs, Category.id_comp]
  obtain ⟨e, me, he⟩ := grpPullback_iso p'
    (((isGrpPullback_pullback D.P.A (specOf (RingHom.id R))).comp p).congr hsf rfl)
  rw [← Category.assoc] at he
  subst he
  have gp : IsGrpPullback D'.P.A D.P.A (specOf (RingHom.id R))
      (e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R))) :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback D.P.A (specOf (RingHom.id R)))).congr
      (Category.id_comp _) rfl
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec D.P.A := (cubeMapOf gp).e_comm
  obtain ⟨wD, T⟩ := exists_cancel hM₀ w w' g g' D.P.isLB D'.P.isLB
  have hc' : ∀ x, (D'.c x).left ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      (D.c (xe x)).left := fun x => by
    apply p.1.hom_ext
    · rw [Category.assoc]; exact hc x
    · rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w, Over.w, hs]; exact Category.comp_id _
  obtain ⟨gW, hgW⟩ : ∃ gW : (TK R).left ⟶ (TW Wo).left, gW ≫ Wo.ι = jK R :=
    ⟨IsOpenImmersion.lift Wo.ι (jK R) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hy : jK R y = genericPoint (Spec (CommRingCat.of R)) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        show Ideal.comap (algebraMap R (FractionRing R)) (PrimeSpectrum.asIdeal y) = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ (PrimeSpectrum.asIdeal y) (PrimeSpectrum.isPrime y)]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
      show jK R y ∈ Wo
      rw [hy]; exact hWo), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ Wo).toScheme, lam ≫ (jK R ⁻¹ᵁ Wo).ι = 𝟙 _ ∧
      lam ≫ (jK R ∣_ Wo) = gW :=
    ⟨(isPullback_morphismRestrict (jK R) Wo).lift _ _ (hgW.trans (Category.id_comp _).symm),
      (isPullback_morphismRestrict (jK R) Wo).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) Wo).lift_fst _ _ _⟩
  refine ⟨⟨e, me, wD, (isGen_iff _).2 (T.pgen_cancel hM₀ g g'), hE, ?_, xe,
    fun x => (hc' x).trans (by rw [hs, Category.id_comp]), Wo, ψW, gW, hgW.trans (by rw [hs, Category.comp_id]),
    fun x => ?_⟩, rfl, fun _ => rfl, w', HEq.rfl, T⟩
  · refine (maps_iff wD _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf (RingHom.id R)) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf (RingHom.id R)) hE D.P.L) (fun _ => rfl)).2 ?_
    exact T.pmaps_cancel hM₀ (fun _ => hE) r (by rw [hsf]; exact r')
  · obtain ⟨pt₀, t₀, s, h, h'⟩ := hψ x
    obtain ⟨b, hb, vb⟩ := mapsAt_of_genRel hM₀ T ρ x (xe x)
      ((Category.assoc _ _ _).trans (congrArg (jK R ≫ ·) (hc' x))) t₀ s h h'
    refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (vb _ _ y J hJ).trans ?_⟩
    have v := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂] at v
    exact v.symm.trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp])).symm

end GlobalTheory.ArcData

namespace GlobalTheory

theorem arcWit_data_iso : Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ'), ∃ (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) := by
  intro h5 E _ _ _ H D l c₀ c k _ bF a O O' _ _ β β' Y Y' χ χ' W W'
  obtain ⟨s1, s2, s3, -, s5, s6⟩ := W.spec
  obtain ⟨t1, t2, t3, -, t5, t6⟩ := W'.spec
  obtain ⟨Wo, hWo, ⟨ψW⟩⟩ := h5.psiOnExists _ _ (admissibleBase_powerSeries k) W'.P.D
  let F := AlgebraicClosure (FractionRing (PowerSeries k))
  let κ : k →+* F := ((algebraMap (FractionRing (PowerSeries k)) F).comp (algebraMap (PowerSeries k) _)).comp
    (PowerSeries.C (R := k))
  letI : Algebra (FractionRing k) F := (IsFractionRing.lift (K := FractionRing k) (g := κ) κ.injective).toAlgebra
  have ha : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C (R := k) x)) :=
    fun x => IsFractionRing.lift_algebraMap (K := FractionRing k) (g := κ) κ.injective x
  have k₁ := (s6 F _ ha rfl).1
  have k₂ := (t6 F _ ha rfl).1
  let xe : W.P.D.toPre.X ≃+ W'.P.D.toPre.X := W.e.symm.toAddEquiv.trans W'.e.toAddEquiv
  have hxe : ∀ y, xe (W.e y) = W'.e y := fun y => congrArg W'.e (W.e.symm_apply_apply y)
  obtain ⟨hD, h₁, h₂, h₃⟩ := ArcData.exists_isPullDeg_id W'.P.D.toPre W.P.D.toPre a.D₀.P.isLB a.D₀.rig t1 s1 W'.w W.w
    ((isGen_iff _).1 t2) ((isGen_iff _).1 s2)
    ((maps_iff W'.w _ (fun _ => eSec a.D₀.P.A) _ W'.P.D.toPre.rig a.D₀.rig _ _
      (rigPull_le W'.φ _ W'.he a.D₀.P.L) (fun _ => rfl)).1 t3)
    ((maps_iff W.w _ (fun _ => eSec a.D₀.P.A) _ W.P.D.toPre.rig a.D₀.rig _ _
      (rigPull_le W.φ _ W.he a.D₀.P.L) (fun _ => rfl)).1 s3)
    xe (fun x => by
      obtain ⟨y, rfl⟩ := W.e.surjective x
      rw [hxe]
      exact (s5 y).trans (t5 y).symm) Wo hWo ψW (F := F) (jFK (R := PowerSeries k) F) (fun x => by
      obtain ⟨y, rfl⟩ := W.e.surjective x
      rw [hxe]
      exact ⟨_, _, _, k₂ y, k₁ y⟩)
  exact ⟨hD, h₁, fun x => (h₂ _).trans (hxe x), h₃⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepComb
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepComb
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange

namespace GlobalTheory

theorem sval_eq_zero_of_indep_comb :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (X Y Y' : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of R)) [Flat π] (π' : Y' ⟶ Spec (CommRingCat.of R')) (p : Y' ⟶ Y), IsPullback p π' π (Spec.map (CommRingCat.ofHom f)) → ∀ (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (M : Type) [Fintype M] (β : M → R'), (∀ c : M → R, ∑ m, f (c m) * β m = 0 → ∀ m, c m = 0) → ∀ d : M → LB.Sec (LB.LinComb L φ ε), (∀ (y : Y') (J), Good L y J → ∑ m, constVal π' y (β m) * sval (d m) p y J = 0) → ∀ (m : M) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval (d m) r z J = 0 := by
  intro R R' _ _ f X Y Y' π _ π' p H L hL K _ φ ε M _ β hβ d hd m Z r z J hJ
  let e := (Fintype.equivFin M).symm
  have key := ThetaSpecialise.sec_indep H ε (φ := φ) (φ' := fun k => p ≫ φ k) (fun _ => rfl) (fun i => β (e i))
    (fun a ha i => by
      have := hβ (fun m => a (e.symm m)) (by
        rw [← ha, ← e.sum_comp]
        simp only [Equiv.symm_apply_apply]) (e i)
      simpa only [Equiv.symm_apply_apply] using this)
    (fun i => d (e i)) (sec_ext' hL fun y J hJ => by
      rw [sval_sum' hJ, sval_zero' hJ, ← hd y J hJ, ← e.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sval_smul' hJ]
      exact congrArg₂ (· * ·) (by rw [Category.id_comp])
        ((sval_pullOver H.w _ _ _ hJ).trans (by rw [Category.id_comp]))) (e.symm m)
  rw [Equiv.apply_symm_apply] at key
  exact (congrArg (fun s => sval s r z J) key).trans (sval_zero' (π := π) hJ r)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfIndepCombStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBaseChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sval_eq_zero_of_linearIndependent_comb : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (X Y Y' : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of R)) [Flat π] (π' : Y' ⟶ Spec (CommRingCat.of R')) (p : Y' ⟶ Y), IsPullback p π' π (Spec.map (CommRingCat.ofHom f)) → ∀ (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (M : Type) [Fintype M] (β : M → R'), (∀ c : M → R, ∑ m, f (c m) * β m = 0 → ∀ m, c m = 0) → ∀ d : M → LB.Sec (LB.LinComb L φ ε), (∀ (y : Y') (J), Good L y J → ∑ m, constVal π' y (β m) * sval (d m) p y J = 0) → ∀ (m : M) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval (d m) r z J = 0 := by
  first | exact @GlobalTheory.sval_eq_zero_of_indep_comb | exact GlobalTheory.sval_eq_zero_of_indep_comb | (intros; apply GlobalTheory.sval_eq_zero_of_indep_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenOfChartPull
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_gen_of_chartPull {Y Y' : Scheme.{0}} {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (t : LB.Gen A) (ht : t.IsGen) : ∃ t' : LB.Gen A', t'.IsGen := by
  refine ⟨⟨fun i => res (a.le i) (pullU h _ (t.s (a.idx i)))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have v : ∀ i, y ∈ A'.U i → gm (𝟙 Y') y _ (res (a.le i) (pullU h _ (t.s (a.idx i)))) =
      gm h y (A.U (a.idx i)) (t.s (a.idx i)) := fun i hi =>
    (gm_res (𝟙 Y') y (a.le i) hi _).trans ((gm_pull (𝟙 Y') h y _ (a.le i hi) _).trans (by rw [Category.id_comp]))
  have hm : h y ∈ A.U (a.idx i) ⊓ A.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := congrArg (gm h y (A.U (a.idx i) ⊓ A.U (a.idx j))) (ht (a.idx i) (a.idx j))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg (_ * ·) (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (v i hy.1)).trans (e'.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (a.g y i j hy.1 hy.2)
    ((gm_res (𝟙 Y') y _ hy _).trans (v j hy.2)))

theorem polarisation_extends : Laws → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∃ L : RigLB G, LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V)))) := by
  intro hL V _ _ _ A G _ _ hG gen hgen
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  obtain ⟨t, ht⟩ := A.rigid
  have e₁ : eSec ((Over.pullback (jK V)).obj G) ≫ gen.hom.left = eSec A.A := by
    unfold eSec
    rw [← Over.comp_left, IsMonHom.one_hom]
  have e₂ : eSec ((Over.pullback (jK V)).obj G) ≫ jA V (FractionRing V) G = eK V (FractionRing V) G := by
    unfold eSec eK eSec
    simp
  obtain ⟨ρ, hρ⟩ := exists_gen_of_chartPull
    (chartPullLinComb A.L gen.hom.left (K := PUnit) (fun _ => eSec ((Over.pullback (jK V)).obj G))
      (fun _ => eSec A.A) (fun _ => 1) (𝟙 _) (fun _ => e₁.trans (Category.id_comp _).symm)) t ht
  obtain ⟨L, φ, hφ⟩ := hL.extend V (FractionRing V) G _ e₂ (A.L.pull gen.hom.left) (pull_isLB A.isLB _) ρ hρ
  exact ⟨L, LBIso.symm ⟨φ, hφ⟩⟩

end GlobalTheory.UU
end
