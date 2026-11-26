module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)

universe u v

namespace UpperTheory.Gal.G3

abbrev etG (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] : Th.{1} (sp k) ℚ_[l] :=
  (et l (sp Ω)).bc (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

def AlgIsoPts : Prop := ∀ (D E : Type) [CommRing D] [CommRing E] [Algebra D E] [Algebra.Etale D E],
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : D →+* Ω), ∃! y : E →+* Ω, y.comp (algebraMap D E) = x) →
  Function.Bijective (algebraMap D E)

def AlgSplit : Prop := ∀ (A A' C : Type) [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C] [Algebra.Etale A A']
  (J : Type) [Fintype J] (τ : J → (A' →ₐ[A] C)),
  (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : C →+* Ω) (y : A' →+* Ω), y.comp (algebraMap A A') = x.comp (algebraMap A C) →
    ∃! j, x.comp (τ j : A' →+* C) = y) →
  ∃ e : C ⊗[A] A' ≃ₐ[C] (J → C), ∀ b j, e (1 ⊗ₜ b) j = τ j b

def AlgTr : Prop := ∀ (A A' C : Type) [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C] [Module.Finite A A']
  [Algebra.Etale A A'] (J : Type) [Fintype J] (τ : J → (A' →ₐ[A] C)) (e : C ⊗[A] A' ≃ₐ[C] (J → C)),
  (∀ b j, e (1 ⊗ₜ b) j = τ j b) → ∀ b, algebraMap A C (etTrace A A' b) = ∑ j, τ j b

def FEtBasic : Prop :=
  (∀ {P Y Z' Z : Scheme.{0}} (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z) (d : ℕ), IsPullback v s' s g → FEt s d → FEt s' d) ∧
  (∀ {W Y Z : Scheme.{0}} (r : W ⟶ Y) (s : Y ⟶ Z) (d e : ℕ), FEt r e → FEt s d → FEt (r ≫ s) (d * e)) ∧
  ∀ {W Z : Scheme.{0}} (c : W ⟶ Z) (G : Type) [Group G] [Finite G] (a : G → (W ⟶ W)), IsGalois c G a → FEt c (Nat.card G)

def SplitsBasic : Prop :=
  (∀ {Z Y W W' : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Finite J] (σ : J → (W ⟶ Y)) (g : W' ⟶ W),
    Splits s c σ → Splits s (g ≫ c) fun j => g ≫ σ j) ∧
  ∀ {P Y Z' Z W : Scheme.{0}} (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z) [IsFinite s] [Etale s], IsPullback v s' s g →
    ∀ (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P)), (∀ j, σ j ≫ s' = c) →
      (Splits s' c σ ↔ Splits s (c ≫ g) fun j => σ j ≫ v)

def OrdEx : Prop := ∀ {Z Y : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (d : ℕ), ∃ (W : Scheme.{0}) (c : W ⟶ Z)
  (σ : Fin d → (W ⟶ Y)), IsFinite c ∧ Etale c ∧ (∀ j, σ j ≫ s = c) ∧
  (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j) ∧
  ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin d → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
    (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
    ∃! w : U ⟶ W, w ≫ c = z ∧ ∀ j, w ≫ σ j = y j

def OrdStep : Prop := ∀ {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (d : ℕ) (σ : Fin d → (W ⟶ Y)),
  (∀ j, σ j ≫ s = c) → ∃ V : (pullback s c).Opens, IsClosed (V : Set ↑(pullback s c)) ∧
    ∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ pullback s c),
      (x (IsLocalRing.closedPoint Ω) ∈ V ↔ ∀ j, x ≫ pullback.snd s c ≫ σ j ≠ x ≫ pullback.fst s c)

def GalClosD : Prop := ∀ {Z Y : Scheme.{0}} (s : Y ⟶ Z) (d : ℕ), FEt s d →
  ∃ (W : Scheme.{0}) (c : W ⟶ Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (σ : Fin d → (W ⟶ Y)),
    IsGalois c G a ∧ Splits s c σ

def MultiSplit : Prop := ∀ {Z : Scheme.{0}} (n : ℕ) (Y : Fin n → Scheme.{0}) (s : ∀ i, Y i ⟶ Z) (d : Fin n → ℕ),
  (∀ i, FEt (s i) (d i)) → ∃ (W : Scheme.{0}) (c : W ⟶ Z) (e : ℕ), 0 < e ∧ FEt c e ∧
    ∀ i, ∃ σ : Fin (d i) → (W ⟶ Y i), Splits (s i) c σ

def FEtInj : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {Z W : Scheme.{0}} (p : Z ⟶ B)
  (r : W ⟶ B) (c : W ⟶ Z) (hc : c ≫ p = r) (d : ℕ), 0 < d → FEt c d → Function.Injective (T.pull c hc)

def TrBase : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {P Y Z' Z : Scheme.{0}}
  (p : Z ⟶ B) (q : Y ⟶ B) (p' : Z' ⟶ B) (q' : P ⟶ B) (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z) (d : ℕ)
  (hv : v ≫ q = q') (hg : g ≫ p = p'), s' ≫ p' = q' → IsPullback v s' s g → FEt s d →
  ∀ tr tr', T.IsTr p q s tr → T.IsTr p' q' s' tr' → ∀ x, T.pull g hg (tr x) = tr' (T.pull v hv x)

def TrPushM : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {Y P Z : Scheme.{0}}
  (p : Z ⟶ B) (q : P ⟶ B) (r : Y ⟶ B) (κ : Y ⟶ P) (s : P ⟶ Z) (d m : ℕ) (hκ : κ ≫ q = r), s ≫ p = q → FEt s d → FEt κ m →
  ∀ tr tr', T.IsTr p q s tr → T.IsTr p r (κ ≫ s) tr' → ∀ x, tr' (T.pull κ hκ x) = (m : R) • tr x

def SplitsComp : Prop := ∀ {Y P Z W : Scheme.{0}} (κ : Y ⟶ P) (s : P ⟶ Z) [IsFinite κ] [Etale κ] [IsFinite s] [Etale s]
  (c : W ⟶ Z) (I J : Type) [Finite I] [Finite J] (τ : I → (W ⟶ P)) (σ : I → J → (W ⟶ Y)), Splits s c τ →
  (∀ i, Splits κ (τ i) (σ i)) → Splits (κ ≫ s) c fun x : I × J => σ x.1 x.2

def LiesAbs : Prop := ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R), T.Good → ∀ {Z Y C D : Scheme.{0}}
  (pZ : Z ⟶ B) (pY : Y ⟶ B) (pC : C ⟶ B) (pD : D ⟶ B) (π : Z ⟶ Y) (hπ : π ≫ pY = pZ) (sg tg : C ⟶ Z) (htg : tg ≫ pZ = pC)
  (s t : D ⟶ Y) (ht : t ≫ pY = pD) (κ : C ⟶ D) (h : sg ≫ π = κ ≫ s) (d m : ℕ), sg ≫ pZ = pC → s ≫ pY = pD →
  κ ≫ t = tg ≫ π → FEt s d → FEt (pullback.lift sg κ h) m → ∀ tr trg, T.IsTr pY pD s tr → T.IsTr pZ pC sg trg →
  ∀ x, trg (T.pull tg htg (T.pull π hπ x)) = (m : R) • T.pull π hπ (tr (T.pull t ht x))

abbrev piK {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) :
    H.Z ⟶ pullback C.p (gen O k) := pullback.lift C.π H.q C.ov

theorem piK_snd {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) :
    piK C ≫ pullback.snd C.p (gen O k) = H.q := pullback.lift_snd _ _ _

def HopSpec : Prop := ∀ (l : ℕ) [Fact l.Prime] {k : Type} [Field k], (l : k) ≠ 0 → ∀ (H : HTower k) (Ω : Type) [Field Ω]
  [Algebra k Ω] (g : H.Γ) (d : ℕ), FEt (H.s g) d → IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (hop l H Ω g) ∧
    ∀ tr, (etG l k Ω).IsTr H.q (H.s g ≫ H.q) (H.s g) tr → hop l H Ω g = tr ∘ₗ (etG l k Ω).pull (H.t g) (H.comm g)

def LiesGen : Prop := ∀ {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L}
  (C : Cover H θ O) (g : H.Γ) {D : Scheme.{0}} (s t : D ⟶ C.Y) (hst : t ≫ C.p = s ≫ C.p) (m : ℕ), C.Lies g s t m →
  ∃ (κ : H.Y g ⟶ pullback (s ≫ C.p) (gen O k)) (h : H.s g ≫ piK C = κ ≫ bcMap (gen O k) s rfl),
    κ ≫ bcMap (gen O k) t hst = H.t g ≫ piK C ∧ FEt (pullback.lift (H.s g) κ h) m

def LiesOp : Prop := ∀ {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L}
  (C : Cover H θ O) (g : H.Γ) {D : Scheme.{0}} (s t : D ⟶ C.Y) (hst : t ≫ C.p = s ≫ C.p) (m d : ℕ), C.Lies g s t m →
  FEt (bcMap (gen O k) s (rfl : s ≫ C.p = _)) d → ∀ {R : Type} [Field R] (T : Th.{u} (sp k) R), T.Good →
  ∀ tr trg, T.IsTr (pullback.snd C.p (gen O k)) (pullback.snd (s ≫ C.p) (gen O k)) (bcMap (gen O k) s rfl) tr →
    T.IsTr H.q (H.s g ≫ H.q) (H.s g) trg →
    ∀ x, trg (T.pull (H.t g) (H.comm g) (T.pull (piK C) (piK_snd C) x)) =
      (m : R) • T.pull (piK C) (piK_snd C) (tr (T.pull (bcMap (gen O k) t hst) (bcMap_snd _ _ _) x))

def CoverInv : Prop := ∀ {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k} {θ : H.Γ → L}
  (C : Cover H θ O), C.Onto → ∀ {R : Type} [Field R] [CharZero R] (T : Th.{u} (sp k) R), T.Good →
  Function.Injective (T.pull (piK C) (piK_snd C)) ∧ ∀ y : T.H H.q,
    (∀ g, IsIso (H.s g) → θ g = 1 → ∃ tr, T.IsTr H.q (H.s g ≫ H.q) (H.s g) tr ∧ tr (T.pull (H.t g) (H.comm g) y) = y) →
    ∃ x, T.pull (piK C) (piK_snd C) x = y

def PieceLe : Prop := ∀ (l : ℕ) [Fact l.Prime] {k L O : Type} [Field k] [Field L] [Algebra ℚ_[l] L] [CommRing O] [Algebra O k],
  (l : k) ≠ 0 → ∀ {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O), C.Onto → ∀ (Ω : Type) [Field Ω] [Algebra k Ω],
  Function.Injective (((etG l k Ω).pull (piK C) (piK_snd C)).baseChange L) ∧
  ∀ y ∈ piece l H Ω L θ, ∃ x, ((etG l k Ω).pull (piK C) (piK_snd C)).baseChange L x = y

end UpperTheory.Gal.G3

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFnRing
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.G3

namespace UpperTheory.Gal.G3.FunctionRings

variable {G R : Type} [Group G] [Field R] {K : Subgroup G}

variable {B : Scheme.{0}} (X : Tower B G)

end UpperTheory.Gal.G3.FunctionRings

private theorem apply_out_mk_eq_of_tower_biinvariant {B : Scheme} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (j : X.ι) (f : G → R) (hf : ∀ k ∈ X.K j, ∀ g : G, f (k * g) = f g ∧ f (g * k) = f g) (w : G) :
    f ((QuotientGroup.mk w : G ⧸ X.K j).out) = f w := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (X.K j) w
  rw [hu]
  exact (hf _ u.2 w).2

private theorem tower_isFn_ind_inv_of_mem {B : Scheme} {G : Type} [Group G] (X : Tower B G) (R : Type) [Field R]
    (j : X.ι) (h : G) (hh : h ∈ X.Δ) : X.IsFn j (ind R (X.K j) h⁻¹) := by
  classical
  have key : ∀ g, ind R (X.K j) h⁻¹ g ≠ 0 ↔
      g ∈ DoubleCoset.doubleCoset h⁻¹ (X.K j : Set G) (X.K j) := by
    intro g
    unfold ind
    rw [Set.indicator_apply]
    split_ifs with hg <;> simp [hg]
  have memL : ∀ k ∈ X.K j, ∀ g, k * g ∈ DoubleCoset.doubleCoset h⁻¹ (X.K j : Set G) (X.K j) ↔
      g ∈ DoubleCoset.doubleCoset h⁻¹ (X.K j : Set G) (X.K j) := by
    intro k hk g
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨k⁻¹ * x, (X.K j).mul_mem ((X.K j).inv_mem hk) hx, y, hy, ?_⟩
      rw [show k⁻¹ * x * h⁻¹ * y = k⁻¹ * (x * h⁻¹ * y) by group, ← e]
      group
    · rintro ⟨x, hx, y, hy, e⟩
      exact ⟨k * x, (X.K j).mul_mem hk hx, y, hy, by rw [e]; group⟩
  have memR : ∀ k ∈ X.K j, ∀ g, g * k ∈ DoubleCoset.doubleCoset h⁻¹ (X.K j : Set G) (X.K j) ↔
      g ∈ DoubleCoset.doubleCoset h⁻¹ (X.K j : Set G) (X.K j) := by
    intro k hk g
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨x, hx, y * k⁻¹, (X.K j).mul_mem hy ((X.K j).inv_mem hk), ?_⟩
      rw [show x * h⁻¹ * (y * k⁻¹) = (x * h⁻¹ * y) * k⁻¹ by group, ← e]
      group
    · rintro ⟨x, hx, y, hy, e⟩
      exact ⟨x, hx, y * k, (X.K j).mul_mem hy hk, by rw [e]; group⟩
  refine ⟨fun k hk g => ⟨?_, ?_⟩, fun g hg => ?_, ?_⟩
  · unfold ind
    simp only [Set.indicator_apply, memL k hk g, Pi.one_apply]
  · unfold ind
    simp only [Set.indicator_apply, memR k hk g, Pi.one_apply]
  · obtain ⟨x, hx, y, hy, e⟩ := DoubleCoset.mem_doubleCoset.mp ((key g).mp hg)
    rw [e, show (x * h⁻¹ * y)⁻¹ = y⁻¹ * (h * x⁻¹) by group]
    exact X.Δ.mul_mem (X.K_le _ _ ((X.K j).inv_mem hy))
      (X.Δ.mul_mem hh (X.K_le _ _ ((X.K j).inv_mem hx)))
  · obtain ⟨m, -, -, hS⟩ := X.deep j {(j, h)}
    have hu : ∀ u ∈ X.K m, h * u * h⁻¹ ∈ X.K j :=
      fun u hu => hS (j, h) (Finset.mem_singleton_self _) u hu
    have fin : Finite (X.K j ⧸ (X.K m).subgroupOf (X.K j)) := by
      have := X.idx m j
      rw [Subgroup.relIndex, Subgroup.index] at this
      exact (Nat.card_ne_zero.mp this).2
    refine (Set.finite_range (fun q : X.K j ⧸ (X.K m).subgroupOf (X.K j) =>
      (QuotientGroup.mk (((q.out : X.K j) : G) * h⁻¹) : G ⧸ X.K j))).subset ?_
    intro y hy
    obtain ⟨x, hx, z, hz, e⟩ := DoubleCoset.mem_doubleCoset.mp ((key _).mp hy)
    refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
    obtain ⟨u, hu'⟩ := QuotientGroup.mk_out_eq_mul ((X.K m).subgroupOf (X.K j)) ⟨x, hx⟩
    have hum : ((u : X.K j) : G) ∈ X.K m := Subgroup.mem_subgroupOf.mp u.2
    have hc := hu _ hum
    simp only
    rw [hu']
    conv_rhs => rw [← QuotientGroup.out_eq' y]
    rw [e, QuotientGroup.eq]
    rw [show ((⟨x, hx⟩ * (u : X.K j) : X.K j) : G) = x * ((u : X.K j) : G) from rfl]
    rw [show (x * ((u : X.K j) : G) * h⁻¹)⁻¹ * (x * h⁻¹ * z) =
      (h * ((u : X.K j) : G) * h⁻¹)⁻¹ * z by group]
    exact (X.K j).mul_mem ((X.K j).inv_mem hc) hz

private theorem tower_isFn_add {B : Scheme} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (j : X.ι) (f f' : G → R) (hf : X.IsFn j f) (hf' : X.IsFn j f') : X.IsFn j (f + f') := by
  obtain ⟨a1, b1, c1⟩ := hf
  obtain ⟨a2, b2, c2⟩ := hf'
  refine ⟨fun k hk g => ?_, fun g hg => ?_, (c1.union c2).subset ?_⟩
  · simp [(a1 k hk g).1, (a1 k hk g).2, (a2 k hk g).1, (a2 k hk g).2]
  · by_cases h1 : f g = 0
    · exact b2 g (by simpa [h1] using hg)
    · exact b1 g h1
  · intro y hy
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
    exact hy (by simp [hn.1, hn.2])

private theorem tower_isFn_conv {B : Scheme} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (j : X.ι) (f f' : G → R) (hf : X.IsFn j f) (hf' : X.IsFn j f') :
    X.IsFn j (conv (X.K j) f f') := by
  obtain ⟨a1, b1, c1⟩ := hf
  obtain ⟨a2, b2, c2⟩ := hf'
  have nz : ∀ x, conv (X.K j) f f' x ≠ 0 →
      ∃ y : G ⧸ X.K j, f y.out ≠ 0 ∧ f' (y.out⁻¹ * x) ≠ 0 := by
    intro x hx
    by_contra hn
    push_neg at hn
    apply hx
    have h0 : ∀ y : G ⧸ X.K j, f y.out * f' (y.out⁻¹ * x) = 0 := by
      intro y
      by_cases h : f y.out = 0
      · simp [h]
      · simp [hn y h]
    simp only [conv, h0, finsum_zero]
  refine ⟨fun k hk g => ⟨?_, ?_⟩, fun g hg => ?_, ?_⟩
  · unfold conv
    rw [← finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (G ⧸ X.K j))]
    refine finsum_congr (fun z => ?_)
    have e1 : (MulAction.toPerm k : Equiv.Perm (G ⧸ X.K j)) z =
        (QuotientGroup.mk (k * z.out) : G ⧸ X.K j) := by
      conv_lhs => rw [← QuotientGroup.out_eq' z]
      rfl
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (X.K j) (k * z.out)
    rw [e1, hu, (a1 _ u.2 _).2, (a1 k hk _).1]
    congr 1
    rw [show (k * z.out * (u : G))⁻¹ * (k * g) = (u : G)⁻¹ * (z.out⁻¹ * g) by group]
    exact (a2 _ ((X.K j).inv_mem u.2) _).1
  · unfold conv
    refine finsum_congr (fun y => ?_)
    rw [← mul_assoc, (a2 k hk _).2]
  · obtain ⟨y, h1, h2⟩ := nz g hg
    have := X.Δ.mul_mem (b2 _ h2) (b1 _ h1)
    rwa [show (y.out⁻¹ * g)⁻¹ * y.out⁻¹ = g⁻¹ by group] at this
  · refine (Set.Finite.biUnion (t := fun y : G ⧸ X.K j =>
      (fun w => (y.out : G) • w) '' {z : G ⧸ X.K j | f' z.out ≠ 0}) c1
      (fun y _ => c2.image _)).subset ?_
    intro x hx
    obtain ⟨y, h1, h2⟩ := nz _ hx
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
    refine ⟨y, h1, QuotientGroup.mk (y.out⁻¹ * x.out), ?_, ?_⟩
    · rw [apply_out_mk_eq_of_tower_biinvariant X j f' a2]
      exact h2
    · rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_inv_cancel_left, QuotientGroup.out_eq']

private theorem tower_isFn_smul {B : Scheme} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (j : X.ι) (c : R) (f : G → R) (hf : X.IsFn j f) : X.IsFn j (c • f) := by
  obtain ⟨a1, b1, c1⟩ := hf
  refine ⟨fun k hk g => ?_, fun g hg => b1 g ?_, c1.subset ?_⟩
  · simp [(a1 k hk g).1, (a1 k hk g).2]
  · intro h0
    apply hg
    simp [h0]
  · intro y hy h0
    apply hy
    simp [h0]

open UpperTheory.Gal.G3.FunctionRings in
theorem UpperTheory.Gal.G3.pFnRing : FnRing := by
  intro B G _ X R _ j
  refine ⟨fun h hh => tower_isFn_ind_inv_of_mem X R j h hh, ?_,
    fun f f' hf hf' => ⟨tower_isFn_add X j f f' hf hf', tower_isFn_conv X j f f' hf hf'⟩,
    fun c f hf => tower_isFn_smul X j c f hf⟩
  refine ⟨fun k _ g => ⟨rfl, rfl⟩, fun g hg => (hg rfl).elim, ?_⟩
  simp
end
