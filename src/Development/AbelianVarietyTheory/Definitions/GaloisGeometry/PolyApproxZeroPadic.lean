module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormAevalSubLe
namespace GlobalTheory.NormAevalSubBound

theorem norm_aeval_sub_le {k : Type} [inst : NormedField k] [NormOneClass k] [IsUltrametricDist k]
    {J : Type} {x y : J → k} {δ : ℝ} (hδ : (0 : ℝ) ≤ δ) (hx : ∀ (j : J), ‖x j‖ ≤ (1 : ℝ))
    (hy : ∀ (j : J), ‖y j‖ ≤ (1 : ℝ)) (hxy : ∀ (j : J), ‖x j - y j‖ ≤ δ) (P : MvPolynomial J ℤ) :
    ‖(MvPolynomial.aeval x : MvPolynomial J ℤ → k) P‖ ≤ (1 : ℝ) ∧
    ‖(MvPolynomial.aeval y : MvPolynomial J ℤ → k) P‖ ≤ (1 : ℝ) ∧
    ‖(MvPolynomial.aeval x : MvPolynomial J ℤ → k) P -
      (MvPolynomial.aeval y : MvPolynomial J ℤ → k) P‖ ≤ δ := by
  have hadd : ∀ (a b : k) (r : ℝ), ‖a‖ ≤ r → ‖b‖ ≤ r → ‖a + b‖ ≤ r := fun a b r ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : ‖(a : k)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one k a
    refine ⟨?_, ?_, ?_⟩
    · simpa using h
    · simpa using h
    · simpa using hδ
  | add p q hp hq =>
    obtain ⟨p1, p2, p3⟩ := hp
    obtain ⟨q1, q2, q3⟩ := hq
    simp only [map_add (f := _)]
    refine ⟨hadd _ _ _ p1 q1, hadd _ _ _ p2 q2, ?_⟩
    rw [add_sub_add_comm]
    exact hadd _ _ _ p3 q3
  | mul_X p j hp =>
    obtain ⟨p1, p2, p3⟩ := hp
    simp only [map_mul, MvPolynomial.aeval_X]
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_mul]; exact mul_le_one₀ p1 (norm_nonneg _) (hx j)
    · rw [norm_mul]; exact mul_le_one₀ p2 (norm_nonneg _) (hy j)
    · have e : MvPolynomial.aeval x p * x j - MvPolynomial.aeval y p * y j =
          MvPolynomial.aeval x p * (x j - y j) +
            (MvPolynomial.aeval x p - MvPolynomial.aeval y p) * y j := by ring
      rw [e]
      refine hadd _ _ _ ?_ ?_
      · rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) p1).trans (hxy j)
      · rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (hy j)).trans p3

end GlobalTheory.NormAevalSubBound
end

noncomputable section

namespace GlobalTheory.Cong

variable {k : Type} [NormedField k]

def PolyApprox [IsUltrametricDist k] {J : Type} (θ : J → k) (S : Set (J → k)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (J → k)) (c : (J → k) → k), (s : Set (J → k)) ⊆ S ∧
    ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ η ∈ s, c η * MvPolynomial.aeval η P‖ ≤ ε

def trc {Γ A : Type} [Group Γ] [CommRing A] {a : ℕ} (r : Γ →* GL (Fin a) A) (g : Γ) : A :=
  ((r g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).trace

def LinApprox {Γ : Type} [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (Γ →* GL (Fin a) k)) (c : (Γ →* GL (Fin a) k) → k), (s : Set (Γ →* GL (Fin a) k)) ⊆ C ∧
    ∀ g : Γ, ‖trc r g - ∑ ρ ∈ s, c ρ * trc ρ g‖ ≤ ε

def opOf {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ) (v : V) : V :=
  f.sum fun g c => c • ρ g v

theorem PolyApprox.mono [IsUltrametricDist k] {J : Type} {θ : J → k} {S T : Set (J → k)} (h : PolyApprox θ S)
    (hST : S ⊆ T) : PolyApprox θ T := fun ε hε => by
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  exact ⟨s, c, hs.trans hST, hP⟩

variable [NormOneClass k] [IsUltrametricDist k]

theorem aeval_sub_le {J : Type} {x y : J → k} {δ : ℝ} (hδ : 0 ≤ δ) (hx : ∀ j, ‖x j‖ ≤ 1) (hy : ∀ j, ‖y j‖ ≤ 1)
    (hxy : ∀ j, ‖x j - y j‖ ≤ δ) (P : MvPolynomial J ℤ) :
    ‖MvPolynomial.aeval x P‖ ≤ 1 ∧ ‖MvPolynomial.aeval y P‖ ≤ 1 ∧
      ‖MvPolynomial.aeval x P - MvPolynomial.aeval y P‖ ≤ δ := by
  first
  | exact @_root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le
  | exact _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le
  | (apply _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le ..)

end GlobalTheory.Cong

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

abbrev Shv : Type 2 := Sheaf (Scheme.proetaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R))

omit [TopologicalSpace R] [IsTopologicalRing R] in
instance : HasSheafify (Scheme.proetaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

omit [TopologicalSpace R] [IsTopologicalRing R] in
instance : IsGrothendieckAbelian.{1} (Shv R) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ (ModuleCat.{1} (ULift.{1} R))

def coefPre : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj U := ModuleCat.of (ULift.{1} R) (ULift.{1} C(U.unop, R))
  map {U V} f := ModuleCat.ofHom
    { toFun := fun g => ⟨g.down.comp f.unop.base.hom⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def coef : Shv R := (presheafToSheaf _ _).obj (coefPre R)

def freeOn : Scheme.{0} ⥤ Shv R :=
  uliftYoneda.{1} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R)) ⋙ presheafToSheaf _ _

abbrev HS (F : Shv R) (n : ℕ) (X : Scheme.{0}) : Type 1 := Abelian.Ext.{1} ((freeOn R).obj X) F n

def H (n : ℕ) (X : Scheme.{0}) : Type 1 := HS R (coef R) n X

instance (n : ℕ) (X : Scheme.{0}) : AddCommGroup (H R n X) := inferInstanceAs (AddCommGroup (HS R (coef R) n X))

instance (n : ℕ) (X : Scheme.{0}) : Module R (H R n X) :=
  Module.compHom (HS R (coef R) n X) (ULift.ringEquiv.symm : R ≃+* ULift.{1} R).toRingHom

def pull (n : ℕ) {X Y : Scheme.{0}} (f : X ⟶ Y) : H R n Y →ₗ[R] H R n X where
  toFun x := (Abelian.Ext.mk₀ ((freeOn R).map f)).comp (x : HS R (coef R) n Y) (zero_add n)
  map_add' x y := Abelian.Ext.comp_add _ _ _ _
  map_smul' r x := Abelian.Ext.comp_smul _ _ _ (ULift.up r : ULift.{1} R)

theorem pull_id (n : ℕ) (X : Scheme.{0}) : pull R n (𝟙 X) = LinearMap.id := by
  ext x
  change (Abelian.Ext.mk₀ ((freeOn R).map (𝟙 X))).comp (x : HS R (coef R) n X) (zero_add n) = x
  rw [CategoryTheory.Functor.map_id]
  exact Abelian.Ext.mk₀_id_comp _

theorem pull_comp (n : ℕ) {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull R n (f ≫ g) = (pull R n f).comp (pull R n g) := by
  ext x
  change (Abelian.Ext.mk₀ ((freeOn R).map (f ≫ g))).comp (x : HS R (coef R) n Z) (zero_add n) =
    (Abelian.Ext.mk₀ ((freeOn R).map f)).comp ((Abelian.Ext.mk₀ ((freeOn R).map g)).comp (x : HS R (coef R) n Z) (zero_add n)) (zero_add n)
  rw [Functor.map_comp]
  exact (Abelian.Ext.mk₀_comp_mk₀_assoc _ _ _).symm

section Galois

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

abbrev geom : Scheme.{0} := pullback p (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

def galMap (σ : Ω ≃ₐ[k] Ω) : geom Ω p ⟶ geom Ω p :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    congr 3
    ext x
    simp)

@[reassoc] theorem galMap_fst (σ : Ω ≃ₐ[k] Ω) : galMap Ω p σ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc] theorem galMap_snd (σ : Ω ≃ₐ[k] Ω) :
    galMap Ω p σ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) := pullback.lift_snd _ _ _

def geomMap {Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y) (hu : u ≫ q = p) : geom Ω p ⟶ geom Ω q :=
  pullback.lift (pullback.fst _ _ ≫ u) (pullback.snd _ _) (by rw [Category.assoc, hu, pullback.condition])

end Galois

abbrev fibre {O K : Type} [CommRing O] [CommRing K] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) (φ : O →+* K) : Scheme.{0} :=
  pullback p (Spec.map (CommRingCat.ofHom φ))

end GlobalTheory.Et

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OfNatTrans
set_option autoImplicit false

noncomputable section

open CategoryTheory

universe v u v' u'

namespace GlobalTheory.CatH

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{0} R)

abbrev Cn (n : ℕ) : Type (max u v) := ∀ s : ComposableArrows C n, F.obj (s.obj (Fin.last n))

def face {n : ℕ} (i : Fin (n + 2)) (s : ComposableArrows C (n + 1)) : ComposableArrows C n :=
  (Fin.succAboveOrderEmb i).monotone.functor ⋙ s

def toLast {n : ℕ} (i : Fin (n + 2)) (s : ComposableArrows C (n + 1)) :
    (face i s).obj (Fin.last n) ⟶ s.obj (Fin.last (n + 1)) :=
  s.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n))))

def d (n : ℕ) : Cn F n →ₗ[R] Cn F (n + 1) where
  toFun f s := ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s))
  map_add' f g := by
    funext s
    simp only [Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    funext s
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

def Bn : ∀ n : ℕ, Submodule R (Cn F n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (d F n)

abbrev H (n : ℕ) : Type (max u v) := LinearMap.ker (d F n) ⧸ (Bn F n).submoduleOf (LinearMap.ker (d F n))

variable {F} {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C'] {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'}

structure Mor (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R') (σ : R →+* R') where

  G : C' ⥤ C

  τ : ∀ T : C', F.obj (G.obj T) →ₛₗ[σ] F'.obj T
  nat : ∀ {T T' : C'} (φ : T ⟶ T') (x : F.obj (G.obj T)), τ T' ((F.map (G.map φ)).hom x) = (F'.map φ).hom (τ T x)

namespace Mor

def id (F : C ⥤ ModuleCat.{0} R) : Mor F F (RingHom.id R) where
  G := 𝟭 C
  τ _ := LinearMap.id
  nat _ _ := rfl

def restrict (F : C ⥤ ModuleCat.{0} R) (G : C' ⥤ C) : Mor F (G ⋙ F) (RingHom.id R) where
  G := G
  τ _ := LinearMap.id
  nat _ _ := rfl

def ofNatTrans {F₁ : C ⥤ ModuleCat.{0} R} (α : F ⟶ F₁) : Mor F F₁ (RingHom.id R) where
  G := 𝟭 C
  τ T := (α.app T).hom
  nat φ x := by
    change ((F.map φ ≫ α.app _).hom) x = ((α.app _ ≫ F₁.map φ).hom) x
    rw [α.naturality]

variable (m : Mor F F' σ)

def pullC (n : ℕ) : Cn F n →ₛₗ[σ] Cn F' n where
  toFun f s := m.τ _ (f (s ⋙ m.G))
  map_add' f g := funext fun s => map_add (m.τ _) _ _
  map_smul' r f := funext fun s => LinearMap.map_smulₛₗ (m.τ _) _ _

theorem d_pullC (n : ℕ) (f : Cn F n) : d F' n (m.pullC n f) = m.pullC (n + 1) (d F n f) := by
  funext s
  change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F'.map (toLast i s)).hom (m.τ _ (f (face i s ⋙ m.G))) =
    m.τ _ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (m.G.map (toLast i s))).hom (f (face i s ⋙ m.G)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_zsmul, m.nat]

def pullZ (n : ℕ) : LinearMap.ker (d F n) →ₛₗ[σ] LinearMap.ker (d F' n) :=
  ((m.pullC n).domRestrict _).codRestrict _ fun f => by
    change d F' n (m.pullC n f.1) = 0
    rw [m.d_pullC, f.2, map_zero]

def pull (n : ℕ) : H F n →ₛₗ[σ] H F' n :=
  Submodule.mapQ _ _ (m.pullZ n) (by
    intro f hf
    change m.pullC n f.1 ∈ Bn F' n
    have hf' : f.1 ∈ Bn F n := hf
    cases n with
    | zero =>
      have : f.1 = 0 := hf'
      rw [this, map_zero]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨g, hg⟩ := hf'
      exact ⟨m.pullC n g, by rw [m.d_pullC, hg]⟩)

end Mor

end GlobalTheory.CatH
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReductionUniformizerPoint
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

def ideal (S : Finset ι) : X.IdealSheafData := ⨆ i ∈ S, I i

theorem le_ideal {S : Finset ι} {i : ι} (h : i ∈ S) : I i ≤ ideal I S :=
  le_iSup₂ (f := fun i (_ : i ∈ S) => I i) i h

theorem ideal_mono {S S' : Finset ι} (h : S ⊆ S') : ideal I S ≤ ideal I S' :=
  iSup₂_le fun _ hi => le_ideal I (h hi)

def Y (S : Finset ι) : Scheme.{0} := (ideal I S).subscheme

def Yι (S : Finset ι) : Y I S ⟶ X := (ideal I S).subschemeι

def incl {S S' : Finset ι} (h : S ⊆ S') : Y I S' ⟶ Y I S :=
  Scheme.IdealSheafData.inclusion (ideal_mono I h)

abbrev Idx (ι : Type) (s : ℕ) : Type := {S : Finset ι // S.card = s + 1}

def Ystr (s : ℕ) : Scheme.{0} := ∐ fun S : Idx ι s => Y I S.1

def inj {s : ℕ} (S : Idx ι s) : Y I S.1 ⟶ Ystr I s := Sigma.ι (fun S : Idx ι s => Y I S.1) S

section Face

variable [LinearOrder ι]

def face {s : ℕ} (S : Idx ι (s + 1)) (j : Fin (s + 2)) : Idx ι s :=
  ⟨S.1.erase (S.1.orderEmbOfFin S.2 j), by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), S.2]; rfl⟩

theorem face_subset {s : ℕ} (S : Idx ι (s + 1)) (j : Fin (s + 2)) : (face S j).1 ⊆ S.1 :=
  Finset.erase_subset _ _

def δ (s : ℕ) (j : Fin (s + 2)) : Ystr I (s + 1) ⟶ Ystr I s :=
  Sigma.desc fun S : Idx ι (s + 1) => incl I (face_subset S j) ≫ inj I (face S j)

end Face

end GlobalTheory.Strata

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

section Fibre

variable {O : Type} [CommRing O] (p : X ⟶ Spec (CommRingCat.of O)) (ϖ : O)

end Fibre

section BaseChange

variable {X' : Scheme.{0}} (f : X' ⟶ X)

end BaseChange

theorem nonempty_Ystr {s : ℕ} (S : Idx ι s) (y : Y I S.1) : Nonempty (Ystr I s) := ⟨(inj I S).base y⟩

theorem isEmpty_Ystr {s : ℕ} (h : IsEmpty (Idx ι s)) : IsEmpty (Ystr I s) :=
  ⟨fun x => IsEmpty.false ((Sigma.desc (fun S : Idx ι s => (isEmptyElim S : Y I S.1 ⟶ ∅)) : Ystr I s ⟶ ∅).base x)⟩

theorem nonempty_Y_iff (S : Finset ι) : Nonempty (Y I S) ↔ ((ideal I S).support : Set X).Nonempty := by
  rw [← Set.range_nonempty_iff_nonempty (f := (Yι I S).base)]
  unfold Yι
  rw [← Scheme.IdealSheafData.range_subschemeι]
  rfl

end GlobalTheory.Strata

namespace GlobalTheory.Strata

variable {X : Scheme.{0}} {ι : Type} (I : ι → X.IdealSheafData)

section FibreStr

variable {O : Type} [CommRing O] (p : X ⟶ Spec (CommRingCat.of O)) (ϖ : O)

end FibreStr

section BaseChangeStr

variable {X' : Scheme.{0}} (f : X' ⟶ X)

end BaseChangeStr

end GlobalTheory.Strata

namespace GlobalTheory.Strata.Example

open MvPolynomial

variable (O : Type) [CommRing O] (ϖ : O)

abbrev A : Type := MvPolynomial (Fin 2) O ⧸ Ideal.span {X 0 * X 1 - C ϖ}

def T (k : Fin 2) : A O ϖ := Ideal.Quotient.mk _ (X k)

abbrev XS : Scheme.{0} := Spec (CommRingCat.of (A O ϖ))

def compIdeal (k : Fin 2) : (XS O ϖ).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of (A O ϖ))).inv.hom (T O ϖ k)})

def red : A O ϖ →+* O ⧸ Ideal.span {ϖ} :=
  Ideal.Quotient.lift _ (eval₂Hom (Ideal.Quotient.mk _) (fun _ => 0)) (by
    intro a ha
    rw [Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    simp [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self])

theorem reduction_uniformizerPoint (k : Fin 2) : red O ϖ (T O ϖ k) = 0 := by simp [red, T]

theorem mem_support_compIdeal (x : XS O ϖ) (k : Fin 2) (hx : T O ϖ k ∈ x.asIdeal) :
    x ∈ ((compIdeal O ϖ k).support : Set (XS O ϖ)) := by
  rw [compIdeal, Scheme.IdealSheafData.coe_support_ofIdealTop, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton,
    basicOpen_eq_of_affine]
  exact fun h' => (PrimeSpectrum.mem_basicOpen (x := (x : PrimeSpectrum (A O ϖ))) _).1 h' hx

theorem isEmpty_Ystr_two : IsEmpty (Ystr (compIdeal O ϖ) 2) :=
  isEmpty_Ystr _ ⟨fun S => by have := S.1.card_le_univ; have h2 := S.2; simp at this; omega⟩

theorem nonempty_Ystr_one (h : ¬ IsUnit ϖ) : Nonempty (Ystr (compIdeal O ϖ) 1) := by
  haveI : Nontrivial (O ⧸ Ideal.span {ϖ}) :=
    Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (O ⧸ Ideal.span {ϖ})
  let x : XS O ϖ := ⟨M.comap (red O ϖ), Ideal.comap_isPrime _ _⟩
  have hx : x ∈ ((ideal (compIdeal O ϖ) Finset.univ).support : Set (XS O ϖ)) := by
    simp only [ideal, Scheme.IdealSheafData.support_iSup, TopologicalSpace.Closeds.coe_iInf, Set.mem_iInter]
    intro k _
    refine mem_support_compIdeal O ϖ x k ?_
    show red O ϖ (T O ϖ k) ∈ M
    rw [reduction_uniformizerPoint]; exact zero_mem _
  obtain ⟨y⟩ := (nonempty_Y_iff (compIdeal O ϖ) Finset.univ).2 ⟨x, hx⟩
  exact nonempty_Ystr (compIdeal O ϖ) (s := 1) ⟨Finset.univ, by simp⟩ y

end GlobalTheory.Strata.Example

namespace GlobalTheory.Strata

theorem orderEmbOfFin_univ_fin {n : ℕ} (h : (Finset.univ : Finset (Fin n)).card = n) :
    ((Finset.univ : Finset (Fin n)).orderEmbOfFin h : Fin n → Fin n) = id :=
  (Finset.orderEmbOfFin_unique h (f := id) (fun _ => Finset.mem_univ _) strictMono_id).symm

end GlobalTheory.Strata
end
end
