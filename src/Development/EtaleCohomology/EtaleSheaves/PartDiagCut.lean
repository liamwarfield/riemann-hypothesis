module

public import Development.EtaleCohomology.EtaleSheaves.HensCut
public import Development.EtaleCohomology.EtaleSheaves.TorEtPf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.PartDiagCut
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.E.PartDiagCut

structure Part (A : Type) [CommRing A] : Type where

  blocks : Finset A
  idem : ∀ e ∈ blocks, IsIdempotentElem e ∧ e ≠ 0
  orth : ∀ e ∈ blocks, ∀ e' ∈ blocks, e ≠ e' → e * e' = 0
  sum_eq : ∑ e ∈ blocks, e = 1

instance (A : Type) [CommRing A] : Preorder (Part A) where
  le P Q := ∀ e' ∈ Q.1, ∃ e ∈ P.1, e' * e = e'
  le_refl P := fun e he => ⟨e, he, (P.idem e he).1.eq⟩
  le_trans P Q R hPQ hQR := fun e'' he'' => by
    obtain ⟨e', he', h1⟩ := hQR e'' he''
    obtain ⟨e, he, h2⟩ := hPQ e' he'
    exact ⟨e, he, by rw [← h1, mul_assoc, h2]⟩

variable {B : Type} [CommRing B]

def S (I : Ideal B) (e : B ⧸ I) : Submonoid B where
  carrier := {s | ∃ t, Ideal.Quotient.mk I s * t * e = e}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨t, ht⟩ ⟨u, hu⟩
    refine ⟨t * u, ?_⟩
    show Ideal.Quotient.mk I (a * b) * (t * u) * e = e
    rw [map_mul]
    calc _ = Ideal.Quotient.mk I a * t * (Ideal.Quotient.mk I b * u * e) := by ring
      _ = e := by rw [hu, ht]

theorem S_mono (I : Ideal B) {e e' : B ⧸ I} (h : e' * e = e') : S I e ≤ S I e' := by
  rintro s ⟨t, ht⟩
  refine ⟨t, ?_⟩
  calc Ideal.Quotient.mk I s * t * e' = Ideal.Quotient.mk I s * t * (e' * e) := by rw [h]
    _ = e' * (Ideal.Quotient.mk I s * t * e) := by ring
    _ = e' := by rw [ht, h]

abbrev PiLocalization₂ (I : Ideal B) (P : Part (B ⧸ I)) : Type := ∀ e : P.1, Localization (S I e.1)

def par {A : Type} [CommRing A] {P Q : Part A} (h : P ≤ Q) (e : Q.1) : P.1 :=
  ⟨Classical.choose (h e.1 e.2), (Classical.choose_spec (h e.1 e.2)).1⟩

theorem par_spec {A : Type} [CommRing A] {P Q : Part A} (h : P ≤ Q) (e : Q.1) : e.1 * (par h e).1 = e.1 :=
  (Classical.choose_spec (h e.1 e.2)).2

def stageMap (I : Ideal B) {P Q : Part (B ⧸ I)} (h : P ≤ Q) : PiLocalization₂ I P →+* PiLocalization₂ I Q :=
  RingHom.pi fun e => (IsLocalization.map (M := S I (par h e).1) (T := S I e.1) (Localization (S I e.1)) (RingHom.id B)
    (S_mono I (par_spec h e)) : Localization (S I (par h e).1) →+* _).comp (Pi.evalRingHom _ (par h e))

def βP (I : Ideal B) (P : Part (B ⧸ I)) : B →+* PiLocalization₂ I P :=
  RingHom.pi fun e => algebraMap B (Localization (S I e.1))

def DiagId : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : Part (B ⧸ I)) (h : P ≤ P),
  stageMap I h = RingHom.id (PiLocalization₂ I P)

def DiagComp : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P Q R : Part (B ⧸ I)) (h1 : P ≤ Q) (h2 : Q ≤ R),
  stageMap I (h1.trans h2) = (stageMap I h2).comp (stageMap I h1)

def DiagNat : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P Q : Part (B ⧸ I)) (h : P ≤ Q),
  (stageMap I h).comp (βP I P) = βP I Q

def PartDirected : Prop := ∀ (A : Type) [CommRing A], IsDirected (Part A) (· ≤ ·) ∧ Nonempty (Part A)

def StageProd : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∀ P : Part (B ⧸ I), ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
    (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (PiLocalization₂ I P ≃+* ∀ k, R k)

def PartA : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : Part (B ⧸ I)),
  Function.Bijective (Ideal.quotientMap (I.map (βP I P)) (βP I P) Ideal.le_comap_map)

def PartB : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : Part (B ⧸ I)) (x : PiLocalization₂ I P),
  x ∈ I.map (βP I P) → IsUnit (1 + x)

def PartC : Prop := ∀ (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B →
  ∀ (P : Part (B ⧸ I)) (p : Polynomial (PiLocalization₂ I P)) (a₀ : PiLocalization₂ I P), p.Monic → p.eval a₀ ∈ I.map (βP I P) →
    IsUnit (Ideal.Quotient.mk (I.map (βP I P)) (p.derivative.eval a₀)) →
    ∃ (Q : Part (B ⧸ I)) (h : P ≤ Q) (a : PiLocalization₂ I Q), (p.map (stageMap I h)).IsRoot a ∧
      a - stageMap I h a₀ ∈ I.map (βP I Q)

def diag (I : Ideal B) (hid : DiagId) (hcomp : DiagComp) : Part (B ⧸ I) ⥤ CommRingCat.{0} where
  obj P := CommRingCat.of (PiLocalization₂ I P)
  map f := CommRingCat.ofHom (stageMap I (leOfHom f))
  map_id P := by
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_id, CommRingCat.hom_ofHom]
    exact hid B I P _
  map_comp f g := by
    apply CommRingCat.hom_ext
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    exact hcomp B I _ _ _ _ _

def diagβ (I : Ideal B) (hid : DiagId) (hcomp : DiagComp) (hnat : DiagNat) :
    (Functor.const _).obj (CommRingCat.of B) ⟶ diag I hid hcomp where
  app P := CommRingCat.ofHom (βP I P)
  naturality P Q f := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun x => ?_
    change βP I Q x = stageMap I (leOfHom f) (βP I P x)
    rw [← RingHom.comp_apply, hnat]

theorem goal_of (hdir : PartDirected) (hid : DiagId) (hcomp : DiagComp) (hnat : DiagNat) (hprod : StageProd)
    (ha : PartA) (hb : PartB) (hc : PartC) : LateralTheory.E.HensCut.PartDiag := by
  intro q B _ _ I hB hq
  have := (hdir (B ⧸ I)).1
  have := (hdir (B ⧸ I)).2
  refine ⟨Part (B ⧸ I), inferInstance, inferInstance, diag I hid hcomp, diagβ I hid hcomp hnat, ?_, ?_, ?_, ?_⟩
  · intro P; exact hprod q B I hB hq P
  · intro P; exact ha B I P
  · intro P x hx
    refine ⟨P, 𝟙 P, ?_⟩
    rw [(diag I hid hcomp).map_id, CommRingCat.hom_id]
    exact hb B I P x hx
  · intro P p a₀ hp h1 h2
    obtain ⟨Q, h, a, h3, h4⟩ := hc B I hB P p a₀ hp h1 h2
    exact ⟨Q, homOfLE h, a, h3, h4⟩

end LateralTheory.E.PartDiagCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChowGraphCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.ChowGraphCut

theorem iterLine_isProper {P S : Scheme.{0}} {q : P ⟶ S} (h : IterLine q) : IsProper q := by
  induction h with
  | iso e he => exact inferInstance
  | comp l k hl _ ih =>
    have := hl.1
    exact inferInstance

def Cover : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact p],
  Nonempty X → ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ j, IsAffineOpen (U j)) ∧ (∀ j, (U j : Set X).Nonempty) ∧
    ∀ x : X, ∃ j, x ∈ U j

def Embed : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType p]
  (V : X.Opens), IsAffineOpen V → ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A)) (W : P.Opens)
    (e : V.toScheme ⟶ W.toScheme), IterLine q ∧ IsClosedImmersion e ∧ e ≫ W.ι ≫ q = V.ι ≫ p

def IterComp : Prop := ∀ {P T S : Scheme.{0}} (l : P ⟶ T) (k : T ⟶ S), IterLine l → IterLine k → IterLine (l ≫ k)

def Prod : Prop := ∀ {S : Scheme.{0}} (n : ℕ) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S), (∀ j, IterLine (qj j)) →
  ∃ (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j), IterLine q ∧ (∀ j, π j ≫ qj j = q) ∧
    ∀ {T : Scheme.{0}} (t : T ⟶ S) (f : ∀ j, T ⟶ Pj j), (∀ j, f j ≫ qj j = t) →
      ∃! g : T ⟶ P, g ≫ q = t ∧ ∀ j, g ≫ π j = f j

def Core : Prop := ∀ {S X₁ : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁], IsIntegral X₁ →
  ∀ (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ j, (U j : Set X₁).Nonempty) → (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    (∀ {T : Scheme.{0}} (t : T ⟶ S) (f : ∀ j, T ⟶ Pj j), (∀ j, f j ≫ qj j = t) →
      ∃! g : T ⟶ P, g ≫ q = t ∧ ∀ j, g ≫ π j = f j) →
    ∃ (X' : Scheme.{0}) (i : X' ⟶ pullback p₁ q) (V : X₁.Opens) (s : V.toScheme ⟶ X'),
      IsClosedImmersion i ∧ IsClosedImmersion (i ≫ pullback.snd p₁ q) ∧ (V : Set X₁).Nonempty ∧
      s ≫ i ≫ pullback.fst p₁ q = V.ι

theorem goal_of (hC : Cover) (hE : Embed) (hP : Prod) (hK : Core) : ChowGraph := by
  intro A _ X₁ p₁ _ hX
  have := hX
  obtain ⟨n, U, hUa, hUn, hUc⟩ := hC A p₁ inferInstance
  choose Pj qj W e hq he hc using fun j => hE A p₁ (U j) (hUa j)
  obtain ⟨P, q, π, hq', hπ, hUP⟩ := hP n Pj qj hq
  have hsep : ∀ j, IsSeparated (qj j) := fun j => by
    have := iterLine_isProper (hq j)
    infer_instance
  obtain ⟨X', i, V, s, h1, h2, h3, h4⟩ := hK p₁ hX n U Pj qj W e P q π hUn hUc hsep he hc hπ hUP
  exact ⟨P, q, X', i, V, s, hq', h1, h2, h3, h4⟩

end LateralTheory.E.ChowGraphCut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafCurveVCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafCurveVCut

def LeafFibreField : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (F : Type) (_ : Field F) (_ : Algebra k F) (K : Type) (_ : Field K) (_ : Algebra F K)
    (n : ℕ) (s : Finset F) (t : K) (η : Sp K ⟶ X), (n : WithBot ℕ∞) < topologicalKrullDim X ∧ s.card ≤ n ∧
    Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F ∧ Transcendental F t ∧
    FiniteDimensional (IntermediateField.adjoin F {t}) K ∧
    η ≫ p = Spec.map (CommRingCat.ofHom ((algebraMap F K).comp (algebraMap k F))) ∧ genericPoint X ∈ Set.range η

def LeafTrdegDim : Prop := ∀ (k F Ω : Type) [Field k] [Field F] [Field Ω] [Algebra k F] [Algebra F Ω] [Algebra k Ω]
  [IsScalarTower k F Ω] [Algebra.IsAlgebraic F Ω] (n : ℕ) (s : Finset F), s.card ≤ n →
    Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F →
    ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R ≤ n

def LeafBaseChangeField : Prop := ∀ (F Ω K : Type) [Field F] [Field Ω] [Field K] [Algebra F Ω] [Algebra F K] (t : K),
  Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) K →
    ∃ (L : Type) (_ : Field L) (_ : Algebra Ω L) (u : L) (φ : K →+* L), Transcendental Ω u ∧
      FiniteDimensional (IntermediateField.adjoin Ω {u}) L ∧ φ.comp (algebraMap F K) = (algebraMap Ω L).comp (algebraMap F Ω)

def LeafModelCurve : Prop := ∀ (Ω L : Type) [Field Ω] [IsAlgClosed Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    ∃ (C0 : Scheme.{0}) (c0 : C0 ⟶ Sp Ω) (x : C0) (ψ : Spec (C0.presheaf.stalk x) ⟶ Sp L), IsCurve c0 ∧
      IsGenericPoint x (⊤ : Set C0) ∧ ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω L)) = C0.fromSpecStalk x ≫ c0

def LeafExtend : Prop := ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] {X C0 : Scheme.{0}} (p : X ⟶ Sp k)
  [IsProper p] (c0 : C0 ⟶ Sp Ω) (x : C0), IsCurve c0 → IsGenericPoint x (⊤ : Set C0) →
    ∀ ψ : Spec (C0.presheaf.stalk x) ⟶ X,
      ψ ≫ p = C0.fromSpecStalk x ≫ c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
      ∃ e : C0 ⟶ X, C0.fromSpecStalk x ≫ e = ψ ∧ e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω))

theorem goal_of (hA : LeafFibreField) (hT : LeafTrdegDim) (hB1 : LeafBaseChangeField) (hB2 : LeafModelCurve)
    (hC : LeafExtend) : LateralTheory.E.LeafGeoVCut.LeafCurveV := by
  intro k _ _ X _ p _ hd
  obtain ⟨F, _, _, K, _, _, n, s, t, η, hn, hs, halg, ht, hfin, hη, hgen⟩ := hA k p hd
  obtain ⟨L, _, _, u, φ, hu, hufin, hφ⟩ := hB1 F (AlgebraicClosure F) K t ht hfin
  obtain ⟨C0, c0, x, ψ, hc0, hx, hψ⟩ := hB2 (AlgebraicClosure F) L u hu hufin
  have hring : CommRingCat.ofHom ((algebraMap F K).comp (algebraMap k F)) ≫ CommRingCat.ofHom φ =
      CommRingCat.ofHom (algebraMap k (AlgebraicClosure F)) ≫ CommRingCat.ofHom (algebraMap (AlgebraicClosure F) L) := by
    ext a
    have := congrArg (fun f => f (algebraMap k F a)) hφ
    simp only [RingHom.coe_comp, Function.comp_apply] at this
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, this,
      IsScalarTower.algebraMap_apply k F (AlgebraicClosure F)]
  have hcompat : (ψ ≫ Spec.map (CommRingCat.ofHom φ) ≫ η) ≫ p =
      C0.fromSpecStalk x ≫ c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure F))) := by
    rw [Category.assoc, Category.assoc, hη, ← Spec.map_comp, hring, Spec.map_comp, ← Category.assoc, hψ,
      Category.assoc]
  obtain ⟨e, he1, he2⟩ := hC k (AlgebraicClosure F) p c0 x hc0 hx _ hcompat
  refine ⟨AlgebraicClosure F, inferInstance, inferInstance, inferInstance, C0, c0, e, hc0, he2, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hgen
    let w : Spec (C0.presheaf.stalk x) := IsLocalRing.closedPoint (C0.presheaf.stalk x)
    refine ⟨C0.fromSpecStalk x w, ?_⟩
    rw [← Scheme.Hom.comp_apply, he1, ← hz]
    simp only [Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim _ _
  · intro R hR
    exact lt_of_le_of_lt (hT k F (AlgebraicClosure F) n s hs halg R hR) hn

end LateralTheory.E.LeafCurveVCut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafRepCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.EtaleTopologySheaves
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut

abbrev EtTop (B : Scheme.{0}) : GrothendieckTopology B.Etale := Scheme.smallEtaleTopology B

abbrev SShv (B : Scheme.{0}) (q : ℕ) : Type 2 := Sheaf (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))

instance (B : Scheme.{0}) (q : ℕ) : HasSheafify (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q))) := by
  have : EssentiallySmall.{1} B.Etale := inferInstance
  infer_instance

noncomputable instance (B : Scheme.{0}) (q : ℕ) : HasDerivedCategory.{2} (SShv B q) := HasDerivedCategory.standard _

def OU (B : Scheme.{0}) (q : ℕ) : B.Etale ⥤ DerivedCategory (SShv B q) :=
  yoneda ⋙ (Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (ULift.{1} (ZMod q)))).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} (ZMod q))) ⋙ presheafToSheaf (EtTop B) _ ⋙
    DerivedCategory.singleFunctor (SShv B q) 0

def top (B : Scheme.{0}) : B.Etale := MorphismProperty.Over.mk ⊤ (𝟙 B) (inferInstanceAs (Etale (𝟙 B)))

abbrev YU {Y B : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) : Scheme.{0} := pullback p U.hom

abbrev prU {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) : pullback (pullback.snd p U.hom ≫ U.hom) ι ⟶ YU p U :=
  pullback.fst _ _

abbrev resY {Y B : Scheme.{0}} (p : Y ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) : YU p U' ⟶ YU p U :=
  pullback.map p U'.hom p U.hom (𝟙 Y) a.left (𝟙 B) (by simp) (by simpa using a.w.symm)

abbrev resYW {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) :
    pullback (pullback.snd p U'.hom ≫ U'.hom) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (resY p a) (𝟙 W) (𝟙 B)
    (by
      have h : U'.hom = a.left ≫ U.hom := by simpa using a.w.symm
      simp only [resY, pullback.lift_snd_assoc]
      exact congrArg (fun t => pullback.snd p U'.hom ≫ t) h) (by simp)

abbrev prB {B W : Scheme.{0}} (ι : W ⟶ B) (U : B.Etale) : pullback U.hom ι ⟶ U.left := pullback.fst _ _

abbrev toBY {Y B : Scheme.{0}} (p : Y ⟶ B) (U : B.Etale) : YU p U ⟶ U.left := pullback.snd _ _

abbrev toBW {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) : pullback (pullback.snd p U.hom ≫ U.hom) ι ⟶ pullback U.hom ι :=
  pullback.map _ _ _ _ (toBY p U) (𝟙 W) (𝟙 B) (by simp) (by simp)

abbrev mY {Y Y' B : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (U : B.Etale) : YU (g ≫ p) U ⟶ YU p U :=
  pullback.map (g ≫ p) U.hom p U.hom g (𝟙 _) (𝟙 B) (by simp) (by simp)

abbrev mW {Y Y' B W : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) (U : B.Etale) :
    pullback (pullback.snd (g ≫ p) U.hom ≫ U.hom) ι ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.map _ _ _ _ (mY p g U) (𝟙 W) (𝟙 B) (by simp only [mY, pullback.lift_snd_assoc]; simp only [Functor.id_obj, Category.comp_id]; exact Category.comp_id _) (by simp)

variable (q : ℕ) (i : ℤ)

abbrev LocE {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (K : DerivedCategory (SShv B q)) : Type 2 :=
  ∀ (U : B.Etale) (n : ℤ), Hrel (ZMod q) (sch.map (prU p ι U)) (tw q i) n → ((OU B q).obj U ⟶ (shiftFunctor _ n).obj K)

def Rep {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (K : DerivedCategory (SShv B q)) (e : LocE q i p ι K) : Prop :=
  (∀ U n, Function.Bijective (e U n)) ∧ ∀ (U U' : B.Etale) (a : U' ⟶ U) n y,
    e U' n (rpl q i (prU p ι U) (prU p ι U') (resYW p ι a) (resY p a) (pullback.lift_fst _ _ _).symm n y) =
      (OU B q).map a ≫ e U n y

abbrev LocEB {B W : Scheme.{0}} (ι : W ⟶ B) (K : DerivedCategory (SShv B q)) : Type 2 :=
  ∀ (U : B.Etale) (n : ℤ), Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) n → ((OU B q).obj U ⟶ (shiftFunctor _ n).obj K)

def MorRep {B W Y Y' : Scheme.{0}} (p : Y ⟶ B) (g : Y' ⟶ Y) (ι : W ⟶ B) {K K' : DerivedCategory (SShv B q)}
    (e : LocE q i p ι K) (e' : LocE q i (g ≫ p) ι K') (f : K ⟶ K') : Prop :=
  ∀ U n y, e' U n (rpl q i (prU p ι U) (prU (g ≫ p) ι U) (mW p g ι U) (mY p g U) (pullback.lift_fst _ _ _).symm n y) =
    e U n y ≫ (shiftFunctor _ n).map f

def MorRepB {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) {L K : DerivedCategory (SShv B q)}
    (eL : LocEB q i ι L) (e : LocE q i p ι K) (ℓ : L ⟶ K) : Prop :=
  ∀ U n c, e U n (rpl q i (prB ι U) (prU p ι U) (toBW p ι U) (toBY p U) (pullback.lift_fst _ _ _).symm n c) =
    eL U n c ≫ (shiftFunctor _ n).map ℓ

abbrev resBW {B W : Scheme.{0}} (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) : pullback U'.hom ι ⟶ pullback U.hom ι :=
  pullback.map _ _ _ _ a.left (𝟙 W) (𝟙 B) (by simpa using a.w.symm) (by simp)

def RepB {B W : Scheme.{0}} (ι : W ⟶ B) (L : DerivedCategory (SShv B q)) (e : LocEB q i ι L) : Prop :=
  (∀ U n, Function.Bijective (e U n)) ∧ ∀ (U U' : B.Etale) (a : U' ⟶ U) n c,
    e U' n (rpl q i (prB ι U) (prB ι U') (resBW ι a) a.left (pullback.lift_fst _ _ _).symm n c) =
      (OU B q).map a ≫ e U n c


open CategoryTheory.Limits in
def LeafCons : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {B W Y0 Y1 Y2 : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι]
  (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1),
  ∃ (K0 K1 K2 L : DerivedCategory (SShv B q)) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (l0 : LocE q i p ι K0) (l1 : LocE q i (g1 ≫ p) ι K1) (l2 : LocE q i (g2 ≫ g1 ≫ p) ι K2) (lL : LocEB q i ι L)
    (e0 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj K0))
    (e2 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι)) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj K2))
    (eL : ∀ n : ℤ, Hrel (ZMod q) (sch.map ι) (tw q i) n → ((OU B q).obj (top B) ⟶ (shiftFunctor _ n).obj L)),
    Rep q i p ι K0 l0 ∧ Rep q i (g1 ≫ p) ι K1 l1 ∧ Rep q i (g2 ≫ g1 ≫ p) ι K2 l2 ∧ RepB q i ι L lL ∧
    MorRep q i p g1 ι l0 l1 f ∧ MorRep q i (g1 ≫ p) g2 ι l1 l2 g ∧ MorRepB q i (g2 ≫ g1 ≫ p) ι lL l2 ℓ ∧
    (∀ n, Function.Injective (e2 n)) ∧ (∀ n, Function.Surjective (eL n)) ∧
    (∀ n y, e2 n (rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y) = e0 n y ≫ (shiftFunctor _ n).map (f ≫ g)) ∧
    (∀ n c, e2 n (rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p)
          pullback.condition n c) = eL n c ≫ (shiftFunctor _ n).map ℓ)

def LeafDeg : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∀ (K0 K1 K2 L : DerivedCategory (SShv B q)) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (l0 : LocE q i p ι K0) (l1 : LocE q i (g1 ≫ p) ι K1) (l2 : LocE q i (g2 ≫ g1 ≫ p) ι K2) (lL : LocEB q i ι L),
    Rep q i p ι K0 l0 → Rep q i (g1 ≫ p) ι K1 l1 → Rep q i (g2 ≫ g1 ≫ p) ι K2 l2 → RepB q i ι L lL →
    MorRep q i p g1 ι l0 l1 f → MorRep q i (g1 ≫ p) g2 ι l1 l2 g → MorRepB q i (g2 ≫ g1 ≫ p) ι lL l2 ℓ →
    (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K0)) ∧
    (DerivedCategory.homologyFunctor (SShv B q) 2).map f = 0 ∧ (DerivedCategory.homologyFunctor (SShv B q) 1).map g = 0 ∧
    (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj K2)) ∧
    (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (SShv B q) m).obj L)) ∧
    IsIso ((DerivedCategory.homologyFunctor (SShv B q) 0).map ℓ)

theorem goal_of (hC : LeafCons) (hD : LeafDeg) : LateralTheory.E.LeafGhostRelCut.LeafRep := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA
  obtain ⟨K0, K1, K2, L, f, g, ℓ, l0, l1, l2, lL, e0, e2, eL, r0, r1, r2, rL, mf, mg, mℓ, hinj, hsurj, c0, cL⟩ :=
    hC q i ι p g1 g2
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ :=
    hD hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hA K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  exact ⟨SShv B q, inferInstance, inferInstance, inferInstance, (OU B q).obj (top B), K0, K1, K2, L, f, g, ℓ, e0, e2, eL,
    d1, d2, d3, d4, d5, d6, hinj, hsurj, c0, cL⟩

end LateralTheory.E.EtaleTopologySheaves
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CompCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut

namespace LateralTheory.E.CompCut

def LocAC : Prop := ∀ (W : Type) [CommRing W], ProdACF W → ∀ q : PrimeSpectrum W,
  IsField (Localization.AtPrime q.asIdeal) ∧ AIC (Localization.AtPrime q.asIdeal)

def NormAC : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (K : Type) [CommRing K], IsField K → AIC K → ∀ v : Spec (CommRingCat.of K) ⟶ P,
  AICSch v.normalization

def Sys : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D)
      (ι : ∀ j, D.obj j ⟶ w.normalization), ClopenSys y D c ι ∧
      Nonempty (c.pt ≅ (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization)

theorem goal_of (hS : Sys) (hL : LocAC) (hN : NormAC) : Comp := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, c, ι, hc, ⟨e⟩⟩ := hS W w hW y
  obtain ⟨hF, hA⟩ := hL W hW q
  refine ⟨J, inferInstance, inferInstance, D, c.extend e.inv, ι, ⟨⟨IsLimit.ofIsoLimit hc.1.some (Cone.extendIso c e)⟩,
    hc.2.1, hc.2.2⟩, ?_⟩
  exact hN _ hF hA _

end LateralTheory.E.CompCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StandardChartsLineZero
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StandardEtaleChartsIdempotentGluing

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def mS (S : Subalgebra A K) : Submodule A K := IsLocalRing.maximalIdeal A • Subalgebra.toSubmodule S

def AdjoinInv (B : Subalgebra A K) (t : K) : Subalgebra A K := Algebra.adjoin A ((B : Set K) ∪ {t⁻¹})

structure Charts (B C : Subalgebra A K) (t : K) : Prop where
  ne : t ≠ 0
  tB : t ∈ B
  tC : t⁻¹ ∈ C
  intB : ∀ b ∈ B, IsIntegral (Algebra.adjoin A {t}) b
  intC : ∀ c ∈ C, IsIntegral (Algebra.adjoin A {t⁻¹}) c
  glue : AdjoinInv B t = Algebra.adjoin A ((C : Set K) ∪ {t})

def IdemPair (B C : Subalgebra A K) (t e f : K) : Prop :=
  e ∈ B ∧ f ∈ C ∧ e * e - e ∈ mS B ∧ f * f - f ∈ mS C ∧ e - f ∈ mS (AdjoinInv B t)

def StdCharts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧
    ∀ W : Set ↑(pullback p (cpt A)), IsClopen W → ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ)

def IdemLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f →
  ∃ g ∈ B, g ∈ C ∧ g - e ∈ mS B ∧ g - f ∈ mS C

def AlgGlue : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → (∀ x ∈ B, x ∈ C → IsIntegral A x) → ∀ e f : K, IdemPair B C t e f →
  (e ∈ mS B ∧ f ∈ mS C) ∨ (e - 1 ∈ mS B ∧ f - 1 ∈ mS C)

theorem goal_of (hS : StdCharts) (hG : AlgGlue) : LateralTheory.E.t_E2Cut.LineZero := by
  intro A _ _ hSH Z p hIL hZ
  obtain ⟨hH, -⟩ := hSH
  have hne : Nonempty ↑(pullback p (cpt A)) := by
    obtain ⟨L, u, l, hu, hl, rfl⟩ := hIL
    have := hl.1
    have := hZ.1
    exact LateralTheory.E.LineZeroCut.lzNonempty A (u ≫ l) inferInstance inferInstance
  obtain ⟨K, _, _, B, C, t, hc, hint, hW⟩ := hS A p hIL hZ
  have hpre : PreconnectedSpace ↑(pullback p (cpt A)) := by
    rw [preconnectedSpace_iff_clopen]
    intro W hW'
    obtain ⟨e, f, hef, h0, h1⟩ := hW W hW'
    rcases hG A K B C t hc hint e f hef with h | h
    · exact Or.inl (h0 h)
    · exact Or.inr (h1 h)
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

end LateralTheory.E.StandardEtaleChartsIdempotentGluing
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.TruncKerPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.TruncationKernel

def RelDesc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e → SpS e → P E (d ≫ e) → ∀ hpo' : IsPushout φ' e u φ'',
  Function.Injective (rpl q i (Spec.map φ') (Spec.map φ'') (Spec.map u) (Spec.map e)
    (by rw [← Spec.map_comp, ← Spec.map_comp, hpo'.w]) n)

theorem fgt_injective_of_pull_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ),
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R f F m)) → Function.Injective (fgt R f F n) := by
  intro R _ F U E f n hs
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨c, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) c (zero_add n)) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m, hm, γ, hγ⟩ := hy
  change δ m n γ = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp c.1 (zero_add n) at hγ
  have hdec : c.1 = mappingCone.descCochain _ ((mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by lia))
      (δ m n γ) hm := by
    rw [mappingCone.ext_cochain_from_iff _ m n hm, hγ]
    simp
  have hc : δ n (n + 1) c.1 = 0 := Cocycle.δ_eq_zero c (n + 1)
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ rfl] at hc
  have hc' := congrArg (fun z => (mappingCone.inl ((chains R).map f)).comp z (show -1 + (n + 1) = n by lia)) hc
  simp at hc'
  set a := (mappingCone.inl ((chains R).map f)).comp c.1 (show -1 + n = m by lia) with ha
  have hz : δ m n (a - n.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)) = 0 := by
    rw [δ_sub, δ_units_smul, δ_ofHom_comp]
    rw [Int.negOnePow_succ, Units.neg_smul, ← sub_eq_add_neg] at hc'
    exact hc'
  obtain ⟨w, hw⟩ := hs m hm (CohomologyClass.mk (Cocycle.mk _ n hm hz))
  obtain ⟨w', rfl⟩ := w.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) w' (zero_add m)) = _ at hw
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff] at hw
  obtain ⟨k, hk, α0, hα0⟩ := hw
  change δ k m α0 = (Cochain.ofHom ((chains R).map f)).comp w'.1 (zero_add m) -
    (a - n.negOnePow • (Cochain.ofHom ((chains R).map f)).comp γ (zero_add m)) at hα0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, hm, mappingCone.descCochain _ (-α0) (γ + n.negOnePow • w'.1) hk, ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ _ hm, δ_add, δ_units_smul, Cocycle.δ_eq_zero, smul_zero, add_zero]
  conv_rhs => rw [hdec]
  rw [mappingCone.ext_cochain_from_iff _ m n hm]
  refine ⟨?_, ?_⟩
  · simp only [mappingCone.inl_descCochain, Cochain.comp_add, mappingCone.inl_fst_assoc]
    simp only [δ_neg, hα0, Cochain.comp_units_smul, smul_add, smul_smul, Int.units_mul_self, one_smul, mappingCone.inl_snd_assoc, zero_comp, Cochain.zero_comp, add_zero]
    abel
  · simp

end LateralTheory.E.TruncationKernel
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.StandardEtaleChartsMultivariableHensel


attribute [local instance] MvPolynomial.gradedAlgebra in
def stdOpen (i : Fin 2) : P1.Opens := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

def StdPair {A : Type} [CommRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z) : Prop :=
  ∃ (L : Scheme.{0}) (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P1), IsIntegralHom u ∧ IsProper l ∧
    IsPullback f l (terminal.from P1) (terminal.from _) ∧ u ≫ l = p ∧
    Set.range ι₁ = ((u ≫ f) ⁻¹ᵁ stdOpen 0 : Set Z) ∧ Set.range ι₂ = ((u ≫ f) ⁻¹ᵁ stdOpen 1 : Set Z)

def StdCharts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p →
  ∃ (U V : Scheme.{0}) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ ∧ IsOpenImmersion ι₂ ∧ IsAffine U ∧ IsAffine V ∧
    Set.range ι₁ ∪ Set.range ι₂ = Set.univ ∧ StdPair p ι₁ ι₂

def Heart : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
  IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  StdPair p ι₁ ι₂ →
  ∀ g : LocallyConstant ↥(pullback (fibMap p ι₁) (fibMap p ι₂)) (ZMod q),
    ∃ (a : LocallyConstant ↥(fib (ι₁ ≫ p)) (ZMod q)) (b : LocallyConstant ↥(fib (ι₂ ≫ p)) (ZMod q)),
      g = a.comap (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base.hom -
        b.comap (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base.hom

theorem chartSurj (hR : LateralTheory.E.ChartSurjCut.Root) (hL : LateralTheory.E.ChartSurjCut.LCIso) (hT : Heart) :
    ∀ (H : Hyp) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
    ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
    IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
    StdPair p ι₁ ι₂ →
    ∀ w : Ht q (sch.obj (pullback (fibMap p ι₁) (fibMap p ι₂))) 0 i, ∃ a b,
      w = pull _ (sch.map (pullback.fst (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 a -
        pull _ (sch.map (pullback.snd (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 b := by
  unfold LateralTheory.E.ChartSurjCut.Root at hR
  unfold LateralTheory.E.ChartSurjCut.LCIso at hL
  intro H q i A _ _ hSH hq Z U V p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd w
  obtain ⟨ζ⟩ := hR q A p hZ hq
  obtain ⟨e, he⟩ := hL H q i Z ζ
  have k1 : fibMap p ι₁ ≫ pullback.fst p (cpt A) = pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have k2 : fibMap p ι₂ ≫ pullback.fst p (cpt A) = pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have eq : pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ =
      pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by
    rw [← k2, ← k1, ← Category.assoc, ← pullback.condition, Category.assoc]
  obtain ⟨a, b, hab⟩ := hT q A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd
    ((e _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁)).symm w)
  refine ⟨e _ (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁) a, e _ (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂) b, ?_⟩
  rw [he _ _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂)) rfl, he _ _ (pullback.snd (fibMap p ι₁) (fibMap p ι₂)) eq,
    ← map_sub, ← hab, AddEquiv.apply_symm_apply]

theorem goal_of (hMV : MV) (hC : StdCharts) (hF : LateralTheory.E.LineOneCut.FibCover) (hA : ChartAcyc)
    (hR : LateralTheory.E.ChartSurjCut.Root) (hL : LateralTheory.E.ChartSurjCut.LCIso) (hT : Heart) : LineOne := by
  intro H q i A _ _ hSH hq Z p hp hZ
  obtain ⟨U, V, ι₁, ι₂, h1, h2, hU, hV, hcov, hstd⟩ := hC A p hp
  obtain ⟨hf1, hf2, hfcov⟩ := hF A p ι₁ ι₂ h1 h2 hcov
  obtain ⟨δ, hex, -⟩ := hMV H (ZMod q) (tw q i)
  have e := hex (fibMap p ι₁) (fibMap p ι₂) hfcov 0
  have aU := hA H q A p ι₁ h1 hU hZ hq
  have aV := hA H q A p ι₂ h2 hV hZ hq
  have key : ∀ x : Ht q (sch.obj (fib p)) 1 i, x = 0 := by
    intro x
    have s1 := aU 1 i one_pos
    have s2 := aV 1 i one_pos
    obtain ⟨w, hw⟩ := (e.2.2 x).1 ⟨@Subsingleton.elim _ s1 _ _, @Subsingleton.elim _ s2 _ _⟩
    obtain ⟨a, b, hab⟩ := chartSurj hR hL hT H q i A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd w
    rw [← hw]
    exact (e.2.1 w).2 ⟨a, b, hab⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end LateralTheory.E.StandardEtaleChartsMultivariableHensel
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafUnitPairGPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitPairGPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf LateralTheory.E.LeafUnitPairPf

def IsAct (q : ℕ) (i : ℤ) (L : ∀ (U : Scheme.{0}) (t : ℤ), Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)]
    Sec ((res _ (tw q i)).X t) U →ₗ[ULift.{1} (ZMod q)] Sec ((res _ (tw q i)).X t) U) : Prop :=
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Sec.res g (L U t a b) = L V t (Sec.res g a) (Sec.res g b)) ∧
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Sec.map ((res _ (tw q i)).d t (t + 1)) (L U t a b) = L U (t + 1) a (Sec.map ((res _ (tw q i)).d t (t + 1)) b)

def LeafUnitAct : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ L, IsAct q i L ∧
  ∀ (U : Scheme.{0}) (t : ℤ) (ζ : Prim q Γ(U, ⊤)) (b : Sec ((res _ (tw q i)).X t) U), L U t (twGen 0 ζ) b = b

def LeafPairExt : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) L, IsAct q i L →
  ∃ ν : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q i)),
    ∀ (U : Scheme.{0}) (t : ℤ) (a : Sec (tw q 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      ν.mul U 0 t t (zero_add t) (Sec.map (resι _ (tw q 0)) a) b = L U t a b

theorem LeafUnitPairG_of (hact : LeafUnitAct) (hext : LeafPairExt) : LeafUnitPairG := by
  intro q _ i
  obtain ⟨L, hL, hLζ⟩ := hact q i
  obtain ⟨ν, hν⟩ := hext q i L hL
  refine ⟨ν, fun U t ζ b => ?_⟩
  exact (hν U t (twGen 0 ζ) b).trans (hLζ U t ζ b)

end LateralTheory.E.LeafUnitPairGPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.TruncationPieces
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescIntPf

namespace LateralTheory.E.TruncationPieces

def RelK (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {K L : Cx R} (f : K ⟶ L) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (HK.pull R f F m)) ∧ Function.Injective (HK.pull R f F n)

def piece (R : Type) [CommRing R] {U E : Spc} (u : U ⟶ E) (p : ℕ) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (((chains R).obj U).X (-(p : ℤ))) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).obj (((chains R).obj E).X (-(p : ℤ))) :=
  (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (((chains R).map u).f (-(p : ℤ)))

def Piece : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (p : ℕ) (k : ℤ),
  RelZS R F k (disc.map (u.app (Opposite.op (SimplexCategory.mk p)))) → RelK R F (k + p) (piece R u p)

def Filt : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (n : ℤ),
  (∀ p : ℕ, RelK R F n (piece R u p)) → RelZS R F n u

theorem etale_relK_single_degree_pieces_of_piece_and_filtration (hP : Piece) (hF : Filt) : LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels := by
  intro R _ F U E u n hlow h0
  refine hF R F u n (fun p => ?_)
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have := hP R F u 0 n h0
    simpa using this
  · have hk : n - (p : ℤ) < n := by omega
    have := hP R F u p (n - p) (hlow p (n - p) hk)
    simpa using this

end LateralTheory.E.TruncationPieces
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LCSurjPf
section -- merged from Development.EtaleCohomology.EtaleSheaves.LSecGluePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_sec_gluePf

theorem typeSheaf {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property

end LateralTheory.E.L_sec_gluePf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LCSurjPf

def LocForm : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (B : Type) [CommRing B] (ζ : Prim q B) (y : Sec (tw q i) (Spec (CommRingCat.of B))),
  Loc (Spec (CommRingCat.of B)) fun _ g => ∃ c : ZMod q, Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom)

def Descent : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) m, IsLCMap q i m →
  ∀ (B : Type) [CommRing B] (ζ : Prim q B) (y : Sec (tw q i) (Spec (CommRingCat.of B))),
    (Loc (Spec (CommRingCat.of B)) fun _ g => ∃ c : ZMod q, Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom)) →
    ∃ ψ : LocallyConstant (PrimeSpectrum B) (ZMod q),
      Loc (Spec (CommRingCat.of B)) fun _ g => Sec.res g y = Sec.res g (m B ζ ψ)

theorem sec_sep {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U)
    (h : Loc U fun _ g => Sec.res g a = Sec.res g b) : a = b := by
  obtain ⟨S, hS, hab⟩ := h
  exact (LateralTheory.E.L_sec_gluePf.typeSheaf F S hS).isSeparatedFor.ext fun V g hg => hab V g hg

theorem LCSurj_of (hL : LocForm) (hD : Descent) : LateralTheory.E.LCBijPf.LCSurj := by
  intro q _ i m hm B _ ζ y
  obtain ⟨ψ, hψ⟩ := hD q i m hm B ζ y (hL q i B ζ y)
  exact ⟨ψ, (sec_sep _ _ _ _ hψ).symm⟩

end LateralTheory.E.LCSurjPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LCIsoPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ChartSurjCut

namespace LateralTheory.E.LCIsoPf

def TwTriv : Prop := ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (_s : X ⟶ S), Sec (tw q 0) X ≃+ Sec (tw q i) X,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ x : Sec (tw q 0) X,
      Sec.res f (e X s x) = e Y t (Sec.res f x)

def Tw0 : Prop := ∀ (q : ℕ),
  ∃ c : ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → (LocallyConstant T (ZMod q) ≃+ Sec (tw q 0) T),
    ∀ {V U : Scheme.{0}} (g : V ⟶ U) (hV : IsUnit (q : Γ(V, ⊤))) (hU : IsUnit (q : Γ(U, ⊤))) (a : LocallyConstant U (ZMod q)),
      Sec.res g (c U hU a) = c V hV (a.comap g.base.hom)

def SecIso : Prop := ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (_s : X ⟶ S), LocallyConstant X (ZMod q) ≃+ Sec (tw q i) X,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ g : LocallyConstant X (ZMod q),
      Sec.res f (e X s g) = e Y t (g.comap f.base.hom)

theorem unit_of {q : ℕ} {S X : Scheme.{0}} (ζ : Prim q Γ(S, ⊤)) (s : X ⟶ S) : IsUnit (q : Γ(X, ⊤)) :=
  (ζ.map s.appTop.hom).2.1

theorem SecIso_of (hT : TwTriv) (h0 : Tw0) : SecIso := by
  intro q i S ζ
  obtain ⟨eT, heT⟩ := hT q i S ζ
  obtain ⟨c, hc⟩ := h0 q
  refine ⟨fun X s => (c X (unit_of ζ s)).trans (eT X s), ?_⟩
  intro X Y s t f hf g
  simp only [AddEquiv.trans_apply]
  rw [heT s t f hf, hc f (unit_of ζ t) (unit_of ζ s)]

theorem SecIso_LCIso (hS : SecIso) : LCIso := by
  intro H q i S ζ
  obtain ⟨eS, heS⟩ := hS q i S ζ
  obtain ⟨-, eA, heA, -⟩ := H.a9 (ZMod q) (tw q i)
  refine ⟨fun X s => (eS X s).trans (eA X), ?_⟩
  intro X Y s t f hf g
  simp only [AddEquiv.trans_apply]
  rw [heA, heS s t f hf g]

end LateralTheory.E.LCIsoPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSpreadVCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafSpreadVCut

def LeafDescendV : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (Ω : Type) [Field Ω]
    [Algebra k Ω] {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 →
    e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) →
    ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) → IsCurve (γ2 ≫ γ1 ≫ c0) →
    ∃ (R : Subalgebra k Ω), R.FG ∧ ∃ (D0 D1 D2 : Scheme.{0}) (q : D0 ⟶ Sp R) (d1 : D1 ⟶ D0) (d2 : D2 ⟶ D1)
      (f : D0 ⟶ X) (v0 : C0 ⟶ D0) (v1 : C1 ⟶ D1) (v2 : C2 ⟶ D2),
      IsProper q ∧ SmoothOfRelativeDimension 1 q ∧ IsProper (d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d1 ≫ q) ∧
      IsProper (d2 ≫ d1 ≫ q) ∧ SmoothOfRelativeDimension 1 (d2 ≫ d1 ≫ q) ∧
      f ≫ p = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) ∧
      IrreducibleSpace D0 ∧ topologicalKrullDim D0 ≤ ringKrullDim R + 1 ∧
      IsPullback v0 c0 q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v1 (γ1 ≫ c0) (d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      IsPullback v2 (γ2 ≫ γ1 ≫ c0) (d2 ≫ d1 ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ∧
      γ1 ≫ v0 = v1 ≫ d1 ∧ γ2 ≫ v1 = v2 ≫ d2 ∧ v0 ≫ f = e

def LeafCloseB : Prop := ∀ (k : Type) [Field k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A], ∃ (B : Scheme.{0}) (b : B ⟶ Sp k) (ι : Sp A ⟶ B), IsIntegral B ∧ IsProper b ∧
    IsOpenImmersion ι ∧ ι ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k A)) ∧ topologicalKrullDim B ≤ ringKrullDim A

lemma succ_le_of_lt {a x : WithBot ℕ∞} (h : a < x) : a + 1 ≤ x ∧ a + 1 < ⊤ := by
  induction a with
  | bot => exact ⟨by simp, by simp⟩
  | coe n =>
    induction x with
    | bot => exact absurd h (not_lt_bot)
    | coe m =>
      have h' : n < m := WithBot.coe_lt_coe.mp h
      have hn : n ≠ ⊤ := ne_top_of_lt h'
      refine ⟨?_, ?_⟩
      · rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
        exact Order.add_one_le_of_lt h'
      · rw [← WithBot.coe_one, ← WithBot.coe_add]
        exact WithBot.coe_lt_coe.mpr (lt_top_iff_ne_top.mpr (by
          lift n to ℕ using hn
          exact ENat.natCast_ne_top (n + 1)))

end LateralTheory.E.LeafSpreadVCut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LEtaleLiftPf
noncomputable section

namespace LateralTheory.E.LEtaleLiftPf

def LChart : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (A' : Type) [CommRing A']
  [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I),
  ∃ g : A', IsUnit (φ g) ∧ Algebra.IsStandardEtale A (Localization.Away g)

theorem LEtaleLift_of (hC : LChart) : LateralTheory.E.LFactorPf.LEtaleLift := by
  intro A _ I _ A' _ _ _ φ
  obtain ⟨g, hg, hS⟩ := hC A I A' φ
  let φ' : Localization.Away g →ₐ[A] A ⧸ I := IsLocalization.Away.liftAlgHom g hg
  obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_isStandardEtale I (Ideal.Quotient.mkₐ A I)
    (Ideal.Quotient.mkₐ_surjective A I) (fun b => (Ideal.Quotient.eq_zero_iff_mem).symm) φ'
  refine ⟨ψ.comp (IsScalarTower.toAlgHom A A' _), AlgHom.ext fun a => ?_⟩
  exact congr($hψ (algebraMap A' _ a)).trans (show φ' (algebraMap A' _ a) = φ a by simp [φ'])

end LateralTheory.E.LEtaleLiftPf
end
end
