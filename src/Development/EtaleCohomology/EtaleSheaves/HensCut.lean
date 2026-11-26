module

public import Development.EtaleCohomology.EtaleSheaves.SHTensorPf
public import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
public import Development.EtaleCohomology.EtaleSheaves.MayerVietorisSequence

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.HensCut
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.E.HensCut

def LocAIC : Prop := ∀ (B : Type) [CommRing B] [IsDomain B] (M : Submonoid B), (0 : B) ∉ M → AIC B →
  IsDomain (Localization M) ∧ AIC (Localization M)

def MonicSplits : Prop := ∀ (R : Type) [CommRing R] [IsDomain R], AIC R → ∀ p : Polynomial R, p.Monic →
  ∃ s : Multiset R, p = (s.map fun a => Polynomial.X - Polynomial.C a).prod

def IdemPart : Prop := ∀ (A : Type) [CommRing A] (n : ℕ) (y : Fin n → A), ∏ l, y l = 0 →
  IsUnit (∑ l, ∏ m ∈ Finset.univ.erase l, y m) →
  ∃ e : Fin n → A, (∀ l, IsIdempotentElem (e l)) ∧ (∀ l m, l ≠ m → e l * e m = 0) ∧ ∑ l, e l = 1 ∧ ∀ l, e l * y l = 0

def ColimHens : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D) (c : Cocone D), IsColimit c →
  (∀ j, Function.Bijective (Ideal.quotientMap (I.map (β.app j).hom) (β.app j).hom Ideal.le_comap_map)) →
  (∀ j, ∀ x ∈ I.map (β.app j).hom, ∃ (j' : J) (f : j ⟶ j'), IsUnit ((D.map f).hom (1 + x))) →
  (∀ j (p : Polynomial (D.obj j)) (a₀ : D.obj j), p.Monic → p.eval a₀ ∈ I.map (β.app j).hom →
    IsUnit (Ideal.Quotient.mk (I.map (β.app j).hom) (p.derivative.eval a₀)) →
    ∃ (j' : J) (f : j ⟶ j') (a : D.obj j'), (p.map (D.map f).hom).IsRoot a ∧ a - (D.map f).hom a₀ ∈ I.map (β.app j').hom) →
  ∃ K : Ideal c.pt, HenselianRing c.pt K ∧ Nonempty (B ⧸ I ≃+* c.pt ⧸ K)

def PartDiag : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D),
    (∀ j, ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
      (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (D.obj j ≃+* ∀ k, R k)) ∧
    (∀ j, Function.Bijective (Ideal.quotientMap (I.map (β.app j).hom) (β.app j).hom Ideal.le_comap_map)) ∧
    (∀ j, ∀ x ∈ I.map (β.app j).hom, ∃ (j' : J) (f : j ⟶ j'), IsUnit ((D.map f).hom (1 + x))) ∧
    (∀ j (p : Polynomial (D.obj j)) (a₀ : D.obj j), p.Monic → p.eval a₀ ∈ I.map (β.app j).hom →
      IsUnit (Ideal.Quotient.mk (I.map (β.app j).hom) (p.derivative.eval a₀)) →
      ∃ (j' : J) (f : j ⟶ j') (a : D.obj j'), (p.map (D.map f).hom).IsRoot a ∧
        a - (D.map f).hom a₀ ∈ I.map (β.app j').hom)

theorem goal_of (_hL : LocAIC) (_hM : MonicSplits) (_hI : IdemPart) (hC : ColimHens) (hD : PartDiag) :
    LateralTheory.E.QuotAcycCut.Hens := by
  intro q B _ _ I hB hq
  obtain ⟨J, _, _, D, β, hst, ha, hb, hc⟩ := hD q B I hB hq
  obtain ⟨K, hK, he⟩ := hC B I J D β (colimit.cocone D) (colimit.isColimit D) ha hb hc
  refine ⟨J, inferInstance, inferInstance, D, colimit.cocone D, colimit.isColimit D, hst, ?_, K, hK, he⟩
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  have h1 : IsUnit ((q : B)) := hq
  have h2 := h1.map ((β.app j) ≫ (colimit.cocone D).ι.app j).hom
  simpa using h2

end LateralTheory.E.HensCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.BuildCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut

namespace LateralTheory.E.BuildCut

def ProdACF (W : Type) [CommRing W] : Prop :=
  AIC W ∧ ∀ a : W, ∃ e u : W, IsIdempotentElem e ∧ IsUnit u ∧ a = e * u

def Pts : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P],
  ∃ (W : Type) (_ : CommRing W) (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W ∧ Surjective w

def LimInt : Prop := ∀ {Y : Scheme.{0}} (y : Y) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D)
  (ι : ∀ j, D.obj j ⟶ Y), ClopenSys y D c ι → ∀ j, IsIntegralHom (c.π.app j ≫ ι j)

def Comp : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ w.normalization),
      ClopenSys y D c ι ∧ AICSch c.pt

theorem goal_of (hP : Pts) (hL : LimInt) (hC : Comp) : Build := by
  intro P _ _
  obtain ⟨W, _, w, hW, hs⟩ := hP (P := P)
  refine ⟨w.normalization, w.fromNormalization, inferInstance, ?_, fun y => ?_⟩
  · have h := hs
    rw [← w.toNormalization_fromNormalization] at h
    exact ⟨Function.Surjective.of_comp h.surj⟩
  · obtain ⟨J, _, _, D, c, ι, hc, hA⟩ := hC W w hW y
    refine ⟨J, inferInstance, inferInstance, D, c, ι, hc, hA, fun j => ?_⟩
    have := hL y D c ι hc j
    infer_instance

end LateralTheory.E.BuildCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DescIntPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut

namespace LateralTheory.E.DescIntPf

def RelZS (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {U E : Spc} (u : U ⟶ E) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R u F m)) ∧ Function.Injective (pull R u F n)

theorem relZ_iff (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    RelZ q i n f ↔ RelZS (ZMod q) (tw q i) n (sch.map (Spec.map f)) := Iff.rfl

theorem transfer (R : Type) [CommRing R] (F : Shv R) {U E X' X : Spc} (u : U ⟶ E) (f : X' ⟶ X) (a' : U ⟶ X')
    (a : E ⟶ X) (hsq : u ≫ a = a' ≫ f) (ha : Eqv R a F) (ha' : Eqv R a' F) (n : ℤ) (hu : RelZS R F n u) :
    RelZS R F n f := by
  have key : ∀ m (x : H R X F m), pull R a' F m (pull R f F m x) = pull R u F m (pull R a F m x) := by
    intro m x
    rw [← pull_comp, ← pull_comp, hsq]
  refine ⟨fun m hm y => ?_, fun x x' hxx => ?_⟩
  · obtain ⟨z, hz⟩ := hu.1 m hm (pull R a' F m y)
    obtain ⟨x, rfl⟩ := (ha m).2 z
    refine ⟨x, (ha' m).1 ?_⟩
    rw [key, hz]
  · have h1 := congrArg (pull R a' F n) hxx
    rw [key, key] at h1
    exact (ha n).1 (hu.2 h1)

theorem eqv_of_iso (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := fun n => by
  have h1 : ∀ x, pull R e.inv F n (pull R e.hom F n x) = x := fun x => by
    rw [← pull_comp, e.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R e.hom F n (pull R e.inv F n x) = x := fun x => by
    rw [← pull_comp, e.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem RelZS.of_iso (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (u : U ⟶ E) (u' : U' ⟶ E') (e₁ : U ≅ U')
    (e₂ : E ≅ E') (hsq : u ≫ e₂.hom = e₁.hom ≫ u') (n : ℤ) (hu : RelZS R F n u) : RelZS R F n u' :=
  transfer R F u u' e₁.hom e₂.hom hsq (eqv_of_iso R F e₂) (eqv_of_iso R F e₁) n hu

def EtaleRelativeIsoTruncationFromLevels : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (n : ℤ),
  (∀ (p : ℕ) (m : ℤ), m < n → RelZS R F m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) →
  RelZS R F n (disc.map (u.app (Opposite.op (SimplexCategory.mk 0)))) → RelZS R F n u

def CechSq : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → g.hom.IsIntegral → SpS g →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' →
  ∃ (U E : Spc) (u : U ⟶ E) (a' : U ⟶ sch.obj (Spec Y')) (a : E ⟶ sch.obj (Spec C)),
    u ≫ a = a' ≫ sch.map (Spec.map φ') ∧ Eqv _ a (tw q i) ∧ Eqv _ a' (tw q i) ∧
    (∀ p : ℕ, ∃ (L : CommRingCat.{0}) (l : A ⟶ L) (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : L ⟶ Z),
      P L l ∧ IsPushout φ l wz ψ ∧
      ∀ m, RelZ q i m ψ → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) ∧
    ∃ (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : D ⟶ Z), IsPushout φ (c ≫ g) wz ψ ∧
      ∀ m, RelZ q i m ψ → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk 0))))

theorem DescInt_of (hT : EtaleRelativeIsoTruncationFromLevels) (hC : CechSq) : LateralTheory.E.StalkCut.DescInt := by
  intro hH q _ i n A Y φ hq P hpush hbelow C D c g hCc hDc hgi hgs hDn Y' w φ' hpo
  obtain ⟨U, E, u, a', a, hsq, ha, ha', hlev, Z, wz, ψ, hpo0, h0⟩ :=
    hC hH q i φ hq P @hpush c g hCc hDc hgi hgs Y' w φ' hpo
  rw [relZ_iff]
  refine transfer _ _ u _ a' a hsq ha ha' n (hT _ _ u n (fun p m hm => ?_) (h0 n (hDn Z wz ψ hpo0)))
  obtain ⟨L, l, Z', wz', ψ', hL, hpo', hrel⟩ := hlev p
  exact hrel m (hbelow m hm L l hL Z' wz' ψ' hpo')

end LateralTheory.E.DescIntPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChowLCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChowLCut

inductive IterLine {S : Scheme.{0}} : ∀ {Y : Scheme.{0}}, (Y ⟶ S) → Prop
  | iso {Y : Scheme.{0}} (e : Y ⟶ S) : IsIso e → IterLine e
  | comp {Y T : Scheme.{0}} (l : Y ⟶ T) (k : T ⟶ S) : IsLine l → IterLine k → IterLine (l ≫ k)

theorem IT_of_iterLine {S Y : Scheme.{0}} {k : Y ⟶ S} (hk : IterLine k) :
    ∀ {X : Scheme.{0}} (u : X ⟶ Y), IsIntegralHom u → IT (u ≫ k) := by
  induction hk with
  | iso e he => intro X u hu; exact IT.int _ (by infer_instance)
  | comp l k hl _ ih =>
    intro X u hu
    refine IT.step (u ≫ l) k _ ?_ ⟨_, u, l, hu, hl, rfl⟩ (Category.assoc _ _ _)
    simpa using ih (𝟙 _) inferInstance

def LineEx : Prop := ∀ S : Scheme.{0}, ∃ (L : Scheme.{0}) (l : L ⟶ S), IsLine l

def IterBC : Prop := ∀ {P S X : Scheme.{0}} (q : P ⟶ S) (g : X ⟶ S), IterLine q → IterLine (pullback.fst g q)

def ChowGraph : Prop := ∀ (A : Type) [CommRing A] {X₁ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of A)) [IsProper p₁],
  IsIntegral X₁ → ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A)) (X' : Scheme.{0}) (i : X' ⟶ pullback p₁ q)
    (U : X₁.Opens) (s : U.toScheme ⟶ X'), IterLine q ∧ IsClosedImmersion i ∧ IsClosedImmersion (i ≫ pullback.snd p₁ q) ∧
    (U : Set X₁).Nonempty ∧ s ≫ i ≫ pullback.fst p₁ q = U.ι

theorem goal_of (hB : IterBC) (hG : ChowGraph) : LateralTheory.E.ChowCut.ChowL := by
  intro A _ X₁ p₁ _ hX₁
  obtain ⟨P, q, X', i, U, s, hq, hi, his, hU, hs⟩ := hG A p₁ hX₁
  refine ⟨X', i ≫ pullback.fst p₁ q, U, s, hU, hs, IT_of_iterLine (hB q p₁ hq) i inferInstance, ?_⟩
  have e : (i ≫ pullback.fst p₁ q) ≫ p₁ = (i ≫ pullback.snd p₁ q) ≫ q := by
    rw [Category.assoc, pullback.condition, Category.assoc]
  rw [e]
  exact IT_of_iterLine hq _ inferInstance

end LateralTheory.E.ChowLCut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChartSurjCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.ChartSurjCut

def Root : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  AICSch Z → IsUnit (q : A) → Nonempty (Prim q Γ(Z, ⊤))

def LCIso : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (s : X ⟶ S), LocallyConstant X (ZMod q) ≃+ Ht q (sch.obj X) 0 i,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ g : LocallyConstant X (ZMod q),
      pull _ (sch.map f) (tw q i) 0 (e X s g) = e Y t (g.comap f.base.hom)

end LateralTheory.E.ChartSurjCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTwistPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafTwistPf

def LeafLoc : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R)
  (e : ∀ U : Scheme.{0}, (U ⟶ X) → (Sec F U ≃ₗ[ULift.{1} R] Sec G U)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)) →
  ∀ n : ℤ, Nonempty (H R (sch.obj X) F n ≃+ H R (sch.obj X) G n)

def LeafTwSec : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Prim q B → ∀ i j : ℤ,
  ∃ e : ∀ U : Scheme.{0}, (U ⟶ Spec (CommRingCat.of B)) → (Sec (tw q i) U ≃ₗ[ULift.{1} (ZMod q)] Sec (tw q j) U),
    ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ Spec (CommRingCat.of B)) (s : Sec (tw q i) U),
      e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)

theorem LeafTwist_of (hL : LeafLoc) (hT : LeafTwSec) : LateralTheory.E.LeafKumCut.LeafTwist := by
  intro hy q _ B _ hP n i j
  obtain ⟨ζ⟩ := hP
  obtain ⟨e, he⟩ := hT q B ζ i j
  exact hL hy (ZMod q) (Spec (CommRingCat.of B)) (tw q i) (tw q j) e he n

end LateralTheory.E.LeafTwistPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ContStepPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.ContStepPf

def PCS (X0 : Scheme.{0}) : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ j0 : J, Nonempty (D.obj j0 ≅ X0) →
  ∀ n i : ℤ, ∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x

def PCK (X0 : Scheme.{0}) : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ j0 : J, Nonempty (D.obj j0 ≅ X0) →
  ∀ n i : ℤ, ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
    ∃ (k : J) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0

theorem PC_of {X0 : Scheme.{0}} (h1 : PCS X0) (h2 : PCK X0) : PC X0 := by
  intro q J _ _ D c hc ha hcs hqs hu j0 e n i
  exact ⟨h1 q D c hc ha hcs hqs hu j0 e n i, h2 q D c hc ha hcs hqs hu j0 e n i⟩

def StepS : Prop := Hyp → MV → ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) →
  U ⊔ V = ⊤ → PC U.toScheme → PC V.toScheme → PC (U ⊓ V).toScheme → PCS X

def StepK : Prop := Hyp → MV → ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) →
  U ⊔ V = ⊤ → PC U.toScheme → PC V.toScheme → PC (U ⊓ V).toScheme → PCK X

theorem ContStep_of (hS : StepS) (hK : StepK) : ContStep := by
  intro h hmv X U V hU hV hUV pU pV pW
  exact PC_of (hS h hmv X U V hU hV hUV pU pV pW) (hK h hmv X U V hU hV hUV pU pV pW)

end LateralTheory.E.ContStepPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LocalDescent
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut

namespace LateralTheory.E.DescLocPf

def LocPts (q : ℕ) (i : ℤ) {A Y D : CommRingCat.{0}} (φ : A ⟶ Y) (d : A ⟶ D) : Prop :=
  ∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
    BC q i φ (d ≫ o)

def CokLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ')) (tw q i) m)

def KerLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  (∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → LocPts q i φ c →
    ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' →
    ∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map φ')) (tw q i) m)) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d → LocPts q i φ d →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  Function.Injective (pull _ (sch.map (Spec.map φ')) (tw q i) n)

theorem DescLoc_of (hC : CokLoc) (hK : KerLoc) : LateralTheory.E.StalkCut.DescLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hD hpts Y' w φ' hpo
  exact ⟨hC hH q i n φ hq P hpush het hlow D d hD hpts Y' w φ' hpo,
    hK hH q i n φ hq P hpush het hlow (fun C c hC' hpC => hC hH q i n φ hq P hpush het hlow C c hC' hpC) D d hD hpts Y' w φ' hpo⟩

end LateralTheory.E.DescLocPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafGhostRelCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafGhostRelCut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut

def LeafTrunc : Prop := ∀ (A : Type 2) [Category.{1} A] [Abelian A] [HasDerivedCategory.{2} A]
  (K0 K1 K2 L : DerivedCategory A) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2),
  (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor A m).obj K0)) →
  (DerivedCategory.homologyFunctor A 2).map f = 0 → (DerivedCategory.homologyFunctor A 1).map g = 0 →
  (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj K2)) →
  (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj L)) →
  IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ) →
  ∃ h : K0 ⟶ L, h ≫ ℓ = f ≫ g

def LeafRep : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∃ (A : Type 2) (_ : Category.{1} A) (_ : Abelian A) (_ : HasDerivedCategory.{2} A) (O K0 K1 K2 L : DerivedCategory A)
    (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (e0 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj K0))
    (e2 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι)) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj K2))
    (eL : ∀ n : ℤ, Hrel (ZMod q) (sch.map ι) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj L)),
    (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor A m).obj K0)) ∧
    (DerivedCategory.homologyFunctor A 2).map f = 0 ∧ (DerivedCategory.homologyFunctor A 1).map g = 0 ∧
    (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj K2)) ∧
    (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj L)) ∧
    IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ) ∧
    (∀ n, Function.Injective (e2 n)) ∧ (∀ n, Function.Surjective (eL n)) ∧
    (∀ n y, e2 n (rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y) = e0 n y ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map (f ≫ g)) ∧
    (∀ n c, e2 n (rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p)
          pullback.condition n c) = eL n c ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map ℓ)

theorem goal_of (hT : LeafTrunc) (hR : LeafRep) : LeafGhostRel := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA n y
  obtain ⟨A, _, _, _, O, K0, K1, K2, L, f, g, ℓ, e0, e2, eL, hK0, hf, hg, hK2, hL, hℓ, hinj, hsurj, n0, nL⟩ :=
    hR hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hA
  obtain ⟨h, hh⟩ := hT A K0 K1 K2 L f g ℓ hK0 hf hg hK2 hL hℓ
  obtain ⟨c, hc⟩ := hsurj n (e0 n y ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map h)
  refine ⟨c, hinj n ?_⟩
  rw [n0, nL, hc, Category.assoc, ← Functor.map_comp, hh]

end LateralTheory.E.LeafGhostRelCut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafGeomPfLoc
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf

namespace LateralTheory.E.LeafGeomPfLoc

theorem projective_bundle_direct_sum_zero_vertex_coordinates_restrict {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X Y : Scheme.{0}}
    (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) (j : Fin (a + b)) :
    vec0 V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) j = Scheme.Γ.map k.op (vec0 V W x j) := by
  set_option synthInstance.maxHeartbeats 200000 in
  have h := ConcreteCategory.congr_hom (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).naturality k.op) x
  unfold vec0
  erw [h]
  rfl

theorem unit_le {X : Scheme.{0}} (f : Γ(X, ⊤)) {V : X.Opens} (h : V ≤ X.basicOpen f) :
    IsUnit ((X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom f) := by
  have hu := X.toRingedSpace.isUnit_res_basicOpen (U := ⊤) f
  have := hu.map (X.presheaf.map (homOfLE h).op).hom
  erw [← CommRingCat.comp_apply, ← Functor.map_comp] at this
  exact this

theorem unit_basicOpen {X : Scheme.{0}} (f : Scheme.Γ.obj (op X)) :
    IsUnit (Scheme.Γ.map (X.basicOpen f).ι.op f) := by
  rw [Scheme.Γ_map_op, Scheme.Opens.ι_appTop]
  exact unit_le f (X.basicOpen f).ι_image_top.le

theorem leafLocal : LeafLocal := by
  intro E a b V W n X x
  have hspan : Ideal.span (Set.range (vec0 V W x)) = ⊤ :=
    ((show Fin (n + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X)) from
      ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x).obj 0).2
  have hcov : TopologicalSpace.IsOpenCover (fun j => X.basicOpen (vec0 V W x j)) := by
    have := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top (X := X) ⊤ (Set.range (vec0 V W x)) hspan
    refine le_antisymm le_top ?_
    rw [← this]
    exact iSup₂_le fun _ ⟨j, hj⟩ => hj ▸ le_iSup (fun j => X.basicOpen (vec0 V W x j)) j
  let 𝒰 := X.openCoverOfIsOpenCover _ hcov
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.zariskiTopology_le_etaleTopology _ 𝒰.mem_grothendieckTopology, ?_⟩
  intro Y k hk
  rw [Sieve.mem_ofArrows_iff] at hk
  obtain ⟨j, g, rfl⟩ := hk
  have hu : IsUnit (Scheme.Γ.map (g ≫ 𝒰.f j).op (vec0 V W x j)) := by
    rw [op_comp, Functor.map_comp]
    exact (unit_basicOpen (vec0 V W x j)).map (Scheme.Γ.map g.op).hom
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ : (∃ i, j = Fin.castAdd b i) ∨ ∃ i, j = Fin.natAdd a i :=
    Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) j
  · left
    simp only [First, projective_bundle_direct_sum_zero_vertex_coordinates_restrict]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hu
  · right
    simp only [Second, projective_bundle_direct_sum_zero_vertex_coordinates_restrict]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hu

theorem LeafGeom_of (h1 : LeafHalf1) (h2 : LeafHalf2) : LateralTheory.E.D2.LeafGeom :=
  LateralTheory.E.LeafGeomPf.LeafGeom_of h1 h2 leafLocal

end LateralTheory.E.LeafGeomPfLoc
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ZarIndPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.ZarIndPf

def Bij (q : ℕ) (i n : ℤ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) : Prop :=
  Function.Bijective (pull _ (sch.map (fO f p U)) (tw q i) n)

def InjStep : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ, (∀ s : S, Germ q i n f p s) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  ∀ U : S.Opens, IsCompact (U : Set S) → Function.Injective (pull _ (sch.map (fO f p U)) (tw q i) n)

def SurjStep : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ, (∀ s : S, Germ q i n f p s) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Function.Injective (pull _ (sch.map (fO f p U)) (tw q i) n)) →
  ∀ U : S.Opens, IsCompact (U : Set S) → Function.Surjective (pull _ (sch.map (fO f p U)) (tw q i) n)

def Step : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ, (∀ s : S, Germ q i n f p s) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i n f p U

theorem Step_of (h1 : InjStep) (h2 : SurjStep) : Step := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hg hb U hU
  exact ⟨h1 hM hH q f p hq i n hg hb U hU, h2 hM hH q f p hq i n hg hb (h1 hM hH q f p hq i n hg hb) U hU⟩

theorem pull_bij_of_iso {E E' : Spc} (g : E ⟶ E') [IsIso g] {q' : ℕ} (F : Shv (ZMod q')) (n : ℤ) :
    Function.Bijective (pull _ g F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (inv g) F n, fun x => ?_, fun x => ?_⟩
  · simp [← pull_comp, pull_id]
  · simp [← pull_comp, pull_id]

theorem bij_top {q : ℕ} {i n : ℤ} {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [IsIso (⊤ : S.Opens).ι] (h : Bij q i n f p ⊤) :
    Function.Bijective (pull _ (sch.map f) (tw q i) n) := by
  have e : fO f p ⊤ ≫ pullback.fst p (⊤ : S.Opens).ι = pullback.fst (f ≫ p) (⊤ : S.Opens).ι ≫ f := by
    exact pullback.lift_fst _ _ _
  have e2 : ∀ x, pull _ (sch.map (fO f p ⊤)) (tw q i) n (pull _ (sch.map (pullback.fst p (⊤ : S.Opens).ι)) _ n x) =
      pull _ (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) _ n (pull _ (sch.map f) _ n x) := by
    intro x
    rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, e]
  have b1 := pull_bij_of_iso (sch.map (pullback.fst p (⊤ : S.Opens).ι)) (tw q i) n
  have b2 := pull_bij_of_iso (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n
  have hc : Function.Bijective ((pull (ZMod q) (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n) ∘ (pull (ZMod q) (sch.map f) (tw q i) n)) := by
    have : (pull (ZMod q) (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n) ∘ (pull (ZMod q) (sch.map f) (tw q i) n) =
        (pull (ZMod q) (sch.map (fO f p ⊤)) (tw q i) n) ∘ (pull (ZMod q) (sch.map (pullback.fst p (⊤ : S.Opens).ι)) (tw q i) n) :=
      funext fun x => (e2 x).symm
    rw [this]; exact h.comp b1
  refine ⟨hc.1.of_comp, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hc.2 (pull (ZMod q) (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n y)
  exact ⟨x, b2.1 hx⟩

theorem bij_neg (hH : Hyp) {q : ℕ} {i n : ℤ} (hn : n < 0) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    Bij q i n f p U := by
  have h1 := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj (overO p U)) n hn
  have h2 := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj (overO (f ≫ p) U)) n hn
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem ZarInd_of_step (hS : Step) : ZarInd := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i hg
  have P : ∀ n : ℤ, ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i n f p U := by
    intro n
    induction n using Int.induction_on with
    | zero => exact hS hM hH q f p hq i 0 (fun s => hg s 0) (fun U _ => bij_neg hH (by norm_num) f p U)
    | succ m ih =>
      exact hS hM hH q f p hq i (m + 1) (fun s => hg s (m + 1)) (by simpa using ih)
    | pred m ih =>
      exact fun U _ => bij_neg hH (by omega) f p U
  intro n
  have : IsIso (⊤ : S.Opens).ι := (Scheme.topIso S).isIso_hom
  exact bij_top f p (P n ⊤ (by simpa using isCompact_univ))

end LateralTheory.E.ZarIndPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LCBijPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LCBijPf

def TwGenNZAC : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (K : Type) [Field K] [IsAlgClosed K] (ζ : Prim q K) (c : ZMod q),
  c.val • twGen i (gam ζ) = 0 → c = 0

abbrev TwGenNZ : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (B : Type) [CommRing B] [Nontrivial B] (ζ : Prim q B) (c : ZMod q),
  c.val • twGen i (gam ζ) = 0 → c = 0

def LCSurj : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) m, IsLCMap q i m →
  ∀ (B : Type) [CommRing B] (ζ : Prim q B), Function.Surjective (m B ζ)

theorem twGen_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  unfold Sec.res twGen ofRings.sec tw ofRings
  erw [← ModuleCat.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]
  congr 1
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map g.op).hom) (Finsupp.single ζ 1)) = _
  erw [Finsupp.mapDomain_single]
  rfl

theorem gam_map {q : ℕ} {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (ζ : Prim q B) :
    gam (ζ.map f) = (gam ζ).map (Spec.map (CommRingCat.ofHom f)).appTop.hom := by
  apply Subtype.ext
  change (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (f ζ.1) =
    (Spec.map (CommRingCat.ofHom f)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ζ.1)
  have := congrArg (fun φ => φ.hom ζ.1) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

theorem twGenNZ_of (hAC : TwGenNZAC) : TwGenNZ := by
  intro q _ i B _ _ ζ c h
  obtain ⟨M, hM⟩ := Ideal.exists_maximal B
  let _ : Field (B ⧸ M) := Ideal.Quotient.field M
  let f : B →+* AlgebraicClosure (B ⧸ M) := (algebraMap (B ⧸ M) (AlgebraicClosure (B ⧸ M))).comp (Ideal.Quotient.mk M)
  apply hAC q i (AlgebraicClosure (B ⧸ M)) (ζ.map f) c
  have h2 := congrArg (Sec.res (Spec.map (CommRingCat.ofHom f))) h
  have hs : ∀ x : Sec (tw q i) (Spec (CommRingCat.of B)), Sec.res (Spec.map (CommRingCat.ofHom f)) (c.val • x) =
      c.val • Sec.res (Spec.map (CommRingCat.ofHom f)) x := fun x => map_nsmul _ _ x
  have hz : Sec.res (Spec.map (CommRingCat.ofHom f)) (0 : Sec (tw q i) (Spec (CommRingCat.of B))) = 0 := map_zero _
  rw [hs, hz, twGen_res, ← gam_map] at h2
  exact h2

theorem lcInj (hT : TwGenNZ) (q : ℕ) [NeZero q] (i : ℤ) m (hm : IsLCMap q i m) (B : Type) [CommRing B]
    (ζ : Prim q B) : Function.Injective (m B ζ) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro φ hφ
  by_contra hne
  obtain ⟨p, hp⟩ : ∃ p, φ p ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LocallyConstant.ext h)
  set c := φ p with hc
  let U : Set (PrimeSpectrum B) := φ ⁻¹' {c}
  have hU : IsClosed U := (φ.isLocallyConstant.isClopen_fiber c).isClosed
  let I := PrimeSpectrum.vanishingIdeal U
  let f := Ideal.Quotient.mk I
  have hrange : Set.range (PrimeSpectrum.comap f) = U := by
    rw [_root_.range_comap_of_surjective _ f Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hU.closure_eq]
  have hconst : lcMap f φ = LocallyConstant.const _ c := by
    ext x
    have : PrimeSpectrum.comap f x ∈ U := hrange ▸ ⟨x, rfl⟩
    exact this
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ I := h ▸ Submodule.mem_top
    have hpU : p ∈ U := rfl
    exact p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ((PrimeSpectrum.mem_vanishingIdeal _ _).1 h1 p hpU))
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have h1 := hm.1 B (B ⧸ I) f ζ φ
  rw [hφ, hconst, hm.2] at h1
  simp only [map_zero] at h1
  exact hp (hT q i (B ⧸ I) (ζ.map f) c h1.symm)

theorem LCBij_of (hT : TwGenNZAC) (hS : LCSurj) : LateralTheory.E.LocallyConstantH0.LCBij :=
  fun q _ i m hm B _ ζ => ⟨lcInj (twGenNZ_of hT) q i m hm B ζ, hS q i m hm B ζ⟩

end LateralTheory.E.LCBijPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafPrimCoverPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LeafPrimCoverPf

theorem cyc_cond (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ p₁ p₂ : A[X], derivative (cyclotomic q A) * p₁ + cyclotomic q A * p₂ = 1 := by
  obtain ⟨h, hh⟩ : cyclotomic q A ∣ X ^ q - 1 := cyclotomic.dvd_X_pow_sub_one q A
  have hd := congrArg derivative hh
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul] at hd
  obtain ⟨u, hu⟩ := hq.exists_left_inv
  refine ⟨C u * (h * X), C u * (derivative h * X - C (q : A) * h), ?_⟩
  have hq0 : 0 < q := Nat.pos_of_neZero q
  have e1 : (X : A[X]) ^ q = X ^ (q - 1) * X := by
    rw [← pow_succ, Nat.sub_add_cancel hq0]
  have hc : (C (q : A) : A[X]) = (q : A[X]) := map_natCast C q
  have hcu : C u * C (q : A) = 1 := by rw [← C_mul, hu, C_1]
  rw [e1] at hh
  linear_combination (-(C u * X)) * hd + (C u * C (q:A)) * hh + hcu

def cycPair (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) : StandardEtalePair A where
  f := cyclotomic q A
  monic_f := cyclotomic.monic q A
  g := 1
  cond := by
    obtain ⟨p₁, p₂, h⟩ := cyc_cond A q hq
    exact ⟨p₁, p₂, 0, by simpa using h⟩

theorem etale_adjoin (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  let P := cycPair A q hq
  let e1 : P.Ring ≃ₐ[A] Localization.Away (AdjoinRoot.mk P.f P.g) := P.equivAwayAdjoinRoot
  have hu : IsUnit (AdjoinRoot.mk P.f P.g) := by
    rw [show P.g = 1 from rfl, map_one]; exact isUnit_one
  let e2 : AdjoinRoot P.f ≃ₐ[A] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    (IsLocalization.atUnit (AdjoinRoot P.f) (Localization.Away (AdjoinRoot.mk P.f P.g)) (AdjoinRoot.mk P.f P.g) hu).restrictScalars A
  exact Algebra.Etale.of_equiv (e1.trans e2.symm)

theorem ff_adjoin (A : Type) [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] :
    Module.FaithfullyFlat A (AdjoinRoot (cyclotomic q A)) := by
  let b := AdjoinRoot.powerBasisAux' (cyclotomic.monic q A)
  have hpos : 0 < (cyclotomic q A).natDegree := by
    rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_neZero q)
  have : Nonempty (Fin (cyclotomic q A).natDegree) := ⟨⟨0, hpos⟩⟩
  exact Module.FaithfullyFlat.of_linearEquiv _ _ b.repr

theorem prim_adjoin (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Nonempty (Prim q (AdjoinRoot (cyclotomic q A))) := by
  refine ⟨⟨AdjoinRoot.root _, by simpa using hq.map (algebraMap A (AdjoinRoot (cyclotomic q A))), ?_⟩⟩
  have h0 : aeval (AdjoinRoot.root (cyclotomic q A)) (cyclotomic q A) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [← aeval_map_algebraMap A, map_cyclotomic]
  exact h0

theorem spec_surj (A B : CommRingCat.{0}) (φ : A ⟶ B) (hA : Subsingleton A) : Surjective (Spec.map φ) := by
  constructor
  intro x
  exact absurd (Subsingleton.elim _ _) x.isPrime.ne_top

theorem leafPrimCover_pf : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := by
  intro q _ U hq
  let A : Type := Γ(U, ⊤)
  let B : Type := AdjoinRoot (cyclotomic q A)
  let φ : Γ(U, ⊤) ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  have hEt : Etale (Spec.map φ) := by
    have := etale_adjoin A q hq
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr this)
  have hSu : Surjective (Spec.map φ) := by
    rcases subsingleton_or_nontrivial A with h | h
    · exact spec_surj _ _ φ h
    · have := ff_adjoin A q
      exact ((flat_and_surjective_SpecMap_iff φ).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr this)).2
  let f := pullback.fst U.toSpecΓ (Spec.map φ)
  refine ⟨Sieve.generate (Presieve.singleton f), ?_, ?_⟩
  · apply Precoverage.generate_mem_toGrothendieck
    exact (Scheme.singleton_mem_precoverage_iff (P := @Etale) f).2 ⟨Surjective.surj, inferInstance⟩
  · rintro V g ⟨W, h, k, hk, rfl⟩
    cases hk
    obtain ⟨ζ⟩ := prim_adjoin A q hq
    exact ⟨Prim.map (h.appTop.hom.comp ((pullback.snd U.toSpecΓ (Spec.map φ)).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)) ζ⟩

theorem LeafPrimCover_of : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := leafPrimCover_pf

end LateralTheory.E.LeafPrimCoverPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ProEqvPfA
section -- merged from Development.EtaleCohomology.EtaleSheaves.ProEqvPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut

namespace LateralTheory.E.ProEqvPf

def fm {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}} (u : U ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of A)) :
    pullback (u ≫ g) (cpt A) ⟶ pullback g (cpt A) :=
  pullback.map _ _ _ _ u (𝟙 _) (𝟙 _) (by simp) (by simp)

def Hit (q : ℕ) (i n : ℤ) {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A))
    (z : Ht q (sch.obj (pullback g (cpt A))) n i) (u : U ⟶ Y) : Prop :=
  ∃ w : Ht q (sch.obj U) n i, pull _ (sch.map (pullback.fst (u ≫ g) (cpt A))) _ _ w = pull _ (sch.map (fm u g)) _ _ z

def PiLocalization₂ : Prop := LateralTheory.E.t_E2Cut.Cont → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
  [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
  ClopenSys y D c ι → (∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) → ∀ n : ℤ,
  (∀ x : Ht q (sch.obj Y) n i, pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0 → ∃ j, pull _ (sch.map (ι j)) _ _ x = 0) ∧
  ∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∃ j, Hit q i n g z (ι j)

def Glue : Prop := MV → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (n : ℤ),
  (∀ x : Ht q (sch.obj Y) n i, pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0 → ∀ y : Y,
    ∃ (U : Scheme.{0}) (u : U ⟶ Y), IsOpenImmersion u ∧ IsClosedImmersion u ∧ y ∈ Set.range u ∧ pull _ (sch.map u) _ _ x = 0) →
  (∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∀ y : Y,
    ∃ (U : Scheme.{0}) (u : U ⟶ Y), IsOpenImmersion u ∧ IsClosedImmersion u ∧ y ∈ Set.range u ∧ Hit q i n g z u) →
  Function.Bijective (pull _ (sch.map (pullback.fst g (cpt A))) (tw q i) n)

theorem ProEqv_of (hC : LateralTheory.E.t_E2Cut.Cont) (hM : MV) (hS : PiLocalization₂) (hG : Glue) : ProEqv := by
  intro H q i A _ _ hq Y _ _ g hY n
  refine hG hM H q i A hq g n (fun x hx y => ?_) (fun z y => ?_)
  · obtain ⟨J, _, _, D, c, ι, hc, hp⟩ := hY y
    obtain ⟨j, hj⟩ := (hS hC H q i A hq g y D c ι hc hp n).1 x hx
    exact ⟨_, ι j, (hc.2.1 j).1, (hc.2.1 j).2.1, (hc.2.1 j).2.2, hj⟩
  · obtain ⟨J, _, _, D, c, ι, hc, hp⟩ := hY y
    obtain ⟨j, hj⟩ := (hS hC H q i A hq g y D c ι hc hp n).2 z
    exact ⟨_, ι j, (hc.2.1 j).1, (hc.2.1 j).2.1, (hc.2.1 j).2.2, hj⟩

end LateralTheory.E.ProEqvPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.ProEqvPf

theorem LateralTheory.E.ProEqvPf.stageA (hC : Cont) (H : Hyp) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A))
    {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
    [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y)
    (hc : ClopenSys y D c ι) (hp : ∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) (n : ℤ)
    (x : Ht q (sch.obj Y) n i) (hx : pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0) :
    ∃ j, pull _ (sch.map (ι j)) _ _ x = 0 := by
  obtain ⟨⟨hl⟩, hι, hD⟩ := hc
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := J)
  have e1 : pull _ (sch.map (pullback.fst ((c.π.app j0 ≫ ι j0) ≫ g) (cpt A))) (tw q i) n
      (pull _ (sch.map (c.π.app j0 ≫ ι j0)) (tw q i) n x) = pull _ (sch.map (pullback.fst ((c.π.app j0 ≫ ι j0) ≫ g) (cpt A))) (tw q i) n 0 := by
    rw [map_zero, ← pull_comp, ← Functor.map_comp]
    have : pullback.fst ((c.π.app j0 ≫ ι j0) ≫ g) (cpt A) ≫ c.π.app j0 ≫ ι j0 =
        fm (c.π.app j0 ≫ ι j0) g ≫ pullback.fst g (cpt A) := by
      unfold fm pullback.map; rw [pullback.lift_fst]
    rw [this, Functor.map_comp, pull_comp, hx, map_zero]
  have e2 := (hp j0 n).1 e1
  rw [Functor.map_comp, pull_comp] at e2
  have hcs : ∀ j, CompactSpace (D.obj j) := fun j => by
    have := (hι j).2.1; exact QuasiCompact.compactSpace_of_compactSpace (ι j)
  have hqs : ∀ j, QuasiSeparatedSpace (D.obj j) := fun j => by
    have := (hι j).1; exact quasiSeparatedSpace_of_quasiSeparated (ι j)
  obtain ⟨k, f, hk⟩ := (hC H q D c hl (fun f => (hD f).2) hcs hqs (fun j => unit_of hq (ι j ≫ g)) n i).2 j0 _ e2
  refine ⟨k, ?_⟩
  rw [← (hD f).1, Functor.map_comp, pull_comp]
  exact hk

namespace LateralTheory.E.ProEqvPf

def StageB : Prop := Cont → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
  [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
  ClopenSys y D c ι → (∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) → ∀ n : ℤ,
  ∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∃ j, Hit q i n g z (ι j)

theorem stage_of (hB : StageB) : PiLocalization₂ := by
  intro hC H q i A _ _ hq Y _ _ g y J _ _ D c ι hc hp n
  exact ⟨fun x hx => stageA hC H q i A hq g y D c ι hc hp n x hx, hB hC H q i A hq g y D c ι hc hp n⟩

theorem etale_pro_equivalence_of_continuity_mayer_vietoris_lifting_stage_glue (hC : Cont) (hM : MV) (hB : StageB) (hG : Glue) : ProEqv :=
  ProEqv_of hC hM (stage_of hB) hG

end LateralTheory.E.ProEqvPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LZProperCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.LineZeroCut

namespace LateralTheory.E.LZProperCut

def LZHensFinite : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B],
  ConnectedSpace ↑(Spec (CommRingCat.of B)) → IsLocalRing B

end LateralTheory.E.LZProperCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.GlueRelPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 CochainComplex.HomComplex

namespace LateralTheory.E.GlueRelPf

def obs (q : ℕ) [NeZero q] {U E : Spc} (u : U ⟶ E) (i m : ℤ) : Ht q U m i →+ Hrel (ZMod q) u (tw q i) (m + 1) :=
  HK.pre (ZMod q) (CochainComplex.mappingCone.fst ((chains (ZMod q)).map u)) (tw q i) m (m + 1) (add_comm 1 m)

def ConeExact : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ),
  Function.Exact (HK.pull R φ F m) (HK.pre R (CochainComplex.mappingCone.fst φ) F m (m + 1) (add_comm 1 m))

end LateralTheory.E.GlueRelPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafKumSpecPfEv
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafKumSpecPf

theorem freeGen_res (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  have := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
    (ModuleCat.freeMk (ULift.up x))
  have hm : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up ((P.map g.op) x)) := by
    simp [freeP, ModuleCat.freeMk]
    first | (rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl) | (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl) | (simp [Finsupp.mapDomain_single]; rfl)
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hm] at this
  exact this.symm

end LateralTheory.E.LeafKumSpecPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.IECobPf
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.IECobPf

theorem et_cobase : Et.IsStableUnderCobaseChange :=
  (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff).2 RingHom.Etale.isStableUnderBaseChange

theorem IECob_of : LateralTheory.E.ULAStalkPf.IECob := by
  intro A B C D f g u v sq hf
  have := et_cobase
  have hI : IE.IsStableUnderCobaseChange := by
    unfold IE; infer_instance
  exact hI.of_isPushout sq.flip hf

end LateralTheory.E.IECobPf
end
