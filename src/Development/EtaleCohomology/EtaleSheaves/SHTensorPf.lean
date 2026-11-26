module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.SHTensorPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHTensorPf

def LocTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → IsLocalRing Z

def SepTensor : Prop := ∀ {A X B Z : CommRingCat.{0}} (x : A ⟶ X) (b : A ⟶ B) (u : X ⟶ Z) (v : B ⟶ Z), IsPushout x b u v →
  SH A → SH X → IsLocalHom x.hom → b.hom.IsIntegral → IsLocalRing B → ∀ (_ : IsLocalRing Z),
  IsSepClosed (IsLocalRing.ResidueField Z)

theorem intPush {A X B Z : CommRingCat.{0}} {x : A ⟶ X} {b : A ⟶ B} {u : X ⟶ Z} {v : B ⟶ Z}
    (hp : IsPushout x b u v) (hb : b.hom.IsIntegral) : u.hom.IsIntegral := by
  have h : (RingHom.toMorphismProperty fun f => f.IsIntegral).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.isIntegral_isStableUnderBaseChange
  exact h.of_isPushout hp hb

theorem idem_local (R : Type) [CommRing R] [IsLocalRing R] (e : R) (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right; exact (sub_eq_zero.mp ((h.mul_right_eq_zero).mp h0)).symm
  · left; exact (h.mul_left_eq_zero).mp h0

theorem SHTensor_of (hH : LateralTheory.E.t_E3Cut.HensInt) (hL : LocTensor) (hS : SepTensor) : LateralTheory.E.t_E3Cut.SHTensor := by
  intro A X B Z x b u v hp hA hX hx hb hB
  have hZ : IsLocalRing Z := hL x b u v hp hA hX hx hb hB
  have hsep := hS x b u v hp hA hX hx hb hB hZ
  obtain ⟨hXh, _⟩ := hX
  obtain ⟨hZh⟩ := hH X Z u.hom (intPush hp hb) (idem_local Z)
  exact ⟨hZh, hsep⟩

end LateralTheory.E.SHTensorPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CoverCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.CoverCut

def ClopenSys {Y : Scheme.{0}} (y : Y) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D)
    (ι : ∀ j, D.obj j ⟶ Y) : Prop :=
  Nonempty (IsLimit c) ∧ (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
    ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)

def Build : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P],
  ∃ (Y : Scheme.{0}) (k : Y ⟶ P), IsIntegralHom k ∧ Surjective k ∧
    ∀ y : Y, ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
      ClopenSys y D c ι ∧ AICSch c.pt ∧ ∀ j, IsIntegralHom ((c.π.app j ≫ ι j) ≫ k)

def ProEqv : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)),
  (∀ y : Y, ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
      ClopenSys y D c ι ∧ ∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) →
  PB q i g

theorem goal_of (hB : Build) (hP : ProEqv) : Cover := by
  intro H q i A _ _ hq P _ _ p hZ
  obtain ⟨Y, k, hk, hs, hY⟩ := hB (P := P)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace k
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated k
  refine ⟨Y, k, hk, hs, hP H q i A hq (k ≫ p) fun y => ?_⟩
  obtain ⟨J, _, _, D, c, ι, hc, hA, hint⟩ := hY y
  refine ⟨J, inferInstance, inferInstance, D, c, ι, hc, fun j => ?_⟩
  have := hZ c.pt ((c.π.app j ≫ ι j) ≫ k) (hint j) hA
  simpa only [Category.assoc] using this

end LateralTheory.E.CoverCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StalkGerm
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ZLGPf

variable {Y X S : Scheme.{0}}

abbrev overO (p : X ⟶ S) (U : S.Opens) : Scheme.{0} := pullback p U.ι

abbrev resO (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : overO p V ⟶ overO p U :=
  pullback.map p V.ι p U.ι (𝟙 _) (S.homOfLE h) (𝟙 _) (by simp) (by simp)

abbrev fO (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) : overO (f ≫ p) U ⟶ overO p U :=
  pullback.map (f ≫ p) U.ι p U.ι f (𝟙 _) (𝟙 _) (by simp) (by simp)

def Germ (q : ℕ) (i n : ℤ) (f : Y ⟶ X) (p : X ⟶ S) (s : S) : Prop :=
  (∀ (U : S.Opens), s ∈ U → ∀ x : Ht q (sch.obj (overO p U)) n i, pull _ (sch.map (fO f p U)) _ _ x = 0 →
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ pull _ (sch.map (resO p h)) _ _ x = 0) ∧
  (∀ (U : S.Opens), s ∈ U → ∀ y : Ht q (sch.obj (overO (f ≫ p) U)) n i,
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ ∃ x : Ht q (sch.obj (overO p V)) n i,
      pull _ (sch.map (fO f p V)) _ _ x = pull _ (sch.map (resO (f ≫ p) h)) _ _ y)

def StalkGerm : Prop := Cont → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ, ∀ s : S,
  Eqv _ (sch.map (pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) →
  ∀ n : ℤ, Germ q i n f p s

def ZarInd : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ, (∀ (s : S) (n : ℤ), Germ q i n f p s) → Eqv _ (sch.map f) (tw q i)

theorem ZLG_of (hC : Cont) (hM : MV) (h1 : StalkGerm) (h2 : ZarInd) : ZLG := by
  intro hH q Y X S f p _ _ _ _ _ _ hq i hs
  exact h2 hM hH q f p hq i fun s n => h1 hC hH q f p hq i s (hs s) n

end LateralTheory.E.ZLGPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.PullInjOfIso
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.MVPf

def MVSpc : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ n : ℤ, (∀ c : H R (pullback f g) F n, ∃ a b, c = pull R (pullback.fst f g) F n a - pull R (pullback.snd f g) F n b) →
  ∀ x : H R E F (n + 1), pull R f F _ x = 0 → pull R g F _ x = 0 → x = 0

def StdCover : Prop := ∀ (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  Cover2 R (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g)))

def StdPB : Prop := ∀ (S : Type) [CommRing S] (f g : S),
  ∃ e : sp (Localization.Away (f * g)) ⟶
      pullback (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g))),
    IsIso e ∧ e ≫ pullback.fst _ _ = spMap (LateralTheory.E.t_E1Cut.rL f g) ∧ e ≫ pullback.snd _ _ = spMap (LateralTheory.E.t_E1Cut.rR f g)

theorem pull_inj_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ⟶ E') [IsIso e] (F : Shv R) (n : ℤ) :
    Function.Injective (pull R e F n) := by
  intro x y h
  have hx : pull R (inv e) F n (pull R e F n x) = x := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have hy : pull R (inv e) F n (pull R e F n y) = y := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  rw [← hx, ← hy, h]

end LateralTheory.E.MVPf

open LateralTheory.E.MVPf in
theorem LateralTheory.E.t_E1Cut.MV_of (h1 : MVSpc) (h2 : StdCover) (h3 : StdPB) : LateralTheory.E.t_E1Cut.MV := by
  intro hA1 R _ F S _ f g hfg n hc x hxf hxg
  refine h1 hA1 R F _ _ (h2 R S f g hfg) n ?_ x hxf hxg
  intro c
  obtain ⟨e, he, hfst, hsnd⟩ := h3 S f g
  obtain ⟨a, b, hab⟩ := hc (pull R e F n c)
  refine ⟨a, b, pull_inj_of_iso R e F n ?_⟩
  rw [hab, map_sub, ← pull_comp, ← pull_comp, hfst, hsnd]
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafRingUnitPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRingUnitPf
open LateralTheory.E.CupProductRingLaws

def UnitProp {q : ℕ} {i : ℤ} (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i)))) : Prop :=
  ∀ (U : Scheme.{0}) (t w : ℤ) (h : 0 + t = w) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
    Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → HEq (μ.mul U 0 t w h a b) b

def LeafUnitPair : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ),
  ∃ μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i))), IsTwPair μ ∧ UnitProp μ

def OneLoc {q : ℕ} {E : Spc} (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) : Prop :=
  ∀ (U : Scheme.{0}) (x : Sx E 0 U), Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g (ev (R := ZMod q) α.1 0 0 (by simp) U x) = resGen 0 ζ)

def LeafOneLoc : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E →
  ∀ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, IsOneCocycle q E α → OneLoc α

def LeafUnitAW : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) (i : ℤ)
  (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i)))), UnitProp μ →
  ∀ (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0), OneLoc α →
  ∀ (n : ℤ) (β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q i)) n),
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (0 + i))) (0 + n), μ.IsAW rfl α.1 β.1 γ.1 ∧
      CohomologyClass.mk γ = Ht.cast (by ring) (by ring) (CohomologyClass.mk β : Ht q E n i)

theorem LeafRingUnit_of (hcup : LeafCupSpec) (hex : LeafTwPairExists) (hun : LeafTwPairUnique) (hone : LeafOneSpec)
    (h1 : LeafUnitPair) (h2a : LeafOneLoc) (h2 : LeafUnitAW) : LeafRingUnit := by
  intro q _ E hE n i a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨μ, hμ, hU⟩ := h1 q i
  obtain ⟨⟨α, hα⟩, hαone⟩ := hone q E hE
  obtain ⟨γ, hγ, hγc⟩ := h2 q E i μ hU α (h2a q E hE α hα) n β
  have htw : IsTwPair (twPair q 0 i) := pick_spec (hex q 0 i)
  have hc : cup q (one q E) (CohomologyClass.mk β) = (twPair q 0 i).cup E rfl (one q E) (CohomologyClass.mk β) := rfl
  rw [hc, hun q 0 i _ μ htw hμ E rfl, hαone α hα, (hcup (ZMod q) μ E rfl).2 α β γ hγ, hγc]

end LateralTheory.E.LeafRingUnitPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChowCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChowCut

def Img : Prop := ∀ (A : Type) [CommRing A] {Z X : Scheme.{0}} (h : Z ⟶ X) (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p],
  IsIntegralHom h → IsIntegral Z → ∃ (X₁ : Scheme.{0}) (h₁ : Z ⟶ X₁) (p₁ : X₁ ⟶ Spec (CommRingCat.of A)),
    IsIntegral X₁ ∧ IsProper p₁ ∧ IsIntegralHom h₁ ∧ IsDominant h₁ ∧ h₁ ≫ p₁ = h ≫ p

def ChowL : Prop := ∀ (A : Type) [CommRing A] {X₁ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of A)) [IsProper p₁],
  IsIntegral X₁ → ∃ (X' : Scheme.{0}) (π : X' ⟶ X₁) (U : X₁.Opens) (s : U.toScheme ⟶ X'),
    (U : Set X₁).Nonempty ∧ s ≫ π = U.ι ∧ IT π ∧ IT (π ≫ p₁)

def Norm : Prop := ∀ {Z W : Scheme.{0}} (f : W ⟶ Z) [QuasiSeparated f], AICSch Z →
  (∃ (U : Z.Opens) (s : U.toScheme ⟶ W), (U : Set Z).Nonempty ∧ s ≫ f = U.ι) →
  ∃ (Z' : Scheme.{0}) (v : Z' ⟶ W), IsIntegralHom v ∧ AICSch Z' ∧ IsDominant (v ≫ f)

theorem goal_of (hI : Img) (hC : ChowL) (hN : Norm) : LateralTheory.E.t_E2Cut.Chow := by
  intro A _ Z X h p _ hh hZ
  obtain ⟨X₁, h₁, p₁, hX₁, hp₁, hh₁, hd₁, e⟩ := hI A h p hh hZ.1
  have := hp₁
  have := hh₁
  have := hd₁
  obtain ⟨X', π, U, s, hU, hs, hπ, hπp⟩ := hC A p₁ hX₁
  obtain ⟨_, _⟩ := (hπ.bc h₁ (IsPullback.of_hasPullback h₁ π).flip).qc
  have hU' : ((h₁ ⁻¹ᵁ U : Z.Opens) : Set Z).Nonempty := by
    obtain ⟨x, hxU, y, rfl⟩ := h₁.denseRange.inter_open_nonempty _ U.isOpen hU
    exact ⟨y, hxU⟩
  have sec : ∃ (V : Z.Opens) (t : V.toScheme ⟶ pullback h₁ π), (V : Set Z).Nonempty ∧ t ≫ pullback.fst h₁ π = V.ι :=
    ⟨h₁ ⁻¹ᵁ U, pullback.lift (h₁ ⁻¹ᵁ U).ι ((h₁ ∣_ U) ≫ s) (by rw [Category.assoc, hs, morphismRestrict_ι]), hU',
      pullback.lift_fst _ _ _⟩
  obtain ⟨Z', v, hv, hZ', hd⟩ := hN (pullback.fst h₁ π) hZ sec
  refine ⟨Z', v ≫ pullback.fst h₁ π, hZ', hd, hπ.bc h₁ (IsPullback.of_hasPullback h₁ π).flip |>.pre v hv, ?_⟩
  have : (v ≫ pullback.fst h₁ π) ≫ h ≫ p = (v ≫ pullback.snd h₁ π) ≫ π ≫ p₁ := by
    rw [← e, Category.assoc, reassoc_of% pullback.condition, Category.assoc]
  rw [this]
  exact hπp.pre _ inferInstance

end LateralTheory.E.ChowCut

end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.QuotAcycCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.QuotAcycCut

def ProdAcyc : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A : Type) [CommRing A] (n : ℕ) (R : Fin n → Type) [∀ k, CommRing (R k)],
  Nonempty (A ≃+* ∀ k, R k) → (∀ k, Acyc q (sp (R k))) → Acyc q (sp A)

def Hens : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (_ : IsColimit c),
    (∀ j, ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
      (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (D.obj j ≃+* ∀ k, R k)) ∧
    IsUnit (q : c.pt) ∧ ∃ K : Ideal c.pt, HenselianRing c.pt K ∧ Nonempty (B ⧸ I ≃+* c.pt ⧸ K)

theorem goal_of (hP : ProdAcyc) (hH : Hens) : LateralTheory.E.t_E2Cut.QuotAcyc := by
  intro H q B _ _ I hB hq
  obtain ⟨J, _, _, D, c, hc, hD, hqc, K, hK, ⟨e⟩⟩ := hH q B I hB hq

  have hst : ∀ j, Acyc q (sp (D.obj j)) := by
    intro j
    obtain ⟨m, R, _, hR, hiso⟩ := hD j
    refine hP H q (D.obj j) m R hiso fun k => ?_
    have := (hR k).1
    exact H.b5 q (R k) (hR k).2.1 (hR k).2.2

  have hC : Acyc q (sp c.pt) := by
    intro n i hn
    refine ⟨fun x y => ?_⟩
    have h0 : ∀ x : Ht q (sp c.pt) n i, x = 0 := by
      intro x
      obtain ⟨j, y, rfl⟩ := (H.b1 q D c hc n i).1 x hqc
      have := hst j n i hn
      rw [Subsingleton.elim y 0, map_zero]
    rw [h0 x, h0 y]

  have hCK : Acyc q (sp (c.pt ⧸ K)) := by
    intro n i hn
    have := hC n i hn
    have hE := H.e1 q c.pt K hqc i n
    exact hE.2.subsingleton
  exact hP H q (B ⧸ I) 1 (fun _ => c.pt ⧸ K) ⟨e.trans (RingEquiv.piUnique (fun _ : Fin 1 => c.pt ⧸ K)).symm⟩ fun _ => hCK

end LateralTheory.E.QuotAcycCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.AICAcycPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.AICAcycPf

theorem acyc_of_iso (q : ℕ) {X Y : Scheme.{0}} (e : X ≅ Y) (h : Acyc q (sch.obj Y)) : Acyc q (sch.obj X) := by
  intro n i hn
  have := h n i hn
  constructor
  intro a b
  have key : ∀ a : Ht q (sch.obj X) n i,
      a = pull _ (sch.map e.hom) _ n (pull _ (sch.map e.inv) _ n a) := by
    intro a
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [key a, key b, Subsingleton.elim (pull _ (sch.map e.inv) _ n a) (pull _ (sch.map e.inv) _ n b)]

theorem aff (hB5 : B5) (q : ℕ) (Z : Scheme.{0}) [IsAffine Z] (hZ : AICSch Z) (hq : IsUnit (q : Γ(Z, ⊤))) :
    Acyc q (sch.obj Z) := by
  have : IsIntegral Z := hZ.1
  have hA : AIC Γ(Z, ⊤) := hZ.2 ⊤ (isAffineOpen_top Z) ⟨Nonempty.some inferInstance, by simp⟩
  have h5 := hB5 q Γ(Z, ⊤) hA hq
  exact acyc_of_iso q Z.isoSpec h5

def Step : Prop := Hyp → MV → HZero → ∀ (q : ℕ) {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
  [IsOpenImmersion g], Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
  Acyc q (sch.obj U) → Acyc q (sch.obj V) → (Nonempty ↥(pullback f g : Scheme.{0}) → Acyc q (sch.obj (pullback f g))) → Acyc q (sch.obj X)

def Cov : Prop := ∀ (q : ℕ) (P : Scheme.{0} → Prop), (∀ {X Y : Scheme.{0}}, (X ≅ Y) → P Y → P X) →
  (∀ Z : Scheme.{0}, IsAffine Z → AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z) →
  (∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g],
    Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
    P U → P V → (Nonempty ↥(pullback f g : Scheme.{0}) → P (pullback f g)) → P X) →
  ∀ (Z : Scheme.{0}) [CompactSpace Z] [QuasiSeparatedSpace Z], AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z

theorem AICAcyc_of (hZ : HZero) (hMV : MV) (hStep : Step) (hCov : Cov) : AICAcyc := by
  intro hyp q Z _ _ hZs hq
  refine hCov q (fun W => Acyc q (sch.obj W)) ?_ ?_ ?_ Z hZs hq
  · intro X Y e h
    exact acyc_of_iso q e h
  · intro W hA hW hWq
    exact aff hyp.b5 q W hW hWq
  · intro U V X f g _ _ hc hX hU hV hq' hPU hPV hPW
    exact hStep hyp hMV hZ q f g hc hX hU hV hq' hPU hPV hPW

end LateralTheory.E.AICAcycPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSupport
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafA6suppPf

def LeafAWSpec : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) {n m i j : ℤ}
  (α : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q i)) n)
  (β : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q j)) m),
  ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res (ZMod q) (tw q (i + j))) (n + m),
    (twPair q i j).IsAW rfl α.1 β.1 γ.1 ∧
    cup q (CohomologyClass.mk α : Ht q E n i) (CohomologyClass.mk β : Ht q E m j) = CohomologyClass.mk γ

def LeafRepVanish : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E), Mono f → ∀ (F : Shv R) (n : ℤ)
  (a : H R E F n), pull R f F n a = 0 →
  ∃ α : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk α = a ∧
    ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + n = w) (Y : Scheme.{0}) (y : Sx U N Y), ev α.1 N w h Y ((f.app _).app _ y) = 0

def LeafCochainVanish : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g →
  ∀ (K : Cx R) (k : ℤ) (γ : Cochain ((chains R).obj E) K k),
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx U N Y), ev γ N w h Y ((f.app _).app _ y) = 0) →
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx V N Y), ev γ N w h Y ((g.app _).app _ y) = 0) →
    γ = 0

theorem sub_map {U E : Spc} (f : U ⟶ E) {N : ℕ} {Y : Scheme.{0}} (y : Sx U N Y) (j l : ℕ) (h : j + l ≤ N) :
    Sx.sub ((f.app _).app _ y) j l h = (f.app _).app _ (Sx.sub y j l h) := by
  unfold Sx.sub
  have e := NatTrans.congr_app (f.naturality (SimplexCategory.subinterval j l h).op) (op Y)
  exact (ConcreteCategory.congr_hom e y).symm

theorem LeafA6supp_of (h1 : LeafAWSpec) (h2 : LeafRepVanish) (h3 : LeafCochainVanish) : LateralTheory.E.D2.LeafA6supp := by
  intro q _ U V E f g hc n m i j a b ha hb
  obtain ⟨α, rfl, hα⟩ := h2 (ZMod q) f hc.1 (tw q i) n a ha
  obtain ⟨β, rfl, hβ⟩ := h2 (ZMod q) g hc.2.1 (tw q j) m b hb
  obtain ⟨γ, hAW, hcup⟩ := h1 q E α β
  rw [hcup]
  have : γ.1 = 0 := by
    apply h3 (ZMod q) f g hc
    · intro N w h Y y
      rw [hAW N w h Y]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [sub_map f y 0 (p : ℕ), hα]
      simp
    · intro N w h Y y
      rw [hAW N w h Y]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [sub_map g y (p : ℕ) (N - p), hβ]
      simp
  have hγ : γ = 0 := Subtype.ext this
  rw [hγ]
  exact CohomologyClass.mk_zero _ _ _

end LateralTheory.E.LeafA6suppPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SHEqvPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHEqvPf
open LateralTheory.E.t_E3Cut

def SecBij : Prop := SHSection → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) →
  SH A → SH B → Function.Bijective (fun s : Sec (tw q i) (Spec A) => Sec.res (Spec.map f) s)

def SecPre : Prop := SHSection → ∀ (q : ℕ) (i : ℤ) (A : CommRingCat.{0}), SH A →
  Function.Bijective (ofRings.sec (twF q i) (Spec A))

def TwFBij : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B), IsUnit (q : A) → SH A → SH B →
  Function.Bijective ((twF q i).map (Spec.map f).appTop).hom

theorem sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}} (j : V ⟶ U)
    (m : M.obj Γ(U, ⊤)) : Sec.res j (ofRings.sec M U m) = ofRings.sec M V ((M.map j.appTop).hom m) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op
  have h2 := congrArg (fun φ => φ.hom m) h
  exact h2.symm

theorem SecBij_of (hP : SecPre) (hT : TwFBij) : SecBij := by
  intro hSec q _ i A B f hq hA hB
  have key : (fun s : Sec (tw q i) (Spec A) => Sec.res (Spec.map f) s) =
      ofRings.sec (twF q i) (Spec B) ∘ ((twF q i).map (Spec.map f).appTop).hom ∘
        (Equiv.ofBijective _ (hP hSec q i A hA)).symm := by
    funext s
    obtain ⟨m, rfl⟩ := (hP hSec q i A hA).2 s
    simp only [Function.comp]
    rw [Equiv.ofBijective_symm_apply_apply]
    exact sec_res _ _ _
  rw [key]
  exact (hP hSec q i B hB).comp ((hT q i f hq hA hB).comp (Equiv.bijective (Equiv.ofBijective _ (hP hSec q i A hA)).symm))

theorem bij_of_subsingleton {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Subsingleton M] [Subsingleton N]
    (g : M →+ N) : Function.Bijective g :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

theorem SHEqv_of_secBij (hSec : SHSection) (hB : SecBij) : SHEqv := by
  intro hyp q _ i A B f hq hA hBs n
  obtain ⟨_, _, _, _, _, hA9, _, hB2, _⟩ := hyp
  obtain ⟨hneg, e, he, -⟩ := hA9 (ZMod q) (tw q i)
  rcases lt_trichotomy n 0 with h | h | h
  · haveI := hneg (sch.obj (Spec A)) n h
    haveI := hneg (sch.obj (Spec B)) n h
    exact bij_of_subsingleton _
  · subst h
    have key : ⇑(pull (ZMod q) (sch.map (Spec.map f)) (tw q i) 0) =
        (e (Spec B)) ∘ (fun s : Sec (tw q i) (Spec A) => Sec.res (Spec.map f) s) ∘ (e (Spec A)).symm := by
      funext x
      simp only [Function.comp]
      rw [← he]
      simp
    show Function.Bijective (pull (ZMod q) (sch.map (Spec.map f)) (tw q i) 0)
    rw [key]
    exact (e _).bijective.comp ((hB hSec q i f hq hA hBs).comp (e _).symm.bijective)
  · haveI := hB2 (ZMod q) A hA (tw q i) n h
    haveI := hB2 (ZMod q) B hBs (tw q i) n h
    exact bij_of_subsingleton _

end LateralTheory.E.SHEqvPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StalkCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.StalkCut

def RelZ (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map f)) (tw q i) m)) ∧
  Function.Injective (pull _ (sch.map (Spec.map f)) (tw q i) n)

def BCn (q : ℕ) (i n : ℤ) {A Y C : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) : Prop :=
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' → RelZ q i n φ'

def PushClosed {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop) : Prop :=
  ∀ {C D E Z : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D) (g : C ⟶ E) (u : D ⟶ Z) (v : E ⟶ Z), IsPushout f g u v →
    P C c → P D (c ≫ f) → P E (c ≫ g) → P Z (c ≫ f ≫ u)

def EtClosed {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop) : Prop :=
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D), P C c → Et f → P D (c ≫ f)

theorem relZ_neg (hH : Hyp) (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (hn : n < 0) : RelZ q i n f := by
  have hA9 := (hH.2.2.2.2.2.1 (ZMod q) (tw q i)).1
  refine ⟨fun m hm y => ?_, fun x y _ => ?_⟩
  · haveI := hA9 (sch.obj (Spec B)) m (by omega)
    exact ⟨0, Subsingleton.elim _ _⟩
  · haveI := hA9 (sch.obj (Spec A)) n hn
    exact Subsingleton.elim _ _

theorem re_of_relZ {q : ℕ} {i : ℤ} {A B : CommRingCat.{0}} {f : A ⟶ B} (h : ∀ n, RelZ q i n f) : RE q i f :=
  fun m => ⟨(h m).2, (h (m + 1)).1 m rfl⟩

def DescInt : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → g.hom.IsIntegral → SpS g →
  BCn q i n φ (c ≫ g) → BCn q i n φ c

def DescLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  (∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
    BC q i φ (d ≫ o)) →
  BCn q i n φ d

theorem goal_of (hInt : DescInt) (hLoc : DescLoc) : LateralTheory.E.t_E3Cut.Stalk := by
  intro hH q _ i A Y φ hq P hpush het hcov C c hC
  have key : ∀ k : ℕ, ∀ m : ℤ, m < k → ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c := by
    intro k
    induction k with
    | zero =>
      intro m hm C c _ Y' w φ' _
      exact relZ_neg hH q i m φ' (by exact_mod_cast hm)
    | succ k ih =>
      intro m hm C c hC
      have hm' : m ≤ (k : ℤ) := by push_cast at hm; omega
      rcases lt_or_eq_of_le hm' with h | h
      · exact ih m h C c hC
      · subst h
        obtain ⟨D, g, hgi, hgs, hD, hpts⟩ := hcov C c hC
        have hDl : BCn q i (k : ℤ) φ (c ≫ g) :=
          hLoc hH q i k φ hq P @hpush @het ih D (c ≫ g) hD (fun r hr => by
            obtain ⟨O, o, Q, h1, h2, h3, h4⟩ := hpts r hr
            exact ⟨O, o, Q, h1, h2, h3, by rwa [Category.assoc]⟩)
        exact hInt hH q i k φ hq P @hpush ih c g hC hD hgi hgs hDl
  intro Y' w φ' hpo
  refine re_of_relZ fun n => ?_
  exact key (n.toNat + 1) n (by omega) C c hC Y' w φ' hpo

end LateralTheory.E.StalkCut
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LineHighPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.LineHighPf

open LateralTheory.E.t_E2Cut

def QAIC (q : ℕ) (W : Scheme.{0}) : Prop :=
  ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (I : Ideal B), AIC B ∧ IsUnit (q : B) ∧
    Nonempty (W ≅ Spec (CommRingCat.of (B ⧸ I)))

def Cover2 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z →
  ∃ (U V : Scheme.{0}) (f : U ⟶ pullback p (cpt A)) (g : V ⟶ pullback p (cpt A)),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    QAIC q U ∧ QAIC q V ∧ QAIC q (pullback f g)

theorem acyc_of_iso {q : ℕ} {W W' : Scheme.{0}} (e : W ≅ W') (h : Acyc q (sch.obj W')) : Acyc q (sch.obj W) := by
  intro n i hn
  have := h n i hn
  refine ⟨fun x y => ?_⟩
  have hs : ∀ z : Ht q (sch.obj W) n i,
      pull _ (sch.map e.hom) (tw q i) n (pull _ (sch.map e.inv) (tw q i) n z) = z := by
    intro z
    rw [← pull_comp, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [← hs x, ← hs y, Subsingleton.elim (pull _ (sch.map e.inv) (tw q i) n x) (pull _ (sch.map e.inv) (tw q i) n y)]

theorem acyc_of_QAIC (H : Hyp) (hQ : QuotAcyc) {q : ℕ} {W : Scheme.{0}} (h : QAIC q W) : Acyc q (sch.obj W) := by
  obtain ⟨B, _, _, I, hB, hq, ⟨e⟩⟩ := h
  exact acyc_of_iso e (hQ H q B I hB hq)

theorem high_of_cover (H : Hyp) (hM : MV) {q : ℕ} {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
    [IsOpenImmersion g] (hc : Set.range f ∪ Set.range g = Set.univ) (hU : Acyc q (sch.obj U)) (hV : Acyc q (sch.obj V))
    (hW : Acyc q (sch.obj (pullback f g))) (i n : ℤ) (hn : 2 ≤ n) : Subsingleton (Ht q (sch.obj X) n i) := by
  obtain ⟨δ, hδ, -⟩ := hM H (ZMod q) (tw q i)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have key : ∀ x : Ht q (sch.obj X) (m + 1) i, x = 0 := by
    intro x
    have h3 := ((hδ f g hc m).2.2 x).1
    have := hU (m + 1) i (by omega)
    have := hV (m + 1) i (by omega)
    have := hW m i (by omega)
    obtain ⟨w, hw⟩ := h3 ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw, Subsingleton.elim w 0, map_zero]
  exact ⟨fun x y => by rw [key x, key y]⟩

theorem LineHigh_of (hQ : QuotAcyc) (hM : MV) (hC : Cover2) : LineHigh := by
  intro H q i A _ _ hq Z p hp hZ n hn
  obtain ⟨U, V, f, g, hf, hg, hc, hU, hV, hW⟩ := hC q A hq p hp hZ
  exact high_of_cover H hM f g hc (acyc_of_QAIC H hQ hU) (acyc_of_QAIC H hQ hV) (acyc_of_QAIC H hQ hW) i n hn

theorem fibre_affine (A B : Type) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] :
    Nonempty (pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (cpt A) ≅
      Spec (CommRingCat.of (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)))) := by
  refine ⟨pullbackSpecIso A B (IsLocalRing.ResidueField A) ≪≫ ?_⟩
  exact Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal A)).toRingEquiv).op

def Good {A : Type} [CommRing A] {W : Scheme.{0}} (w : W ⟶ Spec (CommRingCat.of A)) : Prop :=
  IsEmpty W ∨ ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra A B), AIC B ∧
    ∃ e : W ≅ Spec (CommRingCat.of B), e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = w

def ZCov : Prop := ∀ (A : Type) [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z →
  ∃ (U V : Scheme.{0}) (f : U ⟶ Z) (g : V ⟶ Z), IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    Good (f ≫ p) ∧ Good (g ≫ p) ∧ Good (pullback.fst f g ≫ f ≫ p)

def FibCov : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)), AICSch Z → ∀ {U V : Scheme.{0}} (f : U ⟶ Z) (g : V ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g],
  Set.range f ∪ Set.range g = Set.univ → Good (f ≫ p) → Good (g ≫ p) → Good (pullback.fst f g ≫ f ≫ p) →
  ∃ (U V : Scheme.{0}) (f : U ⟶ pullback p (cpt A)) (g : V ⟶ pullback p (cpt A)),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧ Set.range f ∪ Set.range g = Set.univ ∧
    QAIC q U ∧ QAIC q V ∧ QAIC q (pullback f g)

theorem Cover2_of (hZ : ZCov) (hF : FibCov) : Cover2 := by
  intro q A _ _ hq Z p hp hZA
  obtain ⟨U, V, f, g, hf, hg, hc, h1, h2, h3⟩ := hZ A p hp hZA
  exact hF q A hq p hZA f g hc h1 h2 h3

end LateralTheory.E.LineHighPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafCover2Of
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafCover2Pf

variable (R : Type) [CommRing R]

theorem pre_eq {P Q : PSh} (G : Shv R) (φ : Q ⟶ P) (u v : (free R).obj P ⟶ G)
    (h : (free R).map φ ≫ u = (free R).map φ ≫ v) :
    (freeP R).map φ ≫ (toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ u.hom) =
      (freeP R).map φ ≫ (toSheafify Scheme.etaleTopology ((freeP R).obj P) ≫ v.hom) := by
  have k := congrArg (fun w => toSheafify Scheme.etaleTopology ((freeP R).obj Q) ≫ w.hom) h
  exact (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map φ) u.hom).trans
    (k.trans (toSheafify_naturality_assoc Scheme.etaleTopology ((freeP R).map φ) v.hom).symm)

theorem gen_eq {P Q : PSh} (G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : Q ⟶ P) (a b : (freeP R).obj P ⟶ G)
    (h : (freeP R).map φ ≫ a = (freeP R).map φ ≫ b) (Y : Scheme.{0}) (y : Q.obj (op Y)) :
    a.app (op Y) (ModuleCat.freeMk (ULift.up (φ.app _ y))) = b.app (op Y) (ModuleCat.freeMk (ULift.up (φ.app _ y))) := by
  have e : ((freeP R).map φ).app (op Y) (ModuleCat.freeMk (ULift.up y)) =
      ModuleCat.freeMk (ULift.up (φ.app _ y)) := by
    first | rfl | exact ModuleCat.free_map_apply (R := ULift R) _ _
  have h3 := congrArg (fun w => w (ModuleCat.freeMk (ULift.up y)))
    (congrArg (fun t => ConcreteCategory.hom t) (NatTrans.congr_app h (op Y)))
  simp only [NatTrans.comp_app] at h3
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, e] at h3
  exact h3

theorem loc_eq {P : PSh} (G : Shv R) (a b : (freeP R).obj P ⟶ G.obj) (X : Scheme.{0}) (x : P.obj (op X))
    (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X)
    (h : ∀ (Y : Scheme.{0}) (k : Y ⟶ X), S.arrows k →
      a.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x))) = b.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x)))) :
    a.app (op X) (ModuleCat.freeMk (ULift.up x)) = b.app (op X) (ModuleCat.freeMk (ULift.up x)) := by
  have key : ∀ (c : (freeP R).obj P ⟶ G.obj) (Y : Scheme.{0}) (k : Y ⟶ X),
      G.obj.map k.op (c.app (op X) (ModuleCat.freeMk (ULift.up x))) = c.app (op Y) (ModuleCat.freeMk (ULift.up (P.map k.op x))) := by
    intro c Y k
    have n1 := ConcreteCategory.congr_hom (c.naturality k.op) (ModuleCat.freeMk (ULift.up x))
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at n1
    rw [← n1]
    congr 1
    first | rfl | exact ModuleCat.free_map_apply (R := ULift R) _ _
  have hE := Presheaf.IsSheaf.hom_ext G.2 ⟨S, hS⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift R) _ (a.app (op X) (ModuleCat.freeMk (ULift.up x)))))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift R) _ (b.app (op X) (ModuleCat.freeMk (ULift.up x))))) (by
      intro I
      ext1
      apply LinearMap.ext_ring
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.toSpanSingleton_apply, one_smul]
      erw [key a, key b]
      exact h _ _ I.hf)
  have := ConcreteCategory.congr_hom hE (1 : ULift R)
  simpa using this

theorem LeafCover2_of : LateralTheory.E.D2.LeafCover2 := by
  intro R _ U V E f g hf hg hc
  refine ⟨hf, hg, fun n => ⟨fun {G} u v huv => ?_⟩⟩
  induction n using Opposite.rec with | op n => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = SimplexCategory.mk m := ⟨n.len, rfl⟩
  have h1 : (free R).map (f.app _) ≫ u = (free R).map (f.app _) ≫ v := by
    simpa using congrArg (biprod.inl ≫ ·) huv
  have h2 : (free R).map (g.app _) ≫ u = (free R).map (g.app _) ≫ v := by
    simpa using congrArg (biprod.inr ≫ ·) huv
  have p1 := pre_eq R G _ u v h1
  have p2 := pre_eq R G _ u v h2
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (P := (freeP R).obj (E.obj (op (SimplexCategory.mk m)))) _ _ _ G.2 ?_
  apply NatTrans.ext
  funext Y
  induction Y using Opposite.rec with | op X => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  obtain ⟨S, hS, hk⟩ := hc m X x
  refine loc_eq R G _ _ X x S hS ?_
  intro Y k hk'
  rcases hk Y k hk' with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [← hy]; exact gen_eq R _ _ _ _ p1 Y y
  · rw [← hy]; exact gen_eq R _ _ _ _ p2 Y y

end LateralTheory.E.LeafCover2Pf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LCSplitPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LCSplitPf
open LateralTheory.E.t_E1Cut

def Idem : Prop := ∀ (q : ℕ) [NeZero q] (R : Type) [CommRing R] (φ : LocallyConstant (PrimeSpectrum R) (ZMod q)),
  ∃ ε : ZMod q → R, CompleteOrthogonalIdempotents ε ∧ ∀ (p : PrimeSpectrum R) (c : ZMod q), φ p = c ↔ ε c ∉ p.asIdeal

def Torsor : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (φ : LocallyConstant (PrimeSpectrum (Localization.Away (f * g))) (ZMod q)) (ε : ZMod q → Localization.Away (f * g)),
  CompleteOrthogonalIdempotents ε → (∀ (p : PrimeSpectrum (Localization.Away (f * g))) (c : ZMod q), φ p = c ↔ ε c ∉ p.asIdeal) →
  ∃ (C : Type) (_ : CommRing C) (_ : Algebra S C), Algebra.Etale S C ∧ Module.Finite S C ∧
    Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) ∧
    (Nonempty (C →ₐ[S] S) → ∃ a b, φ = lcMap (rL f g) a - lcMap (rR f g) b)

theorem LCSplit_of_idem (hF : FinEtSection) (hI : Idem) (hT : Torsor) : LCSplit := by
  intro q _ S _ hS f g hfg φ
  obtain ⟨ε, hε, hφ⟩ := hI q _ φ
  obtain ⟨C, _, _, hEt, hFin, hSurj, hsec⟩ := hT q S f g hfg φ ε hε hφ
  exact hsec (hF S C hS hSurj)

theorem idem_of : Idem := by
  intro q _ R _ φ
  classical
  let E := fun c : ZMod q => PrimeSpectrum.isIdempotentElemEquivClopens (R := R) |>.symm
    ⟨{x | φ x = c}, φ.isLocallyConstant.isClopen_fiber c⟩
  have hB : ∀ c, PrimeSpectrum.basicOpen (E c).1 = ⟨{x | φ x = c}, (φ.isLocallyConstant.isClopen_fiber c).isOpen⟩ :=
    fun c => PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm _
  have hmem : ∀ (p : PrimeSpectrum R) c, φ p = c ↔ (E c).1 ∉ p.asIdeal := by
    intro p c
    have := congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum R) => p ∈ U) (hB c)
    simp only [PrimeSpectrum.mem_basicOpen] at this
    exact (this.to_iff.trans (by rfl)).symm
  refine ⟨fun c => (E c).1, ?_, hmem⟩
  have hid : ∀ c, IsIdempotentElem (E c).1 := fun c => (E c).2
  have horth : OrthogonalIdempotents (fun c => (E c).1) := by
    refine ⟨hid, ?_⟩
    intro c d hcd
    apply IsIdempotentElem.eq_zero_of_isNilpotent ((hid c).mul (hid d))
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    by_contra h
    have hc : (E c).1 ∉ J := fun hc => h (J.mul_mem_right _ hc)
    have hd : (E d).1 ∉ J := fun hd => h (J.mul_mem_left _ hd)
    exact hcd (((hmem ⟨J, hJ⟩ c).2 hc).symm.trans ((hmem ⟨J, hJ⟩ d).2 hd))
  refine CompleteOrthogonalIdempotents.of_prod_one_sub horth ?_
  have hP : IsIdempotentElem (∏ c, (1 - (E c).1)) := by
    classical
    induction (Finset.univ : Finset (ZMod q)) using Finset.induction_on with
    | empty => simpa using IsIdempotentElem.one
    | insert a s ha ih => rw [Finset.prod_insert ha]; exact (hid a).one_sub.mul ih
  apply IsIdempotentElem.eq_zero_of_isNilpotent hP
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  rw [Ideal.IsPrime.prod_mem_iff]
  refine ⟨φ ⟨J, hJ⟩, Finset.mem_univ _, ?_⟩
  have hn : (E (φ ⟨J, hJ⟩)).1 ∉ J := (hmem ⟨J, hJ⟩ _).1 rfl
  have h0 : (E (φ ⟨J, hJ⟩)).1 * (1 - (E (φ ⟨J, hJ⟩)).1) ∈ J := by
    rw [mul_sub, mul_one, (hid _).eq, sub_self]; exact J.zero_mem
  exact (hJ.mem_or_mem h0).resolve_left hn

theorem LCSplit_of (hF : FinEtSection) (hT : Torsor) : LCSplit := LCSplit_of_idem hF idem_of hT

section Conc
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}

def twist (hε : CompleteOrthogonalIdempotents ε) : (ZMod q → A) →+* (ZMod q → A) where
  toFun z k := ∑ c, ε c * z (k + c)
  map_one' := by funext k; simp [hε.complete]
  map_zero' := by funext k; simp
  map_add' x y := by funext k; simp [mul_add, Finset.sum_add_distrib]
  map_mul' x y := by
    funext k
    simp only [Pi.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [show ε c * x (k + c) * (ε c * y (k + c)) = (ε c * ε c) * (x (k + c) * y (k + c)) by ring, (hε.idem c).eq]
    · intro d _ hdc
      rw [show ε c * x (k + c) * (ε d * y (k + d)) = (ε c * ε d) * (x (k + c) * y (k + d)) by ring, hε.ortho (Ne.symm hdc), zero_mul]
    · simp
end Conc

section Tor
variable {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S) {ε : ZMod q → Localization.Away (f * g)}

abbrev Amb (q : ℕ) := (ZMod q → Localization.Away f) × (ZMod q → Localization.Away g)

def h1 : Amb f g q →+* (ZMod q → Localization.Away (f * g)) :=
  Pi.ringHom fun k => (rL f g).comp ((Pi.evalRingHom _ k).comp (RingHom.fst _ _))

def h2 (hε : CompleteOrthogonalIdempotents ε) : Amb f g q →+* (ZMod q → Localization.Away (f * g)) :=
  (twist hε).comp (Pi.ringHom fun k => (rR f g).comp ((Pi.evalRingHom _ k).comp (RingHom.snd _ _)))

def Tor (hε : CompleteOrthogonalIdempotents ε) : Subring (Amb f g q) := RingHom.eqLocus (h1 f g) (h2 f g hε)

def torMap (hε : CompleteOrthogonalIdempotents ε) : S →+* Tor f g hε :=
  RingHom.codRestrict (RingHom.prod ((Pi.constRingHom (ZMod q) _).comp (algebraMap S _))
    ((Pi.constRingHom (ZMod q) _).comp (algebraMap S _))) (Tor f g hε) (by
    intro s
    show h1 f g _ = h2 f g hε _
    funext k
    change rL f g (algebraMap S _ s) = ∑ c, ε c * rR f g (algebraMap S _ s)
    unfold rL rR
    rw [IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayLeft_eq, ← Finset.sum_mul, hε.complete, one_mul])
end Tor

def TorEt : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  Algebra.Etale S (Tor f g hε) ∧ Module.Finite S (Tor f g hε) ∧
    Function.Surjective (PrimeSpectrum.comap (algebraMap S (Tor f g hε)))

def TorSec : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (φ : LocallyConstant (PrimeSpectrum (Localization.Away (f * g))) (ZMod q)) (ε : ZMod q → Localization.Away (f * g))
  (hε : CompleteOrthogonalIdempotents ε), (∀ (p : PrimeSpectrum (Localization.Away (f * g))) (c : ZMod q), φ p = c ↔ ε c ∉ p.asIdeal) →
  letI := (torMap f g hε).toAlgebra
  Nonempty (Tor f g hε →ₐ[S] S) → ∃ a b, φ = lcMap (rL f g) a - lcMap (rR f g) b

theorem torsor_of (hE : TorEt) (hS : TorSec) : Torsor := by
  intro q _ S _ f g hfg φ ε hε hφ
  letI := (torMap f g hε).toAlgebra
  obtain ⟨h1, h2, h3⟩ := hE q S f g hfg ε hε
  exact ⟨Tor f g hε, inferInstance, (torMap f g hε).toAlgebra, h1, h2, h3, hS q S f g hfg φ ε hε hφ⟩

theorem LCSplit_of_tor (hF : FinEtSection) (hE : TorEt) (hS : TorSec) : LCSplit := LCSplit_of hF (torsor_of hE hS)

end LateralTheory.E.LCSplitPf
end
end
