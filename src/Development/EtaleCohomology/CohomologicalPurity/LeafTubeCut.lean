module

public import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

def Good {d : ℕ} (P : SP d) (V : P.X.affineOpens) : Prop :=
  (P.ι.ker.ideal V).FG ∧ Chart d Γ(P.X, V.1) (P.ι.ker.ideal V)

structure Sys {d : ℕ} (P : SP d) where
  J : Type
  [ord : Preorder J]
  V : J → P.X.affineOpens
  mono : ∀ {j k}, j ≤ k → V j ≤ V k
  good : ∀ j, Good P (V j)
  cov : ∀ x : P.X, ∃ j, x ∈ (V j).1
  dir : ∀ (x : P.X) j k, x ∈ (V j).1 → x ∈ (V k).1 → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ (V l).1

attribute [instance] Sys.ord

def Sys.all (hC : LeafChart) {d : ℕ} (P : SP d) : Sys P where
  J := {V : P.X.affineOpens // Good P V}
  V j := j.1
  mono h := h
  good j := j.2
  cov x := by
    obtain ⟨V, h, -, g⟩ := hC d P x ⊤ trivial
    exact ⟨⟨V, g⟩, h⟩
  dir x j k hj hk := by
    obtain ⟨V, h, l, g⟩ := hC d P x (j.1.1 ⊓ k.1.1) ⟨hj, hk⟩
    exact ⟨⟨V, g⟩, l.trans inf_le_left, l.trans inf_le_right, h⟩

variable {d : ℕ}

abbrev eta (H : Hens) (P : SP d) (V : P.X.affineOpens) : Γ(P.X, V.1) →+* H.obj Γ(P.X, V.1) (P.ι.ker.ideal V) := H.η _ _

abbrev hensTo (H : Hens) (P : SP d) (V : P.X.affineOpens) : Spec (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) ⟶ P.X :=
  Spec.map (CommRingCat.ofHom (eta H P V)) ≫ V.2.fromSpec

def Sys.aff {P : SP d} (S : Sys P) : S.J ⥤ Scheme.{0} where
  obj j := Spec Γ(P.X, (S.V j).1)
  map f := Spec.map (P.X.presheaf.map (homOfLE (S.mono f.le)).op)
  map_id j := by rw [← Spec.map_id, ← P.X.presheaf.map_id]; rfl
  map_comp f g := by rw [← Spec.map_comp, ← P.X.presheaf.map_comp]; rfl

def Sys.hen {P : SP d} (S : Sys P) (H : Hens) : S.J ⥤ Scheme.{0} where
  obj j := Spec (H.obj Γ(P.X, (S.V j).1) (P.ι.ker.ideal (S.V j)))
  map f := Spec.map (CommRingCat.ofHom (H.map _ (P.ι.ker.ideal_le_comap_ideal (S.mono f.le))))
  map_id j := by
    have e : (P.X.presheaf.map (homOfLE (le_refl (S.V j).1)).op).hom = RingHom.id Γ(P.X, (S.V j).1) :=
      (congrArg CommRingCat.Hom.hom (P.X.presheaf.map_id (op (S.V j).1))).trans (CommRingCat.hom_id)
    have k : ∀ φ h, φ = RingHom.id _ → H.map (I := P.ι.ker.ideal (S.V j)) (J := P.ι.ker.ideal (S.V j)) φ h = RingHom.id _ := by
      rintro _ h rfl; exact H.map_id _ _ h
    exact (congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (k _ _ e)).trans (Spec.map_id _)
  map_comp {i j k} f g := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← H.map_comp _ _ _ _ (fun x hx =>
      P.ι.ker.ideal_le_comap_ideal (S.mono f.le) (P.ι.ker.ideal_le_comap_ideal (S.mono g.le) hx))]
    congr 3
    rw [← CommRingCat.hom_comp, ← P.X.presheaf.map_comp]; rfl

def Sys.toAff {P : SP d} (S : Sys P) (H : Hens) : S.hen H ⟶ S.aff where
  app j := Spec.map (CommRingCat.ofHom (eta H P (S.V j)))
  naturality j k f := by
    dsimp only [Sys.hen, Sys.aff]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, H.map_η]; rfl

theorem Sys.cocAff {P : SP d} (S : Sys P) : Coc (S.aff ⋙ yoneda) fun j => yoneda.map (S.V j).2.fromSpec := fun j k f =>
  (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map ((S.V k).2.map_fromSpec (S.V j).2 (homOfLE (S.mono f.le)).op))

theorem Sys.cocHen {P : SP d} (S : Sys P) (H : Hens) :
    Coc (S.hen H ⋙ yoneda) fun j => yoneda.map (hensTo H P (S.V j)) := fun j k f =>
  (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (by
    have h := (S.toAff H).naturality f
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (S.V k).2.fromSpec) h).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) ((S.V k).2.map_fromSpec (S.V j).2 (homOfLE (S.mono f.le)).op))))))

abbrev Sys.E {P : SP d} (S : Sys P) (H : Hens) : Spc := hoc (S.hen H ⋙ yoneda)

abbrev Sys.π {P : SP d} (S : Sys P) (H : Hens) : S.E H ⟶ sch.obj P.X := aug _ (S.cocHen H)

def LeafQuot : Prop := ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A), IndNbhd φ I →
  Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)

def LeafZ : Prop := ∀ (X Z : Scheme.{0}) (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) (B : Type) [CommRing B]
  (φ : Γ(X, V.1) →+* B),
  (∃ z, IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((ι.ker.ideal V).map φ)))) z
    (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ι) ∧
  ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ →
    off B ((ι.ker.ideal V).map φ) = (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ U

def LeafAbv : Prop := ∀ (Y X : Scheme.{0}) (w : Y ⟶ X) (U' : Y.Opens) (U : X.Opens) (h : U' = w ⁻¹ᵁ U),
  ∃ e : opn U' ≅ abv U (sch.map w), e.hom.right = 𝟙 (sch.obj Y) ∧ e.hom ≫ abvMap U (sch.map w) = opnMap w U' U h.le

def LeafLocFst : Prop := E1 → ∀ (H : Hens) (d : ℕ) (P : SP d) (V : P.X.affineOpens) (q : ℕ), IsUnit (q : Γ(P.X, ⊤)) → ∀ i,
  Eqv _ (pullback.fst (sch.map (hensTo H P V)) (sch.map P.ι)) (tw q i)

def LeafLocIso : Prop := ∀ (H : Hens) (d : ℕ) (P : SP d) (V : P.X.affineOpens) h,
  IsIso (pbRel (sch.map P.ι) (sch.map (Spec.map (CommRingCat.ofHom (eta H P V)))) (sch.map (hensTo H P V))
    (sch.map V.2.fromSpec) h)

def LeafLocHen : Prop := Hyp → ∀ (H : Hens) (d : ℕ) (P : SP d) (V : P.X.affineOpens) (q : ℕ), IsUnit (q : Γ(P.X, ⊤)) →
  (P.ι.ker.ideal V).FG → ∀ h, Exc q (abvRel P.U (sch.map (Spec.map (CommRingCat.ofHom (eta H P V)))) (sch.map (hensTo H P V))
    (sch.map V.2.fromSpec) h)

def LeafPrdAff : Prop := Hyp → ∀ (d q : ℕ) [NeZero q] (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  (ψ : MvPolynomial (Fin d) R →+* B) (η : B →+* C), IsUnit (q : R) →
  Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) → ∀ (I : Ideal B) (K : Ideal C), IndNbhd η I → K = I.map η → HenselianRing C K →
  ∀ (_ : Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) = I) hy (n i : ℤ),
  Function.Bijective fun a : Ht q (sp C) n i =>
    Hs.act q (P := opn (off C K)) a (thom d q C K (fun j => η (ψ (MvPolynomial.X j))) hy)

def LeafPrdRing : Prop := Hyp → ∀ (H : Hens) (d q : ℕ) [NeZero q] (A : Type) [CommRing A] (I : Ideal A), IsUnit (q : A) → I.FG →
  Chart d A I → ∀ c : Hs q (opn (off A I)) (2 * d) d,
  (∀ (B : Type) [CommRing B] (φ : A →+* B) (x : Fin d → B) hx h, φ.Etale →
    Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h) _ _ c = thom d q B (I.map φ) x hx) →
  ∀ h (n i : ℤ), Function.Bijective fun a : Ht q (sp (H.obj A I)) n i =>
    Hs.act q (P := opn (off (H.obj A I) (I.map (H.η A I)))) a
      (Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom (H.η A I))) (off _ (I.map (H.η A I))) (off A I) h) _ _ c)

def LeafLocPrd : Prop := Hyp → ∀ (H : Hens) (d : ℕ) (P : SP d) (V : P.X.affineOpens) (q : ℕ) [NeZero q],
  IsUnit (q : Γ(P.X, ⊤)) → Good P V → Prd q P.U (sch.map (hensTo H P V)) (fcl d q P)

def LeafRefine : Prop := ∀ (hC : LeafChart) (H : Hens) (d : ℕ) (P' P : SP d) (φ : P'.Hom P),
  ∃ (S' : Sys P') (a : S'.E H ⟶ (Sys.all hC P').E H) (b : S'.E H ⟶ (Sys.all hC P).E H),
    a ≫ (Sys.all hC P').π H = S'.π H ∧ b ≫ (Sys.all hC P).π H = S'.π H ≫ sch.map φ.f

theorem hs_pull_comp (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q (φ ≫ ψ) n i x = Hs.pull q φ n i (Hs.pull q ψ n i x) := by
  have e : dbl.map (φ ≫ ψ) = dbl.map φ ≫ dbl.map ψ := by
    exact (pushout.map_comp φ.left ψ.left _ _ _ _ (Arrow.w φ).symm (Arrow.w φ).symm (Arrow.w ψ).symm (Arrow.w ψ).symm).symm
  apply Subtype.ext
  change pull _ (dbl.map (φ ≫ ψ)) _ _ x.1 = pull _ (dbl.map φ) _ _ (pull _ (dbl.map ψ) _ _ x.1)
  rw [e, pull_comp]

theorem exc_comp (q : ℕ) {P'' P' P : Arrow Spc} {φ : P'' ⟶ P'} {ψ : P' ⟶ P} (h : Exc q φ) (h' : Exc q ψ) : Exc q (φ ≫ ψ) :=
  fun n i => by
    have e : ⇑(Hs.pull q (φ ≫ ψ) n i) = Hs.pull q φ n i ∘ Hs.pull q ψ n i := funext (hs_pull_comp q φ ψ n i)
    rw [e]; exact (h n i).comp (h' n i)

theorem eqv_comp {R : Type} [CommRing R] {E'' E' E : Spc} {f : E'' ⟶ E'} {g : E' ⟶ E} {F : Shv R} (h : Eqv R f F)
    (h' : Eqv R g F) : Eqv R (f ≫ g) F := fun n => by
  have e : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext (pull_comp R f g F n)
  rw [e]; exact (h n).comp (h' n)

theorem eqv_iso {R : Type} [CommRing R] {E' E : Spc} (f : E' ⟶ E) [IsIso f] (F : Shv R) : Eqv R f F := fun n =>
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id], fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem abvRel_abvMap {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (a : E' ⟶ E) (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X)
    (h : a ≫ π = π') : abvRel U a π' π h ≫ abvMap U π = abvMap U π' :=
  Arrow.hom_ext _ _ ((pullback.lift_snd _ _ _).trans (Category.comp_id _)) h

theorem goal_of (hH : LeafHens) (hC : LeafChart) (fst : LeafFstHoc) (rel : LeafRelHoc) (exc : LeafExcHoc) (prd : LeafPrdHoc)
    (loc : LeafLoc) (locExc : LeafLocExc) (lf : LeafLocFst) (li : LeafLocIso) (lh : LeafLocHen) (lp : LeafLocPrd)
    (ref : LeafRefine) : LeafTube := by
  intro hyp d
  obtain ⟨H⟩ := hH
  have hyp' := hyp
  obtain ⟨a1, -, a3, -, -, -, -, -, -, -, -, e1⟩ := hyp'
  have ok : ∀ (P : SP d) (S : Sys P) (q : ℕ) [NeZero q], IsUnit (q : Γ(P.X, ⊤)) →
      (∀ i, Eqv _ (pullback.fst (S.π H) (sch.map P.ι)) (tw q i)) ∧ (∀ i, Eqv _ (pullback.snd (S.π H) (sch.map P.ι)) (tw q i)) ∧
      Exc q (abvMap P.U (S.π H)) ∧ Prd q P.U (S.π H) (fcl d q P) := by
    intro P S q _ hq
    have L : Loc (aug _ S.cocAff) := loc S.J S.aff P.X (fun j => (S.V j).2.fromSpec) (fun j => (S.V j).2.isOpenImmersion_fromSpec)
      (fun x => by
        obtain ⟨j, h⟩ := S.cov x
        exact ⟨j, (S.V j).2.range_fromSpec.ge h⟩)
      (fun x j k hj hk => by
        obtain ⟨l, h, h', h''⟩ := S.dir x j k ((S.V j).2.range_fromSpec.le hj) ((S.V k).2.range_fromSpec.le hk)
        exact ⟨l, h, h', (S.V l).2.range_fromSpec.ge h''⟩) S.cocAff
    have hj : ∀ j, (Functor.whiskerRight (S.toAff H) yoneda).app j ≫ yoneda.map (S.V j).2.fromSpec =
        yoneda.map (hensTo H P (S.V j)) := fun j => (yoneda.map_comp _ _).symm
    have hj' := fun j => (disc.map_comp _ _).symm.trans (congrArg disc.map (hj j))
    have hg := map_aug _ _ _ (S.cocHen H) S.cocAff hj
    refine ⟨fun i => fst a3 _ _ _ _ _ _ (yoneda.map P.ι) _ (S.cocHen H) fun j => lf e1 H d P (S.V j) q hq i, fun i => ?_, ?_,
      prd hyp q _ _ _ P.U _ (S.cocHen H) _ _ _ fun j => lp hyp H d P (S.V j) q hq (S.good j)⟩
    · have e : pullback.snd (S.π H) (sch.map P.ι) =
          pbRel (sch.map P.ι) _ _ _ hg ≫ pullback.snd (aug _ S.cocAff) (sch.map P.ι) :=
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm
      rw [e]
      refine eqv_comp (rel a3 _ _ _ _ _ _ _ _ (yoneda.map P.ι) _ _ (S.cocHen H) S.cocAff hj' hg fun j => ?_) fun n => ?_
      · exact @eqv_iso _ _ _ _ _ (li H d P (S.V j) (hj' j)) _
      · exact @a1 _ _ _ _ _ (L _ _ P.ι) _ n
    · rw [← abvRel_abvMap P.U _ _ _ hg]
      exact exc_comp q (exc a3 q _ _ _ _ _ P.U _ _ (S.cocHen H) S.cocAff hj' hg
        fun j => lh hyp H d P (S.V j) q hq (S.good j).1 (hj' j)) (locExc a1 q _ _ _ _ L)
  refine ⟨fun P => ⟨_, (Sys.all hC P).π H, ok P _⟩, fun P' P φ => ?_⟩
  obtain ⟨S', a, b, ha, hb⟩ := ref hC H d P' P φ
  exact ⟨⟨_, S'.π H, ok P' S'⟩, a, b, ha, hb⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafExcSheafCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def LeafFreeCok : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B'.obj (op T)) (x : A.obj (op T)), i.app (op T) x = b.app (op T) y →
    ∃ x' : A'.obj (op T), i'.app (op T) x' = y) →
  (∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y) →
  (∀ (T : Scheme.{0}) (y₁ y₂ : B'.obj (op T)), b.app (op T) y₁ = b.app (op T) y₂ →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      B'.map g.op y₁ = B'.map g.op y₂ ∨ ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op y₁)) →
  IsIso (cokernel.map ((free R).map i') ((free R).map i) ((free R).map a) ((free R).map b)
    (by rw [← Functor.map_comp, ← Functor.map_comp, w]))

def LeafSurjGeo : Prop := ∀ {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X') (ι : Z ⟶ X)
  [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U : X.Opens), (U : Set X) = (Set.range ι)ᶜ →
  ∀ {T : Scheme.{0}} (t : T ⟶ X), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : V ⟶ U.toScheme, x ≫ U.ι = g ≫ t) ∨ ∃ y : V ⟶ X', y ≫ f = g ≫ t

def LeafInjGeo : Prop := ∀ {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X') (ι : Z ⟶ X)
  [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U : X.Opens), (U : Set X) = (Set.range ι)ᶜ →
  ∀ {T : Scheme.{0}} (y₁ y₂ : T ⟶ X'), y₁ ≫ f = y₂ ≫ f →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      g ≫ y₁ = g ≫ y₂ ∨ ∃ x : V ⟶ U.toScheme, x ≫ U.ι = (g ≫ y₁) ≫ f

theorem excSheaf_cart_preimage {X' X T : Scheme.{0}} (f : X' ⟶ X) (U : X.Opens) (y : T ⟶ X') (x : T ⟶ U.toScheme)
    (hx : x ≫ U.ι = y ≫ f) : ∃ x' : T ⟶ (f ⁻¹ᵁ U).toScheme, x' ≫ (f ⁻¹ᵁ U).ι = y :=
  ⟨(isPullback_morphismRestrict f U).lift x y hx, (isPullback_morphismRestrict f U).lift_snd _ _ _⟩

theorem LeafExcSheaf_of (hF : LeafFreeCok) (hS : LeafSurjGeo) (hI : LeafInjGeo) : LeafExcSheaf := by
  intro R _ X' X Z f _ ι' ι _ hp U' U hU h
  subst h
  exact hF R (yoneda.map (f ⁻¹ᵁ U).ι) (yoneda.map U.ι) (yoneda.map (f.resLE U (f ⁻¹ᵁ U) le_rfl)) (yoneda.map f)
    (by rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι])
    (fun T y x hx => excSheaf_cart_preimage f U y x hx) (fun T y => hS f ι' ι hp U hU y)
    (fun T y₁ y₂ h => hI f ι' ι hp U hU y₁ y₂ h)

end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafExcFormalPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

theorem chainsInrSq (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) :
    (chains (ZMod q)).map (dbl.inr P') ≫ (chains (ZMod q)).map (dbl.map φ) =
      (chains (ZMod q)).map φ.right ≫ (chains (ZMod q)).map (dbl.inr P) := by
  rw [← Functor.map_comp, ← Functor.map_comp, dbl.inr_map]

abbrev cokC (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) :=
  cokernel.map ((chains (ZMod q)).map (dbl.inr P')) ((chains (ZMod q)).map (dbl.inr P))
    ((chains (ZMod q)).map φ.right) ((chains (ZMod q)).map (dbl.map φ)) (chainsInrSq q φ)

theorem HK.pull_comp' (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  rcases x.mk_surjective with ⟨z, rfl⟩
  simp only [HK.pull, HK.pre, cpre_mk]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem HK.pull_id' (R : Type) [CommRing R] (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) :
    HK.pull R (𝟙 K) F n x = x := by
  rcases x.mk_surjective with ⟨z, rfl⟩
  simp only [HK.pull, HK.pre, cpre_mk]
  congr 1
  ext1
  simp [zcomp]

theorem HK.pull_bij (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [IsIso f] (F : Shv R) (n : ℤ) :
    Function.Bijective (HK.pull R f F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨HK.pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← HK.pull_comp', IsIso.inv_hom_id, HK.pull_id']
  · rw [← HK.pull_comp', IsIso.hom_inv_id, HK.pull_id']

def LeafExcIdent : Prop := ∀ (q : ℕ) (n i : ℤ), ∃ e : ∀ P : Arrow Spc,
    HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n ≃+ Hs q P n i,
  ∀ {P' P : Arrow Spc} (φ : P' ⟶ P) (x : HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n),
    Hs.pull q φ n i (e P x) = e P' (HK.pull (ZMod q) (cokC q φ) (tw q i) n x)

def LeafExcCx : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsIso (cokC q φ) → Exc q φ

theorem LeafExcCx_of (hI : LeafExcIdent) : LeafExcCx := by
  intro q P' P φ hφ n i
  obtain ⟨e, he⟩ := hI q n i
  have hfun : ⇑(Hs.pull q φ n i) = ⇑(e P') ∘ ⇑(HK.pull (ZMod q) (cokC q φ) (tw q i) n) ∘ ⇑(e P).symm := by
    funext y
    obtain ⟨x, rfl⟩ := (e P).surjective y
    simp [he]
  rw [hfun]
  exact (e P').bijective.comp ((HK.pull_bij _ _ _ _).comp (e P).symm.bijective)

def LeafExcDeg : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P),
  (∀ p : SimplexCategoryᵒᵖ, IsIso (cokernel.map ((free (ZMod q)).map (P'.hom.app p)) ((free (ZMod q)).map (P.hom.app p))
    ((free (ZMod q)).map (φ.left.app p)) ((free (ZMod q)).map (φ.right.app p)) (freeSq _ φ p))) → IsIso (cokC q φ)

theorem LeafExcFormal_of (hI : LeafExcIdent) (hD : LeafExcDeg) : LeafExcFormal := by
  intro q P' P φ h
  exact LeafExcCx_of hI q φ (hD q φ h)

end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafFlqPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

abbrev ZN {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) (W : X.Opens) :
    AddSubgroup (Sec (K.X n) W.toScheme) := Zc K (W.ι ⁻¹ᵁ U) n

def BN {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) (W : X.Opens) :
    AddSubgroup (Sec (K.X n) W.toScheme) := AddSubgroup.closure {a | Bd K (W.ι ⁻¹ᵁ U) n a}

abbrev OK {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (N : ∀ W : X.Opens, AddSubgroup (Sec G W.toScheme)) : Prop :=
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ N W, rs h a ∈ N V) ∧
  (∀ (W : X.Opens) (a : Sec G W.toScheme), (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ rs h a ∈ N V) → a ∈ N W) ∧
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ N V, ∃ b ∈ N W, rs h b = a)

def LeafBdAdd : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ) (W : X.Opens)
  (a : Sec (K.X n) W.toScheme), a ∈ BN K U n W → Bd K (W.ι ⁻¹ᵁ U) n a

def LeafBZ : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ) (W : X.Opens)
  (a : Sec (K.X n) W.toScheme), Bd K (W.ι ⁻¹ᵁ U) n a → a ∈ ZN K U n W

def LeafZloc : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ),
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ ZN K U n W, rs h a ∈ ZN K U n V) ∧
  (∀ (W : X.Opens) (a : Sec (K.X n) W.toScheme), (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ rs h a ∈ ZN K U n V) →
    a ∈ ZN K U n W)

def LeafZero : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ),
  IsZero (K.X n) → OK (ZN K U n)

def LeafStep : Prop := ∀ (R : Type) [CommRing R] (K : Cx R), LateralTheory.CohomologicalPurity.Cl.LeafZorn → (∀ s, Injective (K.X s)) →
  ∀ (X : Scheme.{0}) (U : X.Opens) (n : ℤ), OK (ZN K U (n - 1)) → OK (BN K U n)

def LeafTop : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ)
  (c' : Sec (K.X n) (⊤ : X.Opens).toScheme), c' ∈ ZN K U n ⊤ →
  ∃ c ∈ Zc K U n, ∀ V : X.Opens, Sec.res V.ι c = rs le_top c'

def LeafRs : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) (X : Scheme.{0}) (T V W : X.Opens) (h : V ≤ W) (h' : T ≤ V)
  (a b : Sec G W.toScheme), rs h (a - b) = rs h a - rs h b ∧ rs h' (rs h a) = rs (h'.trans h) a

theorem LeafRs_of : LeafRs := by
  intro R _ G X T V W h h' a b
  refine ⟨?_, ?_⟩
  · show ((G.obj.map (X.homOfLE h).op).hom (a - b)) = _
    exact map_sub _ a b
  · show ((G.obj.map (X.homOfLE h').op).hom ((G.obj.map (X.homOfLE h).op).hom a)) = (G.obj.map (X.homOfLE (h'.trans h)).op).hom a
    have e : X.homOfLE (h'.trans h) = X.homOfLE h' ≫ X.homOfLE h := (Scheme.homOfLE_homOfLE X h' h).symm
    rw [e, op_comp, Functor.map_comp]
    rfl

theorem LeafFlq_of (hZ : LateralTheory.CohomologicalPurity.Cl.LeafZorn) (hA : LeafBdAdd) (hBZ : LeafBZ) (hL : LeafZloc) (h0 : LeafZero)
    (hS : LeafStep) (hT : LeafTop) : LateralTheory.CohomologicalPurity.Cl.LeafFlq := by
  intro R _ K hinj hneg X U m H
  have hR := LeafRs_of
  have key : ∀ n, n < m → OK (ZN K U (n - 1)) → OK (ZN K U n) := by
    intro n hn hprev
    have hB := hS R K hZ hinj X U n hprev
    have eq : ZN K U n = BN K U n := by
      funext W; ext a; constructor
      · intro ha; apply hB.2.1 W a; intro x hx
        obtain ⟨V, h, hxV, hb⟩ := H n hn W a ha x hx
        exact ⟨V, h, hxV, AddSubgroup.subset_closure hb⟩
      · intro ha; exact hBZ R K X U n W a (hA R K X U n W a ha)
    rw [eq]; exact hB
  have P : ∀ k : ℕ, (k : ℤ) < m → OK (ZN K U (k : ℤ)) := by
    intro k
    induction k with
    | zero => intro h; exact key _ h (h0 R K X U _ (hneg _ (by norm_num)))
    | succ k ih =>
      intro h
      apply key _ h
      have e : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [e]; exact ih (by omega)
  have hm : OK (ZN K U (m - 1)) := by
    by_cases hc : m - 1 < 0
    · exact h0 R K X U _ (hneg _ hc)
    · have e : ((m - 1).toNat : ℤ) = m - 1 := Int.toNat_of_nonneg (by omega)
      have := P (m - 1).toNat (by omega)
      rw [e] at this; exact this
  have hBm := hS R K hZ hinj X U m hm
  refine ⟨fun W a hloc => hA R K X U m W a (hBm.2.1 W a fun x hx => ?_), ?_⟩
  · obtain ⟨V, h, hxV, hb⟩ := hloc x hx
    exact ⟨V, h, hxV, AddSubgroup.subset_closure hb⟩
  intro A V a ha hcov hagree
  obtain ⟨c', hc'⟩ := hZ R (K.X m) X (BN K U m) hBm.1 hBm.2.1 hBm.2.2 ⊤ A V (fun _ => le_top) a
    (fun x _ => hcov x) (by
      intro k l
      apply hBm.2.1
      intro x hx
      obtain ⟨hxk, hxl⟩ := hx
      obtain ⟨T, hk, hl, hxT, hb⟩ := hagree k l x hxk hxl
      refine ⟨T, le_inf hk hl, hxT, ?_⟩
      have e : rs (le_inf hk hl) (rs (inf_le_left : V k ⊓ V l ≤ V k) (a k) - rs (inf_le_right : V k ⊓ V l ≤ V l) (a l))
          = rs hk (a k) - rs hl (a l) := by
        have rsub : ∀ {V W : X.Opens} (h : V ≤ W) (x y : Sec (K.X m) W.toScheme), rs h (x - y) = rs h x - rs h y :=
          fun {V W} h x y => (hR R _ X V V W h le_rfl x y).1
        have rrs : ∀ {T V W : X.Opens} (h : V ≤ W) (h' : T ≤ V) (x : Sec (K.X m) W.toScheme),
            rs h' (rs h x) = rs (h'.trans h) x := fun {T V W} h h' x => (hR R _ X T V W h h' x x).2
        rw [rsub, rrs, rrs]
      rw [e]; exact AddSubgroup.subset_closure hb)
  have hmem : c' ∈ ZN K U m ⊤ := by
    apply (hL R K X U m).2 ⊤ c'
    intro x _
    obtain ⟨k, hk⟩ := hcov x
    refine ⟨V k, le_top, hk, ?_⟩
    have h1 := hBZ R K X U m (V k) _ (hA R K X U m (V k) _ (hc' k))
    have h2 : a k ∈ ZN K U m (V k) := ha k
    simpa using add_mem h1 h2
  obtain ⟨c, hc, hcV⟩ := hT R K X U m c' hmem
  refine ⟨c, hc, fun k => ?_⟩
  rw [hcV]; exact hA R K X U m (V k) _ (hc' k)

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafHtpyPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafHtpyZero : Prop := A1 → ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A]
  (h : off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A ⊥) (i : ℤ),
    Eqv _ (sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)) (tw q i)

def LeafHtpyOne : Prop := A1 → C4 → ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (x : A), IsUnit (q : A) →
  ∀ (h : off (Polynomial A) ((Ideal.span {x}).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A (Ideal.span {x})) (i : ℤ),
    Eqv _ (sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)) (tw q i)

def LeafHtpyMV : Prop := A4 → ∀ (R : Type) [CommRing R] (F : Shv R) {X' X : Scheme.{0}} (p : X' ⟶ X)
  (U V : X.Opens) (U' V' : X'.Opens) (hU : U' ≤ p ⁻¹ᵁ U) (hV : V' ≤ p ⁻¹ᵁ V) (hI : U' ⊓ V' ≤ p ⁻¹ᵁ (U ⊓ V))
  (hS : U' ⊔ V' ≤ p ⁻¹ᵁ (U ⊔ V)),
  Eqv R (sch.map (p.resLE U U' hU)) F → Eqv R (sch.map (p.resLE V V' hV)) F →
  Eqv R (sch.map (p.resLE (U ⊓ V) (U' ⊓ V') hI)) F → Eqv R (sch.map (p.resLE (U ⊔ V) (U' ⊔ V') hS)) F

namespace HtpyPf

theorem offle (A : Type) [CommRing A] (I : Ideal A) : off (Polynomial A) (I.map Polynomial.C) ≤
    Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I := by
  intro p hp hz
  apply hp
  change ((I.map Polynomial.C : Ideal (Polynomial A)) : Set (Polynomial A)) ⊆ p.asIdeal
  change (I : Set A) ⊆ (PrimeSpectrum.comap Polynomial.C p).asIdeal at hz
  exact SetLike.coe_subset_coe.2 (Ideal.map_le_iff_le_comap.2 hz)

theorem eqv_congr {X' X : Scheme.{0}} (p : X' ⟶ X) {R : Type} [CommRing R] (F : Shv R) {U U₁ : X.Opens}
    {U' U₁' : X'.Opens} (e : U = U₁) (e' : U' = U₁') (h : U' ≤ p ⁻¹ᵁ U) (h₁ : U₁' ≤ p ⁻¹ᵁ U₁) :
    Eqv R (sch.map (p.resLE U U' h)) F ↔ Eqv R (sch.map (p.resLE U₁ U₁' h₁)) F := by
  subst e e'; rfl

theorem off_sup (A : Type) [CommRing A] (I J : Ideal A) : off A (I ⊔ J) = off A I ⊔ off A J := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A))ᶜ =
    (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ∪ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ
  rw [PrimeSpectrum.zeroLocus_sup, Set.compl_inter]

theorem off_mul (A : Type) [CommRing A] (I J : Ideal A) : off A (I * J) = off A I ⊓ off A J := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((I * J : Ideal A) : Set A))ᶜ =
    (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ∩ (PrimeSpectrum.zeroLocus (J : Set A))ᶜ
  rw [PrimeSpectrum.zeroLocus_mul, Set.compl_union]

end HtpyPf

namespace HtpyPf

theorem span_cons {A : Type} [CommRing A] (x : A) (t : List A) :
    Ideal.span {a | a ∈ x :: t} = Ideal.span {x} ⊔ Ideal.span {a | a ∈ t} := by
  rw [← Ideal.span_insert]; congr 1; ext a; simp

theorem span_mul {A : Type} [CommRing A] (x : A) (t : List A) :
    Ideal.span {x} * Ideal.span {a | a ∈ t} = Ideal.span {a | a ∈ t.map (x * ·)} := by
  rw [Ideal.span_mul_span']; congr 1; ext a; simp [Set.singleton_mul]

theorem main (hZ : LeafHtpyZero) (hO : LeafHtpyOne) (hMV : LeafHtpyMV) (a1 : A1) (a4 : A4) (c4 : C4)
    (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hq : IsUnit (q : A)) (i : ℤ) :
    ∀ (n : ℕ) (s : List A), s.length = n →
    ∀ h : off (Polynomial A) ((Ideal.span {a | a ∈ s}).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A (Ideal.span {a | a ∈ s}),
    Eqv _ (sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)) (tw q i) := by
  intro n
  induction n with
  | zero =>
    intro s hs h
    obtain rfl : s = [] := List.length_eq_zero_iff.1 hs
    have e : Ideal.span {a | a ∈ ([] : List A)} = ⊥ := by simp
    have e1 : off A (Ideal.span {a | a ∈ ([] : List A)}) = off A ⊥ := by rw [e]
    have e2 : off (Polynomial A) ((Ideal.span {a | a ∈ ([] : List A)}).map Polynomial.C) =
        off (Polynomial A) ((⊥ : Ideal A).map Polynomial.C) := by rw [e]
    exact (eqv_congr (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (tw q i) e1 e2 h
      (offle A ⊥)).2 (hZ a1 q A (offle A ⊥) i)
  | succ n ih =>
    intro s hs h
    obtain ⟨x, t, rfl⟩ : ∃ x t, s = x :: t := by
      cases s with
      | nil => simp at hs
      | cons x t => exact ⟨x, t, rfl⟩
    have ht : t.length = n := by simpa using hs
    set I := Ideal.span ({x} : Set A)
    set J := Ideal.span {a | a ∈ t}
    set P := Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))
    have hU := offle A I
    have hV := offle A J
    have hI : off (Polynomial A) (I.map Polynomial.C) ⊓ off (Polynomial A) (J.map Polynomial.C) ≤
        P ⁻¹ᵁ (off A I ⊓ off A J) := fun p hp => ⟨hU hp.1, hV hp.2⟩
    have hS : off (Polynomial A) (I.map Polynomial.C) ⊔ off (Polynomial A) (J.map Polynomial.C) ≤
        P ⁻¹ᵁ (off A I ⊔ off A J) := by
      rw [← off_sup, ← off_sup, ← Ideal.map_sup]; exact offle A (I ⊔ J)
    have e1 : off A (Ideal.span {a | a ∈ x :: t}) = off A I ⊔ off A J := by rw [span_cons, off_sup]
    have e2 : off (Polynomial A) ((Ideal.span {a | a ∈ x :: t}).map Polynomial.C) =
        off (Polynomial A) (I.map Polynomial.C) ⊔ off (Polynomial A) (J.map Polynomial.C) := by
      rw [span_cons, Ideal.map_sup, off_sup]
    refine (eqv_congr P (tw q i) e1 e2 h hS).2 (hMV a4 _ _ P _ _ _ _ hU hV hI hS (hO a1 c4 q A x hq hU i) (ih t ht hV) ?_)
    have e3 : off A (Ideal.span {a | a ∈ t.map (x * ·)}) = off A I ⊓ off A J := by rw [← span_mul, off_mul]
    have e4 : off (Polynomial A) ((Ideal.span {a | a ∈ t.map (x * ·)}).map Polynomial.C) =
        off (Polynomial A) (I.map Polynomial.C) ⊓ off (Polynomial A) (J.map Polynomial.C) := by
      rw [← span_mul, Ideal.map_mul, off_mul]
    exact (eqv_congr P (tw q i) e3 e4 (offle A _) hI).1 (ih _ (by simpa using ht) _)

end HtpyPf

theorem LeafHtpy_of (hZ : LeafHtpyZero) (hO : LeafHtpyOne) (hMV : LeafHtpyMV) : LeafHtpy := by
  intro a1 a4 c4 q _ A _ I hI hq h i
  obtain ⟨S, rfl⟩ := hI
  have e : ({a | a ∈ S.toList} : Set A) = (S : Set A) := by ext a; simp
  have := HtpyPf.main hZ hO hMV a1 a4 c4 q A hq i _ S.toList rfl (by rw [e]; exact HtpyPf.offle A _)
  exact (HtpyPf.eqv_congr (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (tw q i)
    (by rw [e]) (by rw [e]) _ h).1 this

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafGoodPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd

theorem pb_v {R : Type} [CommRing R] {A B I : Cx R} (f : A ⟶ B) {n : ℤ} (c : Cochain B I n) (p q : ℤ) (hpq : p + n = q) :
    (pb f c).v p q hpq = f.f p ≫ c.v p q hpq := by
  simp [pb, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]

theorem LeafGood_of : LeafGood := by
  intro R _ A B D i l r I hm hp hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply HomologicalComplex.hom_ext
    intro p
    simpa using (hp p).w
  · intro n a
    refine ⟨Cochain.mk (fun p q hpq => Injective.factorThru (a.v p q hpq) (i.f p)), ?_⟩
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [pb_v]
    simp [Cochain.mk_v]
  · intro n c c' h
    refine ⟨Cochain.mk (fun p q hpq => (hp p).desc (c.v p q hpq) (c'.v p q hpq) (by
      have := congrArg (fun x => x.v p q hpq) h
      simpa only [pb_v] using this)), ?_, ?_⟩
    · refine Cochain.ext _ _ (fun p q hpq => ?_); rw [pb_v]; simp [Cochain.mk_v]
    · refine Cochain.ext _ _ (fun p q hpq => ?_); rw [pb_v]; simp [Cochain.mk_v]
  · intro n b b' h1 h2
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    apply (hp p).hom_ext
    · have := congrArg (fun x => x.v p q hpq) h1
      simpa only [pb_v] using this
    · have := congrArg (fun x => x.v p q hpq) h2
      simpa only [pb_v] using this

end LateralTheory.CohomologicalPurity.Bd
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafMonoPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

theorem mono_freeP (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q) [Mono g] : Mono ((freeP R).map g) := by
  have : ∀ U, Mono (((freeP R).map g).app U) := by
    intro U
    have hg : Function.Injective (g.app U) := (mono_iff_injective _).1 inferInstance
    rw [ModuleCat.mono_iff_injective]
    dsimp [freeP]
    exact Finsupp.mapDomain_injective (fun a b h => ULift.ext (hg (congrArg ULift.down h)))
  exact NatTrans.mono_of_mono_app _

theorem mono_free (R : Type) [CommRing R] {P Q : PSh} (g : P ⟶ Q) [Mono g] : Mono ((free R).map g) := by
  have := mono_freeP R g
  dsimp [free]
  infer_instance

theorem LeafMono_of : LeafMono := by
  intro R _ U E f hf p
  have hk : ∀ k : ℕ, Mono (((chainsN R).map f).f k) := by
    intro k
    have : Mono (f.app (op (SimplexCategory.mk k))) := inferInstance
    have := mono_free R (f.app (op (SimplexCategory.mk k)))
    simp only [chainsN, Functor.comp_map, AlgebraicTopology.alternatingFaceMapComplex_map_f]
    exact this
  by_cases h : ∃ k : ℕ, -(k : ℤ) = p
  · obtain ⟨k, rfl⟩ := h
    have e := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := k) (i' := -(k:ℤ)) rfl
    change Mono (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat |>.f _)
    rw [e]
    have := hk k
    infer_instance
  · have hz : IsZero (((chains R).obj U).X p) := by
      apply HomologicalComplex.isZero_extend_X
      intro k hk; exact h ⟨k, hk⟩
    exact hz.mono _
end LateralTheory.CohomologicalPurity.Bd
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafImgHomPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (a : F ⟶ G) (b : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

theorem sec_map_add {R : Type} [CommRing R] {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a + b) x = Sec.map a x + Sec.map b x := rfl

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← a.hom.naturality]

theorem LeafImgHom_of (hG : LeafGen) : LeafImgHom := by
  intro S R _ _ I J ρ
  have ex : ∀ (P : PSh) (s : ℤ) (φ : (free S).obj P ⟶ I.X s), ∃ ψ : (free R).obj P ⟶ J.X s,
      ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map ψ (freeGen R P U x) = ρ.app U s (Sec.map φ (freeGen S P U x)) := by
    intro P s φ
    refine (hG R P).2.2.2 (J.X s) (fun U x => ρ.app U s (Sec.map φ (freeGen S P U x))) ?_
    intro V U g x
    rw [ρ.nat, sec_map_res, (hG S P).1]
  choose T hT using ex
  have ext : ∀ (P : PSh) (s : ℤ) (ψ ψ' : (free R).obj P ⟶ J.X s),
      (∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map ψ (freeGen R P U x) = Sec.map ψ' (freeGen R P U x)) → ψ = ψ' :=
    fun P s ψ ψ' h => (hG R P).2.2.1 _ ψ ψ' h
  refine ⟨fun P s => { toFun := T P s, map_zero' := ?_, map_add' := ?_ }, ?_, ?_, ?_⟩
  · apply ext; intro U x
    rw [hT]; show ρ.app U s 0 = 0; exact map_zero _
  · intro φ ψ; apply ext; intro U x
    rw [sec_map_add, hT, hT, hT, sec_map_add, map_add (f := _)]
  · intro P s φ U x; exact hT P s φ U x
  · intro P s t φ; apply ext; intro U x
    show Sec.map (T P t (φ ≫ I.d s t)) _ = Sec.map (T P s φ ≫ J.d s t) _
    rw [hT, sec_map_comp, sec_map_comp, hT, ρ.comm]
  · intro P P' f s φ; apply ext; intro U x
    show Sec.map (T P s ((free S).map f ≫ φ)) _ = Sec.map ((free R).map f ≫ T P' s φ) _
    rw [hT, sec_map_comp, sec_map_comp, (hG S P).2.1, (hG R P).2.1, hT]

end LateralTheory.CohomologicalPurity.Bd
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.PresSheafify
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd.PushPf

variable (R : Type) [CommRing R]

instance pres_ulift : PreservesColimitsOfShape WalkingSpan uliftFunctor.{1, 0} := inferInstance

instance pres_freeMod : PreservesColimitsOfShape WalkingSpan (ModuleCat.free.{1} (ULift.{1} R)) :=
  (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape

instance pres_freeP : PreservesColimitsOfShape WalkingSpan (freeP R) := by
  unfold freeP; infer_instance

instance pres_sheafify : PreservesColimitsOfShape WalkingSpan
    (presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))) := inferInstance

instance pres_free : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free; infer_instance

instance pres_eval (k : ℕ) : PreservesColimitsOfShape WalkingSpan
    ((evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk k))) := inferInstance

def isoN (k : ℕ) : chainsN R ⋙ HomologicalComplex.eval _ _ k ≅
    (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk k)) ⋙ free R :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

instance pres_N (k : ℕ) : PreservesColimitsOfShape WalkingSpan (chainsN R ⋙ HomologicalComplex.eval _ _ k) :=
  preservesColimitsOfShape_of_natIso (isoN R k).symm

theorem hk (k : ℕ) : ComplexShape.embeddingDownNat.f k = -(k : ℤ) := by simp

def isoC (k : ℕ) : chains R ⋙ HomologicalComplex.eval _ _ (-(k : ℤ)) ≅ chainsN R ⋙ HomologicalComplex.eval _ _ k :=
  NatIso.ofComponents (fun X => HomologicalComplex.extendXIso _ _ (hk k))
    (by
      intro X Y f
      change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(k : ℤ)) ≫ _ =
        _ ≫ ((chainsN R).map f).f k
      rw [HomologicalComplex.extendMap_f _ _ (hk k)]
      simp)

theorem pres (p : ℤ) : PreservesColimitsOfShape WalkingSpan (chains R ⋙ HomologicalComplex.eval _ _ p) := by
  by_cases hp : ∃ k : ℕ, ComplexShape.embeddingDownNat.f k = p
  · obtain ⟨k, rfl⟩ := hp
    have := pres_N R k
    exact preservesColimitsOfShape_of_natIso (isoC R k).symm
  · push Not at hp
    apply Functor.preservesColimitsOfShape_of_isZero
    rw [Functor.isZero_iff]
    intro X
    exact HomologicalComplex.isZero_extend_X _ _ _ hp

end LateralTheory.CohomologicalPurity.Bd.PushPf

open LateralTheory.CohomologicalPurity.Bd.PushPf in
theorem LateralTheory.CohomologicalPurity.Bd.LeafPush_of : LateralTheory.CohomologicalPurity.Bd.LeafPush := by
  intro R _ U E E' D f g l r h p
  have := pres R p
  exact (chains R ⋙ HomologicalComplex.eval _ _ p).map_isPushout h
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPBPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafPBInvSp : Prop := ∀ (q : ℕ) (R : Type) [CommRing R], IsUnit (q : R) → Inv q (sp R)

def LeafPBCmp : Prop := A1 → ∀ (q : ℕ) [NeZero q] (N : ℕ) (R : Type) [CommRing R], IsUnit (q : R) →
  ∃ (V : sp R ⟶ ofCat (glCat N)) (e : pullback V (PGL.pr N) ⟶ PR N 0 R),
    e ≫ prod.snd = pullback.fst V (PGL.pr N) ∧
    e ≫ prod.fst ≫ Pj.line N 0 = pullback.snd V (PGL.pr N) ≫ PGL.line N ∧
    ∀ i : ℤ, Eqv _ e (tw q i)

def LeafAffEqv : Prop := A1 → ∀ (q : ℕ) [NeZero q] {E E' : Spc} (e : E ⟶ E'),
  (∀ (n : ℕ) (A : Type) [CommRing A], Function.Bijective
    (fun x : Sx E n (Spec (CommRingCat.of A)) => (e.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x)) →
  ∀ i : ℤ, Eqv _ e (tw q i)

def LeafPBMap : Prop := ∀ (N : ℕ) (R : Type) [CommRing R],
  ∃ (V : sp R ⟶ ofCat (glCat N)) (e : pullback V (PGL.pr N) ⟶ PR N 0 R),
    e ≫ prod.snd = pullback.fst V (PGL.pr N) ∧
    e ≫ prod.fst ≫ Pj.line N 0 = pullback.snd V (PGL.pr N) ≫ PGL.line N ∧
    ∀ (n : ℕ) (A : Type) [CommRing A], Function.Bijective
      (fun x : Sx (pullback V (PGL.pr N)) n (Spec (CommRingCat.of A)) =>
        (e.app (op (SimplexCategory.mk n))).app (op (Spec (CommRingCat.of A))) x)

theorem leafPBCmp_of (hMap : LeafPBMap) (hAff : LeafAffEqv) : LeafPBCmp := by
  intro hA1 q _ N R _ _
  obtain ⟨V, e, h1, h2, h3⟩ := hMap N R
  exact ⟨V, e, h1, h2, hAff hA1 q e h3⟩

theorem leafPBInvSp : LeafPBInvSp := by
  intro q R _ hq U ⟨x⟩
  have f : U ⟶ Spec (CommRingCat.of R) := x
  have h1 := hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have h2 := h1.map f.appTop.hom
  simpa using h2

theorem pull_cast' {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (Ht.cast hn hi x) = Ht.cast (E := E) hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem pull_cpow' (hA : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hE : Inv q E')
    (x : Ht q E' 2 1) (k : ℕ) : pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast', (hA q).2.1 f hE]
  | succ k ih =>
    show pull _ f _ _ ((cup q (cpow q x k) x).cast (by push_cast; ring) (by push_cast; ring)) =
      (cup q (cpow q (pull _ f _ _ x) k) (pull _ f _ _ x)).cast (by push_cast; ring) (by push_cast; ring)
    rw [pull_cast', (hA q).1, ih]

theorem LeafPB_of' (hGeo : LeafGeo) (hCmp : LeafPBCmp) : LeafPB := by
  have hInv := leafPBInvSp
  intro hA1 hA6 hD1 q _ N R _ hq n i
  obtain ⟨V, e, h1, h2, h3⟩ := hCmp hA1 q N R hq
  have hD := hD1 q V (hInv q R hq) n i
  have hPR : Inv q (PR N 0 R) := hGeo.2.1 q N 0 R hq
  refine (Function.Bijective.of_comp_iff' (h3 i n) _).1 ?_
  convert hD using 1
  funext a
  simp only [Function.comp_apply, poly, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_cast', (hA6 q).1, pull_cpow' hA6 q e hPR, ← pull_comp, h1, hyp, (hA6 q).2.2.1 e _ hPR, h2]

theorem LeafPB_of (hGeo : LeafGeo) (hMap : LeafPBMap) (hAff : LeafAffEqv) : LeafPB :=
  LeafPB_of' hGeo (leafPBCmp_of hMap hAff)

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTailPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem pull_bij_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem eqv_of_iso (R : Type) [CommRing R] {E₁ E₂ E₁' E₂' : Spc} (f : E₁ ⟶ E₂) (g : E₁' ⟶ E₂')
    (e₁ : E₁ ≅ E₁') (e₂ : E₂ ≅ E₂') (w : f ≫ e₂.hom = e₁.hom ≫ g) (F : Shv R) (h : Eqv R g F) : Eqv R f F := by
  have hf : f = e₁.hom ≫ g ≫ e₂.inv := by rw [← Category.assoc, ← w, Category.assoc, e₂.hom_inv_id, Category.comp_id]
  have hE : ∀ {E E' : Spc} (u : E ⟶ E'), Eqv R u F ↔ ∀ n, Function.Bijective (pull R u F n) := fun _ => Iff.rfl
  rw [hE] at h ⊢
  intro n
  have key : pull R f F n = (pull R e₁.hom F n).comp ((pull R g F n).comp (pull R e₂.inv F n)) := by
    ext x; simp only [hf, pull_comp, AddMonoidHom.comp_apply]
  rw [key]
  exact (pull_bij_of_iso R e₁ F n).comp ((h n).comp (pull_bij_of_iso R e₂.symm F n))

def LeafTailRep : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (n : SimplexCategoryᵒᵖ),
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (φ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : disc.obj ((PR (d + 1) 1 R).obj n) ≅ sch.obj (off (Polynomial A) (I.map Polynomial.C)))
      (e₂ : disc.obj ((PR d 0 R).obj n) ≅ sch.obj (off A I)),
      disc.map ((prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R).app n) ≫ e₂.hom =
        e₁.hom ≫ sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

theorem LeafTail_of (hRep : LeafTailRep) (hH : LeafHtpy) : LeafTail := by
  intro hyp q _ d R _ hq i
  obtain ⟨hA1, -, hA3, hA4, -, -, -, -, -, hC4, -, -⟩ := hyp
  apply hA3
  intro n
  obtain ⟨A, _, I, φ, hI, h, e₁, e₂, w⟩ := hRep d R n
  have hqA : IsUnit (q : A) := by simpa using hq.map φ
  exact eqv_of_iso _ _ _ e₁ e₂ w _ (hH hA1 hA4 hC4 q A I hI hqA h i)

end LateralTheory.CohomologicalPurity.Thom
end
end
