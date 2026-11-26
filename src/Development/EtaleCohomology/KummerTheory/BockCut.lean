module

public import Development.EtaleCohomology.KummerTheory.InjSlice
public import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally

@[expose] public section

section -- merged from Development.EtaleCohomology.KummerTheory.BockCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.BockCut

abbrev TZ (q : ℕ) (i : ℤ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q i)

def genZ {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) : Sec (TZ q i) U := twGen i ζ

def IsRed (Q q : ℕ) (i : ℤ) (π : TZ Q i ⟶ TZ q i) : Prop :=
  ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → Sec.map π (genZ i ζ) = genZ i ξ

def DerDict : Prop := ∀ (R : Type) [CommRing R] (K : Cx R),
  letI := HasDerivedCategory.standard (Shv R)
  ∃ e : ∀ (F : Shv R) (n : ℤ), HK R K F n ≃+ (DerivedCategory.Q.obj K ⟶ ((DerivedCategory.singleFunctor (Shv R) 0).obj F)⟦n⟧),
    ∀ {F G : Shv R} (φ : F ⟶ G) (n : ℤ) (x : HK R K F n),
      e G n (HK.post R K φ n x) = e F n x ≫ ((DerivedCategory.singleFunctor (Shv R) 0).map φ)⟦n⟧'

def NatLES : Prop := ∀ (R : Type) [CommRing R] (K : Cx R),
  ∃ d : ∀ (S : ShortComplex (Shv R)), S.ShortExact → ∀ n : ℤ, HK R K S.X₃ n →+ HK R K S.X₁ (n + 1),
    (∀ (S : ShortComplex (Shv R)) (hS : S.ShortExact) (n : ℤ),
      Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
      Function.Exact (HK.post R K S.g n) (d S hS n) ∧
      Function.Exact (d S hS n) (HK.post R K S.f (n + 1))) ∧
    ∀ (S T : ShortComplex (Shv R)) (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℤ) (x : HK R K S.X₃ n),
      HK.post R K φ.τ₁ (n + 1) (d S hS n x) = d T hT n (HK.post R K φ.τ₃ n x)

def ZHom : Prop := ∀ (F G : Shv ℤ) (f : ∀ U : Scheme.{0}, Sec F U →+ Sec G U),
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (a : Sec F U), Sec.res g (f U a) = f V (Sec.res g a)) →
  ∃ φ : F ⟶ G, ∀ (U : Scheme.{0}) (a : Sec F U), Sec.map φ a = f U a

def RedEx : Prop := ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ i : ℤ, ∃ π : TZ Q i ⟶ TZ q i, IsRed Q q i π

def TwExt : Prop := ∀ (Q : ℕ) [NeZero Q] (i : ℤ) (M : Shv ℤ) (φ ψ : TZ Q i ⟶ M),
  (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map φ (genZ i ζ) = Sec.map ψ (genZ i ζ)) → φ = ψ

def RedEpi : Prop := ∀ (l : ℕ) [Fact l.Prime] (c a : ℕ), a ≤ c → ∀ (i : ℤ) (π : TZ (l ^ c) i ⟶ TZ (l ^ a) i),
  IsRed (l ^ c) (l ^ a) i π → Epi π

def RedKer : Prop := ∀ (Q e q : ℕ) [NeZero Q], Q = e * q → ∀ (i : ℤ) (π : TZ Q i ⟶ TZ q i), IsRed Q q i π →
  ∀ (U : Scheme.{0}) (y : Sec (TZ Q i) U), (Sec.map π y = 0 ↔ e • y = 0) ∧
    (Sec.map π y = 0 → Loc U fun V g => ∃ x : Sec (TZ Q i) V, q • x = Sec.res g y)

def TwSES : Prop := ∀ (l : ℕ) [Fact l.Prime] (b a : ℕ) (i : ℤ) (π₁ : TZ (l ^ (b + a)) i ⟶ TZ (l ^ a) i)
  (π₂ : TZ (l ^ (b + a)) i ⟶ TZ (l ^ b) i), IsRed _ _ i π₁ → IsRed _ _ i π₂ →
  ∃ ι : TZ (l ^ a) i ⟶ TZ (l ^ (b + a)) i, π₁ ≫ ι = l ^ b • 𝟙 _ ∧ ∃ w : ι ≫ π₂ = 0, (ShortComplex.mk ι π₂ w).ShortExact

def RestrRes : Prop := ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S),
  ∃ (T : Cx R) (σ : SemiMap (res S F) T) (ε : sgl ((restr φ).obj F) ⟶ T), QuasiIso ε ∧
    (∀ (U : Scheme.{0}) (s : ℤ), Function.Bijective (σ.app U s)) ∧
    ∀ (U : Scheme.{0}) (a : Sec F U), Sec.map (ε.f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) =
      σ.app U 0 (Sec.map (resι S F) a)

def SemiUniq : Prop := ∀ (S : Type) [CommRing S] (F : Shv S) (G : Shv ℤ) (ρ ρ' : SemiMap (res S F) (res ℤ G)),
  (∀ (U : Scheme.{0}) (a : Sec F U), ρ.app U 0 (Sec.map (resι S F) a) = ρ'.app U 0 (Sec.map (resι S F) a)) →
  ∀ (E : Spc) (n : ℤ) (x : H S E F n), ρ.op.app E n x = ρ'.op.app E n x

def RedPost : Prop := ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (i : ℤ) (π : TZ Q i ⟶ TZ q i), IsRed Q q i π →
  ∀ (E : Spc) (n : ℤ) (x : Ht Q E n i),
    restrH (Int.castRingHom (ZMod q)) E (tw q i) n (red Q q E n i x) =
      HK.post ℤ ((chains ℤ).obj E) π n (restrH (Int.castRingHom (ZMod Q)) E (tw Q i) n x)

theorem post_comp (hD : DerDict) {R : Type} [CommRing R] (K : Cx R) {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) (n : ℤ)
    (x : HK R K F n) : HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x) := by
  obtain ⟨e, he⟩ := hD R K
  apply (e M n).injective
  rw [he, he, he, Functor.map_comp, Functor.map_comp, Category.assoc]

theorem post_nsmul (hD : DerDict) {R : Type} [CommRing R] (K : Cx R) {F : Shv R} (c : ℕ) (n : ℤ)
    (x : HK R K F n) : HK.post R K (c • 𝟙 F) n x = c • x := by
  obtain ⟨e, he⟩ := hD R K
  let := HasDerivedCategory.standard (Shv R)
  apply (e F n).injective
  rw [he, Functor.map_nsmul, Functor.map_nsmul, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Preadditive.comp_nsmul, Category.comp_id, map_nsmul]

theorem red_comp (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities) (hE : TwExt) {Q q r : ℕ} [NeZero Q] (h1 : q ∣ Q) (h2 : r ∣ q) {i : ℤ}
    {π₁ : TZ Q i ⟶ TZ q i} {π₂ : TZ q i ⟶ TZ r i} {π₃ : TZ Q i ⟶ TZ r i} (a : IsRed Q q i π₁) (b : IsRed q r i π₂)
    (c : IsRed Q r i π₃) : π₁ ≫ π₂ = π₃ := by
  have : NeZero q := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne Q) h1⟩
  refine hE Q i _ _ _ fun U ζ => ?_
  obtain ⟨ξ, hξ⟩ := (hP Q Γ(U, ⊤)).2.2.2.2.2 q h1 ζ
  obtain ⟨η, hη⟩ := (hP q Γ(U, ⊤)).2.2.2.2.2 r h2 ξ
  have h : η.1 = ζ.1 ^ (Q / r) := by rw [hη, hξ, ← pow_mul, Nat.div_mul_div h1 h2]
  rw [c U ζ η h, ← b U ξ η hη, ← a U ζ ξ hξ]
  rfl

theorem exact_tr {A B C A' B' C' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup A']
    [AddCommGroup B'] [AddCommGroup C'] (ea : A ≃+ A') (eb : B ≃+ B') (ec : C ≃+ C') {f : A → B} {g : B → C}
    {f' : A' → B'} {g' : B' → C'} (hf : ∀ x, eb (f x) = f' (ea x)) (hg : ∀ x, ec (g x) = g' (eb x))
    (h : Function.Exact f' g') : Function.Exact f g := by
  intro y
  rw [← ec.map_eq_zero_iff, hg, h]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨ea.symm x, eb.injective (by rw [hf, ea.apply_symm_apply, hx])⟩
  · rintro ⟨x, rfl⟩
    exact ⟨ea x, (hf x).symm⟩

theorem goal_of (hD : DerDict) (hL : NatLES) (hX : RedEx) (hE : TwExt) (hEpi : RedEpi) (hS : TwSES) (hR : RedPost)
    (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities) : LateralTheory.KummerTheory.Bock := by
  intro _ h8 _ _ l _ b E i _
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hnz : ∀ c : ℕ, NeZero (l ^ c) := fun c => ⟨pow_ne_zero _ hl⟩
  choose π hπ using fun (c a : ℕ) (h : a ≤ c) => hX (l ^ c) (l ^ a) (pow_dvd_pow l h) i
  have hc : ∀ (c a r : ℕ) (h1 : a ≤ c) (h2 : r ≤ a), π c a h1 ≫ π a r h2 = π c r (h2.trans h1) := fun c a r h1 h2 =>
    red_comp hP hE (pow_dvd_pow l h1) (pow_dvd_pow l h2) (hπ _ _ _) (hπ _ _ _) (hπ _ _ _)
  choose ι hι w hw using fun a : ℕ => hS l b a i (π (b + a) a (by omega)) (π (b + a) b (by omega)) (hπ _ _ _) (hπ _ _ _)
  have hsq : ∀ a : ℕ, π (a + 1) a (by omega) ≫ ι a = ι (a + 1) ≫ π (b + (a + 1)) (b + a) (by omega) := fun a => by
    have := hEpi l (b + (a + 1)) (a + 1) (by omega) i _ (hπ _ _ (Nat.le_add_left _ _))
    rw [← cancel_epi (π (b + (a + 1)) (a + 1) (Nat.le_add_left _ _)), ← Category.assoc, ← Category.assoc, hι, hc,
      ← hc (b + (a + 1)) (b + a) a (Nat.le_succ _) (Nat.le_add_left a b), Category.assoc, hι, Preadditive.comp_nsmul,
      Preadditive.nsmul_comp, Category.comp_id, Category.id_comp]
  obtain ⟨d, hd, hnat⟩ := hL ℤ ((chains ℤ).obj E)
  let e : ∀ (c : ℕ) (n : ℤ), Ht (l ^ c) E n i ≃+ HK ℤ ((chains ℤ).obj E) (TZ (l ^ c) i) n := fun c n =>
    AddEquiv.ofBijective (restrH (Int.castRingHom (ZMod (l ^ c))) E (tw (l ^ c) i) n) (h8 ℤ _ _ E _ n)
  have he : ∀ (c a : ℕ) (h : a ≤ c) (n : ℤ) (x : Ht (l ^ c) E n i),
      e a n (red (l ^ c) (l ^ a) E n i x) = HK.post ℤ _ (π c a h) n (e c n x) := fun c a h n x =>
    hR _ _ (pow_dvd_pow l h) i _ (hπ c a h) E n x
  let u : ∀ (a : ℕ) (n : ℤ), Ht (l ^ a) E n i →+ Ht (l ^ (b + a)) E n i := fun a n =>
    ((e (b + a) n).symm.toAddMonoidHom.comp (HK.post ℤ _ (ι a) n)).comp (e a n).toAddMonoidHom
  let δ : ∀ (a : ℕ) (n : ℤ), Ht (l ^ b) E n i →+ Ht (l ^ a) E (n + 1) i := fun a n =>
    ((e a (n + 1)).symm.toAddMonoidHom.comp (d _ (hw a) n)).comp (e b n).toAddMonoidHom
  have hu : ∀ a n x, e (b + a) n (u a n x) = HK.post ℤ _ (ι a) n (e a n x) := fun a n x => (e (b + a) n).apply_symm_apply _
  have hδ : ∀ a n x, e a (n + 1) (δ a n x) = d _ (hw a) n (e b n x) := fun a n x => (e a (n + 1)).apply_symm_apply _
  refine ⟨u, δ, fun a n => ⟨?_, ?_, ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩⟩
  · exact exact_tr _ _ _ (hu a n) (he _ _ (by omega) n) (hd _ (hw a) n).1
  · exact exact_tr _ _ _ (he _ _ (by omega) n) (hδ a n) (hd _ (hw a) n).2.1
  · exact exact_tr _ _ _ (hδ a n) (hu a (n + 1)) (hd _ (hw a) n).2.2
  · apply (e (b + a) n).injective
    rw [hu, he _ _ (by omega), ← post_comp hD, hι, post_nsmul hD, map_nsmul]
  · apply (e a (n + 1)).injective
    let φ : ShortComplex.mk _ _ (w (a + 1)) ⟶ ShortComplex.mk _ _ (w a) :=
      { τ₁ := π (a + 1) a (by omega)
        τ₂ := π (b + (a + 1)) (b + a) (by omega)
        τ₃ := 𝟙 _
        comm₁₂ := hsq a
        comm₂₃ := (hc _ _ _ _ _).trans (Category.comp_id _).symm }
    have h1 := hnat _ _ (hw (a + 1)) (hw a) φ n (e b n x)
    have h2 := post_nsmul hD ((chains ℤ).obj E) 1 n (e b n x)
    rw [one_smul, one_smul] at h2
    rw [he _ _ (by omega), hδ, hδ]
    exact h1.trans (congrArg _ h2)
  · apply (e (b + a) n).injective
    rw [he _ _ (by omega), hu, hu, he _ _ (by omega), ← post_comp hD, ← post_comp hD, hsq]

end LateralTheory.KummerTheory.BockCut
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.ContCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ContCut

def Lim {J : Type} [SmallCategory J] {K : Type 1} [Category.{0} K] (G : K ⥤ AddCommGrpCat.{1}) {D : J ⥤ K} (c : Cocone D) :
    Prop :=
  (∀ x : G.obj c.pt, ∃ (j : J) (y : G.obj (D.obj j)), (G.map (c.ι.app j)).hom y = x) ∧
  ∀ (j : J) (y : G.obj (D.obj j)), (G.map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (G.map (D.map f)).hom y = 0

structure MVSeq {K : Type 1} [Category.{0} K] (X U V W : ℤ → K ⥤ AddCommGrpCat.{1}) where
  f : ∀ n, X n ⟶ U n
  g : ∀ n, X n ⟶ V n
  a : ∀ n, U n ⟶ W n
  b : ∀ n, V n ⟶ W n
  δ : ∀ n, W n ⟶ X (n + 1)
  comm : ∀ n, f n ≫ a n = g n ≫ b n
  exUV : ∀ n k u v, ((a n).app k).hom u = ((b n).app k).hom v → ∃ x, ((f n).app k).hom x = u ∧ ((g n).app k).hom x = v
  exX : ∀ n k x, ((f (n + 1)).app k).hom x = 0 → ((g (n + 1)).app k).hom x = 0 → ∃ w, ((δ n).app k).hom w = x
  exW : ∀ n k w, ((δ n).app k).hom w = 0 ↔ ∃ u v, w = ((a n).app k).hom u - ((b n).app k).hom v

def IsMV {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X) : Prop :=
  IsOpenImmersion f ∧ IsOpenImmersion g ∧ IsPullback a b f g ∧ ∀ x : X, x ∈ Set.range f ∨ x ∈ Set.range g

def Hf {R : Type} [CommRing R] (F : Shv R) (n : ℤ) : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1} where
  obj X := AddCommGrpCat.of (H R (sch.obj X.unop) F n)
  map f := AddCommGrpCat.ofHom (pull R (sch.map f.unop) F n)
  map_id X := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => by
    change pull R (sch.map (𝟙 X.unop)) F n x = x
    rw [CategoryTheory.Functor.map_id, pull_id])
  map_comp f g := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => by
    change pull R (sch.map (g.unop ≫ f.unop)) F n x = pull R _ F n (pull R _ F n x)
    rw [Functor.map_comp, pull_comp])

theorem bcMap_comp {X : Scheme.{0}} {R A B C : CommRingCat.{0}} (p : X ⟶ Spec R) (f : R ⟶ A) (g : R ⟶ B) (k : R ⟶ C)
    (h : A ⟶ B) (h' : B ⟶ C) (e : f ≫ h = g) (e' : g ≫ h' = k) (e'' : f ≫ h ≫ h' = k) :
    bcMap p f k (h ≫ h') e'' = bcMap p g k h' e' ≫ bcMap p f g h e := by
  apply pullback.hom_ext <;> simp [bcMap, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]

def bc {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R) : Under R ⥤ Scheme.{0}ᵒᵖ where
  obj A := op (pullback p (Spec.map A.hom))
  map {A B} h := (bcMap p A.hom B.hom h.right (Under.w h)).op
  map_id A := Quiver.Hom.unop_inj (by apply pullback.hom_ext <;> simp [bcMap])
  map_comp h h' := Quiver.Hom.unop_inj (bcMap_comp p _ _ _ h.right h'.right (Under.w h) (Under.w h') (Under.w (h ≫ h')))

def bcHom {U X : Scheme.{0}} {R A : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R) (e : f ≫ p = r)
    (s : R ⟶ A) : pullback r (Spec.map s) ⟶ pullback p (Spec.map s) :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by rw [Category.comp_id, e]) (by simp)

theorem bcHom_bcMap {U X : Scheme.{0}} {R A B : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R)
    (e : f ≫ p = r) (s : R ⟶ A) (t : R ⟶ B) (h : A ⟶ B) (e' : s ≫ h = t) :
    bcHom f p r e t ≫ bcMap p s t h e' = bcMap r s t h e' ≫ bcHom f p r e s := by
  apply pullback.hom_ext <;> simp [bcMap, bcHom, pullback.map, pullback.lift_fst, pullback.lift_snd,
    pullback.lift_snd_assoc, pullback.lift_fst_assoc]

def bcNat {U X : Scheme.{0}} {R : CommRingCat.{0}} (f : U ⟶ X) (p : X ⟶ Spec R) (r : U ⟶ Spec R) (e : f ≫ p = r) :
    bc p ⟶ bc r where
  app A := (bcHom f p r e A.hom).op
  naturality _ _ h := Quiver.Hom.unop_inj (bcHom_bcMap f p r e _ _ h.right (Under.w h))

def Conn {R : Type} [CommRing R] (F : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (f : U ⟶ X) (g : V ⟶ X) (n : ℤ)
    (w : H R (sch.obj W) F n) (x : H R (sch.obj X) F (n + 1)) : Prop :=
  ∃ (s : Sec ((res R F).X n) U) (z : Sec ((res R F).X (n + 1)) X), IsCls w (Sec.res a s) ∧ IsCls x z ∧
    Sec.res f z = Sec.map ((res R F).d n (n + 1)) s ∧ Sec.res g z = 0

def Five : Prop := ∀ {J : Type} [SmallCategory J] [IsFiltered J] {K : Type 1} [Category.{0} K]
  (X U V W : ℤ → K ⥤ AddCommGrpCat.{1}), Nonempty (MVSeq X U V W) → ∀ {D : J ⥤ K} (c : Cocone D),
  (∀ n, Lim (U n) c) → (∀ n, Lim (V n) c) → (∀ n, Lim (W n) c) → ∀ n, Lim (X n) c

def Ind : Prop := ∀ (R : CommRingCat.{0}) (P : ∀ X : Scheme.{0}, (X ⟶ Spec R) → Prop),
  (∀ (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec R), P X p) →
  (∀ {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X) (p : X ⟶ Spec R), IsMV a b f g →
    P U (f ≫ p) → P V (g ≫ p) → P W (a ≫ f ≫ p) → P X p) →
  ∀ (X : Scheme.{0}) (p : X ⟶ Spec R) [QuasiCompact p] [IsSeparated p], P X p

def BC : Prop := ∀ {R A : CommRingCat.{0}} (s : R ⟶ A) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
  (p : X ⟶ Spec R) (pU : U ⟶ Spec R) (pV : V ⟶ Spec R) (pW : W ⟶ Spec R) (ea : a ≫ pU = pW) (eb : b ≫ pV = pW)
  (ef : f ≫ p = pU) (eg : g ≫ p = pV), IsMV a b f g →
  IsMV (bcHom a pU pW ea s) (bcHom b pV pW eb s) (bcHom f p pU ef s) (bcHom g p pV eg s)

def Glue : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X)
  (g : V ⟶ X), IsMV a b f g →
  (∀ z : Sec G X, Sec.res f z = 0 → Sec.res g z = 0 → z = 0) ∧
  ∀ (s : Sec G U) (t : Sec G V), Sec.res a s = Sec.res b t → ∃ z : Sec G X, Sec.res f z = s ∧ Sec.res g z = t

def Flasque : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) [Injective G] {W U : Scheme.{0}} (a : W ⟶ U) [Mono a],
  Function.Surjective fun s : Sec G U => Sec.res a s

def Delta : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X)
  (g : V ⟶ X), IsMV a b f g → ∀ n : ℤ, ∃ δ : H R (sch.obj W) F n →+ H R (sch.obj X) F (n + 1),
    ∀ w x, Conn F a f g n w x ↔ δ w = x

def Exact : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {W U V X : Scheme.{0}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X)
  (g : V ⟶ X), IsMV a b f g → ∀ n : ℤ,
  (∀ u v, pull R (sch.map a) F n u = pull R (sch.map b) F n v →
    ∃ x, pull R (sch.map f) F n x = u ∧ pull R (sch.map g) F n x = v) ∧
  (∀ x, pull R (sch.map f) F (n + 1) x = 0 → pull R (sch.map g) F (n + 1) x = 0 → ∃ w, Conn F a f g n w x) ∧
  ∀ w, Conn F a f g n w 0 ↔ ∃ u v, w = pull R (sch.map a) F n u - pull R (sch.map b) F n v

def MVnat : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K : Type 1} [Category.{0} K] (X U V W : K ⥤ Scheme.{0}ᵒᵖ)
  (f : X ⟶ U) (g : X ⟶ V) (a : U ⟶ W) (b : V ⟶ W),
  (∀ k, IsMV (a.app k).unop (b.app k).unop (f.app k).unop (g.app k).unop) →
  Nonempty (MVSeq (fun n => X ⋙ Hf F n) (fun n => U ⋙ Hf F n) (fun n => V ⋙ Hf F n) (fun n => W ⋙ Hf F n))

def AffRing : Prop := ∀ {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (p : X ⟶ Spec R),
  ∃ T : Under R ⥤ CommRingCat.{0}, Nonempty (bc p ≅ T ⋙ Scheme.Spec.rightOp) ∧ (∀ A, Nonempty (R ⟶ T.obj A)) ∧
    ∀ {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ Under R} (c : Cocone D),
      IsColimit ((Under.forget R).mapCocone c) → Nonempty (IsColimit (T.mapCocone c))

def Aff : Prop := B1 → ∀ (q : ℕ) {X : Scheme.{0}} [IsAffine X] {R : CommRingCat.{0}} (p : X ⟶ Spec R), IsUnit (q : R) →
  ∀ {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ Under R} (c : Cocone D),
    IsColimit ((Under.forget R).mapCocone c) → ∀ n i : ℤ, Lim (bc p ⋙ Hf (tw q i) n) c

theorem goal_of (h5 : Five) (hI : Ind) (hB : BC) (hM : MVnat) (hA : Aff) : Cont := by
  intro _ b1 q _ X R p _ _ hq J _ _ D c hc u hu v hv n i
  let D' : J ⥤ Under R :=
    { obj := fun j => Under.mk (u j)
      map := fun f => Under.homMk (D.map f) (hu f)
      map_id := fun j => by ext1; exact D.map_id j
      map_comp := fun f g => by ext1; exact D.map_comp f g }
  let c' : Cocone D' :=
    { pt := Under.mk v
      ι := { app := fun j => Under.homMk (c.ι.app j) (hv j)
             naturality := fun j k f => by ext1; exact c.ι.naturality f } }
  have hc' : IsColimit ((Under.forget R).mapCocone c') := hc
  have key : ∀ n, Lim (bc p ⋙ Hf (tw q i) n) c' := by
    refine hI R (fun X p => ∀ n, Lim (bc p ⋙ Hf (tw q i) n) c') (fun X _ p n => hA b1 q p hq c' hc' n i) ?_ X p
    intro W U V X a b f g p h hU hV hW
    have eb : b ≫ g ≫ p = a ≫ f ≫ p := by rw [← Category.assoc, ← h.2.2.1.w, Category.assoc]
    exact h5 _ _ _ _ (hM _ (tw q i) _ _ _ _ (bcNat f p _ rfl) (bcNat g p _ rfl) (bcNat a _ _ rfl) (bcNat b _ _ eb)
      fun k => hB k.hom a b f g p _ _ _ rfl eb rfl rfl h) c' hU hV hW
  exact key n

end LateralTheory.KummerTheory.ContCut

end
end

section -- merged from Development.EtaleCohomology.KummerTheory.AdicDegPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.KummerTheory

def AdicLim : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (i : ℤ), (∀ b, BockData l b E i) →
  (∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) → ∀ n : ℤ, Module.Finite ℤ_[l] (Hl l E n i) ∧
    (∀ (k : ℕ) (x : Hl l E n i), lev l x k = 0 → ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y) ∧
    ∃ M : ℕ, 0 < M ∧ ∀ (k : ℕ) (z : Ht (l ^ k) E n i), ∃ x : Hl l E n i, lev l x k = M • z

def AdicAlg : Prop := ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ), Module.Finite ℤ_[l] (Hl l E n i) →
  (∀ (k : ℕ) (x : Hl l E n i), lev l x k = 0 → ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ k) • y) →
  ∀ M : ℕ, 0 < M → (∀ (k : ℕ) (z : Ht (l ^ k) E n i), ∃ x : Hl l E n i, lev l x k = M • z) →
  ∃ (r : ℕ) (c : Fin r → Hl l E n i) (N : ℕ), 0 < N ∧ QBasis l c ∧
    ∀ k, IsoUpTo N (comb (l ^ k) fun s => lev l (c s) k)

theorem AdicDeg_of (h1 : AdicLim) (h2 : AdicAlg) : AdicDeg := by
  intro hA l _ E i hB hF n
  obtain ⟨hfin, hker, M, hM, hcok⟩ := h1 hA l E i hB hF n
  exact h2 l E n i hfin hker M hM hcok

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.InjSlicePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def ForgetInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) [Injective F] (S : Scheme.{0}),
  ∃ h : Presheaf.IsSheaf (Scheme.etaleTopology.over S) ((Over.forget S).op ⋙ F.obj),
    Injective (⟨_, h⟩ : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R)))

theorem pushPullback_inj {R : Type} [CommRing R] {X S : Scheme.{0}} (p : X ⟶ S)
    (G : Sheaf (Scheme.etaleTopology.over X) (ModuleCat.{1} (ULift.{1} R))) [Injective G] :
    Injective (((Over.pullback p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over S) (Scheme.etaleTopology.over X)).obj G) := by
  have adj := (Over.mapPullbackAdj p).sheafPushforwardContinuous (E := ModuleCat.{1} (ULift.{1} R))
    (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over S)
  have : ((Over.map p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over X) (Scheme.etaleTopology.over S)).PreservesMonomorphisms := inferInstance
  exact Injective.injective_of_adjoint adj G

theorem InjSlice_of (hF : ForgetInj) : InjSlice := by
  intro R _ F _ X S p
  obtain ⟨hX, iX⟩ := hF R F X
  refine ⟨?_, hF R F S⟩
  let G : Sheaf (Scheme.etaleTopology.over X) (ModuleCat.{1} (ULift.{1} R)) := ⟨_, hX⟩
  exact ⟨(((Over.pullback p).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R))
      (Scheme.etaleTopology.over S) (Scheme.etaleTopology.over X)).obj G).2, pushPullback_inj p G⟩

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.DictPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def EvLin : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
  (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
    ev (R := R) (α + β) p s h U x = ev (R := R) α p s h U x + ev (R := R) β p s h U x ∧ ev (R := R) (-α) p s h U x = -ev (R := R) α p s h U x) ∧
  (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
    Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x)) ∧
  ∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
    ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x =
      ev (R := R) α p s h U ((f.app (op (SimplexCategory.mk p))).app (op U) x)

def DictExist : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ) (a : Sec (I.X n) X),
  Sec.map (I.d n (n + 1)) a = 0 → ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n,
    ev (R := R) α.1 0 n (by simp) X (𝟙 X) = a ∧
    ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev (R := R) α.1 (p + 1) s h U y = 0

def DictNormal : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ)
  (α : Cocycle ((chains R).obj (sch.obj X)) I n), ∃ α' : Cocycle ((chains R).obj (sch.obj X)) I n,
    CohomologyClass.mk α' = CohomologyClass.mk α ∧
    ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev (R := R) α'.1 (p + 1) s h U y = 0

def DictZero : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) (X : Scheme.{0}) (n : ℤ)
  (α : Cocycle ((chains R).obj (sch.obj X)) I n),
  (∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : Sx (sch.obj X) (p + 1) U), ev (R := R) α.1 (p + 1) s h U y = 0) →
  Sec.map (I.d n (n + 1)) (ev (R := R) α.1 0 n (by simp) X (𝟙 X)) = 0 ∧
    (CohomologyClass.mk α = 0 ↔ ∃ b : Sec (I.X (n - 1)) X, Sec.map (I.d (n - 1) n) b = ev (R := R) α.1 0 n (by simp) X (𝟙 X))

theorem Dict_of (hL : EvLin) (hE : DictExist) (hN : DictNormal) (hZ : DictZero) : Dict := by
  intro R _ I X n
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨α, h0, h1⟩ := hE R I X n a ha
    exact ⟨_, α, rfl, h0, h1⟩
  · intro x
    obtain ⟨α, rfl⟩ := x.mk_surjective
    obtain ⟨α', e, h1⟩ := hN R I X n α
    exact ⟨_, α', e, rfl, h1⟩
  · rintro x a ⟨α, rfl, h0, h1⟩
    subst h0
    exact hZ R I X n α h1
  · rintro x x' a a' ⟨α, rfl, h0, h1⟩ ⟨α', rfl, h0', h1'⟩
    refine ⟨⟨α + α', CohomologyClass.mk_add _ _ |>.symm, ?_, ?_⟩, ⟨-α, ?_, ?_, ?_⟩⟩
    · rw [← h0, ← h0']; exact ((hL R).1 α.1 α'.1 0 n _ X (𝟙 X)).1
    · intro p s h U y
      rw [show ((α + α' : Cocycle _ _ n) : Cochain _ _ n) = α.1 + α'.1 from rfl, ((hL R).1 _ _ _ _ _ _ _).1, h1, h1', add_zero]
    · rw [← CohomologyClass.mk_neg]
    · rw [← h0]; exact ((hL R).1 α.1 α.1 0 n _ X (𝟙 X)).2
    · intro p s h U y
      rw [show ((-α : Cocycle _ _ n) : Cochain _ _ n) = -α.1 from rfl, ((hL R).1 α.1 α.1 _ _ _ _ _).2, h1, neg_zero]
  · rintro Y f x a ⟨α, rfl, h0, h1⟩
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_, ?_⟩
    · change ev (R := R) ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) 0 n _ Y (𝟙 Y) = _
      refine ((hL R).2.2 (sch.map f) α.1 0 n _ Y (𝟙 Y)).trans ?_
      rw [← h0]
      exact (((hL R).2.1 α.1 0 n _ Y X f (𝟙 X)).trans rfl).symm
    · intro p s h U y
      change ev (R := R) ((Cochain.ofHom ((chains R).map (sch.map f))).comp α.1 (zero_add n)) (p + 1) s h U y = 0
      exact ((hL R).2.2 (sch.map f) α.1 _ _ _ _ _).trans (h1 _ _ _ _ _)

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.TwSecPf
section -- merged from Development.EtaleCohomology.KummerTheory.TwSecPfGamma
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.KummerTheory.TwSecPfGamma

theorem map_symm_map {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (f : B[X]) :
    (f.map (e.symm : B →+* A)).map (e : A →+* B) = f := by
  rw [Polynomial.map_map]
  have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by
    ext x; simp
  rw [this, Polynomial.map_id]

theorem mem_max_iff {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (x : B) :
    e.symm x ∈ IsLocalRing.maximalIdeal A ↔ x ∈ IsLocalRing.maximalIdeal B := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rw [isUnit_map_iff e.symm x]

theorem henselian_of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) [hA : HenselianLocalRing A] :
    HenselianLocalRing B := by
  haveI : Nontrivial A := inferInstance
  haveI : Nontrivial B := e.injective.nontrivial
  haveI : IsLocalRing B := IsLocalRing.of_surjective' (e : A →+* B) e.surjective
  refine { is_henselian := ?_ }
  intro f hf a₀ h1 h2
  have hev : ∀ (p : B[X]) (b : B), (p.map (e.symm : B →+* A)).eval (e.symm b) = e.symm (p.eval b) := by
    intro p b
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_hom (e.symm : B →+* A) b
  obtain ⟨a, ha, hmem⟩ := hA.is_henselian (f.map (e.symm : B →+* A)) (hf.map _) (e.symm a₀)
    (by rw [hev, mem_max_iff]; exact h1)
    (by rw [Polynomial.derivative_map, hev]; exact (isUnit_map_iff e.symm _).2 h2)
  refine ⟨e a, ?_, ?_⟩
  · have := ha.map (f := (e : A →+* B))
    rwa [map_symm_map] at this
  · rw [← mem_max_iff e]
    have : e.symm (e a - a₀) = a - e.symm a₀ := by simp
    rw [this]; exact hmem

theorem sepClosed_of_equiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) [IsSepClosed K] : IsSepClosed L := by
  refine IsSepClosed.of_exists_root _ fun p hm hirr hsep => ?_
  have hdeg : (p.map (e.symm : L →+* K)).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    intro h
    exact hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root (p.map (e.symm : L →+* K)) hdeg (hsep.map)
  refine ⟨e x, ?_⟩
  have := hx.map (f := (e : K →+* L))
  rw [map_symm_map] at this
  exact this

theorem SH_of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (h : SH A) : SH B := by
  obtain ⟨hA, hs⟩ := h
  haveI := hA
  haveI := henselian_of_equiv e
  refine ⟨inferInstance, ?_⟩
  haveI := hs
  exact sepClosed_of_equiv (IsLocalRing.ResidueField.mapEquiv e)

end LateralTheory.KummerTheory.TwSecPfGamma

namespace LateralTheory.KummerTheory

theorem SHGamma_holds (A : Type) [CommRing A] (h : SH A) : SH Γ(Spec (CommRingCat.of A), ⊤) :=
  TwSecPfGamma.SH_of_equiv (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm h

end LateralTheory.KummerTheory
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def PrimTors : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], SH B → IsUnit (q : B) →
  Nonempty (Prim q B) ∧ ∀ (i : ℤ) (ζ : Prim q B), Function.Bijective fun t : ZMod q =>
    (ULift.up t : ULift.{1} (ZMod q)) • (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) :
      (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q i B)

def SecSH : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ (R : Type) [CommRing R]
  (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)), Function.Bijective (ofRings.sec (R := R) M (Spec (CommRingCat.of A)))

theorem TwSec_of (h1 : PrimTors) (h2 : SecSH) : TwSec := by
  intro q _ A _ hA hq
  have hB := SHGamma_holds A hA
  have hqB : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  obtain ⟨hne, hbij⟩ := h1 q _ hB hqB
  refine ⟨hne, fun i ζ => ?_⟩
  have key : (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen i ζ) =
      ofRings.sec (R := ZMod q) (twF q i) (Spec (CommRingCat.of A)) ∘ (fun t : ZMod q =>
        (ULift.up t : ULift.{1} (ZMod q)) • (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) :
          (Prim q _ →₀ ULift.{1} (ZMod q)) ⧸ twRel q i _)) := by
    funext t
    simp only [twGen, ofRings.sec]
    exact (map_smul _ _ _).symm
  rw [key]
  exact (h2 A hA (ZMod q) (twF q i)).comp (hbij i ζ)

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.PlacePf
noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def PlaceEx : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K],
  ∃ (T : ValuationSubring K) (σ : k →+* T), (∀ x, (σ x : K) = algebraMap k K x) ∧
    Function.Surjective ((IsLocalRing.residue T).comp σ)

def ValAIC : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] (T : ValuationSubring K), AIC T ∧ HenselianLocalRing T

theorem Place_of (h1 : PlaceEx) (h2 : ValAIC) : Place := by
  intro k K _ _ _ _ _
  obtain ⟨T, σ, hσ, hs⟩ := h1 k K
  obtain ⟨hA, hH⟩ := h2 K T
  have hb : Function.Bijective ((IsLocalRing.residue T).comp σ) := ⟨RingHom.injective _, hs⟩
  refine ⟨T, σ, hσ, hb, hA, hH, ?_⟩
  have : IsAlgClosed (IsLocalRing.ResidueField T) := IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective _ hb)
  infer_instance

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.AlgExtPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AlgExtPf

variable {R : Type} [CommRing R] (F : Shv R)

theorem eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hg : Eqv R g F) :
    Eqv R (f ≫ g) F := fun n => by
  have : (pull R (f ≫ g) F n : _ → _) = (pull R f F n) ∘ (pull R g F n) := funext (pull_comp R f g F n)
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_cancel {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (h : Eqv R (f ≫ g) F) (hf : Eqv R f F) :
    Eqv R g F := fun n => by
  have hc : ∀ x, pull R (f ≫ g) F n x = pull R f F n (pull R g F n x) := pull_comp R f g F n
  refine ⟨fun a b hab => (h n).1 (by rw [hc, hc, hab]), fun y => ?_⟩
  obtain ⟨z, hz⟩ := (h n).2 (pull R f F n y)
  exact ⟨z, (hf n).1 (by rw [← hc, hz])⟩

theorem eqv_iso {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := fun n => by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem eqv_sch_iso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] : Eqv R (sch.map f) F := eqv_iso F _

theorem eqv_fst_comp {W X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (g' : W ⟶ Y)
    (h1 : Eqv R (sch.map (pullback.fst (pullback.snd f g) g')) F) (h2 : Eqv R (sch.map (pullback.fst f g)) F) :
    Eqv R (sch.map (pullback.fst f (g' ≫ g))) F := by
  rw [← pullbackLeftPullbackSndIso_inv_fst, Functor.map_comp, Functor.map_comp]
  exact eqv_comp F (eqv_sch_iso F _) (eqv_comp F h1 h2)

theorem eqv_fst_congr {X Z W : Scheme.{0}} (f : X ⟶ Z) {h h' : W ⟶ Z} (e : h = h') :
    Eqv R (sch.map (pullback.fst f h)) F → Eqv R (sch.map (pullback.fst f h')) F := by
  subst e; exact id

end LateralTheory.KummerTheory.AlgExtPf

namespace LateralTheory.KummerTheory
open LateralTheory.KummerTheory.AlgExtPf

theorem AlgExt_of (hP : Place) : AlgExt := by
  intro hE2 hE3 q _ k K _ _ _ _ f hq X p _ _ i
  let _ := f.toAlgebra
  obtain ⟨T, σ, hσ, hres, hAIC, hSH⟩ := hP k K
  have hqT : IsUnit ((q : ℕ) : T) := by simpa using hq.map σ
  set gσ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom σ) with hgσ
  set gr : Spec (CommRingCat.of (IsLocalRing.ResidueField T)) ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue T)) with hgr
  have e2 := hE2 q T hSH hqT (pullback.snd p gσ) i

  have hiso : IsIso (CommRingCat.ofHom ((IsLocalRing.residue T).comp σ)) :=
    (RingEquiv.ofBijective _ hres).toCommRingCatIso.isIso_hom
  have hcomp : gr ≫ gσ = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue T).comp σ)) := by
    rw [hgr, hgσ, ← Spec.map_comp]; rfl
  have hs : Eqv (ZMod q) (sch.map (pullback.fst p (gr ≫ gσ))) (tw q i) := by
    rw [hcomp]; exact eqv_sch_iso _ _
  rw [← pullbackLeftPullbackSndIso_inv_fst, Functor.map_comp, Functor.map_comp] at hs
  have hT : Eqv (ZMod q) (sch.map (pullback.fst p gσ)) (tw q i) :=
    eqv_cancel _ (eqv_cancel _ hs (eqv_sch_iso _ _)) e2

  have e3 := hE3 q T hAIC hqT (pullback.snd p gσ) i
  let eK : FractionRing T ≃+* K := (IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K).toRingEquiv
  set gj : Spec (CommRingCat.of (FractionRing T)) ⟶ Spec (CommRingCat.of T) :=
    Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T))) with hgj
  set ge : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (FractionRing T)) :=
    Spec.map (CommRingCat.ofHom eK.toRingHom) with hge
  have hge_iso : IsIso ge := by
    have : IsIso (CommRingCat.ofHom eK.toRingHom) := eK.toCommRingCatIso.isIso_hom
    rw [hge]; infer_instance
  have hfac : (ge ≫ gj) ≫ gσ = Spec.map (CommRingCat.ofHom f) := by
    rw [hge, hgj, hgσ, ← Spec.map_comp, ← Spec.map_comp]
    congr 1; ext x
    have h1 := hσ x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    change eK (algebraMap T (FractionRing T) (σ x)) = f x
    rw [show f x = algebraMap k K x from rfl, ← h1]
    exact (IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K).commutes (σ x)
  refine eqv_fst_congr _ p hfac (eqv_fst_comp _ p gσ (ge ≫ gj) ?_ hT)
  refine eqv_fst_comp _ _ gj ge ?_ e3
  exact eqv_sch_iso _ _

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.FinalTheorems
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

abbrev SlShv (Λ : Type) [CommRing Λ] (S : Scheme.{0}) : Type 2 :=
  Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} Λ))

instance (Λ : Type) [CommRing Λ] (S : Scheme.{0}) : HasSheafify (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} Λ)) := by
  have : EssentiallySmall.{1} (Over S) := inferInstance
  infer_instance

instance (Λ : Type) [CommRing Λ] (S : Scheme.{0}) : IsGrothendieckAbelian.{1} (SlShv Λ S) := by
  have : EssentiallySmall.{1} (Over S) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ (ModuleCat.{1} (ULift.{1} Λ))

def rst {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) : pullback p V.hom ⟶ pullback p U.hom :=
  pullback.map _ _ _ _ (𝟙 X) g.left (𝟙 S) (by simp) (by simp)

def Nbhd {S : Scheme.{0}} {V U : Over S} (g : V ⟶ U) (u : U.left) : Prop := Etale g.left ∧ ∃ v : V.left, g.left v = u

section Cone
variable {Λ : Type} [CommRing Λ] {I : Cx Λ} {X S : Scheme.{0}}

abbrev FinalTheorems (J : Cx Λ) (r : ℕ → ℕ) (M : ℕ) (n : ℤ) (U : Scheme.{0}) : Type 1 :=
  ∀ a : Fin (M + 1), Fin (r a) → Sec (J.X (n - ((a : ℕ) : ℤ))) U

abbrev Cone (J K : Cx Λ) (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ) (j : ℤ) (U : Over S) : Type 1 :=
  FinalTheorems J r M (j + 1) U.left × Sec (K.X j) (pullback p U.hom)

variable {J K : Cx Λ} {r : ℕ → ℕ} {M : ℕ}

def dS (n m : ℤ) {U : Scheme.{0}} (b : FinalTheorems J r M n U) : FinalTheorems J r M m U :=
  fun a s => ((a : ℕ) : ℤ).negOnePow • Sec.map (J.d (n - ((a : ℕ) : ℤ)) (m - ((a : ℕ) : ℤ))) (b a s)

def cres {p : X ⟶ S} {j : ℤ} {V U : Over S} (g : V ⟶ U) (x : Cone J K p r M j U) : Cone J K p r M j V :=
  (fun a s => Sec.res g.left (x.1 a s), Sec.res (rst p g) x.2)

variable (μ : Pair I J K) (p : X ⟶ S) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

def Phi (n w : ℤ) (h : n = w) (U : Over S) (b : FinalTheorems J r M n U.left) : Sec (K.X w) (pullback p U.hom) :=
  ∑ a : Fin (M + 1), ∑ s : Fin (r a), μ.mul _ ((a : ℕ) : ℤ) (n - ((a : ℕ) : ℤ)) w (by omega)
    (Sec.res (pullback.fst p U.hom) (γ a s)) (Sec.res (pullback.snd p U.hom) (b a s))

def cD (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) : Cone J K p r M j' U :=
  (dS (j + 1) (j' + 1) x.1, Phi μ p γ (j + 1) j' h U x.1 - Sec.map (K.d j j') x.2)

variable (M)

def ConeEx (N : ℕ) (j : ℤ) (U : Over S) : Prop := ∀ x : Cone J K p r M j U, cD μ p γ j (j + 1) rfl U x = 0 →
  ∃ y : Cone J K p r M (j - 1) U, cD μ p γ (j - 1) j (by omega) U y = N • x

def ConeLoc (N : ℕ) (j : ℤ) : Prop := ∀ (U : Over S) (x : Cone J K p r M j U), cD μ p γ j (j + 1) rfl U x = 0 →
  ∀ u : U.left, ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧
    ∃ y : Cone J K p r M (j - 1) V, cD μ p γ (j - 1) j (by omega) V y = N • cres g x

end Cone

def Closed {Λ : Type} [CommRing Λ] {I : Cx Λ} {X : Scheme.{0}} {r : ℕ → ℕ} (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X) : Prop :=
  ∀ (a : ℕ) (s : Fin (r a)), Sec.map (I.d a (a + 1)) (γ a s) = 0

def InjPos {Λ : Type} [CommRing Λ] (J : Cx Λ) : Prop := (∀ n, Injective (J.X n)) ∧ ∀ n : ℤ, n < 0 → IsZero (J.X n)

def mu (q : ℕ) (i : ℤ) : Pair (res _ (tw q i)) (res _ (tw q 0)) (res _ (tw q i)) :=
  cast (congrArg (fun w => Pair (res _ (tw q i)) (res _ (tw q 0)) (res _ (tw q w))) (add_zero i)) (twPair q i 0)

section Cls
variable (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ) (n : ℤ)

def KerLoc : Prop := ∀ (U : Over S) (u : U.left) y, lh q p U.hom i r c M n y = 0 →
  ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧ ∀ a s, N • pull _ (sch.map g.left) _ _ (y a s) = 0

def CokLoc : Prop := ∀ (U : Over S) (u : U.left) (x : Ht q (sch.obj (pullback p U.hom)) n i),
  ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧ ∃ y, lh q p V.hom i r c M n y = N • pull _ (sch.map (rst p g)) _ _ x

end Cls

def ClsMore : Prop := ∀ (Λ : Type) [CommRing Λ] (I : Cx Λ) (X : Scheme.{0}) (n : ℤ),
  IsCls (0 : CohomologyClass ((chains Λ).obj (sch.obj X)) I n) 0 ∧
  (∀ (N : ℕ) x (a : Sec (I.X n) X), IsCls x a → IsCls (N • x) (N • a)) ∧
  (∀ (ι : Type) [Fintype ι] (x : ι → CohomologyClass ((chains Λ).obj (sch.obj X)) I n) (a : ι → Sec (I.X n) X),
    (∀ t, IsCls (x t) (a t)) → IsCls (∑ t, x t) (∑ t, a t)) ∧
  ∀ (m : ℤ), m + 1 = n → ∀ x x' (a a' : Sec (I.X n) X), IsCls x a → IsCls x' a' →
    (x = x' ↔ ∃ b : Sec (I.X m) X, Sec.map (I.d m n) b = a - a')

def LhSec : Prop := ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
  (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X), (∀ a s, IsCls (c a s) (γ a s)) →
  ∀ (M : ℕ) (n : ℤ) (U : Over S) y (b : FinalTheorems (res _ (tw q 0)) r M n U.left), (∀ a s, IsCls (y a s) (b a s)) →
  IsCls (lh q p U.hom i r c M n y) (Phi (mu q i) p γ n n rfl U b)

def LhNat : Prop := DivisorNaturality → ∀ (q : ℕ) [NeZero q] {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ)
  (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ) {V U : Over S} (g : V ⟶ U) y,
  pull _ (sch.map (rst p g)) _ _ (lh q p U.hom i r c M n y) =
    lh q p V.hom i r c M n (fun a s => pull _ (sch.map g.left) _ _ (y a s))

def ConeAlg : Prop := ∀ (Λ : Type) [CommRing Λ] {I J K : Cx Λ} (μ : Pair I J K) {X S : Scheme.{0}} (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ)
  (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X), Closed γ → ∀ (j j' : ℤ) (h : j + 1 = j') (U : Over S),
  IsLinearMap (ULift.{1} Λ) (cD (M := M) μ p γ j j' h U) ∧
  (∀ (j'' : ℤ) (h' : j' + 1 = j'') (x : Cone J K p r M j U), cD μ p γ j' j'' h' U (cD μ p γ j j' h U x) = 0) ∧
  ∀ (V : Over S) (g : V ⟶ U), IsLinearMap (ULift.{1} Λ) (cres g : Cone J K p r M j U → _) ∧
    (∀ x : Cone J K p r M j U, cres g (cD μ p γ j j' h U x) = cD μ p γ j j' h V (cres g x)) ∧
    ∀ (W : Over S) (g' : W ⟶ V) (x : Cone J K p r M j U), cres (g' ≫ g) x = cres g' (cres g x)

def LocKer : Prop := DivisorNaturality → B1 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R), IsUnit (q : R) →
  ∀ (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ) (n : ℤ),
  (∀ (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsoUpTo N (lh q p (Spec.map s) i r c M n)) → KerLoc q p i r c M N n

def LocCok : Prop := A2 → DivisorNaturality → B1 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
  [QuasiCompact p] [IsSeparated p], IsUnit (q : R) →
  ∀ (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ) (n : ℤ),
  (∀ (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsoUpTo N (lh q p (Spec.map s) i r c M n)) → CokLoc q p i r c M N n

def LocCone : Prop := ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
  (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X), (∀ a s, IsCls (c a s) (γ a s)) → ∀ (M N : ℕ) (j : ℤ),
  KerLoc q p i r c M N (j + 1) → CokLoc q p i r c M N j → ConeLoc M (mu q i) p γ (N ^ 2) j

def ExIso : Prop := ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
  (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X), (∀ a s, IsCls (c a s) (γ a s)) → ∀ (M N : ℕ) (j : ℤ) (U : Over S),
  ConeEx M (mu q i) p γ N j U → ConeEx M (mu q i) p γ N (j + 1) U → IsoUpTo N (lh q p U.hom i r c M (j + 1))

def Corep : Prop := ∀ (Λ : Type) [CommRing Λ] (S : Scheme.{0}) (U : Over S), ∃ (P : SlShv Λ S) (z : P.obj.obj (op U)),
  ∀ F : SlShv Λ S, Function.Bijective fun φ : P ⟶ F => (φ.hom.app (op U)).hom z

def CxLoc {Λ : Type} [CommRing Λ] {S : Scheme.{0}} (C : CochainComplex (SlShv Λ S) ℤ) (N : ℕ) (j : ℤ) : Prop :=
  ∀ (U : Over S) (x : (C.X j).obj.obj (op U)), ((C.d j (j + 1)).hom.app (op U)).hom x = 0 → ∀ u : U.left,
    ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧ ∃ y : (C.X (j - 1)).obj.obj (op V),
      ((C.d (j - 1) j).hom.app (op V)).hom y = N • ((C.X j).obj.map g.op).hom x

def HomKill : Prop := ∀ (Λ : Type) [CommRing Λ] (S : Scheme.{0}) (C : CochainComplex (SlShv Λ S) ℤ) (N : ℕ) (j : ℤ),
  CxLoc C N j → N • 𝟙 (C.homology j) = 0

def GhostSec : Prop := ∀ (Λ : Type) [CommRing Λ] (S : Scheme.{0}) (C : CochainComplex (SlShv Λ S) ℤ), (∀ j, Injective (C.X j)) →
  (∀ j : ℤ, j < -1 → IsZero (C.X j)) → ∀ N m : ℕ, (∀ j : ℤ, j < m → CxLoc C N j) → ∀ j : ℤ, j < m →
  ∀ (U : Over S) (x : (C.X j).obj.obj (op U)), ((C.d j (j + 1)).hom.app (op U)).hom x = 0 →
    ∃ y : (C.X (j - 1)).obj.obj (op U), ((C.d (j - 1) j).hom.app (op U)).hom y = N ^ (m + 1) • x

def ConeObj : Prop := ∀ (Λ : Type) [CommRing Λ] (J K : Cx Λ), (∀ n, Injective (J.X n)) → (∀ n, Injective (K.X n)) →
  ∀ {X S : Scheme.{0}} (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ) (j : ℤ), ∃ T : SlShv Λ S, Injective T ∧
    ∃ e : ∀ U : Over S, T.obj.obj (op U) ≃ₗ[ULift.{1} Λ] Cone J K p r M j U,
      ∀ (V U : Over S) (g : V ⟶ U) x, e V ((T.obj.map g.op).hom x) = cres g (e U x)

def ConeCx : Prop := ∀ (Λ : Type) [CommRing Λ] {I J K : Cx Λ} (μ : Pair I J K), InjPos J → InjPos K →
  ∀ {X S : Scheme.{0}} (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X), Closed γ →
  ∃ C : CochainComplex (SlShv Λ S) ℤ, (∀ j, Injective (C.X j)) ∧ (∀ j : ℤ, j < -1 → IsZero (C.X j)) ∧
    ∃ e : ∀ (j : ℤ) (U : Over S), (C.X j).obj.obj (op U) ≃+ Cone J K p r M j U,
      (∀ (j : ℤ) (V U : Over S) (g : V ⟶ U) x, e j V (((C.X j).obj.map g.op).hom x) = cres g (e j U x)) ∧
      ∀ (j j' : ℤ) (h : j + 1 = j') (U : Over S) x, e j' U (((C.d j j').hom.app (op U)).hom x) = cD μ p γ j j' h U (e j U x)

def Glob : Prop := ∀ (Λ : Type) [CommRing Λ] {I J K : Cx Λ} (μ : Pair I J K), InjPos J → InjPos K →
  ∀ {X S : Scheme.{0}} (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X), Closed γ →
  ∀ N m : ℕ, (∀ j : ℤ, j < m → ConeLoc M μ p γ N j) → ∀ j : ℤ, j < m → ∀ U : Over S, ConeEx M μ p γ (N ^ (m + 1)) j U

theorem injPos_res (Λ : Type) [CommRing Λ] (F : Shv Λ) : InjPos (res Λ F) :=
  ⟨fun n => by unfold res; infer_instance,
   fun n hn => (injectiveResolution F).cochainComplex.isZero_of_isStrictlyGE 0 n hn⟩

theorem goal_of (hD : Dict) (h1 : LocKer) (h2 : LocCok) (h3 : LocCone) (h4 : Glob) (h5 : ExIso) : LH := by
  intro a2 a6 b1
  refine ⟨fun M => 2 * (M + 1), ?_⟩
  intro q _ X R p _ _ hq i r c M N hS Y pY n hn
  choose γ hγ using fun (a : ℕ) (s : Fin (r a)) => (hD _ (res _ (tw q i)) X a).2.1 (c a s)
  have hc : Closed γ := fun a s => ((hD _ (res _ (tw q i)) X a).2.2.1 _ _ (hγ a s)).1
  have hl : ∀ j : ℤ, j < M → ConeLoc M (mu q i) p γ (N ^ 2) j := fun j hj =>
    h3 q p i r c γ hγ M N j (h1 a6 b1 q p hq i r c M N _ fun A s hA => hS A s hA _ (by omega))
      (h2 a2 a6 b1 q p hq i r c M N _ fun A s hA => hS A s hA _ (by omega))
  have hg := h4 _ (mu q i) (injPos_res _ _) (injPos_res _ _) p r M γ hc (N ^ 2) M hl
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have := h5 q p i r c γ hγ M _ j (Over.mk pY) (hg j (by omega) _) (hg (j + 1) hn _)
  rw [← pow_mul] at this
  exact this

end LateralTheory.KummerTheory.LHCut

end
end
