module

public import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafChartCut
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

def LocStd (e d : ℕ) {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) : Prop :=
  RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (e + d)) φ ∧
  RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension e) ((Ideal.Quotient.mk I).comp φ)

def Std (e d : ℕ) {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) : Prop :=
  φ.IsStandardSmoothOfRelativeDimension (e + d) ∧ ((Ideal.Quotient.mk I).comp φ).IsStandardSmoothOfRelativeDimension e

def IsCoord {e d : ℕ} {R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) (x : Fin d → A)
    (y : Fin e → A) : Prop :=
  (MvPolynomial.eval₂Hom φ (Sum.elim x y)).Etale ∧ I = Ideal.span (Set.range x)

def LeafLoc : Prop := ∀ (d : ℕ) (P : SP d) (x : P.X) (W : P.X.Opens), x ∈ W →
  ∃ V : P.X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W ∧
    ∃ (R : Type) (_ : CommRing R) (φ : R →+* Γ(P.X, V.1)), LocStd P.e d φ (P.ι.ker.ideal V)

def LeafShrink : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I p : Ideal A), p.IsPrime → I ≤ p →
  LocStd e d φ I → ∃ f, f ∉ p ∧ ∀ (A' : Type) [CommRing A'] [Algebra A A'] [IsLocalization.Away f A'],
    Std e d ((algebraMap A A').comp φ) (I.map (algebraMap A A'))

def LeafRank : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (I p : Ideal A) [p.IsPrime], I ≤ p →
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) R A → Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) →
  Module.finrank p.ResidueField (p.ResidueField ⊗[A] I) = d

def LeafPick : Prop := ∀ (d : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] (p : Ideal A)
  [p.IsPrime], Module.finrank p.ResidueField (p.ResidueField ⊗[A] M) = d →
  ∃ (x : Fin d → M) (f : A), f ∉ p ∧ ∀ m : M, f • m ∈ Submodule.span A (Set.range x)

def LeafSpan : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  (I p : Ideal A), p.IsPrime → I ≤ p → Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) →
  ∀ (x : Fin d → A) (f : A), (∀ j, x j ∈ I) → f ∉ p → (∀ a ∈ I, f * a ∈ Ideal.span (Set.range x)) →
  ∃ (y : Fin e → A) (g : A), g ∉ p ∧ ∀ ω : Ω[A⁄R],
    g • ω ∈ Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (Sum.elim x y k))

def LeafEt : Prop := ∀ (n : ℕ) (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] (z : ι → A),
  Fintype.card ι = n → Algebra.IsStandardSmoothOfRelativeDimension n R A →
  Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (z k)) = ⊤ →
  (MvPolynomial.eval₂Hom (algebraMap R A) z).Etale

def LeafCoord : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I p : Ideal A), p.IsPrime → I ≤ p →
  Std e d φ I → ∃ f, f ∉ p ∧ ∀ (A' : Type) [CommRing A'] [Algebra A A'] [IsLocalization.Away f A'],
    ∃ (x : Fin d → A') (y : Fin e → A'), IsCoord ((algebraMap A A').comp φ) (I.map (algebraMap A A')) x y

def LeafSec : Prop := ∀ (A T : Type) [CommRing A] [CommRing T] (φ : A →+* T) (I : Ideal A) (μ : T →+* A ⧸ I), φ.Etale →
  μ.comp φ = Ideal.Quotient.mk I → ∃ t : T, μ t = 1 ∧ ∀ s : T, μ s = 0 → t * s ∈ I.map φ

def LeafPoly : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) (x : Fin d → A)
  (y : Fin e → A), IsCoord φ I x y →
  (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp ((Ideal.Quotient.mk I).comp φ))
    (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i)))).Etale

def LeafNbhd : Prop := ∀ (e d : ℕ) (R A : Type) [CommRing R] [CommRing A] (φ : R →+* A) (I : Ideal A) (x : Fin d → A)
  (y : Fin e → A), IsCoord φ I x y → Chart d A I

theorem etale_of_subsingleton {A B : Type} [CommRing A] [CommRing B] [Subsingleton B] (φ : A →+* B) : φ.Etale := by
  algebraize [φ]
  exact RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A B)

theorem chart_top (d : ℕ) (A : Type) [CommRing A] : Chart d A ⊤ := by
  have : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
  refine ⟨A ⧸ (⊤ : Ideal A), inferInstance, Ideal.Quotient.mk ⊤, MvPolynomial.constantCoeff,
    ⟨etale_of_subsingleton _, ?_⟩, etale_of_subsingleton _, Subsingleton.elim _ _, fun a => ?_⟩
  · have := (Ideal.Quotient.mk_surjective (I := (⊤ : Ideal A).map (Ideal.Quotient.mk (⊤ : Ideal A)))).subsingleton
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  · rw [Subsingleton.elim (_ - _) 0]; exact zero_mem _

theorem mem_basicOpen_of_notMem {X : Scheme.{0}} (V : X.affineOpens) (x : X) (hx : x ∈ V.1) (f : Γ(X, V.1))
    (hf : f ∉ (V.2.primeIdealOf ⟨x, hx⟩).asIdeal) : x ∈ X.basicOpen f := by
  have h : V.2.primeIdealOf ⟨x, hx⟩ ∈ V.2.fromSpec ⁻¹ᵁ X.basicOpen f := by
    rw [V.2.fromSpec_preimage_basicOpen]; exact hf
  have h2 : V.2.fromSpec (V.2.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h
  rwa [V.2.fromSpec_primeIdealOf] at h2

theorem shrink {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens) (x : X) (hx : x ∈ V.1) (f : Γ(X, V.1))
    (hf : f ∉ (V.2.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ (V' : X.affineOpens) (_ : Algebra Γ(X, V.1) Γ(X, V'.1)), x ∈ V'.1 ∧ V'.1 ≤ V.1 ∧ IsLocalization.Away f Γ(X, V'.1) ∧
      I.ideal V' = (I.ideal V).map (algebraMap Γ(X, V.1) Γ(X, V'.1)) :=
  ⟨X.affineBasicOpen f, (inferInstance : Algebra Γ(X, V.1) Γ(X, X.basicOpen f)), mem_basicOpen_of_notMem V x hx f hf,
    X.basicOpen_le f, V.2.isLocalization_basicOpen f, (I.map_ideal_basicOpen V f).symm⟩

theorem off_case (d : ℕ) {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens) (x : X) (hx : x ∈ V.1)
    (h : ¬ I.ideal V ≤ (V.2.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ V' : X.affineOpens, x ∈ V'.1 ∧ V'.1 ≤ V.1 ∧ (I.ideal V').FG ∧ Chart d Γ(X, V'.1) (I.ideal V') := by
  obtain ⟨f, hfI, hf⟩ := SetLike.not_le_iff_exists.mp h
  obtain ⟨V', _, hx', hle, _, hI⟩ := shrink I V x hx f hf
  have ht : I.ideal V' = ⊤ := by
    rw [hI]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hfI) (IsLocalization.Away.algebraMap_isUnit f)
  refine ⟨V', hx', hle, ?_, ?_⟩
  · rw [ht]; exact Ideal.fg_top _
  · rw [ht]; exact chart_top d _

theorem goal_of (hL : LeafLoc) (hS : LeafShrink) (hC : LeafCoord) (hN : LeafNbhd) : LeafChart := by
  intro d P x W hx
  obtain ⟨V, hxV, hVW, R, _, φ, hφ⟩ := hL d P x W hx
  by_cases h : P.ι.ker.ideal V ≤ (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal
  swap
  · obtain ⟨V', a, b, c⟩ := off_case d P.ι.ker V x hxV h
    exact ⟨V', a, b.trans hVW, c⟩
  obtain ⟨f, hf, H⟩ := hS P.e d R _ φ _ _ (V.2.primeIdealOf ⟨x, hxV⟩).isPrime h hφ
  obtain ⟨V₁, _, hx₁, hle₁, _, hI₁⟩ := shrink P.ι.ker V x hxV f hf
  have H₁ := H Γ(P.X, V₁.1)
  rw [← hI₁] at H₁
  by_cases h₁ : P.ι.ker.ideal V₁ ≤ (V₁.2.primeIdealOf ⟨x, hx₁⟩).asIdeal
  swap
  · obtain ⟨V', a, b, c⟩ := off_case d P.ι.ker V₁ x hx₁ h₁
    exact ⟨V', a, b.trans (hle₁.trans hVW), c⟩
  obtain ⟨g, hg, G⟩ := hC P.e d R _ _ _ _ (V₁.2.primeIdealOf ⟨x, hx₁⟩).isPrime h₁ H₁
  obtain ⟨V₂, _, hx₂, hle₂, _, hI₂⟩ := shrink P.ι.ker V₁ x hx₁ g hg
  obtain ⟨u, v, G₂⟩ := G Γ(P.X, V₂.1)
  rw [← hI₂] at G₂
  refine ⟨V₂, hx₂, hle₂.trans (hle₁.trans hVW), ?_, hN P.e d R _ _ _ u v G₂⟩
  rw [G₂.2]
  exact Submodule.fg_span (Set.finite_range u)

end LateralTheory.CohomologicalPurity.ChartCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafBdCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd

section Defs
variable {R : Type} [CommRing R] {A B D : Cx R}

abbrev pb (f : A ⟶ B) {I : Cx R} {n : ℤ} (c : Cochain B I n) : Cochain A I n := (Cochain.ofHom f).comp c (zero_add n)

abbrev hpb (f : A ⟶ B) (I : Cx R) (n : ℤ) : CohomologyClass B I n →+ CohomologyClass A I n :=
  cpre (Cocycle.ofHom f) I n n (zero_add n)

structure Good (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R) : Prop where
  w : i ≫ l = i ≫ r
  surj : ∀ (n : ℤ) (a : Cochain A I n), ∃ c : Cochain B I n, pb i c = a
  glue : ∀ (n : ℤ) (c c' : Cochain B I n), pb i c = pb i c' → ∃ b : Cochain D I n, pb l b = c ∧ pb r b = c'
  ext : ∀ (n : ℤ) (b b' : Cochain D I n), pb l b = pb l b' → pb r b = pb r b' → b = b'

def Tri (i : A ⟶ B) (l r : B ⟶ D) {I : Cx R} {n : ℤ} (a : Cocycle A I n) (c : Cochain B I n)
    (b : Cocycle D I (n + 1)) : Prop :=
  pb i c = a.1 ∧ pb l b.1 = δ n (n + 1) c ∧ pb r b.1 = 0

def IsDelta (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R) (n : ℤ) (d : CohomologyClass A I n →+ (hpb r I (n + 1)).ker) : Prop :=
  ∀ (a : Cocycle A I n) (c : Cochain B I n) (b : Cocycle D I (n + 1)), Tri i l r a c b →
    (d (CohomologyClass.mk a)).1 = CohomologyClass.mk b

theorem Good.tri {i : A ⟶ B} {l r : B ⟶ D} {I : Cx R} (h : Good i l r I) {n : ℤ} (a : Cocycle A I n) :
    ∃ c b, Tri i l r a c b := by
  obtain ⟨c, hc⟩ := h.surj n a.1
  obtain ⟨b, hl, hr⟩ := h.glue (n + 1) (δ n (n + 1) c) 0 (by
    rw [pb, ← δ_ofHom_comp]
    change δ n (n + 1) (pb i c) = _
    rw [hc]; simp [pb])
  refine ⟨c, Cocycle.mk b (n + 1 + 1) rfl (h.ext _ _ _ ?_ ?_), hc, hl, hr⟩
  · rw [pb, ← δ_ofHom_comp]
    change δ _ _ (pb l b) = _
    rw [hl, δ_δ]; simp [pb]
  · rw [pb, ← δ_ofHom_comp]
    change δ _ _ (pb r b) = _
    rw [hr]; simp [pb]

theorem pb_pb (f : A ⟶ B) (g : B ⟶ D) {I : Cx R} {n : ℤ} (c : Cochain D I n) : pb f (pb g c) = pb (f ≫ g) c := by
  simp [pb, Cochain.ofHom_comp]

end Defs

def LeafMono : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E), Mono f → ∀ p : ℤ, Mono (((chains R).map f).f p)

def LeafPush : Prop := ∀ (R : Type) [CommRing R] {U E E' D : Spc} (f : U ⟶ E) (g : U ⟶ E') (l : E ⟶ D) (r : E' ⟶ D),
  IsPushout f g l r → ∀ p : ℤ, IsPushout (((chains R).map f).f p) (((chains R).map g).f p) (((chains R).map l).f p)
    (((chains R).map r).f p)

def LeafGood : Prop := ∀ (R : Type) [CommRing R] {A B D : Cx R} (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R),
  (∀ p, Mono (i.f p)) → (∀ p, IsPushout (i.f p) (i.f p) (l.f p) (r.f p)) → (∀ p, Injective (I.X p)) → Good i l r I

def LeafDelta : Prop := ∀ (R : Type) [CommRing R] {A B D : Cx R} (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R),
  Good i l r I → ∀ n : ℤ, ∃ d, IsDelta i l r I n d

def LeafExact : Prop := ∀ (R : Type) [CommRing R] {A B D : Cx R} (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R),
  Good i l r I → ∀ (n : ℤ) d, IsDelta i l r I n d →
    Function.Exact ((hpb l I n).comp (hpb r I n).ker.subtype) (hpb i I n) ∧ Function.Exact (hpb i I n) d ∧
    Function.Exact d ((hpb l I (n + 1)).comp (hpb r I (n + 1)).ker.subtype)

def LeafGen : Prop := ∀ (R : Type) [CommRing R] (P : PSh),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x)) ∧
  (∀ (P' : PSh) (f : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)),
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R P' U (f.app (op U) x)) ∧
  (∀ (G : Shv R) (φ ψ : (free R).obj P ⟶ G),
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) → φ = ψ) ∧
  ∀ (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U),
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x)) →
    ∃ φ : (free R).obj P ⟶ G, ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = t U x

def LeafImgHom : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] (I : Cx S) (J : Cx R) (ρ : SemiMap I J),
  ∃ T : ∀ (P : PSh) (s : ℤ), ((free S).obj P ⟶ I.X s) →+ ((free R).obj P ⟶ J.X s),
    (∀ (P : PSh) (s : ℤ) (φ : (free S).obj P ⟶ I.X s) (U : Scheme.{0}) (x : P.obj (op U)),
      Sec.map (T P s φ) (freeGen R P U x) = ρ.app U s (Sec.map φ (freeGen S P U x))) ∧
    (∀ (P : PSh) (s t : ℤ) (φ : (free S).obj P ⟶ I.X s), T P t (φ ≫ I.d s t) = T P s φ ≫ J.d s t) ∧
    ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T P s ((free S).map f ≫ φ) = (free R).map f ≫ T P' s φ

def LeafImg : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] (I : Cx S) (J : Cx R) (ρ : SemiMap I J),
  ∃ T : ∀ (E : Spc) (n : ℤ), Cochain ((chains S).obj E) I n →+ Cochain ((chains R).obj E) J n,
    (∀ (E : Spc) (n : ℤ) (α : Cochain ((chains S).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
      (x : Sx E p U), ev (R := R) (T E n α) p s h U x = ρ.app U s (ev (R := S) α p s h U x)) ∧
    (∀ (E : Spc) (n m : ℤ) (α : Cochain ((chains S).obj E) I n), T E m (δ n m α) = δ n m (T E n α)) ∧
    ∀ (E E' : Spc) (f : E ⟶ E') (n : ℤ) (α : Cochain ((chains S).obj E') I n),
      T E n (pb ((chains S).map f) α) = pb ((chains R).map f) (T E' n α)

theorem good (h1 : LeafMono) (h2 : LeafPush) (h3 : LeafGood) (R : Type) [CommRing R] (F : Shv R) (P : Arrow Spc)
    (hP : Mono P.hom) : Good ((chains R).map P.hom) ((chains R).map (dbl.inl P)) ((chains R).map (dbl.inr P)) (res R F) :=
  h3 R _ _ _ _ (h1 R _ hP) (h2 R _ _ _ _ (IsPushout.of_hasPushout P.hom P.hom)) fun p => by
    unfold res; infer_instance

theorem inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem goal_of (h1 : LeafMono) (h2 : LeafPush) (h3 : LeafGood) (h4 : LeafDelta) (h5 : LeafExact) (h6 : LeafImg) :
    LeafBd := by
  have G := fun (q : ℕ) (i : ℤ) => good h1 h2 h3 (ZMod q) (tw q i)
  have ex : ∀ (q : ℕ) (P : Arrow Spc) (n i : ℤ), ∃ d : Ht q P.left n i →+ Hs q P (n + 1) i, Mono P.hom →
      IsDelta ((chains _).map P.hom) ((chains _).map (dbl.inl P)) ((chains _).map (dbl.inr P)) (res _ (tw q i)) n d := by
    intro q P n i
    by_cases hP : Mono P.hom
    · obtain ⟨d, hd⟩ := h4 _ _ _ _ _ (G q i P hP) n
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose d hd using ex
  refine ⟨d, fun q P hP n i => h5 _ _ _ _ _ (G q i P hP) n _ (hd q P n i hP), ?_, ?_⟩
  · intro q P' P φ hP' hP n i u
    obtain ⟨a, rfl⟩ := u.mk_surjective
    obtain ⟨c, b, ht⟩ := (G q i P hP).tri a
    have e := hd q P n i hP a c b ht
    have e' := hd q P' n i hP' (zcomp (Cocycle.ofHom ((chains _).map φ.left)) a (zero_add n))
      (pb ((chains _).map φ.right) c) (zcomp (Cocycle.ofHom ((chains _).map (dbl.map φ))) b (zero_add _)) (by
        obtain ⟨t1, t2, t3⟩ := ht
        refine ⟨?_, ?_, ?_⟩
        · change _ = pb _ a.1
          rw [← t1, pb_pb, pb_pb, ← Functor.map_comp, ← Functor.map_comp, Arrow.w φ]
        · change pb _ (pb _ b.1) = _
          rw [δ_ofHom_comp, ← t2]
          change _ = pb _ (pb _ b.1)
          rw [pb_pb, pb_pb, ← Functor.map_comp, ← Functor.map_comp, inl_map]
        · change pb _ (pb _ b.1) = _
          rw [pb_pb, ← Functor.map_comp, dbl.inr_map, Functor.map_comp, ← pb_pb, t3]
          exact Cochain.comp_zero _ _)
    apply Subtype.ext
    refine Eq.trans ?_ e'.symm
    exact congrArg (pull _ (dbl.map φ) (tw q i) (n + 1)) e
  · intro Q q _ _ P hP n i u
    obtain ⟨T, hv, hδ, hp⟩ := h6 _ _ _ _ (redMap Q q i)
    let Z : ∀ (E : Spc) (m : ℤ), Cocycle ((chains _).obj E) (res _ (tw Q i)) m → Cocycle ((chains _).obj E) (res _ (tw q i)) m :=
      fun E m α => Cocycle.mk (T E m α.1) (m + 1) rfl (by rw [← hδ, α.δ_eq_zero, map_zero])
    have key : (∀ E m x, red Q q E m i x = 0) ∨
        ∀ E m α, red Q q E m i (CohomologyClass.mk α) = CohomologyClass.mk (Z E m α) := by
      unfold red SemiMap.op pick
      split_ifs with h
      · exact Or.inr fun E m α => h.choose_spec E m α (Z E m α) (hv E m α.1)
      · exact Or.inl fun _ _ _ => rfl
    rcases key with k | k
    · rw [k, k, map_zero]; rfl
    obtain ⟨a, rfl⟩ := u.mk_surjective
    obtain ⟨c, b, ht⟩ := (G Q i P hP).tri a
    have e := hd Q P n i hP a c b ht
    have e' := hd q P n i hP (Z _ _ a) (T _ _ c) (Z _ _ b) (by
      obtain ⟨t1, t2, t3⟩ := ht
      refine ⟨?_, ?_, ?_⟩
      · change _ = T _ _ a.1
        rw [← hp, t1]
      · change pb _ (T _ _ b.1) = _
        rw [← hp, t2, hδ]
      · change pb _ (T _ _ b.1) = _
        rw [← hp, t3, map_zero])
    rw [k]
    refine e'.trans ?_
    rw [← k]
    exact congrArg _ e.symm

end LateralTheory.CohomologicalPurity.Bd
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafClCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

def Zc {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) : AddSubgroup (Sec (K.X n) X) :=
  ((K.X n).obj.map U.ι.op).hom.toAddMonoidHom.ker ⊓ ((K.d n (n + 1)).hom.app (op X)).hom.toAddMonoidHom.ker

theorem mem_Zc {R : Type} [CommRing R] {K : Cx R} {X : Scheme.{0}} {U : X.Opens} {n : ℤ} (a : Sec (K.X n) X) :
    a ∈ Zc K U n ↔ Sec.res U.ι a = 0 ∧ Sec.map (K.d n (n + 1)) a = 0 := Iff.rfl

def Bd {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) (a : Sec (K.X n) X) : Prop :=
  ∃ b : Sec (K.X (n - 1)) X, Sec.res U.ι b = 0 ∧ Sec.map (K.d (n - 1) n) b = a

abbrev rs {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (a : Sec G W.toScheme) :
    Sec G V.toScheme := Sec.res (X.homOfLE h) a

structure Pc {X : Scheme.{0}} (U : X.Opens) where
  Y : Scheme.{0}
  j : Y ⟶ X
  op : IsOpenImmersion j
  V : Y.Opens
  hV : V = j ⁻¹ᵁ U

abbrev Pc.res {X : Scheme.{0}} {U : X.Opens} (p : Pc U) (q : ℕ) (n i : ℤ) : Hs q (opn U) n i →+ Hs q (opn p.V) n i :=
  Hs.pull q (opnMap p.j p.V U p.hV.le) n i

def LocVan (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop := ∀ (x : X) (W : X.Opens), x ∈ W →
  ∃ p : Pc U, x ∈ Set.range p.j ∧ Set.range p.j ⊆ W ∧ ∀ n < m, Subsingleton (Hs q (opn p.V) n i)

def Sep (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop := ∀ s : Hs q (opn U) m i,
  (∀ x : X, x ∉ U → ∃ p : Pc U, x ∈ Set.range p.j ∧ p.res q m i s = 0) → s = 0

def Glue (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop :=
  ∀ (A : Type) (p : A → Pc U) (s : ∀ a, Hs q (opn (p a).V) m i), (∀ x : X, x ∉ U → ∃ a, x ∈ Set.range (p a).j) →
  (∀ a b (y : (p a).Y), (p a).j y ∉ U → (p a).j y ∈ Set.range (p b).j →
    ∃ (t : Pc (p a).V) (u : t.Y ⟶ (p b).Y) (h : t.V ≤ u ⁻¹ᵁ (p b).V), t.j ≫ (p a).j = u ≫ (p b).j ∧ y ∈ Set.range t.j ∧
      t.res q m i (s a) = Hs.pull q (opnMap u t.V (p b).V h) m i (s b)) →
  ∃ c, ∀ a, (p a).res q m i c = s a

structure Frame {d : ℕ} (P : SP d) where
  B : Type
  [cr : CommRing B]
  I : Ideal B
  x : Fin d → B
  hx : Ideal.span (Set.range x) = I
  w : Spec (CommRingCat.of B) ⟶ P.X
  z : Spec (CommRingCat.of (B ⧸ I)) ⟶ P.Z
  h : off B I ≤ w ⁻¹ᵁ P.U
  cart : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) z w P.ι

attribute [instance] Frame.cr

def LeafDisc : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ),
  ∃ cl : ∀ P : PSh, ((free R).obj P ⟶ K.X n) → CohomologyClass ((chains R).obj (disc.obj P)) K n,
    (∀ P a b, a ≫ K.d n (n + 1) = 0 → b ≫ K.d n (n + 1) = 0 → cl P (a + b) = cl P a + cl P b) ∧
    (∀ P x, ∃ a, a ≫ K.d n (n + 1) = 0 ∧ cl P a = x) ∧
    (∀ P a, a ≫ K.d n (n + 1) = 0 → (cl P a = 0 ↔ ∃ b, b ≫ K.d (n - 1) n = a)) ∧
    ∀ (P' P : PSh) (f : P' ⟶ P) (a : (free R).obj P ⟶ K.X n), a ≫ K.d n (n + 1) = 0 →
      cpre (Cocycle.ofHom ((chains R).map (disc.map f))) K n n (zero_add n) (cl P a) = cl P' ((free R).map f ≫ a)

def LeafDict : Prop := ∀ (q : ℕ) (n i : ℤ),
  ∃ cls : ∀ {X : Scheme.{0}} (U : X.Opens), Zc (res _ (tw q i)) U n →+ Hs q (opn U) n i,
    (∀ {X : Scheme.{0}} (U : X.Opens), Function.Surjective (cls U)) ∧
    (∀ {X : Scheme.{0}} (U : X.Opens) (a : Zc (res _ (tw q i)) U n), cls U a = 0 ↔ Bd _ U n a.1) ∧
    ∀ {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U) (a : Zc (res _ (tw q i)) U n)
      (a' : Zc (res _ (tw q i)) U' n), a'.1 = Sec.res f a.1 → Hs.pull q (opnMap f U' U h) n i (cls U a) = cls U' a'

def LeafZorn : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) (X : Scheme.{0}) (N : ∀ W : X.Opens, AddSubgroup (Sec G W.toScheme)),
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ N W, rs h a ∈ N V) →
  (∀ (W : X.Opens) (a : Sec G W.toScheme), (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ rs h a ∈ N V) → a ∈ N W) →
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ N V, ∃ b ∈ N W, rs h b = a) →
  ∀ (W : X.Opens) (A : Type) (V : A → X.Opens) (h : ∀ k, V k ≤ W) (a : ∀ k, Sec G (V k).toScheme),
    (∀ x ∈ W, ∃ k, x ∈ V k) → (∀ k l, rs inf_le_left (a k) - rs inf_le_right (a l) ∈ N (V k ⊓ V l)) →
    ∃ c : Sec G W.toScheme, ∀ k, rs (h k) c - a k ∈ N (V k)

def LeafFlq : Prop := ∀ (R : Type) [CommRing R] (K : Cx R), (∀ s, Injective (K.X s)) → (∀ s < 0, IsZero (K.X s)) →
  ∀ (X : Scheme.{0}) (U : X.Opens) (m : ℤ),
  (∀ n < m, ∀ (W : X.Opens), ∀ a ∈ Zc K (W.ι ⁻¹ᵁ U) n, ∀ x ∈ W,
    ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Bd K (V.ι ⁻¹ᵁ U) n (rs h a)) →
  (∀ (W : X.Opens) (a : Sec (K.X m) W.toScheme),
    (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Bd K (V.ι ⁻¹ᵁ U) m (rs h a)) → Bd K (W.ι ⁻¹ᵁ U) m a) ∧
  ∀ (A : Type) (V : A → X.Opens) (a : ∀ k, Sec (K.X m) (V k).toScheme), (∀ k, a k ∈ Zc K ((V k).ι ⁻¹ᵁ U) m) →
    (∀ x : X, ∃ k, x ∈ V k) →
    (∀ k l, ∀ x ∈ V k, x ∈ V l → ∃ (T : X.Opens) (hk : T ≤ V k) (hl : T ≤ V l), x ∈ T ∧
      Bd K (T.ι ⁻¹ᵁ U) m (rs hk (a k) - rs hl (a l))) →
    ∃ c ∈ Zc K U m, ∀ k, Bd K ((V k).ι ⁻¹ᵁ U) m (Sec.res (V k).ι c - a k)

def LeafDesc : Prop := ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ), LocVan q U m i → Sep q U m i ∧ Glue q U m i

def LeafNb : Prop := A1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (J : Ideal B),
  Nbhd φ I → J = I.map φ → ∀ h, Exc q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B J) (off A I) h)

def LeafVanRing : Prop := Hyp → ∀ (d q : ℕ) [NeZero q] (A : Type) [CommRing A] (I : Ideal A), Chart d A I → IsUnit (q : A) →
  ∀ n i : ℤ, n < 2 * d → Subsingleton (Hs q (opn (off A I)) n i)

def LeafVan : Prop := Hyp → ∀ (d q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) → ∀ i : ℤ, LocVan q P.U (2 * d) i

def LeafVanF : Prop := Hyp → ∀ (d q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) → ∀ F : Frame P, Etale F.w →
  ∀ i : ℤ, LocVan q (off F.B F.I) (2 * d) i

def LeafOff : Prop := ∀ (d : ℕ) (P : SP d) (F : Frame P), off F.B F.I = F.w ⁻¹ᵁ P.U

def LeafGenRing : Prop := ∀ (d : ℕ) (A : Type) [CommRing A] (I : Ideal A), I.FG → Chart d A I →
  ∃ (a : Fin d → A) (r : A), r - 1 ∈ I ∧ (∀ j, a j ∈ I) ∧ ∀ y ∈ I, r * y ∈ Ideal.span (Set.range a)

def LeafGen : Prop := ∀ (d : ℕ) (P : SP d) (x : P.X), x ∉ P.U →
  ∃ F : Frame P, IsOpenImmersion F.w ∧ x ∈ Set.range F.w

def LeafMat : Prop := ∀ (d : ℕ) (A : Type) [CommRing A] (x y : Fin d → A),
  Ideal.span (Set.range x) = Ideal.span (Set.range y) → ∀ p : PrimeSpectrum A,
  ∃ M : Matrix (Fin d) (Fin d) A, M.det ∉ p.asIdeal ∧ y = M.mulVec x

def LeafCmp : Prop := ∀ (d : ℕ) (P : SP d) (F F₀ : Frame P), IsOpenImmersion F₀.w → ∀ y, F.w y ∈ Set.range F₀.w →
  ∃ (C : Type) (_ : CommRing C) (φ : F.B →+* C) (ψ : F₀.B →+* C) (M : Matrix (Fin d) (Fin d) C),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) ∧ y ∈ Set.range (Spec.map (CommRingCat.ofHom φ)) ∧
    Spec.map (CommRingCat.ofHom φ) ≫ F.w = Spec.map (CommRingCat.ofHom ψ) ≫ F₀.w ∧ F.I.map φ = F₀.I.map ψ ∧
    IsUnit M.det ∧ φ ∘ F.x = M.mulVec (ψ ∘ F₀.x)

theorem off_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) :
    off B (I.map φ) = Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ off A I := by
  ext y
  change ¬ ((I.map φ : Set B) ⊆ (y : PrimeSpectrum B).asIdeal) ↔ ¬ ((I : Set A) ⊆ ((y : PrimeSpectrum B).asIdeal.comap φ))
  exact not_congr Ideal.map_le_iff_le_comap

theorem unit_B {X : Scheme.{0}} {q : ℕ} (hq : IsUnit (q : Γ(X, ⊤))) {B : Type} [CommRing B]
    (w : Spec (CommRingCat.of B) ⟶ X) : IsUnit (q : B) := by
  simpa using (hq.map w.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom

theorem inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem dbl_comp {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) : dbl.map (φ ≫ ψ) = dbl.map φ ≫ dbl.map ψ := by
  set_option synthInstance.maxHeartbeats 200000 in
    apply pushout.hom_ext
  · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
    rw [inl_map, ← Category.assoc, inl_map, Category.assoc, inl_map, ← Category.assoc]
    rfl
  · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
    rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, ← Category.assoc]
    rfl

theorem opnMap_comp {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' U' U) (h h' h'') :
    opnMap f U'' U' h ≫ opnMap g U' U h' = opnMap (f ≫ g) U'' U h'' := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · exact (sch.map_comp f g).symm

theorem pull_pull {q : ℕ} {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) {k : X'' ⟶ X} (e : f ≫ g = k) (U'' U' U)
    (h h' h'') (n i : ℤ) (c : Hs q (opn U) n i) :
    Hs.pull q (opnMap f U'' U' h) n i (Hs.pull q (opnMap g U' U h') n i c) = Hs.pull q (opnMap k U'' U h'') n i c := by
  subst e
  apply Subtype.ext
  rw [← opnMap_comp f g U'' U' U h h' h'']
  change pull _ (dbl.map _) _ n (pull _ (dbl.map _) _ n c.1) = pull _ (dbl.map _) _ n c.1
  rw [dbl_comp, pull_comp]

variable {d q : ℕ}

abbrev Frame.th {P : SP d} (F : Frame P) (q : ℕ) : Hs q (opn (off F.B F.I)) (2 * d) d := thom d q F.B F.I F.x F.hx

abbrev Frame.pl {P : SP d} (F : Frame P) (q : ℕ) : Hs q (opn P.U) (2 * d) d →+ Hs q (opn (off F.B F.I)) (2 * d) d :=
  Hs.pull q (opnMap F.w (off F.B F.I) P.U F.h) _ _

def Fund (q : ℕ) (P : SP d) (c : Hs q (opn P.U) (2 * d) d) : Prop := ∀ x : P.X, x ∉ P.U →
  ∃ F : Frame P, IsOpenImmersion F.w ∧ x ∈ Set.range F.w ∧ F.pl q c = F.th q

theorem span_comp {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (x : Fin d → A) :
    Ideal.span (Set.range (φ ∘ x)) = (Ideal.span (Set.range x)).map φ := by
  rw [Ideal.map_span, Set.range_comp]

theorem agree [NeZero q] (hT : IsThom d (thom d)) (hC : LeafCmp) {P : SP d} (hq : IsUnit (q : Γ(P.X, ⊤))) (F F₀ : Frame P)
    (h₀ : IsOpenImmersion F₀.w) (y) (hy : F.w y ∈ Set.range F₀.w) :
    ∃ (t : Pc (off F.B F.I)) (u : t.Y ⟶ Spec (CommRingCat.of F₀.B)) (h : t.V ≤ u ⁻¹ᵁ off F₀.B F₀.I),
      t.j ≫ F.w = u ≫ F₀.w ∧ y ∈ Set.range t.j ∧
      t.res q _ _ (F.th q) = Hs.pull q (opnMap u t.V _ h) _ _ (F₀.th q) := by
  obtain ⟨C, _, φ, ψ, M, ho, hyr, e, hI, hM, hx⟩ := hC d P F F₀ h₀ y hy
  obtain ⟨h1, h2, -, -⟩ := hT q
  have hB := unit_B hq F.w
  have a1 : Ideal.span (Set.range (φ ∘ F.x)) = F.I.map φ := by rw [span_comp, F.hx]
  have a2 : Ideal.span (Set.range (ψ ∘ F₀.x)) = F.I.map φ := by rw [span_comp, F₀.hx, hI]
  refine ⟨⟨_, _, ho, off C (F.I.map φ), off_map φ F.I⟩, Spec.map (CommRingCat.ofHom ψ),
    (hI ▸ off_map ψ F₀.I).le, e, hyr, ?_⟩
  refine (h1 _ _ φ _ _ _ _ a1 _ hB).trans (Eq.trans ?_ (h1 _ _ ψ _ _ _ _ a2 _ (unit_B hq F₀.w)).symm)
  have := h2 C _ (ψ ∘ F₀.x) M a2 (hx ▸ a1) (by simpa using hB.map φ) hM
  rw [← this]
  congr 1

theorem frame_eq [NeZero q] (hT : IsThom d (thom d)) (hC : LeafCmp) (hO : LeafOff) {P : SP d}
    (hq : IsUnit (q : Γ(P.X, ⊤))) {c} (hc : Fund q P c) (F : Frame P) (hS : Sep q (off F.B F.I) (2 * d) d) :
    F.pl q c = F.th q := by
  refine sub_eq_zero.1 (hS _ fun y hy => ?_)
  rw [hO] at hy
  obtain ⟨F₀, h₀, hy₀, e₀⟩ := hc (F.w y) hy
  obtain ⟨t, u, h, e, hyt, ht⟩ := agree hT hC hq F F₀ h₀ y hy₀
  refine ⟨t, hyt, ?_⟩
  have hle : t.V ≤ (u ≫ F₀.w) ⁻¹ᵁ P.U := fun a ha => by simpa using F₀.h (h ha)
  rw [map_sub, ht, ← e₀, sub_eq_zero]
  exact (pull_pull _ _ e _ _ _ _ _ hle _ _ c).trans (pull_pull _ _ rfl _ _ _ _ _ hle _ _ c).symm

def Frame.pc (hO : LeafOff) {P : SP d} (F : Frame P) (h : IsOpenImmersion F.w) : Pc P.U := ⟨_, F.w, h, off F.B F.I, hO d P F⟩

theorem goal_of (hTh : LeafThom) (hD : LeafDesc) (hV : LeafVan) (hVF : LeafVanF) (hO : LeafOff) (hG : LeafGen)
    (hC : LeafCmp) : LeafCl := by
  intro H d
  have hT : IsThom d (thom d) := @pick_spec _ ⟨fun _ _ _ _ _ _ => 0⟩ _ (hTh H d)
  have ex : ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) → ∃ c, Fund q P c := by
    intro q _ P hq
    choose F hF hx using fun x : {x : P.X // x ∉ P.U} => hG d P x.1 x.2
    obtain ⟨c, hc⟩ := (hD q P.U _ _ (hV H d q P hq d)).2 _ (fun a => (F a).pc hO (hF a)) (fun a => (F a).th q)
      (fun x h => ⟨⟨x, h⟩, hx _⟩) (fun a b y _ hy => agree hT hC hq (F a) (F b) (hF b) y hy)
    exact ⟨c, fun x h => ⟨F ⟨x, h⟩, hF _, hx _, hc _⟩⟩
  have et : ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) → ∀ c, Fund q P c → ∀ F : Frame P, Etale F.w →
      F.pl q c = F.th q := fun q _ P hq c hc F hF =>
    frame_eq hT hC hO hq hc F (hD q _ _ _ (hVF H d q P hq F hF d)).1
  have un : ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) → ∀ c c', Fund q P c → Fund q P c' → c = c' := by
    intro q _ P hq c c' hc hc'
    refine sub_eq_zero.1 ((hD q P.U _ _ (hV H d q P hq d)).1 _ fun x hx => ?_)
    obtain ⟨F, hF, hxF, e⟩ := hc x hx
    refine ⟨F.pc hO hF, hxF, ?_⟩
    rw [map_sub, sub_eq_zero]
    exact e.trans (et q P hq c' hc' F inferInstance).symm
  refine ⟨fun q P => pick (Fund q P), fun q _ => ⟨?_, ?_, ?_⟩⟩
  · intro P hq B _ I x hx w z h hw hc
    exact et q P hq _ (pick_spec (ex q P hq)) ⟨B, I, x, hx, w, z, h, hc⟩ hw
  · intro P' P φ hq
    have hq' : IsUnit (q : Γ(P'.X, ⊤)) := by simpa using hq.map φ.f.appTop.hom
    refine un q P' hq' _ _ (fun x hx => ?_) (pick_spec (ex q P' hq'))
    obtain ⟨F, hF, hxF⟩ := hG d P' x hx
    have hle : off F.B F.I ≤ (F.w ≫ φ.f) ⁻¹ᵁ P.U := fun a ha => by simpa using φ.le (F.h ha)
    refine ⟨F, hF, hxF, (pull_pull _ _ rfl _ _ _ _ _ hle _ _ _).trans ?_⟩
    exact frame_eq hT hC hO hq (pick_spec (ex q P hq))
      ⟨F.B, F.I, F.x, F.hx, F.w ≫ φ.f, F.z ≫ φ.g, hle, (F.cart.flip.paste_horiz φ.cart.flip).flip⟩
      (hD q _ _ _ (hVF H d q P' hq' F inferInstance d)).1
  · intro r hr P hq
    have : NeZero r := ⟨fun h => NeZero.ne q (zero_dvd_iff.1 (h ▸ hr))⟩
    have hr' : IsUnit (r : Γ(P.X, ⊤)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hr) hq
    let c := pick (Fund q P)
    have hc0 : pull _ (dbl.inr (opn P.U)) (tw q d) (2 * d) c.1 = 0 := c.2
    let c' : Hs r (opn P.U) (2 * d) d := ⟨red q r _ _ _ c.1, by
      change pull _ (dbl.inr _) _ _ _ = 0
      rw [pull_red, hc0, map_zero]⟩
    refine congrArg Subtype.val (un r P hr' _ c' (pick_spec (ex r P hr')) fun x hx => ?_)
    obtain ⟨F, hF, hxF, e⟩ := pick_spec (ex q P hq) x hx
    refine ⟨F, hF, hxF, Subtype.ext ?_⟩
    rw [(hT q).2.2.2 r hr F.B F.I F.x F.hx (unit_B hq F.w), ← show _ = thom d q F.B F.I F.x F.hx from e]
    exact pull_red q r _ _ _ _

end LateralTheory.CohomologicalPurity.Cl
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafExcPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem freeSq (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) (p : SimplexCategoryᵒᵖ) :
    (free R).map (P'.hom.app p) ≫ (free R).map (φ.right.app p) =
      (free R).map (φ.left.app p) ≫ (free R).map (P.hom.app p) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.comp_app, Arrow.w φ]

def LeafExcFormal : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P),
  (∀ p : SimplexCategoryᵒᵖ, IsIso (cokernel.map ((free (ZMod q)).map (P'.hom.app p)) ((free (ZMod q)).map (P.hom.app p))
    ((free (ZMod q)).map (φ.left.app p)) ((free (ZMod q)).map (φ.right.app p)) (freeSq _ φ p))) → Exc q φ

theorem freeSqSch (R : Type) [CommRing R] {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens)
    (h : U' ≤ f ⁻¹ᵁ U) :
    (free R).map (yoneda.map U'.ι) ≫ (free R).map (yoneda.map f) =
      (free R).map (yoneda.map (f.resLE U U' h)) ≫ (free R).map (yoneda.map U.ι) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι]

def LeafExcSheaf : Prop := ∀ (R : Type) [CommRing R] {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X')
  (ι : Z ⟶ X) [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U' : X'.Opens) (U : X.Opens),
  (U : Set X) = (Set.range ι)ᶜ → ∀ h : U' = f ⁻¹ᵁ U,
  IsIso (cokernel.map ((free R).map (yoneda.map U'.ι)) ((free R).map (yoneda.map U.ι))
    ((free R).map (yoneda.map (f.resLE U U' h.le))) ((free R).map (yoneda.map f)) (freeSqSch R f U' U h.le))

theorem LeafExc_of (hF : LeafExcFormal) (hS : LeafExcSheaf) : LeafExc := by
  intro _ q X' X Z f _ ι' ι _ hp U' U hU h
  refine hF q _ fun p => ?_
  exact hS (ZMod q) f ι' ι hp U' U hU h

end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

section Hoc
variable {J : Type} [SmallCategory J]

def hocF (J : Type) [SmallCategory J] : (J ⥤ PSh) ⥤ Spc :=
  flipFunctor _ _ _ ⋙ (Functor.whiskeringRight _ _ _).obj (Functor.elementsFunctor ⋙ nerveFunctor) ⋙ flipFunctor _ _ _

abbrev hoc (D : J ⥤ PSh) : Spc := (hocF J).obj D

def chn {D : J ⥤ PSh} {n : SimplexCategoryᵒᵖ} {U : Scheme.{0}ᵒᵖ} (x : ((hoc D).obj n).obj U) :
    Fin (n.unop.len + 1) ⥤ (D.flip.obj U).Elements := x

def Coc (D : J ⥤ PSh) {Y : PSh} (c : ∀ j, D.obj j ⟶ Y) : Prop := ∀ j k (f : j ⟶ k), D.map f ≫ c k = c j

def aug {D : J ⥤ PSh} {Y : PSh} (c : ∀ j, D.obj j ⟶ Y) (hc : Coc D c) : hoc D ⟶ disc.obj Y where
  app n :=
    { app := fun U => TypeCat.ofHom fun x => (c ((chn x).obj 0).1).app U ((chn x).obj 0).2
      naturality := fun U U' f => by
        ext x
        exact ConcreteCategory.congr_hom ((c ((chn x).obj 0).1).naturality f) ((chn x).obj 0).2 }
  naturality n m θ := by
    ext U x
    have g := (chn x).map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (hc _ _ g.1) U) ((chn x).obj 0).2
    refine Eq.trans ?_ h
    exact congrArg (fun y => (c ((chn x).obj (θ.unop.toOrderHom 0)).1).app U y) g.2.symm

theorem map_aug {D' D : J ⥤ PSh} {Y : PSh} (α : D' ⟶ D) (c' : ∀ j, D'.obj j ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c')
    (hc : Coc D c) (h : ∀ j, α.app j ≫ c j = c' j) : (hocF J).map α ≫ aug c hc = aug c' hc' := by
  ext n U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (h ((chn x).obj 0).1) U) ((chn x).obj 0).2

def mkChn {I : Type} [SmallCategory I] {F : J ⥤ Type} (σ : I ⥤ J) (s : ∀ i, F.obj (σ.obj i))
    (h : ∀ i k (g : i ⟶ k), F.map (σ.map g) (s i) = s k) : I ⥤ F.Elements where
  obj i := F.elementsMk (σ.obj i) (s i)
  map g := Functor.Elements.homMk (σ.map g) (h _ _ g)
  map_id i := Functor.Elements.hom_ext (σ.map_id i)
  map_comp g g' := Functor.Elements.hom_ext (σ.map_comp g g')

theorem mkChn_congr {I : Type} [SmallCategory I] {F : J ⥤ Type} (σ : I ⥤ J) {s s' : ∀ i, F.obj (σ.obj i)} (e : s = s') h h' :
    mkChn σ s h = mkChn σ s' h' := by subst e; rfl

theorem laurent_adjoin_eq_of_image_eq (D : J ⥤ PSh) {n : ℕ} (σ : Fin (n + 1) ⥤ J) (i k : Fin (n + 1)) (g : i ⟶ k) :
    D.map (σ.map (homOfLE (Fin.zero_le i))) ≫ D.map (σ.map g) = D.map (σ.map (homOfLE (Fin.zero_le k))) := by
  rw [← D.map_comp, ← σ.map_comp]; rfl

def inj (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ) (σ : Fin (n.unop.len + 1) ⥤ J) : D.obj (σ.obj 0) ⟶ (hoc D).obj n where
  app U := TypeCat.ofHom fun x => mkChn (F := D.flip.obj U) σ (fun i => (D.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)
    fun i k g => ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) x
  naturality U U' f := by
    ext x
    exact mkChn_congr (F := D.flip.obj U') σ
      (funext fun i => ConcreteCategory.congr_hom ((D.map (σ.map (homOfLE (Fin.zero_le i)))).naturality f) x)
      (fun i k g => ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U') _)
      (fun i k g => by
        have a := ConcreteCategory.congr_hom ((D.map (σ.map g)).naturality f) ((D.map (σ.map (homOfLE (Fin.zero_le i)))).app U x)
        exact a.trans (congrArg ((D.obj (σ.obj k)).map f)
          (ConcreteCategory.congr_hom (NatTrans.congr_app (laurent_adjoin_eq_of_image_eq D σ i k g) U) x)))

end Hoc

def pbRel {B G E' E : Spc} (g : G ⟶ B) (a : E' ⟶ E) (π' : E' ⟶ B) (π : E ⟶ B) (h : a ≫ π = π') :
    pullback π' g ⟶ pullback π g := pullback.map π' g π g a (𝟙 _) (𝟙 _) (by simp [h]) (by simp)

def abvRel {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (a : E' ⟶ E) (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X)
    (h : a ≫ π = π') : abv U π' ⟶ abv U π :=
  Arrow.homMk (pbRel (sch.map U.ι) a π' π h) a (pullback.lift_fst _ _ _)

def Prd (q : ℕ) {X : Scheme.{0}} (U : X.Opens) {E : Spc} (π : E ⟶ sch.obj X) {m j : ℤ} (c : Hs q (opn U) m j) : Prop :=
  ∀ n i : ℤ, Function.Bijective fun a : Ht q E n i => Hs.act q (P := abv U π) a (Hs.pull q (abvMap U π) _ _ c)

def Loc {X : Scheme.{0}} {E : Spc} (π : E ⟶ sch.obj X) : Prop :=
  ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (g : Y ⟶ X), QuasiIso ((chains R).map (pullback.snd π (sch.map g)))

def lev (n : SimplexCategoryᵒᵖ) : Arrow Spc ⥤ Arrow Spc := ((evaluation _ _).obj n ⋙ disc).mapArrow

def LeafLevel : Prop := ∀ (J : Type) [SmallCategory J] (D : J ⥤ PSh) (n : SimplexCategoryᵒᵖ),
  Nonempty (IsColimit (Cofan.mk ((hoc D).obj n) (inj D n)))

def LeafSum : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) (E : A → Spc) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ n : ℤ, Function.Bijective fun (x : H R c.pt F n) (a : A) => pull R (c.inj a) F n x

def LeafRel : Prop := ∀ (q : ℕ) (i : ℤ),
  ∃ e : ∀ (P : Arrow Spc) (n : ℤ), HK _ (cokernel ((chains (ZMod q)).map P.hom)) (tw q i) n ≃+ Hs q P n i,
    (∀ (P : Arrow Spc) (n : ℤ) (p : (chains (ZMod q)).obj (dbl P) ⟶ cokernel ((chains (ZMod q)).map P.hom)),
      (chains _).map (dbl.inl P) ≫ p = cokernel.π _ → (chains _).map (dbl.inr P) ≫ p = 0 →
      ∀ x, (e P n x).1 = HK.pull _ p (tw q i) n x)

def LeafExcLevel : Prop := A3 → ∀ (q : ℕ) (P' P : Arrow Spc) (φ : P' ⟶ P), (∀ n, Exc q ((lev n).map φ)) → Exc q φ

def LeafPrdLevel : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) (U : X.Opens) (E : Spc) (π : E ⟶ sch.obj X) (m j : ℤ)
  (c : Hs q (opn U) m j), (∀ n, Prd q U (E := disc.obj (E.obj n)) (disc.map (π.app n)) c) → Prd q U π c

def LeafActNat : Prop := DivisorNaturality → ∀ (q : ℕ) [NeZero q] (P' P : Arrow Spc) (φ : P' ⟶ P) (n m i j : ℤ) (a : Ht q P.right n i)
  (b : Hs q P m j), Hs.pull q φ _ _ (Hs.act q a b) = Hs.act q (pull _ φ.right _ _ a) (Hs.pull q φ _ _ b)

def LeafHsSum : Prop := ∀ (q : ℕ) (X : Scheme.{0}) (U : X.Opens) (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ (π : c.pt ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X)
  (h : ∀ a, disc.map (c.inj a) ≫ disc.map π = disc.map (π' a)) (n i : ℤ),
  Function.Bijective fun (x : Hs q (abv U (E := disc.obj c.pt) (disc.map π)) n i) (a : A) =>
    Hs.pull q (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)) n i x

def LeafFstHoc : Prop := A3 → ∀ (R : Type) [CommRing R] (F : Shv R) (J : Type) [SmallCategory J] (D : J ⥤ PSh) (Y G : PSh)
  (g : G ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc : Coc D c), (∀ j, Eqv R (pullback.fst (disc.map (c j)) (disc.map g)) F) →
  Eqv R (pullback.fst (aug c hc) (disc.map g)) F

def LeafRelHoc : Prop := A3 → ∀ (R : Type) [CommRing R] (F : Shv R) (J : Type) [SmallCategory J] (D' D : J ⥤ PSh) (α : D' ⟶ D)
  (Y G : PSh) (g : G ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y) (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j)) h',
  (∀ j, Eqv R (pbRel (disc.map g) (disc.map (α.app j)) (disc.map (c' j)) (disc.map (c j)) (h j)) F) →
  Eqv R (pbRel (disc.map g) ((hocF J).map α) (aug c' hc') (aug c hc) h') F

def LeafExcHoc : Prop := A3 → ∀ (q : ℕ) (J : Type) [SmallCategory J] (D' D : J ⥤ PSh) (α : D' ⟶ D) (X : Scheme.{0})
  (U : X.Opens) (c' : ∀ j, D'.obj j ⟶ yoneda.obj X) (c : ∀ j, D.obj j ⟶ yoneda.obj X) (hc' : Coc D' c') (hc : Coc D c)
  (h : ∀ j, disc.map (α.app j) ≫ disc.map (c j) = disc.map (c' j)) h',
  (∀ j, Exc q (abvRel U (disc.map (α.app j)) (disc.map (c' j)) (disc.map (c j)) (h j))) →
  Exc q (abvRel U ((hocF J).map α) (aug c' hc') (aug c hc) h')

def LeafPrdHoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (J : Type) [SmallCategory J] (D : J ⥤ PSh) (X : Scheme.{0}) (U : X.Opens)
  (c : ∀ j, D.obj j ⟶ yoneda.obj X) (hc : Coc D c) (m k : ℤ) (b : Hs q (opn U) m k),
  (∀ j, Prd q U (E := disc.obj (D.obj j)) (disc.map (c j)) b) → Prd q U (aug c hc) b

def LeafLoc : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j), Loc (aug _ hc)

def LeafLocExc : Prop := A1 → ∀ (q : ℕ) (X : Scheme.{0}) (U : X.Opens) (E : Spc) (π : E ⟶ sch.obj X), Loc π → Exc q (abvMap U π)

def LeafPush : Prop := ∀ (J' J : Type) [SmallCategory J'] [SmallCategory J] (D' : J' ⥤ PSh) (D : J ⥤ PSh) (G : J' ⥤ J)
  (α : D' ⟶ G ⋙ D) (Y' Y : PSh) (f : Y' ⟶ Y) (c' : ∀ j, D'.obj j ⟶ Y') (c : ∀ j, D.obj j ⟶ Y) (hc' : Coc D' c') (hc : Coc D c),
  (∀ j, α.app j ≫ c (G.obj j) = c' j ≫ f) → ∃ b : hoc D' ⟶ hoc D, b ≫ aug c hc = aug c' hc' ≫ disc.map f

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafIndExcPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def LeafNbhdExc : Prop := A1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A),
  Nbhd φ I → IsUnit (q : A) → ∀ h, Exc q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h)

def LeafHsCont : Prop := A1 → A4 → B1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A),
  I.FG → IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ,
  (∀ x : Hs q (opn (off B (I.map φ))) n i, ∃ j h, ∃ y,
    Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = x) ∧
  (∀ j h y, Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = 0 →
    ∃ (k : J) (f : j ⟶ k) (h' : _), Hs.pull q (opnMap (Spec.map (D.map f)) (off (D.obj k) (I.map (s.app k).hom))
      (off (D.obj j) (I.map (s.app j).hom)) h') n i y = 0)

theorem off_map {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (J : Ideal R) :
    off S (J.map ψ) = Spec.map (CommRingCat.ofHom ψ) ⁻¹ᵁ off R J := by
  ext x
  show ¬ ((Ideal.map ψ J : Set S) ⊆ (x : PrimeSpectrum S).asIdeal) ↔
    ¬ ((J : Set R) ⊆ (PrimeSpectrum.comap ψ x).asIdeal)
  simp only [SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap]
  exact Iff.rfl

theorem dbl.inl_map' {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem dbl.map_comp' {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) :
    dbl.map (φ ≫ ψ) = dbl.map φ ≫ dbl.map ψ := by
  set_option synthInstance.maxHeartbeats 200000 in
  apply pushout.hom_ext
  · change dbl.inl P'' ≫ dbl.map (φ ≫ ψ) = dbl.inl P'' ≫ dbl.map φ ≫ dbl.map ψ
    rw [dbl.inl_map', ← Category.assoc, dbl.inl_map', Category.assoc, dbl.inl_map', Arrow.comp_right,
      Category.assoc]
  · change dbl.inr P'' ≫ dbl.map (φ ≫ ψ) = dbl.inr P'' ≫ dbl.map φ ≫ dbl.map ψ
    rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, Arrow.comp_right,
      Category.assoc]

theorem Hs.pull_comp' (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.pull q (φ ≫ ψ) n i x = Hs.pull q φ n i (Hs.pull q ψ n i x) := by
  apply Subtype.ext
  change GlobalTheory.EtC.pull _ (dbl.map (φ ≫ ψ)) _ n x.1 = GlobalTheory.EtC.pull _ (dbl.map φ) _ n (GlobalTheory.EtC.pull _ (dbl.map ψ) _ n x.1)
  rw [dbl.map_comp', pull_comp]

theorem opnMap_comp {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens)
    (U : X.Opens) (h1 : U'' ≤ f ⁻¹ᵁ U') (h2 : U' ≤ g ⁻¹ᵁ U) (h : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap (f ≫ g) U'' U h = opnMap f U'' U' h1 ≫ opnMap g U' U h2 := by
  apply Arrow.hom_ext
  · change sch.map _ = sch.map _ ≫ sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map _ = sch.map _ ≫ sch.map _
    rw [Functor.map_comp]

theorem opnMap_congr {X' X : Scheme.{0}} {f g : X' ⟶ X} (e : f = g) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U)
    (h' : U' ≤ g ⁻¹ᵁ U) : opnMap f U' U h = opnMap g U' U h' := by
  subst e; rfl

theorem leafIndExc_of (hN : LeafNbhdExc) (hC : LeafHsCont) : LeafIndExc := by
  intro a1 a4 b1 q A B _ _ φ I hI hInd hq h n i
  obtain ⟨J, _, _, D, s, t, ⟨hcol⟩, hst⟩ := hInd
  have hs : ∀ j, Nbhd (A := A) (s.app j).hom I := fun j => (hst j).1
  have he : ∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ := fun j => (hst j).2
  obtain ⟨hsurj, hinj⟩ := hC a1 a4 b1 q φ I hI hq J D s t hcol he n i
  have hsle : ∀ j, off (D.obj j) (I.map (s.app j).hom) ≤ Spec.map (s.app j) ⁻¹ᵁ off A I := fun j =>
    le_of_eq (off_map (s.app j).hom I)
  have hE : ∀ j, Function.Bijective (Hs.pull q (opnMap (Spec.map (s.app j)) _ _ (hsle j)) n i) := fun j =>
    hN a1 q (s.app j).hom I (hs j) hq (hsle j) n i
  have hB : ∀ j, off B (I.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom) := fun j => by
    intro x hx
    have hx' := h hx
    rw [← he j, Spec.map_comp] at hx'
    have e := off_map (s.app j).hom I
    simp only [CommRingCat.ofHom_hom] at e
    rw [e]
    exact hx'
  have hfac : ∀ j (h1 : off B (I.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom)),
      opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h =
        opnMap (Spec.map (t.app j)) _ _ h1 ≫ opnMap (Spec.map (s.app j)) _ _ (hsle j) := by
    intro j h1
    have hcomp : off B (I.map φ) ≤ (Spec.map (t.app j) ≫ Spec.map (s.app j)) ⁻¹ᵁ off A I := by
      rw [← Spec.map_comp, he j]; exact h
    exact (opnMap_congr (by rw [← Spec.map_comp, he j]) _ _ _ hcomp).trans
      (opnMap_comp _ _ _ _ _ h1 (hsle j) hcomp)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    rw [hfac j (hB j), Hs.pull_comp'] at hz
    obtain ⟨k, f, h', hk⟩ := hinj j (hB j) _ hz
    have hn : s.app k = s.app j ≫ D.map f := by
      have := s.naturality f
      simpa using this
    have hk' : opnMap (Spec.map (s.app k)) _ _ (hsle k) =
        opnMap (Spec.map (D.map f)) _ _ h' ≫ opnMap (Spec.map (s.app j)) _ _ (hsle j) := by
      have hcomp : off (D.obj k) (I.map (s.app k).hom) ≤ (Spec.map (D.map f) ≫ Spec.map (s.app j)) ⁻¹ᵁ off A I := by
        rw [← Spec.map_comp, ← hn]; exact hsle k
      exact (opnMap_congr (by rw [← Spec.map_comp, ← hn]) _ _ _ hcomp).trans
        (opnMap_comp _ _ _ _ _ h' (hsle j) hcomp)
    apply (injective_iff_map_eq_zero _).1 (hE k).1
    rw [hk', Hs.pull_comp', hk]
  · intro x
    obtain ⟨j, h1, y, hy⟩ := hsurj x
    obtain ⟨z, hz⟩ := (hE j).2 y
    exact ⟨z, by rw [hfac j h1, Hs.pull_comp', hz, hy]⟩

end LateralTheory.CohomologicalPurity
end
end
