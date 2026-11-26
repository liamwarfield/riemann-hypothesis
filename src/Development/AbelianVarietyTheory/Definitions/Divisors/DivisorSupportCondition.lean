module

public import GroundTheory.ProfiniteCohomology.CupProducts
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.BlockGLMap
public import GroundTheory.FunctionField.PlaceBridge
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

def A1 : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [QuasiIso f] (F : Shv R) (n : ℤ),
  Function.Bijective (HK.pull R f F n)

def A2 : Prop := ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] [Surjective f] (F : Shv R), Eqv R (cechAug f) F

def A3 : Prop := ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R),
  (∀ n, Eqv R (disc.map (f.app n)) F) → Eqv R f F

def A4 : Prop := ∀ (R : Type) [CommRing R] {U V E U' V' E' : Spc} (f : U ⟶ E) (g : V ⟶ E) (f' : U' ⟶ E') (g' : V' ⟶ E')
  (p : E ⟶ E') (u : U ⟶ U') (v : V ⟶ V') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (F : Shv R),
  Cover2 R f g → Cover2 R f' g' → Eqv R u F → Eqv R v F → Eqv R (pullback.map f g f' g' u v p hu hv) F → Eqv R p F

def A5 : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ), 0 < n → ∀ x : H R (sch.obj X) F n,
  ∃ (Y : Scheme.{0}) (f : Y ⟶ X), Etale f ∧ Surjective f ∧ pull R (sch.map f) F n x = 0

def DivisorNaturality : Prop := ∀ (q : ℕ) [NeZero q],
  (∀ {E E' : Spc} (f : E ⟶ E') {n m i j : ℤ} (a : Ht q E' n i) (b : Ht q E' m j),
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a) (pull _ f _ _ b)) ∧
  (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E) ∧
  (∀ {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' → pull _ f _ _ (c1 q L) = c1 q (f ≫ L)) ∧
  ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) →
    pull _ (sch.map f) _ _ (kum q u) = kum q (Units.map f.appTop.hom.toMonoidHom u)

def DivisorRingCompatibility : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc),
  (Inv q E → ∀ {n i : ℤ} (a : Ht q E n i), cup q (one q E) a = a.cast (by ring) (by ring)) ∧
  (∀ {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l),
    cup q (cup q a b) c = (cup q a (cup q b c)).cast (by ring) (by ring)) ∧
  ∀ {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), cup q a b = (n * m).negOnePow • (cup q b a).cast (by ring) (by ring)

def DivisorSupportCondition : Prop := ∀ (q : ℕ) [NeZero q] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 (ZMod q) f g →
  ∀ {n m i j : ℤ} (a : Ht q E n i) (b : Ht q E m j), pull _ f _ _ a = 0 → pull _ g _ _ b = 0 → cup q a b = 0

def DivisorAdditivity : Prop := ∀ (q : ℕ) [NeZero q],
  (∀ {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E →
    (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) → c1 q N = c1 q L + c1 q M) ∧
  ∀ {X : Scheme.{0}} (u v : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → kum q (u * v) = kum q u + kum q v ∧ kum q (u ^ q) = 0

def A7 : Prop := ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1, ∀ (K : Cx R) (n : ℤ),
    Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
    Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
    Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))

def A8 : Prop := ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (E : Spc) (F : Shv S) (n : ℤ),
  Function.Bijective (restrH φ E F n)

def A9 : Prop := ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E : Spc) (n : ℤ), n < 0 → Subsingleton (H R E F n)) ∧
  ∃ e : ∀ X : Scheme.{0}, Sec F X ≃+ H R (sch.obj X) F 0,
    (∀ {Y X : Scheme.{0}} (f : Y ⟶ X) (s : Sec F X), pull R (sch.map f) F 0 (e X s) = e Y (Sec.res f s)) ∧
    ∀ (X : Scheme.{0}) (s : Sec F X), ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = e X s ∧
      ev α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s

def A10 : Prop := ∀ (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G),
  (∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) →
  ∀ n, Function.Bijective (HK.post R ((chains R).obj E) φ n)

def A11 : Prop := ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ E : Spc,
  (∀ {n m i j : ℤ} (a : Ht Q E n i) (b : Ht Q E m j), red Q q E _ _ (cup Q a b) = cup q (red Q q E _ _ a) (red Q q E _ _ b)) ∧
  (Inv Q E → red Q q E _ _ (one Q E) = one q E ∧ ∀ L : E ⟶ ofCat (glCat 1), red Q q E _ _ (c1 Q L) = c1 q L) ∧
  (∀ (n i : ℤ) (a : Ht Q E n i), red Q Q E n i a = a) ∧
  ∀ r : ℕ, r ∣ q → ∀ (n i : ℤ) (a : Ht Q E n i), red q r E n i (red Q q E n i a) = red Q r E n i a

def B1 : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c →
  ∀ n i : ℤ,
  (∀ x : Ht q (sp c.pt) n i, IsUnit (q : c.pt) → ∃ j y, pull _ (spMap (c.ι.app j).hom) _ _ y = x) ∧
  ∀ j (y : Ht q (sp (D.obj j)) n i), IsUnit (q : D.obj j) → pull _ (spMap (c.ι.app j).hom) _ _ y = 0 →
    ∃ (k : J) (f : j ⟶ k), pull _ (spMap (D.map f).hom) _ _ y = 0

def B2 : Prop := ∀ (R : Type) [CommRing R] (A : Type) [CommRing A], SH A → ∀ (F : Shv R) (n : ℤ), 0 < n →
  Subsingleton (H R (sp A) F n)

def B3 : Prop := ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f]
  [QuasiSeparated f], IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ,
  (∀ (A : Type) [CommRing A] (s : Spec (CommRingCat.of A) ⟶ S), SH A →
    Eqv _ (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)) → Eqv _ (sch.map f) (tw q i)

def B4 : Prop := ∀ (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsIntegralHom f] [Surjective f], IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ,
  Eqv _ (cechAug f) (tw q i)

def B5 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A], AIC A → IsUnit (q : A) → Acyc q (sp A)

def DivisorPicardCompatibility : Prop := ∀ (A : Type) [CommRing A], Nonempty (H ℤ (sp A) Gm 1 ≃+ Additive (CommRing.Pic A))

def B6h1 : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ u : Aˣ, ∃ v, u = v ^ q) →
  (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → Subsingleton (Ht q (sp A) 1 1)

def B7 : Prop := ∀ (q : ℕ) [NeZero q] (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω], IsUnit (q : K) → ∀ (i : ℕ)
  (M : Rep (ZMod q) (Ω ≃ₐ[K] Ω)) [GroundTheory.ProfCoh.IsDiscreteRep M] (ζ : Ω), IsPrimitiveRoot ζ q → ∀ b : Module.Basis Unit (ZMod q) M,
  (∀ (σ : Ω ≃ₐ[K] Ω) (a : ℕ), σ ζ = ζ ^ a → M.ρ σ (b ()) = ((a : ZMod q) ^ i) • b ()) → ∀ n : ℕ,
  Nonempty (Ht q (sp K) n i ≃+ GroundTheory.ProfCoh.cohomology M n)

def C1 : Prop := ∀ (q : ℕ) [NeZero q] (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra (RatFunc k) K]
  [Algebra.IsAlgebraic (RatFunc k) K], IsUnit (q : K) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp K) n i)

def C2 : Prop := ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
  [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp B) n i)

def C3 : Prop := ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  ∀ (B : Type) [CommRing B] [Algebra (Polynomial T) B] [Algebra.Etale (Polynomial T) B] [Algebra T B]
    [IsScalarTower T (Polynomial T) B] (i : ℤ),
  Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := B)).toRingHom) (tw q i)

def C4 : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → ∀ i : ℤ,
  Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i)

def C5 : Prop := ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ,
  (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧ Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q)

def D1 : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)), Inv q E → ∀ n i : ℤ,
  Function.Bijective fun a : ∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ)) =>
    ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i)

def D2 : Prop := ∀ (q : ℕ) [NeZero q] (k : ℕ), 0 < k →
  ∃ s : ∀ {E : Spc} {N : ℕ}, (E ⟶ ofCat (glCat N)) → Ht q E (2 * k) k,
    (∀ {E E' : Spc} {N} (f : E ⟶ E') (V : E' ⟶ ofCat (glCat N)), Inv q E' → pull _ f _ _ (s V) = s (f ≫ V)) ∧
    (∀ {E : Spc} {a b} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)), Inv q E → s (bsumOf V W) = s V + s W) ∧
    ∀ {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → s L = cpow q (c1 q L) k

def D3 : Prop := ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ),
  (∀ c : groupHomology.cycles (Rep.trivial R Γ R) m, ∃ z, IsSlant R X (groupHomology.iCycles (Rep.trivial R Γ R) m c) z) ∧
  ∀ (F : Shv R) (n : ℤ), IsSlantMap R Γ X F m n (slantR R Γ X F m n)

def E1 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], IsUnit (q : A) → ∀ i : ℤ,
  Eqv _ (spMap (Ideal.Quotient.mk I)) (tw q i)

def E2 : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p] (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))) (tw q i)

def E3 : Prop := ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
  ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of T)) [Smooth p] (i : ℤ),
  Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap T (FractionRing T)))))) (tw q i)

def E4 : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (n i : ℤ), Finite (Ht q (sch.obj X) n i)

def E6 : Prop := ∀ (q : ℕ) [NeZero q] {X Z S : Scheme.{0}} (p : X ⟶ S) (ι : Z ⟶ X) [IsClosedImmersion ι] (d e : ℕ)
  [SmoothOfRelativeDimension (e + d) p] [SmoothOfRelativeDimension e (ι ≫ p)], IsUnit (q : Γ(S, ⊤)) →
  ∀ U : X.Opens, (U : Set X) = (Set.range ι)ᶜ → ∀ n i : ℤ,
  (n < 2 * d - 1 → Function.Bijective (pull _ (sch.map U.ι) (tw q i) n)) ∧
  (n < 2 * d → Function.Injective (pull _ (sch.map U.ι) (tw q i) n))

def E8 : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p],
  ∃ tr : Ht q (sch.obj X) (2 * d) d ≃+ ZMod q, ∀ (n i : ℤ) (φ : Ht q (sch.obj X) (2 * d - n) (d - i) →+ ZMod q),
    ∃! a : Ht q (sch.obj X) n i, ∀ b, φ b = tr ((cup q a b).cast (by ring) (by ring))

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
set_option autoImplicit false

noncomputable section

open scoped IntermediateField Polynomial

namespace GlobalTheory.Nef

def IsFF (k F : Type) [Field k] [Field F] [Algebra k F] : Prop :=
  ∃ t : F, Transcendental k t ∧ FiniteDimensional k⟮t⟯ F

def Place (k F : Type) [Field k] [Field F] [Algebra k F] : Type :=
  {v : Valuation F (WithZero (Multiplicative ℤ)) //
    Function.Surjective v ∧ ∀ c : k, c ≠ 0 → v (algebraMap k F c) = 1}

variable {k F : Type} [Field k] [Field F] [Algebra k F]

abbrev Place.O (v : Place k F) : ValuationSubring F := v.1.valuationSubring

def ord (v : Place k F) (x : F) : ℤ := -WithZero.log (v.1 x)

def nrm {n : ℕ} (v : Place k F) (x : Fin n → F) : WithZero (Multiplicative ℤ) :=
  Finset.univ.sup fun i => v.1 (x i)

def ordVec {n : ℕ} (v : Place k F) (x : Fin n → F) : ℤ := -WithZero.log (nrm v x)

def Unimod {n : ℕ} (v : Place k F) (g : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ i j, v.1 (g i j) ≤ 1) ∧ v.1 g.det = 1

def admitted {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ v, (g v).det ≠ 0) ∧ {v | ¬ Unimod v (g v)}.Finite

def deg [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) : ℤ := ∑ᶠ v, ord v (g v).det

def degLine [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) (w : Fin n → F) : ℤ :=
  ∑ᶠ v, ordVec v ((g v).mulVec w)

def IsRes {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F) : Prop :=
  ∀ p x, p.1 (algebraMap F E x) ≤ 1 ↔ (ρ p).1 x ≤ 1

def pullAd {n : ℕ} {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F)
    (g : Place k F → Matrix (Fin n) (Fin n) F) : Place k E → Matrix (Fin n) (Fin n) E :=
  fun p => (g (ρ p)).map (algebraMap F E)

def LinesLE [IsAlgClosed k] {n : ℕ} (g : Place k F → Matrix (Fin n) (Fin n) F) (b : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E]
    (ρ : Place k E → Place k F), IsRes ρ → ∀ w : Fin n → E, w ≠ 0 →
      (degLine (pullAd ρ g) w : ℝ) ≤ b * Module.finrank F E

def IsRat (φ : PowerSeries F) : Prop :=
  ∃ p q : F[X], q ≠ 0 ∧ (q : PowerSeries F) * φ = (p : PowerSeries F)

def hankel (c : ℕ → F) (n : ℕ) : F := (Matrix.of fun i j : Fin (n + 1) => c (i + j)).det

def sc (v : Place k F) (u : F) : PowerSeries v.O →+* PowerSeries F :=
  (PowerSeries.rescale u).comp (PowerSeries.map v.O.subtype)

namespace Lib

open scoped WithZero
open IsDedekindDomain GroundTheory.FunctionField


section Line

variable (k)


variable {k}

end Line

section Product

end Product

end Lib

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff ENNReal

namespace GlobalTheory.ChartGlue

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {ι : Type*}

def transDet (e e' : OpenPartialHomeomorph X (V n)) (y : X) : ℂ :=
  (fderiv ℂ (e' ∘ e.symm) (e y)).det

theorem isOpen_over (e : OpenPartialHomeomorph X (V n)) {S : Set X} (hS : IsOpen S) :
    IsOpen (e.target ∩ e.symm ⁻¹' S) := e.isOpen_inter_preimage_symm hS

theorem mem_over (e : OpenPartialHomeomorph X (V n)) {S : Set X} {y : X} (hy : y ∈ e.source)
    (hS : y ∈ S) : e y ∈ e.target ∩ e.symm ⁻¹' S :=
  ⟨e.map_source hy, by rwa [mem_preimage, e.left_inv hy]⟩

theorem contDiffOn_real {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) : ContDiffOn ℝ ∞ g U :=
  (contDiffOn_of_differentiableOn n g U hU hg).restrict_scalars ℝ

theorem contDiffOn_log_normSq {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (h0 : ∀ v ∈ U, g v ≠ 0) :
    ContDiffOn ℝ ∞ (fun v => Real.log (‖g v‖ ^ 2)) U :=
  ((contDiffOn_real hU hg).norm_sq ℂ).log fun v hv => pow_ne_zero _ (norm_ne_zero_iff.2 (h0 v hv))

section Measure

variable [MeasurableSpace X]

def chartMeas (e : OpenPartialHomeomorph X (V n)) (ρ : X → ℝ≥0∞) : Measure X :=
  Measure.map e.symm ((volume.restrict e.target).withDensity (ρ ∘ e.symm))

def glueMeas (e : ι → OpenPartialHomeomorph X (V n)) (ρ : ι → X → ℝ≥0∞) : Measure X :=
  ⨆ i, chartMeas (e i) (ρ i)

variable [BorelSpace X]

theorem chartMeas_apply (e : OpenPartialHomeomorph X (V n)) (ρ : X → ℝ≥0∞) {A : Set X}
    (hA : MeasurableSet A) : chartMeas e ρ A = ∫⁻ v in e '' (e.source ∩ A), ρ (e.symm v) := by
  have h : AEMeasurable e.symm ((volume.restrict e.target).withDensity (ρ ∘ e.symm)) :=
    (e.continuousOn_symm.aemeasurable e.open_target.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  rw [chartMeas, Measure.map_apply_of_aemeasurable h hA, withDensity_apply',
    Measure.restrict_restrict' e.open_target.measurableSet, e.image_source_inter_eq', inter_comm]
  rfl

theorem chartMeas_apply_of_subset (e : OpenPartialHomeomorph X (V n)) (ρ : X → ℝ≥0∞) {A : Set X}
    (hA : MeasurableSet A) (h : A ⊆ e.source) :
    chartMeas e ρ A = ∫⁻ v in e '' A, ρ (e.symm v) := by
  rw [chartMeas_apply e ρ hA, inter_eq_right.2 h]

theorem measurableSet_image (e : OpenPartialHomeomorph X (V n)) {A : Set X}
    (hA : MeasurableSet A) (h : A ⊆ e.source) : MeasurableSet (e '' A) := by
  have hm : Measurable (e.target.restrict e.symm) :=
    (continuousOn_iff_continuous_restrict.1 e.continuousOn_symm).measurable
  have := e.open_target.measurableSet.subtype_image (hm hA)
  rw [← inter_eq_right.2 h, e.image_source_inter_eq']
  convert this using 1
  ext v
  exact ⟨fun hv => ⟨⟨v, hv.1⟩, hv.2, rfl⟩, by rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩⟩

theorem chartMeas_eq (e e' : OpenPartialHomeomorph X (V n)) {ρ ρ' : X → ℝ≥0∞}
    (hd : DifferentiableOn ℂ (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source)) {A : Set X}
    (hA : MeasurableSet A) (h : A ⊆ e.source) (h' : A ⊆ e'.source)
    (hρ : ∀ y ∈ A, ρ y = ENNReal.ofReal (‖transDet e e' y‖ ^ 2) * ρ' y) :
    chartMeas e ρ A = chartMeas e' ρ' A := by
  have hm := measurableSet_image e hA h
  have him : e' '' A = (e' ∘ e.symm) '' (e '' A) := by
    rw [image_image]
    exact image_congr fun y hy => by simp only [Function.comp_apply, e.left_inv (h hy)]
  have hinj : InjOn (e' ∘ e.symm) (e '' A) := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hyz
    simp only [Function.comp_apply, e.left_inv (h hy), e.left_inv (h hz)] at hyz
    rw [e'.injOn (h' hy) (h' hz) hyz]
  have hder : ∀ v ∈ e '' A, HasFDerivWithinAt (e' ∘ e.symm)
      ((fderiv ℂ (e' ∘ e.symm) v).restrictScalars ℝ) (e '' A) v := by
    rintro _ ⟨y, hy, rfl⟩
    exact ((hd.differentiableAt ((isOpen_over e e'.open_source).mem_nhds
      (mem_over e (h hy) (h' hy)))).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [chartMeas_apply_of_subset e ρ hA h, chartMeas_apply_of_subset e' ρ' hA h', him,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hm hder hinj]
  refine setLIntegral_congr_fun hm ?_
  rintro _ ⟨y, hy, rfl⟩
  have hdet : ((fderiv ℂ (e' ∘ e.symm) (e y)).restrictScalars ℝ).det =
      Algebra.norm ℝ (transDet e e' y) :=
    LinearMap.det_restrictScalars (f := (fderiv ℂ (e' ∘ e.symm) (e y) : V n →ₗ[ℂ] V n))
  simp only [Function.comp_apply, e.left_inv (h hy), e'.left_inv (h' hy), hρ y hy, hdet]
  rw [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]

variable [SecondCountableTopology X]

theorem iSup_apply_of_compat (μ : ι → Measure X) (S : ι → Set X) (hS : ∀ i, IsOpen (S i))
    (h0 : ∀ i A, MeasurableSet A → μ i A = μ i (S i ∩ A))
    (hc : ∀ i j A, MeasurableSet A → A ⊆ S i → A ⊆ S j → μ i A = μ j A)
    (i : ι) {A : Set X} (hA : MeasurableSet A) (hAi : A ⊆ S i) : (⨆ j, μ j) A = μ i A := by
  obtain ⟨T, hT, hTS⟩ := TopologicalSpace.isOpen_iUnion_countable S hS
  obtain ⟨f, hf⟩ := (hT.insert i).exists_eq_range (insert_nonempty _ _)
  have hcov (j : ι) : S j ⊆ ⋃ m, disjointed (S ∘ f) m := by
    rw [iUnion_disjointed]
    intro y hy
    obtain ⟨l, hl, hy⟩ := mem_iUnion₂.1 (hTS.ge (mem_iUnion.2 ⟨j, hy⟩))
    obtain ⟨m, rfl⟩ := hf.le (mem_insert_of_mem _ hl)
    exact mem_iUnion.2 ⟨m, hy⟩
  have hD := MeasurableSet.disjointed (f := S ∘ f) fun m => (hS _).measurableSet
  let ν : Measure X := Measure.sum fun m => (μ (f m)).restrict (disjointed (S ∘ f) m)
  have hν (j : ι) (B : Set X) (hB : MeasurableSet B) (hBj : B ⊆ S j) : ν B = μ j B := by
    rw [Measure.sum_apply _ hB]
    conv_rhs => rw [← inter_eq_left.2 (hBj.trans (hcov j)), inter_iUnion,
      measure_iUnion ((disjoint_disjointed _).mono fun _ _ h =>
        h.mono inter_subset_right inter_subset_right) fun m => hB.inter (hD m)]
    refine tsum_congr fun m => ?_
    rw [Measure.restrict_apply hB]
    exact hc _ _ _ (hB.inter (hD m)) (inter_subset_right.trans (disjointed_subset (S ∘ f) m))
      (inter_subset_left.trans hBj)
  refine le_antisymm ?_ (Measure.le_iff'.1 (le_iSup μ i) A)
  rw [← hν i A hA hAi]
  refine Measure.le_iff'.1 (iSup_le fun j => Measure.le_iff.2 fun B hB => ?_) A
  rw [h0 j B hB, ← hν j _ ((hS j).measurableSet.inter hB) inter_subset_left]
  exact measure_mono inter_subset_right

theorem ext_of_cover {μ ν : Measure X} (S : ι → Set X) (hS : ∀ i, IsOpen (S i))
    (hc : ∀ y, ∃ i, y ∈ S i) (h : ∀ i A, MeasurableSet A → A ⊆ S i → μ A = ν A) : μ = ν := by
  obtain ⟨T, hT, hTS⟩ := TopologicalSpace.isOpen_iUnion_countable S hS
  refine Measure.ext_of_biUnion_eq_univ hT (hTS.trans (iUnion_eq_univ_iff.2 hc)) fun i _ => ?_
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  exact h i _ (hA.inter (hS i).measurableSet) inter_subset_right

theorem glueMeas_apply (e : ι → OpenPartialHomeomorph X (V n)) (ρ : ι → X → ℝ≥0∞)
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    (hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y)
    (i : ι) {A : Set X} (hA : MeasurableSet A) (h : A ⊆ (e i).source) :
    glueMeas e ρ A = chartMeas (e i) (ρ i) A :=
  iSup_apply_of_compat _ (fun i => (e i).source) (fun i => (e i).open_source)
    (fun i A hA => by
      rw [chartMeas_apply _ _ hA, chartMeas_apply_of_subset _ _
        ((e i).open_source.measurableSet.inter hA) inter_subset_left])
    (fun i j _ hA h h' => chartMeas_eq _ _ (hd i j) hA h h' fun y hy => hρ i j y (h hy) (h' hy))
    i hA h

end Measure

theorem differentiableOn_prod {κ : Type*} [Fintype κ] {f : κ → V n → ℂ} {U : Set (V n)}
    (h : ∀ a, DifferentiableOn ℂ (f a) U) : DifferentiableOn ℂ (fun v => ∏ a, f a v) U := by
  have := Finset.prod_induction (s := Finset.univ) f (fun g => DifferentiableOn ℂ g U)
    (fun _ _ => DifferentiableOn.mul) (differentiableOn_const 1) fun a _ => h a
  exact this.congr fun v _ => (Finset.prod_apply _ _ _).symm

theorem log_normSq_prod_zpow {κ : Type*} [Fintype κ] (g : κ → ℂ) (hg : ∀ a, g a ≠ 0) (m : κ → ℤ) :
    Real.log (‖∏ a, g a ^ m a‖ ^ 2) = ∑ a, m a * Real.log (‖g a‖ ^ 2) := by
  rw [norm_prod, ← Finset.prod_pow, Real.log_prod fun a _ =>
    pow_ne_zero _ (norm_ne_zero_iff.2 (zpow_ne_zero _ (hg a)))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [norm_zpow, Real.log_pow, Real.log_pow, Real.log_zpow]
  ring

variable [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

def freeAtlas (e : ι → OpenPartialHomeomorph X (V n)) (cover : ∀ y, ∃ i, y ∈ (e i).source)
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) (ovl e i j))
    {κ : Type*} [Fintype κ] [DecidableEq κ] (g : κ → ι → ι → X → ℂ)
    (holo_g : ∀ a i j, DifferentiableOn ℂ (g a i j ∘ (e i).symm) (ovl e i j))
    (g_ne : ∀ a i j y, y ∈ (e i).source → y ∈ (e j).source → g a i j y ≠ 0)
    (g_cocycle : ∀ a i j k y, y ∈ (e i).source → y ∈ (e j).source → y ∈ (e k).source →
      g a i k y = g a i j y * g a j k y)
    (ph : κ → ι → X → ℝ) (smooth_ph : ∀ a i, ContDiffOn ℝ ∞ (ph a i ∘ (e i).symm) (e i).target)
    (ph_trans : ∀ a i j y, y ∈ (e i).source → y ∈ (e j).source →
      ph a j y = ph a i y - Real.log (‖g a i j y‖ ^ 2))
    (a₀ : κ) (g_kap : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      g a₀ i j y = transDet (e i) (e j) y) : WeightedAtlas n X ι (κ → ℤ) where
  chart := e
  pick y := (cover y).choose
  mem_pick y := (cover y).choose_spec
  holo_trans := hd
  g m i j y := ∏ a, g a i j y ^ m a
  holo_g m i j := differentiableOn_prod (f := fun a v => g a i j ((e i).symm v) ^ m a)
    fun a => (holo_g a i j).zpow (Or.inl fun v hv => g_ne a i j _ ((e i).map_target hv.1) hv.2)
  g_ne m i j y hi hj := Finset.prod_ne_zero_iff.2 fun a _ => zpow_ne_zero _ (g_ne a i j y hi hj)
  g_cocycle m i j k y hi hj hk := by
    simp only [fun a => g_cocycle a i j k y hi hj hk, mul_zpow, Finset.prod_mul_distrib]
  g_add m m' i j y hi hj := by
    simp only [Pi.add_apply, fun a => zpow_add₀ (g_ne a i j y hi hj), Finset.prod_mul_distrib]
  ph m i y := ∑ a, m a * ph a i y
  smooth_ph m i := ContDiffOn.sum (f := fun a v => m a * ph a i ((e i).symm v))
    fun a _ => contDiffOn_const.mul (smooth_ph a i)
  ph_add m m' i y _ := by simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  ph_trans m i j y hi hj := by
    rw [log_normSq_prod_zpow _ fun a => g_ne a i j y hi hj, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [ph_trans a i j y hi hj, mul_sub]
  kap := Pi.single a₀ 1
  g_kap i j y hi hj := by
    rw [Fintype.prod_eq_single a₀ fun a ha => by rw [Pi.single_eq_of_ne ha, zpow_zero],
      Pi.single_eq_same, zpow_one]
    exact g_kap i j y hi hj
  mu := glueMeas e fun i y => ENNReal.ofReal (Real.exp (ph a₀ i y))
  mu_chart i A hA h := by
    rw [glueMeas_apply e _ hd _ i hA h, chartMeas_apply_of_subset _ _ hA h]
    · simp [Pi.single_apply]
    · intro i j y hi hj
      rw [← g_kap i j y hi hj, ph_trans a₀ i j y hi hj, ← ENNReal.ofReal_mul (sq_nonneg _),
        Real.exp_sub, Real.exp_log (pow_pos (norm_pos_iff.2 (g_ne a₀ i j y hi hj)) 2),
        mul_div_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.2 (g_ne a₀ i j y hi hj)))]

end GlobalTheory.ChartGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective
noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory

namespace GlobalTheory.PDivGroup.Test

open PDiv

variable {p : ℕ} {O : Type} [CommRing O]


theorem _root_.GlobalTheory.PDivGroup.Test.mulP_injective (G : _root_.GlobalTheory.PDivGroup p O) (n : ℕ) :
    Function.Injective (G.mulP n) := by
  intro x y hxy
  have hinj := _root_.GlobalTheory.CartierDual.map_injective_of_surjective (G.dual_mulP_surjective n)
  have hx := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) x
  have hy := _root_.GlobalTheory.CartierDual.map_map_bidual (G.mulP n) y
  rw [hxy, ← hy] at hx
  exact (_root_.GlobalTheory.CartierDual.bidual O (G.A n)).injective (hinj hx)

theorem hodgeTate_values [Fact p.Prime] (hp : ¬ IsUnit (p : O)) :
    (∀ t, hodgeTate (mu p O) t = 0) ∧ hodgeTate (const p O) (constGen p O) ≠ 0 := by
  refine ⟨fun t => Subsingleton.elim _ _, fun h => dlogT_ne_zero p O hp ?_⟩
  rw [hodgeTate_eq_omegaMap, ← dualHom_constHom, show constHom _ (constGen p O) = 𝟙 _ by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], dualHom_id,
    Category.id_comp] at h
  have h2 := LinearMap.congr_fun (omegaMap_comp (mu p O).bidual.hom (mu p O).bidual.inv) (dlogT p O)
  rw [Iso.hom_inv_id, omegaMap_id, LinearMap.id_apply, LinearMap.comp_apply] at h2
  rw [h2]
  exact (congrArg _ h).trans (map_zero _)

section Prod

variable (A B : Type) [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]

def inl : A →ₐc[O] A ⊗[O] B :=
  (Bialgebra.TensorProduct.map (BialgHom.id O A) (Bialgebra.unitBialgHom O B)).comp
    (Bialgebra.TensorProduct.rid O O A).symm.toBialgHom

def inr : B →ₐc[O] A ⊗[O] B :=
  (Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom O A) (BialgHom.id O B)).comp
    (Bialgebra.TensorProduct.lid O B).symm.toBialgHom

variable {A B}

theorem inl_apply (a : A) : inl (O := O) A B a = a ⊗ₜ 1 :=
  congrArg (fun y : B => a ⊗ₜ[O] y) (map_one (Bialgebra.unitBialgHom O B))

theorem inr_apply (b : B) : inr (O := O) A B b = 1 ⊗ₜ b :=
  congrArg (fun y : A => y ⊗ₜ[O] b) (map_one (Bialgebra.unitBialgHom O A))

theorem pts_ext {E : Type} [CommRing E] [Algebra O E] {x y : WithConv (A ⊗[O] B →ₐ[O] E)}
    (h1 : pointsMap E (inl A B) x = pointsMap E (inl A B) y)
    (h2 : pointsMap E (inr A B) x = pointsMap E (inr A B) y) : x = y := by
  refine ofConv_injective (Algebra.TensorProduct.ext' fun a b => ?_)
  have e1 : x.ofConv (inl A B a) = y.ofConv (inl A B a) := DFunLike.congr_fun (congrArg ofConv h1) a
  have e2 : x.ofConv (inr A B b) = y.ofConv (inr A B b) := DFunLike.congr_fun (congrArg ofConv h2) b
  have e : a ⊗ₜ[O] b = inl A B a * inr A B b := by simp [inl_apply, inr_apply]
  rw [e, map_mul, map_mul, e1, e2]

end Prod

@[reducible] def prod (G H : PDivGroup p O) : PDivGroup p O where
  height := G.height + H.height
  A n := G.A n ⊗[O] H.A n
  rank_eq n q := by
    rw [rankAtStalk_tensorProduct, Pi.mul_apply, G.rank_eq, H.rank_eq, mul_add, pow_add]
  res n := Bialgebra.TensorProduct.map (G.res n) (H.res n)
  res_surjective n := TensorProduct.map_surjective (g := (G.res n).toLinearMap) (g' := (H.res n).toLinearMap) (G.res_surjective n) (H.res_surjective n)
  ker_res n := by
    refine le_antisymm (fun a ha => ?_) ?_
    · let π := Ideal.Quotient.mkₐ O
        (torsionIdeal (R := O) (A := G.A (n + 1) ⊗[O] H.A (n + 1)) (p ^ n))
      have h1 := (torsionIdeal_le_ker_iff (p ^ n) π).1
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
      obtain ⟨y, hy⟩ := (G.exists_comp_res_iff n (pointsMap _ (inl _ _) (toConv π)).ofConv).2
        (by rw [toConv_ofConv, ← map_pow, h1, map_one])
      obtain ⟨z, hz⟩ := (H.exists_comp_res_iff n (pointsMap _ (inr _ _) (toConv π)).ofConv).2
        (by rw [toConv_ofConv, ← map_pow, h1, map_one])
      have h2 : (Algebra.TensorProduct.lift y z fun _ _ => .all _ _).comp
          (Bialgebra.TensorProduct.map (G.res n) (H.res n) :
            G.A (n + 1) ⊗[O] H.A (n + 1) →ₐ[O] G.A n ⊗[O] H.A n) = π :=
        Algebra.TensorProduct.ext' fun a b => by
          have e1 : y (G.res n a) = π (inl _ _ a) := DFunLike.congr_fun hy a
          have e2 : z (H.res n b) = π (inr _ _ b) := DFunLike.congr_fun hz b
          change y (G.res n a) * z (H.res n b) = _
          rw [e1, e2, ← map_mul, inl_apply, inr_apply]
          simp
      have h3 := (DFunLike.congr_fun h2 a).symm
      rw [AlgHom.comp_apply] at h3
      erw [show Bialgebra.TensorProduct.map (G.res n) (H.res n) a = 0 from ha, map_zero] at h3
      exact Ideal.Quotient.eq_zero_iff_mem.1 h3
    · refine (torsionIdeal_le_ker_iff (p ^ n) (Bialgebra.TensorProduct.map (G.res n) (H.res n) :
          G.A (n + 1) ⊗[O] H.A (n + 1) →ₐ[O] G.A n ⊗[O] H.A n)).2 (pts_ext ?_ ?_)
      · rw [map_pow, map_one]
        refine (G.exists_comp_res_iff n _).1 ⟨(inl (O := O) (G.A n) (H.A n)).toAlgHom, AlgHom.ext fun a => ?_⟩
        change inl _ _ (G.res n a) = Bialgebra.TensorProduct.map (G.res n) (H.res n) (inl _ _ a)
        simp [inl_apply]
      · rw [map_pow, map_one]
        refine (H.exists_comp_res_iff n _).1 ⟨(inr (O := O) (G.A n) (H.A n)).toAlgHom, AlgHom.ext fun a => ?_⟩
        change inr _ _ (H.res n a) = Bialgebra.TensorProduct.map (G.res n) (H.res n) (inr _ _ a)
        simp [inr_apply]

end GlobalTheory.PDivGroup.Test
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
set_option autoImplicit false

noncomputable section

open Coalgebra

namespace GlobalTheory.HTPair

open _root_.GlobalTheory.PDiv

structure QuotTower {p : ℕ} {O : Type} [CommRing O] (G : _root_.GlobalTheory.PDivGroup p O) : Type 1 where

  B : ℕ → Type
  [commRing : ∀ m, CommRing (B m)]
  [hopf : ∀ m, HopfAlgebra O (B m)]
  [cocomm : ∀ m, IsCocomm O (B m)]
  [finite : ∀ m, Module.Finite O (B m)]
  [projective : ∀ m, Module.Projective O (B m)]

  j : ∀ m, B m →ₐc[O] G.A (m + 1)

  ρ : ∀ m, G.A (m + 1) →ₗ[O] B m

  r : ∀ m, B (m + 1) →ₐc[O] B m

  s : ∀ m, G.A m →ₐc[O] B m

  ρ_j : ∀ m b, ρ m (j m b) = b

  r_surjective : ∀ m, Function.Surjective (r m)

  j_r : ∀ m b, j m (r m b) = G.res (m + 1) (j (m + 1) b)

  j_s : ∀ m a, j m (s m a) = G.mulP m a

  tors_le : ∀ m, torsionIdeal (R := O) (A := G.A (m + 1)) p ≤ kerIdeal (j m)

attribute [instance] QuotTower.commRing QuotTower.hopf QuotTower.cocomm QuotTower.finite
  QuotTower.projective

def QuotTower.trivial {p : ℕ} {O : Type} [CommRing O] (G : _root_.GlobalTheory.PDivGroup p O) : QuotTower G where
  B m := G.A (m + 1)
  j _ := BialgHom.id O _
  ρ _ := LinearMap.id
  r m := G.res (m + 1)
  s m := G.mulP m
  ρ_j _ _ := rfl
  r_surjective m := G.res_surjective (m + 1)
  j_r _ _ := rfl
  j_s _ _ := rfl
  tors_le m := by
    rw [kerIdeal_of_surjective (f := BialgHom.id O (G.A (m + 1))) Function.surjective_id]
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    have ha' : counit (R := O) a = 0 := ha
    change counit (R := O) (mulBy (R := O) (A := G.A (m + 1)) p a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha']

theorem exists_retraction_mulP {p : ℕ} {O : Type} [CommRing O] (G : _root_.GlobalTheory.PDivGroup p O) (m : ℕ) :
    ∃ ρ : G.A (m + 1) →ₗ[O] G.A m, ∀ a, ρ (G.mulP m a) = a := by
  let f : G.A m →ₗ[O] G.A (m + 1) := (G.mulP m : G.A m →ₐ[O] G.A (m + 1)).toLinearMap
  have hs : Function.Surjective f.dualMap := fun φ => by
    obtain ⟨ψ, hψ⟩ := G.dual_mulP_surjective m (WithConv.toConv φ)
    exact ⟨ψ.ofConv, congrArg WithConv.ofConv hψ⟩
  obtain ⟨σ, hσ⟩ := f.dualMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)
  refine ⟨(Module.evalEquiv O (G.A m)).symm.toLinearMap ∘ₗ σ.dualMap ∘ₗ
    (Module.evalEquiv O (G.A (m + 1))).toLinearMap, fun a => ?_⟩
  change (Module.evalEquiv O (G.A m)).symm _ = a
  rw [LinearEquiv.symm_apply_eq]
  ext φ
  exact LinearMap.congr_fun (LinearMap.congr_fun hσ φ) a

def QuotTower.full {p : ℕ} {O : Type} [CommRing O] (G : _root_.GlobalTheory.PDivGroup p O) : QuotTower G where
  B m := G.A m
  j m := G.mulP m
  ρ m := (exists_retraction_mulP G m).choose
  r m := G.res m
  s _ := BialgHom.id O _
  ρ_j m := (exists_retraction_mulP G m).choose_spec
  r_surjective := G.res_surjective
  j_r m b := by rw [G.mulP_res, G.res_mulP]
  j_s _ _ := rfl
  tors_le m := by
    rw [← kerIdeal_comp_of_surjective _ (G.res_surjective m), G.mulP_comp_res]

theorem QuotTower.map_res_kerIdeal {p : ℕ} {O : Type} [CommRing O] {G : _root_.GlobalTheory.PDivGroup p O}
    (T : QuotTower G) (m : ℕ) :
    Ideal.map (G.res (m + 1) : G.A (m + 2) →ₐ[O] G.A (m + 1)) (kerIdeal (T.j (m + 1))) =
      kerIdeal (T.j m) := by
  have h : (G.res (m + 1)).comp (T.j (m + 1)) = (T.j m).comp (T.r m) :=
    BialgHom.ext fun b => (T.j_r m b).symm
  rw [← kerIdeal_comp, h, kerIdeal_comp_of_surjective (T.j m) (T.r_surjective m)]

end GlobalTheory.HTPair
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.MiddleNotMem
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj

section Alg
variable {k : Type*} [Field k] {n n' n'' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  [Fintype n''] [DecidableEq n'']

theorem symPr_zero (C : Subgroup (GL (n ⊕ Fin 0) k)) : symPr C = C.comap (embX 0) := by
  have h : ∀ p, N k n 0 p = ⊥ := fun p => (Subgroup.eq_bot_iff_forall _).2 fun g hg => Units.ext (by
    ext (r | r) (s | s)
    · exact RootEx.Model.mem_N_iff.1 hg _ _ le_rfl
    all_goals first | exact r.elim0 | exact s.elim0)
  ext g
  show (∃ u ∈ symN k n 0, u * embX 0 g ∈ C) ↔ _
  simp [symN, h]
end Alg

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {G : Grid (k := k)} (hs : 1 ≤ G.s) [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)



end GlobalTheory.FunObj.UnfModel
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermTools

open ReciprocityTheory.GeometryOfNumbersTheory Matrix NumberField
open scoped ComplexOrder ComplexConjugate

variable {K E : Type*} [Field K] [Field E] {V V' : Type*} [AddCommGroup V] [Module K V]

section Complex

variable (h : HermFam K V) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]

def csq (c : ι → ℂ) (v : ι → V) : ℝ := (∑ i, ∑ k, conj (c i) * c k * h.form σ (v i) (v k)).re

def cnrm (c : ι → ℂ) (v : ι → V) : ℝ := Real.sqrt (csq h σ c v)

theorem csq_map (a : ι → K) (v : ι → V) :
    csq h σ (fun i => σ (a i)) v = (h.form σ (∑ i, a i • v i) (∑ i, a i • v i)).re := by
  rw [csq, h.form_sum_left]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [h.form_sum_right]
  exact Finset.sum_congr rfl fun k _ => by rw [h.form_smul_left, h.smul_right, mul_assoc]

theorem cnrm_map (a : ι → K) (v : ι → V) : cnrm h σ (fun i => σ (a i)) v = h.nrm σ (∑ i, a i • v i) :=
  congrArg Real.sqrt (csq_map h σ a v)

theorem csq_comb {κ : Type*} [Fintype κ] (c : ι → ℂ) (a : ι → κ → K) (b : κ → V) :
    csq h σ c (fun i => ∑ k, a i k • b k) = csq h σ (fun k => ∑ i, c i * σ (a i k)) b := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [csq, h.form_sum_left, h.form_sum_right, h.form_smul_left, h.smul_right, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine congrArg _ ?_
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ⟨fun t => (t.2.2.1, t.2.2.2, t.2.1, t.1), fun t => (t.2.2.2, t.2.2.1, t.1, t.2.1),
    fun _ => rfl, fun _ => rfl⟩ _ _ fun t => by simp only [Equiv.coe_fn_mk]; ring

theorem csq_nonneg (c : ι → ℂ) (v : ι → V) : 0 ≤ csq h σ c v := by
  let S := Submodule.span K (Set.range v)
  have : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range v)
  let b := Module.finBasis K S
  have e : v = fun i => ∑ k, b.repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ k • (b k : V) := funext fun i => by
    exact (congrArg S.subtype (b.sum_repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩).symm).trans (map_sum _ _ _)
  rw [e, csq_comb]
  generalize (fun k => ∑ i, c i * σ _) = x
  have := (h.posDef σ _ _ (b.linearIndependent.map' S.subtype S.ker_subtype)).posSemidef.dotProduct_mulVec_nonneg x
  refine (Complex.nonneg_iff.1 this).1.trans_eq (congrArg _ ?_)
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

end Complex

def ofCoords {P : (K →+* ℂ) → Type*} [∀ σ, Fintype (P σ)] (φ : ∀ σ, V →ₛₗ[σ] (P σ → ℂ))
    (G : ∀ σ, Matrix (P σ) (P σ) ℂ) (hG : ∀ σ, (G σ).PosDef)
    (hφ : ∀ σ n (v : Fin n → V), LinearIndependent K v → LinearIndependent ℂ fun i => φ σ (v i)) :
    HermFam K V where
  form σ x y := star (φ σ x) ⬝ᵥ G σ *ᵥ φ σ y
  add_right σ x y z := by rw [map_add (f := _), mulVec_add, dotProduct_add]
  smul_right σ a x y := by rw [map_smulₛₗ, mulVec_smul, dotProduct_smul, smul_eq_mul]
  conj_symm σ x y := by
    rw [starRingEnd_apply, ← star_dotProduct_star, star_star, star_mulVec, (hG σ).1.eq, ← dotProduct_mulVec]
  posDef σ n v hv := by
    classical
    have := (hG σ).conjTranspose_mul_mul_same (B := Matrix.of fun p i => φ σ (v i) p)
      (Matrix.mulVec_injective_iff.2 (hφ σ n v hv))
    convert this using 1
    ext i j
    simp [dotProduct, mulVec, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm

def comap [AddCommGroup V'] [Module K V'] (h : HermFam K V) (f : V' →ₗ[K] V) (hf : Function.Injective f) :
    HermFam K V' where
  form σ x y := h.form σ (f x) (f y)
  add_right σ x y z := by rw [map_add (f := _), h.add_right]
  smul_right σ a x y := by rw [map_smul, h.smul_right]
  conj_symm σ x y := h.conj_symm σ _ _
  posDef σ n v hv := h.posDef σ n _ (hv.map' f (LinearMap.ker_eq_bot.2 hf))

theorem isConjInv_comap [AddCommGroup V'] [Module K V'] {h : HermFam K V} (hh : h.IsConjInv) (f : V' →ₗ[K] V)
    (hf : Function.Injective f) : (comap h f hf).IsConjInv := fun σ _ _ => hh σ _ _

def basisCoords {n : Type*} [Finite n] (b : Module.Basis n K V) (σ : K →+* ℂ) : V →ₛₗ[σ] (n → ℂ) where
  toFun x i := σ (b.repr x i)
  map_add' x y := funext fun i => by simp
  map_smul' a x := funext fun i => by simp

theorem linearIndependent_basisCoords {n ι : Type*} [Finite n] (b : Module.Basis n K V) (σ : K →+* ℂ) {v : ι → V}
    (hv : LinearIndependent K v) : LinearIndependent ℂ fun i => basisCoords b σ (v i) :=
  letI := σ.toAlgebra
  linearIndependent_algebraMap_comp_iff.2 (hv.map' b.equivFun.toLinearMap b.equivFun.ker)

def ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) (G : (K →+* ℂ) → Matrix n n ℂ)
    (hG : ∀ σ, (G σ).PosDef) : HermFam K V :=
  ofCoords (P := fun _ => n) (basisCoords b) G hG fun σ _ _ => linearIndependent_basisCoords b σ

theorem form_ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) (G : (K →+* ℂ) → Matrix n n ℂ)
    (hG : ∀ σ, (G σ).PosDef) (σ : K →+* ℂ) (i j : n) : (ofGram b G hG).form σ (b i) (b j) = G σ i j := by
  classical
  simp [ofGram, ofCoords, basisCoords, dotProduct, mulVec, Finsupp.single_apply, apply_ite]

theorem isConjInv_ofGram {n : Type*} [Fintype n] (b : Module.Basis n K V) {G : (K →+* ℂ) → Matrix n n ℂ}
    (hG : ∀ σ, (G σ).PosDef) (hc : ∀ σ i j, G (ComplexEmbedding.conjugate σ) i j = conj (G σ i j)) :
    (ofGram b G hG).IsConjInv := fun σ x y => by
  simp [ofGram, ofCoords, basisCoords, dotProduct, mulVec, hc]

def ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) : HermFam K V :=
  ofGram b (fun _ => 1) fun _ => PosDef.one

theorem nrm_ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) (σ : K →+* ℂ) (i : n) :
    (ofBasis b).nrm σ (b i) = 1 := by
  simp [HermFam.nrm, ofBasis, form_ofGram]

theorem isConjInv_ofBasis {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K V) :
    (ofBasis b).IsConjInv := isConjInv_ofGram b _ fun _ i j => by simp [Matrix.one_apply, apply_ite]

section Extend

variable [AddCommGroup V'] [Module E V'] {j : K →+* E}

structure IsExtension (ι : V →ₛₗ[j] V') : Prop where

  indep : ∀ (n : ℕ) (v : Fin n → V), LinearIndependent K v → LinearIndependent E fun i => ι (v i)

  span : Submodule.span E (Set.range ι) = ⊤

variable {ι : V →ₛₗ[j] V'} (hι : IsExtension ι)

def IsExtension.basis {n : ℕ} (b : Module.Basis (Fin n) K V) : Module.Basis (Fin n) E V' :=
  Module.Basis.mk (hι.indep n b b.linearIndependent) (hι.span.ge.trans (Submodule.span_le.2 (by
    rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))))

variable [FiniteDimensional K V]


def extend (h : HermFam K V) : HermFam E V' :=
  ofGram (hι.basis (Module.finBasis K V)) (fun τ => h.gram (τ.comp j) (Module.finBasis K V))
    fun _ => h.posDef _ _ _ (Module.finBasis K V).linearIndependent

theorem isConjInv_extend {h : HermFam K V} (hh : h.IsConjInv) : (extend hι h).IsConjInv :=
  isConjInv_ofGram _ _ fun τ _ _ => hh (τ.comp j) _ _

end Extend

end GlobalTheory.HermTools
end
end
