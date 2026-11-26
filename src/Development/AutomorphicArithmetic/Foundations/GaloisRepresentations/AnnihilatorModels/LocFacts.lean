module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleOfCrystalline
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.HkOfPush

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts
noncomputable section

open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Module CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison.Br

def LocFacts : Prop := ∀ (A : Type) [CommRing A] (a t : A), (∃ r : ℕ, a ∣ t ^ r) →
  (∀ x : Formalism.Per6.Loc2 a t, ∃ (r : ℕ) (y : A), Formalism.Per6.Loc2.mk₀ a t t ^ r * x = Formalism.Per6.Loc2.mk₀ a t y) ∧
    ∀ y : A, Formalism.Per6.Loc2.mk₀ a t y = 0 → ∃ r : ℕ, t ^ r * y = 0

def ActEq : Prop := ∀ (l : ℕ) [Fact l.Prime], (∀ (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (g : K.fixingSubgroup) (x : Acris l),
    galA g x = GroundTheory.PAdicHodge.ACris.galCris (Formalism.Per6.toBot g.1) x) ∧ ∀ z : ℤ_[l], Formalism.Per6.zB l z = Formalism.Per6.cB l (zA l z)

def PBTied : Prop := ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ K : FinExt l,
  ∃ (B : PB l K.1) (e : P.R.B ≃ₐ[ℚ_[l]] B.C), (∀ (g : ↥(GK K)) b, e (P.actQ (g : GQ l) b) = B.σ g (e b)) ∧ (∀ b, e (P.φB b) = B.φ (e b)) ∧
    Function.Injective B.φ

def AnnDrop : Prop := ∀ (F G B C : Type) [Field F] [Group G] [CommRing B] [Algebra F B] [CommRing C] [Algebra F C] (σ : G → End F B)
  (φ : B →ₐ[F] B) (s : G → (C →ₐ[F] C)) (ψ : C →ₐ[F] C) (e : B ≃ₐ[F] C), (∀ g b, e (σ g b) = s g (e b)) → (∀ b, e (φ b) = ψ (e b)) →
  Function.Injective ψ → ∀ (V : Type 1) [AddCommGroup V] [Module F V] (V₀ : Type) [AddCommGroup V₀] [Module F V₀] (i : V ≃ₗ[F] V₀)
    (act : G → End F V) (ρ : Representation F G V₀), (∀ g v, ρ g (i v) = i (act g v)) → ∀ (f q n N : ℕ) (A : Fin (n + 1) → End F V)
    (T : ℕ → End F V₀), (∀ (j : Fin (n + 1)) v, T j (i v) = i (A j v)) →
    (∀ x : V ⊗[F] C, (∀ g, TensorProduct.map (act g) (s g).toLinearMap x = x) →
      ∑ j : Fin (n + 1), ((-1) ^ (j : ℕ) * (q : ℤ) ^ ((j : ℕ).choose 2)) • TensorProduct.map (A j) (ψ.toLinearMap ^ (f * (n - j + N))) x = 0) →
    AnnD σ (φ.toLinearMap ^ f) q n ρ T

def FinAll : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  [IsDomain (OK l K)] [IsDiscreteValuationRing (OK l K)] (f : ℕ), 0 < f → Nat.card (IsLocalRing.ResidueField (OK l K)) = l ^ f →
  ∀ (ϖ : OK l K), Irreducible ϖ → ∀ (M : Model l K), M.Sm → ∀ (n j : ℕ) (T : Fin (n + 1) → Corr l M.X)
    (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p), PtId l (l ^ f) n (fn M.p ϖ) T →
  ∀ A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j), (∀ i, IsHk M (T i) (hr i) j (A i)) → ∀ B₀ : PB l K, ∃ N : ℕ, ∀ x, IsInv B₀ M j x →
    ∑ i : Fin (n + 1), ((-1) ^ (i : ℕ) * ((l ^ f : ℕ) : ℤ) ^ ((i : ℕ).choose 2)) •
      TensorProduct.map (A i) (B₀.φ.toLinearMap ^ (f * (n - i + N))) x = 0

def AnnModel : Prop := FinAll → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (K : FinExt l)
  [IsDomain (OK l K.1)] [IsDiscreteValuationRing (OK l K.1)] (f : ℕ), 0 < f → Nat.card (IsLocalRing.ResidueField (OK l K.1)) = l ^ f →
  ∀ (ϖ : OK l K.1), Irreducible ϖ → ∀ (M : Model l K.1), M.Sm → ∀ (n j : ℕ) (T : Fin (n + 1) → Corr l M.X)
    (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p), PtId l (l ^ f) n (fn M.p ϖ) T →
  ∀ A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j), (∀ i, IsHk M (T i) (hr i) j (A i)) →
  ∀ (V₀ : Type) [AddCommGroup V₀] [Module ℚ_[l] V₀] (i : M.V j ≃ₗ[ℚ_[l]] V₀) (ρ : Representation ℚ_[l] ↥(GK K) V₀),
    (∀ g v, ρ g (i v) = i (M.act j g v)) → ∀ T₀ : ℕ → End ℚ_[l] V₀, (∀ (a : Fin (n + 1)) v, T₀ a (i v) = i (A a v)) →
    AnnD (σCr P K) (ψCr P f) (l ^ f) n ρ T₀

end UpperTheory.Gal.crystallineComparison.Br
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAffFin
open CategoryTheory AlgebraicGeometry Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct Module Matrix
open scoped Formalism.Per
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.affFin_of :
    AffFinProj := by
  intro R _ Y f hf s
  haveI : GlobalTheory.FiniteSubsetsInAffineOpens Y := GlobalTheory.FiniteSubsetsInAffineOpens.of_isProjOver hf
  obtain ⟨U, hU, hsub⟩ :=
    GlobalTheory.FiniteSubsetsInAffineOpens.exists_isAffineOpen (X := Y) (s : Set Y) s.finite_toSet
  exact ⟨U, hU, fun x hx => hsub (Finset.mem_coe.mpr hx)⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PhiKOfNil
noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

def CorrPull : Prop :=
  ∀ (l : ℕ) (S S' Y Y' : Scheme.{0}) (u : S' ⟶ S) (f : Y ⟶ S) (f' : Y' ⟶ S') (h : Y' ⟶ Y), IsPullback h f' f u →
    ∀ T : Corr l Y, T.r ≫ f = T.p ≫ f → ∃ (T' : Corr l Y') (g : T'.Z ⟶ T.Z),
      IsPullback T'.p g h T.p ∧ T'.r ≫ h = g ≫ T.r ∧ T'.r ≫ f' = T'.p ≫ f' ∧ T'.d = T.d

def PtIdBC : Prop :=
  ∀ (l q n : ℕ) (O O' : Type) [CommRing O] [CommRing O'] (σ : O →+* O'), σ.Flat → ∀ (ϖ : O) (ϖ' : O'),
    (∀ P : Ideal O', P.IsPrime → (σ ϖ ∈ P ↔ ϖ' ∈ P)) → (∀ a : O', a ^ q - a ∈ Ideal.span {ϖ'}) →
    ∀ (Y Y' : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of O)) (f' : Y' ⟶ Spec (CommRingCat.of O')) (h : Y' ⟶ Y),
    IsPullback h f' f (Spec.map (CommRingCat.ofHom σ)) → ∀ (T : Fin (n + 1) → Corr l Y) (T' : Fin (n + 1) → Corr l Y')
      (g : ∀ j, (T' j).Z ⟶ (T j).Z), (∀ j, IsPullback (T' j).p (g j) h (T j).p) → (∀ j, (T' j).r ≫ h = g j ≫ (T j).r) →
      (∀ j, (T' j).r ≫ f' = (T' j).p ≫ f') → PtId l q n (fn f ϖ) T → PtId l q n (fn f' ϖ') T'

def DvdOfNil : Prop :=
  ∀ (K W : Type) [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W] [Module.Finite K W] (M : End K W) (s : Multiset K) (u : K),
    u ≠ 0 → IsNilpotent (Polynomial.aeval M (Polynomial.C u * rootPol s)) → ∃ m : ℕ, M.charpoly ∣ rootPol s ^ m

def PhiKOfNil : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ)
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) (a : ℕ)
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (LL : FinExt l) (r' : ↥(Dec (F := E) A) →* GL (Fin a) ↥LL.1),
    IsModel Bw r LL r' → Bw.IsCrysE P LL r' → ∀ (Q : Polynomial ↥LL.1), NilD (σSt P Bw.Kw) (ψSt P (resDeg l w)) (Bw.repE LL r') Q →
    ∀ (s : Multiset ℂ) (u : ℂ), u ≠ 0 → Q.map (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) = Polynomial.C u * rootPol s →
    ∃ g : ↥(Weil h), deg g = -1 ∧ ∃ m : ℕ, (wdAt P ι Bw h hj r).charPol g ∣ rootPol s ^ m

end UpperTheory.Gal.crystallineComparison
end
end
