module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteTorsOfFiniteTorsion
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlphaPair

section Eval

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

def evP {n d : ℕ} (v : Fin n → Fin d → A) (f : PS R n d) : A := nEval f (fun q : Fin n × Fin d => v q.1 q.2)

def addP {d : ℕ} (F : Fin d → PS R 2 d) (a b : Fin d → A) : Fin d → A := fun j => evP ![a, b] (F j)

def cv {d : ℕ} (ga : Fin d → PowerSeries R) (t : A) : Fin d → A :=
  fun j => nEval (σ := Unit) (ga j) (fun _ => t)

variable {κ : Type} [Fintype κ] [DecidableEq κ] {a : κ → A} (ha : ∀ i, IsNilpotent (a i))

def evHom : MvPowerSeries κ R →+* A :=
  (MvPowerSeries.constantCoeff : MvPowerSeries Empty A →+* A).comp
    (MvPowerSeries.substAlgHom (R := R) (ChartCompare.hasSubst_C a ha)).toRingHom

theorem evHom_apply (f : MvPowerSeries κ R) : evHom ha f = nEval f a := by
  simp [evHom, MvPowerSeries.coe_substAlgHom, ChartCompare.subst_C_eq f a ha]

include ha

theorem nEval_add (f g : MvPowerSeries κ R) : nEval (f + g) a = nEval f a + nEval g a := by
  simp only [← evHom_apply ha, map_add (f := _)]

theorem nEval_sub (f g : MvPowerSeries κ R) : nEval (f - g) a = nEval f a - nEval g a := by
  simp only [← evHom_apply ha, map_sub]

theorem nEval_one : nEval (1 : MvPowerSeries κ R) a = 1 := by simp only [← evHom_apply ha, map_one]

end Eval

section Points

variable {S S' : Scheme.{0}} {Ω : Type} [Field Ω]

abbrev Fam (s : Sp Ω ⟶ S) (G : Over S) : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A], A → (overAt s A ⟶ G)

def IsAlpha (p : ℕ) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (g : Fam s G) : Prop :=
  (∀ (A B : Type) [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (a : A), a ^ p = 0 →
    g B (f a) = homAt s f ≫ g A a) ∧
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (a a' : A), a ^ p = 0 → a' ^ p = 0 → g A (a + a') = g A a * g A a'

def Orth (p : ℕ) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    (g : Fam s G) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) → ∀ e : A, e ^ 2 = 0 →
    ∀ z : overAt s A ⟶ G, homAt s π ≫ z = 1 → z ^ p = 1 → CubWeil c p (g A e) z 1

def NonDeg (p : ℕ) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) : Prop :=
  ∀ g : Fam s G, IsAlpha p s G g → Orth p s G c g → g (DualNumber Ω) DualNumber.eps = 1

def Perf (n : ℕ) (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) : Prop :=
  ∀ (T : Over S) (x : T ⟶ G), x ^ n = 1 →
    (∀ (T' : Over S) (ρ : T' ⟶ T) (y : T' ⟶ G), y ^ n = 1 → CubWeil c n (ρ ≫ x) y 1) → x = 1

abbrev PtHom (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S') (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A], (overAt s A ⟶ G) →* (overAt s' A ⟶ B)

abbrev TorHom (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A], (Multiplicative X →* Aˣ) →* (overAt s A ⟶ G)

def IsTorExt (s : Sp Ω ⟶ S) (s' : Sp Ω ⟶ S') (G : Over S) [GrpObj G] (B : Over S') [GrpObj B] (X : Type)
    [AddCommGroup X] (τ : PtHom s s' G B) (io : TorHom s G X) : Prop :=
  (∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (f : A →ₐ[Ω] A') (x : overAt s A ⟶ G),
    τ A' (homAt s f ≫ x) = homAt s' f ≫ τ A x) ∧
  (∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (f : A →ₐ[Ω] A')
    (χ : Multiplicative X →* Aˣ), io A' ((Units.map (f : A →* A')).comp χ) = homAt s f ≫ io A χ) ∧
  (∀ (A : Type) [CommRing A] [Algebra Ω A], Function.Injective (io A)) ∧
  (∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt s A ⟶ G), τ A x = 1 ↔ ∃ χ, io A χ = x) ∧
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) →
    ∀ y : overAt s' A ⟶ B, homAt s' π ≫ y = 1 → ∃ x : overAt s A ⟶ G, homAt s π ≫ x = 1 ∧ τ A x = y

def Transfer (n : ℕ) {s : Sp Ω ⟶ S} {s' : Sp Ω ⟶ S'} {G : Over S} [GrpObj G] [IsCommMonObj G] {B : Over S'} [GrpObj B]
    [IsCommMonObj B] {L : RigLB G} (c : CubicalStr G L) {M : RigLB B} (c' : CubicalStr B M) (τ : PtHom s s' G B) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (x y : overAt s A ⟶ G), CubWeil c n x y 1 → CubWeil c' n (τ A x) (τ A y) 1

abbrev PtFam (s : Sp Ω ⟶ S) (G : Over S) (d : ℕ) : Type 1 :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A], (Fin d → A) → (overAt s A ⟶ G)

def IsJetPt {V : Type} [CommRing V] (β : V →+* Ω) {G : Over (Sp V)} {d : ℕ}
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (P : PtFam (spMap β) G d) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (m : ℕ) (ψ : Jet V (Fin 1 × Fin d) m →+* A),
    (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) →
    (P A fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))).left = spMap ψ ≫ (x m).left

def IsPtLaw (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] {d : ℕ} (F : Fin d → PS Ω 2 d) (P : PtFam s G d) : Prop :=
  (∀ (A B : Type) [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (a : Fin d → A),
    (∀ j, IsNilpotent (a j)) → P B (fun j => f (a j)) = homAt s f ≫ P A a) ∧
  (∀ (A : Type) [CommRing A] [Algebra Ω A], P A 0 = 1) ∧
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (a b : Fin d → A), (∀ j, IsNilpotent (a j)) → (∀ j, IsNilpotent (b j)) →
    P A (addP F a b) = P A a * P A b

def IsPtUniv (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] {d : ℕ} (P : PtFam s G d) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (π : A →ₐ[Ω] Ω), IsNilpotent (RingHom.ker π) →
    (∀ a : Fin d → A, (∀ j, IsNilpotent (a j)) → P A a = 1 → a = 0) ∧
    ∀ z : overAt s A ⟶ G, homAt s π ≫ z = 1 → ∃ a : Fin d → A, (∀ j, IsNilpotent (a j)) ∧ P A a = z

def IsPtCube (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) {d : ℕ}
    (F : Fin d → PS Ω 2 d) (ph1 ph2 : PS Ω 3 d) (P : PtFam s G d) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Ω A] (I : Ideal A), IsNilpotent I →
    ∀ (z : (overAt s A).left) (J), Good L.L z J →
    ∃ e : (Fin d → A) → (Fin d → A) → ((overAt s A).left.presheaf.stalk z)ˣ,
      ∀ a b u : Fin d → A, (∀ j, a j ∈ I) → (∀ j, b j ∈ I) → (∀ j, u j ∈ I) →
        (cubV c z J (P A a) (P A b) (P A u) * e a u * e b u).val =
          gs (𝟙 (overAt s A).left) z ⊤ (toΓ A (evP ![a, b, u] ph1)) * (e (addP F a b) u).val ∧
        (cubV c z J (P A b) (P A u) (P A a) * e a b * e a u).val =
          gs (𝟙 (overAt s A).left) z ⊤ (toΓ A (evP ![a, b, u] ph2)) * (e a (addP F b u)).val

section Basic

variable {s : Sp Ω ⟶ S} {s' : Sp Ω ⟶ S'} {G : Over S} [GrpObj G] {p : ℕ}

theorem hom_comp {A B C : Type} [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] [CommRing C] [Algebra Ω C]
    (f : A →ₐ[Ω] B) (g : B →ₐ[Ω] C) : homAt s g ≫ homAt s f = homAt s (g.comp f) :=
  Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp s f g

theorem hom_id {A : Type} [CommRing A] [Algebra Ω A] : homAt s (AlgHom.id Ω A) = 𝟙 _ :=
  Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_id s

theorem IsAlpha.zero {g : Fam s G} (h : IsAlpha p s G g) (hp : p ≠ 0) (A : Type) [CommRing A] [Algebra Ω A] :
    g A 0 = 1 := by
  have := h.2 A 0 0 (zero_pow hp) (zero_pow hp)
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem IsAlpha.nsmul {g : Fam s G} (h : IsAlpha p s G g) (hp : p ≠ 0) {A : Type} [CommRing A] [Algebra Ω A] {a : A}
    (ha : a ^ p = 0) (n : ℕ) : g A (n * a) = g A a ^ n := by
  induction n with
  | zero => simpa using h.zero hp A
  | succ n ih => rw [Nat.cast_succ, add_mul, _root_.one_mul, h.2 A _ _ (by rw [mul_pow, ha, mul_zero]) ha, ih, pow_succ]

theorem IsAlpha.pow_eq_one [CharP Ω p] {g : Fam s G} (h : IsAlpha p s G g) (hp : p ≠ 0) {A : Type} [CommRing A]
    [Algebra Ω A] {a : A} (ha : a ^ p = 0) : g A a ^ p = 1 := by
  rw [← h.nsmul hp ha, ← map_natCast (algebraMap Ω A), CharP.cast_eq_zero, map_zero, zero_mul, h.zero hp]

theorem IsAlpha.map {B : Over S'} [GrpObj B] {X : Type} [AddCommGroup X] {τ : PtHom s s' G B} {io : TorHom s G X}
    (hτ : IsTorExt s s' G B X τ io) {g : Fam s G} (h : IsAlpha p s G g) :
    IsAlpha p s' B (fun A _ _ a => τ A (g A a)) :=
  ⟨fun A A' _ _ _ _ f a ha => by beta_reduce; rw [h.1 A A' f a ha, hτ.1],
    fun A _ _ a a' ha ha' => by beta_reduce; rw [h.2 A a a' ha ha', map_mul]⟩

theorem cubWeil_of_injective [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {n : ℕ} {A B : Type} [CommRing A]
    [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (hf : Function.Injective f) {x y : overAt s A ⟶ G}
    (hx : x ^ n = 1) (hy : y ^ n = 1) (h : CubWeil c n (homAt s f ≫ x) (homAt s f ≫ y) 1) : CubWeil c n x y 1 := by
  obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c hx hy
  have e := congrArg Units.val ((hζ.comp (homAt s f)).unique h)
  have inj : Function.Injective (homAt s f).left.appTop.hom := by
    have h₁ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* B))
    have h₂ : Function.Injective ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom (f : A →+* B)).hom :=
      hf.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
    rw [← h₁] at h₂
    exact Function.Injective.of_comp (f := (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom) h₂
  obtain rfl : ζ = 1 := Units.ext (inj (e.trans (map_one _).symm))
  exact hζ

theorem cubWeil_mul_right [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L} {n : ℕ} {T : Over S} {x y y' : T ⟶ G}
    (h : CubWeil c n x y 1) (h' : CubWeil c n x y' 1) : CubWeil c n x (y * y') 1 := by
  simpa using (h.symm.mul_left h'.symm).symm

end Basic

end Points

section Series

def c2 {R : Type} [CommRing R] {d : ℕ} (ph2 : PS R 3 d) (u : Fin d → R) : PS R 2 d :=
  fun mu => ∑ i, u i * MvPowerSeries.coeff
    (mu.mapDomain (fun q : Fin 2 × Fin d => (q.1.succ, q.2)) + Finsupp.single ((0 : Fin 3), i) 1) ph2

def AddMod (p : ℕ) {Ω : Type} [Field Ω] {d : ℕ} (F : Fin d → PS Ω 2 d) (ga : Fin d → PowerSeries Ω) : Prop :=
  ∀ i (mu : Fin 2 →₀ ℕ), mu 0 < p → mu 1 < p → MvPowerSeries.coeff mu
    (MvPowerSeries.subst (fun q : Fin 2 × Fin d => Formalism.L2.FormalSeriesBounds.cvAt (MvPowerSeries.X q.1) (ga q.2)) (F i) -
      Formalism.L2.FormalSeriesBounds.cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (ga i)) = 0

def Degenerate (p : ℕ) {Ω : Type} [Field Ω] {d : ℕ} (F : Fin d → PS Ω 2 d) (ph2 : PS Ω 3 d) : Prop :=
  ∃ ga : Fin d → PowerSeries Ω, (∀ i, PowerSeries.constantCoeff (ga i) = 0) ∧ (∃ i, PowerSeries.coeff 1 (ga i) ≠ 0) ∧
    AddMod p F ga ∧ ∃ b : PS Ω 1 d, c2 ph2 (fun i => PowerSeries.coeff 1 (ga i)) =
      ev (n := 2) ![addOf F (pt Ω d 0) (pt Ω d 1)] b - ev (n := 2) ![pt Ω d 0] b - ev (n := 2) ![pt Ω d 1] b

end Series

end GlobalTheory.AlphaPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EmbeddingsCongruentEq
open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory

theorem ringOfIntegers_hom_injective (E : Type) [Field E] [NumberField E] (C : Type) [Field C]
    [CharZero C] (f : 𝓞 E →+* C) : Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  simp only [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
  simpa using hn

theorem ringOfIntegers_hom_eq_of_congr_maximalIdeal :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ ((p : ℤ) ∣ NumberField.discr E) → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsLocalRing O] [Algebra O C], v.Integers O → ¬ IsUnit (p : O) → ∀ σ σ' : 𝓞 E →+* O, (∀ x, σ x - σ' x ∈ maximalIdeal O) → σ = σ' := by
  intro E _ _ p hp hd C _ _ _ v O _ _ _ hv hpu σ σ' hcong
  classical
  by_contra hne
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj

  have hext : ∀ s : 𝓞 E →+* O, ∃ τ : E →ₐ[ℚ] C,
      ∀ x : 𝓞 E, τ (algebraMap (𝓞 E) E x) = algebraMap O C (s x) := by
    intro s
    refine ⟨(IsFractionRing.lift (K := E)
      (ringOfIntegers_hom_injective E C ((algebraMap O C).comp s))).toRatAlgHom, fun x => ?_⟩
    simp
  obtain ⟨τ, hτ⟩ := hext σ
  obtain ⟨τ', hτ'⟩ := hext σ'
  have hττ : τ ≠ τ' := by
    intro h
    apply hne
    ext x
    apply hinj
    rw [← hτ, ← hτ', h]
  have hmem : ∀ (φ : E →ₐ[ℚ] C) (x : 𝓞 E), ∃ y : O,
      algebraMap O C y = φ (algebraMap (𝓞 E) E x) := by
    intro φ x
    have h1 : IsIntegral ℤ (φ (algebraMap (𝓞 E) E x)) :=
      (x.isIntegral_coe).map (φ.toRingHom.toIntAlgHom)
    have h2 : IsIntegral O (φ (algebraMap (𝓞 E) E x)) := h1.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h2)
  choose F hF using hmem
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let e : ι ≃ (E →ₐ[ℚ] C) := Fintype.equivOfCardEq (by
    rw [AlgHom.card, Module.finrank_eq_card_basis (integralBasis E)])
  let N : Matrix ι ι O := fun i j => F (e j) (RingOfIntegers.basis E i)
  have hN : (algebraMap O C).mapMatrix N =
      Algebra.embeddingsMatrixReindex ℚ C (integralBasis E) e := by
    ext i j
    show algebraMap O C (F (e j) (RingOfIntegers.basis E i)) = _
    simp [hF, Algebra.embeddingsMatrixReindex, integralBasis_apply]
  have hdisc : ((NumberField.discr E : ℤ) : O) = N.det ^ 2 := by
    apply hinj
    rw [map_pow, RingHom.map_det, hN, ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two,
      ← NumberField.coe_discr]
    simp
  have hdet : N.det ∈ maximalIdeal O := by
    rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
    apply Matrix.det_zero_of_column_eq (i := e.symm τ) (j := e.symm τ')
      (fun h => hττ (e.symm.injective h))
    intro k
    show residue O (F (e (e.symm τ)) (RingOfIntegers.basis E k)) =
      residue O (F (e (e.symm τ')) (RingOfIntegers.basis E k))
    simp only [Equiv.apply_symm_apply]
    have a1 : F τ (RingOfIntegers.basis E k) = σ (RingOfIntegers.basis E k) :=
      hinj (by rw [hF, hτ])
    have a2 : F τ' (RingOfIntegers.basis E k) = σ' (RingOfIntegers.basis E k) :=
      hinj (by rw [hF, hτ'])
    rw [a1, a2, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hcong _
  have hdm : ((NumberField.discr E : ℤ) : O) ∈ maximalIdeal O := by
    rw [hdisc]
    exact Ideal.pow_mem_of_mem _ hdet 2 (by norm_num)
  have hpm : (p : O) ∈ maximalIdeal O := hpu
  have hcop : IsCoprime (p : ℤ) (NumberField.discr E) :=
    (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hd
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : O) ∈ maximalIdeal O := by
    have := congrArg (Int.cast : ℤ → O) hab
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hdm)
  exact (maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqMvExpOfAdditive
open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.AddChar


open MvPowerSeries in
theorem subst_zero_eq {C : Type} [Field C] {κ τ : Type} [Fintype κ] (F : MvPowerSeries κ C) :
    MvPowerSeries.subst (fun _ : κ => (0 : MvPowerSeries τ C)) F = MvPowerSeries.C (constantCoeff F) := by
  classical
  have hs : HasSubst (fun _ : κ => (0 : MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  ext m
  rw [coeff_subst hs, finsum_eq_single _ 0]
  · simp [coeff_one, coeff_C]
  · intro d hd
    obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hd
    have : (d.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0 := by
      refine Finset.prod_eq_zero (i := w) (by simpa using hw) ?_
      exact zero_pow (by simpa using hw)
    simp [this]


open MvPowerSeries in
theorem eq_mvExp_of_additive : ∀ (C : Type) [Field C] [CharZero C] (κ : Type) [Fintype κ] (U : MvPowerSeries κ C), MvPowerSeries.constantCoeff U = 1 → MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((0 : Fin 2), i) + MvPowerSeries.X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U = MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((0 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U * MvPowerSeries.subst (fun i : κ => (MvPowerSeries.X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) U → U = mvExp (∑ i : κ, MvPowerSeries.coeff (Finsupp.single i 1) U • (MvPowerSeries.X i : MvPowerSeries κ C)) := by
  classical
  intro C _ _ κ _ U h0 h
  have hA : HasSubst (fun i : κ => (X ((0 : Fin 2), i) + X ((1 : Fin 2), i) : MvPowerSeries (Fin 2 × κ) C)) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have hB : ∀ a : Fin 2, HasSubst (fun i : κ => (X (a, i) : MvPowerSeries (Fin 2 × κ) C)) := fun a =>
    hasSubst_of_constantCoeff_zero (by simp)
  let p : Fin 2 × κ → MvPowerSeries κ C := fun x => if x.1 = 0 then X x.2 else 0
  have hp : HasSubst p := hasSubst_of_constantCoeff_zero (by
    intro x; simp only [p]; split_ifs <;> simp)
  have hE : constantCoeff U = 1 ∧ ∀ w, pderiv w U = coeff (Finsupp.single w 1) U • U := by
    refine ⟨h0, fun w => ?_⟩
    have h1 := congrArg (pderiv (R := C) ((1 : Fin 2), w)) h
    rw [Derivation.leibniz, Formalism.G.LogCR.pderiv_subst (by simp), Formalism.G.LogCR.pderiv_subst (by simp),
      Formalism.G.LogCR.pderiv_subst (by simp), Finset.sum_eq_single w, Finset.sum_eq_single w,
      Finset.sum_eq_zero] at h1
    · simp [pderiv_X, Pi.single_apply] at h1
      have h2 := congrArg (subst p) h1
      rw [subst_mul hp, subst_comp_subst_apply hA hp, subst_comp_subst_apply (hB 0) hp,
        subst_comp_subst_apply (hB 1) hp] at h2
      simp only [subst_add hp, subst_X hp, p] at h2
      simp [subst_zero_eq] at h2
      have hs : ∀ F : MvPowerSeries κ C, subst (fun s : κ => (X s : MvPowerSeries κ C)) F = F :=
        fun F => congrFun subst_self F
      rw [hs, hs] at h2
      rw [h2, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, smul_eq_C_mul, mul_comm]
      simp
    all_goals simp +contextual [pderiv_X, Pi.single_apply]
  have hcoeff : ∀ (F : MvPowerSeries κ C),
      (constantCoeff F = 1 ∧ ∀ w, pderiv w F = coeff (Finsupp.single w 1) U • F) →
      ∀ (n : ℕ) (m : κ →₀ ℕ), m.degree = n →
      (mfact m : C) * coeff m F = m.prod (fun s k => coeff (Finsupp.single s 1) U ^ k) := by
    intro F h
    intro n
    induction n with
    | zero =>
      intro m hm
      rw [Finsupp.degree_eq_zero_iff] at hm
      subst hm
      simp [mfact, h.1]
    | succ n ih =>
      intro m hm
      have hne : m ≠ 0 := by rintro rfl; simp at hm
      obtain ⟨w, hw⟩ := Finsupp.ne_iff.1 hne
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
        refine ⟨m - Finsupp.single w 1, ?_⟩
        rw [tsub_add_cancel_of_le]
        rw [Finsupp.single_le_iff]
        simp at hw; omega
      have hd : m'.degree = n := by
        rw [map_add (f := _), Finsupp.degree_single] at hm; omega
      have h1 := congrArg (MvPowerSeries.coeff m') (h.2 w)
      rw [coeff_pderiv, coeff_smul] at h1
      have h2 : mfact (m' + Finsupp.single w 1) = (m' w + 1) * mfact m' := by
        unfold mfact
        have e1 := Finsupp.mul_prod_erase' (m' + Finsupp.single w 1) w (fun _ k => k.factorial) (by simp)
        have e2 := Finsupp.mul_prod_erase' m' w (fun _ k => k.factorial) (by simp)
        rw [← e1, ← e2, Finsupp.erase_add, Finsupp.erase_single, add_zero]
        simp [Nat.factorial_succ, mul_assoc]
      rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), ← ih m' hd, h2,
        Finsupp.prod_single_index (by simp)]
      push_cast
      linear_combination (mfact m' : C) * h1
  have hF : constantCoeff (mvExp (∑ i : κ, coeff (Finsupp.single i 1) U • (X i : MvPowerSeries κ C))) = 1 ∧
      ∀ w, pderiv w (mvExp (∑ i : κ, coeff (Finsupp.single i 1) U • (X i : MvPowerSeries κ C))) =
        coeff (Finsupp.single w 1) U • mvExp (∑ i : κ, coeff (Finsupp.single i 1) U • (X i : MvPowerSeries κ C)) := by
    constructor
    · rw [← coeff_zero_eq_constantCoeff_apply, (show ∀ (h : MvPowerSeries κ C) (m : κ →₀ ℕ), coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) from fun _ _ => rfl)]; simp
    · intro w
      ext m
      have hL : pderiv w (∑ x, (coeff (Finsupp.single x 1) U) • (X x : MvPowerSeries κ C)) = MvPowerSeries.C ((coeff (Finsupp.single w 1) U)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_eq_single w]
        · simp [smul_eq_C_mul]
        · intro b _ hb; simp [pderiv_X_of_ne hb]
        · simp
      rw [coeff_pderiv, coeff_smul, (show ∀ (h : MvPowerSeries κ C) (m : κ →₀ ℕ), coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) from fun _ _ => rfl), (show ∀ (h : MvPowerSeries κ C) (m : κ →₀ ℕ), coeff m (mvExp h) = ∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C) from fun _ _ => rfl), map_add (f := _), Finsupp.degree_single,
        Finset.sum_range_succ', Finset.mul_sum, add_mul, Finset.sum_mul]
      have h0 : MvPowerSeries.coeff (m + Finsupp.single w 1)
          ((∑ x, (coeff (Finsupp.single x 1) U) • (X x : MvPowerSeries κ C)) ^ 0) = 0 := by
        rw [pow_zero, coeff_one, if_neg]
        intro h
        have := DFunLike.congr_fun h w
        simp at this
      rw [h0, zero_div, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 := coeff_pderiv (i := w) ((∑ x, (coeff (Finsupp.single x 1) U) • (X x : MvPowerSeries κ C)) ^ (k + 1)) m
      rw [pderiv_pow, hL, Nat.add_sub_cancel, ← map_natCast (MvPowerSeries.C (σ := κ) (R := C)),
        coeff_mul_C, coeff_C_mul] at h1
      have hk : (k.factorial : C) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      have hk1 : ((k + 1 : ℕ) : C) ≠ 0 := by exact_mod_cast k.succ_ne_zero
      rw [div_mul_eq_mul_div, ← h1, Nat.factorial_succ]
      push_cast at hk1 ⊢
      field_simp
  ext m
  have hm : (mfact m : C) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    unfold mfact
    exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  exact mul_left_cancel₀ hm ((hcoeff U hE _ m rfl).trans (hcoeff _ hF _ m rfl).symm)

end GlobalTheory.AddChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationIntegersPadicComplete
open scoped BigOperators TensorProduct
open NumberField IsLocalRing Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

namespace GlobalTheory.ValExp

noncomputable def halfPow (t : WithTop ℝ) : NNReal :=
  WithTop.recTopCoe (0 : NNReal) (fun r : ℝ => (2⁻¹ : NNReal) ^ r) t

theorem halfPow_top : halfPow ⊤ = 0 := rfl

theorem halfPow_coe (r : ℝ) : halfPow (r : WithTop ℝ) = (2⁻¹ : NNReal) ^ r := rfl

theorem halfPow_zero : halfPow 0 = 1 := by
  rw [← WithTop.coe_zero, halfPow_coe, NNReal.rpow_zero]

theorem halfPow_one : halfPow 1 = 2⁻¹ := by
  rw [← WithTop.coe_one, halfPow_coe, NNReal.rpow_one]

theorem halfPow_add (a b : WithTop ℝ) : halfPow (a + b) = halfPow a * halfPow b := by
  induction a using WithTop.recTopCoe with
  | top => simp [halfPow_top]
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp [halfPow_top]
    | coe b => rw [← WithTop.coe_add, halfPow_coe, halfPow_coe, halfPow_coe, NNReal.rpow_add (by norm_num)]

theorem halfPow_strictAnti : StrictAnti halfPow := by
  intro a b hab
  induction a using WithTop.recTopCoe with
  | top => exact absurd hab not_top_lt
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => rw [halfPow_top, halfPow_coe]; exact NNReal.rpow_pos (by norm_num)
    | coe b =>
      rw [halfPow_coe, halfPow_coe]
      exact NNReal.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) (by exact_mod_cast hab)

variable {C : Type} [Field C]

noncomputable def mulVal (V : VF C) : Valuation C NNReal where
  toFun x := halfPow (V.v x)
  map_zero' := by rw [V.v.map_zero, halfPow_top]
  map_one' := by rw [V.v.map_one, halfPow_zero]
  map_mul' x y := by rw [V.v.map_mul, halfPow_add]
  map_add_le_max' x y := by
    refine (halfPow_strictAnti.antitone (V.v.map_add x y)).trans ?_
    rcases le_total (V.v x) (V.v y) with h | h
    · rw [min_eq_left h]; exact le_max_left _ _
    · rw [min_eq_right h]; exact le_max_right _ _

theorem mulVal_apply (V : VF C) (x : C) : mulVal V x = halfPow (V.v x) := rfl

theorem mulVal_l (V : VF C) : mulVal V (V.l : C) = 2⁻¹ := by
  rw [mulVal_apply, V.v_l, halfPow_one]

theorem mulVal_le_one_iff (V : VF C) (x : C) : mulVal V x ≤ 1 ↔ V.Ge 0 x := by
  rw [mulVal_apply, ← halfPow_zero, halfPow_strictAnti.le_iff_ge]; rfl

theorem mulVal_lt_one_iff (V : VF C) (x : C) : mulVal V x < 1 ↔ V.MM x := by
  rw [mulVal_apply, ← halfPow_zero, halfPow_strictAnti.lt_iff_gt]; rfl

theorem ge_l_pow (V : VF C) (n : ℕ) : V.Ge n ((V.l : C) ^ n) := by
  induction n with
  | zero => simpa using VF.Ge.one
  | succ n ih => rw [pow_succ]; push_cast; exact ih.mul VF.ge_l

theorem ge_of_l_pow_mul (V : VF C) (n : ℕ) {w : ℝ} {a : C} (h : V.Ge w ((V.l : C) ^ n * a)) :
    V.Ge (w - n) a := by
  induction n generalizing w with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', mul_assoc] at h
    refine (ih h.of_l_mul).mono (le_of_eq ?_)
    push_cast; ring

theorem mem_pow_iff (V : VF C) (n : ℕ) (x : (mulVal V).integer) :
    x ∈ (Ideal.span {((V.l : ℕ) : (mulVal V).integer)} ^ n • ⊤ :
      Submodule (mulVal V).integer (mulVal V).integer) ↔ V.Ge n (x : C) := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    have hy : V.Ge 0 (y : C) := (mulVal_le_one_iff V _).1 y.2
    simpa using (ge_l_pow V n).mul hy
  · intro h
    have hl : (V.l : C) ^ n ≠ 0 := pow_ne_zero _ VF.l_ne_zero
    have hy : V.Ge 0 (((V.l : C) ^ n)⁻¹ * x) := by
      have := ge_of_l_pow_mul V n (w := n) (a := ((V.l : C) ^ n)⁻¹ * x)
        (by rwa [mul_inv_cancel_left₀ hl])
      simpa using this
    refine ⟨⟨_, (mulVal_le_one_iff V _).2 hy⟩, Subtype.ext ?_⟩
    simp [mul_inv_cancel_left₀ hl]

theorem isAdicComplete (V : VF C)
    (hc : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) :
    IsAdicComplete (Ideal.span {((V.l : ℕ) : (mulVal V).integer)}) (mulVal V).integer := by
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    by_contra h0
    have h1 : (x : C) ≠ 0 := fun h => h0 (Subtype.ext h)
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff V.v).2 h1)
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have := (mem_pow_iff V n x).1 (SModEq.zero.1 (hx n))
    rw [VF.Ge, ← ht] at this
    exact hn.not_ge (by exact_mod_cast this)
  · intro f hf
    obtain ⟨x, hx⟩ := hc (fun n => (f n : C)) fun n => by
      have := (mem_pow_iff V n _).1 (SModEq.sub_mem.1 (hf (Nat.le_succ n)).symm)
      simpa using this
    have h0 : V.Ge 0 x := by
      have h1 : V.Ge 0 (x - f 0) := by simpa using hx 0
      simpa using h1.add ((mulVal_le_one_iff V _).1 (f 0).2)
    refine ⟨⟨x, (mulVal_le_one_iff V _).2 h0⟩, fun n => SModEq.symm (SModEq.sub_mem.2 ?_)⟩
    rw [mem_pow_iff]
    simpa using hx n

theorem exists_mulVal : ∀ (C : Type) [Field C] (V : VF C) [Fact V.l.Prime], (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) → ∃ vm : Valuation C NNReal, ValuationFitting.ValTie V vm ∧ 0 < (vm (V.l : C) : ℝ) ∧ (vm (V.l : C) : ℝ) < 1 ∧ (∀ x : C, vm x ≤ 1 ↔ V.Ge 0 x) ∧ (∀ x : C, vm x < 1 ↔ V.MM x) ∧ IsAdicComplete (Ideal.span {((V.l : ℕ) : vm.integer)}) vm.integer ∧ Nonempty (Algebra ℤ_[V.l] vm.integer) := by
  intro C _ V _ hc
  haveI := isAdicComplete V hc
  refine ⟨mulVal V, fun x hx => ?_, ?_, ?_, mulVal_le_one_iff V, mulVal_lt_one_iff V, this, ?_⟩
  · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 ((AddValuation.ne_top_iff V.v).2 hx)
    refine ⟨t, ht.symm, ?_⟩
    rw [mulVal_l, mulVal_apply, ← ht, halfPow_coe, NNReal.coe_rpow]
  · rw [mulVal_l]; norm_num
  · rw [mulVal_l]; norm_num
  · obtain ⟨φ⟩ := nonempty_padicInt_ringHom_of_isAdicComplete
      (Ideal.span {((V.l : ℕ) : (mulVal V).integer)}) V.l (Ideal.mem_span_singleton_self _)
    exact ⟨φ.toAlgebra⟩

end GlobalTheory.ValExp
end
