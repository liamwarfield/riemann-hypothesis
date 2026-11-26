module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrame
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

abbrev Loc (G : HTGroup p) : Type := (w : Fin G.m) → Fin G.n → G.Fw w

def IntL (z : Loc G) : Prop := ∀ w i, ‖(z w i : PadicAlgCl p)‖ ≤ 1

def pairL (a b : Loc G) : ℚ_[p] := ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (a w ⬝ᵥ b w)

structure PFrame (β : G.Cˣ) where
  T : VQ D →+ Loc G
  T' : VQ D →+ Loc G
  act : ∀ (c : G.C) x w, T (L.rep c x) w = G.rho w c *ᵥ T x w
  act' : ∀ (c : G.C) x w, T' (L.rep c x) w = (G.rho w ((β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C)))ᵀ *ᵥ T' x w
  form : ∀ u x, ((formB L β u x : ℚ) : ℚ_[p]) = pairL (T' x) (T u) - pairL (T' u) (T x)
  dense : ∀ (a b : Loc G) (k : ℕ), ∃ x a' b', IntL a' ∧ IntL b' ∧ T x = a + p ^ k • a' ∧ T' x = b + p ^ k • b'
  bound : ∃ (s : Finset (VQ D)) (k : ℕ), Submodule.span ℚ (s : Set (VQ D)) = ⊤ ∧
    ∀ x, IntL (T x) → IntL (T' x) → ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set (VQ D))

variable {L}

def PFrame.Mem {β : G.Cˣ} (A : PFrame L β) (g : Gp G) (x : VQ D) : Prop :=
  IntL (fun w => (((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ A.T x w) ∧
    ∀ z : Loc G, IntL z → ‖((g.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * pairL (A.T' x) (fun w => (g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z w)‖ ≤ 1

def IntPt (g : Gp G) : Prop :=
  ‖(g.1 : ℚ_[p])‖ = 1 ∧ ∀ w i j, ‖((g.2 w : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : PadicAlgCl p)‖ ≤ 1 ∧
    ‖((((g.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) i j : PadicAlgCl p)‖ ≤ 1

end UpperTheory.Gal.W2
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

def FTrace : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (x : G.F), ((Algebra.trace ℚ G.F x : ℚ) : ℚ_[p]) = ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (G.embW w x) +
    ∑ w, Algebra.trace ℚ_[p] (G.Fw w) (G.embW w (IsCMField.complexConj G.F x))

def FInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (x : G.F), (∀ w, ‖(G.embW w x : PadicAlgCl p)‖ ≤ 1 ∧ ‖(G.embW w (IsCMField.complexConj G.F x) : PadicAlgCl p)‖ ≤ 1) →
    ∃ (m : ℕ) (c : 𝓞 G.F), m.Coprime p ∧ (c : G.F) = m * x

def EmbAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p), ∃ (w : Fin G.m) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
    (∀ x, τ x = σ (G.emb w x)) ∨ ∀ x, τ x = σ (G.emb w (IsCMField.complexConj G.F x))

def FApprox : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (a b : ∀ w : Fin G.m, G.Fw w) (e : ℝ), 0 < e → ∃ x : G.F, ∀ w, ‖((G.embW w x - a w : G.Fw w) : PadicAlgCl p)‖ < e ∧
    ‖((G.embW w (IsCMField.complexConj G.F x) - b w : G.Fw w) : PadicAlgCl p)‖ < e

def TrDual : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (w : Fin G.m), ∃ d : G.Fw w, d ≠ 0 ∧ ∀ a : G.Fw w,
    (∀ z : G.Fw w, ‖(z : PadicAlgCl p)‖ ≤ 1 → ‖Algebra.trace ℚ_[p] (G.Fw w) (a * z)‖ ≤ 1) ↔ ‖((a * d : G.Fw w) : PadicAlgCl p)‖ ≤ 1

def KpMem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g : Gp G), inclG G 1 g ∈ KHT p G.m G.n 1 G.Fw ↔ IntPt g

def LocLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (w : Fin G.m) (s : Finset (Fin G.n → G.Fw w)), Submodule.span (G.Fw w) (s : Set (Fin G.n → G.Fw w)) = ⊤ →
    ∃ g : GL (Fin G.n) (G.Fw w), ∀ z : Fin G.n → G.Fw w,
      (∀ i, ‖(((((g⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)) *ᵥ z) i : G.Fw w) : PadicAlgCl p)‖ ≤ 1) ↔
        ∃ a : (Fin G.n → G.Fw w) → G.Fw w, (∀ y, ‖(a y : PadicAlgCl p)‖ ≤ 1) ∧ z = ∑ y ∈ s, a y • y

def PFrameEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → ∀ β : G.Cˣ, sh G β = β → Nonempty (PFrame L β)

def PLatOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (M : AddSubgroup (VQ D)) (s : Finset (VQ D)) (k : ℕ), Submodule.span ℚ (s : Set (VQ D)) = ⊤ →
    (∀ c : D.O, ∀ x ∈ M, actQ D c x ∈ M) → (∀ (m : ℕ) x, m.Coprime p → m • x ∈ M → x ∈ M) → (∀ x ∈ s, p ^ k • x ∈ M) →
    (∀ x ∈ M, ∃ m : ℕ, m.Coprime p ∧ (m * p ^ k) • x ∈ AddSubgroup.closure (s : Set (VQ D))) → IsPLat D M

def MemDual : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∃ d : ∀ w : Fin G.m, G.Fw w, (∀ w, d w ≠ 0) ∧ ∀ a : Loc G,
    ((∀ z : Loc G, IntL z → ‖pairL a z‖ ≤ 1) ↔ IntL (fun w => d w • a w))

def PkLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β), D.m = 1 → ∀ g : Gp G, ∃ M : AddSubgroup (VQ D), (∀ x, x ∈ M ↔ A.Mem g x) ∧ IsPLat D M

def PkEquiv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β) (y : GlobalTheory.LKCx.grp G β) (g : Gp G) (x : VQ D), A.Mem (locC G (y : G.Cˣ × ℚˣ) * g) (actY L y x) ↔ A.Mem g x

def PkPerf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β) (g : Gp G) (s : ℚ), ‖(s : ℚ_[p]) * (g.1 : ℚ_[p])‖ = 1 → ∀ M : AddSubgroup (VQ D), (∀ x, x ∈ M ↔ A.Mem g x) → PerfAt L β s M

def PkInj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β) (g g' : Gp G), (∀ x, A.Mem g x ↔ A.Mem g' x) ↔ IntPt (g⁻¹ * g')

def PkOnto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (β : G.Cˣ) (A : PFrame L β), D.m = 1 → ∀ (M : AddSubgroup (VQ D)) (s : ℚ), IsPLat D M → 0 < s → PerfAt L β s M → ∃ g : Gp G, ∀ x, x ∈ M ↔ A.Mem g x

def OOnto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O)

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPlaceT
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem rho_not_real {tr nm : ℤ} {r : ℂ} (hd : tr ^ 2 - 4 * nm < 0)
    (hr : r ^ 2 - (tr : ℂ) * r + (nm : ℂ) = 0) : (starRingEnd ℂ) r ≠ r := by
  intro hc
  have him : r.im = 0 := Complex.conj_eq_iff_im.mp hc
  obtain ⟨x, rfl⟩ : ∃ x : ℝ, r = (x : ℂ) := ⟨r.re, by apply Complex.ext <;> simp [him]⟩
  have h1 : x ^ 2 - (tr : ℝ) * x + (nm : ℝ) = 0 := by exact_mod_cast hr
  have h2 : ((tr : ℝ)) ^ 2 - 4 * (nm : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [sq_nonneg (2 * x - (tr : ℝ))]

theorem UpperTheory.Gal.W2.placeT_of :
    UpperTheory.Gal.W2.PlaceT := by
  intro p _ D G L ha v hv t₀ ht
  have i₀ : Fin D.a := ⟨0, by omega⟩
  have hsub : ∀ i j : Fin D.a, i = j := fun i j => by
    apply Fin.ext; have := i.2; have := j.2; omega
  have hρ : t₀ (D.ω : D.F) = D.ρc := by rw [← ht i₀]; exact D.tau_ω i₀
  have hne : (starRingEnd ℂ) D.ρc ≠ D.ρc := rho_not_real D.disc_neg D.ρc_root
  obtain ⟨i, hi⟩ := (L.sig v).1 hv
  have hφ : ∀ x, (G.iotaC.comp (L.s i)) (L.e x) = t₀ x := fun x => by
    rw [← ht i]; exact L.s_C i x
  refine ⟨fun v' hv' => ?_, hρ, hne, ?_⟩
  · obtain ⟨j, hj⟩ := (L.sig v').1 hv'
    rw [hi, hj, hsub i j]
  · have hemb := InfinitePlace.embedding_mk_eq (G.iotaC.comp (L.s i))
    rw [← hi] at hemb
    rcases hemb with h | h
    · left
      have hx : ∀ x, v.embedding (L.e x) = t₀ x := fun x => by rw [h]; exact hφ x
      refine ⟨?_, hx⟩
      unfold sgnV
      rw [if_pos (by rw [hx, hρ])]
    · right
      have hx : ∀ x, v.embedding (L.e x) = (starRingEnd ℂ) (t₀ x) := fun x => by
        rw [h, ComplexEmbedding.conjugate_coe_eq, hφ]
      have hω : v.embedding (L.e (D.ω : D.F)) ≠ D.ρc := by rw [hx, hρ]; exact hne
      refine ⟨?_, fun hall => hω (by rw [hall, hρ]), fun x => by rw [hx, Complex.conj_conj]⟩
      unfold sgnV
      rw [if_neg hω]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem add_expand {V A : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup A] [Module ℝ A]
    {n : ℕ} (b : Module.Basis (Fin n) ℚ V) (f : V →+ A) (w : V) :
    f w = ∑ i, ((b.repr w i : ℚ) : ℝ) • f (b i) := by
  conv_lhs => rw [← b.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := map_ratCast_smul f ℚ ℝ (b.repr w i) (b i)
  simpa using h

private theorem span_basis {V A : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup A] [Module ℝ A]
    {n : ℕ} (b : Module.Basis (Fin n) ℚ V) (f : V →+ A)
    (hs : Submodule.span ℝ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℝ (Set.range (fun i => f (b i))) := by
  rw [← hs]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, rfl⟩
  rw [add_expand b f w]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem equiv_of_spans {V A B : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    [AddCommGroup A] [Module ℝ A] [FiniteDimensional ℝ A] [AddCommGroup B] [Module ℝ B]
    [FiniteDimensional ℝ B] (th : V →+ A) (Q : V →+ B)
    (hA : Submodule.span ℝ (Set.range th) = ⊤) (hB : Submodule.span ℝ (Set.range Q) = ⊤)
    (dA : Module.finrank ℝ A = Module.finrank ℚ V) (dB : Module.finrank ℝ B = Module.finrank ℚ V) :
    ∃ R : A ≃ₗ[ℝ] B, ∀ w, Q w = R (th w) := by
  let b := Module.finBasis ℚ V
  let bA : Module.Basis (Fin (Module.finrank ℚ V)) ℝ A :=
    basisOfTopLeSpanOfCardEqFinrank (fun i => th (b i)) (span_basis b th hA) (by simp [dA])
  let bB : Module.Basis (Fin (Module.finrank ℚ V)) ℝ B :=
    basisOfTopLeSpanOfCardEqFinrank (fun i => Q (b i)) (span_basis b Q hB) (by simp [dB])
  refine ⟨bA.equiv bB (Equiv.refl _), fun w => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_expand b th w, add_expand b Q w, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  congr 1
  have h1 : bA i = th (b i) := by simp [bA]
  have h2 : bB i = Q (b i) := by simp [bB]
  rw [← h1, ← h2, Module.Basis.equiv_apply]
  rfl

theorem UpperTheory.Gal.W2.perExt_of :
    UpperTheory.Gal.W2.PerExt := by
  intro p _ D G L A β ρ Q hQ
  haveI : Module.Finite ℤ D.La := D.finLa
  haveI : Module.Finite ℚ (VQ D) := Module.Finite.base_change ℤ ℚ D.La
  refine equiv_of_spans A.th Q A.span hQ.2.1 A.dim ?_
  rw [← A.dim, A.dimg]
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ExistsPosForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_pos_form {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (h1 : sigPosH hA = 1) :
    ∃ w : Fin n → ℂ, 0 < (star w ⬝ᵥ (A *ᵥ w)).re := by
  have hne : Nonempty {i : Fin n // 0 < hA.eigenvalues i} := by
    apply Fintype.card_pos_iff.1
    unfold sigPosH at h1
    omega
  obtain ⟨i, hi⟩ := hne
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single i 1, ?_⟩
  rw [GlobalTheory.SignatureOneForms.form_re_eq_sum hA]
  have hU : star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ
      ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ Pi.single i 1) = Pi.single i 1 := by
    rw [Matrix.mulVec_mulVec, Unitary.coe_star_mul_self, Matrix.one_mulVec]
  rw [hU, Finset.sum_eq_single i]
  · simpa using hi
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem UpperTheory.Gal.W2.sigB_of :
    UpperTheory.Gal.W2.SigB := by
  intro p _ G B v
  obtain ⟨hH, hdet, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v B.β B.sym B.trivR
  have hZi : (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hiZ : ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ x y : Fin G.n → ℂ, hv (GlobalTheory.LKCx.herm G v B.β) x y =
      star ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ y) ⬝ᵥ
        (G.gram v *ᵥ ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x)) := by
    intro x y
    unfold hv
    rw [hZ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have hinj : ∀ x : Fin G.n → ℂ, x ≠ 0 → (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x ≠ 0 := by
    intro x hx h0
    apply hx
    have h2 := congrArg (fun w => ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) h0
    simpa [Matrix.mulVec_mulVec, hiZ] using h2
  refine ⟨hH, fun h1 => ⟨?_, ?_⟩, fun h1 => ?_⟩
  · obtain ⟨w, hw⟩ := exists_pos_form (G.gram_herm v) h1
    refine ⟨((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w, ?_⟩
    rw [key, Matrix.mulVec_mulVec, hZi, Matrix.one_mulVec]
    exact hw
  · intro z x hz hx hxz
    rw [key] at hz hxz ⊢
    exact GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one (G.gram v) (G.gram_herm v) (G.gram_det v) h1 _ _ hz hxz (hinj x hx)
  · have h0 : sigPosH (G.gram_herm v) = 0 := by
      rcases G.sig v with h | h
      · exact absurd h.1 h1
      · exact h.1
    intro x hx
    rw [key]
    exact GlobalTheory.herm_negDef_of_sigPosH_eq_zero (G.gram v) (G.gram_herm v) (G.gram_det v) h0 _ (hinj x hx)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ExistsCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_coords {K C V : Type} [Field K] [Ring C] [Algebra K C] [Algebra ℚ K] [Algebra ℚ C]
    [IsScalarTower ℚ K C] [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] [FiniteDimensional ℚ K]
    [FiniteDimensional K C] (n : ℕ)
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hinj : Function.Injective rep) (hC : Module.finrank K C = n ^ 2)
    (hdim : Module.finrank ℚ V = n * Module.finrank ℚ K) :
    ∃ (kp : V ≃+ (Fin n → K)) (σ : C ≃ₐ[K] Matrix (Fin n) (Fin n) K), ∀ c w, kp (rep c w) = σ c *ᵥ kp w := by
  let f : K →+* Module.End ℚ V := (rep : C →+* Module.End ℚ V).comp (algebraMap K C)
  letI : Module K V := Module.compHom V f
  have hsm : ∀ (x : K) (w : V), x • w = rep (algebraMap K C x) w := fun _ _ => rfl
  haveI : IsScalarTower ℚ K V := by
    refine ⟨fun q x w => ?_⟩
    rw [hsm, hsm, ← IsScalarTower.toAlgHom_apply ℚ K C, map_smul, map_smul]
    rfl
  haveI : Module.Finite K V := Module.Finite.of_restrictScalars_finite ℚ K V
  have hfin : Module.finrank K V = n := by
    have h := Module.finrank_mul_finrank ℚ K V
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
    rw [hdim, mul_comm n] at h
    exact Nat.eq_of_mul_eq_mul_left hpos h
  let b : Module.Basis (Fin n) K V := Module.finBasisOfFinrankEq K V hfin
  let r : C →ₐ[K] Module.End K V := AlgHom.ofLinearMap
    { toFun := fun c =>
        { toFun := rep c
          map_add' := map_add _
          map_smul' := fun x w => by
            simp only [RingHom.id_apply, hsm]
            rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Algebra.commutes] }
      map_add' := fun c c' => by ext w; simp
      map_smul' := fun x c => by
        ext w
        simp [hsm, Algebra.smul_def, Module.End.mul_apply] }
    (by ext w; simp) (fun c c' => by ext w; simp [Module.End.mul_apply])
  have hr : ∀ c w, r c w = rep c w := fun _ _ => rfl
  let s : C →ₐ[K] Matrix (Fin n) (Fin n) K := (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp r
  have hsinj : Function.Injective s := by
    intro c c' h
    have h' : r c = r c' := (LinearMap.toMatrixAlgEquiv b).injective h
    apply hinj
    ext w
    exact congrArg (fun g => g w) h'
  have hrk : Module.finrank K C = Module.finrank K (Matrix (Fin n) (Fin n) K) := by
    rw [hC, Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]
    ring
  have hsurj : Function.Surjective s :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := s.toLinearMap) hrk).1 hsinj
  refine ⟨b.equivFun.toAddEquiv, AlgEquiv.ofBijective s ⟨hsinj, hsurj⟩, fun c w => ?_⟩
  have h := LinearMap.toMatrix_mulVec_repr b b (r c) w
  exact h.symm

theorem UpperTheory.Gal.W2.fMat_of :
    UpperTheory.Gal.W2.FMat := by
  intro p _ D G L hm
  haveI := D.freeLa
  haveI := D.finLa
  have hK : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    ((AlgEquiv.ofRingEquiv (f := L.e) (fun q => map_ratCast L.e q)).toLinearEquiv.finrank_eq).symm
  have hdim : Module.finrank ℚ (VQ D) = G.n * Module.finrank ℚ G.F := by
    rw [Module.finrank_baseChange, D.rankLa, hm, Nat.one_mul, L.n_eq, hK]
  exact exists_coords G.n L.rep L.rep_inj G.rankC hdim
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PLineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem one_add_col_mul_rank_one_mulVec {n : ℕ} (u w v : Fin n → ℂ) :
    (1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit w) *ᵥ v = v + (w ⬝ᵥ v) • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.replicateCol_apply,
    Matrix.replicateRow_apply, Finset.univ_unique, Finset.sum_singleton, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

private theorem hv_sub_smul_left {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x y z : Fin n → ℂ) (a : ℂ) :
    hv M (x - a • y) z = hv M x z - a * hv M y z := by
  simp [hv, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul]

theorem UpperTheory.Gal.W2.lineBasis_of :
    UpperTheory.Gal.W2.LineBasis := by
  intro n M z _ hpos
  have hz : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    have : z = 0 := funext h
    subst this
    simp [hv] at hpos
  obtain ⟨i₀, hi₀⟩ := hz
  have hφ : hv M z z ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  set e : Fin n → ℂ := Pi.single i₀ 1 with he
  set c : Fin n → ℂ := fun j => if j = i₀ then 0 else hv M (Pi.single j 1) z / hv M z z with hc
  refine ⟨i₀, (1 + Matrix.replicateCol Unit (z - e) * Matrix.replicateRow Unit e) *
    (1 + Matrix.replicateCol Unit (-e) * Matrix.replicateRow Unit c), ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_one_add_replicateCol_mul_replicateRow,
      Matrix.det_one_add_replicateCol_mul_replicateRow]
    have h1 : e ⬝ᵥ (z - e) = z i₀ - 1 := by
      simp [he, dotProduct_sub]
    have h2 : c ⬝ᵥ (-e) = 0 := by
      simp [he, hc]
    rw [h1, h2]
    simpa using hi₀
  · rw [← Matrix.mulVec_mulVec, one_add_col_mul_rank_one_mulVec, one_add_col_mul_rank_one_mulVec]
    have h2 : c ⬝ᵥ e = 0 := by simp [he, hc]
    have h3 : e ⬝ᵥ e = 1 := by simp [he]
    rw [h2]
    simp [h3, he]
  · intro i hi
    rw [← Matrix.mulVec_mulVec, one_add_col_mul_rank_one_mulVec, one_add_col_mul_rank_one_mulVec]
    have h2 : c ⬝ᵥ (Pi.single i 1 : Fin n → ℂ) = hv M (Pi.single i 1) z / hv M z z := by
      simp [hc, hi]
    have h3 : e ⬝ᵥ ((Pi.single i 1 : Fin n → ℂ) + (hv M (Pi.single i 1) z / hv M z z) • (-e)) =
        - (hv M (Pi.single i 1) z / hv M z z) := by
      simp [he, dotProduct_add, Pi.single_apply, hi]
    rw [h2, h3]
    have h4 : (Pi.single i 1 : Fin n → ℂ) + (hv M (Pi.single i 1) z / hv M z z) • (-e) +
        (-(hv M (Pi.single i 1) z / hv M z z)) • (z - e) =
        (Pi.single i 1 : Fin n → ℂ) - (hv M (Pi.single i 1) z / hv M z z) • z := by
      ext a
      simp
      ring
    rw [h4, hv_sub_smul_left]
    field_simp
    ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PHermOfJ
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.hermOfJ_of :
    UpperTheory.Gal.W2.HermOfJ := by
  intro g E halt hI hpos
  have hskew : ∀ x y, E x y = - E y x := by
    intro x y
    have h := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt, zero_add, add_zero] at h
    linarith
  have hII : ∀ x : Fin g → ℂ, Complex.I • Complex.I • x = -x := by
    intro x
    rw [smul_smul, Complex.I_mul_I]
    simp
  have hcomm : ∀ x y : Fin g → ℂ, E (Complex.I • x) y = E (Complex.I • y) x := by
    intro x y
    have h := hI (Complex.I • x) y
    rw [hII, map_neg, LinearMap.neg_apply] at h
    rw [← h, hskew x]
    ring
  let H : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun x y => ⟨E (Complex.I • x) y, E x y⟩
  have hsym : ∀ x y, H y x = star (H x y) := by
    intro x y
    apply Complex.ext
    · simpa [H] using hcomm y x
    · simpa [H] using hskew y x
  have hadd : ∀ a b y, H (a + b) y = H a y + H b y := by
    intro a b y
    apply Complex.ext <;> simp [H, smul_add]
  have hsmulI : ∀ x y, H (Complex.I • x) y = Complex.I * H x y := by
    intro x y
    apply Complex.ext
    · simp [H, hII]
    · simp [H]
  have hsmulR : ∀ (r : ℝ) x y, H (r • x) y = (r : ℂ) * H x y := by
    intro r x y
    apply Complex.ext
    · simp [H, smul_comm Complex.I r x]
    · simp [H]
  have hsmul : ∀ (c : ℂ) x y, H (c • x) y = c * H x y := by
    intro c x y
    have hc : c • x = c.re • x + c.im • (Complex.I • x) := by
      ext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
      conv_lhs => rw [← Complex.re_add_im c]
      ring
    rw [hc, hadd, hsmulR, hsmulR, hsmulI]
    conv_rhs => rw [← Complex.re_add_im c]
    ring
  let e : Fin g → Fin g → ℂ := fun i j => if i = j then 1 else 0
  have hexp : ∀ x y, H x y = ∑ i, x i * H (e i) y := by
    intro x y
    let f : (Fin g → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun x => H x y
        map_add' := fun a b => hadd a b y
        map_smul' := fun c a => by simpa using hsmul c a y }
    simpa [f, e] using LinearMap.pi_apply_eq_sum_univ f x
  have hform : ∀ x y, hermForm (Matrix.of fun i j => H (e i) (e j)) x y = H x y := by
    intro x y
    rw [hexp x y]
    simp only [hermForm, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [hsym y (e i), hexp y (e i), star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', ← hsym (e j) (e i), mul_comm]
  refine ⟨Matrix.of fun i j => H (e i) (e j), ?_, ?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [Matrix.of_apply]
    rw [← hsym]
  · intro z hz
    rw [hform]
    exact hpos z hz
  · intro x y
    rw [hform]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.SNOf
open scoped Matrix

namespace UpperTheory.Gal.W2

theorem sN_of : SN := by
  intro F K _ _ n τ ψ hψ
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, by simp, fun M => Subsingleton.elim _ _⟩
  have i0 : Fin n := ⟨0, hn⟩
  haveI : Nonempty (Fin n) := ⟨i0⟩
  have hsc : ∀ {R : Type} [Field R] (i k : Fin n) (x : R),
      Matrix.single i k x = Matrix.scalar (Fin n) x * Matrix.single i k 1 := by
    intro R _ i k x
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hsum1 : ∀ {R : Type} [Field R], (∑ k : Fin n, Matrix.single k k (1 : R)) = 1 := by
    intro R _
    ext r s
    rw [Matrix.sum_apply, Finset.sum_eq_single r]
    · by_cases h : r = s
      · subst h
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, Matrix.one_apply, h]
    · intro k _ hk
      simp [Matrix.single_apply, hk]
    · simp
  have hEE : ∀ i j j' k, ψ (Matrix.single i j 1) * ψ (Matrix.single j' k 1) =
      if j = j' then ψ (Matrix.single i k 1) else 0 := by
    intro i j j' k
    rw [← map_mul]
    split_ifs with h
    · subst h
      rw [Matrix.single_mul_single_same, one_mul]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h _, map_zero]
  have hP : ψ (Matrix.single i0 i0 1) ≠ 0 := by
    intro h0
    have hk : ∀ k, ψ (Matrix.single k k 1) = 0 := by
      intro k
      have e1 : ψ (Matrix.single k k 1) = ψ (Matrix.single k i0 1) * ψ (Matrix.single i0 i0 1) *
          ψ (Matrix.single i0 k 1) := by
        rw [hEE k i0 i0 i0, if_pos rfl, hEE k i0 i0 k, if_pos rfl]
      rw [e1, h0, mul_zero, zero_mul]
    have h1 : ψ 1 = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hsum1 (R := F), map_sum]
      exact Finset.sum_eq_zero fun k _ => hk k
    rw [map_one] at h1
    exact one_ne_zero h1
  obtain ⟨a, b, hab⟩ : ∃ a b, ψ (Matrix.single i0 i0 1) a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (Matrix.ext h)
  have hL : ∀ i k, ψ (Matrix.single i k 1) * (∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1) =
      ψ (Matrix.single i i0 1) * Matrix.single b k 1 := by
    intro i k
    rw [Finset.mul_sum]
    have l1 : ∀ j, ψ (Matrix.single i k 1) * (ψ (Matrix.single j i0 1) * Matrix.single b j 1) =
        if k = j then ψ (Matrix.single i i0 1) * Matrix.single b k 1 else 0 := by
      intro j
      rw [← mul_assoc, hEE]
      split_ifs with h
      · subst h
        rfl
      · rw [zero_mul]
    simp only [l1, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hR : ∀ i k, (∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1) * Matrix.single i k 1 =
      ψ (Matrix.single i i0 1) * Matrix.single b k 1 := by
    intro i k
    rw [Finset.sum_mul]
    have l2 : ∀ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1 * Matrix.single i k 1 =
        if j = i then ψ (Matrix.single i i0 1) * Matrix.single b k 1 else 0 := by
      intro j
      rw [mul_assoc]
      split_ifs with h
      · subst h
        rw [Matrix.single_mul_single_same, one_mul]
      · rw [Matrix.single_mul_single_of_ne _ _ _ _ h _, mul_zero]
    simp only [l2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1, ?_, ?_⟩
  · have hTS : (∑ k, Matrix.single k a (ψ (Matrix.single i0 i0 1) a b)⁻¹ * ψ (Matrix.single i0 k 1)) *
        (∑ j, ψ (Matrix.single j i0 1) * Matrix.single b j 1) = 1 := by
      rw [Finset.sum_mul, ← hsum1 (R := K)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, hL, ← mul_assoc, Matrix.single_mul_mul_single, inv_mul_cancel₀ hab, one_mul]
    have hd := congrArg Matrix.det hTS
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact right_ne_zero_of_mul_eq_one hd
  · intro M
    have hM : M = ∑ i, ∑ k, Matrix.scalar (Fin n) (M i k) * Matrix.single i k 1 := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single M]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsc i k (M i k)
    have hMt : M.map τ = ∑ i, ∑ k, Matrix.scalar (Fin n) (τ (M i k)) * Matrix.single i k 1 := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single (M.map τ)]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsc i k _
    rw [hMt]
    conv_lhs => rw [hM]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hψ, mul_assoc, hL, ← hR, ← mul_assoc, ← mul_assoc,
      (Matrix.scalar_commute (τ (M i k)) (fun r' => Commute.all _ r') _).eq]

end UpperTheory.Gal.W2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PArchSpan
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumOverPlacesFibre
open scoped Classical

theorem UpperTheory.Reformulated.B.SumOverPlacesFibre.sum_fibre_place :
    ∀ (F : Type) [inst : Field F]
    [inst_1 : NumberField F] [NumberField.IsTotallyComplex F] (x : F) (v : NumberField.InfinitePlace F),
    ∑ φ : F →+* ℂ with NumberField.InfinitePlace.mk φ = v, (φ : F → ℂ) x =
      (↑((2 : ℝ) * ((v.embedding : F → ℂ) x).re) : ℂ) := by
  intro F _ _ _ x v
  have hc : v.IsComplex := NumberField.IsTotallyComplex.isComplex v
  have hne : v.embedding ≠ NumberField.ComplexEmbedding.conjugate v.embedding := by
    intro h
    exact (NumberField.InfinitePlace.isComplex_iff.mp hc)
      (NumberField.ComplexEmbedding.isReal_iff.mpr h.symm)
  have hset : (Finset.univ.filter fun φ : F →+* ℂ => NumberField.InfinitePlace.mk φ = v) =
      {v.embedding, NumberField.ComplexEmbedding.conjugate v.embedding} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have h' : NumberField.InfinitePlace.mk v.embedding = NumberField.InfinitePlace.mk φ := by
        rw [NumberField.InfinitePlace.mk_embedding, h]
      rcases NumberField.InfinitePlace.mk_eq_iff.mp h' with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr h1.symm
    · rintro (h | h)
      · rw [h, NumberField.InfinitePlace.mk_embedding]
      · rw [h, NumberField.InfinitePlace.mk_conjugate_eq, NumberField.InfinitePlace.mk_embedding]
  rw [hset, Finset.sum_pair hne, NumberField.ComplexEmbedding.conjugate_coe_eq,
    Complex.add_conj]
end

noncomputable section

open NumberField

namespace UpperTheory.Gal.W2

private theorem two_mul_card_places (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] :
    2 * Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
  rw [← InfinitePlace.card_add_two_mul_card_eq_rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero F]
  ring

open scoped Classical in
private theorem sum_fibre_place (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (x : F)
    (v : InfinitePlace F) :
    ∑ φ : F →+* ℂ with InfinitePlace.mk φ = v, φ x = ((2 * (v.embedding x).re : ℝ) : ℂ) :=
  _root_.UpperTheory.Reformulated.B.SumOverPlacesFibre.sum_fibre_place F x v

private theorem trace_eq_sum_places (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ v : InfinitePlace F, 2 * (v.embedding x).re := by
  classical
  have h1 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := x)
    rw [eq_ratCast] at h
    let e : (F →ₐ[ℚ] ℂ) ≃ (F →+* ℂ) :=
      { toFun := fun σ => σ.toRingHom
        invFun := fun φ => φ.toRatAlgHom
        left_inv := fun σ => by ext a; rfl
        right_inv := fun φ => by ext a; rfl }
    exact h.trans (Fintype.sum_equiv e _ _ fun _ => rfl)
  have h2 : ∑ φ : F →+* ℂ, φ x =
      ∑ v : InfinitePlace F, ∑ φ : F →+* ℂ with InfinitePlace.mk φ = v, φ x :=
    (Finset.sum_fiberwise _ _ _).symm
  have h3 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((∑ v : InfinitePlace F, 2 * (v.embedding x).re : ℝ) : ℂ) := by
    rw [h1, h2, Finset.sum_congr rfl fun v _ => sum_fibre_place F x v, Complex.ofReal_sum]
  have h4 : (((Algebra.trace ℚ F x : ℚ) : ℝ) : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
    push_cast
    rfl
  exact Complex.ofReal_injective (h4.trans h3)

private theorem span_top (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (n : ℕ) :
    Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) =>
      v.embedding (x i)) = ⊤ := by
  classical
  refine eq_top_iff.2 fun y _ => ?_
  set T := Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) =>
    v.embedding (x i)) with hT
  have hs : ∀ (i : Fin n) (g : InfinitePlace F → ℂ),
      (fun v => Pi.single i (g v) : InfinitePlace F → Fin n → ℂ) ∈ T := by
    intro i g
    let S : (InfinitePlace F → ℂ) →ₗ[ℝ] (InfinitePlace F → Fin n → ℂ) :=
      { toFun := fun g v => Pi.single i (g v)
        map_add' := fun a b => by funext v; simp [Pi.single_add]
        map_smul' := fun r a => by
          funext v j
          by_cases h : j = i
          · subst h
            simp
          · simp [h] }
    have hle : Submodule.span ℝ (Set.range fun (a : F) (v : InfinitePlace F) => v.embedding a) ≤
        T.comap S := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      refine Submodule.subset_span ⟨Pi.single i a, ?_⟩
      funext v j
      by_cases h : j = i
      · subst h
        simp [S]
      · simp [S, h]
    exact hle (by rw [GlobalTheory.LKTrip.HTGroup.span_real_embedding_places]; trivial)
  have hy : y = ∑ i : Fin n, fun v => (Pi.single i (y v i) : Fin n → ℂ) := by
    funext v j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hy]
  exact Submodule.sum_mem _ fun i _ => hs i fun v => y v i

theorem archSpan_of : ArchSpan := by
  intro F _ _ _ n
  refine ⟨span_top F n, ?_, trace_eq_sum_places F⟩
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [← two_mul_card_places F]
  ring

end UpperTheory.Gal.W2
end
end
