module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import ReciprocityTheory.ThetaQuasiPeriods.Transl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.ThetaOnto

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a := by
  unfold constFn
  rw [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_map]

theorem constFn_zero {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) :
    constFn p U 0 = 0 := by
  unfold constFn
  rw [map_zero, map_zero]

def secComb {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {K : Type}
    [Fintype K] (a : K → R) (s : K → L.Sec) : L.Sec where
  f j := ∑ i, constFn p _ (a i) * (s i).f j
  compat j k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (s i).compat j k]
    ring

def secConst {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (L : LB X) (a : R) :
    (lbPow L 0).Sec where
  f j := constFn p _ a
  compat j k := by
    have : (lbPow L 0).g j k = 1 := by
      unfold lbPow LB.LinComb
      dsimp only
      exact Finset.prod_eq_one fun _ _ => zpow_zero _
    rw [res_constFn, res_constFn, this, Units.val_one, _root_.one_mul]

theorem mem_span_of_card_le {V : Type} [AddCommGroup V] [Module ℂ V] (Q : V → Prop) {N : ℕ}
    (hN : ∀ (M : ℕ) (f : Fin M → V), (∀ k, Q (f k)) → LinearIndependent ℂ f → M ≤ N)
    (f : Fin N → V) (hf : ∀ k, Q (f k)) (hli : LinearIndependent ℂ f) {v : V} (hv : Q v) :
    ∃ a : Fin N → ℂ, ∑ i, a i • f i = v := by
  by_contra hne
  have hv' : v ∉ Submodule.span ℂ (Set.range f) := by
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact hne
  have hli' : LinearIndependent ℂ (Fin.cons v f : Fin (N + 1) → V) :=
    linearIndependent_finCons.mpr ⟨hli, hv'⟩
  have hQ : ∀ k, Q ((Fin.cons v f : Fin (N + 1) → V) k) := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using hv
    · simpa using hf i
  have := hN (N + 1) _ hQ hli'
  omega

theorem theta_from_section :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Bijective Ef → ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, Differentiable ℂ (f k) ∧ ∀ (l : Λ) z, f k (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) ^ n * f k z) → LinearIndependent ℂ f → N ≤ n ^ g) → (∀ (P : Out.PolAV (Sp ℂ)) (n : ℕ), 1 ≤ n → ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ, (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ → (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef → ∀ (n : ℕ) θ, u.IsThetaFn Hm χ n θ → ∃ s, u.IsFnPow n s θ) := by
  intro hval hdim hsec hfun P u Hm χ Ef hAH hfr hEf n θ hθ
  have hpt : ∀ z, (u.ex z).left ≫ P.A.hom = 𝟙 _ := fun z => Over.w (u.ex z)
  have hconst : ∀ z (U : P.A.left.Opens) (a : ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ U →
      valAt' (u.ex z).left U (constFn P.A.hom U a) = a :=
    fun z U a hU => (hval _ _).2.2.2.2.2 P.A.hom (hpt z) U a hU
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    have hper : ∀ (l : u.Λ) z, θ (z + l) = θ z := fun l z => by
      rw [hθ.2 l z, pow_zero, _root_.one_mul]
    have := u.discrete
    have : IsZLattice ℝ u.Λ := ⟨u.full⟩
    let b := (Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis ℝ u.Λ
    have hb : Bornology.IsBounded (Set.range θ) := by
      have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
        Metric.isCompact_of_isClosed_isBounded isClosed_closure
          (ZSpan.fundamentalDomain_isBounded b).closure
      refine (hK.image hθ.1.continuous).isBounded.subset ?_
      rintro _ ⟨z, rfl⟩
      refine ⟨ZSpan.fract b z, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), ?_⟩
      have hfl : ((ZSpan.floor b z : _) : Fin P.g → ℂ) ∈ u.Λ := by
        have h : ((ZSpan.floor b z : _) : Fin P.g → ℂ) ∈ Submodule.span ℤ (Set.range b) :=
          (ZSpan.floor b z).2
        exact ((Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis_span ℝ).le h
      rw [← hper ⟨_, hfl⟩ (ZSpan.fract b z), ZSpan.fract_apply, sub_add_cancel]
    have hc : ∀ z, θ z = θ 0 := fun z => hθ.1.apply_eq_apply_of_bounded hb z 0
    refine ⟨secConst P.A.hom P.L (θ 0), ?_⟩
    intro j z hz
    show valAt' _ _ (constFn P.A.hom _ (θ 0)) = _
    rw [hconst z _ _ hz, pow_zero, _root_.mul_one, hc z]
  ·
    obtain ⟨s, hs⟩ := hsec P n hn
    have hex : ∀ i, ∃ T, u.IsThetaFn Hm χ n T ∧ u.IsFnPow n (s i) T :=
      fun i => ((hfun P u Hm χ Ef hfr n).1 (s i)).exists
    choose T hT using hex
    have hcomb : ∀ a : Fin (n ^ P.g) → ℂ,
        u.IsFnPow n (secComb P.A.hom a s) (fun z => ∑ i, a i * T i z) := by
      intro a j z hz
      obtain ⟨e, he⟩ := (hval _ (u.ex z).left).2.1 _ hz
      have hca : ∀ i, e (constFn P.A.hom ((lbPow P.L n).U j) (a i)) = a i := fun i => by
        rw [← he]; exact hconst z _ (a i) hz
      have hsi : ∀ i, e ((s i).f j) = T i z * u.fr (j PUnit.unit) z ^ n := fun i => by
        rw [← he]; exact (hT i).2 j z hz
      rw [he]
      show e (∑ i, constFn P.A.hom _ (a i) * (s i).f j) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hca, hsi, _root_.mul_assoc]
    have hli : LinearIndependent ℂ T := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have hz : ∀ z, ∑ i, a i * T i z = 0 := fun z => by
        simpa [Finset.sum_apply] using congrFun ha z
      have h0 : u.IsFnPow n (secComb P.A.hom (0 : Fin (n ^ P.g) → ℂ) s)
          (fun z => ∑ i, a i * T i z) := by
        intro j z hz'
        rw [hcomb 0 j z hz']
        simp [hz]
      have heq := (hfun P u Hm χ Ef hfr n).2 _ _ _ (hcomb a) h0
      have ha0 : a = 0 := by
        apply hs a
        intro j
        have hj := congrArg (fun t => LB.Sec.f t j) heq
        simp only [secComb] at hj
        rw [hj]
        simp [constFn_zero]
      intro i
      rw [ha0]
      rfl
    obtain ⟨a, ha⟩ := mem_span_of_card_le (u.IsThetaFn Hm χ n)
      (fun M f hf hlin => hdim P.g u.Λ u.discrete u.full Hm χ Ef hfr.1 hAH.2.1 hfr.2.1 hfr.2.2.1 hEf
        n hn M f (fun k => ⟨(hf k).1, fun l z => (hf k).2 l z⟩) hlin)
      T (fun i => (hT i).1) hli hθ
    refine ⟨secComb P.A.hom a s, ?_⟩
    intro j z hz
    rw [hcomb a j z hz, ← ha]
    simp [Finset.sum_apply]

end GlobalTheory.ThetaOnto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.HolChart

theorem exists_etale_coords_vanishing {g : ℕ} {A : Type} [CommRing A] (c : ℂ →+* A)
    (hc : c.IsStandardSmoothOfRelativeDimension g) (e : A →+* ℂ) (he : ∀ a, e (c a) = a) :
    ∃ φ : MvPolynomial (Fin g) ℂ →+* A, φ.comp MvPolynomial.C = c ∧ φ.Etale ∧
      ∀ i, e (φ (MvPolynomial.X i)) = 0 := by
  obtain ⟨φ, h1, h2⟩ := hc.exists_etale_mvPolynomial
  let a : Fin g → ℂ := fun i => e (φ (MvPolynomial.X i))
  let T : MvPolynomial (Fin g) ℂ ≃ₐ[ℂ] MvPolynomial (Fin g) ℂ :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (a i))
      (MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (a i))
      (by ext i; simp) (by ext i; simp)
  have hC : ∀ x, φ (MvPolynomial.C x) = c x := fun x => by rw [← h1]; rfl
  refine ⟨φ.comp T.toRingEquiv.toRingHom, ?_, ?_, ?_⟩
  · ext x
    simp [T, hC]
  · exact RingHom.Etale.respectsIso.2 φ T.toRingEquiv h2
  · intro i
    simp [T, hC, he, a]

theorem derivation_eq_zero {g : ℕ} {A : Type} [CommRing A] (φ : MvPolynomial (Fin g) ℂ →+* A)
    (hφ : φ.Etale) (e : A →+* ℂ) (D : A →+ ℂ) (h0 : ∀ a, D (φ (MvPolynomial.C a)) = 0)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f)
    (hX : ∀ i, D (φ (MvPolynomial.X i)) = 0) : D = 0 := by
  have h1 : D 1 = 0 := by simpa using h0 1
  have hP : ∀ p, D (φ p) = 0 := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, add_zero]
    | mul_X p i hp => rw [map_mul, hm, hp, hX]; simp
  let F : A →+* DualNumber ℂ :=
    { toFun := fun f => TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr (D f)
      map_one' := by ext <;> simp [h1]
      map_mul' := fun f f' => by ext <;> simp [hm, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun f f' => by ext <;> simp }
  let F₀ : A →+* DualNumber ℂ := (algebraMap ℂ (DualNumber ℂ)).comp e
  have hFF : ∀ p, F (φ p) = F₀ (φ p) := fun p => by
    ext <;> simp [F, F₀, hP, TrivSqZeroExt.algebraMap_eq_inl]
  let _ := φ.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) ℂ) (DualNumber ℂ) := (F₀.comp φ).toAlgebra
  have _ : Algebra.Etale (MvPolynomial (Fin g) ℂ) A := hφ
  let G : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ :=
    { F with commutes' := hFF }
  let G₀ : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ := { F₀ with commutes' := fun p => rfl }
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom hnil G G₀
    (fun x => by simp [G, G₀, F, F₀])
  ext f
  have := congrArg (fun H : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ => (H f).snd) hG
  simpa [G, G₀, F, F₀, TrivSqZeroExt.algebraMap_eq_inl] using this

theorem hol_of_affine
    (hval : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {g : ℕ} {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {W : Set (Fin g → ℂ)} (hW : IsOpen W)
    (s : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (hs : ∀ w ∈ W, ⊤ ≤ s w ⁻¹ᵁ U)
    (hd : ∀ a : Γ(X, U), DifferentiableOn ℂ (fun w => valAt' (s w) U a) W)
    (V : X.Opens) (f : Γ(X, V)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} ∧
      DifferentiableOn ℂ (fun w => valAt' (s w) V f) {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} := by
  have key : ∀ w₀ ∈ {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V}, {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} ∈ 𝓝 w₀ ∧
      DifferentiableAt ℂ (fun w => valAt' (s w) V f) w₀ := by
    rintro w₀ ⟨hw₀, hV⟩
    obtain ⟨h, hhV, hh⟩ := hU.exists_basicOpen_le (V := V) ⟨_, ((hval X (s w₀)).1 V).1 hV⟩
      (((hval X (s w₀)).1 U).1 (hs w₀ hw₀))
    have hB₀ : ⊤ ≤ s w₀ ⁻¹ᵁ X.basicOpen h := ((hval X (s w₀)).1 _).2 hh
    have hne₀ : valAt' (s w₀) U h ≠ 0 := ((hval X (s w₀)).2.2.2.2.1 U h).1 hB₀
    have hWn : W ∈ 𝓝 w₀ := hW.mem_nhds hw₀
    have hda : ∀ a : Γ(X, U), DifferentiableAt ℂ (fun w => valAt' (s w) U a) w₀ := fun a =>
      (hd a w₀ hw₀).differentiableAt hWn
    have hN : ∀ᶠ w in 𝓝 w₀, w ∈ W ∧ valAt' (s w) U h ≠ 0 :=
      Filter.Eventually.and hWn ((hda h).continuousAt.eventually_ne hne₀)
    have _ := hU.isLocalization_basicOpen h
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG X hhV f)
    refine ⟨hN.mono fun w hw => ⟨hw.1, ?_⟩, ?_⟩
    · exact ((hval X (s w)).1 V).2
        (hhV (((hval X (s w)).1 _).1 (((hval X (s w)).2.2.2.2.1 U h).2 hw.2)))
    · have hq : DifferentiableAt ℂ (fun w => valAt' (s w) U a * (valAt' (s w) U h ^ n)⁻¹) w₀ :=
        (hda a).mul (((hda h).pow n).inv (pow_ne_zero n hne₀))
      refine DifferentiableAt.congr_of_eventuallyEq hq (hN.mono fun w hw => ?_)
      have hB : ⊤ ≤ s w ⁻¹ᵁ X.basicOpen h := ((hval X (s w)).2.2.2.2.1 U h).2 hw.2
      obtain ⟨ev, hev⟩ := (hval X (s w)).2.1 _ hB
      have r1 := (hval X (s w)).2.2.1 V _ hhV f hB
      have r2 := (hval X (s w)).2.2.1 U _ (X.basicOpen_le h) a hB
      have r3 := (hval X (s w)).2.2.1 U _ (X.basicOpen_le h) h hB
      have ha' : resG X hhV f * resG X (X.basicOpen_le h) h ^ n = resG X (X.basicOpen_le h) a := ha
      have := congrArg ev ha'
      rw [map_mul, map_pow, ← hev, ← hev, ← hev, r1, r2, r3] at this
      show valAt' (s w) V f = valAt' (s w) U a * (valAt' (s w) U h ^ n)⁻¹
      rw [← this, mul_inv_cancel_right₀ (pow_ne_zero n hw.2)]
  exact ⟨isOpen_iff_mem_nhds.2 fun w hw => (key w hw).1,
    fun w hw => (key w hw).2.differentiableWithinAt⟩

theorem exists_holomorphic_chart :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ (g : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] [Algebra (MvPolynomial (Fin g) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) A] [Algebra.Etale (MvPolynomial (Fin g) ℂ) A] (e : A →ₐ[ℂ] ℂ), (∀ i, e (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = 0) → ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (A →ₐ[ℂ] ℂ)) (n : ℕ) (f : Fin n → A) (ε : ℝ), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => σ w a) W) ∧ (∀ w ∈ W, ∀ i, σ w (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = w i) ∧ ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → ∃ w ∈ W, x = σ w) → (∀ (X : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g X.hom → ∀ e : (𝟙_ (Over (Sp ℂ)) ⟶ X), ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : X.left.Opens) (t : Fin g → Γ(X.left, U)), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ IsAffineOpen U ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (σ w).left U f) {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U}) ∧ (∀ w ∈ W, ⊤ ≤ (σ w).left ⁻¹ᵁ U ∧ ∀ i, valAt' (σ w).left U (t i) = w i) ∧ IsOpen[(TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})] (σ '' W) ∧ (∀ D : Γ(X.left, U) →+ ℂ, (∀ a, D (constFn X.hom U a) = 0) → (∀ f f', D (f * f') = valAt' e.left U f * D f' + valAt' e.left U f' * D f) → (∀ i, D (t i) = 0) → D = 0)) := by
  intro hval haff hring X g hX e
  let e' : Sp ℂ ⟶ X.left := e.left
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ :=
    hX.exists_isStandardSmoothOfRelativeDimension (e' (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : X.hom (e' (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = X.hom (e' (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact h1
  subst hU₀
  let c : ℂ →+* Γ(X.left, U) :=
    (X.hom.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hcc : ∀ a, constFn X.hom U a = c a := fun a => rfl
  have hc : c.IsStandardSmoothOfRelativeDimension g :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (X.hom.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hsm
  have hpts : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U →
      ∃ ev : Γ(X.left, U) →+* ℂ, (∀ f, valAt' x.left U f = ev f) ∧ ∀ a, ev (c a) = a := by
    intro x hx
    obtain ⟨ev, hev⟩ := (hval X.left x.left).2.1 U hx
    refine ⟨ev, hev, fun a => ?_⟩
    rw [← hev, ← hcc]
    exact (hval X.left x.left).2.2.2.2.2 X.hom (Over.w x) U a hx
  have heU : ⊤ ≤ e.left ⁻¹ᵁ U := ((hval X.left e').1 U).2 hp
  obtain ⟨ev, hev, hevc⟩ := hpts e heU
  obtain ⟨φ, hφc, hφ, hφ0⟩ := exists_etale_coords_vanishing c hc ev hevc
  have hφc' : ∀ a, φ (MvPolynomial.C a) = c a := fun a => by rw [← hφc]; rfl
  let _ : Algebra ℂ Γ(X.left, U) := c.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) ℂ) Γ(X.left, U) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) Γ(X.left, U) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin g) ℂ) Γ(X.left, U) := hφ
  let eA : Γ(X.left, U) →ₐ[ℂ] ℂ := { ev with commutes' := hevc }
  obtain ⟨W, σ, n, f, ε, hW, hW0, hσ0, hε, hσd, hσt, hσs⟩ := hring g Γ(X.left, U) eA hφ0
  have hex : ∀ x : Γ(X.left, U) →ₐ[ℂ] ℂ, ∃! y : (𝟙_ (Over (Sp ℂ)) ⟶ X),
      ⊤ ≤ y.left ⁻¹ᵁ U ∧ ∀ f, valAt' y.left U f = x f := fun x =>
    haff X U hU x.toRingHom (fun a => x.commutes a)
  choose pt hpt hptu using hex
  let W' : Set (Fin g → ℂ) := W ∩ ⋂ k, (W ∩ (fun w => σ w (f k)) ⁻¹' Metric.ball (eA (f k)) ε)
  have hW' : IsOpen W' := hW.inter (isOpen_iInter_of_finite fun k =>
    (hσd (f k)).continuousOn.isOpen_inter_preimage hW Metric.isOpen_ball)
  have hmem : ∀ w, w ∈ W' ↔ w ∈ W ∧ ∀ k, ‖σ w (f k) - eA (f k)‖ < ε := by
    intro w
    simp only [W', Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
    exact ⟨fun h => ⟨h.1, fun k => (h.2 k).2⟩, fun h => ⟨h.1, fun k => ⟨h.1, h.2 k⟩⟩⟩
  refine ⟨W', fun w => pt (σ w), U, fun i => φ (MvPolynomial.X i), hW', ?_, ?_, hU, ?_, ?_, ?_, ?_⟩
  · exact (hmem 0).2 ⟨hW0, fun k => by rw [hσ0, sub_self, norm_zero]; exact hε⟩
  · show pt (σ 0) = e
    rw [hσ0]
    exact (hptu eA e ⟨heU, hev⟩).symm
  · intro V a
    refine hol_of_affine hval hU hW' (fun w => (pt (σ w)).left) (fun w _ => (hpt (σ w)).1)
      (fun b => ?_) V a
    exact ((hσd b).mono Set.inter_subset_left).congr fun w _ => (hpt (σ w)).2 b
  · intro w hw
    exact ⟨(hpt (σ w)).1, fun i => ((hpt (σ w)).2 _).trans (hσt w hw.1 i)⟩
  · have himg : (fun w => pt (σ w)) '' W' =
        {x : 𝟙_ (Over (Sp ℂ)) ⟶ X | ⊤ ≤ x.left ⁻¹ᵁ U ∧ valAt' x.left U 0 ∈ (Set.univ : Set ℂ)} ∩
          ⋂ k, {x : 𝟙_ (Over (Sp ℂ)) ⟶ X | ⊤ ≤ x.left ⁻¹ᵁ U ∧
            valAt' x.left U (f k) ∈ Metric.ball (eA (f k)) ε} := by
      ext x
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_univ,
        and_true, Metric.mem_ball, dist_eq_norm]
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨(hpt (σ w)).1, fun k => ⟨(hpt (σ w)).1, ?_⟩⟩
        rw [(hpt (σ w)).2]
        exact ((hmem w).1 hw).2 k
      · rintro ⟨hx, hk⟩
        obtain ⟨ex, hex, hexc⟩ := hpts x hx
        let xA : Γ(X.left, U) →ₐ[ℂ] ℂ := { ex with commutes' := hexc }
        have hk' : ∀ k, ‖xA (f k) - eA (f k)‖ < ε := fun k => by
          have := (hk k).2
          rw [hex] at this
          exact this
        obtain ⟨w, hw, hxw⟩ := hσs xA hk'
        refine ⟨w, (hmem w).2 ⟨hw, hxw ▸ hk'⟩, ?_⟩
        rw [← hxw]
        exact (hptu xA x ⟨hx, hex⟩).symm
    rw [himg]
    let _ := TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) |
      ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧
        S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}
    refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun k => ?_)
    · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, 0, Set.univ, isOpen_univ, rfl⟩
    · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, f k, _, Metric.isOpen_ball, rfl⟩
  · intro D h0 hm hX
    refine derivation_eq_zero φ hφ ev D (fun a => ?_) (fun a b => ?_) hX
    · rw [hφc', ← hcc]; exact h0 a
    · rw [← hev, ← hev]; exact hm a b

end GlobalTheory.HolChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannFormBijectiveOfWeilNondeg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

section
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem holUnif_ex_zero_eq_one : u.ex 0 = 1 :=
  (u.ker 0).2 (zero_mem _)

theorem holUnif_ex_nsmul_eq_pow (z : Fin g → ℂ) (k : ℕ) : u.ex (k • z) = u.ex z ^ k := by
  induction k with
  | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem holUnif_isZLattice : haveI := u.discrete; IsZLattice ℝ u.Λ := by
  have := u.discrete
  exact ⟨u.full⟩

end

theorem riemannForm_bijective_of_weilNondeg :
    Out.WeilNondegSt → (∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (E : LinearMap.BilinForm ℤ X), (∀ (k : ℕ) (a : X), 0 < k → (∀ b, (k : ℤ) ∣ E a b) → ∃ a', a = (k : ℤ) • a') → Function.Bijective E) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c)) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef) := by
  intro hW hB hE P u Hm χ Ef hc
  have := u.discrete
  have := holUnif_isZLattice u
  apply hB u.Λ Ef
  intro k a hk hdiv
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'

  have hpow : ∀ w : Fin P.g → ℂ, u.ex w ^ k = u.ex ((k : ℂ) • w) := by
    intro w
    rw [← holUnif_ex_nsmul_eq_pow, Nat.cast_smul_eq_nsmul]
  have hx : u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) = 1 := by
    refine hW ℂ P k hk0 _ ?_ ?_
    · rw [hpow, smul_smul, mul_inv_cancel₀ hk0, one_smul]
      exact (u.ker _).2 a.2
    · intro y hy
      obtain ⟨w, rfl⟩ := u.ex_onto y
      have hw : (k : ℂ) • w ∈ u.Λ := (u.ker _).1 (by rw [← hpow]; exact hy)
      set b : u.Λ := ⟨(k : ℂ) • w, hw⟩
      have hwb : w = (k : ℂ)⁻¹ • (b : Fin P.g → ℂ) := by
        simp only [b, smul_smul, inv_mul_cancel₀ hk0, one_smul]
      obtain ⟨m, hm⟩ := hdiv b
      have h1 := hE P u Hm χ Ef hc k a b 1 hk (by
        rw [hm, Units.val_one]
        push_cast
        rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((k : ℂ) * (m : ℂ)) / (k : ℂ)
            = (-m : ℤ) * (2 * Real.pi * Complex.I) by push_cast; field_simp]
        exact (Complex.exp_int_mul_two_pi_mul_I (-m)).symm)
      have hu : unitOn (1 : ℂˣ) = 1 := map_one _
      rw [hu, ← hwb] at h1
      exact h1
  refine ⟨⟨(k : ℂ)⁻¹ • (a : Fin P.g → ℂ), (u.ker _).1 hx⟩, ?_⟩
  ext1
  simp only [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℂ, Int.cast_natCast, smul_smul,
    mul_inv_cancel₀ hk0, one_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowThetaFunctions
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.SectionTheta

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem ex_add_lattice (u : HolUnif A L g) (z : Fin g → ℂ) (l : u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]

theorem quot_eq (u : HolUnif A L g) (z : Fin g → ℂ)
    (hhom : ∀ U : A.left.Opens, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U →
      ∃ e : Γ(A.left, U) →+* ℂ, ∀ f, valAt' (u.ex z).left U f = e f)
    (hres : ∀ (U V : A.left.Opens) (h : V ≤ U) (f : Γ(A.left, U)), ⊤ ≤ (u.ex z).left ⁻¹ᵁ V →
      valAt' (u.ex z).left V (resG A.left h f) = valAt' (u.ex z).left U f)
    (n : ℕ) (s : (lbPow L n).Sec) (j j' : (lbPow L n).ι)
    (hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j) (hj' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow L n).U j') :
    valAt' (u.ex z).left ((lbPow L n).U j) (s.f j) / u.fr (j PUnit.unit) z ^ n =
      valAt' (u.ex z).left ((lbPow L n).U j') (s.f j') / u.fr (j' PUnit.unit) z ^ n := by
  have hW : ⊤ ≤ (u.ex z).left ⁻¹ᵁ ((lbPow L n).U j ⊓ (lbPow L n).U j') :=
    fun p hp => ⟨hj hp, hj' hp⟩
  have hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j PUnit.unit) := Cartier.lbPow_U L n j ▸ hj
  have hi' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j' PUnit.unit) := Cartier.lbPow_U L n j' ▸ hj'
  have hW' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) :=
    fun p hp => ⟨hi hp, hi' hp⟩
  obtain ⟨e, he⟩ := hhom _ hW
  have h1 := hres _ _ (inf_le_left : (lbPow L n).U j ⊓ (lbPow L n).U j' ≤ _) (s.f j) hW
  have h2 := hres _ _ (inf_le_right : (lbPow L n).U j ⊓ (lbPow L n).U j' ≤ _) (s.f j') hW
  have h3 := hres _ _ (inf_le_inf (Cartier.lbPow_U L n j).le (Cartier.lbPow_U L n j').le)
    (L.g (j PUnit.unit) (j' PUnit.unit)).val hW
  have hc : resG A.left (inf_le_left : (lbPow L n).U j ⊓ (lbPow L n).U j' ≤ _) (s.f j) =
      (resG A.left (inf_le_inf (Cartier.lbPow_U L n j).le (Cartier.lbPow_U L n j').le)
        (L.g (j PUnit.unit) (j' PUnit.unit)).val) ^ n *
      resG A.left (inf_le_right : (lbPow L n).U j ⊓ (lbPow L n).U j' ≤ _) (s.f j') := by
    refine (s.compat j j').trans ?_
    exact congrArg (· * _) ((congrArg Units.val (Cartier.lbPow_g L n j j')).trans
      (Units.val_pow_eq_pow_val _ _))
  have hfr := u.fr_compat _ _ z hW'
  have hne := u.fr_ne _ z hi
  have hne' := u.fr_ne _ z hi'
  rw [← h1, ← h2, hc, he, map_mul, map_pow, ← he, ← he, h3]
  rw [hfr] at hne ⊢
  have hg := left_ne_zero_of_mul hne
  rw [mul_pow]
  field_simp

end GlobalTheory.SectionTheta

namespace GlobalTheory

open SectionTheta

theorem sections_pow_theta_functions :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), Smooth p → IsReduced X) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') := by
  intro hval hext hred P u Hm χ Ef hAH n
  obtain ⟨-, -, -, hlaw⟩ := hAH
  have hcov : ∀ z, ∃ j : (lbPow P.L n).ι, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L n).U j := by
    intro z
    have hmem : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, P.L.U i := by
      rw [P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    refine ⟨fun _ => i, ?_⟩
    rw [Cartier.lbPow_U]
    exact ((hval _ (u.ex z).left).1 _).2 hi
  have hU : ∀ z (j : (lbPow P.L n).ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L n).U j →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j PUnit.unit) := fun z j hj => Cartier.lbPow_U P.L n j ▸ hj
  refine ⟨fun s => ?_, fun θ s s' hs hs' => ?_⟩
  · choose c hc using hcov
    let θ : (Fin P.g → ℂ) → ℂ := fun z =>
      valAt' (u.ex z).left ((lbPow P.L n).U (c z)) (s.f (c z)) / u.fr (c z PUnit.unit) z ^ n
    have hθ : ∀ (j : (lbPow P.L n).ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow P.L n).U j →
        θ z = valAt' (u.ex z).left ((lbPow P.L n).U j) (s.f j) / u.fr (j PUnit.unit) z ^ n :=
      fun j z hj => quot_eq u z (hval _ _).2.1 (hval _ _).2.2.1 n s _ _ (hc z) hj
    have hfn : u.IsFnPow n s θ := by
      intro j z hj
      rw [hθ j z hj, div_mul_cancel₀ _ (pow_ne_zero n (u.fr_ne _ z (hU z j hj)))]
    refine ⟨θ, ⟨⟨fun z => ?_, fun l z => ?_⟩, hfn⟩, fun θ' hθ' => ?_⟩
    · obtain ⟨ho, hd⟩ := u.hol _ (s.f (c z))
      have hn := ho.mem_nhds (hc z)
      have hd2 : DifferentiableOn ℂ (u.fr (c z PUnit.unit))
          {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (lbPow P.L n).U (c z)} :=
        (u.fr_hol _).mono fun w hw => hU w _ hw
      have hq := (hd.differentiableAt hn).mul (((hd2.differentiableAt hn).pow n).inv
        (pow_ne_zero n (u.fr_ne _ z (hU z _ (hc z)))))
      refine hq.congr_of_eventuallyEq ?_
      filter_upwards [hn] with w hw
      exact (hθ _ w hw).trans (div_eq_mul_inv _ _)
    · have h1 := hfn (c z) z (hc z)
      have hc' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ (lbPow P.L n).U (c z) := by
        rw [ex_add_lattice]; exact hc z
      have h2 := hfn (c z) (z + l) hc'
      rw [ex_add_lattice, h1, hlaw l _ z (hU z _ (hc z)), mul_pow, ← _root_.mul_assoc] at h2
      have h3 := mul_right_cancel₀ (pow_ne_zero n (u.fr_ne _ _ (hU _ _ hc'))) h2
      rw [← h3, _root_.mul_comm]
      rfl
    · funext z
      have h1 := hfn (c z) z (hc z)
      rw [hθ'.2 (c z) z (hc z)] at h1
      exact mul_right_cancel₀ (pow_ne_zero n (u.fr_ne _ z (hU z _ (hc z)))) h1
  · have hsm : Smooth P.A.hom := by
      have := P.smoothDim
      exact SmoothOfRelativeDimension.smooth P.g P.A.hom
    have hf : s.f = s'.f := by
      funext j
      refine hext P.A (hred _ _ hsm) inferInstance _ _ _ fun x hx => ?_
      obtain ⟨z, rfl⟩ := u.ex_onto x
      rw [hs j z hx, hs' j z hx]
    cases s
    cases s'
    cases hf
    rfl

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsGenTranslDiffComp
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_isGen_linComb_of_pull {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (f : Z ⟶ Y) (c : LB.Gen ((LB.LinComb L φ ε).pull f))
    (hc : c.IsGen) : ∃ d : LB.Gen (LB.LinComb L (fun k => f ≫ φ k) ε), d.IsGen := by
  have hle : ∀ j : K → L.ι, LB.wchart L (fun k => f ≫ φ k) j ≤
      LB.wchart (LB.LinComb L φ ε) (K := PUnit) (fun _ => f) (fun _ => j) :=
    fun j _ hy => Set.mem_iInter.2 fun _ => LB.wchart_comp_le L f φ j hy
  refine ⟨⟨fun j => res (hle j) (LB.ts c (fun _ => j))⟩, ?_⟩
  refine (LB.isGen_iff L _).2 fun i j => ?_
  have key := congrArg (res (inf_le_inf (hle i) (hle j)))
    ((LB.isGen_iff (LB.LinComb L φ ε) c).1 hc (fun _ => i) (fun _ => j))
  have e := LB.lcg_pull (LB.LinComb L φ ε) f (fun _ => i) (fun _ => j)
  rw [LB.lcg_comp]
  refine (LB.res_res _ _ _).trans (((LB.res_res _ _ _).symm.trans key).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · exact (congrArg _ e).trans (LB.res_res _ _ _)
  · exact (LB.res_res _ _ _).trans (LB.res_res _ _ _).symm

theorem exists_isGen_translDiff_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)
    {T T' : Over S} (x : T ⟶ A) (g : T' ⟶ T) (V : T.left.Opens)
    (hg : ∀ q, g.left q ∈ V)
    (c : LB.Gen ((Out.translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι)) (hc : c.IsGen) :
    ∃ d : LB.Gen (Out.translDiff A L (g ≫ x)), d.IsGen := by
  obtain ⟨d, hd⟩ := exists_isGen_linComb_of_pull L _ _ _ c hc
  have hr : Set.range (g ▷ A).left ⊆ Set.range ((fst T A).left ⁻¹ᵁ V).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ((g ▷ A).left ≫ (fst T A).left) y ∈ V
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    exact hg _
  have hl := IsOpenImmersion.lift_fac ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr
  have h4 : ∃ w : LB.Gen (LB.LinComb L _ _), w.IsGen :=
    ⟨_, LB.isGen_pullGen L _ _ d hd (IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr)⟩
  have h3 : (fun k : Fin 2 => IsOpenImmersion.lift ((fst T A).left ⁻¹ᵁ V).ι (g ▷ A).left hr ≫
      ((fst T A).left ⁻¹ᵁ V).ι ≫
        ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] k) =
      ![(lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left, (snd T' A).left] := by
    funext k
    rw [← Category.assoc, hl]
    fin_cases k
    · change (g ▷ A ≫ lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left =
        (lift (fst T' A ≫ g ≫ x) (snd T' A) ≫ μ[A]).left
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    · change (g ▷ A ≫ snd T A).left = (snd T' A).left
      rw [whiskerRight_snd]
  rw [h3] at h4
  exact h4

theorem kTriv_of_global : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB →
    (∀ (R : Type) [CommRing R] [Algebra ℂ R], ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A),
      (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1) → Out.KTriv A L := by
  intro A _ L _ _ H R _ t x hx
  have H' : ∀ (R' : CommRingCat.{0}) (t' : Spec R' ⟶ Sp ℂ) (y : Over.mk t' ⟶ A),
      (∃ c : LB.Gen (Out.translDiff A L y), c.IsGen) → y = 1 := by
    intro R' t'
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t'
    let _ : Algebra ℂ R' := φ.hom.toAlgebra
    exact H R'
  change x = 1
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨V, hp, c, hc⟩ := hx p
  obtain ⟨U, hU, hpU, hUV⟩ := exists_isAffineOpen_mem_and_subset (U := V) (x := p) hp
  refine ⟨U, hpU, ?_⟩
  let g : Over.mk (hU.fromSpec ≫ t) ⟶ Over.mk t := Over.homMk hU.fromSpec rfl
  have h1 : g ≫ x = g ≫ 1 := by
    rw [MonObj.comp_one]
    exact H' _ _ _ (exists_isGen_translDiff_comp A L x g V
      (fun q => hUV (hU.range_fromSpec.le ⟨q, rfl⟩)) c hc)
  have h2 : hU.fromSpec ≫ x.left = hU.fromSpec ≫ (1 : Over.mk t ⟶ A).left :=
    congrArg (·.left) h1
  rw [IsAffineOpen.fromSpec, Category.assoc, Category.assoc, cancel_epi] at h2
  exact h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.PowSec

section Transport

variable {X Y : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)

include e in
theorem chart_eq (j : PUnit → L.ι) :
    LB.wchart L (fun _ : PUnit => 𝟙 X) j = ρ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) := by
  ext y
  have h : σ (ρ y) = y := by rw [← Scheme.Hom.comp_apply, e]; rfl
  constructor
  · intro hy
    refine Set.mem_iInter.2 fun _ => ?_
    have := Set.mem_iInter.1 hy PUnit.unit
    show σ (ρ y) ∈ L.U (j PUnit.unit)
    rw [h]; exact this
  · intro hy
    refine Set.mem_iInter.2 fun _ => ?_
    have : σ (ρ y) ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy 0
    rw [h] at this; exact this

theorem appLE_congr {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens) (h₁ : V ≤ f ⁻¹ᵁ U) (h₂ : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V h₁ = g.appLE U V h₂ := by subst h; rfl

def down (b : (LB.LinComb L (K := Fin 1) (fun _ => σ) (fun _ => n)).Sec) :
    (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => n)).Sec where
  f j := (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (b.f (fun _ => j PUnit.unit))
  compat i j := by
    have hle : LB.wchart L (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) j ≤
      ρ ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) ⊓
        LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit)) :=
      inf_le_inf (chart_eq L σ ρ e i).le (chart_eq L σ ρ e j).le
    have := congrArg (ρ.appLE _ _ hle).hom (b.compat (fun _ => i PUnit.unit) (fun _ => j PUnit.unit))
    replace this := this.trans (map_mul _ _ _)
    refine Eq.trans ?_ (this.trans (congrArg₂ (· * ·) ?_ ?_))
    · exact (congrArg (fun φ => φ.hom (b.f fun _ => i PUnit.unit))
        ((Scheme.Hom.appLE_map ρ _ _).trans (Scheme.Hom.map_appLE ρ hle _).symm) :)
    · simp only [LB.LinComb, Fintype.prod_unique]
      refine (congrArg Units.val ((map_zpow (Units.map (ρ.appLE _ _ hle).hom.toMonoidHom) _ n).trans
        (congrArg (· ^ n) (Units.ext ?_))) :)
      have h1 : (σ.app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) 0)))).op) ≫ ρ.appLE _ _ hle =
          (𝟙 X : X ⟶ X).app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) i PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) j PUnit.unit)))).op :=
        (Scheme.Hom.appLE_comp_appLE ρ σ _ _ _ _ hle).trans (appLE_congr e _ _ _ _)
      exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val) h1
    · exact (congrArg (fun φ => φ.hom (b.f fun _ => j PUnit.unit))
        ((Scheme.Hom.map_appLE ρ hle _).trans (Scheme.Hom.appLE_map ρ _ _).symm) :)

theorem appLE_injective [IsIso ρ] (U : Y.Opens) (V : X.Opens) (h : V = ρ ⁻¹ᵁ U) :
    Function.Injective (ρ.appLE U V h.le).hom := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  exact (ConcreteCategory.bijective_of_isIso (ρ.app U)).1

end Transport

attribute [local instance] Over.cartesianMonoidalCategory


open Out in
theorem exists_indep_sections (H : Out.GlobalSectionsRankAlgClosed) (P : Out.PolAV (Sp ℂ)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ,
      (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0 := by
  have hr := H ℂ P n hn
  let T : Over (Sp ℂ) := baseOver (Sp ℂ)
  let c : Γ(T.left, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  haveI : Nontrivial Γ(T.left, ⊤) := c.symm.injective.nontrivial
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank (R := Γ(T.left, ⊤)) (M := SecM P.A P.L n T) hr.ge
  let ρ : P.A ⟶ T ⊗ P.A := lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)
  have ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom := congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  refine ⟨fun i => down P.L (snd T P.A).left ρ.left ρ₂ n (SecM.toSec P.A (b i)), fun a ha => ?_⟩
  have h0 : ∑ i, c.symm (a i) • b i = 0 := by
    refine Subtype.ext (funext fun j => ?_)
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    refine appLE_injective ρ.left _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)) ?_
    refine Eq.trans ?_ ((ha (fun _ => k)).trans (map_zero _).symm)
    rw [Submodule.coe_sum]
    refine (congrArg _ (Finset.sum_apply _ _ _)).trans ?_
    refine (map_sum (ρ.left.appLE _ _ (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)).le).hom _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    refine (map_mul _ (liftHom P.A _ (c.symm (a i))) ((b i).1 fun _ => k)).trans (congrArg₂ (· * ·) ?_ rfl)
    have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left (fst T P.A).left ⊤ _ _ (fun _ _ => trivial)
      (chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)).le).trans (appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
    exact congrArg (fun φ => φ.hom (c.symm (a i))) h1
  funext i
  exact c.symm.injective ((Fintype.linearIndependent_iff.1 hb _ h0 i).trans (map_zero _).symm)

end GlobalTheory.PowSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsLinearLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.EndoLinear

theorem fderiv_lifts {E E' M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] [Group M] (ex : E' → M) (hex : ∀ z w, ex (z + w) = ex z * ex w)
    (Λ : Submodule ℤ E') (hker : ∀ z, ex z = 1 ↔ z ∈ Λ) (hd : DiscreteTopology Λ)
    (a : E → M) (ha : ∀ z w, a (z + w) = a z * a w) (G : E → E') (h0 : G 0 = 0)
    (hG : DifferentiableAt ℂ G 0) (hev : ∀ᶠ w in 𝓝 0, ex (G w) = a w) (z : E) :
    ex (fderiv ℂ G 0 z) = a z := by
  have hc : ContinuousAt G 0 := hG.continuousAt
  have h2 : Tendsto (fun w : E => w + w) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun w : E => w + w) := by fun_prop
    simpa using this.tendsto 0
  have hG0 : Tendsto G (𝓝 0) (𝓝 0) := by simpa [h0] using hc.tendsto
  have hD : Tendsto (fun w : E => G (w + w) - (G w + G w)) (𝓝 0) (𝓝 0) := by
    simpa using (hG0.comp h2).sub (hG0.add hG0)
  have hmem : ∀ᶠ w in 𝓝 (0 : E), G (w + w) - (G w + G w) ∈ Λ := by
    filter_upwards [hev, h2.eventually hev] with w hw hw2
    rw [← hker]
    have h := hex (G (w + w) - (G w + G w)) (G w + G w)
    rw [sub_add_cancel, hw2, hex (G w), hw, ha] at h
    exact (mul_eq_right.mp h.symm)
  have hiso : ∀ᶠ y in 𝓝 (0 : E'), y ∈ Λ → y = 0 := by
    have ho : IsOpen ({0} : Set Λ) := isOpen_discrete _
    obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp ho
    have h0t : (0 : E') ∈ t := by
      have : (0 : Λ) ∈ Subtype.val ⁻¹' t := by rw [hts]; rfl
      exact this
    filter_upwards [ht.mem_nhds h0t] with y hy hyΛ
    have : (⟨y, hyΛ⟩ : Λ) ∈ Subtype.val ⁻¹' t := hy
    rw [hts] at this
    exact congrArg Subtype.val this
  have hdbl : ∀ᶠ w in 𝓝 (0 : E), G (w + w) = G w + G w := by
    filter_upwards [hmem, hD.eventually hiso] with w h1 h2
    exact sub_eq_zero.mp (h2 h1)
  set c : ℕ → ℂ := fun n => (2 : ℂ) ^ n with hcdef
  have hcn : Tendsto (fun n => ‖c n‖) atTop atTop := by
    simp only [hcdef, norm_pow, Complex.norm_ofNat]
    exact tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  have hz : Tendsto (fun n => (c n)⁻¹ • z) atTop (𝓝 0) := by
    have : Tendsto (fun n => (c n)⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv]
      exact hcn.inv_tendsto_atTop
    simpa using this.smul_const z
  have hhalf : ∀ n, (c n)⁻¹ • z = (c (n + 1))⁻¹ • z + (c (n + 1))⁻¹ • z := by
    intro n
    rw [← add_smul]
    congr 1
    simp only [hcdef, pow_succ]
    field_simp
    norm_num
  have hlim : Tendsto (fun n => c n • G ((c n)⁻¹ • z)) atTop (𝓝 (fderiv ℂ G 0 z)) := by
    have := hG.hasFDerivAt.lim z hcn
    simpa [h0] using this
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hz.eventually (hdbl.and hev))
  have hconst : ∀ n, N ≤ n → c n • G ((c n)⁻¹ • z) = c N • G ((c N)⁻¹ • z) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [← ih, hhalf n, (hN (n + 1) (by omega)).1, ← two_smul ℂ, smul_smul]
      simp only [hcdef, pow_succ]
  have hF : fderiv ℂ G 0 z = c N • G ((c N)⁻¹ • z) := by
    refine tendsto_nhds_unique hlim ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn using (hconst n hn).symm
  have hpow : ∀ (n : ℕ) (x : E') (y : E), ex x = a y → ex (c n • x) = a (c n • y) := by
    intro n x y h
    induction n with
    | zero => simpa [hcdef] using h
    | succ n ih =>
      have e : c (n + 1) = c n + c n := by simp only [hcdef, pow_succ]; ring
      rw [e, add_smul, add_smul, hex, ha, ih]
  rw [hF, hpow N _ _ (hN N le_rfl).2, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]

theorem exists_linear_lift :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∀ (n : ℕ) (a : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : (A).left.Opens) (f : Γ((A).left, U)), IsOpen {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 → ∃ G : (Fin n → ℂ) → (Fin g → ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, u.ex (G w) = a w) → ∀ f : A ⟶ A, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ f) := by
  intro hval A _ L g u hlift f hf
  have h0 : u.ex 0 = 1 := (u.ker 0).mpr u.Λ.zero_mem
  obtain ⟨G, hG0, hGa, hGe⟩ := hlift g (fun z => u.ex z ≫ f) (by
    intro U s
    have hset : {w | w ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (u.ex w ≫ f).left ⁻¹ᵁ U} =
        {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (f.left ⁻¹ᵁ U)} := by
      ext w
      simp
    have hfun : (fun w => valAt' (u.ex w ≫ f).left U s) =
        fun w => valAt' (u.ex w).left (f.left ⁻¹ᵁ U) ((f.left.app U).hom s) := by
      funext w
      exact ((hval A.left (u.ex w).left).2.2.2.1 A.left f.left U s).symm
    rw [hset, hfun]
    exact u.hol _ _) (by simp only [h0]; exact MonObj.one_comp f)
  refine ⟨(fderiv ℂ G 0).toLinearMap, fun z => ?_⟩
  exact fderiv_lifts u.ex u.ex_add u.Λ u.ker u.discrete (fun z => u.ex z ≫ f)
    (fun z w => by simp only [u.ex_add]; exact MonObj.mul_comp _ _ f) G hG0 hGa.differentiableAt hGe z

end GlobalTheory.EndoLinear
end
