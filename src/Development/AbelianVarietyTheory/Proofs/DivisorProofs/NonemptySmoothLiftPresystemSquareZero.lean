module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceCoreOfSumPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameGenericFibreChainRescaledDeeperRealisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLiftsOverSquareZeroThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftOfRetractSquareZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftFormallySmoothSquareZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftFormallySmoothSquareZero
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem idemLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B'] (e₀ : B₀' →ₐ[R₀] B₀'), (∀ x, e₀ (e₀ x) = e₀ x) → ∃ e : B' →ₐ[R] B', (∀ b, e (e b) = e b) ∧ ∀ b, p' (e b) = e₀ (p' b) := by
  intro R R₀ _ _ I hI π hπ hk B' B₀' _ _ _ _ p' hs' hp' hker' _ e₀ he₀
  obtain ⟨e, he⟩ := homLift R R₀ I hI π hπ hk B' B₀' p' hs' hp' hker' B' B₀' p' hs' hp' hker' e₀
  set J : Ideal B' := I.map (algebraMap R B') with hJ
  have hJ2 : ∀ x ∈ J, ∀ y ∈ J, x * y = 0 := by
    intro x hx y hy
    have : x * y ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hy
    rw [hJ, ← Ideal.map_pow, hI] at this
    simpa using this
  have hu : ∀ c, e (e c) - e c ∈ J := by
    intro c
    rw [← hker']
    simp [map_sub, he, he₀]
  have hkill : ∀ x ∈ J, ∀ c, e (e (c * x)) - e (c * x) = 0 := by
    intro x hx
    rw [hJ, Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      intro c
      have h1 : e (c * algebraMap R B' r) = e c * algebraMap R B' r := by
        rw [map_mul, AlgHom.commutes]
      have h2 : e (e c * algebraMap R B' r) = e (e c) * algebraMap R B' r := by
        rw [map_mul, AlgHom.commutes]
      rw [h1, h2, ← sub_mul]
      exact hJ2 _ (hu c) _ (Ideal.mem_map_of_mem _ hr)
    | zero => intro c; simp
    | add x y _ _ hx hy =>
      intro c
      have := hx c
      have := hy c
      rw [mul_add, map_add (f := _), map_add (f := _)]
      linear_combination hx c + hy c
    | smul a x _ hx =>
      intro c
      rw [smul_eq_mul, ← _root_.mul_assoc]
      exact hx (c * a)
  have hrec : ∀ c, e (e (e (e c))) - 2 * e (e (e c)) + e (e c) = 0 := by
    intro c
    have := hkill _ (hu c) 1
    simp only [_root_.one_mul, map_sub] at this
    linear_combination this
  let e' : B' →ₐ[R] B' :=
    { toFun := fun b => 3 * e (e b) - 2 * e (e (e b))
      map_one' := by simp; norm_num
      map_mul' := by
        intro x y
        have h := hJ2 _ (hu (e x)) _ (hu (e y))
        simp only [map_mul]
        linear_combination (-6 : B') * h
      map_zero' := by simp
      map_add' := by intro x y; simp only [map_add (f := _)]; ring
      commutes' := by intro r; simp only [AlgHom.commutes]; ring }
  refine ⟨e', ?_, ?_⟩
  · intro b
    show 3 * e (e (3 * e (e b) - 2 * e (e (e b)))) - 2 * e (e (e (3 * e (e b) - 2 * e (e (e b))))) = 3 * e (e b) - 2 * e (e (e b))
    simp only [map_sub, map_mul, map_ofNat]
    linear_combination (-3 : B') * hrec b + (-4 : B') * hrec (e b) + (4 : B') * hrec (e (e b))
  · intro b
    show p' (3 * e (e b) - 2 * e (e (e b))) = e₀ (p' b)
    simp only [map_sub, map_mul, map_ofNat, he, he₀]
    ring

end GlobalTheory.Obs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftFormallySmoothSquareZeroStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_lift_formallySmooth_squareZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B'] (e₀ : B₀' →ₐ[R₀] B₀'), (∀ x, e₀ (e₀ x) = e₀ x) → ∃ e : B' →ₐ[R] B', (∀ b, e (e b) = e b) ∧ ∀ b, p' (e b) = e₀ (p' b) := by
  first | exact @GlobalTheory.Obs.idemLift | exact GlobalTheory.Obs.idemLift | (intros; apply GlobalTheory.Obs.idemLift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRangeOfIdempotentAlgHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRangeOfIdempotentAlgHom
namespace GlobalTheory

theorem idempotent_algHom_ker_fg {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (e : A →ₐ[R] A) (he : ∀ x, e (e x) = e x) :
    (RingHom.ker e.rangeRestrict.toRingHom).FG := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)
  refine ⟨s.image (fun x => x - e x), ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨x, _, rfl⟩
    change e.rangeRestrict (x - e x) = 0
    apply Subtype.ext
    simp [he]
  · intro b hb
    have hb' : e b = 0 := by
      have := congrArg Subtype.val (show e.rangeRestrict b = 0 from hb)
      simpa using this
    have key : ∀ y : A, y - e y ∈ Ideal.span ((fun x => x - e x) '' (s : Set A)) := by
      intro y
      have hy : y ∈ Algebra.adjoin R (s : Set A) := by rw [hs]; exact Algebra.mem_top
      induction hy using Algebra.adjoin_induction with
      | mem x hx => exact Ideal.subset_span ⟨x, hx, rfl⟩
      | algebraMap r => simp
      | add x y _ _ hx hy =>
        have h : x + y - e (x + y) = (x - e x) + (y - e y) := by rw [map_add (f := _)]; ring
        rw [h]; exact Ideal.add_mem _ hx hy
      | mul x y _ _ hx hy =>
        have h : x * y - e (x * y) = x * (y - e y) + e y * (x - e x) := by rw [map_mul]; ring
        rw [h]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hx)
    simpa [hb'] using key b

theorem smooth_range_of_idempotent : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] (e : A →ₐ[R] A), (∀ x, e (e x) = e x) → Algebra.Smooth R e.range := by
  intro R A _ _ _ _ e he
  have hq : ∀ b : e.range, e.rangeRestrict (b : A) = b := by
    rintro ⟨_, a, rfl⟩
    apply Subtype.ext
    simp [he]
  have hsurj : Function.Surjective e.rangeRestrict := fun b => ⟨b, hq b⟩
  refine { formallySmooth := ?_, finitePresentation := ?_ }
  · refine Algebra.FormallySmooth.of_split e.rangeRestrict
      ((Ideal.Quotient.mkₐ R _).comp e.range.val) ?_
    ext b
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_id, id_eq,
      Subalgebra.coe_val]
    rw [AlgHom.kerSquareLift_mk, hq]
  · exact Algebra.FinitePresentation.of_surjective hsurj (idempotent_algHom_ker_fg e he)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothRangeOfIdempotentAlgHomStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_range_of_idempotent_algHom : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A] (e : A →ₐ[R] A), (∀ x, e (e x) = e x) → Algebra.Smooth R e.range := by
  first | exact @GlobalTheory.smooth_range_of_idempotent | exact GlobalTheory.smooth_range_of_idempotent | (intros; apply GlobalTheory.smooth_range_of_idempotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftOfRetractSquareZero
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Obs

theorem retractLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.Smooth R B'] (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀] (i : B₀ →ₐ[R₀] B₀') (r : B₀' →ₐ[R₀] B₀), (∀ x, r (i x) = x) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B' B₀' _ _ _ _ p' hs' hp' hker' _ B₀ _ _ i r hri
  obtain ⟨e, he, hpe⟩ := GlobalTheory.T.exists_idempotent_lift_formallySmooth_squareZero R R₀ I hI π hπ hk B' B₀' p' hs' hp' hker' (i.comp r) (fun x ↦ by simp [hri])
  have hmem : ∀ x ∈ I.map (algebraMap R B'), e.rangeRestrict x ∈ I.map (algebraMap R e.range) := by
    intro x hx
    have hle : I.map (algebraMap R B') ≤ (I.map (algebraMap R e.range)).comap (e.rangeRestrict : B' →+* e.range) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro y hy
      simp only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
      rw [AlgHom.commutes]
      exact Ideal.mem_map_of_mem _ hy
    exact hle hx
  refine ⟨e.range, inferInstance, inferInstance,
    ((r : B₀' →+* B₀).comp p').comp (e.range.val : e.range →+* B'), ?_, ?_, ?_, GlobalTheory.T.smooth_range_of_idempotent_algHom R B' e he⟩
  · intro c b
    show r (p' ((c • b : e.range) : B')) = π c • r (p' (b : B'))
    rw [Subalgebra.coe_smul, hs' c (b : B'), map_smul]
  · intro y
    obtain ⟨b, hb⟩ := hp' (i y)
    refine ⟨⟨e b, e.mem_range_self b⟩, ?_⟩
    show r (p' (e b)) = y
    rw [hpe, hb]
    simp [hri]
  · intro b
    constructor
    · intro h
      change r (p' (b : B')) = 0 at h
      obtain ⟨c, hc⟩ := b.2
      change e c = (b : B') at hc
      have hfix : e (b : B') = b := by rw [← hc, he]
      have h0 : p' (b : B') = 0 := by
        rw [← hfix, hpe]
        simp [h]
      have hb : e.rangeRestrict (b : B') = b := Subtype.ext hfix
      rw [← hb]
      exact hmem _ ((hker' _).mp h0)
    · intro h
      have hle : I.map (algebraMap R e.range) ≤ RingHom.ker (((r : B₀' →+* B₀).comp p').comp (e.range.val : e.range →+* B')) := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
        have hx0 : π x = 0 := by rw [← RingHom.mem_ker, hk]; exact hx
        show r (p' (algebraMap R B' x)) = 0
        rw [hs'.map_algebraMap, hx0, map_zero, map_zero]
      exact hle h

end GlobalTheory.Obs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftOfRetractSquareZeroStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothLift_of_retract_squareZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.Smooth R B'] (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀] (i : B₀ →ₐ[R₀] B₀') (r : B₀' →ₐ[R₀] B₀), (∀ x, r (i x) = x) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  first | exact @GlobalTheory.Obs.retractLift | exact GlobalTheory.Obs.retractLift | (intros; apply GlobalTheory.Obs.retractLift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardSmoothRetractOfSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPresentationRelationsCombinationNormal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPresentationRelationsCombinationNormal
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothRel

theorem derivation_mem_of_mem_sq {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (I : Ideal A) {x : A} (hx : x ∈ I ^ 2) : D x ∈ I := by
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun y hy z hz => ?_) (fun y z hy hz => ?_)
  · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact I.add_mem (I.mul_mem_right _ hy) (I.mul_mem_right _ hz)
  · rw [map_add (f := _)]; exact I.add_mem hy hz

theorem taylor_rem_mem {R σ : Type} [CommRing R] [Fintype σ] (I : Ideal (MvPolynomial σ R))
    (u : σ → MvPolynomial σ R) (hu : ∀ i, u i ∈ I) (h : MvPolynomial σ R) :
    MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + u i) h - h
      - ∑ i, MvPolynomial.pderiv i h * u i ∈ I ^ 2 := by
  classical
  induction h using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have := Ideal.add_mem _ hp hq
    convert this using 1
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]; ring
  | mul_X p s hp =>
    have hD : ∑ i, MvPolynomial.pderiv i p * u i ∈ I :=
      Ideal.sum_mem _ fun i _ ↦ I.mul_mem_left _ (hu i)
    have h2 : (∑ i, MvPolynomial.pderiv i p * u i) * u s ∈ I ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hD (hu s)
    have h3 := Ideal.add_mem _ h2 ((I ^ 2).mul_mem_left (MvPolynomial.X s + u s) hp)
    have hs : ∑ i, MvPolynomial.pderiv i (p * MvPolynomial.X s) * u i
        = p * u s + MvPolynomial.X s * ∑ i, MvPolynomial.pderiv i p * u i := by
      simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · simp [Pi.single_apply]
      · exact Finset.sum_congr rfl fun i _ => by ring
    convert h3 using 1
    rw [map_mul, MvPolynomial.aeval_X, hs]; ring

theorem relations_combination :
    ∀ (R₀ : Type) [CommRing R₀] (n r : ℕ) (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) (b : Fin r → Fin r → Fin r → MvPolynomial (Fin n) R₀), (∀ j, MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l)) → (∀ j, g j + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * g k ∈ Ideal.span (Set.range g) ^ 2) ∧ ∀ j m, MvPolynomial.pderiv m (g j) + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * MvPolynomial.pderiv m (g k) ∈ Ideal.span (Set.range g) := by
  intro R₀ _ n r g a b hrel
  set J : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span (Set.range g) with hJ
  have hg : ∀ k, g k ∈ J := fun k => Ideal.subset_span ⟨k, rfl⟩
  have hu : ∀ i, (∑ k, a i k * g k) ∈ J := fun i =>
    Ideal.sum_mem _ fun k _ => J.mul_mem_left _ (hg k)
  have h1 : ∀ j, g j + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * g k ∈ J ^ 2 := by
    intro j
    have hT := taylor_rem_mem J (fun i => ∑ k, a i k * g k) hu (g j)
    have hA : MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + ∑ k, a i k * g k) (g j) ∈ J ^ 2 := by
      rw [hrel j]
      exact Ideal.sum_mem _ fun k _ => Ideal.sum_mem _ fun l _ =>
        (J ^ 2).mul_mem_left _ (by rw [pow_two]; exact Ideal.mul_mem_mul (hg k) (hg l))
    have := Ideal.sub_mem _ hA hT
    convert this using 1
    ring
  refine ⟨h1, fun j m => ?_⟩
  have hF := derivation_mem_of_mem_sq (MvPolynomial.pderiv m) J (h1 j)
  have hg0 : ∀ k, Ideal.Quotient.mk J (g k) = 0 := fun k =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hg k)
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hF ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [Derivation.leibniz, map_sum, map_add (f := _), map_mul, hg0, smul_eq_mul, mul_add,
    Finset.sum_add_distrib] using hF

end GlobalTheory.SmoothRel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPresentationRelationsCombinationNormalStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothPresentation_relations_combination_normal : ∀ (R₀ : Type) [CommRing R₀] (n r : ℕ) (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) (b : Fin r → Fin r → Fin r → MvPolynomial (Fin n) R₀), (∀ j, MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l)) → (∀ j, g j + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * g k ∈ Ideal.span (Set.range g) ^ 2) ∧ ∀ j m, MvPolynomial.pderiv m (g j) + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * MvPolynomial.pderiv m (g k) ∈ Ideal.span (Set.range g) := by
  first | exact @GlobalTheory.SmoothRel.relations_combination | exact GlobalTheory.SmoothRel.relations_combination | (intros; apply GlobalTheory.SmoothRel.relations_combination <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardSmoothRetractOfSmooth
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SmoothRetract

open MvPolynomial

variable {R₀ : Type} [CommRing R₀] {n r : ℕ}

def tang (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀)
    (i l : Fin n) : MvPolynomial (Fin n) R₀ :=
  (if i = l then 1 else 0) + ∑ k, a i k * pderiv l (g k)

def rel (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀)
    (i : Fin n) : MvPolynomial (Fin n ⊕ Fin n) R₀ :=
  rename Sum.inr (∑ k, a i k * g k) +
    ∑ l, rename Sum.inr (tang g a i l) * (X (Sum.inl l) - X (Sum.inr l))

theorem aeval_pderiv_rel (g : Fin r → MvPolynomial (Fin n) R₀)
    (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) {B : Type} [CommRing B] [Algebra R₀ B]
    (xb : Fin n → B) (hg : ∀ k, aeval xb (g k) = 0) (i j : Fin n) :
    aeval (Sum.elim xb xb) (pderiv (Sum.inr i) (rel g a j)) = -(if i = j then 1 else 0) := by
  classical
  simp [rel, Derivation.leibniz, pderiv_rename Sum.inr_injective, pderiv_X, Pi.single_apply,
    aeval_rename, Function.comp_def, hg, tang, Finset.sum_add_distrib, mul_add, add_mul]
  exact if_congr eq_comm rfl rfl

theorem sum_pderiv_mul_tang (g : Fin r → MvPolynomial (Fin n) R₀)
    (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) (j : Fin r) (l : Fin n) :
    ∑ i, pderiv i (g j) * tang g a i l =
      pderiv l (g j) + ∑ i, pderiv i (g j) * ∑ k, a i k * pderiv l (g k) := by
  classical
  simp [tang, mul_add, Finset.sum_add_distrib]

theorem core (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀)
    (h1 : ∀ j, g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k ∈ Ideal.span (Set.range g) ^ 2)
    (h2 : ∀ j m, pderiv m (g j) + ∑ i, pderiv i (g j) * ∑ k, a i k * pderiv m (g k) ∈
      Ideal.span (Set.range g)) :
    ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra R₀ C₀)
      (i : (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) →ₐ[R₀] C₀)
      (r : C₀ →ₐ[R₀] (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g))),
      Algebra.IsStandardSmooth R₀ C₀ ∧ ∀ x, r (i x) = x := by
  classical
  set J : Ideal (MvPolynomial (Fin n) R₀) := Ideal.span (Set.range g) with hJ
  set K : Ideal (MvPolynomial (Fin n ⊕ Fin n) R₀) := Ideal.span (Set.range (rel g a)) with hK
  let xb : Fin n → MvPolynomial (Fin n) R₀ ⧸ J := fun l => Ideal.Quotient.mk J (X l)
  have hxb : ∀ p, aeval xb p = Ideal.Quotient.mk J p := fun p =>
    AlgHom.congr_fun (MvPolynomial.algHom_ext (f := aeval xb) (g := Ideal.Quotient.mkₐ R₀ J)
      fun l => by simp [xb]) p
  have hg0 : ∀ k, Ideal.Quotient.mk J (g k) = 0 := fun k =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨k, rfl⟩)
  let r₀' : MvPolynomial (Fin n ⊕ Fin n) R₀ →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    aeval (Sum.elim xb xb)
  have hren : ∀ p, r₀' (rename Sum.inr p) = Ideal.Quotient.mk J p := fun p => by
    simp [r₀', aeval_rename, Function.comp_def, ← hxb]
  have hs0 : ∀ l, r₀' (X (Sum.inl l) - X (Sum.inr l)) = 0 := fun l => by simp [r₀']
  have hrel : ∀ i, r₀' (rel g a i) = 0 := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rel, map_add (f := _), map_sum, map_mul, hren, hs0, mul_zero, Finset.sum_const_zero,
      add_zero, hg0]
  have hKle : K ≤ RingHom.ker r₀' := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hrel i)
  let r₀ : (MvPolynomial (Fin n ⊕ Fin n) R₀ ⧸ K) →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    Ideal.Quotient.liftₐ K r₀' (fun x hx => hKle hx)
  have hr₀ : ∀ p, r₀ (Ideal.Quotient.mk K p) = r₀' p := fun p => rfl
  let P := Algebra.PreSubmersivePresentation.naive (v := rel g a) Sum.inr Sum.inr_injective
  have hval : ∀ v, P.val v = Ideal.Quotient.mk K (X v) := fun v => by
    simp [P]
    rfl
  have hr₀alg : ∀ p, r₀ (algebraMap P.Ring _ p) = r₀' p := by
    intro p
    rw [Algebra.Generators.algebraMap_apply]
    have : r₀.comp (aeval P.val) = r₀' :=
      MvPolynomial.algHom_ext fun v => by simp [hval, hr₀]
    exact AlgHom.congr_fun this p
  have hjac : IsUnit (r₀ P.jacobian) := by
    rw [P.jacobian_eq_jacobiMatrix_det, hr₀alg]
    have hM : r₀'.toRingHom.mapMatrix P.jacobiMatrix = -1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply,
        Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
      change aeval (Sum.elim xb xb) _ = _
      rw [aeval_pderiv_rel g a xb (fun k => by rw [hxb, hg0])]
      simp [Matrix.one_apply]
    have : r₀' P.jacobiMatrix.det = (r₀'.toRingHom.mapMatrix P.jacobiMatrix).det :=
      RingHom.map_det _ _
    rw [this, hM, Matrix.det_neg, Matrix.det_one, _root_.mul_one]
    exact (isUnit_one.neg).pow _
  let D := MvPolynomial (Fin n ⊕ Fin n) R₀ ⧸ K
  let T1 := Localization.Away P.jacobian
  haveI hT1 : Algebra.IsStandardSmooth R₀ T1 := by
    let Q := Algebra.SubmersivePresentation.localizationAway T1 P.jacobian
    let P' : Algebra.SubmersivePresentation R₀ T1 (Unit ⊕ (Fin n ⊕ Fin n)) (Unit ⊕ Fin n) :=
      { __ := Q.toPreSubmersivePresentation.comp P
        jacobian_isUnit := by
          rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
            Algebra.smul_def]
          exact (IsLocalization.Away.algebraMap_isUnit _).mul Q.jacobian_isUnit }
    exact P'.isStandardSmooth
  let r₁ : T1 →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    IsLocalization.Away.liftAlgHom P.jacobian (f := r₀) hjac
  have hr₁ : ∀ y, r₁ (algebraMap D T1 y) = r₀ y := fun y => by
    rw [IsLocalization.Away.liftAlgHom_apply]
    exact IsLocalization.Away.lift_eq _ _ _

  let φ : MvPolynomial (Fin n) R₀ →+* D :=
    (Ideal.Quotient.mk K).comp (rename Sum.inr : _ →ₐ[R₀] MvPolynomial (Fin n ⊕ Fin n) R₀).toRingHom
  have hφ : ∀ p, φ p = Ideal.Quotient.mk K (rename Sum.inr p) := fun p => rfl
  let G : Fin r → D := fun k => φ (g k)
  let s : Fin n → D := fun l => Ideal.Quotient.mk K (X (Sum.inl l) - X (Sum.inr l))
  let JD : Ideal D := Ideal.span (Set.range G)
  let L : Ideal D := JD ⊔ Ideal.span (Set.range s)
  have hJD : J.map φ = JD := by
    simp only [hJ, Ideal.map_span, JD, G, ← Set.range_comp]
    rfl
  have hrelD : ∀ i, φ (∑ k, a i k * g k) + ∑ l, φ (tang g a i l) * s l = 0 := by
    intro i
    have : Ideal.Quotient.mk K (rel g a i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
    rw [← this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rel, map_add (f := _), map_sum, map_mul, hφ, s]
  have key : ∀ j, G j ∈ L * JD := by
    intro j
    have e1 : φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) =
        G j + ∑ i, φ (pderiv i (g j)) * φ (∑ k, a i k * g k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum]
      simp only [map_mul, G]
    have hs : ∑ i, φ (pderiv i (g j)) * φ (∑ k, a i k * g k) +
        ∑ i, φ (pderiv i (g j)) * ∑ l, φ (tang g a i l) * s l = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun i _ => by rw [← mul_add, hrelD i, mul_zero]
    have e3 : ∑ l, s l * φ (∑ i, pderiv i (g j) * tang g a i l) =
        ∑ i, φ (pderiv i (g j)) * ∑ l, φ (tang g a i l) * s l := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have eq : G j = φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) +
        ∑ l, s l * φ (∑ i, pderiv i (g j) * tang g a i l) := by
      rw [e3]
      linear_combination -e1 - hs
    rw [eq]
    refine Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun l _ => ?_)
    · have : φ (g j + ∑ i, pderiv i (g j) * ∑ k, a i k * g k) ∈ JD ^ 2 := by
        rw [← hJD, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem φ (h1 j)
      rw [pow_two] at this
      exact Ideal.mul_mono_left le_sup_left this
    · refine Ideal.mul_mem_mul (Ideal.mem_sup_right (Ideal.subset_span ⟨l, rfl⟩)) ?_
      rw [sum_pderiv_mul_tang, ← hJD]
      exact Ideal.mem_map_of_mem φ (h2 j l)
  obtain ⟨e, he1, he⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul L JD
    (Submodule.fg_span (Set.finite_range G)) (by
      rw [Ideal.smul_eq_mul]
      exact Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact key j))
  have hL : L ≤ RingHom.ker r₀ := by
    refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨k, rfl⟩
      change r₀ (Ideal.Quotient.mk K (rename Sum.inr (g k))) = 0
      rw [hr₀, hren, hg0]
    · rintro _ ⟨l, rfl⟩
      change r₀ (Ideal.Quotient.mk K _) = 0
      rw [hr₀, hs0]
  have hre : r₀ e = 1 := by
    have := hL he1
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
    exact this
  let C₀ := Localization.Away (algebraMap D T1 e)
  haveI : Algebra.IsStandardSmooth T1 C₀ :=
    Algebra.IsStandardSmooth.localization_away (algebraMap D T1 e)
  have hC : Algebra.IsStandardSmooth R₀ C₀ := Algebra.IsStandardSmooth.trans R₀ T1 C₀
  let r₂ : C₀ →ₐ[R₀] MvPolynomial (Fin n) R₀ ⧸ J :=
    IsLocalization.Away.liftAlgHom (algebraMap D T1 e) (f := r₁) (by rw [hr₁, hre]; exact isUnit_one)
  have hr₂ : ∀ y, r₂ (algebraMap T1 C₀ y) = r₁ y := fun y => by
    rw [IsLocalization.Away.liftAlgHom_apply]
    exact IsLocalization.Away.lift_eq _ _ _
  let ψ : D →ₐ[R₀] C₀ := (IsScalarTower.toAlgHom R₀ T1 C₀).comp (IsScalarTower.toAlgHom R₀ D T1)
  have hψe : IsUnit (ψ e) := IsLocalization.Away.algebraMap_isUnit (algebraMap D T1 e)
  have hψG : ∀ k, ψ (G k) = 0 := by
    intro k
    have h0 : e * G k = 0 := he (G k) (Ideal.subset_span ⟨k, rfl⟩)
    have : ψ e * ψ (G k) = 0 := by rw [← map_mul, h0, map_zero]
    exact (hψe.mul_right_eq_zero).1 this
  have hJle : J ≤ RingHom.ker (ψ.comp ((Ideal.Quotient.mkₐ R₀ K).comp
      (rename Sum.inr : _ →ₐ[R₀] MvPolynomial (Fin n ⊕ Fin n) R₀))) :=
    Ideal.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hψG k)
  let i : (MvPolynomial (Fin n) R₀ ⧸ J) →ₐ[R₀] C₀ :=
    Ideal.Quotient.liftₐ J _ (fun x hx => hJle hx)
  refine ⟨C₀, inferInstance, inferInstance, i, r₂, hC, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change r₂ (algebraMap T1 C₀ (algebraMap D T1 (Ideal.Quotient.mk K (rename Sum.inr p)))) = _
  rw [hr₂, hr₁, hr₀, hren]

theorem exists_retract_isStandardSmooth : ∀ (R₀ B₀ : Type) [CommRing R₀] [CommRing B₀] [Algebra R₀ B₀],
    Algebra.Smooth R₀ B₀ → ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra R₀ C₀) (i : B₀ →ₐ[R₀] C₀)
      (r : C₀ →ₐ[R₀] B₀), Algebra.IsStandardSmooth R₀ C₀ ∧ ∀ x, r (i x) = x := by
  intro R₀ B₀ _ _ _ hsm
  obtain ⟨n, f, hf, hfg⟩ := Algebra.FinitePresentation.out (R := R₀) (A := B₀)
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  let e : (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) ≃ₐ[R₀] B₀ :=
    (Ideal.quotientEquivAlgOfEq R₀ hg).trans (Ideal.quotientKerAlgEquivOfSurjective hf)
  haveI : Algebra.FormallySmooth R₀ (MvPolynomial (Fin n) R₀ ⧸ Ideal.span (Set.range g)) :=
    Algebra.FormallySmooth.of_equiv e.symm
  obtain ⟨a, b, hab⟩ :=
    GlobalTheory.exists_witnesses_of_formallySmooth_quotient (Fin n) R₀ r g inferInstance
  obtain ⟨h1, h2⟩ := GlobalTheory.T.smoothPresentation_relations_combination_normal R₀ n r g a b hab
  obtain ⟨C₀, i1, i2, i, ρ, hstd, hret⟩ := core g a h1 h2
  exact ⟨C₀, i1, i2, i.comp e.symm.toAlgHom, e.toAlgHom.comp ρ, hstd, fun x => by simp [hret]⟩

end GlobalTheory.SmoothRetract
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardSmoothRetractOfSmoothStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardSmooth_retract_of_smooth : ∀ (R₀ B₀ : Type) [CommRing R₀] [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (C₀ : Type) (_ : CommRing C₀) (_ : Algebra R₀ C₀) (i : B₀ →ₐ[R₀] C₀) (r : C₀ →ₐ[R₀] B₀), Algebra.IsStandardSmooth R₀ C₀ ∧ ∀ x, r (i x) = x := by
  first | exact @GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth | exact GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth | (intros; apply GlobalTheory.SmoothRetract.exists_retract_isStandardSmooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLiftsOverSquareZeroThickening
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem smooth_lifts_over_sqZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B₀ _ _ hsm
  obtain ⟨C₀, _, _, i, r, hstd, hri⟩ := GlobalTheory.T.exists_standardSmooth_retract_of_smooth R₀ B₀ hsm
  obtain ⟨C, _, _, p', hs', hp', hker', hC⟩ := GlobalTheory.T.standardSmooth_lift_over_sqZero_thickening R R₀ I hI π hπ hk C₀ hstd
  exact GlobalTheory.T.exists_smoothLift_of_retract_squareZero R R₀ I hI π hπ hk C C₀ p' hs' hp' hker' B₀ i r hri

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLiftsOverSquareZeroThickeningStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAlgebra_lifts_over_square_zero_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  first | exact @GlobalTheory.smooth_lifts_over_sqZero | exact GlobalTheory.smooth_lifts_over_sqZero | (intros; apply GlobalTheory.smooth_lifts_over_sqZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftPresystemSquareZero
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem pre_nonempty : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀), (∀ T, Algebra.Smooth R₀ (F.obj T)) → Nonempty (Pre I π F) := by
  intro R R₀ _ _ I hI π hπ hk C _ F hF
  have h := fun T => GlobalTheory.T.smoothAlgebra_lifts_over_square_zero_thickening R R₀ I hI π hπ hk (F.obj T) (hF T)
  choose B iB aB p hs hp hker hsm using h
  letI := iB
  letI := aB
  have hl : ∀ {T T' : C} (a : T ⟶ T'), ∃ ρ : B T →ₐ[R] B T', ∀ b, p T' (ρ b) = mp F a (p T b) :=
    fun {T T'} a => homLift R R₀ I hI π hπ hk (B T) (F.obj T) (p T) (hs T) (hp T) (hker T)
      (B T') (F.obj T') (p T') (hs T') (hp T') (hker T') (mp F a)
  exact ⟨{ B := fun T => CommAlgCat.of R (B T)
           p := p
           semi := hs
           surj := hp
           ker := hker
           smooth := hsm
           ρ := fun a => (hl a).choose
           nat := fun a b => (hl a).choose_spec b }⟩

end GlobalTheory.Obs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftPresystemSquareZeroStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_smoothLiftPresystem_squareZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀), (∀ T, Algebra.Smooth R₀ (F.obj T)) → Nonempty (Pre I π F) := by
  first | exact @GlobalTheory.Obs.pre_nonempty | exact GlobalTheory.Obs.pre_nonempty | (intros; apply GlobalTheory.Obs.pre_nonempty <;> assumption)
end
