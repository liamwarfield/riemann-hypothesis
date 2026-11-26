module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedPowOfUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpanRhoCharLeCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpanRhoCharLeCocycles
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

namespace GlobalTheory.Cut.Coc

theorem KOG_torsion {O : Type} [CommRing O] [IsDomain O] {k : ℕ} (t : KOG O k) :
    ∃ d : O, d ≠ 0 ∧ d • t = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) v
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  choose u hu using hb
  exact ⟨u, funext fun j => hu j⟩

theorem smul_cont {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O)) {k : ℕ} (t : KOG O k) :
    Continuous fun a : O => a • t := by
  obtain ⟨d, hd, hdt⟩ := KOG_torsion t
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  have hopen : IsOpen ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.mp hO).1 n
  have hk : ∀ a ∈ (IsLocalRing.maximalIdeal O ^ n : Ideal O), a • t = 0 := by
    intro a ha
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    have : c * ϖ ^ n = (c * ((u⁻¹ : Oˣ) : O)) * (u * ϖ ^ n) := by
      rw [mul_assoc, Units.inv_mul_cancel_left]
    rw [this, mul_smul, hdt, smul_zero]
  refine continuous_of_continuousAt_zero (LinearMap.toSpanSingleton O (KOG O k) t) ?_
  refine (continuousAt_const (y := (0 : KOG O k))).congr ?_
  filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with a ha
  exact (hk a ha).symm

theorem lin_cont {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O)) {k n : ℕ} {X : Type} [Fintype X]
    [DecidableEq X] (φ : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] KOG O k) : Continuous φ := by
  have h : ∀ y : X → Matrix (Fin n) (Fin n) O,
      φ y = ∑ x, ∑ p, ∑ q, y x p q • φ (Pi.single x (Matrix.single p q 1)) := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum]
    apply congrArg φ
    funext x
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single x]
    · simp only [Pi.smul_apply, Pi.single_eq_same, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single (y x)
    · intro b _ hb
      simp [Pi.smul_apply, Pi.single_eq_of_ne hb.symm]
    · simp
  rw [show (φ : _ → _) = _ from funext h]
  refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun p _ =>
    continuous_finsetSum _ fun q _ => ?_
  exact (smul_cont hO _).comp (by fun_prop : Continuous fun y : X → Matrix (Fin n) (Fin n) O => y x p q)

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (S : IdempotentChoiceData D.nd i)

def tw (g : GE D.nd) : S.X' → MatN D.nd i :=
  fun x' => (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • rO D.nd i r (S.p x') g

theorem tw_mem (g : GE D.nd) : InR' D.nd r S (tw i r S g) := by
  refine ⟨1, fun _ _ => (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i), fun _ => g,
    fun _ => S.T'.algebraMap_mem _, ?_⟩
  rw [Fin.sum_univ_one]
  rfl

theorem yg_mem (g : GE D.nd) : InY D.nd r S (yg D.nd r S g) := by
  refine ⟨1, fun _ => tw i r S 1, fun _ => g, fun _ => tw_mem i r S 1, ?_⟩
  rw [Fin.sum_univ_one]
  funext x'
  simp [tw]

theorem yg_mul (g h : GE D.nd) :
    yg D.nd r S (g * h) = yg D.nd r S g + tw i r S g * yg D.nd r S h := by
  funext x'
  simp only [yg, tw, Pi.add_apply, Pi.mul_apply, map_mul, mul_inv, Units.val_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, mul_smul, mul_assoc]
  rw [smul_comm]
  abel

theorem yg_cont (hr : GoodR D.nd i r) : Continuous fun g => yg D.nd r S g := by
  refine continuous_pi fun x' => ?_
  have hc : Continuous fun g => rO D.nd i r (S.p x') g := (hr (S.p x')).1
  have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
    (D.nd.chi_cont i 1).comp continuous_inv
  refine ((h1.smul (hc.mul (continuous_const (y := Eel D.nd S x')))).sub
    (continuous_const (y := Eel D.nd S x'))).congr fun g => ?_
  simp [yg]

theorem cocW_le (hr : GoodR D.nd i r) (Xs : Set (D.nd.X i)) {k : ℕ}
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hψ : ∀ g, ψ (tw i r S g) = M g) :
    cocW i r S Xs ψ ≤ Z1 (WKG M) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨φ, hφ, -, rfl⟩
  refine ⟨(lin_cont (D.nd.O_adic i) φ).comp (yg_cont i r S hr), fun g h => ?_⟩
  show φ _ = φ _ + WKG M g (φ _)
  rw [yg_mul, map_add (f := _), hφ _ (tw_mem i r S g) _ (yg_mem i r S h), hψ]
  rfl

theorem blocks (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hS : GoodCongruenceObjects D.nd r ρ π S) (g : GE D.nd) :
    S.ψρ (tw i r S g) = WpO D.nd i ρ π g ∧
    ∀ c : Fin D.R.t, S.ψχ c (tw i r S g) =
      (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have key : ∀ w : (Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i),
      (((S.ψρ (tw i r S g)).map (toK D.nd i)).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i (S.ψχ c (tw i r S g)) * w.2 c) =
      toK D.nd i (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * w.2 c) := by
    intro w
    obtain ⟨u, rfl⟩ := S.e.surjective w
    rw [← h2 _ (tw_mem i r S g) u, ← h1 g u, ← map_smul, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [tw, hp, mapM]
  have hinj : Function.Injective (toK D.nd i) := IsFractionRing.injective _ _
  constructor
  · ext p q
    apply hinj
    have := congrFun (congrArg Prod.fst (key (Pi.single q 1, 0))) p
    simpa [mapM, WpO, twistM] using this
  · intro c
    apply hinj
    have := congrFun (congrArg Prod.snd (key (0, 1))) c
    simpa using this

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  intro D i r ρ π Xs S hr hS _
  refine ⟨cocW_le i r S hr Xs _ _ fun g => (blocks i r S ρ π hS g).1, fun c =>
    cocW_le i r S hr Xs _ _ fun g => ?_⟩
  rw [(blocks i r S ρ π hS g).2 c, mul_comm]
  rfl

end GlobalTheory.Cut.Coc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpanRhoCharLeCocyclesStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  first | exact @GlobalTheory.Cut.Coc.main | exact GlobalTheory.Cut.Coc.main | (intros; apply GlobalTheory.Cut.Coc.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedPeriodAinfUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltGaloisActionRootOfUnityCoprime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltGaloisActionRootOfUnityCoprime
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem σC_root_of_unity {m n : ℕ} {g : GQ l} (hm : 0 < m) (hg : ∀ x : Om l, x ^ m = 1 → g x = x ^ n)
    {x : ℂ_[l]} (hx : x ^ m = 1) : Per.σC g x = x ^ n := by
  have : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  have hζ' := hζ.map_of_injective (algebraMap (Om l) ℂ_[l]).injective
  obtain ⟨i, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hx
  have h1 : (ζ ^ i) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (ζ ^ i)) = algebraMap (Om l) ℂ_[l] (g (ζ ^ i)) :=
    GlobalTheory.RingBasics.σC_coe g (ζ ^ i)
  rw [← map_pow, h2, hg _ h1, map_pow]

theorem tilt_root_eq_one {c : Per.Fl l} {m : ℕ} (hlm : ¬ l ∣ m) (hc : c ^ m = 1)
    (h0 : PreTilt.coeff 0 c = 1) : c = 1 := by
  have : IsDomain (Per.Fl l) := inferInstance
  by_contra hne
  have h1 : (∑ i ∈ Finset.range m, c ^ i) * (c - 1) = 0 := by rw [geom_sum_mul, hc, sub_self]
  have h2 : (∑ i ∈ Finset.range m, c ^ i) = 0 :=
    (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hne)
  have h3 := congrArg (PreTilt.coeff (O := Per.OC l) (p := l) 0) h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_pow, h0, one_pow, Finset.sum_const, Finset.card_range, map_zero,
    nsmul_eq_mul, mul_one] at h3
  exact hlm ((CharP.cast_eq_zero_iff _ l m).1 h3)

theorem tilt_root_inj {a b : Per.Fl l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (ha : a ^ m = 1)
    (hb : b ^ m = 1) (h : a.untilt = b.untilt) : a = b := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hb' : b * b ^ k = 1 := by rw [← pow_succ', hb]
  have h0 : PreTilt.coeff 0 a = PreTilt.coeff 0 b := by
    rw [← PreTilt.mk_untilt_eq_coeff_zero, ← PreTilt.mk_untilt_eq_coeff_zero, h]
  have h1 : a * b ^ k = 1 := by
    refine tilt_root_eq_one hlm ?_ ?_
    · rw [mul_pow, ha, ← pow_mul, mul_comm k, pow_mul, hb, one_pow, one_mul]
    · rw [map_mul, h0, ← map_mul, hb', map_one]
  calc a = a * (b * b ^ k) := by rw [hb', mul_one]
    _ = (a * b ^ k) * b := by ring
    _ = b := by rw [h1, one_mul]

theorem σF_root_of_unity (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (m n : ℕ) (g : GQ l) (hm : 0 < m)
    (hlm : ¬ l ∣ m) (he : e ^ m = 1) (hg : ∀ x : Om l, x ^ m = 1 → g x = x ^ n) :
    Per.σF g e = e ^ n := by
  refine tilt_root_inj hm hlm ?_ ?_ ?_
  · rw [← map_pow, he, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, he, one_pow]
  · rw [GlobalTheory.RingBasics.untilt_σF, map_pow]
    have h1 : e.untilt ^ m = 1 := by rw [← map_pow, he, map_one]
    have h2 : ((e.untilt : Per.OC l) : ℂ_[l]) ^ m = 1 := by
      simpa using congrArg Subtype.val h1
    exact Subtype.ext ((GlobalTheory.RingIface.sigO_coe l g _).trans
      ((σC_root_of_unity hm hg h2).trans (by simp)))

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltGaloisActionRootOfUnityCoprimeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_galois_action_root_of_unity_coprime : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (m n : ℕ) (g : GQ l), 0 < m → ¬ l ∣ m → e ^ m = 1 → (∀ x : Om l, x ^ m = 1 → g x = x ^ n) → Per.σF g e = e ^ n := by
  first | exact @GlobalTheory.MemLoc.σF_root_of_unity | exact GlobalTheory.MemLoc.σF_root_of_unity | (intros; apply GlobalTheory.MemLoc.σF_root_of_unity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedPeriodAinfUnit
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_pow_eq_one_algClosure_coprime (l : ℕ) [Fact l.Prime] (a : AlgebraicClosure (ZMod l))
    (ha : a ≠ 0) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ a ^ m = 1 := by
  have hint : IsIntegral (ZMod l) a := Algebra.IsIntegral.isIntegral a
  let K := IntermediateField.adjoin (ZMod l) ({a} : Set (AlgebraicClosure (ZMod l)))
  haveI : FiniteDimensional (ZMod l) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod l)
  letI : Fintype K := Fintype.ofFinite K
  let b : K := ⟨a, IntermediateField.mem_adjoin_simple_self _ a⟩
  have hb : b ≠ 0 := fun h => ha (congrArg Subtype.val h)
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  refine ⟨Fintype.card K - 1, by omega, ?_, ?_⟩
  · intro hd
    have h0 : ((Fintype.card K - 1 : ℕ) : K) = 0 := by
      obtain ⟨c, hc⟩ := hd
      have hl : ((l : ℕ) : K) = 0 := by
        rw [← map_natCast (algebraMap (ZMod l) K), ZMod.natCast_self, map_zero]
      rw [hc, Nat.cast_mul, hl, zero_mul]
    rw [Nat.cast_sub h1.le, FiniteField.cast_card_eq_zero] at h0
    simp at h0
  · have := congrArg Subtype.val (FiniteField.pow_card_sub_one_eq_one b hb)
    simpa [b] using this

theorem exists_unit_frobenius_eq_mul (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [IsAlgClosed k]
    (u : WittVector l k) (hu : IsUnit u) :
    ∃ w : WittVector l k, IsUnit w ∧ WittVector.frobenius w = u * w := by
  have h1 : (1 : WittVector l k).coeff 0 ≠ 0 := by simp
  have h2 : u.coeff 0 ≠ 0 := (hu.map (WittVector.constantCoeff (p := l) (R := k))).ne_zero
  refine ⟨WittVector.frobeniusRotation l h1 h2, ?_, ?_⟩
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    simpa [WittVector.frobeniusRotation, WittVector.frobeniusRotationCoeff] using
      WittVector.RecursionBase.solution_nonzero l h1 h2
  · have := WittVector.frobenius_frobeniusRotation l h1 h2
    rwa [mul_one, mul_comm] at this

private theorem padicInt_ringHom_ext (l : ℕ) [Fact l.Prime] {R : Type*} [CommRing R]
    [IsHausdorff (Ideal.span {(l : R)}) R] (f g : ℤ_[l] →+* R) : f = g := by
  refine RingHom.ext fun x => ?_
  refine sub_eq_zero.1 (IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(l : R)}) R) _ fun n => ?_)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
  have hx : x = c * (l : ℤ_[l]) ^ n + (x.appr n : ℤ_[l]) := by rw [hc]; ring
  have h : f x - g x = (f c - g c) * (l : R) ^ n := by
    rw [hx]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, h]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_unramified_period : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l), (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) → ∀ u : ℤ_[l]ˣ, ∃ w : Per.Ainf l, IsUnit w ∧ (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σA g w = w) ∧ Per.σA F w = Per.zA l u * w ∧ Per.φA l w = Per.zA l u * w := by
  intro l _ F hF u
  obtain ⟨f⟩ := GlobalTheory.T.nonempty_closure_hom_tilt_field l
  let u' : WittVector l (AlgebraicClosure (ZMod l)) :=
    WittVector.map (ZMod.castHom (dvd_refl l) _) (WittVector.fromPadicInt l u)
  have hu' : IsUnit u' := (u.isUnit.map _).map _
  obtain ⟨w₀, hw₀, hφ⟩ := exists_unit_frobenius_eq_mul l _ u' hu'
  have hfu : WittVector.map f u' = Per.zA l u := by
    exact RingHom.congr_fun (padicInt_ringHom_ext l (R := Per.Ainf l)
      ((WittVector.map f).comp ((WittVector.map (ZMod.castHom (dvd_refl l) _)).comp
        (WittVector.fromPadicInt l))) (Per.zA l)) u
  have hact : ∀ (g : GQ l) (n : ℕ), n ≠ 0 →
      (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → g x = x ^ n) →
      ∀ a, Per.σF g (f a) = f a ^ n := by
    intro g n hn hg a
    by_cases ha : a = 0
    · rw [ha, map_zero, map_zero, zero_pow hn]
    · obtain ⟨m, hm, hl, ham⟩ := exists_pow_eq_one_algClosure_coprime l a ha
      exact GlobalTheory.T.tilt_galois_action_root_of_unity_coprime l (f a) m n g hm hl (by rw [← map_pow, ham, map_one])
        fun x hx => hg x m hm hl hx
  have hφA : Per.φA l (WittVector.map f w₀) = Per.zA l u * WittVector.map f w₀ := by
    rw [← hfu, ← map_mul, ← hφ]
    refine WittVector.ext fun n => ?_
    rw [GlobalTheory.RingIface.phiA_coeff]
    simp only [WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]
  refine ⟨WittVector.map f w₀, hw₀.map _, fun g hg => ?_, ?_, hφA⟩
  · refine WittVector.ext fun n => ?_
    have := hact g 1 one_ne_zero (fun x m hm hl hx => by
      rw [pow_one]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x
        (IntermediateField.subset_adjoin _ _ ⟨m, hm, hl, hx⟩)) (w₀.coeff n)
    rw [pow_one] at this
    rw [GlobalTheory.RingIface.sigA_coeff, WittVector.map_coeff]
    exact this
  · rw [← hφA]
    refine WittVector.ext fun n => ?_
    rw [GlobalTheory.RingIface.sigA_coeff, GlobalTheory.RingIface.phiA_coeff, WittVector.map_coeff]
    exact hact F l (Fact.out : l.Prime).ne_zero hF (w₀.coeff n)

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedPeriodAinfUnitStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_period_ainf_unit : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l), (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) → ∀ u : ℤ_[l]ˣ, ∃ w : Per.Ainf l, IsUnit w ∧ (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σA g w = w) ∧ Per.σA F w = Per.zA l u * w ∧ Per.φA l w = Per.zA l u * w := by
  first | exact @GlobalTheory.MemLoc.exists_unramified_period | exact GlobalTheory.MemLoc.exists_unramified_period | (intros; apply GlobalTheory.MemLoc.exists_unramified_period <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicAdmissibleSemistable
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Inhab

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

include P in
theorem fixed_frob (c : ↥(MaximalUnramifiedExtension l)) (hc : frobUr (l := l) c = c) : ∃ q : ℚ_[l], algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q = c := by
  let K := adjExt (c : Om l)
  let x : ↥(K0 K) := ⟨c, mem_adjExt _, c.2⟩
  have h1 : (P.PD K).φ (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c := by
    rw [P.PD_φ, phiB_algebraMap, hc]
  have h2 : (P.PD K).ι (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) ∈ (P.PD K).Fil 0 := by
    have e : (P.PD K).ι (algebraMap ↥(K0 K) P.R.B x) = algebraMap ↥(K0 K) P.R.BdR x := (P.PD K).ι.commutes x
    have e2 : algebraMap ↥(K0 K) P.R.BdR x = (algebraMap ↥(K0 K) ↥K.1 x) • (1 : P.R.BdR) := by
      rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR, Algebra.algebraMap_eq_smul_one]
    have e3 : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c = algebraMap ↥(K0 K) P.R.B x := rfl
    rw [e3, e, e2]
    exact Submodule.smul_mem _ _ (P.PD K).one_mem
  obtain ⟨q, hq⟩ := (P.PD K).fund _ h1 h2
  haveI := nontrivial_B P
  refine ⟨q, (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective ?_⟩
  rw [← hq, ← IsScalarTower.algebraMap_apply]

theorem kd_alg (q : ℚ_[l]) : kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] P.R.BdR q := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]; rfl

theorem act_zpow (g : GQ l) (a : ℤ) :
    P.actQ g (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) =
      algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (isUnit_tB P).unit =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * (isUnit_tB P).unit := by
    ext; simp [localPrime_galoisAction_periodT, Algebra.smul_def]
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at h2
  rw [← map_zpow P.χQ]
  exact h2

end GlobalTheory.PMon.Inhab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleEmbeddingFrobeniusGaloisCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleEmbeddingFrobeniusGaloisCompat
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Decompl

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem ioE_fixed_of_resΓ_eq_one (hO : Function.Injective (algebraMap O LL)) (g : G)
    (hg : W.resΓ g = 1) (e : W.EE) : gR g (E.ioE e) = E.ioE e := by
  rw [← GlobalTheory.TorsionBoundCompare.ioE_γ E hO g e, hg, map_one]
  rfl

theorem ioE_letπ : E.ioE (algebraMap (LetA O n) W.EE letπ) = inclR πA := by
  rw [E.ioE_ext, E.io_π]

theorem ioE_bounded_pole {p : ℕ} (hp : PD.p = p) (e : W.EE) :
    ∃ c : ℕ, Near (inclR : RA →+* RW) p (inclR πA) 0 (inclR πA ^ c * E.ioE e) := by
  obtain ⟨a, m, h⟩ := W.EE_dense e 1
  rw [pow_one, Ideal.mem_span_singleton, hp] at h
  obtain ⟨r, hr⟩ := h
  have h1 := congrArg E.ioE hr
  rw [map_sub, map_mul, map_mul, map_natCast, map_pow, map_pow, ioE_letπ, E.ioE_ext] at h1
  refine ⟨m, E.io a, E.ioE r, ?_⟩
  rw [pow_zero, one_mul, ← h1]
  change _ = inclR (E.io a) + _
  ring

end Generic

set_option synthInstance.maxHeartbeats 200000 in
theorem ioE_compat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ e, E.tie.ioE (W.φE e) = φRW LL (E.tie.ioE e)) ∧ (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ e, AI.gRW LL (g : GQ l) (E.tie.ioE e) = E.tie.ioE e) ∧ E.tie.ioE (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ) = piR AI LL s ∧ (∀ e, ∃ c : ℕ, NearPi AI LL s 0 (piR AI LL s ^ c * E.tie.ioE e)) := by
  intro l _ P AI K s LL h W E
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  exact ⟨fun e => GlobalTheory.TorsionBoundCompare.ioE_φ E.tie hO e,
    fun g hg e => ioE_fixed_of_resΓ_eq_one E.tie hO g hg e, ioE_letπ E.tie,
    fun e => ioE_bounded_pole E.tie (P.PD_p K) e⟩

end GlobalTheory.Decompl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleEmbeddingFrobeniusGaloisCompatStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem _root_.GlobalTheory.T.etaleEmbedding_frobenius_galois_compat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ e, E.tie.ioE (W.φE e) = φRW LL (E.tie.ioE e)) ∧ (∀ g : ↥(GK K), W.resΓ g = 1 → ∀ e, AI.gRW LL (g : GQ l) (E.tie.ioE e) = E.tie.ioE e) ∧ E.tie.ioE (algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE letπ) = piR AI LL s ∧ (∀ e, ∃ c : ℕ, NearPi AI LL s 0 (piR AI LL s ^ c * E.tie.ioE e)) := by
  first | exact @GlobalTheory.Decompl.ioE_compat | exact GlobalTheory.Decompl.ioE_compat | (intros; apply GlobalTheory.Decompl.ioE_compat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrKIsometricAndOneSubSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrKIsometricAndOneSubSurjective
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime]

theorem norm_algHom_self (F : IntermediateField ℚ_[l] (Om l)) (σ : ↥F →ₐ[ℚ_[l]] ↥F) (c : ↥F) :
    ‖((σ c : ↥F) : Om l)‖ = ‖(c : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  unfold spectralNorm
  have h1 := minpoly.algHom_eq F.val F.val.injective (σ c)
  have h2 := minpoly.algHom_eq F.val F.val.injective c
  have h3 := minpoly.algHom_eq σ σ.injective c
  simp only [IntermediateField.coe_val] at h1 h2
  exact congrArg spectralValue (h1.trans (h3.trans h2.symm))

theorem norm_l_pow_lt_one {j : ℕ} (hj : 1 ≤ j) : ‖(l : Om l) ^ j‖ < 1 := by
  rw [norm_pow]
  apply pow_lt_one₀ (norm_nonneg _) _ (by omega)
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem norm_sub_pow_mul_algHom (F : IntermediateField ℚ_[l] (Om l)) (σ : ↥F →ₐ[ℚ_[l]] ↥F)
    {j : ℕ} (hj : 1 ≤ j) (d : ↥F) :
    ‖((d - (l : ↥F) ^ j * σ d : ↥F) : Om l)‖ = ‖(d : Om l)‖ := by
  by_cases hd : d = 0
  · simp [hd]
  have hd' : 0 < ‖(d : Om l)‖ := norm_pos_iff.2 (by exact_mod_cast hd)
  have hlt : ‖-((l : Om l) ^ j * ((σ d : ↥F) : Om l))‖ < ‖(d : Om l)‖ := by
    rw [norm_neg, norm_mul, norm_algHom_self]
    exact mul_lt_of_lt_one_left hd' (norm_l_pow_lt_one hj)
  have e : ((d - (l : ↥F) ^ j * σ d : ↥F) : Om l) =
      (d : Om l) + -((l : Om l) ^ j * ((σ d : ↥F) : Om l)) := by
    push_cast
    ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

theorem frK_isometric_and_one_sub_surjective (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) :
    (∀ c : ↥(K0 K), ‖((frK P K c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖) ∧
    ∀ j : ℕ, 1 ≤ j → ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 →
      ∃ d : ↥(K0 K), ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ j * frK P K d = c := by
  refine ⟨norm_algHom_self _ _, fun j hj c hc => ?_⟩
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  let T : ↥(K0 K) →ₗ[ℚ_[l]] ↥(K0 K) :=
    LinearMap.id - (LinearMap.mulLeft ℚ_[l] ((l : ↥(K0 K)) ^ j)).comp (frK P K).toLinearMap
  have hT : ∀ d, T d = d - (l : ↥(K0 K)) ^ j * frK P K d := fun d => rfl
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro d hd
    have := norm_sub_pow_mul_algHom _ (frK P K) hj d
    rw [← hT, hd] at this
    have h0 : (d : Om l) = 0 := by
      rw [← norm_eq_zero, ← this]; simp
    exact_mod_cast h0
  obtain ⟨d, hd⟩ := LinearMap.injective_iff_surjective.1 hinj c
  rw [hT] at hd
  refine ⟨d, ?_, hd⟩
  rw [← norm_sub_pow_mul_algHom _ (frK P K) hj d, hd]
  exact hc

end GlobalTheory.ExpImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrKIsometricAndOneSubSurjectiveStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), (∀ c : ↥(K0 K), ‖((frK P K c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖) ∧ ∀ j : ℕ, 1 ≤ j → ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 → ∃ d : ↥(K0 K), ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ j * frK P K d = c := by
  first | exact @GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective | exact GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective | (intros; apply GlobalTheory.ExpImage.frK_isometric_and_one_sub_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActDEqOfEqOne
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

namespace GlobalTheory.CutTrivIne

section Gen

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) [IsDomain O]


set_option synthInstance.maxHeartbeats 400000 in
theorem eq_zero_of_phi (k : ℕ) (x : KOG O k) (hx : Br.phi Bw k x = 0) : x = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : Br.vecS Bw k v ∈ stdG (Br.Ow Bw) (Br.LLw Bw) k :=
    (Submodule.Quotient.mk_eq_zero _).1 hx
  obtain ⟨u, hu⟩ := h1
  refine (Submodule.Quotient.mk_eq_zero _).2 ⟨fun j => Bw.eO.symm (u j), ?_⟩
  funext j
  apply (Br.toLLK Bw).injective
  have h2 := Br.toLLK_alg Bw (Bw.eO.symm (u j))
  rw [RingEquiv.apply_symm_apply] at h2
  exact h2.trans (congrFun hu j)

end Gen

theorem actD_eq_of_eq_one {G LL O : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL] {k : ℕ}
    (M : G →* Matrix (Fin k) (Fin k) LL) (L : Lattice (O := O) (matRep M)) (g : G) (hg : M g = 1)
    (x : (Fin k → LL) ⧸ L.T) : actD L g x = x := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h : matRep M g v = v := by
    show Matrix.toLin' (M g) v = v
    rw [hg, Matrix.toLin'_one]
    rfl
  show Submodule.Quotient.mk (matRep M g v) = _
  rw [h]

theorem chiRatO_one (D : D7) (i : D.nd.Loc) (γ : GE D.nd) : chiRatO D.nd i 1 γ = 1 := by
  simp [chiRatO, twistM]


set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ (D : D7) (i : D.nd.Loc) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1)), ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ C, locFun i (chiRatO D.nd i 1) w hw f ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw)) → resIne i C w = ⊥ := by
  intro D i C w hw h
  rw [eq_bot_iff]
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨x, hx⟩ := h f hf
  rw [Submodule.mem_bot]
  funext γ
  obtain ⟨g, hg⟩ := (Br.ι_bijective (D.nbr i w hw)).2 ⟨γ.1, Ine_le_Dec _ γ.2⟩
  have hg' : ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) = γ.1 := congrArg Subtype.val hg
  have hmem : g ∈ Br.inert D.nbr i w hw := by
    show ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)
    rw [hg']
    exact γ.2
  have h1 : Br.loc D.nbr i w hw (chiRatO D.nd i 1) g = 1 := by
    show (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))).mapMatrix
      ((D.nbr i w hw).eO.toRingHom.mapMatrix
        (chiRatO D.nd i 1 ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))) = 1
    rw [chiRatO_one, map_one, map_one]
  have h2 := hx g hmem
  rw [actD_eq_of_eq_one _ _ g h1, sub_self] at h2
  have h3 := eq_zero_of_phi (D.nbr i w hw) 1 _ h2
  rw [hg'] at h3
  exact h3

end GlobalTheory.CutTrivIne

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexReadingLocalEmbedding
noncomputable section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.ReadEmbEx

theorem exists_read {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)
    (ι : FractionRing O →+* ℂ) :
    ∃ φ : ↥B.LL.1 →+* ℂ, ∀ a : O, φ (B.toLL a) = ι (algebraMap O (FractionRing O) a) := by
  have hinj : Function.Injective B.toLL := fun _ _ h => B.eO.injective (Subtype.ext h)
  let f : FractionRing O →+* ↥B.LL.1 := IsFractionRing.lift (g := B.toLL) hinj
  have hf : ∀ a : O, f (algebraMap O (FractionRing O) a) = B.toLL a := fun a =>
    IsFractionRing.lift_algebraMap _ a
  have hb : Function.Bijective f := by
    refine ⟨f.injective, fun y => ?_⟩
    have hint (x : Om l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
      have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
      rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
      constructor
      · intro h n
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
        exact ((minpoly ℤ_[l] x).coeff n).2
      · intro h
        have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
          rw [Polynomial.lifts_iff_coeff_lifts]
          exact fun n => ⟨⟨_, h n⟩, rfl⟩
        obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
        refine ⟨q, hqm, ?_⟩
        rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]
    have hmem (x : ↥B.LL.1) : x ∈ OL B.LL ↔ ‖(x : Om l)‖ ≤ 1 := by
      rw [← hint, OL, mem_integralClosure_iff]
      exact (isIntegral_algHom_iff (B.LL.1.val.restrictScalars ℤ_[l]) B.LL.1.val.toRingHom.injective).symm
    have hnorm (x : ↥B.LL.1) : ‖(x : Om l)‖ ≤ 1 → ∃ n : O, x = B.toLL n := by
      intro hx
      refine ⟨B.eO.symm ⟨x, (hmem x).2 hx⟩, ?_⟩
      simp [LocBridge.toLL]
    have hfrac (y : ↥B.LL.1) : ∃ n d : O, d ≠ 0 ∧ B.toLL d * y = B.toLL n := by
      by_cases h : ‖(y : Om l)‖ ≤ 1
      · obtain ⟨n, hn⟩ := hnorm y h
        refine ⟨n, 1, fun h1 => ?_, by simp [hn]⟩
        have := congrArg B.toLL h1
        simp at this
      · have hy : y ≠ 0 := by
          rintro rfl
          simp at h
        have h' : ‖((y⁻¹ : ↥B.LL.1) : Om l)‖ ≤ 1 := by
          rw [IntermediateField.coe_inv, norm_inv]
          exact inv_le_one_of_one_le₀ (not_le.1 h).le
        obtain ⟨d, hd⟩ := hnorm _ h'
        refine ⟨1, d, fun h1 => ?_, by rw [← hd, map_one, inv_mul_cancel₀ hy]⟩
        rw [h1, map_zero] at hd
        exact hy (inv_eq_zero.1 hd)
    obtain ⟨n, d, hd, e⟩ := hfrac y
    have hd' : B.toLL d ≠ 0 := fun h0 => hd (hinj (h0.trans (map_zero _).symm))
    refine ⟨algebraMap O _ n / algebraMap O _ d, ?_⟩
    rw [map_div₀, hf, hf, ← e, mul_div_cancel_left₀ _ hd']
  let e := RingEquiv.ofBijective f hb
  refine ⟨ι.comp e.symm.toRingHom, fun a => ?_⟩
  rw [← hf]
  exact congrArg ι (e.symm_apply_apply _)

theorem exists_readEmb : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv), ∃ τc : D.host.E →+* ℂ, ReadEmb bkP i ι v hv τ τc ∧ ∀ (v' : HeightOneSpectrum (𝓞 D.host.E)) (hv' : v' ∈ placesOver D.host.E (D.ntw.l i)) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' → ReadEmb bkP i ι v' hv' τ' (τc.comp (cj D)) := by
  intro D bkP i ι v hv τ
  obtain ⟨φ, hφ⟩ := exists_read (bkP.br i v hv) ι
  let c : D.host.E →+* ↥(bkP.br i v hv).Kw.1 :=
    ((bkP.br i v hv).j.comp (algebraMap D.host.E D.nd.Om)).codRestrict (bkP.br i v hv).Kw.1 (bkP.br i v hv).j_E
  have h : ReadEmb bkP i ι v hv τ ((φ.comp (AlgHom.toRingHom τ)).comp c) := by
    intro x n d hx
    have := congrArg φ hx.2
    rw [map_mul, hφ, hφ] at this
    exact this
  exact ⟨_, h, fun v' hv' τ' hc x n d hx => h _ n d ((hc x n d).1 hx)⟩

end GlobalTheory.ReadEmbEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelSubgroupMemWachSubgroups
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelSubgroupMemWachSubgroups
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

namespace GlobalTheory.Cyc.Decomp

theorem le_v_of_norm_le {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (k : ℕ)
    (hx : ‖x‖ ≤ (l : ℝ) ^ (-(k : ℤ))) :
    ((k : ℚ) : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) := by
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlk : (l : ℚ_[l]) ^ k ≠ 0 := pow_ne_zero k hl
  have hy : ‖x / (l : ℚ_[l]) ^ k‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p_pow, div_le_one (zpow_pos hlpos _)]
    exact hx
  obtain ⟨y, hxy⟩ : ∃ y : ℤ_[l], x = (l : ℚ_[l]) ^ k * (y : ℚ_[l]) := by
    refine ⟨⟨x / (l : ℚ_[l]) ^ k, hy⟩, ?_⟩
    show x = (l : ℚ_[l]) ^ k * (x / (l : ℚ_[l]) ^ k)
    field_simp
  have hmem : algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]) ∈ OL LL := by
    have e : algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l]) = algebraMap ℤ_[l] ↥LL.1 y := rfl
    rw [e]
    exact (OL LL).algebraMap_mem y
  have hv0 : 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 (y : ℚ_[l])) := (P.27 LL _).2 hmem
  have hk : k • (1 : WithTop ℚ) = ((k : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_one]
  rw [hxy, map_mul, map_pow, map_natCast, (P.v LL).map_mul, (P.v LL).map_pow, P.26 LL, hk]
  exact le_add_of_nonneg_right hv0

theorem grp_GKs_H : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))), W.s = s → ∀ g : ↥(GK K), ((g : GQ l) ∈ Gj K s → g ∈ W.GKs) ∧ ((g : GQ l) ∈ Hinf K → W.resΓ g = 1) := by
  intro l _ P _ K s LL _ W hW g
  have hcyc : IsCyc P.χQ := P.20
  have hχ : ((P.PD K).χ g : ℚ_[l]) = (P.χQ (g : GQ l) : ℚ_[l]) := P.PD_χ K g
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · unfold Gj at hg
    obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) s
    have hmem : ζ ∈ Ks K s := by
      unfold Ks
      exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ s = 1} ≤ _)
        (IntermediateField.subset_adjoin ℚ_[l] _ hζ.pow_eq_one)
    have hfix : (g : GQ l) ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hmem
    have hn : ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) :=
      hcyc.norm_sub_one_le_of_prim (g : GQ l) s hζ hfix
    have hv := le_v_of_norm_le P LL ((P.χQ (g : GQ l) : ℚ_[l]) - 1) s hn
    have e : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l]) - 1 =
        algebraMap ℚ_[l] ↥LL.1 ((P.χQ (g : GQ l) : ℚ_[l]) - 1) := by
      rw [hχ, map_sub, map_one]
    rw [W.GKs_def g, hW, e]
    exact_mod_cast hv
  · unfold Hinf at hg
    have hall : ∀ m : ℕ, ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      intro m
      refine (hcyc.fix_iff (g : GQ l) m).1 (fun ζ hζ => ?_)
      have hmem : ζ ∈ Kinf K := by
        unfold Kinf
        exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | ∃ j : ℕ, x ^ l ^ j = 1} ≤ _)
          (IntermediateField.subset_adjoin ℚ_[l] _ ⟨m, hζ⟩)
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ hmem
    have h1 : (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
      by_contra hne
      have hpos : 0 < ‖(P.χQ (g : GQ l) : ℚ_[l]) - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hpos
      exact absurd (hall m) (not_le.2 hm)
    have h2 : (algebraMap ↥(OL LL) ↥LL.1) ↑(W.χΓ (W.resΓ g)) = 1 := by
      rw [W.χΓ_res g, hχ, h1, map_one]
    have h3 : ((W.χΓ (W.resΓ g) : ↥(OL LL))) = 1 := Subtype.ext h2
    have h4 : W.χΓ (W.resΓ g) = 1 := Units.val_eq_one.1 h3
    exact W.χΓ_inj (by rw [h4, map_one])

end GlobalTheory.Cyc.Decomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelSubgroupMemWachSubgroupsStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicLevelSubgroup_mem_wachSubgroups : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))), W.s = s → ∀ g : ↥(GK K), ((g : GQ l) ∈ Gj K s → g ∈ W.GKs) ∧ ((g : GQ l) ∈ Hinf K → W.resΓ g = 1) := by
  first | exact @GlobalTheory.Cyc.Decomp.grp_GKs_H | exact GlobalTheory.Cyc.Decomp.grp_GKs_H | (intros; apply GlobalTheory.Cyc.Decomp.grp_GKs_H <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutValueMemHeckeValueIdealOffSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutValueMemHeckeValueIdealOffSupport
namespace GlobalTheory.Cut

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem cutVal_exists_single {O X : Type} [CommRing O] [IsDomain O] [Fintype X]
    (T : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (x : X) :
    ∃ g ∈ T, g x ≠ 0 ∧ ∀ y, y ≠ x → g y = 0 := by
  classical
  have key : ∀ y : X, ∃ f ∈ T, f x ≠ 0 ∧ (y ≠ x → f y = 0) := by
    intro y
    by_cases hy : y = x
    · exact ⟨1, one_mem _, one_ne_zero, fun h => absurd hy h⟩
    · obtain ⟨f, hf, hne⟩ := hsep y x hy
      refine ⟨f - algebraMap _ _ (f y), sub_mem hf (Subalgebra.algebraMap_mem _ _), ?_, fun _ => ?_⟩
      · simpa [sub_eq_zero] using hne.symm
      · simp
  choose f hf h1 h2 using key
  refine ⟨∏ y, f y, prod_mem fun y _ => hf y, ?_, fun y hy => ?_⟩
  · rw [Finset.prod_apply]
    exact Finset.prod_ne_zero_iff.2 fun y _ => h1 y
  · rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (h2 y hy)

theorem cutVal_coord_eq_zero {O X X' ι : Type} [CommRing O] [IsDomain O] [Fintype X] [Fintype ι]
    (T : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y)
    (p : X' → X) (b : ι → X' → O)
    (huniq : ∀ cf : ι → T, (0 : X' → O) = ∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k →
      cf = 0)
    (cf : ι → T) (x : X)
    (h0 : ∀ x', p x' = x → (∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k) x' = 0)
    (k : ι) : (cf k : X → O) x = 0 := by
  obtain ⟨g, hg, hx, hy⟩ := cutVal_exists_single T hsep x
  have h := huniq (fun k => ⟨g, hg⟩ * cf k) (by
    funext x'
    have : (∑ k, ((fun x' => (((⟨g, hg⟩ : T) * cf k : T) : X → O) (p x')) : X' → O) * b k) x' =
        g (p x') * (∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k) x' := by
      simp [Finset.sum_apply, Finset.mul_sum, mul_assoc]
    rw [this]
    by_cases hp : p x' = x
    · rw [h0 x' hp]; simp
    · rw [hy _ hp]; simp)
  have h2 : g x * (cf k : X → O) x = 0 := by
    have := congrArg (fun c : ι → T => (c k : X → O) x) h
    simpa using this
  exact (mul_eq_zero.1 h2).resolve_left hx

theorem value_mem_ccOff :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  intro D i r ρ π Xs S _ hS _ f hf h0
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, ⟨b, -, hb⟩, -⟩, -, ⟨hπ, -⟩, -⟩ := hS
  obtain ⟨cf, hcf, -⟩ := hb f hf
  have huniq : ∀ c : Fin D.R.t.factorial → D.nd.T i,
      (0 : S.X' → D.nd.O i) = ∑ k, ((fun x' => (c k : D.nd.X i → D.nd.O i) (S.p x')) :
        S.X' → D.nd.O i) * b k → c = 0 := by
    intro c hc
    obtain ⟨c0, -, hc0⟩ := hb 0 (zero_mem _)
    rw [hc0 c hc, hc0 0 (by funext x'; simp)]
  have hz : ∀ k, ∀ x ∈ Xs, x ∉ D.nd.Z i → (cf k : D.nd.X i → D.nd.O i) x = 0 := by
    intro k x hx hZ
    refine cutVal_coord_eq_zero (D.nd.T i) (D.nd.T_sep i) S.p b huniq cf x (fun x' hp => ?_) k
    rw [← hcf]
    exact h0 x' (hp ▸ hx) (hp ▸ hZ)
  rw [hcf, Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Pi.mul_apply]
  refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨cf k, (cf k).2, hz k, ?_⟩)
  rw [hπ]

end GlobalTheory.Cut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutValueMemHeckeValueIdealOffSupportStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutValue_mem_heckeValueIdealOffSupport : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  first | exact @GlobalTheory.Cut.value_mem_ccOff | exact GlobalTheory.Cut.value_mem_ccOff | (intros; apply GlobalTheory.Cut.value_mem_ccOff <;> assumption)
end
end
