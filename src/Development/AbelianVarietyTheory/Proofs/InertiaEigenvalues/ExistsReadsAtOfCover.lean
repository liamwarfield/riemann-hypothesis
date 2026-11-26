module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivMapLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

variable (D : D7)

theorem val_nonneg_iff (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 ≤ D.what₂.places.val w x ↔ (D.plEq w).valuation D.what₂.LL x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := by simpa using hx
  rw [D.val_eq w x hx, vAdd, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.log_exp]
  norm_cast
  exact neg_nonneg

theorem val_pos_iff (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    0 < D.what₂.places.val w x ↔ (D.plEq w).valuation D.what₂.LL x < 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : (D.plEq w).valuation D.what₂.LL x ≠ 0 := by simpa using hx
  rw [D.val_eq w x hx, vAdd, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.log_exp]
  norm_cast
  exact neg_pos

theorem val_pos_iff_mem (w : D.what₂.places.Pl) (x : 𝓞 ↥D.LL0) :
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔
      algebraMap (𝓞 ↥D.LL0) (𝓞 D.what₂.LL) x ∈ (D.plEq w).asIdeal := by
  rw [val_pos_iff, ← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL)]
  rfl

theorem val_resChar_pos (w : D.what₂.places.Pl) :
    0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
  rw [D.what₂.places.val_resChar]
  exact_mod_cast D.what₂.places.ramIdx_pos w

theorem eq_resChar_of_pos (w : D.what₂.places.Pl) {p : ℕ} (hp : p.Prime)
    (h : 0 < D.what₂.places.val w ((p : ℕ) : D.what₂.LL)) : p = D.what₂.places.resChar w := by
  by_contra hne
  have h1 := (val_pos_iff_mem D w (p : 𝓞 ↥D.LL0)).1 (by simpa using h)
  have h2 := (val_pos_iff_mem D w (D.what₂.places.resChar w : 𝓞 ↥D.LL0)).1 (by simpa using val_resChar_pos D w)
  rw [map_natCast] at h1 h2
  have h3 : IsCoprime ((p : ℕ) : 𝓞 D.what₂.LL) ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) :=
    Nat.Coprime.cast ((Nat.coprime_primes hp (D.what₂.places.resChar_prime w)).2 hne)
  obtain ⟨a, b, hab⟩ := h3
  exact (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem exists_star_int (hG : IsGalois ℚ ↥D.LL0) (x : 𝓞 ↥D.LL0) :
    ∃ y : 𝓞 ↥D.LL0, ((y : ↥D.LL0) : D.what₂.LL) = star ((x : ↥D.LL0) : D.what₂.LL) := by
  let s : D.what₂.LL →ₐ[ℚ] D.what₂.LL := (starRingEnd D.what₂.LL).toRatAlgHom
  have h1 : star ((x : ↥D.LL0) : D.what₂.LL) ∈ D.LL0 :=
    (IntermediateField.normal_iff_forall_map_le.1 hG.to_normal s) ⟨_, (x : ↥D.LL0).2, rfl⟩
  have h2 : IsIntegral ℤ (star ((x : ↥D.LL0) : D.what₂.LL)) :=
    IsIntegral.map_of_comp_eq (RingHom.id ℤ) ((starRingEnd D.what₂.LL).comp (algebraMap ↥D.LL0 D.what₂.LL))
      (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe x)
  exact ⟨⟨⟨_, h1⟩, (isIntegral_algebraMap_iff ).1 h2⟩, rfl⟩

theorem exists_star (hG : IsGalois ℚ ↥D.LL0) (x : ↥D.LL0) : ∃ y : ↥D.LL0, (y : D.what₂.LL) = star (x : D.what₂.LL) :=
  ⟨⟨_, (IntermediateField.normal_iff_forall_map_le.1 hG.to_normal (starRingEnd D.what₂.LL).toRatAlgHom)
    ⟨_, x.2, rfl⟩⟩, rfl⟩

def OverOne (w w' : D.what₂.places.Pl) : Prop :=
  ∀ x : 𝓞 ↥D.LL0, 0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔
    0 < D.what₂.places.val w' ((x : ↥D.LL0) : D.what₂.LL)

def OverOnePair (w w' : D.what₂.places.Pl) : Prop := OverOne D w w' ∨ OverOne D (D.what₂.places.conj w) w'

variable {D}

theorem OverOne.conj (hG : IsGalois ℚ ↥D.LL0) {w w' : D.what₂.places.Pl} (h : OverOne D w w') :
    OverOne D (D.what₂.places.conj w) (D.what₂.places.conj w') := fun x => by
  obtain ⟨y, hy⟩ := exists_star_int D hG x
  rw [D.conj_val, D.conj_val, ← hy]
  exact h y

theorem overOnePair_refl (w : D.what₂.places.Pl) : OverOnePair D w w := Or.inl fun _ => Iff.rfl

theorem overOnePair_conj (w : D.what₂.places.Pl) : OverOnePair D w (D.what₂.places.conj w) := Or.inr fun _ => Iff.rfl

theorem OverOnePair.symm (hG : IsGalois ℚ ↥D.LL0) {w w' : D.what₂.places.Pl} (h : OverOnePair D w w') :
    OverOnePair D w' w := by
  rcases h with h | h
  · exact Or.inl fun x => (h x).symm
  · have h1 := h.conj hG
    rw [D.what₂.places.conj_conj] at h1
    exact Or.inr fun x => (h1 x).symm

theorem OverOnePair.trans (hG : IsGalois ℚ ↥D.LL0) {w w' w'' : D.what₂.places.Pl} (h : OverOnePair D w w')
    (h' : OverOnePair D w' w'') : OverOnePair D w w'' := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact Or.inl fun x => (h x).trans (h' x)
  · exact Or.inr fun x => (h.conj hG x).trans (h' x)
  · exact Or.inr fun x => (h x).trans (h' x)
  · have h1 := h.conj hG
    rw [D.what₂.places.conj_conj] at h1
    exact Or.inl fun x => (h1 x).trans (h' x)

def sideEmb (i : D.ntw.Tw) (b : Bool) : ↥D.LL0 →+* FractionRing (D.ntw.O0 i) :=
  if b then D.ntw.emb0 i else D.ntw.emb0b i

def ReadsAt (i : D.ntw.Tw) (b : Bool) (w : D.what₂.places.Pl) : Prop :=
  ∀ x : 𝓞 ↥D.LL0, (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = sideEmb i b (x : ↥D.LL0)) ↔
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL)

theorem sideEmb_not (i : D.ntw.Tw) (b : Bool) {x y : ↥D.LL0} (h : (y : D.what₂.LL) = star (x : D.what₂.LL)) :
    sideEmb i (!b) x = sideEmb i b y := by
  cases b
  · exact (D.ntw.restX_coefficientEmbedding_conj i y x (by rw [h, star_star])).symm
  · exact D.ntw.restX_coefficientEmbedding_conj i x y h

theorem ReadsAt.conj (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {b : Bool} {w : D.what₂.places.Pl} (h : ReadsAt i b w) :
    ReadsAt i (!b) (D.what₂.places.conj w) := fun x => by
  obtain ⟨y, hy⟩ := exists_star_int D hG x
  rw [sideEmb_not i b hy, D.conj_val, ← hy]
  exact h y

theorem ReadsAt.of_overOne {i : D.ntw.Tw} {b : Bool} {w w' : D.what₂.places.Pl} (h : ReadsAt i b w) (h' : OverOne D w w') :
    ReadsAt i b w' := fun x => (h x).trans (h' x)

theorem l_mem_max (i : D.ntw.Tw) : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := fun hu =>
  D.ntw.O_l i (by simpa using hu.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)))

theorem ReadsAt.l_eq {i : D.ntw.Tw} {b : Bool} {w : D.what₂.places.Pl} (h : ReadsAt i b w) :
    D.ntw.l i = D.what₂.places.resChar w :=
  eq_resChar_of_pos D w (D.ntw.lPrime i).out
    (by simpa using (h (D.ntw.l i : 𝓞 ↥D.LL0)).1 ⟨_, l_mem_max i, by simp⟩)

theorem exists_orbitRep : ∃ o : D.what₂.places.Pl → D.what₂.places.Pl,
    ∀ w, (o w = w ∨ o w = D.what₂.places.conj w) ∧ o (D.what₂.places.conj w) = o w := by
  refine ⟨fun w => @Classical.epsilon _ ⟨w⟩ fun v => v = w ∨ v = D.what₂.places.conj w, fun w => ⟨?_, ?_⟩⟩
  · exact Classical.epsilon_spec (p := fun v => v = w ∨ v = D.what₂.places.conj w) ⟨w, Or.inl rfl⟩
  · simp only [D.what₂.places.conj_conj, or_comm]

theorem isLocalHom_phiK (i : D.ntw.Tw) (k : ℕ) : IsLocalHom (BlochKatoReduction.Gen.phiK D.ntw i k) := by
  haveI := D.ntw.Ok_fin i k
  haveI : FaithfulSMul (D.ntw.O i) (D.ntw.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj i k)
  haveI : IsLocalHom (algebraMap (D.ntw.O0 i) (D.ntw.O i)) := by
    refine ⟨fun y hy => ?_⟩
    by_contra hu
    haveI : CharZero (FractionRing (D.ntw.O0 i)) := (RingHom.charZero_iff (D.ntw.emb0 i).injective).1 inferInstance
    have hl : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ≠ 0 := fun h => by
      have := congrArg (algebraMap _ (FractionRing (D.ntw.O0 i))) h
      rw [map_natCast, map_zero] at this
      exact (D.ntw.lPrime i).out.ne_zero (Nat.cast_eq_zero.1 this)
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (D.ntw.O0 i)
    obtain ⟨n, u, hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl hϖ
    have hy' : y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := hu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hy'
    obtain ⟨a, rfl⟩ := hy'
    rw [map_mul] at hy
    refine D.ntw.O_l i ?_
    rw [← map_natCast (algebraMap (D.ntw.O0 i) (D.ntw.O i)), hu', map_mul, map_pow]
    exact (u.isUnit.map _).mul ((isUnit_of_mul_isUnit_left hy).pow n)
  unfold BlochKatoReduction.Gen.phiK
  infer_instance

structure Reading (i : D.ntw.Tw) (k : ℕ) (b : Bool) (w : D.what₂.places.Pl) : Type 1 where
  Oe : Type
  [cr : CommRing Oe]
  [dom : IsDomain Oe]
  [dvr : IsDiscreteValuationRing Oe]
  [alg : Algebra (D.ntw.Ok i k) Oe]
  inj : Function.Injective (algebraMap (D.ntw.Ok i k) Oe)
  fin : Module.Finite (D.ntw.Ok i k) Oe
  loc : IsLocalHom (algebraMap (D.ntw.Ok i k) Oe)
  emb : D.what₂.LL →+* FractionRing Oe
  emb_w : ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val w x ↔ emb x ∈ (algebraMap Oe (FractionRing Oe)).range
  emb_side : ∀ (x : ↥D.LL0) (y z : D.ntw.O0 i),
    sideEmb i b x * algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) z =
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y →
    emb (x : D.what₂.LL) * algebraMap Oe (FractionRing Oe) (algebraMap (D.ntw.Ok i k) Oe (BlochKatoReduction.Gen.phiK D.ntw i k z)) =
      algebraMap Oe (FractionRing Oe) (algebraMap (D.ntw.Ok i k) Oe (BlochKatoReduction.Gen.phiK D.ntw i k y))

attribute [instance] Reading.cr Reading.dom Reading.dvr Reading.alg

theorem ReadsAt.nonempty_reading {i : D.ntw.Tw} {b : Bool} {w : D.what₂.places.Pl} (h : ReadsAt i b w) (k : ℕ) :
    Nonempty (Reading i k b w) := by
  haveI := D.ntw.Ok_fin i k
  haveI := D.ntw.O_complete i
  haveI := FormalIsogeny.isAdicComplete_maximalIdeal_of_finite (D.ntw.O i) (D.ntw.Ok i k)
  haveI := isLocalHom_phiK i k
  have hinj : Function.Injective (BlochKatoReduction.Gen.phiK D.ntw i k) := (D.ntw.Ok_inj i k).comp (D.ntw.O_inj i)
  let m : FractionRing (D.ntw.O0 i) →+* FractionRing (D.ntw.Ok i k) := IsFractionRing.map hinj
  have hm : ∀ y, m (algebraMap _ _ y) = algebraMap _ _ (BlochKatoReduction.Gen.phiK D.ntw i k y) := fun y => by
    simp [m, IsFractionRing.map]
  obtain ⟨O, _, _, _, _, e, h1, h2, h3, h4, h5⟩ := exists_coeff_ext D.what₂.LL D.LL0 (D.ntw.Ok i k)
    (m.comp (sideEmb i b)) (D.plEq w) fun x => by
      rw [← val_pos_iff_mem, ← h x]
      obtain ⟨φ, hφ⟩ := exists_intMap (sideEmb i b)
      constructor
      · rintro ⟨y, hy, hy'⟩
        exact ⟨_, map_nonunit (BlochKatoReduction.Gen.phiK D.ntw i k) y hy, by rw [← hm, hy']; rfl⟩
      · rintro ⟨y, hy, hy'⟩
        refine ⟨φ x, fun hu => hy ?_, hφ x⟩
        have : y = BlochKatoReduction.Gen.phiK D.ntw i k (φ x) :=
          IsFractionRing.injective _ (FractionRing (D.ntw.Ok i k)) (by rw [hy', ← hm, hφ]; rfl)
        exact this ▸ hu.map _
  refine ⟨{ Oe := O, inj := h1, fin := h2, loc := h3, emb := e
            emb_w := fun x => (val_nonneg_iff D w x).trans (h4 x)
            emb_side := fun x y z hxy => h5 x _ _ ?_ }⟩
  rw [← hm, ← hm, ← hxy, map_mul]
  rfl

def Reading.conj (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} (ρ : Reading i k b w) :
    Reading i k (!b) (D.what₂.places.conj w) where
  Oe := ρ.Oe
  inj := ρ.inj
  fin := ρ.fin
  loc := ρ.loc
  emb := ρ.emb.comp (starRingEnd D.what₂.LL)
  emb_w x := by rw [D.conj_val]; exact ρ.emb_w _
  emb_side x y z h := by
    obtain ⟨x', hx'⟩ := exists_star D hG x
    rw [sideEmb_not i b hx'] at h
    have h1 := ρ.emb_side x' y z h
    rw [hx'] at h1
    exact h1

theorem star_root {x : (D.what₂.LL)ˣ} {n : ℕ} (hn : 0 < n) (h : x ^ n = 1) :
    star (x : D.what₂.LL) = ((x⁻¹ : (D.what₂.LL)ˣ) : D.what₂.LL) := by
  apply D.what₂.embLL.injective
  have h1 : ‖D.what₂.embLL (x : D.what₂.LL)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, map_one]) hn.ne'
  rw [D.starLL_cx, Units.val_inv_eq_inv_val, map_inv₀, Complex.inv_eq_conj h1]

end GlobalTheory.TwistChoice

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisor
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mem_nonZeroDivisors_of_invertible_eq_span {A : Type} [CommRing A] {I : Ideal A} {t : A}
    (hI : Module.Invertible A ↥I) (h : I = Ideal.span {t}) : t ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply (Module.Invertible.toModuleEnd_bijective A ↥I).1
  rw [map_zero]
  ext ⟨y, hy⟩
  rw [h] at hy
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  change x * (z * t) = 0
  linear_combination z * hx

theorem hf_E_span_and_regular : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (g : Hom bk.prism B), B.I = Ideal.span {BK.hf g bk.E} ∧ BK.hf g bk.E ∈ nonZeroDivisors B.A := by
  intro l _ K bk B g
  have h : B.I = Ideal.span {BK.hf g bk.E} := by
    rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ _ _ g]
    change Ideal.map (BK.hf g) (Ideal.span {bk.E}) = _
    rw [Ideal.map_span, Set.image_singleton]
  exact ⟨h, mem_nonZeroDivisors_of_invertible_eq_span B.inv h⟩

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisorStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (g : Hom bk.prism B), B.I = Ideal.span {BK.hf g bk.E} ∧ BK.hf g bk.E ∈ nonZeroDivisors B.A := by
  first | exact @GlobalTheory.BSP.hf_E_span_and_regular | exact GlobalTheory.BSP.hf_E_span_and_regular | (intros; apply GlobalTheory.BSP.hf_E_span_and_regular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Eps0UnramFrob
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem eps0_unram_frob : ∀ (D : D7) (i : D.ntw.Tw) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.ntw.l i) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) A v → (∀ σ ∈ Ine (F := D.host.E) A, eps0 D.ntw i σ = 1) ∧ ∀ σ : Gen.GE D.nd, IsFrob (F := D.host.E) A (normV v) σ → ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ) := by
  intro D i v hv A hA
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
  · have h1 : cycZ D.host.E D.nd.Om (D.ntw.l i) σ = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq hv hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
      simp
    unfold eps0
    rw [MonoidHom.comp_apply, h1, map_one]
  · have h1 := cycZ_of_isFrob (l := D.ntw.l i) hv hA hσ
    show algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i)
      ((cycZ D.host.E D.nd.Om (D.ntw.l i) σ : ℤ_[D.ntw.l i]ˣ) : ℤ_[D.ntw.l i]) = _
    rw [h1, map_natCast]

end GlobalTheory.TripleGal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneNotMemFilOne
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Module

namespace GlobalTheory.NL.JumpsSES

section Trivial

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

theorem fil_anti {a b : ℤ} (h : a ≤ b) : PD.Fil b ≤ PD.Fil a := by
  induction b, h using Int.leInduction with
  | base => exact le_rfl
  | succ n _ ih => exact (PD.Fil_anti n).trans ih

theorem one_not_mem_fil_one : (1 : BdR) ∉ PD.Fil 1 := by
  intro h
  have := PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h
  rw [mul_one] at this
  exact PD.not_mem_filtration_two this

theorem ddR_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) :
    x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        (IsScalarTower.toAlgHom Qp K BdR).toLinearMap) ∧
    (∀ a ≤ 0, x ∈ FilV PD (LL := LL) (V := V) a) ∧
    (∀ a, 1 ≤ a → x ∈ FilV PD (LL := LL) (V := V) a → x = 0) := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx
  let e := Module.finBasis Qp V
  let c : Fin (finrank Qp V) → V ⊗[Qp] BdR →ₗ[Qp] BdR := fun i =>
    (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ (LinearMap.rTensor BdR (e.coord i))
  have hsum : ∀ y : V ⊗[Qp] BdR, y = ∑ i, e i ⊗ₜ[Qp] c i y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul v b =>
      conv_lhs => rw [← e.sum_repr v, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [c, TensorProduct.smul_tmul]
    | add a b ha hb =>
      simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, ← ha, ← hb]
  have hc : ∀ i g y, c i (actVdR PD ρ g y) = PD.actdR g (c i y) := by
    intro i g y
    induction y using TensorProduct.inductionOn with
    | tmul v b =>
      have := ((PD.actdR g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul (e.coord i v) b
      have h2 : PD.actdR g (e.coord i v • b) = e.coord i v • PD.actdR g b := this
      simp only [c, actVdR, LinearMap.comp_apply, AlgebraTensorModule.map_tmul,
        LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, h2, hρ]
      simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hk : ∀ i, ∃ k : K, algebraMap K BdR k = c i x := fun i =>
    PD.invdR (c i x) fun g => by rw [← hc, hx]
  refine ⟨?_, fun a ha => ?_, fun a ha hF => ?_⟩
  · rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    exact ⟨e i ⊗ₜ k, by simp [hk]⟩
  · rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    have : c i x ∈ PD.Fil a := by
      rw [← hk, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (fil_anti PD ha PD.one_mem)
    exact ⟨e i ⊗ₜ ⟨c i x, this⟩, by simp⟩
  · have hF' : ∀ i, ∀ y ∈ FilV PD (LL := LL) (V := V) a, c i y ∈ PD.Fil a := by
      rintro i _ ⟨y, rfl⟩
      induction y using TensorProduct.inductionOn with
      | tmul v b =>
        have : (e.coord i v) • (b : BdR) ∈ (PD.Fil a).restrictScalars Qp := Submodule.smul_mem _ _ b.2
        simpa [c] using this
      | add y z hy hz => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hy hz
    rw [hsum x]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    by_cases h0 : k = 0
    · rw [← hk, h0]; simp
    · exfalso
      apply one_not_mem_fil_one PD
      have h1 := Submodule.smul_mem _ k⁻¹ (fil_anti PD ha (hF' i x hF))
      rwa [← hk, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ h0, one_smul] at h1

theorem jumps_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) (τ : K →ₐ[Qp] LL) (a : ℤ) (ha : IsJumpV PD ρ τ a) : a = 0 := by
  by_contra h0
  apply ha
  ext x
  simp only [FildR, Submodule.mem_inf]
  refine and_congr_right fun hx => ?_
  obtain ⟨-, h1, h2⟩ := ddR_of_trivial PD ρ hρ x hx.1
  rcases lt_or_gt_of_ne h0 with h | h
  · exact ⟨fun _ => h1 a (by omega), fun _ => h1 (a + 1) (by omega)⟩
  · constructor
    · intro hF; rw [h2 _ (by omega) hF]; exact Submodule.zero_mem _
    · intro hF; rw [h2 _ (by omega) hF]; exact Submodule.zero_mem _

end Trivial

theorem jumps_ses_and_one : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsSESLat (Qp := ℚ_[l]) ι π → (∀ τ a, IsJumpV ((D.loc l).PD K) T₁.ρ τ a ↔ IsJumpV ((D.loc l).PD K) T₀.ρ τ a ∨ IsJumpV ((D.loc l).PD K) T₂.ρ τ a) ∧ ∀ τ a, IsJumpV ((D.loc l).PD K) W.one.ρ τ a → a = 0 := by
  intro D HW l _ K s LL h W T₀ T₁ T₂ ι π hc hS
  refine ⟨fun τ a => ?_, fun τ a ha => ?_⟩
  · have h0 : IsCrys ((D.loc l).PD K) T₀.ρ :=
      (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hS.1 hc
    have h2 : IsCrys ((D.loc l).PD K) T₂.ρ :=
      ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2
        hS.2.1 hc).1
    exact GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l _ _ (D.locT l) K LL T₀ T₁ T₂ ι π hS h0 hc h2 τ a
  · haveI := LL.2
    haveI : FiniteDimensional ℚ_[l] W.one.V := Module.Finite.trans ↥LL.1 W.one.V
    exact jumps_of_trivial _ W.one.ρ W.one_triv τ a ha

end GlobalTheory.NL.JumpsSES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityProperties
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.OEStable

variable {l : ℕ} [hl : Fact l.Prime]

theorem perfect_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  refine ⟨algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm a) /
    algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm b), ?_⟩
  rw [frobenius_def, div_pow, ← map_pow (algebraMap (OCb l) (Cb l)),
    ← map_pow (algebraMap (OCb l) (Cb l)), frobeniusEquiv_symm_pow_p,
    frobeniusEquiv_symm_pow_p]

theorem eq_zero_of_forall_dvd (z : WCb l) (h : ∀ n, ((l : ℕ) : WCb l) ^ n ∣ z) : z = 0 := by
  ext m
  obtain ⟨y, hy⟩ := h (m + 1)
  rw [hy, mul_comm, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self m)]
  simp

private theorem sigmaA_eq_map_pt (g : GQ l) (a : Ainf l) : Per.σA g a = WittVector.map (Per.σF g) a := by
  apply GlobalTheory.Prism.inclW_injective
  rw [← galW_inclW]
  exact WittVector.ext fun n => autCb_alg l (galTilt l g) (a.coeff n)

variable {K : FinExt l} (bk : BK K)

theorem sat (w : WCb l) (hw : ((l : ℕ) : WCb l) * w ∈ bk.OE) : w ∈ bk.OE := by
  haveI := perfect_Cb (l := l)
  obtain ⟨ek, pr, hek, hinj, -, -⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  intro n
  obtain ⟨m, s, y, h⟩ := hw (n + 1)
  have h0 : (bk.evW s).coeff 0 = 0 := by
    have e : bk.evW s = (bk.evW X ^ m * w - ((l : ℕ) : WCb l) ^ n * y) * ((l : ℕ) : WCb l) := by
      linear_combination -h
    rw [e, WittVector.mul_charP_coeff_zero]
  have h1 : (bk.ev s).coeff 0 = 0 := by
    have e : (bk.evW s).coeff 0 = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := WittVector.map_coeff _ _ _
    rw [e] at h0
    exact IsFractionRing.injective (OCb l) (Cb l) (h0.trans (map_zero _).symm)
  have h2 : PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) s = 0 :=
    hinj (by rw [hek, h1, map_zero])
  have h3 : ∀ i, ∃ c : Wq l bk.a, coeff i s = ((l : ℕ) : Wq l bk.a) * c := fun i => by
    have h4 := congrArg (coeff i) h2
    rw [coeff_map, map_zero] at h4
    have h5 : coeff i s ∈ RingHom.ker (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) := h4
    rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at h5
    exact h5
  choose c hc using h3
  have h5 : s = ((l : ℕ) : bk.S) * PowerSeries.mk c := by
    ext i
    rw [hc, ← map_natCast (C (R := Wq l bk.a)) l, coeff_C_mul, coeff_mk]
  refine ⟨m, PowerSeries.mk c, y, ?_⟩
  apply sub_eq_zero.1
  apply WittVector.eq_zero_of_p_mul_eq_zero
  rw [h5, map_mul, map_natCast] at h
  linear_combination h

theorem closed (w : WCb l) (h : ∀ n : ℕ, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ w - v) : w ∈ bk.OE := by
  intro n
  obtain ⟨v, hv, z, hz⟩ := h n
  obtain ⟨m, s, y, hy⟩ := hv n
  exact ⟨m, s, y + bk.evW X ^ m * z, by linear_combination hy + bk.evW X ^ m * hz⟩

theorem frob (w : WCb l) (hw : w ∈ bk.OE) : frobW l w ∈ bk.OE := by
  intro n
  obtain ⟨m, s, y, h⟩ := hw n
  have key : ∀ t : bk.S, frobW l (bk.evW t) = bk.evW (frobS l bk.a t) := fun t => by
    rw [BK.evW, RingHom.comp_apply, RingHom.comp_apply, frobW_inclW, bk.ev_frob]
  refine ⟨l * m, frobS l bk.a s, frobW l y, ?_⟩
  have h' := congrArg (frobW l) h
  simp only [map_mul, map_add (f := _), map_pow, map_natCast, key, frobS_X] at h'
  rw [pow_mul]
  linear_combination h'

theorem gal (g : ↥(GK K)) (hg : bk.FixFlat g) (w : WCb l) (hw : w ∈ bk.OE) : galW l (g : GQ l) w = w := by
  obtain ⟨-, -, -, hflat, -, hcomp, -⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  haveI := (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l (OCb l) bk.flat hflat hcomp).1
  have hteich : Per.σA (g : GQ l) (WittVector.teichmuller l bk.flat) = WittVector.teichmuller l bk.flat := by
    rw [sigmaA_eq_map_pt, WittVector.map_teichmuller]
    exact congrArg _ hg
  have hfix : (Per.σA (g : GQ l)).comp bk.ev = bk.ev := by
    refine ringHom_ext_of_sep _ _ (fun r => ?_) ?_ ?_
    · rw [RingHom.comp_apply, bk.ev_C, bk.gal_w]
    · rw [RingHom.comp_apply, bk.ev_X, hteich]
    · intro x hx
      rw [RingHom.comp_apply, bk.ev_X, hteich] at hx
      refine IsHausdorff.haus' (I := Ideal.span {WittVector.teichmuller l bk.flat}) x fun n => ?_
      simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hx n
  have hW : ∀ t : bk.S, galW l (g : GQ l) (bk.evW t) = bk.evW t := fun t => by
    change galW l _ (inclW l (bk.ev t)) = inclW l (bk.ev t)
    rw [galW_inclW, ← RingHom.comp_apply (Per.σA _) bk.ev, hfix]
  obtain ⟨-, -, hu, -, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  apply sub_eq_zero.1
  apply eq_zero_of_forall_dvd
  intro n
  obtain ⟨m, s, y, h⟩ := hw n
  have h' := congrArg (galW l (g : GQ l)) h
  simp only [map_mul, map_add (f := _), map_pow, map_natCast, hW] at h'
  obtain ⟨u, hu'⟩ := hu.pow m
  have e : (u : WCb l) * (galW l (g : GQ l) w - w) =
      ((l : ℕ) : WCb l) ^ n * (galW l (g : GQ l) y - y) := by
    rw [hu']; linear_combination h' - h
  refine ⟨(↑u⁻¹ : WCb l) * (galW l (g : GQ l) y - y), ?_⟩
  calc galW l (g : GQ l) w - w = (↑u⁻¹ : WCb l) * ((u : WCb l) * (galW l (g : GQ l) w - w)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [e]; ring

theorem inv (w : WCb l) (hw : w ∈ bk.OE) (hu : IsUnit w) : ∃ w' ∈ bk.OE, w * w' = 1 := by
  haveI := perfect_Cb (l := l)
  obtain ⟨-, -, -, -, hinv⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨u, rfl⟩ := hu
  have hy : WittVector.constantCoeff (p := l) (R := Cb l) u ∈
      bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := Subring.mem_map.2 ⟨u, hw, rfl⟩
  obtain ⟨v, hv, hvy⟩ := Subring.mem_map.1 (hinv _ hy)
  have hne : WittVector.constantCoeff (p := l) (R := Cb l) u ≠ 0 := by
    intro h0
    have h1 := congrArg (WittVector.constantCoeff (p := l) (R := Cb l)) u.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at h1
    exact zero_ne_one h1
  have h1 : (u : WCb l) * v - 1 ∈ RingHom.ker (WittVector.constantCoeff (p := l) (R := Cb l)) := by
    rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hvy, map_one, mul_inv_cancel₀ hne, sub_self]
  rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at h1
  obtain ⟨z, hz⟩ := h1
  have hz' : z ∈ bk.OE := sat bk z (by
    rw [← hz]; exact sub_mem (mul_mem hw hv) (one_mem _))
  have huv : (u : WCb l) * v = 1 - (-((l : ℕ) : WCb l) * z) := by linear_combination hz
  have hi : (↑u⁻¹ : WCb l) * u = 1 := Units.inv_mul u
  refine ⟨↑u⁻¹, closed bk _ fun n => ⟨v * ∑ i ∈ Finset.range n, (-((l : ℕ) : WCb l) * z) ^ i,
    mul_mem hv (sum_mem fun i _ => pow_mem (mul_mem (neg_mem (natCast_mem _ l)) hz') i),
    ⟨(↑u⁻¹ : WCb l) * (-z) ^ n, ?_⟩⟩, u.mul_inv⟩
  have hgeom := geom_sum_mul_neg (-((l : ℕ) : WCb l) * z) n
  have hq : (-((l : ℕ) : WCb l) * z) ^ n = ((l : ℕ) : WCb l) ^ n * (-z) ^ n := by
    rw [neg_mul, ← mul_neg, mul_pow]
  linear_combination (-(↑u⁻¹ : WCb l)) * hgeom - ((↑u⁻¹ : WCb l) * ∑ i ∈ Finset.range n,
    (-((l : ℕ) : WCb l) * z) ^ i) * huv + (v * ∑ i ∈ Finset.range n, (-((l : ℕ) : WCb l) * z) ^ i) * hi
    - (↑u⁻¹ : WCb l) * hq

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w : WCb l, ((l : ℕ) : WCb l) * w ∈ bk.OE → w ∈ bk.OE) ∧ (∀ w : WCb l, (∀ n : ℕ, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ w - v) → w ∈ bk.OE) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ ∀ w ∈ bk.OE, IsUnit w → ∃ w' ∈ bk.OE, w * w' = 1 := by
  intro l _ K bk
  exact ⟨sat bk, closed bk, frob bk, fun g hg w hw => gal bk g hg w hw, inv bk⟩

end GlobalTheory.OEStable
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityPropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_OE_stability_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w : WCb l, ((l : ℕ) : WCb l) * w ∈ bk.OE → w ∈ bk.OE) ∧ (∀ w : WCb l, (∀ n : ℕ, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ w - v) → w ∈ bk.OE) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ ∀ w ∈ bk.OE, IsUnit w → ∃ w' ∈ bk.OE, w * w' = 1 := by
  first | exact @GlobalTheory.OEStable.main | exact GlobalTheory.OEStable.main | (intros; apply GlobalTheory.OEStable.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismPushoutModAdicPowUniversal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismPushoutModAdicPowUniversal
open GlobalTheory.Prism GlobalTheory.BSP CategoryTheory

namespace GlobalTheory.BSP.PoUniv

variable {l : ℕ} {R : Type} [CommRing R]

def deltaLocus {A B : Type} [CommRing A] [CommRing B] (D : Delta l A) (D' : Delta l B) (c : A →+* B) :
    Subring A where
  carrier := {x | c (D.δ x) = D'.δ (c x)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    simp [D.δ_mul, D'.δ_mul, ha, hb]
  one_mem' := by simp [D.δ_one, D'.δ_one]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    simp [D.δ_add, D'.δ_add, ha, hb]
  zero_mem' := by simp [D.δ_zero, D'.δ_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    have e1 := congrArg c (D.δ_add a (-a))
    have e2 := D'.δ_add (c a) (-c a)
    rw [add_neg_cancel, D.δ_zero] at e1
    rw [add_neg_cancel, D'.δ_zero] at e2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_zero, map_sub, map_add (f := _), map_sum, map_mul, map_pow, map_natCast, map_neg, ha] at e1 ⊢
    linear_combination e2 - e1

private lemma exists_ringHom_of_isPushout {A X Y P W : Type} [CommRing A] [CommRing X]
    [CommRing Y] [CommRing P] [CommRing W] {f : A →+* X} {g : A →+* Y} {i : X →+* P}
    {j : Y →+* P}
    (hP : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom i)
      (CommRingCat.ofHom j)) (u : X →+* W) (v : Y →+* W) (huv : u.comp f = v.comp g) :
    ∃ w : P →+* W, w.comp i = u ∧ w.comp j = v := by
  have hw : CommRingCat.ofHom f ≫ CommRingCat.ofHom u =
      CommRingCat.ofHom g ≫ CommRingCat.ofHom v := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, huv]
  exact ⟨(hP.desc (W := CommRingCat.of W) _ _ hw).hom,
    congrArg CommRingCat.Hom.hom (hP.inl_desc (W := CommRingCat.of W) _ _ hw),
    congrArg CommRingCat.Hom.hom (hP.inr_desc (W := CommRingCat.of W) _ _ hw)⟩

private lemma ringHom_eq_of_isPushout_of_comp_eq {A X Y P W : Type} [CommRing A] [CommRing X] [CommRing Y]
    [CommRing P] [CommRing W] {f : A →+* X} {g : A →+* Y} {i : X →+* P} {j : Y →+* P}
    (hP : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom i)
      (CommRingCat.ofHom j)) {u v : P →+* W} (hi : u.comp i = v.comp i)
    (hj : u.comp j = v.comp j) : u = v := by
  have h := hP.hom_ext (W := CommRingCat.of W) (k := CommRingCat.ofHom u)
    (l := CommRingCat.ofHom v) (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hi])
    (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hj])
  exact congrArg CommRingCat.Hom.hom h

private lemma factorPow_comp_qmap_eq_qmap_comp_factorPow {l : ℕ} {R : Type} [CommRing R]
    {P P' : _root_.GlobalTheory.Prism.Obj l R} (f : _root_.GlobalTheory.Prism.Hom P P') {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI P') hle).comp
        (_root_.GlobalTheory.BSP.qmap f n) =
      (_root_.GlobalTheory.BSP.qmap f m).comp
        (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI P) hle) := by
  refine Ideal.Quotient.ringHom_ext ?_
  ext x
  simp only [RingHom.comp_apply, _root_.GlobalTheory.BSP.qmap_mk]
  rfl

private lemma eq_of_forall_mk_pow_eq_of_isHausdorff {A : Type} [CommRing A] (I : Ideal A) [IsHausdorff I A]
    {x y : A} (hxy : ∀ n, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) :
    x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq]
  exact hxy n

private lemma mem_subring_of_isPushout_of_maps_mem {A X Y P : Type} [CommRing A] [CommRing X] [CommRing Y]
    [CommRing P] {f : A →+* X} {g : A →+* Y} {i : X →+* P} {j : Y →+* P}
    (hP : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom i)
      (CommRingCat.ofHom j)) (T : Subring P) (hi : ∀ x, i x ∈ T) (hj : ∀ y, j y ∈ T)
    (p : P) : p ∈ T := by
  have hcomm : i.comp f = j.comp g := congrArg CommRingCat.Hom.hom hP.w
  obtain ⟨r, hr1, hr2⟩ := exists_ringHom_of_isPushout hP (i.codRestrict T hi)
    (j.codRestrict T hj) (by
      ext z
      exact RingHom.congr_fun hcomm z)
  have hid : T.subtype.comp r = RingHom.id P := by
    refine ringHom_eq_of_isPushout_of_comp_eq hP ?_ ?_
    · ext x
      show ((r (i x) : T) : P) = i x
      rw [← RingHom.comp_apply, hr1]
      rfl
    · ext y
      show ((r (j y) : T) : P) = j y
      rw [← RingHom.comp_apply, hr2]
      rfl
  have hp : T.subtype (r p) = p := RingHom.congr_fun hid p
  rw [← hp]
  exact (r p).2

theorem _root_.GlobalTheory.BSP.PoUniv.isPO_univ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R]
    (B C B' C' : _root_.GlobalTheory.Prism.Obj l R) (h : _root_.GlobalTheory.Prism.Hom B C)
    (k : _root_.GlobalTheory.Prism.Hom B B') (k' : _root_.GlobalTheory.Prism.Hom C C') (h' : _root_.GlobalTheory.Prism.Hom B' C')
    (H : _root_.GlobalTheory.BSP.IsPO h k k' h') (Q : _root_.GlobalTheory.Prism.Obj l R)
    (a : _root_.GlobalTheory.Prism.Hom C Q) (b : _root_.GlobalTheory.Prism.Hom B' Q)
    (hab : a.comp h = b.comp k) :
    ∃! c : _root_.GlobalTheory.Prism.Hom C' Q,
      c.comp k' = a ∧ c.comp h' = b := by
  haveI : IsAdicComplete (_root_.GlobalTheory.BSP.adI Q) Q.A :=
    Q.complete
  have hex : ∀ m, ∃ ψ : C'.A ⧸ _root_.GlobalTheory.BSP.adI C' ^ m →+*
      Q.A ⧸ _root_.GlobalTheory.BSP.adI Q ^ m,
      ψ.comp (_root_.GlobalTheory.BSP.qmap k' m) = _root_.GlobalTheory.BSP.qmap a m ∧
      ψ.comp (_root_.GlobalTheory.BSP.qmap h' m) = _root_.GlobalTheory.BSP.qmap b m := fun m =>
    exists_ringHom_of_isPushout (H.po m) _ _ (by
      rw [← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hab])
  choose ψ hψa hψb using hex
  have hψa' : ∀ m x, ψ m (Ideal.Quotient.mk _ (k'.f x)) =
      Ideal.Quotient.mk _ (a.f x) := by
    intro m x
    have hx := RingHom.congr_fun (hψa m) (Ideal.Quotient.mk _ x)
    simpa [_root_.GlobalTheory.BSP.qmap_mk] using hx
  have hψb' : ∀ m y, ψ m (Ideal.Quotient.mk _ (h'.f y)) =
      Ideal.Quotient.mk _ (b.f y) := by
    intro m y
    have hy := RingHom.congr_fun (hψb m) (Ideal.Quotient.mk _ y)
    simpa [_root_.GlobalTheory.BSP.qmap_mk] using hy
  have hcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI Q) hle).comp
        ((ψ n).comp (Ideal.Quotient.mk _)) = (ψ m).comp (Ideal.Quotient.mk _) := by
    intro m n hle
    have key : (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI Q) hle).comp (ψ n) =
        (ψ m).comp (Ideal.Quotient.factorPow (_root_.GlobalTheory.BSP.adI C') hle) := by
      refine ringHom_eq_of_isPushout_of_comp_eq (H.po n) ?_ ?_
      · rw [RingHom.comp_assoc, hψa, RingHom.comp_assoc, factorPow_comp_qmap_eq_qmap_comp_factorPow,
          factorPow_comp_qmap_eq_qmap_comp_factorPow, ← RingHom.comp_assoc, hψa]
      · rw [RingHom.comp_assoc, hψb, RingHom.comp_assoc, factorPow_comp_qmap_eq_qmap_comp_factorPow,
          factorPow_comp_qmap_eq_qmap_comp_factorPow, ← RingHom.comp_assoc, hψb]
    rw [← RingHom.comp_assoc, key, RingHom.comp_assoc]
    congr 1
  obtain ⟨c0, hc0⟩ : ∃ c0 : C'.A →+* Q.A, ∀ n x,
      Ideal.Quotient.mk (_root_.GlobalTheory.BSP.adI Q ^ n) (c0 x) = ψ n (Ideal.Quotient.mk _ x) :=
    ⟨_, fun n x => IsAdicComplete.mk_liftRingHom _ _ hcompat n x⟩
  have hmap : ∀ n z, z ∈ _root_.GlobalTheory.BSP.adI C' ^ n →
      c0 z ∈ _root_.GlobalTheory.BSP.adI Q ^ n := by
    intro n z hz
    rw [← Ideal.Quotient.eq_zero_iff_mem, hc0, Ideal.Quotient.eq_zero_iff_mem.mpr hz, map_zero]
  have hk : ∀ x, c0 (k'.f x) = a.f x := fun x =>
    eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => by rw [hc0, hψa']
  have hh : ∀ y, c0 (h'.f y) = b.f y := fun y =>
    eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => by rw [hc0, hψb']
  have hδ : ∀ x, c0 (C'.D.δ x) =
      Q.D.δ (c0 x) := by
    intro x
    have hS : ∀ n, ∃ s ∈ _root_.GlobalTheory.BSP.PoUniv.deltaLocus C'.D Q.D c0,
        x - s ∈ _root_.GlobalTheory.BSP.adI C' ^ n := by
      intro n
      have hT := mem_subring_of_isPushout_of_maps_mem (H.po n)
        ((_root_.GlobalTheory.BSP.PoUniv.deltaLocus C'.D Q.D c0).map
          (Ideal.Quotient.mk (_root_.GlobalTheory.BSP.adI C' ^ n)))
        (fun y => by
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [_root_.GlobalTheory.BSP.qmap_mk]
          refine Subring.mem_map.mpr ⟨_, ?_, rfl⟩
          show c0 (C'.D.δ (k'.f y)) =
            Q.D.δ (c0 (k'.f y))
          rw [← k'.f_δ, hk, hk, a.f_δ])
        (fun y => by
          obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [_root_.GlobalTheory.BSP.qmap_mk]
          refine Subring.mem_map.mpr ⟨_, ?_, rfl⟩
          show c0 (C'.D.δ (h'.f y)) =
            Q.D.δ (c0 (h'.f y))
          rw [← h'.f_δ, hh, hh, b.f_δ])
        (Ideal.Quotient.mk _ x)
      obtain ⟨s, hs, hsx⟩ := Subring.mem_map.mp hT
      exact ⟨s, hs, Ideal.Quotient.eq.mp hsx.symm⟩
    refine sub_eq_zero.mp (eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => ?_)
    rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨s, hs, hxs⟩ := hS (n + 1)
    have hs' : c0 (C'.D.δ s) =
        Q.D.δ (c0 s) := hs
    have hlC : (l : C'.A) ∈ _root_.GlobalTheory.BSP.adI C' :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    have hlQ : (l : Q.A) ∈ _root_.GlobalTheory.BSP.adI Q :=
      Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    have h1 := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l C'.A C'.D _ hlC n s
      (x - s) hxs
    have h2 := _root_.GlobalTheory.BSP.delta_add_sub_mem_pow l Q.A Q.D _ hlQ n (c0 s)
      (c0 (x - s)) (hmap _ _ hxs)
    rw [add_sub_cancel] at h1
    rw [← map_add (f := _), add_sub_cancel] at h2
    have h3 := hmap n _ h1
    rw [map_sub, hs'] at h3
    have h4 := Ideal.sub_mem _ h3 h2
    convert h4 using 1
    ring
  have hI : ∀ z ∈ C'.I, c0 z ∈ Q.I := by
    intro z hz
    have hcb : c0.comp h'.f = b.f := RingHom.ext hh
    have hz' : z ∈ Ideal.map h'.f B'.I := by
      rw [_root_.GlobalTheory.Prism.Rigid.map_I_eq l R B' C' h']
      exact hz
    have hmem := Ideal.mem_map_of_mem c0 hz'
    rwa [Ideal.map_map, hcb, _root_.GlobalTheory.Prism.Rigid.map_I_eq l R B' Q b] at hmem
  have hstr : ∀ (r : R) (z : C'.A),
      Ideal.Quotient.mk C'.I z = C'.str r →
      Ideal.Quotient.mk Q.I (c0 z) = Q.str r := by
    intro r z hz
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (B'.str r)
    have h1 := h'.f_str r y hy
    have h2 := b.f_str r y hy
    rw [← h2, ← hh, Ideal.Quotient.eq, ← map_sub]
    refine hI _ ?_
    rw [← Ideal.Quotient.eq, hz, h1]
  let c : _root_.GlobalTheory.Prism.Hom C' Q := ⟨c0, hδ, hI, hstr⟩
  have hcomm : c.comp k' = a ∧ c.comp h' = b :=
    ⟨_root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext hk),
      _root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext hh)⟩
  refine ⟨c, hcomm, fun c' hc' => ?_⟩
  refine _root_.GlobalTheory.Prism.Hom.ext' (RingHom.ext fun x =>
    eq_of_forall_mk_pow_eq_of_isHausdorff (_root_.GlobalTheory.BSP.adI Q) fun n => ?_)
  have hq : _root_.GlobalTheory.BSP.qmap c' n = _root_.GlobalTheory.BSP.qmap c n := by
    refine ringHom_eq_of_isPushout_of_comp_eq (H.po n) ?_ ?_
    · rw [← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hc'.1, hcomm.1]
    · rw [← _root_.GlobalTheory.BSP.qmap_comp, ← _root_.GlobalTheory.BSP.qmap_comp, hc'.2, hcomm.2]
  have hx := RingHom.congr_fun hq (Ideal.Quotient.mk _ x)
  simpa only [_root_.GlobalTheory.BSP.qmap_mk] using hx

end GlobalTheory.BSP.PoUniv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismPushoutModAdicPowUniversalStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismPushoutModAdicPow_universal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C B' C' : Obj l R) (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C'), IsPO h k k' h' → ∀ (Q : Obj l R) (a : Hom C Q) (b : Hom B' Q), a.comp h = b.comp k → ∃! c : Hom C' Q, c.comp k' = a ∧ c.comp h' = b := by
  first | exact @GlobalTheory.BSP.PoUniv.isPO_univ | exact GlobalTheory.BSP.PoUniv.isPO_univ | (intros; apply GlobalTheory.BSP.PoUniv.isPO_univ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemDecIsFrob
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem exists_mem_Dec_isFrob : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.E)) (A : ValuationSubring D.nd.Om), IsPlaceOver (F := D.host.E) A v → ∃ σ : Gen.GE D.nd, σ ∈ Dec (F := D.host.E) A ∧ IsFrob (F := D.host.E) A (normV v) σ := by
  intro D v A hA
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob (F := D.host.E) hA
  exact ⟨σ, hσ.1, hσ⟩

end GlobalTheory.TripleGal
end
