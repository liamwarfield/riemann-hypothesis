module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlTieOfInertCore
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpNegOneLtOne
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocIdFr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FrobOrderSpec
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ICIntCp
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompletionEquiv
open NumberField IsDedekindDomain IsLocalRing Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.GO.PlWitt
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaceOrbit

theorem exists_hom_of_dense {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    [IsAdicComplete J B] (f : R →+* A) (g : R →+* B) (hs : ∀ (k : ℕ) (a : A), ∃ x, a - f x ∈ I ^ k)
    (hk : ∀ (k : ℕ) x, f x ∈ I ^ k → g x ∈ J ^ k) :
    ∃ h : A →+* B, ∀ (k : ℕ) a x, a - f x ∈ I ^ k → h a - g x ∈ J ^ k := by
  have hsur : ∀ k : ℕ, Function.Surjective ((Ideal.Quotient.mk (I ^ k)).comp f) := fun k y => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hs k a
    exact ⟨x, (Ideal.Quotient.eq.2 hx).symm⟩
  let u : (k : ℕ) → A ⧸ I ^ k →+* B ⧸ J ^ k := fun k =>
    RingHom.liftOfSurjective _ (hsur k) ⟨(Ideal.Quotient.mk (J ^ k)).comp g, fun x hx =>
      Ideal.Quotient.eq_zero_iff_mem.2 (hk k x (Ideal.Quotient.eq_zero_iff_mem.1 hx))⟩
  let φ : (k : ℕ) → A →+* B ⧸ J ^ k := fun k => (u k).comp (Ideal.Quotient.mk _)
  have hφ : ∀ k a x, a - f x ∈ I ^ k → φ k a = Ideal.Quotient.mk _ (g x) := fun k a x h => by
    change u k (Ideal.Quotient.mk _ a) = _
    rw [Ideal.Quotient.eq.2 h]
    exact RingHom.liftOfRightInverse_comp_apply ((Ideal.Quotient.mk (I ^ k)).comp f) _ _ _ x
  have hc : ∀ {m n : ℕ} (h : m ≤ n), (Ideal.Quotient.factorPow J h).comp (φ n) = φ m := by
    intro m n h
    refine RingHom.ext fun a => ?_
    obtain ⟨x, hx⟩ := hs n a
    rw [RingHom.comp_apply, hφ n a x hx, hφ m a x (Ideal.pow_le_pow_right h hx)]
    rfl
  refine ⟨IsAdicComplete.liftRingHom J φ hc, fun k a x h => ?_⟩
  rw [← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom, hφ k a x h]

theorem eq_of_forall_pow {A : Type} [CommRing A] (I : Ideal A) [IsHausdorff I A] {a b : A}
    (h : ∀ k : ℕ, a - b ∈ I ^ k) : a = b :=
  sub_eq_zero.1 (IsHausdorff.haus' (I := I) _ fun k => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact h k)

theorem exists_equiv_of_dense {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    [IsAdicComplete I A] [IsAdicComplete J B] (f : R →+* A) (g : R →+* B)
    (hs : ∀ (k : ℕ) (a : A), ∃ x, a - f x ∈ I ^ k) (hs' : ∀ (k : ℕ) (b : B), ∃ x, b - g x ∈ J ^ k)
    (hk : ∀ (k : ℕ) x, f x ∈ I ^ k ↔ g x ∈ J ^ k) : ∃ e : A ≃+* B, ∀ x, e (f x) = g x := by
  obtain ⟨h, hh⟩ := exists_hom_of_dense I J f g hs fun k x => (hk k x).1
  obtain ⟨h', hh'⟩ := exists_hom_of_dense J I g f hs' fun k x => (hk k x).2
  refine ⟨RingEquiv.ofRingHom h h' (RingHom.ext fun b => eq_of_forall_pow J fun k => ?_)
    (RingHom.ext fun a => eq_of_forall_pow I fun k => ?_), fun x => eq_of_forall_pow J fun k => ?_⟩
  · obtain ⟨x, hx⟩ := hs' k b
    simpa using sub_mem (hh k _ x (hh' k b x hx)) hx
  · obtain ⟨x, hx⟩ := hs k a
    simpa using sub_mem (hh' k _ x (hh k a x hx)) hx
  · exact hh k _ x (by simp)

variable {F : Type} [Field F] [NumberField F] {p n : ℕ} [hp : Fact p.Prime]

theorem exists_completion_equiv {v : HeightOneSpectrum (𝓞 F)} {i : F →+* Qn p n} (h : Good v i) :
    ∃ e : Qn p n ≃+* v.adicCompletion F, (∀ x : F, e (i x) = algebraMap F _ x) ∧
      ∀ y, y ∈ Set.range (algebraMap (Wn p n) (Qn p n)) ↔ e y ∈ v.adicCompletionIntegers F := by
  have hint := h.intAt
  have hd := h.dense
  obtain ⟨g, hg, -, hk⟩ := h
  have hinj := IsFractionRing.injective (Wn p n) (Qn p n)
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by rw [hk, map_natCast, cc_eq_zero]
  have hval : ∀ x : 𝓞 F, Valued.v ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) x : v.adicCompletionIntegers F) :
      v.adicCompletion F) = v.valuation F (x : F) := fun x => by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  have hpF : ∀ k : ℕ, ((p : F) ^ k) ≠ 0 := fun k => pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hvp : ∀ k : ℕ, Valued.v ((((p : v.adicCompletionIntegers F) ^ k : v.adicCompletionIntegers F)) :
      v.adicCompletion F) = v.valuation F ((p : F) ^ k) := fun k => by
    simpa using hval ((p : 𝓞 F) ^ k)
  have hvp0 : ∀ k : ℕ, v.valuation F ((p : F) ^ k) ≠ 0 := fun k => by simpa using hpF k
  haveI : IsAdicComplete (Ideal.span {(p : v.adicCompletionIntegers F)}) (v.adicCompletionIntegers F) :=
    (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).1 _ (by
      have := hval p
      rw [map_natCast] at this
      rw [this]
      exact (v.valuation_lt_one_iff_mem (K := F) _).2 hpv)
  obtain ⟨e, he⟩ := exists_equiv_of_dense (Ideal.span {(p : Wn p n)}) (Ideal.span {(p : v.adicCompletionIntegers F)})
    g (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
    (fun k a => by
      obtain ⟨x, z, hx⟩ := hd a k
      rw [hg] at hx
      exact ⟨x, by rw [hinj hx, Ideal.span_singleton_pow, Ideal.mem_span_singleton]; exact ⟨-z, by ring⟩⟩)
    (fun k b => by
      obtain ⟨x, hx⟩ := Idele.exists_valued_sub_le v (a := (b : v.adicCompletion F)) b.2
        (-WithZero.log (v.valuation F ((p : F) ^ k))).toNat
      refine ⟨x, ?_⟩
      rw [Ideal.span_singleton_pow, GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v (by rw [hvp]; exact hvp0 k), hvp]
      refine le_trans hx ?_
      conv_rhs => rw [← WithZero.exp_log (hvp0 k)]
      rw [WithZero.exp_le_exp]
      omega)
    (fun k x => by
      rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow,
        GlobalTheory.CNorm.mem_span_singleton_adicCompletionIntegers v (by rw [hvp]; exact hvp0 k), hvp, hval,
        ← div_le_one₀ (zero_lt_iff.2 (hvp0 k)), ← map_div₀, ← GlobalTheory.UnramCompletion.intAt_iff, hint,
        Ideal.mem_span_singleton']
      refine exists_congr fun y => ?_
      rw [map_div₀, eq_div_iff ((_root_.map_ne_zero i).2 (hpF k)), hg, ← hinj.eq_iff]
      simp)
  refine ⟨IsFractionRing.ringEquivOfRingEquiv e, fun x => ?_, fun y => ⟨?_, fun hy => ?_⟩⟩
  · have : ((IsFractionRing.ringEquivOfRingEquiv (K := Qn p n) (L := v.adicCompletion F) e).toRingHom.comp i) =
        algebraMap F (v.adicCompletion F) :=
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (RingHom.ext fun x => by
        change IsFractionRing.ringEquivOfRingEquiv e (i (x : F)) = _
        rw [hg, IsFractionRing.ringEquivOfRingEquiv_algebraMap, he]
        rfl)
    exact RingHom.congr_fun this x
  · rintro ⟨w, rfl⟩
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact (e w).2
  · refine ⟨e.symm ⟨_, hy⟩, (IsFractionRing.ringEquivOfRingEquiv (K := Qn p n) (L := v.adicCompletion F) e).injective ?_⟩
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, e.apply_symm_apply]
    rfl

theorem exists_first_frame {E : Type} [Field E] [NumberField E] [Algebra F E] {k : ℕ} (w : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F)
    (halg : ∀ a : w.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a))
    (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hsp : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) :
    ∃ fr : GL (Fin k) (w.adicCompletion F), ∀ t : Fin k → w.adicCompletion F,
      (∃ x ∈ Formalism.L2.Herm.locL w Λ, ∀ a, (φ (x a)).1 = t a) ↔
        ∀ a, ((fr⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)).mulVec t a ∈
          w.adicCompletionIntegers F := by
  obtain ⟨B, -, -, hB, -⟩ := GlobalTheory.DualFrame.exists_dual_frames F E (AlgHom.id F E) k 1 (by simp) Λ hfin hsp w
  let π : E ⊗[F] w.adicCompletion F →+* w.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom
  have hinv : (((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)) : Matrix (Fin k) (Fin k) (w.adicCompletion F)) =
      ((B⁻¹ : GL (Fin k) _) : Matrix (Fin k) (Fin k) _).map π := by
    rw [← map_inv]; rfl
  refine ⟨bc π B, fun t => ⟨?_, fun hu => ?_⟩⟩
  · rintro ⟨x, hx, hxt⟩ a
    have ht : t = π ∘ x := funext fun a => (hxt a).symm
    rw [ht, hinv, ← RingHom.map_mulVec]
    refine Formalism.MainNotions.Gaps.Loc.fst_int w φ halg _ ((hB _).1 ?_ a)
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    exact hx
  · refine ⟨_, (hB fun a => (1 : E) ⊗ₜ[F] (((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)).1.mulVec t a)).2
      fun a => Formalism.MainNotions.Gaps.LG.sc_right_mem w _ (hu a), fun a => ?_⟩
    refine (RingHom.map_mulVec π _ _ a).trans ?_
    have : (π ∘ fun a => (1 : E) ⊗ₜ[F] (((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)).1.mulVec t a)) =
        ((bc π B)⁻¹ : GL (Fin k) (w.adicCompletion F)).1.mulVec t := funext fun a => congrArg Prod.fst (halg _)
    rw [this]
    change ((bc π B).1 *ᵥ _) a = _
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec]

end GlobalTheory.PlaceOrbit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamV
open Formalism.BasicNotions

namespace GlobalTheory.PadicPlaceExt

theorem exists_lam {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [NumberField L] (e : L →+* ℂ) (φ : L →+* ℂ_[p]) :
    ∃ lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p], ∀ z : L, φ z = lamV lam (e z) := by
  have hmem : ∀ z : L, e z ∈ algebraicClosure ℚ ℂ := fun z =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom e.toRatAlgHom)
  let e' : L →+* algebraicClosure ℚ ℂ := e.codRestrict (algebraicClosure ℚ ℂ) hmem
  let : Algebra L (algebraicClosure ℚ ℂ) := e'.toAlgebra
  let : Algebra L ℂ_[p] := φ.toAlgebra
  have : IsScalarTower ℚ L (algebraicClosure ℚ ℂ) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic L (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  let f : algebraicClosure ℚ ℂ →ₐ[L] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨f.toRingHom, fun z => ?_⟩
  rw [lamV, dite_eq_left (hmem z)]
  exact (f.commutes z).symm

end GlobalTheory.PadicPlaceExt
end

open NumberField IsDedekindDomain IsLocalRing Formalism.UG Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.G GlobalTheory.GO.PlWitt
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PlaceOrbit

section General

variable {E : Type} [Field E] [NumberField E] {p n : ℕ} [hp : Fact p.Prime]

theorem exists_aut [IsGalois ℚ E] {K : Type} [Field K] (a b : E →+* K) : ∃ τ : E ≃ₐ[ℚ] E, ∀ x, b x = a (τ x) := by
  have : CharZero K := charZero_of_injective_ringHom a.injective
  let u : (E ≃ₐ[ℚ] E) → (E →ₐ[ℚ] K) := fun τ => a.toRatAlgHom.comp τ
  have hu : Function.Injective u := fun s t h => AlgEquiv.ext fun x => a.injective (AlgHom.congr_fun h x)
  obtain ⟨τ, hτ⟩ := (hu.bijective_of_nat_card_le (by
    rw [IsGalois.card_aut_eq_finrank]; exact card_algHom_le_finrank ℚ E K)).2 b.toRatAlgHom
  exact ⟨τ, fun x => (AlgHom.congr_fun hτ x).symm⟩

theorem unramified_of_inertia [IsGalois ℚ E] (P : Ideal (𝓞 E)) [P.IsPrime]
    (h : ∀ σ : E ≃ₐ[ℚ] E, (∀ x : 𝓞 E, σ • x - x ∈ P) → σ = 1) : Algebra.IsUnramifiedAt ℤ P := by
  have hpr : (P.under ℤ).IsPrime := Ideal.IsPrime.under _ P
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (P.under ℤ) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P (E ≃ₐ[ℚ] E)] at hcard
  have h1 : Nat.card (P.inertia (E ≃ₐ[ℚ] E)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, one_mem _⟩⟩⟩
    rw [h x.1 (AddSubgroup.mem_inertia.mp x.2), h y.1 (AddSubgroup.mem_inertia.mp y.2)]
  rw [h1] at hcard
  exact Ideal.ramificationIdx_eq_one_iff.mp hcard.symm

theorem liesOver_of_mem (Q : HeightOneSpectrum (𝓞 E)) (hQ : (p : 𝓞 E) ∈ Q.asIdeal) :
    Q.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨by
  have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  refine this.eq_of_le (Ideal.comap_ne_top _ Q.isPrime.ne_top) ?_
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact hQ⟩

theorem mem_max (y : Wn p n) : y ∈ maximalIdeal (Wn p n) ↔ WittVector.constantCoeff y = 0 := by
  rw [cc_eq_zero, (WittVector.irreducible p).maximalIdeal_eq, Ideal.mem_span_singleton]

theorem p_mem : (p : Wn p n) ∈ maximalIdeal (Wn p n) := by rw [mem_max, cc_eq_zero]

def plc (i : E →+* Qn p n) : HeightOneSpectrum (𝓞 E) := (exists_ov (O := Wn p n) p_mem i).choose

theorem p_mem_plc (i : E →+* Qn p n) : (p : 𝓞 E) ∈ (plc i).asIdeal := (exists_ov (O := Wn p n) p_mem i).choose_spec.1

theorem ov_plc (i : E →+* Qn p n) : Ov (Wn p n) i (plc i) := (exists_ov (O := Wn p n) p_mem i).choose_spec.2

theorem mem_plc (i : E →+* Qn p n) (x : 𝓞 E) :
    x ∈ (plc i).asIdeal ↔ ∃ y ∈ maximalIdeal (Wn p n), algebraMap _ (Qn p n) y = i x := ov_plc i x

theorem good_plc {i : E →+* Qn p n}
    (h : ∀ y : Wn p n, ∃ x : 𝓞 E, ∃ z ∈ maximalIdeal (Wn p n), algebraMap _ (Qn p n) (y + z) = i x) : Good (plc i) i := by
  obtain ⟨g, hg⟩ := exists_intHom (O := Wn p n) i
  refine ⟨g, fun x => (hg x).symm, fun a => ?_, fun x => ((ov_iff hg).1 (ov_plc i) x).trans (mem_max _)⟩
  obtain ⟨y, rfl⟩ := WittVector.constantCoeff_surjective p a
  obtain ⟨x, z, hz, e⟩ := h y
  refine ⟨x, ?_⟩
  simp only
  rw [← IsFractionRing.injective (Wn p n) (Qn p n) (e.trans (hg x).symm), map_add (f := _), (mem_max z).1 hz, add_zero]

omit [NumberField E] in
theorem good_approx {Q : HeightOneSpectrum (𝓞 E)} {i : E →+* Qn p n} (h : Good Q i) (y : Wn p n) :
    ∃ x : 𝓞 E, ∃ z ∈ maximalIdeal (Wn p n), algebraMap _ (Qn p n) (y + z) = i x := by
  obtain ⟨x, z, e⟩ := h.dense y 1
  exact ⟨x, _, Ideal.mul_mem_right _ _ (by rw [pow_one]; exact p_mem), e.symm⟩

theorem plc_eq_of_pow {Q : HeightOneSpectrum (𝓞 E)} {i j : E →+* Qn p n} (h : Good Q i) (s : ℕ)
    (e : ∀ x, j x = (Fr p n ^ s) (i x)) : plc j = Q :=
  (ov_plc j).eq (h.ov (ι := RingHom.id _) (j := RingHom.id _) p_mem (fun _ => rfl) s e)

theorem good_aut {Q : HeightOneSpectrum (𝓞 E)} {i j : E →+* Qn p n} (h : Good Q i) (τ : E ≃ₐ[ℚ] E)
    (e : ∀ x, j x = i (τ x)) : Good (plc j) j :=
  good_plc fun y => by
    obtain ⟨x, z, hz, e'⟩ := good_approx h y
    refine ⟨τ⁻¹ • x, z, hz, ?_⟩
    rw [e', e]
    exact congrArg i (τ.apply_symm_apply _).symm

theorem isArithFrobAt_of {Q : HeightOneSpectrum (𝓞 E)} {i : E →+* Qn p n} (h : Good Q i) (hQ : (p : 𝓞 E) ∈ Q.asIdeal)
    (τ : E ≃ₐ[ℚ] E) (e : ∀ x, Fr p n (i x) = i (τ x)) : IsArithFrobAt ℤ τ Q.asIdeal := by
  obtain ⟨g, hg, -, hk⟩ := h
  intro x
  have hc : Nat.card (ℤ ⧸ Q.asIdeal.under ℤ) = p := by
    rw [← (liesOver_of_mem Q hQ).over, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  obtain ⟨a, ha, ha'⟩ := fr_pow 1 (g x)
  rw [pow_one] at ha ha'
  have h1 : a = g (τ • x) := IsFractionRing.injective (Wn p n) (Qn p n) (by rw [← ha, ← hg, ← hg, e]; rfl)
  rw [hc, hk, map_sub, map_sub, map_pow, map_pow, ← ha', h1]
  exact sub_self _

end General

section Host

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {R : Ranks} {H : Host R} {p n : ℕ} [hp : Fact p.Prime] {h : R.MA}

theorem sigmaOf_mul (g g' : R.GG) (x : H.E) : H.sigmaOf (g * g') x = H.sigmaOf g (H.sigmaOf g' x) := by
  simp only [Host.sigmaOf, map_mul]
  rfl

theorem sigmaOf_inj : Function.Injective H.sigmaOf := (H.gal).symm.injective

theorem sigmaOf_surj : Function.Surjective H.sigmaOf := (H.gal).symm.surjective

theorem cc_mul_cc (e : Formalism.HC.Frame) : e.cc * e.cc = 1 := e.cc_mul_cc

theorem cc_pow (e : Formalism.HC.Frame) (m : ℕ) : e.cc ^ m = 1 ∨ e.cc ^ m = e.cc := by
  induction m with
  | zero => simp
  | succ m ih => rcases ih with h | h <;> simp [pow_succ, h, cc_mul_cc]

theorem cc_notMem (e : Formalism.HC.Frame) : e.cc ∉ e.Psi := e.cc_notMem_Psi

theorem frob_eq_mul (h : R.MA) : ((c0, h) : R.GG) = (zPsi R.toFrame h : R.GG) * R.cc := by
  rw [zPsi_eq, mul_assoc, cc_mul_cc, mul_one]


variable (H) in
def tw (i : H.E →+* Qn p n) (g : R.GG) : H.E →+* Qn p n := i.comp (H.sigmaOf g : H.E →+* H.E)

theorem tw_apply (i : H.E →+* Qn p n) (g : R.GG) (x : H.E) : tw H i g x = i (H.sigmaOf g x) := rfl


variable (H) in
def twF (i : H.E →+* Qn p n) (g : R.GG) : H.F →+* Qn p n := (tw H i g).comp (algebraMap H.F H.E)

theorem twF_cc_pow (i : H.E →+* Qn p n) (g : R.GG) (m : ℕ) : twF H i (g * R.cc ^ m) = twF H i g := by
  rcases cc_pow R.toFrame m with e | e <;> rw [e]
  · rw [mul_one]
  · refine RingHom.ext fun x => ?_
    change i (H.sigmaOf (g * R.cc) x) = i (H.sigmaOf g x)
    rw [sigmaOf_mul]
    exact congrArg (fun y => i (H.sigmaOf g y)) ((H.conjE_mem_hostF_iff x.1).1 x.2)

theorem mem_plc_twF (i : H.E →+* Qn p n) (g : R.GG) (x : 𝓞 H.F) :
    x ∈ (plc (twF H i g)).asIdeal ↔ algebraMap (𝓞 H.F) (𝓞 H.E) x ∈ (plc (tw H i g)).asIdeal := by
  rw [mem_plc, mem_plc]
  rfl

theorem mem_plc_tw_cc (i : H.E →+* Qn p n) (g : R.GG) (x : 𝓞 H.E) :
    x ∈ (plc (tw H i (g * R.cc))).asIdeal ↔ H.conj • x ∈ (plc (tw H i g)).asIdeal := by
  rw [mem_plc, mem_plc, tw_apply, sigmaOf_mul]
  rfl

theorem conj_conj (x : 𝓞 H.E) : H.conj • H.conj • x = x := by
  have : H.conj * H.conj = 1 := by
    unfold Formalism.HC.HostRaw.conj
    rw [← map_mul, cc_mul_cc, map_one]
  rw [smul_smul, this, one_smul]

theorem exists_real (x : 𝓞 H.E) (hx : H.conj • x = x) : ∃ z : 𝓞 H.F, algebraMap (𝓞 H.F) (𝓞 H.E) z = x := by
  have hm : (x : H.E) ∈ H.F := (H.conjE_mem_hostF_iff _).2 (congrArg (fun y : 𝓞 H.E => (y : H.E)) hx)
  exact ⟨⟨⟨x, hm⟩, (isIntegral_algHom_iff (algebraMap H.F H.E).toIntAlgHom (algebraMap H.F H.E).injective).1
    x.isIntegral_coe⟩, rfl⟩

variable (hun : ∀ Q : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ Q.asIdeal → Algebra.IsUnramifiedAt ℤ Q.asIdeal)
  (hfr : ∀ Q : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ Q.asIdeal → ∀ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ Q.asIdeal →
    σ = H.sigmaOf (c0, h))
  (h2 : 2 ≤ orderOf h) (he : Even (orderOf h))

omit hp in
include he in
theorem orderOf_frob : orderOf ((c0, h) : R.GG) = orderOf h := by
  have : orderOf c0 = 2 := orderOf_eq_prime (by decide) (by decide)
  rw [Prod.orderOf_mk, this]
  exact Nat.lcm_eq_right he.two_dvd

theorem mem_of_good {E : Type} [Field E] {Q : HeightOneSpectrum (𝓞 E)} {i : E →+* Qn p n} (hi : Good Q i) :
    (p : 𝓞 E) ∈ Q.asIdeal := by
  obtain ⟨g, -, -, hk⟩ := hi
  rw [hk, map_natCast, cc_eq_zero]

include hfr in
theorem fr_apply {Q : HeightOneSpectrum (𝓞 H.E)} {i : H.E →+* Qn p n} (hi : Good Q i) (x : H.E) :
    Fr p n (i x) = i (H.sigmaOf (c0, h) x) := by
  have := H.hostE_isGalois
  obtain ⟨τ, hτ⟩ := exists_aut i ((Fr p n).toRingHom.comp i)
  rw [← hfr Q (mem_of_good hi) τ (isArithFrobAt_of hi (mem_of_good hi) τ hτ)]
  exact hτ x

include hfr in
theorem fr_pow_apply {Q : HeightOneSpectrum (𝓞 H.E)} {i : H.E →+* Qn p n} (hi : Good Q i) (s : ℕ) (x : H.E) :
    (Fr p n ^ s) (i x) = i (H.sigmaOf ((c0, h) ^ s) x) := by
  induction s generalizing x with
  | zero => simp [Host.sigmaOf]
  | succ s ih => rw [pow_succ, pow_succ, RingAut.mul_apply, fr_apply hfr hi, ih, sigmaOf_mul]


include hfr h2 he in
theorem degree_eq {Q : HeightOneSpectrum (𝓞 H.E)} {i : H.E →+* Qn p n} (hi : Good Q i) (hn : n ≠ 0) : n = orderOf h := by
  have h1 : ((c0, h) : R.GG) ^ n = 1 := sigmaOf_inj (H := H) (AlgEquiv.ext fun x => i.injective (by
    rw [← fr_pow_apply hfr hi, GlobalTheory.SqrtUnif.fractionRing_frobenius_pow p hn]
    simp [Host.sigmaOf]))
  have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (orderOf_dvd_of_pow_eq_one h1)
  rw [orderOf_frob he] at h3
  refine (h3.eq_or_lt.resolve_right fun hlt => ?_).symm
  have := hi.pow_inj hn hlt (Nat.pos_of_ne_zero hn) fun x => by
    rw [fr_pow_apply hfr hi, fr_pow_apply hfr hi, ← orderOf_frob he, pow_orderOf_eq_one, pow_zero]
  omega

variable {Q₀ : HeightOneSpectrum (𝓞 H.E)} {i : H.E →+* Qn p n} (hi : Good Q₀ i) (hn : n ≠ 0)

include hi in
theorem good_tw (g : R.GG) : Good (plc (tw H i g)) (tw H i g) := good_aut hi _ fun _ => rfl


include hun hfr hi hn in
theorem exists_pow_of_plc_eq {g g' : R.GG} (e : plc (tw H i g') = plc (tw H i g)) : ∃ s : ℕ, g' = g * (c0, h) ^ s := by
  have := hun _ (p_mem_plc (tw H i g))
  obtain ⟨s, -, hs⟩ := (good_tw hi g).exists_pow (ι := RingHom.id _) (j := RingHom.id _) hn p_mem (fun _ => rfl)
    (e ▸ ov_plc (tw H i g'))
  refine ⟨s, sigmaOf_inj (H := H) (AlgEquiv.ext fun x => i.injective ?_)⟩
  rw [sigmaOf_mul]
  exact (hs x).trans (fr_pow_apply hfr (good_tw hi g) s x)


include hun hfr he hi hn in
theorem plc_ne_conj (g : R.GG) : plc (tw H i (g * R.cc)) ≠ plc (tw H i g) := fun e => by
  obtain ⟨s, hs⟩ := exists_pow_of_plc_eq hun hfr hi hn e
  have h1 := (R.toFrame.cc_mem_zpowers_iff (c0, h)).1 (by
    rw [mul_left_cancel hs]; exact Subgroup.npow_mem_zpowers _ s)
  exact Nat.not_even_iff_odd.2 h1.2 he


include hun hfr he hi hn in
theorem good_twF (g : R.GG) : Good (plc (twF H i g)) (twF H i g) :=
  good_plc fun y => by
    obtain ⟨x, z, hz, e⟩ := good_approx (good_tw hi g) y
    have hco : (plc (tw H i g)).asIdeal ⊔ (plc (tw H i (g * R.cc))).asIdeal = ⊤ :=
      (plc _).isMaximal.coprime_of_ne (plc _).isMaximal fun e =>
        plc_ne_conj hun hfr he hi hn g (HeightOneSpectrum.ext e.symm)
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hco ▸ Submodule.mem_top : x ∈ _)
    obtain ⟨t, ht⟩ := exists_real (b + H.conj • b) (by rw [smul_add, conj_conj, add_comm])
    obtain ⟨u, hu, eu⟩ := (mem_plc _ _).1 (sub_mem ((mem_plc_tw_cc i g b).1 hb) ha)
    refine ⟨t, z + u, add_mem hz hu, ?_⟩
    rw [← add_assoc, map_add (f := _), e, eu, ← map_add (f := _)]
    have : x + (H.conj • b - a) = algebraMap (𝓞 H.F) (𝓞 H.E) t := by rw [ht, ← hab]; ring
    exact congrArg (fun y : 𝓞 H.E => tw H i g (y : H.E)) this

include hun hfr hi hn in
theorem place_injective : Function.Injective fun v : Fin (nOrb (zPsi R.toFrame h)) =>
    plc (twF H i (orbRep (zPsi R.toFrame h) v : R.Psi)) := by
  have key : ∀ g g' : R.GG, plc (twF H i g') = plc (twF H i g) → ∃ s m : ℕ, g' = g * (zPsi R.toFrame h : R.GG) ^ s * R.cc ^ m := by
    intro g g' e
    have hsub : ((plc (tw H i g')).asIdeal : Set (𝓞 H.E)) ⊆
        (plc (tw H i g)).asIdeal ∪ (plc (tw H i (g * R.cc))).asIdeal := fun y hy => by
      obtain ⟨t, ht⟩ := exists_real (y * H.conj • y) (by rw [smul_mul', conj_conj, mul_comm])
      have h1 : t ∈ (plc (twF H i g')).asIdeal := by
        rw [mem_plc_twF, ht]; exact Ideal.mul_mem_right _ _ hy
      rw [e, mem_plc_twF, ht] at h1
      exact ((plc _).isPrime.mem_or_mem h1).imp id (mem_plc_tw_cc i g y).2
    rcases Ideal.subset_union.1 hsub with hle | hle
    · obtain ⟨s, hs⟩ := exists_pow_of_plc_eq hun hfr hi hn
        (HeightOneSpectrum.ext ((plc _).isMaximal.eq_of_le (plc _).isPrime.ne_top hle))
      exact ⟨s, s, by rw [hs, frob_eq_mul, mul_pow, mul_assoc]⟩
    · obtain ⟨s, hs⟩ := exists_pow_of_plc_eq hun hfr hi hn
        (HeightOneSpectrum.ext ((plc _).isMaximal.eq_of_le (plc _).isPrime.ne_top hle))
      exact ⟨s, s + 1, by rw [hs, frob_eq_mul, mul_pow, pow_succ (R.cc)]; ac_rfl⟩
  intro v v' e
  obtain ⟨s, m, hs⟩ := key _ _ e.symm
  have h1 : R.cc ^ m = 1 := (cc_pow R.toFrame m).resolve_right fun e' => cc_notMem R.toFrame (by
    rw [e'] at hs
    rw [← inv_mul_eq_of_eq_mul hs]
    exact mul_mem (inv_mem (mul_mem (orbRep _ v).2 (pow_mem (zPsi R.toFrame h).2 s))) (orbRep _ v').2)
  rw [h1, mul_one] at hs
  have h3 : orbRep (zPsi R.toFrame h) v' = orbRep (zPsi R.toFrame h) v * zPsi R.toFrame h ^ s := Subtype.ext hs
  apply (orbEquiv (zPsi R.toFrame h)).injective
  rw [← orbRep_mk, ← orbRep_mk, h3, QuotientGroup.mk_mul_of_mem _ (Subgroup.npow_mem_zpowers _ s)]

include hun hfr h2 he hi hn in
theorem place_surjective (w : HeightOneSpectrum (𝓞 H.F)) (hw : (p : 𝓞 H.F) ∈ w.asIdeal) :
    ∃ v : Fin (nOrb (zPsi R.toFrame h)), plc (twF H i (orbRep (zPsi R.toFrame h) v : R.Psi)) = w := by
  have := H.hostE_isGalois
  have := w.isPrime
  obtain ⟨⟨P, hP, hPl⟩⟩ : Nonempty (w.asIdeal.primesOver (𝓞 H.E)) := inferInstance
  have hpP : (p : 𝓞 H.E) ∈ P := by
    rw [hPl.over, Ideal.mem_comap, map_natCast] at hw
    exact hw
  let Q : HeightOneSpectrum (𝓞 H.E) := ⟨P, hP, fun e => by
    rw [e, Ideal.mem_bot] at hpP
    exact hp.out.ne_zero (Nat.cast_eq_zero.1 hpP)⟩
  have := hun Q hpP
  obtain ⟨m, j, hm, hj⟩ := exists_good Q hpP
  obtain rfl : m = n := (degree_eq hfr h2 he hj hm).trans (degree_eq hfr h2 he hi hn).symm
  obtain ⟨τ, hτ⟩ := exists_aut i j
  obtain ⟨g, rfl⟩ := sigmaOf_surj τ
  have hQ : plc (tw H i g) = Q := plc_eq_of_pow hj 0 fun x => (hτ x).symm
  have hwg : plc (twF H i g) = w := HeightOneSpectrum.ext (Ideal.ext fun x => by
    rw [mem_plc_twF, hQ, hPl.over]; rfl)
  obtain ⟨g₀, t, rfl⟩ : ∃ (g₀ : R.Psi) (t : ℕ), g = g₀ * R.cc ^ t := by
    by_cases hg : g ∈ R.Psi
    · exact ⟨⟨g, hg⟩, 0, by simp⟩
    · exact ⟨⟨g * R.cc, (Subgroup.mul_mem_iff_of_index_two R.toFrame.index_Psi).2 (iff_of_false hg (cc_notMem _))⟩, 1,
        by rw [pow_one, mul_assoc, cc_mul_cc, mul_one]⟩
  obtain ⟨⟨v, s⟩, rfl⟩ := (posG (zPsi R.toFrame h)).surjective g₀
  refine ⟨v, ?_⟩
  rw [← hwg, twF_cc_pow, ← twF_cc_pow i ((posG (zPsi R.toFrame h) ⟨v, s⟩ : R.Psi) : R.GG) s.val, posG_apply, Subgroup.coe_mul, Subgroup.coe_pow, mul_assoc, ← mul_pow,
    ← frob_eq_mul]
  refine (plc_eq_of_pow (good_twF hun hfr he hi hn _) s fun x => ?_).symm
  refine Eq.trans ?_ (fr_pow_apply hfr (good_tw hi _) s _).symm
  exact congrArg i (sigmaOf_mul _ _ _)

end Host

section Assembly

theorem exists_locId_of_completions {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} (L : ColLevel R F E sp gp C A clsLat) {p nV : ℕ} {W Qq : Type}
    [CommRing W] [Field Qq] [Algebra W Qq] (b : E) (hb0 : b ≠ 0) (hb : star b = -b)
    (pl : Fin nV ≃ {v : HeightOneSpectrum (𝓞 F) // ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}) (j : Fin nV → (E →+* Qq))
    (hE : ∀ v, ∃ e : Qq ≃+* (pl v).1.adicCompletion F, (∀ x : F, e (j v (algebraMap F E x)) = algebraMap F _ x) ∧
      ∀ y, y ∈ Set.range (algebraMap W Qq) ↔ e y ∈ (pl v).1.adicCompletionIntegers F) :
    ∃ I : LocId L p nV W Qq, I.pl = pl ∧ ∀ v x, I.iw v x = j v x := by
  choose eQ heQ heW using hE
  have hS : ∀ (w : HeightOneSpectrum (𝓞 F)) (_ : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal),
      ∃ φ : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F,
        (∀ x, φ (sigR sp.cm.sig (w.adicCompletion F) x) = swapR _ (φ x)) ∧
        (∀ a : w.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
        ∀ v, (pl v).1 = w → ∀ x : E, HEq (φ (inclE (F := F) (w.adicCompletion F) x)).1 (eQ v (j v x)) := by
    intro w hw
    obtain ⟨v, hv⟩ := pl.surjective ⟨w, hw⟩
    obtain rfl : (pl v).1 = w := congrArg Subtype.val hv
    obtain ⟨φ, h1, h3, h4⟩ := Formalism.MainNotions.Gaps.Loc.exists_spl sp.cm.sig (fun x => star_star x) sp.cm.deg2 b hb0 hb
      ({ (eQ v).toRingHom.comp (j v) with commutes' := heQ v } : E →ₐ[F] (pl v).1.adicCompletion F)
    refine ⟨φ, h1, h3, fun v' hv' x => ?_⟩
    obtain rfl : v' = v := pl.injective (Subtype.ext hv')
    exact heq_of_eq (h4 x)
  choose spl hs1 hs2 hs3 using hS
  choose fr hfr using fun w hw => exists_first_frame w (spl w hw) (hs2 w hw) L.Lb L.Lb_fin L.Lb_span
  exact ⟨⟨pl, eQ, heW, spl, hs1, hs2, fr, hfr⟩, rfl, fun v x =>
    (eQ v).symm_apply_eq.2 (eq_of_heq (hs3 _ (pl v).2 v rfl x))⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_locId_host {R : Ranks} {H : Host R} {p : ℕ} [hp : Fact p.Prime] {h : R.MA}
    (hun : ∀ Q : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ Q.asIdeal → Algebra.IsUnramifiedAt ℤ Q.asIdeal)
    (hfr : ∀ Q : HeightOneSpectrum (𝓞 H.E), (p : 𝓞 H.E) ∈ Q.asIdeal → ∀ σ : H.E ≃ₐ[ℚ] H.E, IsArithFrobAt ℤ σ Q.asIdeal →
      σ = H.sigmaOf (c0, h))
    (h2 : 2 ≤ orderOf h) (he : Even (orderOf h)) {n : ℕ} (hn : n = orderOf h)
    {sp : Spaces R H.F H.E} {gp : Fin 2 → ℕ} {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc}
    {A : ColumnsAtT R C} {clsLat : ∀ i, C.cls i → Submodule (𝓞 H.E) (sp.X i).V}
    (L : ColLevel R H.F H.E sp gp C A clsLat) (κ : QQ p n →+* ℂ_[p]) (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p]) :
    ∃ I : LocId L p (nOrb (zPsi R.toFrame h)) (WQ p n) (QQ p n),
      (∀ v x, κ (I.iw v x) = lamV lam (H.emb ((orbRep (zPsi R.toFrame h) v : R.Psi) : R.GG) x)) ∧
      ∀ v x, sig p n (I.iw v x) = I.iw v (H.sigmaOf ((c0, h) : R.GG) x) := by
  have := H.hostE_isGalois
  have hn0 : n ≠ 0 := by omega

  obtain ⟨Q₀, i₀, hi₀⟩ : ∃ (Q₀ : HeightOneSpectrum (𝓞 H.E)) (i₀ : H.E →+* Qn p n), Good Q₀ i₀ := by
    have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨⟨P, hP, hPl⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
    have hpP : (p : 𝓞 H.E) ∈ P := by
      have := Ideal.mem_span_singleton_self (p : ℤ)
      rwa [hPl.over, Ideal.mem_comap, map_natCast] at this
    let Q : HeightOneSpectrum (𝓞 H.E) := ⟨P, hP, fun e => by
      rw [e, Ideal.mem_bot] at hpP
      exact hp.out.ne_zero (Nat.cast_eq_zero.1 hpP)⟩
    have := hun Q hpP
    obtain ⟨m, j, hm, hj⟩ := exists_good Q hpP
    obtain rfl : m = n := (degree_eq hfr h2 he hj hm).trans hn.symm
    exact ⟨Q, j, hj⟩

  have hmem : ∀ x : H.E, H.φ₀ x ∈ algebraicClosure ℚ ℂ := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom H.φ₀.toRatAlgHom)
  obtain ⟨γ, hγ⟩ := exists_aut (κ.comp i₀) (lam.comp (H.φ₀.codRestrict (algebraicClosure ℚ ℂ) hmem))
  let i : H.E →+* Qn p n := i₀.comp (γ : H.E →+* H.E)
  have hi : Good (plc i) i := good_aut hi₀ γ fun _ => rfl
  have hκ : ∀ x, κ (i x) = lamV lam (H.φ₀ x) := fun x => by
    rw [lamV, dite_eq_left (hmem x)]
    exact (hγ x).symm
  let rp : Fin (nOrb (zPsi R.toFrame h)) → R.GG := fun v => (orbRep (zPsi R.toFrame h) v : R.Psi)
  let pl : Fin (nOrb (zPsi R.toFrame h)) ≃ {v : HeightOneSpectrum (𝓞 H.F) // ((p : ℕ) : 𝓞 H.F) ∈ v.asIdeal} :=
    Equiv.ofBijective (fun v => ⟨plc (twF H i (rp v)), p_mem_plc _⟩)
      ⟨fun v v' e => place_injective hun hfr hi hn0 (congrArg Subtype.val e), fun w => by
        obtain ⟨v, hv⟩ := place_surjective hun hfr h2 he hi hn0 w.1 w.2
        exact ⟨v, Subtype.ext hv⟩⟩
  have hb0 : H.sqrtMinusD ≠ 0 := fun e => by
    have := H.sqrtMinusD_sq
    rw [e, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at this
    exact H.hyp.2.1.ne_zero this
  obtain ⟨I, -, hI⟩ := exists_locId_of_completions (W := WQ p n) L H.sqrtMinusD hb0
    ((bridge_star_holds R H _).trans H.conj_sqrtMinusD) pl (fun v => tw H i (rp v))
    fun v => exists_completion_equiv (good_twF hun hfr he hi hn0 (rp v))
  refine ⟨I, fun v x => ?_, fun v x => ?_⟩
  · rw [hI]
    exact hκ _
  · rw [hI, hI]
    exact fr_apply hfr (good_tw hi _) x

open GlobalTheory.Mem.LocalPack Formalism.MainNotions Formalism.MainNotions.G

attribute [local instance] Formalism.BasicNotions.factResChar

theorem exists_locId_of_emb (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (iK : KfRec D w (frobOrder D (D.what₂.places.resChar w)) →+* ℂ_[(D.what₂.places.resChar w)])
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[(D.what₂.places.resChar w)]) :
    ∃ I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))),
      ∀ ψ, (pack D u Lc w hg.2.1 (frobOrder_spec D hg).1 (frobOrder_spec D hg).2 I ψ).posOK iK lam := by
  have hn : frobOrder D (D.what₂.places.resChar w) = orderOf (D.R.iota (hP D (D.what₂.places.resChar w))) :=
    orderOf_zPsi _ _
  obtain ⟨h2, hq, hd, -, -⟩ := Formalism.BasicNotions.Examples₂.LevelValuationRings.of_cls D.host _ hg.2.2.1
  have hN : ¬ D.what₂.places.resChar w ∣ D.host.condN := fun hdv =>
    ((D.host.toHostRaw.dvd_condN_iff_small hg.1).1 hdv).elim h2 fun h' => h'.elim hq hd
  have := D.host.hostE_isGalois
  obtain ⟨I, h1, h3⟩ := exists_locId_host (H := D.host) (p := D.what₂.places.resChar w)
    (h := D.R.iota (hP D (D.what₂.places.resChar w)))
    (fun Q hQ => by
      have := liesOver_of_mem Q hQ
      exact unramified_of_inertia _ fun σ hσ => ((D.host.der.frob _ hN Q.asIdeal).2.2.2 σ).1 hσ)
    (fun Q hQ σ hσ => by
      have := liesOver_of_mem Q hQ
      exact ((D.host.gal).symm_apply_eq.2 (frob_eq D hg Q.asIdeal σ hσ).symm).symm)
    (hn ▸ (frobOrder_spec D hg).1) (hn ▸ (frobOrder_spec D hg).2) hn Lc
    (iK.comp ((extRec D w (frobOrder D (D.what₂.places.resChar w))).φK.comp (iota _ _))) lam
  exact ⟨I, fun ψ => posCompat_of_base D.host _ _ _ I.iw iK lam h1 h3⟩

theorem exists_emb_norm (D : D7) (w : D.what₂.places.Pl) (n : ℕ) :
    ∃ iK : KfRec D w n →+* ℂ_[(D.what₂.places.resChar w)],
      ∀ x, ‖iK x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap (ORec D w n) (KfRec D w n)) :=
  ⟨(iC (Formalism.L2.G.Pend.k0ToC _)).comp (gL _), fun x =>
    (iC_int_Cp _ (fun y => (Formalism.L2.G.Pend.norm_k0ToC_le_iff _ _).2 ⟨y, rfl⟩) _).symm.trans (Oc_K _ x)⟩

theorem exists_locId : ∀ (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    ∃ (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
        (WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
        (QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))))
      (iK : KfRec D w (frobOrder D (D.what₂.places.resChar w)) →+* ℂ_[(D.what₂.places.resChar w)])
      (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[(D.what₂.places.resChar w)]),
      (∀ z : D.what₂.LL, iK (embRec D w (frobOrder D (D.what₂.places.resChar w)) z) = lamV lam (D.what₂.embLL z)) ∧
      ∀ ψ, (pack D u Lc w hg.2.1 (frobOrder_spec D hg).1 (frobOrder_spec D hg).2 I ψ).posOK iK lam := by
  intro D u Lc w hg
  obtain ⟨iK, -⟩ := exists_emb_norm D w (frobOrder D (D.what₂.places.resChar w))
  obtain ⟨lam, hlam⟩ := GlobalTheory.PadicPlaceExt.exists_lam D.what₂.embLL (iK.comp (embRec D w _))
  obtain ⟨I, hI⟩ := exists_locId_of_emb D u Lc w hg iK lam
  exact ⟨I, iK, lam, hlam, hI⟩

end Assembly

end GlobalTheory.PlaceOrbit
