module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
public import Formalism.LatticeTheta.Statement
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLOneLeftRightUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLOneLeftRightUnit
noncomputable section

namespace GlobalTheory.Shin.HcUnit

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

variable {F : Type} [Field F]

theorem toG_val {n : ℕ} (x : GL (Fin n) F) : toG (x : Matrix (Fin n) (Fin n) F) = x := by
  unfold toG
  rw [dite_eq_left x.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem brG_zero {a : ℕ} (x : GL (Fin a) F) : brG 0 a x = x := by
  have h : br 0 a (x : Matrix (Fin a) (Fin a) F) = x := by
    ext i j
    simp [br, ent]
  unfold brG
  rw [h, toG_val]

theorem tlG_self {a : ℕ} (x : GL (Fin a) F) : tlG a x = x := by
  have h : tl a (x : Matrix (Fin a) (Fin a) F) = x := by
    ext i j
    simp [tl, ent]
  unfold tlG
  rw [h, toG_val]

theorem inPar_zero {n : ℕ} (x : GL (Fin n) F) : InPar 0 x :=
  fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)

theorem inPar_self {a : ℕ} (x : GL (Fin a) F) : InPar a x :=
  fun i _ _ hi => absurd i.isLt (not_lt.mpr hi)

theorem gal_id {n : ℕ} (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j
  simp [gal]

theorem mean_class {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsCl χ) (x : G) :
    (Nat.card G : ℂ)⁻¹ * ∑ᶠ y : G, χ (y⁻¹ * x * y) = χ x := by
  have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h' : ∀ y : G, χ (y⁻¹ * x * y) = χ x := fun y => h x y
  have := Fintype.ofFinite G
  rw [finsum_congr h', finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

private theorem card_infinitePlace_eq_f {G : Type} {p : G → Prop} (h : ∀ x, p x) :
    Nat.card {x // p x} = Nat.card G :=
  Nat.card_congr (Equiv.subtypeUnivEquiv h)

theorem main : ∀ (F : Type) [Field F] [Finite F], ∀ (a : ℕ) (α : GL (Fin a) F → ℂ), IsCl α →
    hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α := by
  intro F _ _ a α hα
  refine ⟨funext fun x => ?_, funext fun x => ?_⟩
  · simp only [hc, hcTw]
    rw [card_infinitePlace_eq_f inPar_zero]
    simp only [gal_id, inPar_zero, ↓reduceIte, brG_zero, one_mul]
    exact mean_class hα x
  · simp only [hc, hcTw]
    rw [card_infinitePlace_eq_f inPar_self]
    simp only [gal_id, inPar_self, ↓reduceIte, tlG_self, mul_one]
    exact mean_class hα x

end GlobalTheory.Shin.HcUnit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLOneLeftRightUnitStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_one_left_right_unit : ∀ (F : Type) [Field F] [Finite F], ∀ (a : ℕ) (α : GL (Fin a) F → ℂ), IsCl α → hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α := by
  first | (exact @GlobalTheory.Shin.HcUnit.main) | (exact GlobalTheory.Shin.HcUnit.main) | (intros; apply GlobalTheory.Shin.HcUnit.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLBoundedEntriesCompletionFinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLBoundedEntriesCompletionFinitePlace
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace GlobalTheory.BoundedGL

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem isCompact_le (c : WithZero (Multiplicative ℤ)) :
    IsCompact {x : w.adicCompletion E | Valued.v x ≤ c} := by
  by_cases hc : c = 0
  · have e : {x : w.adicCompletion E | Valued.v x ≤ c} = {0} := by
      ext x
      simp [hc]
    rw [e]
    exact isCompact_singleton
  · obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
    set u : w.adicCompletion E := ((π ^ (-WithZero.log c) : E) : w.adicCompletion E) with hu
    have hvu : Valued.v u = c := by
      rw [hu, valuedAdicCompletion_eq_valuation', map_zpow₀, hπ, ← WithZero.exp_zsmul]
      simp [WithZero.exp_log hc]
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, map_zero] at hvu
      exact hc hvu.symm
    have hO : IsCompact {x : w.adicCompletion E | Valued.v x ≤ 1} := by
      have := PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers w
      convert this using 1
      ext x
      simp [mem_adicCompletionIntegers]
    have e : {x : w.adicCompletion E | Valued.v x ≤ c} = (fun y => u * y) '' {x | Valued.v x ≤ 1} := by
      ext x
      constructor
      · intro hx
        refine ⟨u⁻¹ * x, ?_, by simp [hu0]⟩
        show Valued.v (u⁻¹ * x) ≤ 1
        rw [map_mul, map_inv₀, hvu]
        exact inv_mul_le_one_of_le₀ hx zero_le'
      · rintro ⟨y, hy, rfl⟩
        show Valued.v (u * y) ≤ c
        rw [map_mul, hvu]
        exact mul_le_of_le_one_right' hy
    rw [e]
    exact hO.image (continuous_const_mul u)

theorem isCompact_bounded : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (c : WithZero (Multiplicative ℤ)), IsCompact {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
  intro E _ _ w n c
  set K := w.adicCompletion E
  set S : Set (Matrix (Fin n) (Fin n) K) := {A | ∀ i j, Valued.v (A i j) ≤ c} with hS
  have hK : IsCompact S := by
    have h : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => {x : K | Valued.v x ≤ c}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_le w c
    have e : S = (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => {x : K | Valued.v x ≤ c}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]; exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) K)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [hS, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]
  exact ⟨fun hg => ⟨fun i j => (hg i j).1, fun i j => (hg i j).2⟩, fun hg i j => ⟨hg.1 i j, hg.2 i j⟩⟩

end GlobalTheory.BoundedGL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLBoundedEntriesCompletionFinitePlaceStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (c : WithZero (Multiplicative ℤ)), IsCompact {g : GL (Fin n) (w.adicCompletion E) | ∀ i j, Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧ Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
  first | exact @GlobalTheory.BoundedGL.isCompact_bounded | exact GlobalTheory.BoundedGL.isCompact_bounded | (intros; apply GlobalTheory.BoundedGL.isCompact_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomLiftOfFormallySmooth
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

theorem exists_ringHom_lift_of_formallySmooth {R A C : Type} [CommRing R] [CommRing A] [CommRing C]
    (φ : R →+* A) (hφ : φ.FormallySmooth) (ψ : R →+* C) (I : Ideal C) (hI : IsNilpotent I)
    (g : A →+* C ⧸ I) (hg : g.comp φ = (Ideal.Quotient.mk I).comp ψ) :
    ∃ F : A →+* C, (∀ x, Ideal.Quotient.mk I (F x) = g x) ∧ ∀ r, F (φ r) = ψ r := by
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  haveI : Algebra.FormallySmooth R A := hφ
  let g' : A →ₐ[R] C ⧸ I :=
    { g with
      commutes' := fun r => by
        have := congrArg (· r) hg
        exact this }
  refine ⟨(Algebra.FormallySmooth.lift I hI g').toRingHom, fun x => ?_, fun r => ?_⟩
  · exact Algebra.FormallySmooth.mk_lift I hI g' x
  · have := (Algebra.FormallySmooth.lift I hI g').commutes r
    simpa [RingHom.algebraMap_toAlgebra] using this

def powModP (p : ℕ) (hp : p.Prime) (B : Type) [CommRing B] :
    B →+* B ⧸ Ideal.span {(p : B)} where
  toFun z := Ideal.Quotient.mk _ (z ^ p)
  map_one' := by simp
  map_mul' x y := by simp [mul_pow]
  map_zero' := by simp [zero_pow hp.ne_zero]
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
    rw [hr, map_add (f := _), map_add (f := _)]
    have : Ideal.Quotient.mk (Ideal.span {(p : B)}) ((p : B) * x * y * r) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, mul_assoc, mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [this, add_zero]

theorem frob_lift_etale_chart :
    ∀ (p : ℕ) [Fact p.Prime] {n : ℕ} {B : Type} [CommRing B]
      (φ : MvPolynomial (Fin n) (ZMod (p ^ 2)) →+* B), φ.Etale →
      ∃ F : B →+* B, (∀ z, ∃ w, F z = z ^ p + p * w) ∧
        ∀ l, F (φ (MvPolynomial.X l)) = φ (MvPolynomial.X l) ^ p := by
  intro p hpf n B _ φ hφ
  have hp : p.Prime := hpf.out
  set I : Ideal B := Ideal.span {(p : B)} with hIdef
  have hp2 : ((p : B)) ^ 2 = 0 := by
    have : ((p ^ 2 : ℕ) : MvPolynomial (Fin n) (ZMod (p ^ 2))) = 0 := by
      rw [← map_natCast (MvPolynomial.C (σ := Fin n)), ZMod.natCast_self, map_zero]
    calc ((p : B)) ^ 2 = φ ((p ^ 2 : ℕ) : MvPolynomial (Fin n) (ZMod (p ^ 2))) := by
          rw [map_natCast]; push_cast; rfl
      _ = 0 := by rw [this, map_zero]
  have hI : IsNilpotent I := by
    refine ⟨2, ?_⟩
    rw [hIdef, Ideal.span_singleton_pow, hp2, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.zero_eq_bot]
  have hsm : φ.FormallySmooth := by
    letI := φ.toAlgebra
    haveI : Algebra.Etale _ B := hφ
    show Algebra.FormallySmooth _ B
    infer_instance
  let ψ : MvPolynomial (Fin n) (ZMod (p ^ 2)) →+* B :=
    φ.comp (MvPolynomial.expand p).toRingHom
  have hg : (powModP p hp B).comp φ = (Ideal.Quotient.mk I).comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact congrArg (· r) (Subsingleton.elim ((((powModP p hp B).comp φ)).comp MvPolynomial.C)
        (((Ideal.Quotient.mk I).comp ψ).comp MvPolynomial.C))
    · intro i
      simp [ψ, powModP, I]
  obtain ⟨F, hF1, hF2⟩ := exists_ringHom_lift_of_formallySmooth φ hsm ψ I hI (powModP p hp B) hg
  refine ⟨F, fun z => ?_, fun l => ?_⟩
  · have h1 := hF1 z
    have : F z - z ^ p ∈ I := by
      rw [← Ideal.Quotient.eq]
      exact h1
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨w, by rw [mul_comm]; linear_combination -hw⟩
  · rw [hF2]
    simp [ψ]

end GlobalTheory.DI
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEigenFiltrationPiecesAddValInt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEigenFiltrationPiecesAddValInt
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.HerbFin

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {S : Type} [Fintype S]
  [DecidableEq S]

theorem monic_prod (a : S → Int0 v) : (∏ s, (X - Polynomial.C (a s)) : (Int0 v)[X]).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_sub_C (a s)

def powBasis (a : S → Int0 v) : PowerBasis (Int0 v) (RS a) := AdjoinRoot.powerBasis' (monic_prod a)

instance finite_RS (a : S → Int0 v) : Module.Finite (Int0 v) (RS a) := (powBasis a).finite

theorem eq_zero_of_smul_RS (a : S → Int0 v) {c : Int0 v} (hc : c ≠ 0) {y : RS a}
    (h : c • y = 0) : y = 0 := by
  have b := (powBasis a).basis
  apply b.repr.injective
  refine Finsupp.ext fun i => ?_
  have h2 := congrArg (fun z => b.repr z i) h
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
    Pi.zero_apply] at h2
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact (mul_eq_zero.1 h2).resolve_left hc

theorem eq_zero_of_smul_pi (a : S → Int0 v) {N : ℕ} {c : Int0 v} (hc : c ≠ 0)
    {y : Fin N → RS a} (h : c • y = 0) : y = 0 := by
  funext i
  have h3 := congrFun h i
  simp only [Pi.smul_apply, Pi.zero_apply] at h3
  exact eq_zero_of_smul_RS a hc h3

theorem sat_kerMul (a : S → Int0 v) (r : RS a) (Q : Type) [AddCommGroup Q] [Module (RS a) Q]
    [Module (Int0 v) Q] [IsScalarTower (Int0 v) (RS a) Q]
    (htf : ∀ (c : Int0 v) (y : Q), c ≠ 0 → c • y = 0 → y = 0) :
    GlobalTheory.IsSaturatedSubmodule (kerMul a r Q) := by
  rw [GlobalTheory.isSaturatedSubmodule_iff]
  intro c hc x hx
  simp only [kerMul, Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.lsmul_apply] at hx ⊢
  rw [smul_comm] at hx
  exact htf c _ hc hx

theorem finite_main : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, Module.Finite (Int0 v) (Fil.restrictScalars (Int0 v)) ∧ Module.Finite (Int0 v) (preEig a Fil τ) ∧ Module.Finite (Int0 v) (filKer a Fil τ) ∧ Module.Finite (Int0 v) (eigSub a τ (Fin N → RS a)) ∧ Module.Finite (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)) ∧ Module.Finite (Int0 v) (eigSub a τ Fil) ∧ Module.Finite (Int0 v) (kerMul a (cofac a τ) Fil) := by
  intro C _ v S _ _ a _ N Fil hFil τ
  have hsatF : GlobalTheory.IsSaturatedSubmodule (Fil.restrictScalars (Int0 v)) :=
    GlobalTheory.isSaturatedSubmodule_iff.2 fun c hc x hx => hFil c x hc hx
  have hT1 : ∀ (c : Int0 v) (y : Fin N → RS a), c ≠ 0 → c • y = 0 → y = 0 :=
    fun c y hc h => eq_zero_of_smul_pi a hc h
  have hT2 : ∀ (c : Int0 v) (y : Fil), c ≠ 0 → c • y = 0 → y = 0 := fun c y hc h =>
    Subtype.ext (hT1 c y hc (congrArg Subtype.val h))
  have hT3 : ∀ (c : Int0 v) (y : (Fin N → RS a) ⧸ Fil), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc h
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      rw [Submodule.Quotient.mk_eq_zero]
      exact hFil c x hc h
  have hF : Module.Finite (Int0 v) (Fil.restrictScalars (Int0 v)) := hsatF.finite_of_valuationRing
  have hFil' : Module.Finite (Int0 v) Fil := hF
  have hQ : Module.Finite (Int0 v) ((Fin N → RS a) ⧸ Fil) :=
    Module.Finite.of_surjective (proj a Fil) (Submodule.mkQ_surjective Fil)
  refine ⟨hF, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hsatF.comap (mulR a N (lin a τ))).finite_of_valuationRing
  · refine (hsatF.inf ?_).finite_of_valuationRing
    exact sat_kerMul a (cofac a τ) (Fin N → RS a) hT1
  · exact (sat_kerMul a (lin a τ) (Fin N → RS a) hT1).finite_of_valuationRing
  · exact (sat_kerMul a (lin a τ) _ hT3).finite_of_valuationRing
  · exact (sat_kerMul a (lin a τ) Fil hT2).finite_of_valuationRing
  · exact (sat_kerMul a (cofac a τ) Fil hT2).finite_of_valuationRing

end GlobalTheory.HerbFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEigenFiltrationPiecesAddValIntStatement
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_eigenFiltration_pieces_addValInt : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, Module.Finite (Int0 v) (Fil.restrictScalars (Int0 v)) ∧ Module.Finite (Int0 v) (preEig a Fil τ) ∧ Module.Finite (Int0 v) (filKer a Fil τ) ∧ Module.Finite (Int0 v) (eigSub a τ (Fin N → RS a)) ∧ Module.Finite (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)) ∧ Module.Finite (Int0 v) (eigSub a τ Fil) ∧ Module.Finite (Int0 v) (kerMul a (cofac a τ) Fil) := by
  first | exact @GlobalTheory.HerbFin.finite_main | exact GlobalTheory.HerbFin.finite_main | (intros; apply GlobalTheory.HerbFin.finite_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLFieldAutomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLFieldAutomorphism
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.HcGal

variable {F F' : Type} [Field F] [Field F']

theorem gal_coe (t : F →+* F') {n : ℕ} (x : GL (Fin n) F) :
    ((gal t n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = (x : Matrix (Fin n) (Fin n) F).map t := by
  ext i j; simp [gal]

theorem gal_id {n : ℕ} (x : GL (Fin n) F) : gal (RingHom.id F) n x = x := by
  ext i j; simp [gal]

theorem ent_map (t : F →+* F') {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map t) i j = t (ent M i j) := by
  unfold ent
  split_ifs <;> simp

theorem isUnit_map_iff (t : F →+* F') {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    IsUnit (M.map t) ↔ IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
  have : (M.map t).det = t M.det := by
    rw [RingHom.map_det]; rfl
  rw [this, _root_.map_ne_zero]

theorem toG_map (t : F →+* F') {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    toG (M.map t) = gal t n (toG M) := by
  unfold toG
  by_cases h : IsUnit M
  · rw [dite_eq_left h, dite_eq_left ((isUnit_map_iff t M).2 h)]
    apply Units.ext
    rw [gal_coe, IsUnit.unit_spec, IsUnit.unit_spec]
  · rw [dite_eq_right h, dite_eq_right (fun h' => h ((isUnit_map_iff t M).1 h')), map_one]

theorem tlG_gal (t : F →+* F') (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    tlG a (gal t n x) = gal t a (tlG a x) := by
  unfold tlG
  rw [← toG_map, gal_coe]
  congr 1
  ext i j
  simp only [tl, Matrix.map_apply, ent_map]

theorem brG_gal (t : F →+* F') (a b : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    brG a b (gal t n x) = gal t b (brG a b x) := by
  unfold brG
  rw [← toG_map, gal_coe]
  congr 1
  ext i j
  simp only [br, Matrix.map_apply, ent_map]

theorem inPar_gal (t : F →+* F') (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    InPar a (gal t n x) ↔ InPar a x := by
  unfold InPar
  simp only [gal_coe, Matrix.map_apply, map_eq_zero]

theorem gal_bijective (t : F ≃+* F') (n : ℕ) : Function.Bijective (gal (t : F →+* F') n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨gal (t.symm : F' →+* F) n, fun x => ?_, fun x => ?_⟩
  · ext i j; simp [gal]
  · ext i j; simp [gal]

theorem hc_gal : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F ≃+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x : GL (Fin n) F), hc a b α β n (gal (t : F →+* F) n x) =
    hc a b (fun y => α (gal (t : F →+* F) a y)) (fun y => β (gal (t : F →+* F) b y)) n x := by
  intro F _ _ t a b n α β x
  unfold hc hcTw
  congr 1
  symm
  refine finsum_eq_of_bijective (gal (t : F →+* F) n) (gal_bijective t n) fun y => ?_
  rw [gal_id, gal_id, ← map_inv, ← map_mul, ← map_mul, tlG_gal, brG_gal]
  simp only [inPar_gal]

end GlobalTheory.Shin.HcGal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLFieldAutomorphismStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F ≃+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (x : GL (Fin n) F), hc a b α β n (gal (t : F →+* F) n x) = hc a b (fun y => α (gal (t : F →+* F) a y)) (fun y => β (gal (t : F →+* F) b y)) n x := by
  first | (exact @GlobalTheory.Shin.HcGal.hc_gal) | (exact GlobalTheory.Shin.HcGal.hc_gal) | (intros; apply GlobalTheory.Shin.HcGal.hc_gal  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZLatticeFractionalIdealRealLatticeImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZLatticeFractionalIdealRealLatticeImage
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.LipschitzTR

theorem span_range_remb (F : Type) [Field F] [NumberField F] :
    Submodule.span ℝ (Set.range (remb F)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hli := (linearIndependent_monoidHom F ℝ).comp
    (fun τ : F →+* ℝ => (τ : F →* ℝ)) (fun τ₁ τ₂ h => by
      ext a; exact congrArg (fun g : F →* ℝ => g a) h)
  have hsum : ∀ a : F, ∑ τ : F →+* ℝ, f (EuclideanSpace.single τ 1) * τ a = 0 := by
    intro a
    have h1 : f (remb F a) = 0 := hle (Submodule.subset_span ⟨a, rfl⟩)
    have h2 : remb F a = ∑ τ : F →+* ℝ, τ a • EuclideanSpace.single τ (1 : ℝ) := by
      ext σ
      simp [PiLp.single_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum] at h1
    simpa [mul_comm] using h1
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun τ => f (EuclideanSpace.single τ 1))
    (by
      funext a
      simpa [Finset.sum_apply] using hsum a)
  apply hf0
  apply LinearMap.ext
  intro x
  have hx : x = ∑ τ : F →+* ℝ, x τ • EuclideanSpace.single τ (1 : ℝ) := by
    ext σ
    simp [PiLp.single_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  simp [hcoef]

end GlobalTheory.LipschitzTR

namespace GlobalTheory.LipschitzTR

theorem isZLattice_latOf : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)],
    IsZLattice ℝ (latOf N) := by
  intro F _ _ _ N hN _
  refine ⟨?_⟩
  rw [eq_top_iff, ← span_range_remb F, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have hc : ∃ c ∈ N, c ≠ 0 := by
    by_contra h
    push_neg at h
    apply hN
    ext x
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨h x, fun hx => hx ▸ (N : Submodule (𝓞 F) F).zero_mem⟩
  obtain ⟨c, hcN, hc0⟩ := hc
  obtain ⟨y, hy0, hint⟩ := exists_integral_multiples ℤ ℚ (L := F) {a / c}
  let α : 𝓞 F := ⟨y • (a / c), hint _ (Finset.mem_singleton_self _)⟩
  have hmem : (y : F) * a ∈ N := by
    have h := Submodule.smul_mem (N : Submodule (𝓞 F) F) α hcN
    have he : α • c = (y : F) * a := by
      rw [Algebra.smul_def]
      show (y • (a / c)) * c = (y : F) * a
      rw [zsmul_eq_mul]
      field_simp
    rw [he] at h
    exact h
  have hy : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
  have heq : remb F a = (y : ℝ)⁻¹ • remb F ((y : F) * a) := by
    ext τ
    simp only [remb_apply, PiLp.smul_apply, smul_eq_mul, map_mul, map_intCast]
    field_simp
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ((mem_latOf N _).2 ⟨_, hmem, rfl⟩))

end GlobalTheory.LipschitzTR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZLatticeFractionalIdealRealLatticeImageStatement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isZLattice_fractionalIdealRealLatticeImage : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)], IsZLattice ℝ (latOf N) := by
  first | exact @GlobalTheory.LipschitzTR.isZLattice_latOf | exact GlobalTheory.LipschitzTR.isZLattice_latOf | (intros; apply GlobalTheory.LipschitzTR.isZLattice_latOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsStructure
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.RingFacts

variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

theorem monic_Q (a : S → O) : (∏ s, (X - Polynomial.C (a s)) : O[X]).Monic :=
  monic_prod_of_monic _ _ fun s _ => monic_X_sub_C (a s)

theorem lin_eq (a : S → O) (s : S) :
    lin a s = AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s)) : O[X]) (X - Polynomial.C (a s)) := by
  simp [lin, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

theorem cofac_eq (a : S → O) (τ : S) :
    cofac a τ = AdjoinRoot.mk (∏ s, (X - Polynomial.C (a s)) : O[X])
      (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) := by
  rw [cofac, map_prod]
  exact Finset.prod_congr rfl fun s _ => lin_eq a s

theorem ev_mk (a : S → O) (τ : S) (f : O[X]) :
    ev a τ (AdjoinRoot.mk _ f) = f.eval (a τ) := by
  simp [ev]

theorem exists_lin_mul_of_ev_eq_zero (a : S → O) (τ : S) (r : RS a) (hr : ev a τ r = 0) :
    ∃ r', r = lin a τ * r' := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [ev_mk] at hr
  obtain ⟨h, hh⟩ := (Polynomial.dvd_iff_isRoot).2 hr
  exact ⟨AdjoinRoot.mk _ h, by rw [hh, map_mul, lin_eq]⟩

theorem eq_algebraMap_add_lin_mul (a : S → O) (τ : S) (r : RS a) :
    ∃ g, r = algebraMap O (RS a) (ev a τ r) + lin a τ * g := by
  obtain ⟨g, hg⟩ := exists_lin_mul_of_ev_eq_zero a τ (r - algebraMap O (RS a) (ev a τ r))
    (by rw [map_sub, AlgHom.commutes]; simp)
  exact ⟨g, by rw [← hg]; ring⟩

theorem lin_mul_cofac (a : S → O) (τ : S) : lin a τ * cofac a τ = 0 := by
  rw [cofac, Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Finset.prod_congr rfl
    (fun s _ => lin_eq a s), ← map_prod]
  exact AdjoinRoot.mk_self

theorem ev_cofac (a : S → O) (τ : S) :
    ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) := by
  rw [cofac, map_prod]
  exact Finset.prod_congr rfl fun s _ => ev_lin a τ s

theorem eq_smul_cofac_of_lin_mul_eq_zero [IsDomain O] (a : S → O) (τ : S) (r : RS a)
    (hr : lin a τ * r = 0) : ∃ c : O, r = algebraMap O (RS a) c * cofac a τ := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [lin_eq, ← map_mul, AdjoinRoot.mk_eq_zero] at hr
  obtain ⟨g, hg⟩ := hr
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), mul_assoc] at hg
  have hf : f = (∏ s ∈ Finset.univ.erase τ, (X - Polynomial.C (a s))) * g :=
    mul_left_cancel₀ (X_sub_C_ne_zero (a τ)) hg
  obtain ⟨h, hh⟩ := eq_algebraMap_add_lin_mul a τ (AdjoinRoot.mk _ g)
  refine ⟨ev a τ (AdjoinRoot.mk _ g), ?_⟩
  have hc := lin_mul_cofac a τ
  calc AdjoinRoot.mk _ f = cofac a τ * AdjoinRoot.mk _ g := by rw [hf, map_mul, cofac_eq]
    _ = cofac a τ * (algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) + lin a τ * h) := by
        rw [← hh]
    _ = algebraMap O (RS a) (ev a τ (AdjoinRoot.mk _ g)) * cofac a τ
        + (lin a τ * cofac a τ) * h := by ring
    _ = _ := by rw [hc]; simp

theorem ring_facts : ∀ (O : Type) [CommRing O] [IsDomain O] (S : Type) [Fintype S] [DecidableEq S]
    (a : S → O) (τ : S), Module.Free O (RS a) ∧ Module.Finite O (RS a) ∧
    lin a τ * cofac a τ = 0 ∧ ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) ∧
    (∀ r : RS a, ev a τ r = 0 → ∃ r', r = lin a τ * r') ∧
    (∃ g : RS a, cofac a τ = algebraMap O (RS a) (ev a τ (cofac a τ)) + lin a τ * g) ∧
    (∀ r : RS a, lin a τ * r = 0 → ∃ c : O, r = algebraMap O (RS a) c * cofac a τ) := by
  intro O _ _ S _ _ a τ
  let pb := AdjoinRoot.powerBasis' (monic_Q a)
  exact ⟨Module.Free.of_basis pb.basis, pb.finite, lin_mul_cofac a τ, ev_cofac a τ,
    exists_lin_mul_of_ev_eq_zero a τ, eq_algebraMap_add_lin_mul a τ (cofac a τ),
    eq_smul_cofac_of_lin_mul_eq_zero a τ⟩

end GlobalTheory.RingFacts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsStructureStatement
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoinRootProdLinearFactors_structure : ∀ (O : Type) [CommRing O] [IsDomain O] (S : Type) [Fintype S] [DecidableEq S] (a : S → O) (τ : S), Module.Free O (RS a) ∧ Module.Finite O (RS a) ∧ lin a τ * cofac a τ = 0 ∧ ev a τ (cofac a τ) = ∏ s ∈ Finset.univ.erase τ, (a τ - a s) ∧ (∀ r : RS a, ev a τ r = 0 → ∃ r', r = lin a τ * r') ∧ (∃ g : RS a, cofac a τ = algebraMap O (RS a) (ev a τ (cofac a τ)) + lin a τ * g) ∧ (∀ r : RS a, lin a τ * r = 0 → ∃ c : O, r = algebraMap O (RS a) c * cofac a τ) := by
  first | exact @GlobalTheory.RingFacts.ring_facts | exact GlobalTheory.RingFacts.ring_facts | (intros; apply GlobalTheory.RingFacts.ring_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceClosedUnderConjReflection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceClosedUnderConjReflection
namespace AdelicReflection
section

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicReflect

def conjNeg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  let g : SchwartzMap E ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (ContinuousLinearEquiv.neg ℝ) f
  { toFun := fun y => starRingEnd ℂ (g y)
    smooth' := Complex.conjCLE.contDiff.comp g.smooth'
    decay' := by
      intro k n
      obtain ⟨C, hC⟩ := g.decay' k n
      refine ⟨C, fun x => ?_⟩
      have e : (fun y => starRingEnd ℂ (g y)) = Complex.conjLIE ∘ g := rfl
      rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
      exact hC x }

theorem conjNeg_mem_SB {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] {g : X → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB X) : (fun y => starRingEnd ℂ (g (-y))) ∈ GlobalTheory.WeilM.SB X := by
  obtain ⟨hlc, hcs⟩ := hg
  refine ⟨(hlc.comp_continuous continuous_neg).comp (starRingEnd ℂ), ?_⟩
  exact (hcs.comp_homeomorph (Homeomorph.neg X)).comp_left (g := starRingEnd ℂ) (map_zero _)

theorem conj_pureA_neg (F : Type) [Field F] [NumberField F] {κ : Type}
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → AdeleRing (𝓞 F) F) :
    starRingEnd ℂ (GlobalTheory.WeilM.pureA F f g (-x)) =
      GlobalTheory.WeilM.pureA F (fun y => starRingEnd ℂ (f (-y))) (fun y => starRingEnd ℂ (g (-y))) x := by
  simp only [GlobalTheory.WeilM.pureA, map_mul]
  congr 3
  funext i
  rw [Pi.neg_apply, Pi.neg_apply, ← map_neg]
  rfl

theorem schA_conj_neg : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ φ hφ
  unfold GlobalTheory.WeilM.schA at hφ ⊢
  induction hφ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    refine Submodule.subset_span ⟨conjNeg f, fun y => starRingEnd ℂ (g (-y)), conjNeg_mem_SB hg, ?_⟩
    funext x
    rw [conj_pureA_neg]
    congr 1
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext x
    simp
  | add a b _ _ ha hb =>
    convert Submodule.add_mem _ ha hb using 1
    funext x
    simp only [Pi.add_apply, map_add]
  | smul c a _ ha =>
    convert Submodule.smul_mem _ (starRingEnd ℂ c) ha using 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]

end GlobalTheory.CompanionTheory.AdelicReflect

end

end

end AdelicReflection
section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ φ hφ
  exact AdelicReflection.GlobalTheory.CompanionTheory.AdelicReflect.schA_conj_neg F κ φ hφ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceClosedUnderConjReflectionStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartzSpace_closed_under_conj_reflection : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∀ φ ∈ GlobalTheory.WeilM.schA F κ, (fun x => starRingEnd ℂ (φ (-x))) ∈ GlobalTheory.WeilM.schA F κ := by
  first | exact @GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection | exact GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection | (intros; apply GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularPairLiftToPrimePowerField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaKernelDerivativeVanishes
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.RegNorm

theorem geom_mul (q m l : ℕ) (hq : 0 < q) :
    (q ^ m - 1) * ∑ i ∈ Finset.range l, q ^ (m * i) = (q ^ l) ^ m - 1 := by
  have h1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ (q ^ l) ^ m := Nat.one_le_pow _ _ (pow_pos hq _)
  have hZ : (((q ^ m : ℕ) : ℤ) - 1) * ∑ i ∈ Finset.range l, ((q ^ m : ℕ) : ℤ) ^ i
      = ((q ^ m : ℕ) : ℤ) ^ l - 1 := mul_geom_sum _ _
  have : (((q ^ m - 1) * ∑ i ∈ Finset.range l, q ^ (m * i) : ℕ) : ℤ) = (((q ^ l) ^ m - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    simp only [pow_mul] at *
    push_cast at hZ
    rw [hZ, ← pow_mul, ← pow_mul, mul_comm m l]
  exact_mod_cast this

theorem pow_modEq_pow_mod (q m x : ℕ) (hq : 1 ≤ q) :
    q ^ x ≡ q ^ (x % m) [MOD q ^ m - 1] := by
  have h1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq
  have hm : q ^ m ≡ 1 [MOD q ^ m - 1] := Nat.modEq_sub h1
  calc q ^ x = (q ^ m) ^ (x / m) * q ^ (x % m) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1 ^ (x / m) * q ^ (x % m) [MOD q ^ m - 1] := (hm.pow _).mul_right _
    _ = q ^ (x % m) := by simp

end GlobalTheory.Shin.RegNorm

namespace GlobalTheory.Shin.RegNorm

theorem lift_iff (q m l k x y : ℕ) (hq : 0 < q) (hl : 0 < l) :
    (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * x ≡ (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * y
      [MOD (q ^ l) ^ m - 1] ↔ k * x ≡ k * y [MOD q ^ m - 1] := by
  set S := ∑ i ∈ Finset.range l, q ^ (m * i) with hSdef
  have hS : S ≠ 0 := by
    have : 0 < S := Finset.sum_pos (fun i _ => pow_pos hq _) ⟨0, by simp [hl]⟩
    omega
  rw [← geom_mul q m l hq, ← hSdef]
  have e1 : k * S * x = k * x * S := by ring
  have e2 : k * S * y = k * y * S := by ring
  rw [e1, e2]
  exact ⟨Nat.ModEq.mul_right_cancel' hS, Nat.ModEq.mul_right' S⟩

end GlobalTheory.Shin.RegNorm

namespace GlobalTheory.Shin

theorem reg_norm_frob : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k →
    Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∧
      ∃ a, (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * q ≡
        (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ l) ^ a [MOD (q ^ l) ^ m - 1] := by
  intro q l m k hq hl hm hlm hreg
  have hq0 : 0 < q := by omega
  have hq1 : 1 ≤ q := by omega
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hlm
  refine ⟨?_, ?_⟩
  · intro i hi0 him h
    have h' : (k * ∑ j ∈ Finset.range l, q ^ (m * j)) * (q ^ l) ^ i ≡
        (k * ∑ j ∈ Finset.range l, q ^ (m * j)) * 1 [MOD (q ^ l) ^ m - 1] := by
      simpa using h
    have h2 := (RegNorm.lift_iff q m l k _ _ hq0 hl.pos).1 h'
    rw [← pow_mul, mul_one] at h2
    have h3 : k * q ^ (l * i % m) ≡ k [MOD q ^ m - 1] :=
      ((RegNorm.pow_modEq_pow_mod q m (l * i) hq1).mul_left k).symm.trans h2
    refine hreg (l * i % m) ?_ (Nat.mod_lt _ hm) h3
    rcases Nat.eq_zero_or_pos (l * i % m) with h0 | h0
    · exfalso
      have hd : m ∣ l * i := Nat.dvd_of_mod_eq_zero h0
      have : m ∣ i := hcop.symm.dvd_of_dvd_mul_left hd
      exact absurd (Nat.le_of_dvd hi0 this) (by omega)
    · exact h0
  · have ha : ∃ a, l * a % m = 1 % m := by
      rcases Nat.lt_or_ge 1 m with h1 | h1
      · obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
        exact ⟨a, by rw [ha, Nat.mod_eq_of_lt h1]⟩
      · have : m = 1 := by omega
        subst this
        exact ⟨0, by simp⟩
    obtain ⟨a, ha⟩ := ha
    refine ⟨a, (RegNorm.lift_iff q m l k _ _ hq0 hl.pos).2 ?_⟩
    rw [← pow_mul]
    have e1 : q ^ 1 ≡ q ^ (1 % m) [MOD q ^ m - 1] := RegNorm.pow_modEq_pow_mod q m 1 hq1
    have e2 : q ^ (l * a) ≡ q ^ (l * a % m) [MOD q ^ m - 1] := RegNorm.pow_modEq_pow_mod q m (l * a) hq1
    rw [ha] at e2
    rw [pow_one] at e1
    exact (e1.trans e2.symm).mul_left k

end GlobalTheory.Shin
end

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_pair_lift_to_prime_power_field : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k → Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∧ ∃ a, (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * q ≡ (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ l) ^ a [MOD (q ^ l) ^ m - 1] := by
  first | (exact @GlobalTheory.Shin.reg_norm_frob) | (exact GlobalTheory.Shin.reg_norm_frob) | (intros; apply GlobalTheory.Shin.reg_norm_frob  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularQuotientPrimeElement
namespace GlobalTheory

theorem prime_algebraMap_localization_of_isRegularRing_quotient :
    ∀ (A : Type) [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime] (x : A), x ≠ 0 → x ∈ P →
      IsRegularRing (A ⧸ Ideal.span {x}) → Prime (algebraMap A (Localization.AtPrime P) x) := by
  intro A _ _ P _ x hx hxP hreg
  set R := Localization.AtPrime P
  set J : Ideal A := Ideal.span {x} with hJdef
  have hJP : RingHom.ker (Ideal.Quotient.mk J) ≤ P := by
    rw [Ideal.mk_ker, hJdef, Ideal.span_le, Set.singleton_subset_iff]; exact hxP
  have hle : J ≤ (J.map (algebraMap A R)).comap (algebraMap A R) := Ideal.le_comap_map
  letI : Algebra (A ⧸ J) (R ⧸ J.map (algebraMap A R)) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective P.primeCompl R (S' := R ⧸ J.map (algebraMap A R))
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have hm : (P.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hJP
  have e : P.primeCompl.map (Ideal.Quotient.mk J) = (P.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (P.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = P := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJP]
    ext y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨z', hz', e⟩ hz
      exact hz' (hc.le (show Ideal.Quotient.mk J z' ∈ _ from e ▸ hz))
    · exact fun hz => ⟨z, fun h => hz (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  have := IsRegularRing.isRegularLocalRing_localization (P.map (Ideal.Quotient.mk J))
  haveI : IsRegularLocalRing (R ⧸ J.map (algebraMap A R)) :=
    IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (P.map (Ideal.Quotient.mk J)).primeCompl
      (Localization.AtPrime (P.map (Ideal.Quotient.mk J))) _).toRingEquiv
  have hdom : IsDomain (R ⧸ J.map (algebraMap A R)) :=
    (isDomain_and_isIntegrallyClosed_of_isRegularLocalRing _).1
  have hmap : J.map (algebraMap A R) = Ideal.span {algebraMap A R x} := by
    rw [hJdef, Ideal.map_span, Set.image_singleton]
  rw [hmap] at hdom
  have hprime : (Ideal.span {algebraMap A R x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).1 hdom
  have hne : algebraMap A R x ≠ 0 := by
    intro h0
    apply hx
    exact IsLocalization.injective R (P.primeCompl_le_nonZeroDivisors) (by simpa using h0)
  exact (Ideal.span_singleton_prime hne).1 hprime

end GlobalTheory
end
