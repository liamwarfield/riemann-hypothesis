module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecond
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConstantExponentsFinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminingLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.DecoClassCount


open scoped TensorProduct in
theorem exists_span_quot {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ v : Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N),
      Submodule.span R (Set.range v) = ⊤ := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  refine ⟨(TensorProduct.quotTensorEquivQuotSMul N I) ∘ b, ?_⟩
  have h1 : Submodule.span R (Set.range b) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq,
      Submodule.restrictScalars_top]
  have h2 := congrArg (Submodule.map (TensorProduct.quotTensorEquivQuotSMul N I).toLinearMap) h1
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h2
  rw [Set.range_comp]
  exact h2

theorem exists_determining {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    ∃ v : Fin (Module.finrank R N) → N, ∀ f g : N →ₗ[R] R ⧸ I, (∀ i, f (v i) = g (v i)) → f = g := by
  obtain ⟨v, hv⟩ := exists_span_quot (R := R) (N := N) I
  choose u hu using fun i => Submodule.Quotient.mk_surjective _ (v i)
  have hk : ∀ f : N →ₗ[R] R ⧸ I, (I • ⊤ : Submodule R N) ≤ LinearMap.ker f := by
    intro f
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  refine ⟨u, fun f g hfg => ?_⟩
  have : Submodule.liftQ _ f (hk f) = Submodule.liftQ _ g (hk g) :=
    LinearMap.ext_on_range hv fun i => by
      rw [← hu i]
      exact hfg i
  ext x
  simpa using LinearMap.congr_fun this (Submodule.Quotient.mk x)

theorem finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : Submodule (𝓞 K) V)
    (h : Submodule.span K (p : Set V) = ⊤) : Module.finrank (𝓞 K) p = Module.finrank K V := by
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
    · have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
      exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
    · have hy : y ∈ Submodule.span K (p : Set V) := h ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl,
    IsFractionRing.finrank_right_eq (𝓞 K) K V]

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def IsLocForm (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (φ : Sp E n → 𝓞 E ⧸ P.asIdeal) : Prop :=
  (∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, ∀ y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, φ (x + y) = φ x + φ y) ∧
  ∀ (a : 𝓞 E), ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, φ (a • x) = Ideal.Quotient.mk P.asIdeal a * φ x


omit [StarRing E] in
theorem exists_determining_lattice (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n))
    (hN : Submodule.IsLattice E N) :
    ∃ v : Fin n → Sp E n, ∀ φ ψ, IsLocForm P N φ → IsLocForm P N ψ → (∀ i, φ (v i) = ψ (v i)) →
      ∀ x ∈ N, φ x = ψ x := by
  have : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 (Submodule.IsLattice.fg (self := hN))
  have : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 E) N := inferInstance
  have : Module.Projective (𝓞 E) N := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hr : Module.finrank (𝓞 E) N ≤ n := by
    letI : Submodule.IsLattice E N := hN
    rw [← Submodule.IsLattice.finrank_span_eq_finrank E N]
    simpa using Submodule.finrank_le (Submodule.span E (N : Set (Sp E n)))
  obtain ⟨v, hv⟩ := exists_determining (R := 𝓞 E) (N := N) P.asIdeal
  have hle : N ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := fun x hx =>
    ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩
  let lin : ∀ φ, IsLocForm P N φ → (N →ₗ[𝓞 E] 𝓞 E ⧸ P.asIdeal) := fun φ hφ =>
    { toFun := fun x => φ x
      map_add' := fun x y => hφ.1 x (hle x.2) y (hle y.2)
      map_smul' := fun a x => hφ.2 a x (hle x.2) }
  classical
  refine ⟨fun i => if hi : i.val < Module.finrank (𝓞 E) N then v ⟨i.val, hi⟩ else 0,
    fun φ ψ hφ hψ h x hx => ?_⟩
  have := hv (lin φ hφ) (lin ψ hψ) fun i => by
    change φ (v i) = ψ (v i)
    simpa using h ⟨i.val, lt_of_lt_of_le i.isLt hr⟩
  exact LinearMap.congr_fun this ⟨x, hx⟩

theorem card_fibre_le (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) :
    {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) | d.1.N = N}.Finite ∧ {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) | d.1.N = N}.ncard ≤
      (∏ P ∈ ST, Ideal.absNorm P.asIdeal ^ n) * ∏ w ∈ SG, Ideal.absNorm w.asIdeal ^ (n ^ 2) := by
  classical
  rcases Set.eq_empty_or_nonempty {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) | d.1.N = N} with he | ⟨d0, hd0⟩
  · rw [he]; simp
  have hlat : Submodule.IsLattice E N := by
    have := d0.2.lat
    rwa [show d0.1.N = N from hd0] at this
  choose v hv using fun P => exists_determining_lattice P N hlat
  haveI hfin : ∀ P : HeightOneSpectrum (𝓞 E), Finite (𝓞 E ⧸ P.asIdeal) := fun P =>
    Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  let Φ : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) →
      (∀ P : ST, Fin n → 𝓞 E ⧸ P.1.asIdeal) × (∀ w : SG, Fin n → Fin n → 𝓞 E ⧸ w.1.asIdeal) :=
    fun d => (fun P i => d.1.f P (v P.1 i), fun w i => d.1.be w (v w.1 i))
  have hinj : Set.InjOn Φ {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG) | d.1.N = N} := by
    intro d hd d' hd' hdd
    replace hd : d.1.N = N := hd
    replace hd' : d'.1.N = N := hd'
    have hf : ∀ e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG), e.1.N = N → ∀ P : ST, IsLocForm P.1 N (e.1.f P) := by
      rintro e rfl P
      exact ⟨e.2.f_add P, e.2.f_smul P⟩
    have hb : ∀ e : DecoSet (E := E) (n := n) (ST := ST) (SG := SG), e.1.N = N → ∀ (w : SG) (j : Fin n),
        IsLocForm w.1 N fun x => e.1.be w x j := by
      rintro e rfl w j
      exact ⟨fun x hx y hy => congrFun (e.2.be_add w x hx y hy) j,
        fun a x hx => congrFun (e.2.be_smul w a x hx) j⟩
    apply Subtype.ext
    refine d.2.ext_on d'.2 (hd.trans hd'.symm) (fun P x hx => ?_) (fun w x hx => ?_)
    · exact hv P.1 _ _ (hf d hd P) (hf d' hd' P)
        (fun i => congrFun (congrFun (congrArg Prod.fst hdd) P) i) x (hd ▸ hx)
    · funext j
      exact hv w.1 _ _ (hb d hd w j) (hb d' hd' w j)
        (fun i => congrFun (congrFun (congrFun (congrArg Prod.snd hdd) w) i) j) x (hd ▸ hx)
  refine ⟨Set.Finite.of_finite_image (Set.toFinite _) hinj, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn Φ (t := Set.univ) (fun _ _ => Set.mem_univ _) hinj
    (Set.toFinite _)
  refine hle.trans (le_of_eq ?_)
  have hc : ∀ P : HeightOneSpectrum (𝓞 E), Nat.card (𝓞 E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal :=
    fun P => by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Set.ncard_univ, Nat.card_prod, Nat.card_pi, Nat.card_pi]
  simp only [Nat.card_fun, hc, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul, ← sq]
  rw [Finset.prod_coe_sort ST (fun P => Ideal.absNorm P.asIdeal ^ n),
    Finset.prod_coe_sort SG (fun P => Ideal.absNorm P.asIdeal ^ (n ^ 2))]

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
theorem card_classes_le : ∀ (X : Fields), X.Ok → ∀ (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 X.E))), Finite (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG (E := X.E) (n := n) (SG := SG)))) (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) ∧ (Nat.card (MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG (E := X.E) (n := n) (SG := SG)))) (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) : ℝ) ≤ (3 * ((Module.finrank ℚ X.E : ℝ) ^ 2 * (n : ℝ) ^ 4 * (|(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ X.E * n ^ 2) * (∏ P ∈ ST, (Ideal.absNorm P.asIdeal : ℝ) ^ n) * ∏ w ∈ SG, (Ideal.absNorm w.asIdeal : ℝ) ^ (n ^ 2) := by
  intro X hX n ST SG
  classical
  have hΓ : ∀ g : UF X.E n, (g, (1 : GLG (E := X.E) (n := n) (SG := SG))) ∈
      (⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG (E := X.E) (n := n) (SG := SG))) := fun g =>
    ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩
  refine ⟨DecoSet.finite_orbits (posStar_of_conj hX.conjE) _ hΓ, ?_⟩
  have := hX.realF
  have := hX.cplxE
  have : Algebra.IsQuadraticExtension X.F X.E := ⟨hX.rankE⟩
  have : IsCMField X.E := IsCMField.ofCMExtension X.F X.E
  have hs : ∀ x : X.E, star x = IsCMField.complexConj X.E x := by
    intro x
    let φ : X.E →+* ℂ := (IsAlgClosed.lift : X.E →ₐ[ℚ] ℂ).toRingHom
    apply φ.injective
    rw [hX.conjE, IsCMField.complexEmbedding_complexConj]
  obtain ⟨Rs, hR, H⟩ := GlobalTheory.exists_finset_decoSet_lattice_reps X.E hs n
  let fib : Submodule (𝓞 X.E) (Sp X.E n) → Finset (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) := fun N =>
    (card_fibre_le ST SG N).1.toFinset
  let B : ℕ := (∏ P ∈ ST, Ideal.absNorm P.asIdeal ^ n) * ∏ w ∈ SG, Ideal.absNorm w.asIdeal ^ (n ^ 2)
  have hfib : ∀ N, (fib N).card ≤ B := fun N => by
    rw [← Set.ncard_eq_toFinset_card _ (card_fibre_le ST SG N).1]
    exact (card_fibre_le ST SG N).2
  have hS : (Rs.biUnion fib).card ≤ Rs.card * B := Finset.card_biUnion_le_card_mul _ _ _ fun N _ => hfib N
  have hsurj : Function.Surjective (fun d : ↥(Rs.biUnion fib) => (Quotient.mk'' d.1 :
      MulAction.orbitRel.Quotient ((⊤ : Subgroup (UF X.E n)).prod (⊥ : Subgroup (GLG (E := X.E) (n := n) (SG := SG))))
        (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)))) := by
    intro c
    induction c using Quotient.inductionOn' with
    | h d =>
      obtain ⟨g, hg⟩ := H ST SG d
      refine ⟨⟨(g, (1 : GLG (E := X.E) (n := n) (SG := SG))) • d, Finset.mem_biUnion.2 ⟨_, hg, ?_⟩⟩, ?_⟩
      · exact (Set.Finite.mem_toFinset _).2 rfl
      · apply Quotient.sound'
        rw [MulAction.orbitRel_apply]
        exact ⟨⟨(g, 1), hΓ g⟩, rfl⟩
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := ↥(Rs.biUnion fib)), Fintype.card_coe] at h1
  have h2 : ((Rs.card * B : ℕ) : ℝ) = Rs.card * (∏ P ∈ ST, (Ideal.absNorm P.asIdeal : ℝ) ^ n) *
      ∏ w ∈ SG, (Ideal.absNorm w.asIdeal : ℝ) ^ (n ^ 2) := by
    simp only [B]
    push_cast
    ring
  refine (Nat.cast_le.2 (h1.trans hS)).trans (h2.le.trans ?_)
  gcongr

end GlobalTheory.DecoClassCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumePerRankLeNegSlopeScaled
section -- merged from Development.AbelianVarietyTheory.Counterexamples.RotationExamples.MeasureFailsForLargeConstant
open Finset Module NumberField Formalism.HN Formalism.L2.Indef Formalism.L2.Indef.Tree

noncomputable section

namespace GlobalTheory.MeasureLeaf

section Bound₂

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def OneConstant {d : ℕ} (X X' : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (c : InfinitePlace K → ℝ) : Prop :=
  ∀ v, 0 < c v ∧ ∀ x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y =
    (c v : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X' v x y

theorem lcv_of_oneConstant [_root_.NumberField.IsTotallyComplex K] {d : ℕ} (hd : 0 < d)
    (X X' : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det)
    (c : InfinitePlace K → ℝ) (hc : OneConstant X X' c) (M : Submodule (𝓞 K) (Fin d → K))
    (hM : Submodule.IsFullLattice K M) :
    Formalism.DivisionValues.lcv X M / (d : ℝ) = Formalism.DivisionValues.lcv X' M / (d : ℝ) + 2 / (finrank ℚ K : ℝ) * ∑ v, Real.log (c v) := by
  have hli : LinearIndependent K (fun i : Fin d => (Pi.basisFun K (Fin d)) i) := (Pi.basisFun K (Fin d)).linearIndependent
  rw [(Formalism.DivisionValues.covolume_via_basis K d X hX M hM _ hli).2, (Formalism.DivisionValues.covolume_via_basis K d X' hX' M hM _ hli).2]
  have hv : ∀ v, Real.log (Formalism.DivisionValues.gram X v (fun i : Fin d => (Pi.basisFun K (Fin d)) i)).det.re =
      d * Real.log (c v) + Real.log (Formalism.DivisionValues.gram X' v (fun i : Fin d => (Pi.basisFun K (Fin d)) i)).det.re := by
    intro v
    have e : Formalism.DivisionValues.gram X v (fun i : Fin d => (Pi.basisFun K (Fin d)) i) =
        (c v : ℂ) • Formalism.DivisionValues.gram X' v (fun i : Fin d => (Pi.basisFun K (Fin d)) i) := by
      ext a b
      simp only [Formalism.DivisionValues.gram, gramPl, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      exact (hc v).2 _ _
    have hne : (Formalism.DivisionValues.gram X' v (fun i : Fin d => (Pi.basisFun K (Fin d)) i)).det.re ≠ 0 := by
      have g : Formalism.DivisionValues.gram X' v (fun i : Fin d => (Pi.basisFun K (Fin d)) i) =
          ((X' v)⁻¹).conjTranspose * (X' v)⁻¹ := by
        ext a b
        simp [Formalism.DivisionValues.gram, gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Matrix.mul_apply,
          Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite v.embedding]
      rw [g, Matrix.det_mul, Matrix.det_conjTranspose]
      have hu : ((X' v)⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det _ (hX' v)).ne_zero
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact (Complex.normSq_pos.mpr hu).ne'
    rw [e, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
      Real.log_mul (pow_pos (hc v).1 d).ne' hne, Real.log_pow]
  simp only [hv, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

end Bound₂

end GlobalTheory.MeasureLeaf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumePerRankLeNegSlopeScaled
open NumberField

noncomputable section

namespace GlobalTheory.CovolCore

section Transport

variable {R V W E F : Type} [Ring R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem rk_deg_transport (ρ : V →+ E) (σ : W →+ F) (T : V →+ W) {A : Submodule R V} {B : Submodule R W}
    (hA : Formalism.HN.IsLat ρ A) (hB : Formalism.HN.IsLat σ B)
    (hAB : ∀ y, y ∈ B ↔ ∃ x ∈ A, T x = y) (hn : ∀ x ∈ A, ‖σ (T x)‖ = ‖ρ x‖) :
    Formalism.HN.rk σ B = Formalism.HN.rk ρ A ∧ Formalism.HN.deg σ B = Formalism.HN.deg ρ A := by
  let f : A.toAddSubgroup →+ E := ρ.comp A.toAddSubgroup.subtype
  let g : A.toAddSubgroup →+ F := (σ.comp T).comp A.toAddSubgroup.subtype
  have h1 : ∀ y, y ∈ Formalism.HN.zl ρ A ↔ ∃ m, f m = y :=
    fun y => ⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩
  have h2 : ∀ y, y ∈ Formalism.HN.zl σ B ↔ ∃ m, g m = y := fun y =>
    ⟨fun ⟨m, hm, e⟩ => by
      obtain ⟨x, hx, rfl⟩ := (hAB m).1 hm
      exact ⟨⟨x, hx⟩, e⟩, fun ⟨m, e⟩ => ⟨T m.1, (hAB _).2 ⟨m.1, m.2, rfl⟩, e⟩⟩
  have hn' : ∀ m, ‖f m‖ = ‖g m‖ := fun m => (hn m.1 m.2).symm
  haveI := hA.2
  haveI := hB.2
  refine ⟨?_, ?_⟩
  · have hf : Function.Injective f := fun x y h => Subtype.ext (hA.1 x.2 y.2 h)
    have hg : Function.Injective g := fun x y h =>
      hf (Formalism.HN.QuotientRealization.eq_of_norm_eq g f (fun m => (hn' m).symm) h)
    have e1 : Formalism.HN.zl ρ A = LinearMap.range f.toIntLinearMap := Submodule.ext h1
    have e2 : Formalism.HN.zl σ B = LinearMap.range g.toIntLinearMap := Submodule.ext h2
    unfold Formalism.HN.rk Formalism.F.rk
    rw [e1, e2, ← (LinearEquiv.ofInjective f.toIntLinearMap hf).finrank_eq,
      ← (LinearEquiv.ofInjective g.toIntLinearMap hg).finrank_eq]
  · unfold Formalism.HN.deg Formalism.F.deg
    rw [Formalism.HN.QuotientRealization.covol_eq_of_norm_eq f g _ _ h1 h2 hn']

end Transport

theorem cnorm_smul {ι : Type} [Fintype ι] (s : ℝ) (hs : 0 ≤ s) (u : ι → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm ((s : ℂ) • u) = s * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, mul_pow,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

end GlobalTheory.CovolCore

namespace GlobalTheory.CovolCore

theorem lcv_div_le_neg_slope_sq : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ), GlobalTheory.AllWt.HasGram N →
    ∀ (L : Submodule (𝓞 K) V) (d : ℕ), 0 < d → ∀ (b : Fin d → V), LinearIndependent K b →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range b)) →
    ∀ (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (s : ℝ), 0 < s → s ≤ 1 → (∀ v, IsUnit (X v).det) →
    (∀ v (c : Fin d → K), Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v c = s * N v.embedding (∑ k, c k • b k)) →
    Submodule.IsFullLattice K (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) →
    Formalism.DivisionValues.lcv X (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) / (d : ℝ) ≤
      -GlobalTheory.AllWt.slope_sq N L := by
  intro K V _ _ _ _ _ _ _ _ N hN L d hd b hb hLb X s hs0 hs1 hX hnorm hM
  set φ := Fintype.linearCombination K b with hφ
  set M := L.comap (φ.restrictScalars (𝓞 K)) with hMdef
  have hφa : ∀ c : Fin d → K, φ c = ∑ k, c k • b k := fun c => Fintype.linearCombination_apply K b c
  let X' : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ := fun v => (s : ℂ) • X v
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hX' : ∀ v, IsUnit (X' v).det := fun v => by
    show IsUnit ((s : ℂ) • X v).det
    rw [Matrix.det_smul]
    exact ((Ne.isUnit hs').pow _).mul (hX v)
  have hfc : ∀ v c, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v c =
      (s : ℂ) • Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X' v c := by
    intro v c
    have e : X' v = (Units.mk0 (s : ℂ) hs') • X v := rfl
    simp only [Formalism.HermitianLatticesTheory.fcoord]
    rw [e, Matrix.inv_smul' (X v) (Units.mk0 (s : ℂ) hs') (hX v), Units.smul_def, Matrix.smul_mulVec, smul_smul,
      Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel₀ hs', one_smul]
  have hOC : GlobalTheory.MeasureLeaf.OneConstant X X' (fun _ => s ^ 2) := fun v =>
    ⟨by positivity, fun x y => by
      simp only [Formalism.HermitianLatticesTheory.majAt, hfc, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_mul', Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring⟩
  have hn' : ∀ v c, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X' v c = N v.embedding (φ c) := by
    intro v c
    have h := hnorm v c
    simp only [Formalism.HermitianLatticesTheory.normAt, hfc, cnorm_smul s hs0.le] at h
    rw [hφa]
    exact mul_left_cancel₀ hs0.ne' h
  have h1 := GlobalTheory.MeasureLeaf.lcv_of_oneConstant hd X X' hX hX' (fun _ => s ^ 2) hOC M hM
  have h2 := Formalism.ExtensionFiltration.lcvMu K d hd X' hX' M hM
  have hlog : 2 / (Module.finrank ℚ K : ℝ) * ∑ v : InfinitePlace K, Real.log (s ^ 2) ≤ 0 := by
    refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun v _ => ?_)
    exact Real.log_nonpos (sq_nonneg _) (by nlinarith)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hMfg : M.FG := hM.toIsLattice.fg
  have hML : ∀ y, y ∈ L ↔ ∃ x ∈ M, φ x = y := fun y =>
    ⟨fun hy => by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hLb y hy)
      refine ⟨c, ?_, by rw [hφa, hc]⟩
      show φ c ∈ L
      rw [hφa, hc]; exact hy,
     fun ⟨x, hx, e⟩ => e ▸ hx⟩
  have hLM : L = M.map (φ.restrictScalars (𝓞 K)) := by
    ext y
    rw [hML y, Submodule.mem_map]
    rfl
  have hLfg : L.FG := by rw [hLM]; exact hMfg.map _
  obtain ⟨⟨n, ⟨b0, X0⟩, hG⟩⟩ := id hN
  change GlobalTheory.AllWt.IsGram b0 X0 N at hG
  rw [GlobalTheory.AllWt.slope_sq_eq hG hLfg]
  have hlatM := (Formalism.HN.plLat K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X' hX' M hMfg).1
  have hlatL := (Formalism.HN.plLat K V (Fin n) b0 X0 (fun v => (hG v).1) L hLfg).1
  have hnr : ∀ x ∈ M, ‖Formalism.HermitianLatticesTheory.realize b0 X0 (φ.toAddMonoidHom x)‖ =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin d)) X' x‖ := fun x _ => by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), GlobalTheory.AllWt.norm_realize_sq, GlobalTheory.AllWt.norm_realize_sq]
    exact Finset.sum_congr rfl fun v _ => by rw [(hG v).2, hn' v x]; rfl
  obtain ⟨e1, e2⟩ := rk_deg_transport (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin d)) X')
    (Formalism.HermitianLatticesTheory.realize b0 X0) φ.toAddMonoidHom hlatM hlatL hML hnr
  have key : Formalism.HN.muDef (Pi.basisFun K (Fin d)) X' M = Formalism.HN.muDef b0 X0 L := by
    unfold Formalism.HN.rk at e1
    unfold Formalism.HN.deg at e2
    unfold Formalism.HN.muDef Formalism.HN.slope Formalism.F.slope
    rw [e1, e2]
  have h3 : Formalism.DivisionValues.lcv X' M / (d : ℝ) = -Formalism.HN.muDef (Pi.basisFun K (Fin d)) X' M := by
    rw [h2]; field_simp
  rw [h1, h3, key]
  linarith

end GlobalTheory.CovolCore
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumePerRankLeNegSlopeScaledStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolumePerRank_le_neg_slope_scaled : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ), GlobalTheory.AllWt.HasGram N →
    ∀ (L : Submodule (𝓞 K) V) (d : ℕ), 0 < d → ∀ (b : Fin d → V), LinearIndependent K b →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range b)) →
    ∀ (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (s : ℝ), 0 < s → s ≤ 1 → (∀ v, IsUnit (X v).det) →
    (∀ v (c : Fin d → K), Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v c = s * N v.embedding (∑ k, c k • b k)) →
    Submodule.IsFullLattice K (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) →
    Formalism.DivisionValues.lcv X (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) / (d : ℝ) ≤ -GlobalTheory.AllWt.slope_sq N L := by
  first | exact @GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq | exact GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq | (intros; apply GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq <;> first | assumption | exact (show Submodule.IsFullLattice _ _ from by assumption).toIsLattice)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormEqFiniteIdeleModule
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormEqFiniteIdeleModule
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal.InvIdealNorm

open scoped GlobalTheory.Idele

variable {K : Type} [Field K] [NumberField K]

theorem eq_inv_smul_one {t : (Af K)ˣ} {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h : IsInvIdealOf t 𝔞) :
    𝔞 = t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  have h' := GlobalTheory.LatVal.CurveTransport.isInvIdealOf_inv_smul_one t
  ext x
  rw [h x, h' x]

theorem finprod_absNorm_zpow_count {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count K v I =
      ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  let g : FractionalIdeal (𝓞 K)⁰ K →*₀ ℝ :=
    (Rat.castHom ℝ).toMonoidWithZeroHom.comp FractionalIdeal.absNorm
  have hg : ∀ J, g J = ((FractionalIdeal.absNorm J : ℚ) : ℝ) := fun _ => rfl
  conv_rhs => rw [← hg, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
  rw [map_finprod g]
  · refine finprod_congr fun v => ?_
    rw [map_zpow₀, hg, FractionalIdeal.coeIdeal_absNorm]
    simp
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset fun v hv h0 => hv ?_
    simp only [h0, zpow_zero]

end GlobalTheory.LatVal.InvIdealNorm


open GlobalTheory.LatVal.InvIdealNorm in
open scoped GlobalTheory.Idele in
theorem GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ)
    (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h : IsInvIdealOf t 𝔞), nrm 𝔞 = modF t := by
  intro K _ _ t 𝔞 h
  have e := eq_inv_smul_one h
  rw [GlobalTheory.Idele.smul_one_eq] at e
  have h0 : 𝔞 ≠ 0 := e ▸ GlobalTheory.Idele.idealOf_ne_zero _
  rw [nrm, ← finprod_absNorm_zpow_count h0, modF]
  refine finprod_congr fun v => ?_
  congr 1
  rw [e, GlobalTheory.Idele.count_idealOf, GlobalTheory.Idele.ord_vw_inv, GlobalTheory.Idele.ord_vw, neg_neg]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormEqFiniteIdeleModuleStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdealNorm_eq_finiteIdeleModule : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h : IsInvIdealOf t 𝔞), nrm 𝔞 = modF t := by
  first | exact @GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf | exact GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf | (intros; apply GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMonicPolynomialOfUnitRelation
open scoped TensorProduct
open IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.OddLocalNorm

theorem exists_eq_of_finite (O : Type) {S : Type} [CommRing O] [HenselianLocalRing O]
    [Finite (ResidueField O)] [CommRing S] [Algebra O S] [Module.Finite O S]
    (h2 : IsUnit (2 : O)) {m d : S} (hm : IsUnit m) (hd : IsUnit d) :
    ∃ a b : S, m = a * a - d * (b * b) := by
  let T := QuadraticAlgebra S d 0
  haveI : Module.Finite O T := Module.Finite.trans S T
  let I : Ideal T := (maximalIdeal O).map (algebraMap O T)
  have hI : I ≤ (⊥ : Ideal T).jacobson := by
    refine le_sInf fun M hM => Ideal.map_le_iff_le_comap.2 ?_
    haveI := hM.2
    exact (eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) M)).ge
  haveI : HenselianRing T I := GlobalTheory.henselianRing_of_finite O I hI
  haveI : Finite (O ⧸ maximalIdeal O) := inferInstanceAs (Finite (ResidueField O))
  haveI : Module.Finite O (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O I).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (O ⧸ maximalIdeal O) (T ⧸ I) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Finite (T ⧸ I) := Module.finite_of_finite (O ⧸ maximalIdeal O)
  have hc : ∀ s : S, starRingEnd T (algebraMap S T s) = algebraMap S T s := by
    intro s
    ext <;> simp [T, starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hcO : (starRingEnd T).comp (algebraMap O T) = algebraMap O T := by
    ext1 r
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply O S T, hc]
  have hcI : I ≤ I.comap (starRingEnd T) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hcO]
    exact Ideal.le_comap_map
  have h2S : IsUnit (2 : S) := by
    simpa only [map_ofNat] using h2.map (algebraMap O S)
  obtain ⟨x, hx⟩ := GlobalTheory.HenselianNorm.exists_norm_eq T I (starRingEnd T)
    (fun x => star_star x) (fun x hx => hcI hx)
    ⟨⟨0, 1⟩, by
      have h : ((⟨0, 1⟩ : T) - starRingEnd T ⟨0, 1⟩) * ((⟨0, 1⟩ : T) - starRingEnd T ⟨0, 1⟩)
          = algebraMap S T (2 * 2 * d) := by
        ext <;> simp [T, starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
        ring
      exact isUnit_of_mul_isUnit_left (h ▸ ((h2S.mul h2S).mul hd).map (algebraMap S T))⟩
    (algebraMap S T m) (hc m) (hm.map _)
  refine ⟨x.re, x.im, ?_⟩
  have := congrArg QuadraticAlgebra.re hx
  simp [T, starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this
  linear_combination -this

theorem exists_eq_of_isIntegral (O : Type) {A : Type} [CommRing O] [HenselianLocalRing O]
    [Finite (ResidueField O)] [CommRing A] [Algebra O A]
    (h2 : IsUnit (2 : O)) {m m' d d' : A} (hm : m * m' = 1) (hd : d * d' = 1)
    (im : IsIntegral O m) (im' : IsIntegral O m') (id : IsIntegral O d) (id' : IsIntegral O d') :
    ∃ a b : A, m = a * a - d * (b * b) := by
  let S := Algebra.adjoin O ({m, m', d, d'} : Set A)
  haveI : Module.Finite O S := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.toFinite _) (by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption)
  have h1 : m ∈ S := Algebra.subset_adjoin (by simp)
  have h1' : m' ∈ S := Algebra.subset_adjoin (by simp)
  have h3 : d ∈ S := Algebra.subset_adjoin (by simp)
  have h3' : d' ∈ S := Algebra.subset_adjoin (by simp)
  obtain ⟨a, b, h⟩ := exists_eq_of_finite O h2 (m := (⟨m, h1⟩ : S)) (d := ⟨d, h3⟩)
    (IsUnit.of_mul_eq_one ⟨m', h1'⟩ (Subtype.ext hm)) (IsUnit.of_mul_eq_one ⟨d', h3'⟩ (Subtype.ext hd))
  exact ⟨a, b, congrArg Subtype.val h⟩

end GlobalTheory.OddLocalNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqLeOfNoShortVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqLeOfNoShortVector
open NumberField GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.SlopeMink

theorem sum_embeddings_eq_two_mul {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (g : (K →+* ℂ) → ℝ) (hg : ∀ σ, g ((starRingEnd ℂ).comp σ) = g σ) :
    ∑ σ : K →+* ℂ, g σ = 2 * ∑ v : InfinitePlace K, g v.embedding := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun σ => InfinitePlace.mk σ) g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hc : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w), g σ = g w.embedding := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [← hσ.2]
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ := by
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [this, hg]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two, nsmul_eq_mul]
  norm_num

theorem slopeMax_sq_le_of_no_short : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V)
    (La : ℝ), HasGram N → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → L.FG → L ≠ ⊥ →
    (∀ x ∈ L, x ≠ 0 → -La ≤ (∑ σ : K →+* ℂ, Real.log (N σ x)) / (Module.finrank ℚ K : ℝ)) →
    slopeMax_sq N L ≤ 2 * La + Real.log (Module.finrank K V : ℝ) +
      Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  intro K V _ _ _ _ _ _ _ N L La hG hconj hfg h0 hshort
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, hX⟩ := hG.some
  rw [(slopeMax_slopeMin_eq hX hfg h0).1]
  have hXu : ∀ v, IsUnit (X v).det := fun v => (hX v).1
  have hnf : Module.finrank ℚ K = 2 * Formalism.HN.nPl K := Formalism.HN.sizeMu_finrank_eq K
  have hf : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have : 0 < Formalism.HN.nPl K := Fintype.card_pos
    exact_mod_cast this
  have hmink := Formalism.ExtensionFiltration.muMaxMinkowski K V (Fin n) b X hXu L La hfg h0 (by
    intro x hx hx0
    have h1 := hshort x hx hx0
    rw [sum_embeddings_eq_two_mul (fun σ => Real.log (N σ x)) (fun σ => by simp only [hconj])] at h1
    have e : ∀ v : InfinitePlace K, Real.log (N v.embedding x) = Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) :=
      fun v => by rw [(hX v).2 x]
    simp only [e] at h1
    rw [hnf] at h1
    push_cast at h1
    have : (2 * ∑ v : InfinitePlace K, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x)) / (2 * (Formalism.HN.nPl K : ℝ)) =
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) := by
      field_simp
    linarith)
  haveI : Module.Finite K V := Module.Finite.of_basis b
  have hj : 0 < Formalism.HN.rkK L := by
    have h : Submodule.span K (L : Set V) ≠ ⊥ := by
      intro h
      apply h0
      rw [Submodule.span_eq_bot] at h
      exact (Submodule.eq_bot_iff _).2 (fun x hx => h x hx)
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)
  have hle : (Formalism.HN.rkK L : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast Submodule.finrank_le _
  have hlog : Real.log (Formalism.HN.rkK L : ℝ) ≤ Real.log (Module.finrank K V : ℝ) :=
    Real.log_le_log (by exact_mod_cast hj) hle
  have hd : Formalism.HN.logDisc K = Real.log |(discr K : ℝ)| := rfl
  rw [hd] at hmink
  linarith

end GlobalTheory.SlopeMink
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqLeOfNoShortVectorStatement
open NumberField GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSlope_sq_le_of_no_short_vector : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (La : ℝ), HasGram N → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → L.FG → L ≠ ⊥ → (∀ x ∈ L, x ≠ 0 → -La ≤ (∑ σ : K →+* ℂ, Real.log (N σ x)) / (Module.finrank ℚ K : ℝ)) → slopeMax_sq N L ≤ 2 * La + Real.log (Module.finrank K V : ℝ) + Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  first | exact @GlobalTheory.SlopeMink.slopeMax_sq_le_of_no_short | exact GlobalTheory.SlopeMink.slopeMax_sq_le_of_no_short | (intros; apply GlobalTheory.SlopeMink.slopeMax_sq_le_of_no_short <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOnEqZeroOfEqOne
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory

open TopForm

namespace TopForm

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} {U : Y.Opens}

theorem dOn_eq_zero_of_eq_one (f : Fin D → Γ(Y, U)) (b : Fin D) (hb : f b = 1) : dOn p f = 0 := by
  rw [dOn, dForm_eq]
  refine AlternatingMap.map_coord_zero _ b ?_
  let := (algX p U).toAlgebra
  rw [hb]
  exact (KaehlerDifferential.D k Γ(Y, U)).map_one_eq_zero

theorem jacOn_of_eq_one (f : Fin (D + 1) → Γ(Y, U)) (i : Fin (D + 1)) (hi : f i = 1) :
    jacOn p f = (-1 : Γ(Y, U)) ^ (i : ℕ) • dOn p fun b => f (i.succAbove b) := by
  rw [jacOn_eq, Finset.sum_eq_single i, hi, mul_one]
  · intro a _ ha
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq (Ne.symm ha)
    rw [dOn_eq_zero_of_eq_one _ b (by rw [hb, hi]), smul_zero]
  · intro h
    exact (h (Finset.mem_univ i)).elim

theorem isUnit_of_affine {f : Γ(Y, U)}
    (h : ∀ W : Y.Opens, IsAffineOpen W → ∀ hW : W ≤ U, IsUnit (resG Y hW f)) : IsUnit f := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => ?_
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hx
  have := (h W hW hWU).map (Y.presheaf.germ W x hxW).hom
  rwa [show (Y.presheaf.germ W x hxW).hom (resG Y hWU f) = (Y.presheaf.germ U x hx).hom f from
    Y.presheaf.germ_res_apply (homOfLE hWU) x hxW f] at this

theorem isFreeGen_dForm_X (k : Type) [CommRing k] (D : ℕ) : IsFreeGen (MvPolynomial (Fin D) k)
    (dForm (algebraMap k (MvPolynomial (Fin D) k)) (X : Fin D → _)) := by
  have key (inst : Algebra k (MvPolynomial (Fin D) k))
      (e : inst = AddMonoidAlgebra.algebra) :
      IsFreeGen (MvPolynomial (Fin D) k) (@dWedge k _ _ _ inst D X) := by
    subst e
    have := isFreeGen_ιMulti (KaehlerDifferential.mvPolynomialBasis k (Fin D))
    rwa [funext (KaehlerDifferential.mvPolynomialBasis_apply k (Fin D))] at this
  exact key _ (Algebra.algebra_ext _ _ fun _ => rfl)

end TopForm

namespace ProjSpace

variable (R : Type) [CommRing R] (N : ℕ)

theorem isFrame_dOn_ratio (i : Fin (N + 1)) :
    IsFrame (dOn (PSpace.str R N) fun b : Fin N => ratio R N i (i.succAbove b)) := by
  refine ⟨isAffineOpen_chart R N i, ?_⟩
  let e : MvPolynomial (Fin N) R ≃ₐ[R] Γ(PSpace R N, chart R N i) :=
    (renameEquiv R (finSuccAboveEquiv i)).trans (chartAlgEquiv R N i)
  have he : (e : MvPolynomial (Fin N) R →+* _).comp (algebraMap R _) =
      algX (PSpace.str R N) (chart R N i) := RingHom.ext fun r => e.commutes r
  have := (isFreeGen_dForm_X R N).formMap (RingHom.Etale.of_bijective e.bijective) he
  rw [formMap_dForm] at this
  convert this using 3 with b
  exact ((congrArg (chartAlgEquiv R N i) (rename_X _ b)).trans
    (chartAlgEquiv_X R N i (finSuccAboveEquiv i b))).symm

theorem isUnit_jacSec_coord [SmoothOfRelativeDimension N (PSpace.str R N)]
    (K : CanonLB (PSpace.str R N) N) (c : (K.adj (O1 R N) (N + 1)).ι) :
    IsUnit ((K.jacSec (coord R N)).f c) := by
  refine isUnit_of_affine fun W hW h => ?_
  have l := h.trans (K.adj_U_le _ c)
  have h₂ : W ≤ chart R N (c.2 PUnit.unit) := l.trans inf_le_right
  rw [K.resG_jacSec_f _ c h (l.trans inf_le_left) h₂]
  change IsUnit (K.coeff _ _ (jacOn _ (ratioOn W (c.2 PUnit.unit) h₂)))
  rw [jacOn_of_eq_one _ (c.2 PUnit.unit) (ratioOn_self (hi := h₂)), map_smul, smul_eq_mul]
  refine (isUnit_one.neg.pow _).mul ((K.isUnit_jacobian_iff _ hW _ _).2 ?_)
  have := (isFrame_dOn_ratio R N (c.2 PUnit.unit)).res hW h₂
  rw [resForm_dOn] at this
  exact this

end ProjSpace

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentLowerRowsLeviSetClosedSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentLowerRowsLeviSetClosedSubgroup
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

open MeasureTheory in
open scoped FourierTransform ContDiff in
private theorem mem_levSet_iff_unitriangular_below_r {n r : ℕ} {g : GL (Fin n) ℂ} :
    g ∈ _root_.GlobalTheory.JSW.levSet n r ↔
      ∀ i : Fin n, r ≤ (i : ℕ) →
        (∀ j < i, (g : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧ (g : Matrix (Fin n) (Fin n) ℂ) i i = 1 :=
  Iff.rfl

open MeasureTheory in
open scoped FourierTransform ContDiff in
private theorem mul_apply_eq_apply_of_unitriangular_index_le {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    {i : Fin n} (hA : (∀ j < i, A i j = 0) ∧ A i i = 1)
    (hB : ∀ k, i < k → ∀ j < k, B k j = 0) (j : Fin n) (hj : j ≤ i) :
    (A * B) i j = B i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hA.2, one_mul]
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hA.1 k hk, zero_mul]
    · rw [hB k hk j (lt_of_le_of_lt hj hk), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h


open MeasureTheory in
open scoped FourierTransform ContDiff in
theorem _root_.GlobalTheory.JSW.levSet_closed_subgroup : ∀ (n r : ℕ),
    (∀ g ∈ _root_.GlobalTheory.JSW.levSet n r, ∀ h ∈ _root_.GlobalTheory.JSW.levSet n r,
      g * h ∈ _root_.GlobalTheory.JSW.levSet n r) ∧
    (∀ g ∈ _root_.GlobalTheory.JSW.levSet n r, g⁻¹ ∈ _root_.GlobalTheory.JSW.levSet n r) ∧
    (∀ u ∈ _root_.GlobalTheory.SmGL.unipB ℂ (Fin n), u ∈ _root_.GlobalTheory.JSW.levSet n r) ∧
    IsClosed (_root_.GlobalTheory.JSW.levSet n r) := by
  intro n r
  refine ⟨fun g hg h hh => ?_, fun g hg => ?_, fun u hu => ?_, ?_⟩
  · rw [mem_levSet_iff_unitriangular_below_r] at hg hh ⊢
    intro i hi
    have hrow := mul_apply_eq_apply_of_unitriangular_index_le (hg i hi) (B := (h : Matrix (Fin n) (Fin n) ℂ))
      fun k hk => (hh k (hi.trans (Fin.lt_iff_val_lt_val.mp hk).le)).1
    rw [Units.val_mul]
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [hrow j hj.le]
      exact (hh i hi).1 j hj
    · rw [hrow i le_rfl]
      exact (hh i hi).2
  · rw [mem_levSet_iff_unitriangular_below_r] at hg ⊢
    have hgh : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
      Units.mul_inv g
    have key : ∀ m : ℕ, ∀ i : Fin n, r ≤ (i : ℕ) → n - (i : ℕ) ≤ m →
        (∀ j < i, ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = 0) ∧
          ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1 := by
      intro m
      induction m with
      | zero =>
        intro i _ hm
        have := i.isLt
        omega
      | succ m ih =>
        intro i hi hm
        have hrow := mul_apply_eq_apply_of_unitriangular_index_le (hg i hi)
          (B := ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
          fun k hk => by
            have hik := Fin.lt_iff_val_lt_val.mp hk
            exact (ih k (hi.trans hik.le) (by omega)).1
        refine ⟨fun j hj => ?_, ?_⟩
        · rw [← hrow j hj.le, hgh, Matrix.one_apply_ne hj.ne']
        · rw [← hrow i le_rfl, hgh, Matrix.one_apply_eq]
    exact fun i hi => key n i hi (Nat.sub_le _ _)
  · rw [_root_.GlobalTheory.SmGL.mem_unipB] at hu
    exact fun i _ => ⟨fun j hj => hu.1 i j hj, hu.2 i⟩
  · have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) i j :=
      fun i j => Units.continuous_val.matrix_elem i j
    have hset : _root_.GlobalTheory.JSW.levSet n r = ⋂ i : Fin n, ⋂ (_ : r ≤ (i : ℕ)),
        ((⋂ j : Fin n, ⋂ (_ : j < i), {g : GL (Fin n) ℂ | (g : Matrix (Fin n) (Fin n) ℂ) i j = 0}) ∩
          {g : GL (Fin n) ℂ | (g : Matrix (Fin n) (Fin n) ℂ) i i = 1}) := by
      ext g
      simp only [mem_levSet_iff_unitriangular_below_r, Set.mem_iInter, Set.mem_inter_iff,
        Set.mem_setOf_eq]
    rw [hset]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      (isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hc i j) continuous_const).inter
        (isClosed_eq (hc i i) continuous_const)

end GlobalTheory.JSW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentLowerRowsLeviSetClosedSubgroupStatement
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup : ∀ (n r : ℕ), (∀ g ∈ levSet n r, ∀ h ∈ levSet n r, g * h ∈ levSet n r) ∧ (∀ g ∈ levSet n r, g⁻¹ ∈ levSet n r) ∧ (∀ u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n), u ∈ levSet n r) ∧ IsClosed (levSet n r) := by
  first | exact @GlobalTheory.JSW.levSet_closed_subgroup | exact GlobalTheory.JSW.levSet_closed_subgroup | (intros; apply GlobalTheory.JSW.levSet_closed_subgroup <;> assumption)
end
end
