module

public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntitoneFiltrationExistsAdaptedLinearIndepSet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SummableNormCosetOut
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteCocycles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr
open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory.ComplexEmbedding

open Cardinal IsLocalRing

theorem mk_le_continuum_of_finite_residueField (V : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [Finite (ResidueField V)] : #V ≤ 𝔠 := by
  have hfin : ∀ n : ℕ, Finite (V ⧸ maximalIdeal V ^ n) := fun n =>
    haveI : Finite (V ⧸ maximalIdeal V) := inferInstanceAs (Finite (ResidueField V))
    Ideal.finite_quotient_pow (maximalIdeal V).fg_of_isNoetherianRing n
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n => mk_le_aleph0).trans ?_
  simp

theorem exists_embedding_of_mk_le_continuum {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (hΩ : #Ω ≤ 𝔠) (σ : K →+* ℂ) :
    ∃ P : Ω →+* ℂ, P.comp (algebraMap K Ω) = σ := by
  let _ : Algebra K ℂ := σ.toAlgebra
  have hK : #K ≤ ℵ₀ := by
    have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
    simpa [Cardinal.mkRat] using this
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K Ω
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have hst : #s ≤ #t := by
    have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hK
      (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
    rw [← h1, Cardinal.mk_complex]
    exact (Cardinal.mk_subtype_le _).trans hΩ
  obtain ⟨e⟩ := hst
  have hv : AlgebraicIndependent K (((↑) : t → ℂ) ∘ e) := ht.1.comp e e.injective
  let f : IntermediateField.adjoin K (Set.range ((↑) : s → Ω)) →ₐ[K] ℂ :=
    (IntermediateField.val _).comp (hv.aevalEquivField.toAlgHom.comp hs.1.reprField)
  have halg := hs.isAlgebraic_field
  obtain ⟨φ, -⟩ := IntermediateField.exists_algHom_of_splits' f
    (fun (x : Ω) => ⟨(Algebra.IsAlgebraic.isAlgebraic
      (R := IntermediateField.adjoin K (Set.range ((↑) : s → Ω))) x).isIntegral, IsAlgClosed.splits _⟩)
  refine ⟨φ.toRingHom, ?_⟩
  ext x
  exact φ.commutes x

theorem exists_embedding_fractionField :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : CDVR), T.FinRes →
      ∀ io : K →+* T.Fr, ∃ ι : T.Fr →+* ℂ, ι.comp io = σ := by
  intro K _ _ σ T hT io
  haveI : Finite (ResidueField T.V) := hT
  have hV := mk_le_continuum_of_finite_residueField T.V
  have hF : #T.Fr ≤ 𝔠 := by
    rw [show #T.Fr = #T.V from IsFractionRing.cardinalMk T.V T.Fr]
    exact hV
  exact @exists_embedding_of_mk_le_continuum K T.Fr _ _ _ io.toAlgebra hF σ

end GlobalTheory.ComplexEmbedding
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvrStatement
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_embedding_fractionField_cdvr : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : CDVR), T.FinRes → ∀ io : K →+* T.Fr, ∃ ι : T.Fr →+* ℂ, ι.comp io = σ := by
  first | exact @GlobalTheory.ComplexEmbedding.exists_embedding_fractionField | exact GlobalTheory.ComplexEmbedding.exists_embedding_fractionField | (intros; apply GlobalTheory.ComplexEmbedding.exists_embedding_fractionField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSubrepFixedOfUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalProjectionFinite
namespace GlobalTheory.OrthogonalProjection

open Module

theorem exists_orthogonal_projection_finite {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hB : ∀ v : W, B v v = 0 → v = 0) (M : Submodule ℂ W) [FiniteDimensional ℂ M] (v : W) :
    ∃ m ∈ M, ∀ z ∈ M, B z (v - m) = 0 := by
  classical
  let b : Basis (Fin (finrank ℂ M)) ℂ M := Module.finBasis ℂ M
  let T : M →ₗ[ℂ] (Fin (finrank ℂ M) → ℂ) :=
    LinearMap.pi (fun i => (B (b i : W)).comp M.subtype)
  have key : ∀ w : W, (∀ i, B (b i : W) w = 0) → ∀ z ∈ M, B z w = 0 := by
    intro w hw z hz
    have h0 : (B.flip w).comp M.subtype = 0 := by
      apply b.ext
      intro i
      simpa using hw i
    have := LinearMap.congr_fun h0 ⟨z, hz⟩
    simpa using this
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    have h1 : ∀ i, B (b i : W) (m : W) = 0 := by
      intro i
      have := congr_fun hm i
      simpa [T] using this
    have h2 := key m h1 m m.2
    exact Subtype.ext (hB _ h2)
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun])).mp hinj
  obtain ⟨m, hm⟩ := hsurj (fun i => B (b i : W) v)
  refine ⟨m, m.2, ?_⟩
  apply key
  intro i
  have := congr_fun hm i
  simp [T] at this
  simp [map_sub, this]

theorem exists_orth_proj : ∀ {W : Type} [inst : AddCommGroup W] [inst_1 : Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ (v : W), ((B : W → W →ₗ[ℂ] ℂ) v : W → ℂ) v = (0 : ℂ) → v = (0 : W)) → ∀ (M : Submodule ℂ W) [FiniteDimensional ℂ ↥M] (v : W), ∃ m ∈ M, ∀ z ∈ M, ((B : W → W →ₗ[ℂ] ℂ) z : W → ℂ) (v - m) = (0 : ℂ) := by
  intro W _ _ B hB M _ v
  exact exists_orthogonal_projection_finite B hB M v

end GlobalTheory.OrthogonalProjection
end

namespace GlobalTheory.UnitarySemisimple

variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W]

theorem exists_orth_proj (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (hdef : ∀ v, B v v = 0 → v = 0)
    (M : Submodule ℂ W) [FiniteDimensional ℂ M] (v : W) :
    ∃ m ∈ M, ∀ z ∈ M, B z (v - m) = 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjection.exists_orth_proj
  | exact _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj
  | (apply _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjection.exists_orth_proj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjection.exists_orth_proj ..)

theorem rho_inv_rho (ρ : Representation ℂ H W) (g : H) (u : W) : ρ g⁻¹ (ρ g u) = u := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem rho_rho_inv (ρ : Representation ℂ H W) (g : H) (u : W) : ρ g (ρ g⁻¹ u) = u := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem orth_stable (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v) (Z : Subrepresentation ρ) (s : W)
    (hs : ∀ z ∈ Z.toSubmodule, B z s = 0) (g : H) : ∀ z ∈ Z.toSubmodule, B z (ρ g s) = 0 := by
  intro z hz
  calc B z (ρ g s) = B (ρ g (ρ g⁻¹ z)) (ρ g s) := by rw [rho_rho_inv]
    _ = B (ρ g⁻¹ z) s := hinv _ _ _
    _ = 0 := hs _ (Z.apply_mem_toSubmodule _ hz)

theorem exists_compl_proj (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (hdef : ∀ v, B v v = 0 → v = 0) (hinv : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hadm : ∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧
      ∀ w, (Set.range fun k : K => ρ k w).Finite)
    (Z : Subrepresentation ρ) (v : W) :
    ∃ t ∈ Z.toSubmodule, ∀ z ∈ Z.toSubmodule, B z (v - t) = 0 := by
  classical
  obtain ⟨K, hvK, hfd, hfin⟩ := hadm v
  have ofF : ∀ u ∈ GlobalTheory.PRep.fixed ρ K, ∀ k ∈ K, ρ k u = u := by
    intro u hu k hk
    have := hu ⟨k, hk⟩
    simpa using this
  have memF : ∀ u, (∀ k ∈ K, ρ k u = u) → u ∈ GlobalTheory.PRep.fixed ρ K := by
    intro u hu k
    show ρ (k : H) u = ((1 : ℂˣ) : ℂ) • u
    simp [hu k k.2]
  haveI : FiniteDimensional ℂ (Z.toSubmodule ⊓ GlobalTheory.PRep.fixed ρ K : Submodule ℂ W) :=
    Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨m, hmM, hm⟩ := exists_orth_proj B hdef (Z.toSubmodule ⊓ GlobalTheory.PRep.fixed ρ K) v
  refine ⟨m, hmM.1, fun z hz => ?_⟩
  have hwK : ∀ k ∈ K, ρ k (v - m) = v - m := by
    intro k hk
    rw [map_sub, hvK k hk, ofF m hmM.2 k hk]
  set s := (hfin z).toFinset with hs
  have hmem : ∀ o ∈ s, ∃ k' : K, ρ k' z = o := by
    intro o ho
    simpa [s] using ho
  have hperm : ∀ k ∈ K, ∑ o ∈ s, ρ k o = ∑ o ∈ s, o := by
    intro k hk
    apply Finset.sum_nbij' (fun o => ρ k o) (fun o => ρ k⁻¹ o)
    · intro o ho
      obtain ⟨k', rfl⟩ := hmem o ho
      simp only [s, Set.Finite.mem_toFinset, Set.mem_range]
      exact ⟨⟨k, hk⟩ * k', by simp [map_mul, Module.End.mul_apply]⟩
    · intro o ho
      obtain ⟨k', rfl⟩ := hmem o ho
      simp only [s, Set.Finite.mem_toFinset, Set.mem_range]
      exact ⟨⟨k, hk⟩⁻¹ * k', by simp [map_mul, Module.End.mul_apply]⟩
    · intro o _; exact rho_inv_rho ρ k o
    · intro o _; exact rho_rho_inv ρ k o
    · intro o _; rfl
  have heZ : ∑ o ∈ s, o ∈ Z.toSubmodule := by
    refine Submodule.sum_mem _ (fun o ho => ?_)
    obtain ⟨k', rfl⟩ := hmem o ho
    exact Z.apply_mem_toSubmodule _ hz
  have heF : ∑ o ∈ s, o ∈ GlobalTheory.PRep.fixed ρ K := by
    refine memF _ (fun k hk => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, hperm k hk]
  have h0 := hm _ ⟨heZ, heF⟩
  have hterm : ∀ o ∈ s, B o (v - m) = B z (v - m) := by
    intro o ho
    obtain ⟨k', rfl⟩ := hmem o ho
    rw [← hinv k' z (v - m), hwK k' k'.2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hz1 : z ∈ s := by
    simp only [s, Set.Finite.mem_toFinset, Set.mem_range]
    exact ⟨1, by simp⟩
  have hcard : s.card ≠ 0 := Finset.card_ne_zero.2 ⟨z, hz1⟩
  rw [nsmul_eq_mul] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd (by exact_mod_cast h) hcard
  · exact h

def orbSpan (ρ : Representation ℂ H W) (y : W) : Subrepresentation ρ :=
  ⟨Submodule.span ℂ (Set.range fun g => ρ g y), by
    intro g v hv
    have hle : (Submodule.span ℂ (Set.range fun g => ρ g y)).map (ρ g) ≤
        Submodule.span ℂ (Set.range fun g => ρ g y) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp [map_mul]⟩
    exact hle (Submodule.mem_map_of_mem hv)⟩

theorem mem_orbSpan (ρ : Representation ℂ H W) (y : W) : y ∈ (orbSpan ρ y).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

theorem orbSpan_le (ρ : Representation ℂ H W) (y : W) (Z : Subrepresentation ρ)
    (hy : y ∈ Z.toSubmodule) : (orbSpan ρ y).toSubmodule ≤ Z.toSubmodule :=
  Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact Z.apply_mem_toSubmodule g hy)

end GlobalTheory.UnitarySemisimple

namespace GlobalTheory.UnitarySemisimple

end GlobalTheory.UnitarySemisimple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityQuotientAdditiveChain
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityQuotientAdditiveChain
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
noncomputable section
namespace GlobalTheory.PhiGam.GmultAdd

variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

def quotEquiv (A B S : Submodule k U) (hSB : S ≤ B) :
    (↥A ⧸ B.submoduleOf A) ≃ₗ[k] (↥(A.map S.mkQ) ⧸ (B.map S.mkQ).submoduleOf (A.map S.mkQ)) :=
  (Submodule.quotEquivOfEq _ _ (by
      ext a
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      change (a : U) ∈ B ↔ S.mkQ a ∈ B.map S.mkQ
      have h : (B.map S.mkQ).comap S.mkQ = B := by
        rw [Submodule.comap_map_mkQ]; exact sup_eq_right.2 hSB
      constructor
      · intro ha
        exact Submodule.mem_map_of_mem (f := S.mkQ) ha
      · intro ha
        rw [← h]
        exact ha)).trans
    (LinearMap.quotKerEquivOfSurjective
      (((B.map S.mkQ).submoduleOf (A.map S.mkQ)).mkQ ∘ₗ (S.mkQ.submoduleMap A))
      ((Submodule.mkQ_surjective _).comp (LinearMap.submoduleMap_surjective _ _)))

theorem map_self (S : Submodule k U) : S.map S.mkQ = ⊥ := by
  simp

theorem fin_map (A S : Submodule k U) (h : FiniteDimensional k (↥A ⧸ S.submoduleOf A)) :
    FiniteDimensional k (A.map S.mkQ) := by
  have e := quotEquiv A S S le_rfl
  have h2 : (S.map S.mkQ).submoduleOf (A.map S.mkQ) = ⊥ := by
    rw [map_self]; simp [Submodule.submoduleOf]
  have e2 := e.trans (Submodule.quotEquivOfEqBot _ h2)
  exact e2.finiteDimensional

theorem finrank_quot (A B S : Submodule k U) (hSB : S ≤ B) (hBA : B ≤ A)
    [FiniteDimensional k (A.map S.mkQ)] :
    Module.finrank k (↥A ⧸ B.submoduleOf A) + Module.finrank k (B.map S.mkQ)
      = Module.finrank k (A.map S.mkQ) := by
  rw [(quotEquiv A B S hSB).finrank_eq,
    ← Submodule.finrank_quotient_add_finrank ((B.map S.mkQ).submoduleOf (A.map S.mkQ)),
    (Submodule.submoduleOfEquivOfLe (Submodule.map_mono hBA)).finrank_eq]

theorem map_inf_mkQ (A B S : Submodule k U) (hA : S ≤ A) :
    (A ⊓ B).map S.mkQ = A.map S.mkQ ⊓ B.map S.mkQ := by
  apply le_antisymm (Submodule.map_inf_le _)
  rintro y ⟨⟨a, ha, rfl⟩, b, hb, hab⟩
  refine ⟨b, ⟨?_, hb⟩, hab⟩
  have : b - a ∈ S := by
    simpa [Submodule.Quotient.eq] using hab
  simpa using A.add_mem (hA this) ha

theorem pow_mem (N : Module.End k U) (Q : Submodule k U) (hQ : ∀ y ∈ Q, N y ∈ Q) (m : ℕ) :
    ∀ y ∈ Q, (N ^ m) y ∈ Q := by
  induction m with
  | zero => intro y hy; simpa using hy
  | succ m ih => intro y hy; rw [pow_succ', Module.End.mul_apply]; exact hQ _ (ih y hy)

theorem mem_gen (N : Module.End k U) (Q : Submodule k U) (hQ : ∀ y ∈ Q, N y ∈ Q) (y : U) :
    y ∈ (⨆ m : ℕ, Q.comap (N ^ m)) ↔ ∃ m : ℕ, (N ^ m) y ∈ Q := by
  have hmono : Monotone (fun m : ℕ => Q.comap (N ^ m)) := by
    apply monotone_nat_of_le_succ
    intro m z hz
    simp only [Submodule.mem_comap] at hz ⊢
    rw [pow_succ', Module.End.mul_apply]; exact hQ _ hz
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  rfl

theorem stab (N : Module.End k U) (Q S : Submodule k U) (hQ : ∀ y ∈ Q, N y ∈ Q)
    [FiniteDimensional k (Q.map S.mkQ)] :
    ∃ M : ℕ, ∀ m : ℕ, (Q.map (N ^ M)).map S.mkQ ≤ (Q.map (N ^ (M + m))).map S.mkQ := by
  have hle : ∀ j : ℕ, (Q.map (N ^ j)).map S.mkQ ≤ Q.map S.mkQ := fun j =>
    Submodule.map_mono (by rintro _ ⟨y, hy, rfl⟩; exact pow_mem N Q hQ j y hy)
  have hfin : ∀ j : ℕ, FiniteDimensional k ((Q.map (N ^ j)).map S.mkQ) := fun j =>
    Submodule.finiteDimensional_of_le (hle j)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ j : ℕ, Module.finrank k ((Q.map (N ^ M)).map S.mkQ)
      ≤ Module.finrank k ((Q.map (N ^ j)).map S.mkQ) :=
    ⟨Function.argmin (fun j : ℕ => Module.finrank k ((Q.map (N ^ j)).map S.mkQ)),
      fun j => Function.argmin_le (fun j : ℕ => Module.finrank k ((Q.map (N ^ j)).map S.mkQ)) j⟩
  refine ⟨M, fun m => ?_⟩
  have h1 : (Q.map (N ^ (M + m))).map S.mkQ ≤ (Q.map (N ^ M)).map S.mkQ := by
    apply Submodule.map_mono
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(N ^ m) y, pow_mem N Q hQ m y hy, by rw [pow_add, Module.End.mul_apply]⟩
  haveI := hfin M
  exact (Submodule.eq_of_le_of_finrank_le h1 (hM _)).ge

theorem gen_sup (N : Module.End k U) (P Q S : Submodule k U) (hSQ : S ≤ Q) (hQP : Q ≤ P)
    (hQ : ∀ y ∈ Q, N y ∈ Q) (hS : ∀ y ∈ S, N y ∈ S) [FiniteDimensional k (Q.map S.mkQ)] :
    P ⊓ (⨆ m : ℕ, Q.comap (N ^ m)) = (P ⊓ ⨆ m : ℕ, S.comap (N ^ m)) ⊔ Q := by
  apply le_antisymm
  · rintro u ⟨huP, hu⟩
    obtain ⟨m, hm⟩ := (mem_gen N Q hQ u).1 hu
    obtain ⟨M, hM⟩ := stab N Q S hQ
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := hM m
      (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (f := N ^ M) hm))
    have h' : (N ^ M) ((N ^ m) u) - (N ^ (M + m)) q ∈ S := by
      simpa [Submodule.Quotient.eq] using h.symm
    have hu' : u = (u - q) + q := by abel
    rw [hu']
    refine Submodule.add_mem_sup ⟨P.sub_mem huP (hQP hq), (mem_gen N S hS _).2 ⟨M + m, ?_⟩⟩ hq
    rw [map_sub]
    convert h' using 2
    rw [pow_add, Module.End.mul_apply]
  · refine sup_le (inf_le_inf_left _ (iSup_mono fun m => Submodule.comap_mono hSQ)) (le_inf hQP ?_)
    intro y hy
    exact (mem_gen N Q hQ y).2 ⟨0, by simpa using hy⟩

theorem main : ∀ {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (P Q S : Submodule k U), S ≤ Q → Q ≤ P → (∀ x ∈ P, T x ∈ P) → (∀ x ∈ Q, T x ∈ Q) → (∀ x ∈ S, T x ∈ S) → FiniteDimensional k (↥P ⧸ S.submoduleOf P) → ∀ x : k, gmult T P S x = gmult T P Q x + gmult T Q S x := by
  intro k U _ _ _ T P Q S hSQ hQP _ hQ hS hfin x
  unfold gmult
  set N := T - algebraMap k (Module.End k U) x with hN
  have hst : ∀ A : Submodule k U, (∀ y ∈ A, T y ∈ A) → ∀ y ∈ A, N y ∈ A := by
    intro A hA y hy
    have : N y = T y - x • y := by simp [hN, Module.algebraMap_end_apply]
    rw [this]
    exact A.sub_mem (hA y hy) (A.smul_mem x hy)
  haveI hP := fin_map P S hfin
  have hf : ∀ A : Submodule k U, A ≤ P → FiniteDimensional k (A.map S.mkQ) := fun A hA =>
    Submodule.finiteDimensional_of_le (Submodule.map_mono hA)
  haveI := hf Q hQP
  have hSG : S ≤ ⨆ m : ℕ, S.comap (N ^ m) := fun y hy =>
    (mem_gen N S (hst S hS) y).2 ⟨0, by simpa using hy⟩
  have h1 := gen_sup N P Q S hSQ hQP (hst Q hQ) (hst S hS)
  set G := ⨆ m : ℕ, S.comap (N ^ m) with hG
  have h2 : Q ⊓ G = (P ⊓ G) ⊓ Q := by
    rw [inf_right_comm, inf_eq_right.2 hQP]
  rw [h1, h2]
  set A := P ⊓ G with hA
  have hSA : S ≤ A := le_inf (hSQ.trans hQP) hSG
  haveI := hf A inf_le_left
  haveI := hf (A ⊔ Q) (sup_le inf_le_left hQP)
  haveI := hf (A ⊓ Q) (inf_le_right.trans hQP)
  have e1 := finrank_quot A S S le_rfl hSA
  have e2 := finrank_quot (A ⊔ Q) Q S hSQ le_sup_right
  have e3 := finrank_quot (A ⊓ Q) S S le_rfl (le_inf hSA hSQ)
  have e4 := Submodule.finrank_sup_add_finrank_inf_eq (A.map S.mkQ) (Q.map S.mkQ)
  rw [← Submodule.map_sup, ← map_inf_mkQ A Q S hSA] at e4
  rw [map_self, finrank_bot] at e1 e3
  omega

end GlobalTheory.PhiGam.GmultAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityQuotientAdditiveChainStatement
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genEigenMultiplicityQuotient_additive_chain : ∀ {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (P Q S : Submodule k U), S ≤ Q → Q ≤ P → (∀ x ∈ P, T x ∈ P) → (∀ x ∈ Q, T x ∈ Q) → (∀ x ∈ S, T x ∈ S) → FiniteDimensional k (↥P ⧸ S.submoduleOf P) → ∀ x : k, gmult T P S x = gmult T P Q x + gmult T Q S x := by
  first | exact @GlobalTheory.PhiGam.GmultAdd.main | exact GlobalTheory.PhiGam.GmultAdd.main | (intros; apply GlobalTheory.PhiGam.GmultAdd.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SubIdBijOfContracting
noncomputable section
namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem sub_id_bij_of_contracting {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (I : Ideal A)
    [IsPrecomplete I M] [IsHausdorff I M] (T : M →+ M)
    (hT : ∀ (j : ℕ) (m : M), m ∈ (I ^ j • ⊤ : Submodule A M) → T m ∈ (I ^ (j + 1) • ⊤ : Submodule A M)) :
    (∀ b : M, ∃ m, T m - m = b) ∧ ∀ m : M, T m = m → m = 0 := by
  have hmem0 : ∀ m : M, m ∈ (I ^ 0 • ⊤ : Submodule A M) := by intro m; simp

  have hTpow : ∀ (j k : ℕ) (m : M), m ∈ (I ^ j • ⊤ : Submodule A M) →
      T^[k] m ∈ (I ^ (j + k) • ⊤ : Submodule A M) := by
    intro j k
    induction k with
    | zero => intro m hm; simpa using hm
    | succ k ih =>
      intro m hm
      rw [Function.iterate_succ_apply', ← add_assoc]
      exact hT _ _ (ih m hm)
  have hhaus : ∀ m : M, (∀ j, m ∈ (I ^ j • ⊤ : Submodule A M)) → m = 0 := fun m hm =>
    IsHausdorff.haus ‹IsHausdorff I M› m fun j => by rw [SModEq.zero]; exact hm j
  have hle : ∀ {j k : ℕ}, j ≤ k → (I ^ k • ⊤ : Submodule A M) ≤ I ^ j • ⊤ :=
    fun h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  refine ⟨fun b => ?_, fun m hm => hhaus m fun j => ?_⟩
  · have hiter : ∀ k, T^[k] b ∈ (I ^ k • ⊤ : Submodule A M) := fun k => by
      simpa using hTpow 0 k b (hmem0 b)

    have hcauchy : ∀ {m n : ℕ}, m ≤ n →
        (fun n => -(∑ k ∈ Finset.range n, T^[k] b)) m ≡
          (fun n => -(∑ k ∈ Finset.range n, T^[k] b)) n [SMOD (I ^ m • ⊤ : Submodule A M)] := by
      intro m n hmn
      rw [SModEq.sub_mem]
      have hd : -(∑ k ∈ Finset.range m, T^[k] b) - -(∑ k ∈ Finset.range n, T^[k] b) =
          ∑ k ∈ Finset.Ico m n, T^[k] b := by
        rw [Finset.sum_Ico_eq_sub _ hmn]
        abel
      simp only
      rw [hd]
      exact Submodule.sum_mem _ fun k hk => hle (Finset.mem_Ico.mp hk).1 (hiter k)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹IsPrecomplete I M› hcauchy
    refine ⟨L, sub_eq_zero.mp (hhaus _ fun j => ?_)⟩
    have h1 : L - -(∑ k ∈ Finset.range j, T^[k] b) ∈ (I ^ j • ⊤ : Submodule A M) := by
      have h := SModEq.sub_mem.mp (hL j)
      rw [← neg_sub]
      exact Submodule.neg_mem _ h
    have htel := Finset.sum_range_sub' (fun k => T^[k] b) j
    rw [Finset.sum_sub_distrib] at htel
    simp only [Function.iterate_zero_apply] at htel
    have hsucc : ∀ k, T (T^[k] b) = T^[k + 1] b := fun k => (Function.iterate_succ_apply' T k b).symm
    have h2 : T (-(∑ k ∈ Finset.range j, T^[k] b)) - -(∑ k ∈ Finset.range j, T^[k] b) - b =
        -(T^[j] b) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_neg, map_sum]
      simp only [hsucc]
      have e : -(∑ k ∈ Finset.range j, T^[k + 1] b) - -(∑ k ∈ Finset.range j, T^[k] b) - b =
          ((∑ k ∈ Finset.range j, T^[k] b) - ∑ k ∈ Finset.range j, T^[k + 1] b) - b := by abel
      rw [e, htel]
      abel
    have h3 : T (L - -(∑ k ∈ Finset.range j, T^[k] b)) ∈ (I ^ j • ⊤ : Submodule A M) :=
      hle (Nat.le_succ j) (hT j _ h1)
    have hsplit : T L - L - b = (T (L - -(∑ k ∈ Finset.range j, T^[k] b)) -
        (L - -(∑ k ∈ Finset.range j, T^[k] b))) +
        (T (-(∑ k ∈ Finset.range j, T^[k] b)) - -(∑ k ∈ Finset.range j, T^[k] b) - b) := by
      rw [map_sub]
      abel
    rw [hsplit, h2]
    exact Submodule.add_mem _ (Submodule.sub_mem _ h3 h1) (Submodule.neg_mem _ (hiter j))
  · induction j with
    | zero => exact hmem0 m
    | succ j ih =>
      have h := hT j m ih
      rwa [hm] at h

theorem mem_span_pow_smul_top {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (x : A) (j : ℕ) (m : M) :
    m ∈ (Ideal.span {x} ^ j • ⊤ : Submodule A M) ↔ ∃ y, x ^ j • y = m := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

theorem contracting_of_semi {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (x c : A) (T : M →+ M)
    (h1 : ∀ m, T (x • m) = (c * x) • T m) (h2 : ∀ m, ∃ y, x • y = T m) (j : ℕ) (m : M)
    (hm : m ∈ (Ideal.span {x} ^ j • ⊤ : Submodule A M)) :
    T m ∈ (Ideal.span {x} ^ (j + 1) • ⊤ : Submodule A M) := by
  rw [mem_span_pow_smul_top] at hm ⊢
  obtain ⟨y, rfl⟩ := hm
  obtain ⟨z, hz⟩ := h2 y
  have hpow : ∀ (i : ℕ) (m : M), T (x ^ i • m) = (c * x) ^ i • T m := by
    intro i
    induction i with
    | zero => intro m; simp
    | succ i ih => intro m; rw [pow_succ, mul_smul, ih, h1, smul_smul, ← pow_succ]
  refine ⟨c ^ j • z, ?_⟩
  rw [hpow, ← hz, smul_smul, smul_smul]
  congr 1
  ring

theorem one_sub_frob_bij : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (P : ZMod n → Submodule k⟦X⟧ V), (∀ i, IsLat (P i)) → (∀ i, ∀ x ∈ P (i - 1), D.φ i x ∈ sh 1 (P i)) → (∀ b : ZMod n → V, (∀ i, b i ∈ P i) → ∃ m : ZMod n → V, (∀ i, m i ∈ P i) ∧ ∀ i, D.φ i (m (i - 1)) - m i = b i) ∧ ∀ m : ZMod n → V, (∀ i, m i ∈ P i) → (∀ i, D.φ i (m (i - 1)) = m i) → m = 0 := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D P hP hφ

  have hcoe : ∀ (a : k⟦X⟧) (y : V), a • y = ((a : k⟦X⟧) : k⸨X⸩) • y := by
    intro a y
    rw [← algebraMap_smul k⸨X⸩ a y]
    rfl
  have hφP : ∀ i, ∀ x ∈ P (i - 1), ∃ y ∈ P i, (PowerSeries.X : k⟦X⟧) • y = D.φ i x := by
    intro i x hx
    obtain ⟨y, hy, hyx⟩ := mem_sh_iff_exists.mp (hφ i x hx)
    exact ⟨y, hy, by rw [hcoe, ← vv_eq_coe_X, ← hyx, zpow_one]⟩
  have hφmem : ∀ i, ∀ x ∈ P (i - 1), D.φ i x ∈ P i := by
    intro i x hx
    obtain ⟨y, hy, hyx⟩ := hφP i x hx
    rw [← hyx]
    exact (P i).smul_mem _ hy

  let T : ((i : ZMod n) → P i) →+ ((i : ZMod n) → P i) :=
    { toFun := fun m i => ⟨D.φ i (m (i - 1)), hφmem i _ (m (i - 1)).2⟩
      map_zero' := by
        funext i
        apply Subtype.ext
        simp
      map_add' := by
        intro a b
        funext i
        apply Subtype.ext
        simp [map_add (f := _)] }
  have : ∀ i, Module.Finite k⟦X⟧ (P i) := fun i => Module.Finite.iff_fg.mpr (hP i).1
  have hXtop : Ideal.span {(PowerSeries.X : k⟦X⟧)} ≠ ⊤ := by
    intro h
    have h1 := (Ideal.span_singleton_eq_top.mp h).map (PowerSeries.constantCoeff (R := k))
    simp at h1
  have : IsHausdorff (Ideal.span {(PowerSeries.X : k⟦X⟧)}) ((i : ZMod n) → P i) :=
    IsHausdorff.of_isLocalRing _ _ hXtop
  have : IsPrecomplete (Ideal.span {(PowerSeries.X : k⟦X⟧)}) ((i : ZMod n) → P i) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module _ _

  obtain ⟨u, hu⟩ := R.φ_v
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have h1 : ∀ m : ((i : ZMod n) → P i), T ((PowerSeries.X : k⟦X⟧) • m) =
      (((u : k⟦X⟧) * PowerSeries.X ^ (l - 1)) * PowerSeries.X) • T m := by
    intro m
    funext i
    apply Subtype.ext
    simp only [T, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, Submodule.coe_smul]
    rw [hcoe, hcoe, ← vv_eq_coe_X, D.φ_semi, hu, PowerSeries.coe_mul, PowerSeries.coe_mul,
      PowerSeries.coe_pow, ← vv_eq_coe_X, mul_assoc, pow_sub_one_mul hl]
  have h2 : ∀ m : ((i : ZMod n) → P i), ∃ y : ((i : ZMod n) → P i),
      (PowerSeries.X : k⟦X⟧) • y = T m := by
    intro m
    choose y hy hyx using fun i => hφP i _ (m (i - 1)).2
    exact ⟨fun i => ⟨y i, hy i⟩, funext fun i => Subtype.ext (hyx i)⟩
  obtain ⟨hsurj, hinj⟩ := sub_id_bij_of_contracting (Ideal.span {(PowerSeries.X : k⟦X⟧)}) T
    (fun j m hm => contracting_of_semi _ _ T h1 h2 j m hm)
  refine ⟨fun b hb => ?_, fun m hm hfix => ?_⟩
  · obtain ⟨m, hm⟩ := hsurj (fun i => ⟨b i, hb i⟩)
    refine ⟨fun i => (m i : V), fun i => (m i).2, fun i => ?_⟩
    have h := congrArg (fun z => ((z i : P i) : V)) hm
    simpa [T] using h
  · have h := hinj (fun i => ⟨m i, hm i⟩) (funext fun i => Subtype.ext (hfix i))
    funext i
    have hi := congrArg (fun z => ((z i : P i) : V)) h
    simpa using hi

end GlobalTheory.PhiGam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSpanImageEqCard
open Module

namespace GlobalTheory.Per.Sen

theorem finrank_span_image_eq_card {L M : Type} [Field L] [AddCommGroup M] [Module L M] {m : ℕ}
    (d : Fin m → M) (hd : LinearIndependent L d) (p : Fin m → Prop) [DecidablePred p] :
    Module.finrank L (Submodule.span L (d '' {i | p i})) = (Finset.univ.filter p).card := by
  have h := finrank_span_eq_card (hd.comp (Subtype.val : {i // p i} → Fin m) Subtype.val_injective)
  rw [Fintype.card_subtype] at h
  rw [show d '' {i | p i} = Set.range (d ∘ (Subtype.val : {i // p i} → Fin m)) by
    ext x; simp [Set.mem_image, Set.mem_range]]
  exact h

private theorem exists_eq_of_antitone_le_of_exhaustive {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M) (hA : Antitone A)
    (hAD : ∀ a, A a ≤ D) (hex : ∀ x ∈ D, ∃ a, x ∈ A a) : ∃ a, A a = D := by
  obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional D).mpr inferInstance
  have key : ∀ T : Finset M, (T : Set M) ⊆ D → ∃ a, ∀ x ∈ T, x ∈ A a := by
    intro T
    classical
    refine Finset.induction_on T ?_ ?_
    · intro _; exact ⟨0, by simp⟩
    · intro y T _ ih hT
      obtain ⟨a, ha⟩ := ih (fun z hz => hT (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hz)))
      obtain ⟨b, hb⟩ := hex y (hT (Finset.mem_coe.mpr (Finset.mem_insert_self y T)))
      refine ⟨min a b, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hA (min_le_right a b) hb
      · exact hA (min_le_left a b) (ha x hx)
  obtain ⟨a, ha⟩ := key S (by rw [← hS]; exact Submodule.subset_span)
  refine ⟨a, le_antisymm (hAD a) ?_⟩
  rw [← hS, Submodule.span_le]
  exact fun x hx => ha x hx

private theorem exists_adapted_basis_of_finrank_jumps {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (r : ℕ) : ∀ (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M)
    (U : Multiset ℤ), Module.finrank L D = r → Antitone A → (∀ a, A a ≤ D) →
    (∀ x ∈ D, ∃ a, x ∈ A a) → (∀ x, (∀ a, x ∈ A a) → x = 0) →
    (∀ a : ℤ, (Module.finrank L (A a) : ℤ) - Module.finrank L (A (a + 1)) = (U.count a : ℤ)) →
    ∃ (u : Fin r → ℤ) (d : Fin r → M), Finset.univ.val.map u = U ∧ LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {k | a ≤ u k}) := by
  induction r with
  | zero =>
    intro D _ A U hr hA hAD hex hsep hU
    have hD : D = ⊥ := Submodule.finrank_eq_zero.mp hr
    have hA0 : ∀ a, A a = ⊥ := fun a => le_bot_iff.mp (hD ▸ hAD a)
    have hU0 : U = 0 := by
      ext a
      have h := hU a
      rw [hA0 a, hA0 (a + 1), finrank_bot] at h
      rw [Multiset.count_zero]
      push_cast at h
      omega
    refine ⟨Fin.elim0, Fin.elim0, by simp [hU0], linearIndependent_empty_type, fun a => ?_⟩
    rw [hA0 a]; symm
    rw [Submodule.span_eq_bot]
    rintro x ⟨k, -, -⟩
    exact k.elim0
  | succ r ih =>
    intro D _ A U hr hA hAD hex hsep hU
    classical
    obtain ⟨a0, ha0⟩ := exists_eq_of_antitone_le_of_exhaustive D A hA hAD hex
    have hDne : D ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at hr; omega
    obtain ⟨w, hwD, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hDne
    obtain ⟨b, hb⟩ : ∃ b, w ∉ A b := by
      by_contra h; push Not at h; exact hw0 (hsep w h)
    have hbd : ∀ a, A a = D → a < b := by
      intro a ha; by_contra h; push Not at h
      exact hb (hA h (by rw [ha]; exact hwD))
    obtain ⟨s, hs, hsmax⟩ :=
      Int.exists_greatest_of_bdd ⟨b, fun z hz => (hbd z hz).le⟩ ⟨a0, ha0⟩
    have hBD : A (s + 1) < D :=
      lt_of_le_of_ne (hAD _) (fun h => by have := hsmax _ h; omega)
    obtain ⟨v, hvD, hvB⟩ := SetLike.exists_of_lt hBD
    have hv0 : v ≠ 0 := fun h => hvB (by rw [h]; exact Submodule.zero_mem _)
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl (A (s + 1) ⊔ Submodule.span L {v})
    obtain ⟨D', hD'⟩ : ∃ D' : Submodule L M, D' = A (s + 1) ⊔ (C ⊓ D) := ⟨_, rfl⟩
    have hED : A (s + 1) ⊔ Submodule.span L {v} ≤ D :=
      sup_le (hAD _) ((Submodule.span_singleton_le_iff_mem _ _).mpr hvD)
    have hD'D : D' ≤ D := by rw [hD']; exact sup_le (hAD _) inf_le_right
    have hBD' : A (s + 1) ≤ D' := by rw [hD']; exact le_sup_left
    have hvD' : v ∉ D' := by
      intro hv
      rw [hD'] at hv
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
      have hzE : z ∈ A (s + 1) ⊔ Submodule.span L {v} := by
        have : z = v - y := by rw [← hyz]; abel
        rw [this]
        exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
          (Submodule.mem_sup_left hy)
      have hz0 : z = 0 := (Submodule.disjoint_def.mp hC.disjoint) z hzE hz.1
      apply hvB; rw [← hyz, hz0, add_zero]; exact hy
    have hsup : D' ⊔ Submodule.span L {v} = D := by
      rw [hD', sup_right_comm, ← sup_inf_assoc_of_le _ hED, hC.sup_eq_top, top_inf_eq]
    have hinf : D' ⊓ Submodule.span L {v} = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx2
      by_cases hc : c = 0
      · simp [hc]
      · exact absurd ((Submodule.smul_mem_iff _ hc).mp hx1) hvD'
    have : FiniteDimensional L D' := Submodule.finiteDimensional_of_le hD'D
    have : FiniteDimensional L (Submodule.span L {v}) :=
      FiniteDimensional.span_of_finite L (Set.finite_singleton v)
    have hrD' : Module.finrank L D' = r := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq D' (Submodule.span L {v})
      rw [hsup, hinf, finrank_bot, finrank_span_singleton hv0, hr] at h
      omega
    have hlow : ∀ a, a ≤ s → A a = D := fun a ha =>
      le_antisymm (hAD a) (by rw [← hs]; exact hA ha)
    have hs_mem : 0 < U.count s := by
      have h := hU s
      rw [hs, hr] at h
      have := Submodule.finrank_lt_finrank_of_lt hBD
      rw [hr] at this
      omega
    have hU' : ∀ a : ℤ, (Module.finrank L ↥(A a ⊓ D') : ℤ) -
        Module.finrank L ↥(A (a + 1) ⊓ D') = ((U.erase s).count a : ℤ) := by
      intro a
      rcases lt_trichotomy a s with h | h | h
      · have h0 := hU a
        rw [hlow a h.le, hlow (a + 1) (by omega)] at h0
        rw [hlow a h.le, hlow (a + 1) (by omega), inf_eq_right.mpr hD'D,
          Multiset.count_erase_of_ne h.ne]
        omega
      · rw [h]
        have h0 := hU s
        rw [hs, hr] at h0
        rw [hs, inf_eq_right.mpr hD'D, inf_eq_left.mpr hBD', Multiset.count_erase_self, hrD',
          Nat.cast_sub hs_mem, Nat.cast_one]
        push_cast at h0 ⊢
        omega
      · rw [inf_eq_left.mpr ((hA (show s + 1 ≤ a by omega)).trans hBD'),
          inf_eq_left.mpr ((hA (show s + 1 ≤ a + 1 by omega)).trans hBD'),
          Multiset.count_erase_of_ne h.ne']
        exact hU a
    obtain ⟨u', d', hu', hd', hspan'⟩ := ih D' (fun a => A a ⊓ D') (U.erase s) hrD'
      (fun a b h => inf_le_inf_right _ (hA h)) (fun a => inf_le_right)
      (fun x hx => by obtain ⟨a, ha⟩ := hex x (hD'D hx); exact ⟨a, Submodule.mem_inf.mpr ⟨ha, hx⟩⟩)
      (fun x hx => hsep x (fun a => (Submodule.mem_inf.mp (hx a)).1)) hU'
    have hd'D' : ∀ k, d' k ∈ D' := by
      intro k
      have h := hspan' (u' k)
      have hk : d' k ∈ Submodule.span L (d' '' {j | u' k ≤ u' j}) :=
        Submodule.subset_span ⟨k, le_refl (u' k), rfl⟩
      rw [← h] at hk
      exact (Submodule.mem_inf.mp hk).2
    refine ⟨Fin.cons s u', Fin.cons v d', ?_, ?_, ?_⟩
    · rw [Fin.univ_val_map, List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Multiset.cons_coe, ← Fin.univ_val_map, hu']
      exact Multiset.cons_erase (Multiset.count_pos.mp hs_mem)
    · refine linearIndependent_finCons.mpr ⟨hd', fun hv => hvD' ?_⟩
      exact (Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hd'D' k)) hv
    · intro a
      by_cases has : a ≤ s
      · rw [hlow a has]
        apply le_antisymm
        · rw [← hsup, sup_le_iff]
          constructor
          · have h := hspan' a
            rw [hlow a has, inf_eq_right.mpr hD'D] at h
            rw [h]
            apply Submodule.span_mono
            rintro _ ⟨j, hj, rfl⟩
            exact ⟨j.succ, by simpa using hj, by simp⟩
          · rw [Submodule.span_le, Set.singleton_subset_iff]
            exact Submodule.subset_span ⟨0, by simpa using has, by simp⟩
        · rw [Submodule.span_le]
          rintro _ ⟨k, -, rfl⟩
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
          · simpa using hvD
          · simpa using hD'D (hd'D' j)
      · push Not at has
        have h := hspan' a
        rw [inf_eq_left.mpr ((hA (show s + 1 ≤ a by omega)).trans hBD')] at h
        rw [h]
        congr 1
        ext x
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j.succ, by simpa using hj, by simp⟩
        · rintro ⟨k, hk, rfl⟩
          rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
          · simp at hk; omega
          · exact ⟨j, by simpa using hk, by simp⟩

theorem adapted_basis_jumps : ∀ {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (D : Submodule L M) [FiniteDimensional L D] (A : ℤ → Submodule L M) (U : Multiset ℤ) (r : ℕ),
    Module.finrank L D = r → Antitone A → (∀ a, A a ≤ D) → (∀ x ∈ D, ∃ a, x ∈ A a) →
    (∀ x, (∀ a, x ∈ A a) → x = 0) →
    (∀ a : ℤ, (Module.finrank L (A a) : ℤ) - Module.finrank L (A (a + 1)) = (U.count a : ℤ)) →
    ∃ (u : Fin r → ℤ) (d : Fin r → M), Finset.univ.val.map u = U ∧ LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {k | a ≤ u k}) := by
  intro L M _ _ _ D _ A U r hr hA hAD hex hsep hU
  exact exists_adapted_basis_of_finrank_jumps r D A U hr hA hAD hex hsep hU

end GlobalTheory.Per.Sen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentTrace
open Polynomial

namespace GlobalTheory.SimpleCharIndep

theorem exists_smul_eq_ite {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, IsSimpleModule R (M i)]
    (h : ∀ i j, i ≠ j → ∀ f : M i →ₗ[R] M j, f = 0) (i₀ : ι) (s : ∀ i, Finset (M i)) :
    ∃ r : R, ∀ i, ∀ m ∈ s i, r • m = if i = i₀ then m else 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjectionOnto.main
  | exact _root_.GlobalTheory.OrthogonalProjectionOnto.main
  | (apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjectionOnto.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjectionOnto.main ..)

end GlobalTheory.SimpleCharIndep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdEApply
noncomputable section

namespace GlobalTheory.StableLatCount

def adE (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    (g₁ : A₁) (g₂ : A₂) : (A₂ →ₗ[E] A₁) →ₗ[E] (A₂ →ₗ[E] A₁) :=
  LinearMap.llcomp E A₂ A₁ A₁ (LinearMap.mulLeft E g₁) - LinearMap.lcomp E A₁ (LinearMap.mulLeft E g₂)

def homLat (E : Type) [Field E] {O A₁ A₂ : Type} [CommRing O] [Algebra O E] [CommRing A₁] [CommRing A₂]
    [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁]
    (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) : Submodule O (A₂ →ₗ[E] A₁) where
  carrier := {ψ | ∀ x ∈ M₂, ψ x ∈ M₁}
  add_mem' := fun ha hb x hx => by simpa using M₁.add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c ψ hψ x hx => by simpa using M₁.smul_mem c (hψ x hx)

theorem adE_apply (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    (g₁ : A₁) (g₂ : A₂) (ψ : A₂ →ₗ[E] A₁) (x : A₂) : adE E g₁ g₂ ψ x = g₁ * ψ x - ψ (g₂ * x) := rfl

end GlobalTheory.StableLatCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSurjectiveOfIsCplAt
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat

theorem flat_quotientMap_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.Flat)
    (I : Ideal R) : (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).Flat := by
  algebraize [φ]
  have h1 : (algebraMap (R ⧸ I) (TensorProduct R (R ⧸ I) S)).Flat :=
    RingHom.flat_algebraMap_iff.2 inferInstance
  let e : TensorProduct R (R ⧸ I) S ≃+* S ⧸ I.map φ :=
    (Algebra.TensorProduct.comm R (R ⧸ I) S).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toRingEquiv
  have h2 : (e : TensorProduct R (R ⧸ I) S →+* S ⧸ I.map φ).Flat := RingHom.Flat.of_bijective e.bijective
  have h3 := h1.comp h2
  convert h3 using 1
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  have : (Ideal.Quotient.mk I r) ⊗ₜ[R] (1 : S) = (1 : R ⧸ I) ⊗ₜ[R] (φ r) := by
    have := TensorProduct.smul_tmul (R := R) r (1 : R ⧸ I) (1 : S)
    simp only [Algebra.smul_def, mul_one] at this
    exact this
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_coe]
  rw [this]
  apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).injective
  simp [e]
  exact Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk S I (φ r)

end GlobalTheory.Pat
end
