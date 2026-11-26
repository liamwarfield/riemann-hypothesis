module

public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtTransInvHolds

@[expose] public section

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LwRankTies
section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CountHypothesesIffText
noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset Formalism.MainNotions.S

theorem stab_transfer {H : Type} [Group H] (P R U : Subgroup H) (y : P)
    (hs : R ⊓ U.map (MulAut.conj (y : H)).toMonoidHom = ⊥) (γ : R.subgroupOf P) (κ : U.subgroupOf P)
    (e : (γ : P) * y = y * κ) : γ = 1 := by
  have h1 : ((γ : P) : H) ∈ R ⊓ U.map (MulAut.conj (y : H)).toMonoidHom := by
    refine ⟨γ.2, ⟨((κ : P) : H), κ.2, ?_⟩⟩
    have e' := congrArg Subtype.val e
    simp only [Subgroup.coe_mul] at e'
    show (y : H) * ((κ : P) : H) * (y : H)⁻¹ = _
    rw [← e']
    group
  rw [hs] at h1
  exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.1 h1))

end Formalism.MainNotions.StandardLattice
end
end

section -- merged from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLz
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions NumberField

theorem level_prime_splits_totally_real (D : D7) (u : D.what₂.Word) : StandardLattice.SplitsF D (D.mem u).A.T := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have h := Formalism.BasicNotions.Examples₂.placesOver_ncard_of_split D.host (D.mem u).A.T (D.T_mod_cond u)
  have h' := splits_sub D.host.F (D.mem u).A.T D.host.E (D.mem u).A.T_prime h
  rw [finrank_F_eq] at h'
  exact h'

end Formalism.MainNotions.J

end
end

noncomputable section

namespace Formalism.MainNotions.Ext.Lw

open Formalism.BasicNotions Formalism.MainNotions

theorem splitsF_g_all (D : D7) : ∀ j, StandardLattice.SplitsF D (D.host.g j) := fun j => J.splitsF_g D j

theorem splitsF_T_all (D : D7) (u : D.what₂.Word) : StandardLattice.SplitsF D (D.mem u).A.T := J.level_prime_splits_totally_real D u

theorem rank_conditions_iff_lowest_space {eps : ℝ} (Fm : FamP eps) :
    RankTiesF Fm ↔ ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), StandardLattice.Mu0Tie (Fm.D x i) u := by
  unfold RankTiesF
  constructor
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i u => ((hx0 x hx i).2 u).2⟩
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i => ⟨splitsF_g_all (Fm.D x i), fun u => ⟨splitsF_T_all (Fm.D x i) u, hx0 x hx i u⟩⟩⟩

theorem rank_conditions_of_lowest_space {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), StandardLattice.Mu0Tie (Fm.D x i) u) : RankTiesF Fm :=
  (rank_conditions_iff_lowest_space Fm).2 h

end Formalism.MainNotions.Ext.Lw

end
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.GoodLatCM
open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

section Lat

variable {E : Type} [Field E] [NumberField E]

end Lat

end Formalism.MainNotions.Ext

open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions NumberField

namespace Formalism.MainNotions.Ext

theorem discr_K {R : Ranks} (H : Host R) : discr H.K = -(H.d : ℤ) := by
  obtain ⟨-, hdp, -, hd16, -⟩ := H.hyp
  have hm : H.sqd ∈ H.K := IntermediateField.mem_adjoin_simple_self ℚ H.sqd
  have hx : (⟨H.sqd, hm⟩ : H.K) ^ 2 = ((-(H.d : ℤ) : ℤ) : H.K) := by
    apply Subtype.ext
    push_cast
    exact H.sqd_sq
  refine Formalism.HF.P.quadDiscr_ne_one H.K (-(H.d : ℤ)) _ hx ?_ ?_ ?_ ?_
  · have key : @IntermediateField.adjoin ℚ _ H.K _ H.K.algebra' {⟨H.sqd, hm⟩} = ⊤ := by
      apply IntermediateField.map_injective (IntermediateField.val H.K)
      rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
        Set.image_singleton]
      first
      | rfl
      | (simp only [IntermediateField.val_mk]; rfl)
      | simp [Formalism.HC.HostRaw.K]
    convert key
    all_goals first
      | exact Subsingleton.elim _ _
      | (apply Algebra.algebra_ext; intro r; simp [Algebra.algebraMap_eq_smul_one])
  · exact Int.squarefree_natAbs.mp (by simpa using hdp.prime.squarefree)
  · omega
  · omega

end Formalism.MainNotions.Ext
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.EmbeddingPermutesLettersHolds
section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EmbTraceSum
section -- merged from Formalism.PeriodIntegrals.EmbTraceSum
namespace PI

def EmbTraceSum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (φ₀ : E →+* ℂ) (S : Type) [Fintype S]
    (emb : S → E →+* ℂ), Function.Injective emb → (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) →
    Fintype.card S = Module.finrank K E →
    ∀ y : E, ∑ s, emb s y = φ₀ ((Algebra.trace K E y : K) : E)

end PI
end

theorem sumEqTrace_holds : PI.EmbTraceSum := by
  intro E _ _ K φ₀ S _ emb hinj hext hcard y
  let _ : Algebra K ℂ := (φ₀.comp (algebraMap K E)).toAlgebra
  have hcomm : ∀ (s : S) (a : K), emb s (algebraMap K E a) = algebraMap K ℂ a := fun s a => hext s a
  let f : S → (E →ₐ[K] ℂ) := fun s => { emb s with commutes' := hcomm s }
  have hf : Function.Injective f := by
    intro s t hst
    apply hinj
    ext x
    exact AlgHom.congr_fun hst x
  have : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  have hcard' : Fintype.card S = Fintype.card (E →ₐ[K] ℂ) := by
    rw [hcard, AlgHom.card]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcard'⟩
  have htr := trace_eq_sum_embeddings (K := K) (L := E) (E := ℂ) (x := y)
  calc ∑ s, emb s y = ∑ s, f s y := rfl
    _ = ∑ σ : E →ₐ[K] ℂ, σ y := Fintype.sum_bijective f hbij _ _ (fun _ => rfl)
    _ = algebraMap K ℂ (Algebra.trace K E y) := htr.symm
    _ = φ₀ ((Algebra.trace K E y : K) : E) := rfl
end

namespace Formalism.MainNotions.Ext

theorem traceSum_holds : TraceSum := sumEqTrace_holds

theorem trace_sum_over_letters_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.StandardLatticesGL3.TraceMapNormalisation D := trace_sum_over_letters traceSum_holds D

end Formalism.MainNotions.Ext
end
