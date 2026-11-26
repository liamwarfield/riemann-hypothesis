module

public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryStandardAtQFromIsometryOverField
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourfoldLatticeIsometryDenominatorCoprime
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourfoldLatticeIsometryDenominatorCoprime
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomKapi


open Formalism.L2.Th1.H in
theorem nsmul_relIdx_mem {V : Type*} [AddCommGroup V] (S M : AddSubgroup V) {z : V} (hz : z ∈ M) :
    relIdx S M • z ∈ S := by
  have h := AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨z, hz⟩ : M)
  have h2 : ((S.addSubgroupOf M).index • (⟨z, hz⟩ : M) : M).1 ∈ S := AddSubgroup.mem_addSubgroupOf.1 h
  simpa [relIdx, AddSubgroup.relIndex] using h2

theorem denom_prime_to : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ x : Fin 4 → D.host.E, (∀ a, x a ∈ D.host.AA0) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ w, (s : D.host.K) * G (B.γ₀.g x) w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  intro D cc δ B hcc q _ hcop u hn hnq G hG x hx
  set n := Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) with hndef
  set N := Ideal.absNorm cc with hNdef
  have hq : q.Prime := Fact.out
  have hnc : Nat.Coprime n q := ((Nat.Prime.coprime_iff_not_dvd hq).2 hnq).symm
  refine ⟨n * N, Nat.Coprime.mul_left hnc hcop, fun w => ?_⟩
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B

  have hNc : ((N : ℕ) : 𝓞 D.host.K) ∈ cc := Ideal.absNorm_mem cc
  set w₀ : ℂ := δ * D.host.φ₀ (((((N : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E)) with hw₀
  have hw₀mem : w₀ ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨_, hNc, rfl⟩
  have hz : w₀ • emb4 D x ∈ Formalism.L2.Th1.H.pow4 B.lamM := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀mem hx
  have hgC : B.gC (w₀ • emb4 D x) = w₀ • (fun w => D.host.φ₀ ((B.γ₀.g x w : D.host.K) : D.host.E)) := by
    rw [map_smul]
    exact congrArg (w₀ • ·) (B.gC_spec x)
  have hu : u (B.gC (w₀ • emb4 D x)) = w₀ • (fun w => D.host.φ₀ ((G (B.γ₀.g x) w : D.host.K) : D.host.E)) := by
    rw [hgC, map_smul, hG]
  have hM : u (B.gC (w₀ • emb4 D x)) ∈ Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) :=
    ⟨_, ⟨_, hz, rfl⟩, rfl⟩
  have hS := nsmul_relIdx_mem (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) _ hM
  rw [← hndef, hu] at hS
  have hc : n • (w₀ * D.host.φ₀ ((G (B.γ₀.g x) w : D.host.K) : D.host.E)) ∈ B.L.lattice := by
    have := hS w (Set.mem_univ w)
    simpa using this
  obtain ⟨c, -, hc'⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 hc)
  have hC : D.host.φ₀ (((((n * N : ℕ) : D.host.K) * G (B.γ₀.g x) w : D.host.K) : D.host.E)) = D.host.φ₀ ((c : D.host.K) : D.host.E) := by
    apply mul_left_cancel₀ hδ
    rw [← hc', hw₀]
    push_cast
    simp only [map_mul, map_natCast, nsmul_eq_mul]
    ring
  have hK : (((n * N : ℕ) : D.host.K) * G (B.γ₀.g x) w : D.host.K) = (c : D.host.K) :=
    Subtype.coe_injective (D.host.φ₀.injective hC)
  exact ⟨c, hK.symm⟩

end GlobalTheory.MomKapi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourfoldLatticeIsometryDenominatorCoprimeStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourfoldLattice_isometry_denominator_coprime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ x : Fin 4 → D.host.E, (∀ a, x a ∈ D.host.AA0) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ w, (s : D.host.K) * G (B.γ₀.g x) w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range := by
  first | exact @GlobalTheory.MomKapi.denom_prime_to | exact GlobalTheory.MomKapi.denom_prime_to | (intros; apply GlobalTheory.MomKapi.denom_prime_to <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryFourfoldLatticePreservesRationalVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryFourfoldLatticePreservesRationalVectors
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.LatDesc

theorem unitary_maps_rational : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, ∃ v' : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((v' w : D.host.K) : D.host.E) := by
  intro D cc δ B hcc u hidx v
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B
  set S := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hS
  set M := Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM)) with hM
  set n := Formalism.L2.Th1.H.relIdx S M with hn

  have h1 : ∀ x ∈ M, n • x ∈ S := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (S.addSubgroupOf M) (⟨x, hx⟩ : M)
    rw [AddSubgroup.mem_addSubgroupOf, AddSubmonoidClass.coe_nsmul] at this
    exact this

  set y := B.γ₀.g.symm v with hy
  obtain ⟨t, ht, hint⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.exists_nat_mul D.host.E (Finset.univ.image y)
  set N := Ideal.absNorm cc with hNdef
  have hN : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1
  have hNc : ((N : 𝓞 D.host.K)) ∈ cc := Ideal.absNorm_mem cc
  have hw₀ : δ * (N : ℂ) ∈ lamOf D cc δ := by
    refine AddSubgroup.subset_closure ⟨(N : 𝓞 D.host.K), hNc, ?_⟩
    simp
  have hm : (δ * (N : ℂ)) • emb4 D (t • y) ∈ Formalism.L2.Th1.H.pow4 B.lamM :=
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.gen_mem hw₀ fun a => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.int_mem_inverse_half_different (by
      have := hint _ (Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩)
      simpa using this)
  set V : Fin 4 × D.what₂.Tau → ℂ := fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E) with hV
  have hg : B.gC (emb4 D (t • y)) = (t : ℂ) • V := by
    rw [show B.gC (emb4 D (t • y)) = _ from B.gC_spec (t • y), map_nsmul, hy, LinearEquiv.apply_symm_apply]
    funext w
    simp [hV]
  have hmem : (δ * (N : ℂ) * (t : ℂ)) • u V ∈ M := by
    refine ⟨B.gC ((δ * (N : ℂ)) • emb4 D (t • y)), ⟨_, hm, rfl⟩, ?_⟩
    show u (B.gC _) = _
    rw [map_smul, hg, smul_smul, map_smul]
  have hS' := h1 _ hmem
  rw [hS, Formalism.L2.Th1.H.mem_stdLat] at hS'
  have hc : ∀ w, ∃ c ∈ cc, ((n • ((δ * (N : ℂ) * (t : ℂ)) • u V)) w) = δ * D.host.φ₀ (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) :=
    fun w => Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ _ ((Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B _).1 (hS' w))
  choose c _ hc using hc
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hidx
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ⟨fun w => ((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)), ?_⟩
  funext w
  have h := hc w
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at h
  have e : D.host.φ₀ (((((c w : 𝓞 D.host.K) : D.host.K) / ((n : D.host.K) * (N : D.host.K) * (t : D.host.K)) : D.host.K)) : D.host.E)
      = D.host.φ₀ (((c w : 𝓞 D.host.K) : D.host.K) : D.host.E) / ((n : ℂ) * (N : ℂ) * (t : ℂ)) := by
    push_cast
    rw [map_div₀, map_mul, map_mul, map_natCast, map_natCast, map_natCast]
  rw [e, eq_div_iff (mul_ne_zero (mul_ne_zero hnC hNC) htC)]
  apply mul_left_cancel₀ hδ
  rw [← h]
  ring

end GlobalTheory.LatDesc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryFourfoldLatticePreservesRationalVectorsStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_fourfoldLattice_preserves_rationalVectors : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, ∃ v' : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((v' w : D.host.K) : D.host.E) := by
  first | exact @GlobalTheory.LatDesc.unitary_maps_rational | exact GlobalTheory.LatDesc.unitary_maps_rational | (intros; apply GlobalTheory.LatDesc.unitary_maps_rational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InverseIsometryFourfoldLatticeDenominatorCoprime
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InverseIsometryFourfoldLatticeDenominatorCoprime
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.LatInvDenom

theorem lamMM_form (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∀ z ∈ lamMM D (lamOf D cc δ), ∃ e ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      z = fun τ => δ * embT D τ e := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, a, ha, rfl⟩ := hx
    obtain ⟨c, -, rfl⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.lam_mem D cc δ w hw
    refine ⟨((c : D.host.K) : D.host.E) * a, ?_, ?_⟩
    · exact Submodule.smul_mem (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)
        (⟨_, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.intK D c⟩ : 𝓞 D.host.E) ha
    · funext τ
      rw [map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D τ _ (SetLike.coe_mem _)]
      ring
  | zero => exact ⟨0, Submodule.zero_mem _, by funext τ; simp⟩
  | add x y _ _ h1 h2 =>
    obtain ⟨e1, he1, rfl⟩ := h1
    obtain ⟨e2, he2, rfl⟩ := h2
    exact ⟨e1 + e2, Submodule.add_mem _ he1 he2, by funext τ; simp only [Pi.add_apply, map_add (f := _)]; ring⟩
  | neg x _ h1 =>
    obtain ⟨e1, he1, rfl⟩ := h1
    exact ⟨-e1, Submodule.neg_mem _ he1, by funext τ; simp only [Pi.neg_apply, map_neg]; ring⟩

theorem inverseIsometry_fourfoldLattice_denominator_coprime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, (∀ w, v w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ a, (s : D.host.E) * B.γ₀.g.symm (G.symm v) a ∈ D.host.AA0 := by
  intro D cc δ B hcc hδ12 q _ hNq u hu hidx hq hidx' G hG v hv
  have hqp : q.Prime := Fact.out
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.base_linkage_nonempty D cc δ B
  set S := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hS
  set M := Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
      (Formalism.L2.Th1.H.pow4 B.lamM)) with hM

  have hSd : Formalism.L2.Th1.H.IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) S :=
    Formalism.L2.Th1.H.stdSelfDual B.L _
  have hMd : Formalism.L2.Th1.H.IsSelfDual (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) M :=
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.selfDual_img _ _ u hu _ (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.selfDual B hcc hδ12)
  have heq : Formalism.L2.Th1.H.relIdx S M = Formalism.L2.Th1.H.relIdx M S :=
    Formalism.L2.Th1.H.indexEq _ _ (Formalism.L2.Th1.H.stdHBasic B.L _).2.1 S M hSd hMd hidx hidx'
  set n := Formalism.L2.Th1.H.relIdx M S with hn
  have hnq : Nat.Coprime n q := by
    rw [← heq]; exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hqp).2 hq)
  have h1 : ∀ x ∈ S, n • x ∈ M := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (M.addSubgroupOf S) (⟨x, hx⟩ : S)
    rw [AddSubgroup.mem_addSubgroupOf, AddSubmonoidClass.coe_nsmul] at this
    exact this

  set N := Ideal.absNorm cc with hNdef
  have hNc : ((N : 𝓞 D.host.K)) ∈ cc := Ideal.absNorm_mem cc
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff]; exact hcc.1
  choose o ho using hv
  set V : Fin 4 × D.what₂.Tau → ℂ := fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E) with hV
  have hz : (δ * (N : ℂ)) • V ∈ S := by
    rw [hS, Formalism.L2.Th1.H.mem_stdLat]
    intro w
    rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B]
    refine AddSubgroup.subset_closure ⟨(N : 𝓞 D.host.K) * o w, cc.mul_mem_right _ hNc, ?_⟩
    simp only [hV, Pi.smul_apply, smul_eq_mul, ← ho w]
    push_cast
    rw [map_mul, map_natCast]
    ring
  set y := B.γ₀.g.symm (G.symm v) with hy
  have hgy : u (B.gC (emb4 D y)) = V := by
    rw [show B.gC (emb4 D y) = _ from B.gC_spec y, hy, LinearEquiv.apply_symm_apply, hG (G.symm v),
      LinearEquiv.apply_symm_apply]
  obtain ⟨m', ⟨m₀, hm₀, rfl⟩, hm'⟩ := h1 _ hz
  have hm0eq : m₀ = ((n : ℂ) * δ * (N : ℂ)) • emb4 D y := by
    apply B.gC.injective
    apply u.injective
    have e1 : u (B.gC m₀) = n • ((δ * (N : ℂ)) • V) := hm'
    rw [e1, map_smul, map_smul, hgy, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_assoc]

  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.mp (by
    rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.card_tau]
    exact Nat.mul_pos (by decide) D.R.ord_pos)
  refine ⟨n * N, Nat.Coprime.mul_left hnq hNq, fun a => ?_⟩
  obtain ⟨e, he, hee⟩ := lamMM_form D cc δ _ (hm₀ a)
  have h2 := congrFun hee τ
  rw [hm0eq] at h2
  simp only [Formalism.L2.Th1.H.slice, Pi.smul_apply, smul_eq_mul, emb4] at h2
  have h3 : embT D τ (((n * N : ℕ) : D.host.E) * y a) = embT D τ e := by
    apply mul_left_cancel₀ hδ
    rw [map_mul, map_natCast]
    push_cast
    linear_combination h2
  rw [(embT D τ).injective h3]
  exact he

end GlobalTheory.LatInvDenom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InverseIsometryFourfoldLatticeDenominatorCoprimeStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseIsometry_fourfoldLattice_denominator_coprime_alt : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, (∀ w, v w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ a, (s : D.host.E) * B.γ₀.g.symm (G.symm v) a ∈ D.host.AA0 := by
  first | exact @GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime | exact GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime | (intros; apply GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinearEquivDescendsOfPreservesImage
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinearEquivDescendsOfPreservesImage
namespace GlobalTheory

theorem linearEquiv_descends_of_preserves_image {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (f : K →+* ℂ) (u : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ))
    (h : ∀ v : ι → K, ∃ v' : ι → K, u (fun i => f (v i)) = fun i => f (v' i)) :
    ∃ g : (ι → K) ≃ₗ[K] (ι → K), (∀ v, u (fun i => f (v i)) = fun i => f (g v i)) ∧
      LinearMap.det (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) =
        f (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) := by
  classical
  let F : (ι → K) → (ι → ℂ) := fun v i => f (v i)
  have hFinj : Function.Injective F := by
    intro v w hvw
    funext i
    exact f.injective (congrFun hvw i)
  choose G hG using h
  have hG' : ∀ v, u (F v) = F (G v) := hG
  have hFadd : ∀ v w, F (v + w) = F v + F w := by
    intro v w; funext i; simp [F]
  have hFsmul : ∀ (c : K) v, F (c • v) = f c • F v := by
    intro c v; funext i; simp [F]
  let Gl : (ι → K) →ₗ[K] (ι → K) :=
    { toFun := G
      map_add' := fun v w => hFinj (by rw [← hG', hFadd, map_add (f := _), hG', hG', hFadd])
      map_smul' := fun c v => hFinj (by
        simp only [RingHom.id_apply]
        rw [← hG', hFsmul, map_smul, hG', hFsmul]) }
  have hGl : ∀ v, Gl v = G v := fun _ => rfl
  have hinj : Function.Injective Gl := by
    intro v w hvw
    apply hFinj
    apply u.injective
    rw [hG', hG']
    exact congrArg F hvw
  let g : (ι → K) ≃ₗ[K] (ι → K) := LinearEquiv.ofInjectiveEndo Gl hinj
  have hg : ∀ v, g v = G v := fun v => by
    simp [g, hGl]
  have hsingle : ∀ j : ι, F (Pi.single j 1) = Pi.single j 1 := by
    intro j
    funext i
    by_cases hij : i = j
    · subst hij; simp [F]
    · simp [F, Pi.single_eq_of_ne hij]
  have hmat : LinearMap.toMatrix' (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) =
      (LinearMap.toMatrix' (g : (ι → K) →ₗ[K] (ι → K))).map f := by
    ext i j
    have := congrFun (hG' (Pi.single j 1)) i
    rw [hsingle j] at this
    simp only [LinearMap.toMatrix'_apply, Matrix.map_apply]
    simp only [LinearEquiv.coe_coe, hg]
    exact this
  refine ⟨g, fun v => ?_, ?_⟩
  · rw [hg]; exact hG v
  · rw [← LinearMap.det_toMatrix', hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      LinearMap.det_toMatrix']

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinearEquivDescendsOfPreservesImageStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearEquiv_descends_det_of_preserves_image : ∀ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (f : K →+* ℂ) (u : (ι → ℂ) ≃ₗ[ℂ] (ι → ℂ)), (∀ v : ι → K, ∃ v' : ι → K, u (fun i => f (v i)) = fun i => f (v' i)) → ∃ g : (ι → K) ≃ₗ[K] (ι → K), (∀ v, u (fun i => f (v i)) = fun i => f (g v i)) ∧ LinearMap.det (u : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) = f (LinearMap.det (g : (ι → K) →ₗ[K] (ι → K))) := by
  first | exact @GlobalTheory.linearEquiv_descends_of_preserves_image | exact GlobalTheory.linearEquiv_descends_of_preserves_image | (intros; apply GlobalTheory.linearEquiv_descends_of_preserves_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryStandardAtQFromIsometryOverField
noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.KapIsom

theorem form_u (D : D7) (L : PeriodPair) (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
    (hu : Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))
    (x y : Fin 4 × D.what₂.Tau → ℂ) :
    ∑ w, u x w * (starRingEnd ℂ) (u y w) = ∑ w, x w * (starRingEnd ℂ) (y w) := by
  have h := hu x y
  change Formalism.L2.Th1.H.matH (hOne L _) (u x) (u y) = Formalism.L2.Th1.H.matH (hOne L _) x y at h
  rw [matH_hOne, matH_hOne] at h
  have hA : ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Formalism.L2.Th1.F.areaPos L).ne'
  exact (div_left_inj' hA).1 h

theorem main : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∃ γ : IsoK D, γ.AtP q ∧ LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) = D.host.φ₀ ((γ.detRel B.γ₀ : D.host.K) : D.host.E) := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hqc ι u hu h1 h2 h3
  obtain ⟨G, hG, hdet⟩ := GlobalTheory.T.exists_linearEquiv_descends_det_of_preserves_image (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) u
    (GlobalTheory.T.unitary_fourfoldLattice_preserves_rationalVectors D cc δ B hcc u h1)
  have hG' : ∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E))
      = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E) := fun v => hG v
  let γ : IsoK D :=
    { g := B.γ₀.g.trans G
      isom := by
        intro x y
        apply D.host.φ₀.injective
        have e1 := form_u D B.L u hu (fun w => D.host.φ₀ ((B.γ₀.g x w : D.host.K) : D.host.E))
          (fun w => D.host.φ₀ ((B.γ₀.g y w : D.host.K) : D.host.E))
        rw [hG', hG'] at e1
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← B.γ₀.isom x y, map_sum, map_sum]
        simp only [map_mul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.emb_conj]
        exact e1 }
  refine ⟨γ, ⟨fun x hx => GlobalTheory.T.fourfoldLattice_isometry_denominator_coprime D cc δ B hcc q hqc u h1 h2 G hG' x hx,
    fun v hv => GlobalTheory.T.inverseIsometry_fourfoldLattice_denominator_coprime_alt D cc δ B hcc hδ q hqc u hu h1 h2 h3 G hG' v hv⟩, ?_⟩
  have hd : γ.detRel B.γ₀ = LinearMap.det (G : (Fin 4 × D.what₂.Tau → D.host.K) →ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)) := by
    have e : (B.γ₀.g.symm.trans γ.g) = G := by
      apply LinearEquiv.ext; intro v
      show G (B.γ₀.g (B.γ₀.g.symm v)) = G v
      rw [LinearEquiv.apply_symm_apply]
    unfold IsoK.detRel
    rw [e]
  rw [hdet, hd]
  rfl

end GlobalTheory.KapIsom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryStandardAtQFromIsometryOverFieldStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_standard_at_q_from_isometry_over_field : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∃ γ : IsoK D, γ.AtP q ∧ LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) = D.host.φ₀ ((γ.detRel B.γ₀ : D.host.K) : D.host.E) := by
  first | exact @GlobalTheory.KapIsom.main | exact GlobalTheory.KapIsom.main | (intros; apply GlobalTheory.KapIsom.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetIsometryEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugateEmbeddingsInduceDifferentPrimesSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugateEmbeddingsInduceDifferentPrimesSplit
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.ConjPlace

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_le_one_of_int {q : ℕ} [Fact q.Prime] {K : Type} [Field K] (j : K →+* ℂ_[q]) (y : 𝓞 K) :
    ‖j (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by convert map_isIntegral_int j (RingOfIntegers.isIntegral_coe y); exact Subsingleton.elim _ _)

theorem norm_intCast_eq (q : ℕ) [Fact q.Prime] (n : ℤ) : ‖((n : ℤ) : ℂ_[q])‖ = ‖((n : ℤ) : ℚ_[q])‖ := by
  have e : ((n : ℤ) : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] ((n : ℤ) : ℚ_[q]) := (map_intCast _ n).symm
  rw [e]
  exact PadicComplex.norm_extends' (p := q) _

theorem norm_intCast_lt_one_iff (q : ℕ) [Fact q.Prime] (n : ℤ) : ‖((n : ℤ) : ℂ_[q])‖ < 1 ↔ (q : ℤ) ∣ n := by
  rw [norm_intCast_eq]
  exact Padic.norm_intCast_lt_one_iff

theorem exists_sq_add (q : ℕ) [Fact q.Prime] (d : ℕ) (h : jacobiSym (-(d : ℤ)) q = 1) :
    ¬ (q : ℤ) ∣ d ∧ ∃ t : ℤ, (q : ℤ) ∣ t ^ 2 + d := by
  have hl : legendreSym q (-(d : ℤ)) = 1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact h
  have h0 : ((-(d : ℤ) : ℤ) : ZMod q) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff q _).2 h0] at hl
    exact zero_ne_one hl
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff q h0).1 hl
  refine ⟨?_, ⟨(r.val : ℤ), ?_⟩⟩
  · intro hd
    apply h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_neg.2 hd)
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    rw [ZMod.natCast_zmod_val]
    linear_combination (-1 : ZMod q) * hr

theorem exists_small_not_conj {E : Type} [Field E] [CharZero E] (K : IntermediateField ℚ E) (φ : E →+* ℂ) (c : E ≃ₐ[ℚ] E)
    (d q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hj : jacobiSym (-(d : ℤ)) q = 1) (ι : ℂ ≃+* ℂ_[q])
    (s : K) (hs : s * s = -(d : K)) (hc : c (algebraMap K E s) = -algebraMap K E s) :
    ∃ y : 𝓞 K, ‖ι (φ ((y : K) : E))‖ < 1 ∧ 1 ≤ ‖ι (φ (c ((y : K) : E)))‖ := by
  obtain ⟨hnd, t, ht⟩ := exists_sq_add q d hj
  have hint : IsIntegral ℤ s :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, by simp [sq, hs]⟩
  let B : 𝓞 K := ⟨s, hint⟩
  let j : E →+* ℂ_[q] := ι.toRingHom.comp φ
  let jK : K →+* ℂ_[q] := j.comp (algebraMap K E)
  have hc' : c (s : E) = -(s : E) := hc
  have hsE : (s : E) * (s : E) = -(d : E) := by
    have := congrArg (fun x : K => (x : E)) hs
    simpa using this
  have hcoe : ∀ u : ℤ, (((B + u : 𝓞 K) : K) : E) = (s : E) + (u : E) := by
    intro u; push_cast; rfl
  have hle : ∀ y : 𝓞 K, ‖j ((y : K) : E)‖ ≤ 1 := fun y => norm_le_one_of_int jK y

  have hodd : ∀ u : ℤ, (q : ℤ) ∣ 2 * u → (q : ℤ) ∣ u := by
    intro u h
    rcases (Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)).dvd_or_dvd h with h2 | h2
    · exfalso
      have : q ∣ 2 := by exact_mod_cast h2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
    · exact h2
  have key : ∀ u : ℤ, (u = t ∨ u = -t) → ‖j (((B + u : 𝓞 K) : K) : E)‖ < 1 →
      1 ≤ ‖j (c (((B + u : 𝓞 K) : K) : E))‖ := by
    intro u hu h1
    by_contra h2
    push_neg at h2
    have e2 : c (((B + u : 𝓞 K) : K) : E) = -(s : E) + (u : E) := by
      rw [hcoe, map_add (f := _), map_intCast, hc']
    have hsum : j (((B + u : 𝓞 K) : K) : E) + j (c (((B + u : 𝓞 K) : K) : E)) = (((2 * u : ℤ)) : ℂ_[q]) := by
      rw [e2, hcoe, ← map_add (f := _)]
      have : (s : E) + (u : E) + (-(s : E) + (u : E)) = ((2 * u : ℤ) : E) := by push_cast; ring
      rw [this, map_intCast]
    have hlt : ‖(((2 * u : ℤ)) : ℂ_[q])‖ < 1 := by
      rw [← hsum]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)
    have hdu : (q : ℤ) ∣ u := hodd u ((norm_intCast_lt_one_iff q _).1 hlt)
    have hdt : (q : ℤ) ∣ t := by
      rcases hu with rfl | rfl
      · exact hdu
      · exact dvd_neg.1 hdu
    exact hnd ((dvd_add_right (dvd_pow hdt two_ne_zero)).1 ht)
  have hprod : j (((B + t : 𝓞 K) : K) : E) * j (((B + (-t : ℤ) : 𝓞 K) : K) : E) = ((-(t ^ 2 + d) : ℤ) : ℂ_[q]) := by
    rw [← map_mul, hcoe, hcoe]
    have : ((s : E) + (t : E)) * ((s : E) + ((-t : ℤ) : E)) = ((-(t ^ 2 + d) : ℤ) : E) := by
      push_cast
      linear_combination hsE
    rw [this, map_intCast]
  have hpl : ‖((-(t ^ 2 + d) : ℤ) : ℂ_[q])‖ < 1 := (norm_intCast_lt_one_iff q _).2 (dvd_neg.2 ht)
  by_cases h1 : ‖j (((B + t : 𝓞 K) : K) : E)‖ < 1
  · exact ⟨B + t, h1, key t (Or.inl rfl) h1⟩
  · push_neg at h1
    have h2 : ‖j (((B + (-t : ℤ) : 𝓞 K) : K) : E)‖ < 1 := by
      by_contra h2
      push_neg at h2
      rw [← hprod, norm_mul] at hpl
      nlinarith
    exact ⟨B + (-t : ℤ), h2, key (-t) (Or.inr rfl) h2⟩

theorem conj_place_ne : ∀ (D : D7) (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 →
    ∀ ι : ℂ ≃+* ℂ_[q], ∃ y : 𝓞 D.host.K, ‖ι (D.host.φ₀ ((y : D.host.K) : D.host.E))‖ < 1 ∧
      1 ≤ ‖ι (D.host.φ₀ (D.host.conj ((y : D.host.K) : D.host.E)))‖ := by
  intro D q _ hq2 hj ι
  obtain ⟨s, h1, h2⟩ := sqrtInK D
  exact exists_small_not_conj D.host.K D.host.φ₀ D.host.conj D.host.d q hq2 hj ι s h1 h2

end GlobalTheory.ConjPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugateEmbeddingsInduceDifferentPrimesSplitStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_embeddings_induce_different_primes_split : ∀ (D : D7) (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → ∀ ι : ℂ ≃+* ℂ_[q], ∃ y : 𝓞 D.host.K, ‖ι (D.host.φ₀ ((y : D.host.K) : D.host.E))‖ < 1 ∧ 1 ≤ ‖ι (D.host.φ₀ (D.host.conj ((y : D.host.K) : D.host.E)))‖ := by
  first | exact @GlobalTheory.ConjPlace.conj_place_ne | exact GlobalTheory.ConjPlace.conj_place_ne | (intros; apply GlobalTheory.ConjPlace.conj_place_ne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelativeDeterminantIsometryNormOne
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelativeDeterminantIsometryNormOne
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory

theorem det_mul_conj_eq_one_of_preserves {K E : Type} [Field K] [Field E] [Algebra K E] (cj : E →+* E)
    {n : Type} [Fintype n] [DecidableEq n] (φ : (n → K) →ₗ[K] (n → K))
    (h : ∀ v u : n → K, ∑ w, algebraMap K E (φ v w) * cj (algebraMap K E (φ u w))
      = ∑ w, algebraMap K E (v w) * cj (algebraMap K E (u w))) :
    algebraMap K E (LinearMap.det φ) * cj (algebraMap K E (LinearMap.det φ)) = 1 := by
  set A := LinearMap.toMatrix' φ with hA
  have key : ((algebraMap K E).mapMatrix A).transpose * (cj.mapMatrix ((algebraMap K E).mapMatrix A)) = 1 := by
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hA,
      LinearMap.toMatrix'_apply]
    rw [this, Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← RingHom.map_det, ← RingHom.map_det, ← RingHom.map_det, hA,
    LinearMap.det_toMatrix'] at hd
  exact hd

theorem detRel_mul_conj_eq_one (D : D7) (γ₀ γ : IsoK D) :
    ((γ.detRel γ₀ : D.host.K) : D.host.E) * D.host.conj ((γ.detRel γ₀ : D.host.K) : D.host.E) = 1 := by
  refine det_mul_conj_eq_one_of_preserves (K := D.host.K) (E := D.host.E) (D.host.conj : D.host.E →+* D.host.E) _ ?_
  intro v u
  have h1 := γ.isom (γ₀.g.symm v) (γ₀.g.symm u)
  have h2 := γ₀.isom (γ₀.g.symm v) (γ₀.g.symm u)
  simp only [LinearEquiv.apply_symm_apply] at h2
  exact h1.trans h2.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelativeDeterminantIsometryNormOneStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeDeterminant_isometry_norm_one : ∀ (D : D7) (γ₀ γ : IsoK D), ((γ.detRel γ₀ : D.host.K) : D.host.E) * D.host.conj ((γ.detRel γ₀ : D.host.K) : D.host.E) = 1 := by
  first | exact @GlobalTheory.detRel_mul_conj_eq_one | exact GlobalTheory.detRel_mul_conj_eq_one | (intros; apply GlobalTheory.detRel_mul_conj_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticAtMostTwoPrimesOver
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticAtMostTwoPrimesOver
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem quadratic_at_most_two_primes_over (K : Type) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (q : ℕ) (hq : q.Prime)
    (P₁ P₂ P₃ : HeightOneSpectrum (𝓞 K))
    (h₁ : ((q : ℕ) : 𝓞 K) ∈ P₁.asIdeal) (h₂ : ((q : ℕ) : 𝓞 K) ∈ P₂.asIdeal)
    (h₃ : ((q : ℕ) : 𝓞 K) ∈ P₃.asIdeal) : P₁ = P₂ ∨ P₁ = P₃ ∨ P₂ = P₃ := by
  by_contra hne
  push Not at hne
  obtain ⟨h12, h13, h23⟩ := hne
  have hN : Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 K)}) = q ^ 2 := by
    rw [Ideal.absNorm_span_singleton]
    have : ((q : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank, hK]
    simp
  have hd : ∀ P : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ P.asIdeal →
      P.asIdeal ∣ Ideal.span {((q : ℕ) : 𝓞 K)} := fun P hP =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hP)
  have hqd : ∀ P : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ P.asIdeal →
      q ∣ Ideal.absNorm P.asIdeal := by
    intro P hP
    have h1 : Ideal.absNorm P.asIdeal ∣ q ^ 2 := hN ▸ map_dvd Ideal.absNorm (hd P hP)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hq).mp h1
    rcases i with _ | i
    · exfalso
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hi
      exact P.isPrime.ne_top hi
    · rw [hi]; exact dvd_pow_self q (Nat.succ_ne_zero i)
  have hc : ∀ P Q : HeightOneSpectrum (𝓞 K), P ≠ Q → IsCoprime P.asIdeal Q.asIdeal := by
    intro P Q h
    rw [Ideal.isCoprime_iff_sup_eq]
    exact P.isMaximal.coprime_of_ne Q.isMaximal (fun e => h (HeightOneSpectrum.ext e))
  have hprod : P₁.asIdeal * P₂.asIdeal * P₃.asIdeal ∣ Ideal.span {((q : ℕ) : 𝓞 K)} :=
    IsCoprime.mul_dvd (IsCoprime.mul_left (hc _ _ h13) (hc _ _ h23))
      (IsCoprime.mul_dvd (hc _ _ h12) (hd _ h₁) (hd _ h₂)) (hd _ h₃)
  have h4 := map_dvd Ideal.absNorm hprod
  rw [hN, map_mul, map_mul] at h4
  have h5 : q * q * q ∣ q ^ 2 :=
    (mul_dvd_mul (mul_dvd_mul (hqd _ h₁) (hqd _ h₂)) (hqd _ h₃)).trans h4
  have h6 : q ^ 3 ∣ q ^ 2 := by rwa [show q ^ 3 = q * q * q by ring]
  have := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp h6
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticAtMostTwoPrimesOverStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_field_at_most_two_primes_over_prime : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (q : ℕ), q.Prime → ∀ P₁ P₂ P₃ : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ P₁.asIdeal → ((q : ℕ) : 𝓞 K) ∈ P₂.asIdeal → ((q : ℕ) : 𝓞 K) ∈ P₃.asIdeal → P₁ = P₂ ∨ P₁ = P₃ ∨ P₂ = P₃ := by
  first | exact @GlobalTheory.quadratic_at_most_two_primes_over | exact GlobalTheory.quadratic_at_most_two_primes_over | (intros; apply GlobalTheory.quadratic_at_most_two_primes_over <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationOfGeneratorOfPow
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationOfGeneratorOfPow
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem valuation_of_generator_of_pow (K : Type) [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (n : ℕ) (π : 𝓞 K) (h : 𝔭.asIdeal ^ n = Ideal.span {π}) :
    𝔭.valuation K (π : K) = WithZero.exp (-(n : ℤ)) := by
  have hπ : π ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at h
    exact 𝔭.ne_bot (pow_eq_zero_iff'.mp h).1
  rw [show (π : K) = algebraMap (𝓞 K) K π from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    𝔭.intValuation_if_neg hπ, ← h, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr 𝔭.ne_bot) 𝔭.associates_irreducible,
    Associates.count_self 𝔭.associates_irreducible, mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuationOfGeneratorOfPowStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_eq_exp_neg_of_pow_eq_span_singleton : ∀ (K : Type) [Field K] [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K)) (n : ℕ) (π : 𝓞 K), 𝔭.asIdeal ^ n = Ideal.span {π} → 𝔭.valuation K (π : K) = WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.valuation_of_generator_of_pow | exact GlobalTheory.valuation_of_generator_of_pow | (intros; apply GlobalTheory.valuation_of_generator_of_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetIsometryEqOne
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.KapVal

open IsDedekindDomain

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_le_one_of_int {q : ℕ} [Fact q.Prime] {K : Type} [Field K] [NumberField K] (j : K →+* ℂ_[q])
    (y : 𝓞 K) : ‖j (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by
    convert map_isIntegral_int j (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

theorem norm_natCast_lt_one (q : ℕ) [Fact q.Prime] : ‖((q : ℕ) : ℂ_[q])‖ < 1 := by
  have e : ((q : ℕ) : ℂ_[q]) = ((algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by
    simp
  rw [e, PadicComplex.norm_extends']
  exact Padic.norm_p_lt_one

end GlobalTheory.KapVal

namespace GlobalTheory.KapVal

open IsDedekindDomain

variable {q : ℕ} [Fact q.Prime] {K : Type} [Field K] [NumberField K]

theorem exists_place (j : K →+* ℂ_[q]) :
    ∃ w : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ w.asIdeal ∧ ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1 := by
  let P : Ideal (𝓞 K) :=
    { carrier := {x | ‖j (x : K)‖ < 1}
      add_mem' := fun {x y} hx hy => by
        show ‖j ((x : K) + (y : K))‖ < 1
        rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      zero_mem' := by
        show ‖j (0 : K)‖ < 1
        simp
      smul_mem' := fun r x hx => by
        show ‖j ((r : K) * (x : K))‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one_of_int j r) (norm_nonneg _) hx }
  have hP : ∀ x : 𝓞 K, x ∈ P ↔ ‖j (x : K)‖ < 1 := fun _ => Iff.rfl
  have hl : ((q : ℕ) : 𝓞 K) ∈ P := by
    rw [hP]
    have e : j (((q : ℕ) : 𝓞 K) : K) = ((q : ℕ) : ℂ_[q]) := by simp
    rw [e]
    exact norm_natCast_lt_one q
  have hprime : P.IsPrime := by
    refine ⟨?_, fun {x y} hxy => ?_⟩
    · rw [Ideal.ne_top_iff_one, hP]
      simp
    · rw [hP] at hxy
      have e : j ((x * y : 𝓞 K) : K) = j (x : K) * j (y : K) := by simp
      rw [e, norm_mul] at hxy
      rw [hP, hP]
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      exact absurd (one_le_mul_of_one_le_of_one_le h.1 h.2) (not_le.2 hxy)
  refine ⟨⟨P, hprime, ?_⟩, hl, hP⟩
  intro h0
  rw [h0, Ideal.mem_bot] at hl
  exact (Fact.out : q.Prime).ne_zero (by exact_mod_cast hl)

theorem norm_le_one_of_val (j : K →+* ℂ_[q]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1) (x : K) (hx : w.valuation K x ≤ 1) :
    ‖j x‖ ≤ 1 := by
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have hd : 1 ≤ ‖j ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have h2 : ‖j x‖ * ‖j ((d : 𝓞 K) : K)‖ = ‖j (n : K)‖ := by
    rw [← norm_mul, ← map_mul]; exact congrArg (fun z => ‖j z‖) h
  have h3 := norm_le_one_of_int j n
  nlinarith [norm_nonneg (j x)]

theorem norm_eq_one_of_val (j : K →+* ℂ_[q]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1) (x : K) (hx : w.valuation K x = 1) :
    ‖j x‖ = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h1 := norm_le_one_of_val j w hw x hx.le
  have h2 := norm_le_one_of_val j w hw x⁻¹ (by rw [map_inv₀, hx, inv_one])
  have h3 : ‖j x‖ * ‖j x⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
  nlinarith [norm_nonneg (j x), norm_nonneg (j x⁻¹)]

theorem norm_pow_eq (j : K →+* ℂ_[q]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1) (n : ℕ) (π : 𝓞 K)
    (hπ : w.valuation K (π : K) = WithZero.exp (-(n : ℤ))) (x : K) (hx : x ≠ 0) :
    ‖j x‖ ^ n = ‖j (π : K)‖ ^ (-WithZero.log (w.valuation K x)) := by
  set y := -WithZero.log (w.valuation K x) with hy
  have hv0 : w.valuation K x ≠ 0 := by simpa using hx
  have hvx : w.valuation K x = WithZero.exp (-y) := by
    rw [hy, neg_neg, WithZero.exp_log hv0]
  have hπ0 : (π : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hz : w.valuation K (x ^ n * (π : K) ^ (-y)) = 1 := by
    rw [map_mul, map_pow, map_zpow₀, hvx, hπ, ← WithZero.exp_nsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    rw [← WithZero.exp_zero]
    congr 1
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  have h1 := norm_eq_one_of_val j w hw _ hz
  rw [map_mul, map_pow, map_zpow₀, norm_mul, norm_pow, norm_zpow] at h1
  have hjπ : ‖j (π : K)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero j).2 hπ0
  have h2 : ‖j (π : K)‖ ^ (-y) * ‖j (π : K)‖ ^ y = 1 := by
    rw [← zpow_add₀ hjπ, neg_add_cancel, zpow_zero]
  calc ‖j x‖ ^ n = ‖j x‖ ^ n * (‖j (π : K)‖ ^ (-y) * ‖j (π : K)‖ ^ y) := by rw [h2, mul_one]
    _ = (‖j x‖ ^ n * ‖j (π : K)‖ ^ (-y)) * ‖j (π : K)‖ ^ y := by ring
    _ = ‖j (π : K)‖ ^ y := by rw [h1, one_mul]

end GlobalTheory.KapVal

namespace GlobalTheory.KapVal

open IsDedekindDomain

theorem norm_kappa_sq_mul_det : ∀ (D : D7) (γ₀ γ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], q ≠ 2 →
    jacobiSym (-(D.host.d : ℤ)) q = 1 → γ.AtP q → ∀ ι : ℂ ≃+* ℂ_[q],
    ‖ι k.kappa‖ ^ 2 * ‖ι (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E))‖ = 1 := by
  intro D γ₀ γ k q _ hq2 hj hat ι
  have hqp : q.Prime := Fact.out
  have hs : SplitK D q := Or.inr hj
  let jK : D.host.K →+* ℂ_[q] := ι.toRingHom.comp (D.host.φ₀.comp (algebraMap D.host.K D.host.E))
  let jK' : D.host.K →+* ℂ_[q] := ι.toRingHom.comp (D.host.φ₀.comp
    ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E)))
  have ejK : ∀ z : D.host.K, jK z = ι (D.host.φ₀ (z : D.host.E)) := fun z => rfl
  have ejK' : ∀ z : D.host.K, jK' z = ι (D.host.φ₀ (D.host.conj (z : D.host.E))) := fun z => rfl
  have hU := GlobalTheory.T.relativeDeterminant_isometry_norm_one D γ₀ γ
  set x : D.host.K := γ.detRel γ₀ with hxdef
  set h : ℕ := classNumber D.host.K with hh
  have hy : ordK (k.pp q) x = k.yP q :=
    yIndep D γ₀ q (k.pp q) γ (k.gaP q) hqp hs (k.pp_over q hqp hs) hat (k.gaP_at q hqp hs)
  have hπv : (k.pp q).valuation D.host.K ((k.pi q : 𝓞 D.host.K) : D.host.K) = WithZero.exp (-(h : ℤ)) :=
    GlobalTheory.T.valuation_eq_exp_neg_of_pow_eq_span_singleton D.host.K (k.pp q) h (k.pi q) (k.pi_gen q hqp hs)
  have hkap := GlobalTheory.T.complexPadic_norm_kappa_splitPrime D γ₀ k q hs ι
  have hrt := k.rt_pow q hqp hs
  have hrt0 := k.rt_ne_zero q hqp hs
  set y : ℤ := k.yP q with hydef
  set 𝔭 := k.pp q with h𝔭
  set π : 𝓞 D.host.K := k.pi q with hπdef
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hU
    simp at hU
  have hxx : ‖jK x‖ * ‖jK' x‖ = 1 := by
    rw [← norm_mul, ejK, ejK', ← map_mul, ← map_mul, hU, map_one, map_one, norm_one]
  obtain ⟨w, hqw, hw⟩ := exists_place jK
  obtain ⟨w', hqw', hw'⟩ := exists_place jK'
  have hne : w ≠ w' := by
    intro heq
    obtain ⟨y0, h1, h2⟩ := GlobalTheory.T.conjugate_embeddings_induce_different_primes_split D q hq2 hj ι
    have a1 : y0 ∈ w.asIdeal := (hw y0).2 (by rw [ejK]; exact h1)
    rw [heq, hw', ejK'] at a1
    exact absurd a1 (not_lt.2 h2)
  have hq𝔭 : ((q : ℕ) : 𝓞 D.host.K) ∈ 𝔭.asIdeal := k.pp_over q hqp hs
  have hnot : ∀ v : HeightOneSpectrum (𝓞 D.host.K), v ≠ 𝔭 → π ∉ v.asIdeal := by
    intro v hv hπ
    apply hv
    have h1 : 𝔭.asIdeal ^ h ≤ v.asIdeal := by
      rw [hh, k.pi_gen q hqp hs, Ideal.span_singleton_le_iff_mem]
      exact hπ
    have h2 : 𝔭.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le h1
    have h3 : 𝔭.asIdeal = v.asIdeal := 𝔭.isMaximal.eq_of_le v.isPrime.ne_top h2
    exact (HeightOneSpectrum.ext h3).symm
  have hone : ∀ (j : D.host.K →+* ℂ_[q]) (v : HeightOneSpectrum (𝓞 D.host.K)),
      (∀ z : 𝓞 D.host.K, z ∈ v.asIdeal ↔ ‖j (z : D.host.K)‖ < 1) → v ≠ 𝔭 → ‖j (π : D.host.K)‖ = 1 := by
    intro j v hv hv𝔭
    exact le_antisymm (norm_le_one_of_int j π) (not_lt.1 fun hlt => hnot v hv𝔭 ((hv π).2 hlt))
  have key : ‖jK x‖ ^ h = (‖jK (π : D.host.K)‖ / ‖jK' (π : D.host.K)‖) ^ y := by
    rcases GlobalTheory.T.quadratic_field_at_most_two_primes_over_prime D.host.K (kQuad D) q hqp 𝔭 w w' hq𝔭 hqw hqw' with e | e | e
    · have h1 := norm_pow_eq jK w hw h π (by rw [← e]; exact hπv) x hx0
      have h2 : -WithZero.log (w.valuation D.host.K x) = y := by rw [← e]; exact hy
      rw [h2] at h1
      rw [h1, hone jK' w' hw' (fun e' => hne (e.symm.trans e'.symm)), div_one]
    · have h1 := norm_pow_eq jK' w' hw' h π (by rw [← e]; exact hπv) x hx0
      have h2 : -WithZero.log (w'.valuation D.host.K x) = y := by rw [← e]; exact hy
      rw [h2] at h1
      rw [hone jK w hw (fun e' => hne (e'.trans e)), one_div, inv_zpow', zpow_neg, ← h1]
      have hx' : ‖jK x‖ = ‖jK' x‖⁻¹ := eq_inv_of_mul_eq_one_left hxx
      rw [hx', inv_pow]
    · exact absurd e hne
  have hjx : ‖ι (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E))‖ = ‖jK x‖ := rfl
  rw [hjx, hkap]
  rw [← hh] at hrt
  have hr0 : 0 < ‖ι (k.rt q)‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hrt0)
  have hratio : ‖jK (π : D.host.K)‖ / ‖jK' (π : D.host.K)‖ = ‖ι (k.rt q)‖ ^ (2 * h) := by
    rw [ejK, ejK', ← norm_div, ← map_div₀, ← hrt, map_pow, norm_pow]
  rw [hratio] at key
  have hh0 : h ≠ 0 := by rw [hh]; exact (NumberField.classNumber_pos D.host.K).ne'
  have hxr : ‖jK x‖ = ‖ι (k.rt q)‖ ^ (2 * y) := by
    have e : (‖ι (k.rt q)‖ ^ (2 * h)) ^ y = (‖ι (k.rt q)‖ ^ (2 * y)) ^ h := by
      rw [← zpow_natCast, ← zpow_natCast (‖ι (k.rt q)‖ ^ (2 * y)), ← zpow_mul, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [e] at key
    exact (pow_left_inj₀ (norm_nonneg _) (zpow_nonneg hr0.le _) hh0).1 key
  rw [hxr, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hr0.ne']
  rw [show -y * ((2 : ℕ) : ℤ) + 2 * y = 0 by push_cast; ring, zpow_zero]

end GlobalTheory.KapVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetIsometryEqOneStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_kappa_sq_mul_det_isometry_eq_one : ∀ (D : D7) (γ₀ γ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → γ.AtP q → ∀ ι : ℂ ≃+* ℂ_[q], ‖ι k.kappa‖ ^ 2 * ‖ι (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E))‖ = 1 := by
  first | exact @GlobalTheory.KapVal.norm_kappa_sq_mul_det | exact GlobalTheory.KapVal.norm_kappa_sq_mul_det | (intros; apply GlobalTheory.KapVal.norm_kappa_sq_mul_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetSplitPrime
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem norm_kappa_sq_mul_norm_det : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ‖ι B.kappa‖ ^ 2 * ‖ι (LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))‖ = 1 := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hcop ι u hu h1 h2 h3
  obtain ⟨γ, hγ, hdet⟩ := GlobalTheory.T.unitary_standard_at_q_from_isometry_over_field D cc δ B hcc hδ q hq2 hsplit hcop ι u hu h1 h2 h3
  rw [hdet]
  exact GlobalTheory.T.norm_kappa_sq_mul_det_isometry_eq_one D B.γ₀ γ B.kc q hq2 hsplit hγ ι

end GlobalTheory.MomN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetSplitPrimeStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_kappa_sq_mul_det_splitPrime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]), ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ‖ι B.kappa‖ ^ 2 * ‖ι (LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))‖ = 1 := by
  first | exact @GlobalTheory.MomN.norm_kappa_sq_mul_norm_det | exact GlobalTheory.MomN.norm_kappa_sq_mul_norm_det | (intros; apply GlobalTheory.MomN.norm_kappa_sq_mul_norm_det <;> assumption)
end
