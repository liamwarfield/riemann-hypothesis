module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarePresentationOfCounitalComul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomothetyLatSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupMulPUnitFibreEqLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPFlatStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastSmulMemAugIdealSqSupMapMulPStatement
open scoped TensorProduct
open Coalgebra GlobalTheory.PDiv in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCast_smul_mem_augIdealSq_sup_map_mulP : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))), (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 ⊔ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n a ha
  have ha₀ : counit (R := R) a = 0 := ha
  have hres : G.res n a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A n)) := by
    change counit (R := R) (G.res n a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha₀]
  have hmap : mulBy R (G.A (n + 1)) p a ∈ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
      ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
    rw [← G.mulP_res n a]
    exact Ideal.mem_map_of_mem _ hres
  have hdiff : mulBy R (G.A (n + 1)) p a - (p : R) • a ∈
      RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 := by
    have hd : dUnit (R := R) (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0 := by
      change GlobalTheory.AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))
        (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0
      rw [map_sub, map_smul]
      change dUnit (R := R) (mulBy R (G.A (n + 1)) p a) - (p : R) • dUnit (R := R) a = 0
      rw [← cotMap_d, cotMap_mulBy, sub_self]
    have h := (GlobalTheory.AugCot.d_eq_zero_iff _ _).1 hd
    have hc : Bialgebra.counitAlgHom R (G.A (n + 1))
        (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0 := by
      change counit (R := R) (mulBy R (G.A (n + 1)) p a - (p : R) • a) = 0
      rw [map_sub, map_smul, CoalgHomClass.counit_comp_apply, ha₀, smul_zero, sub_zero]
    rwa [hc, map_zero, sub_zero] at h
  have hsmul : (p : R) • a = mulBy R (G.A (n + 1)) p a - (mulBy R (G.A (n + 1)) p a - (p : R) • a) :=
    (sub_sub_cancel _ _).symm
  rw [hsmul]
  exact sub_mem (Ideal.mem_sup_right hmap) (Ideal.mem_sup_left hdiff)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSquarePresentationOfFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSupKerMulOfLeSupMaximalMulSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSupKerMulOfLeSupMaximalMulSection
open scoped TensorProduct

namespace GlobalTheory

theorem nakayama_at_section : ∀ (O P : Type) [CommRing O] [IsLocalRing O] [CommRing P] [Algebra O P] (η : P →ₐ[O] O) (J S : Ideal P), J.FG → J ≤ S ⊔ (IsLocalRing.maximalIdeal O).comap η * J → J ≤ S ⊔ RingHom.ker η * J := by
  intro O P _ _ _ _ η J S hJ h
  set S' : Ideal P := S ⊔ RingHom.ker η * J with hS'
  set n : Ideal P := (IsLocalRing.maximalIdeal O).comap η with hn
  have hK : (Submodule.map S'.mkQ J).FG := Submodule.FG.map _ hJ
  have hle : Submodule.map S'.mkQ J ≤ n • Submodule.map S'.mkQ J := by
    rw [← Submodule.map_smul'']
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp (h hj)
    refine Submodule.mem_map.mpr ⟨t, ht, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    have : t - (s + t) = -s := by ring
    rw [this]
    exact S'.neg_mem (Ideal.mem_sup_left hs)
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul n _ hK hle
  intro j hj
  have h1 : r * j ∈ S' := by
    have := hr _ (Submodule.mem_map_of_mem hj)
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    simpa using this
  have hu : IsUnit (η r) := by
    by_contra hne
    have a : η r ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hne
    have b : η r - 1 ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.mem_comap.mp hr1
      simpa [map_sub] using this
    have c : (1:O) ∈ IsLocalRing.maximalIdeal O := by
      have := sub_mem a b
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr c)
  obtain ⟨u, hu'⟩ := hu
  have hk : r - algebraMap O P (η r) ∈ RingHom.ker η := by
    rw [RingHom.mem_ker]
    simp
  have h2 : (r - algebraMap O P (η r)) * j ∈ S' := Ideal.mem_sup_right (Ideal.mul_mem_mul hk hj)
  have h3 : algebraMap O P (η r) * j ∈ S' := by
    have e : algebraMap O P (η r) * j = r * j - (r - algebraMap O P (η r)) * j := by ring
    rw [e]
    exact S'.sub_mem h1 h2
  have h4 : algebraMap O P (↑u⁻¹) * (algebraMap O P (η r) * j) ∈ S' := S'.mul_mem_left _ h3
  rwa [← mul_assoc, ← map_mul, ← hu', Units.inv_mul, map_one, one_mul] at h4

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeSupKerMulOfLeSupMaximalMulSectionStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_sup_ker_mul_of_le_sup_maximal_mul_section : ∀ (O P : Type) [CommRing O] [IsLocalRing O] [CommRing P] [Algebra O P] (η : P →ₐ[O] O) (J S : Ideal P), J.FG → J ≤ S ⊔ (IsLocalRing.maximalIdeal O).comap η * J → J ≤ S ⊔ RingHom.ker η * J := by
  first | exact @GlobalTheory.nakayama_at_section | exact GlobalTheory.nakayama_at_section | (intros; apply GlobalTheory.nakayama_at_section <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMapLeMapMulKerOfFlatTarget
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMapLeMapMulKerOfFlatTarget
open scoped TensorProduct

namespace GlobalTheory

theorem exists_fin_sum_of_mem_ideal_smul_top {B P : Type} [CommRing B] [AddCommGroup P]
    [Module B P] (I : Ideal B) {z : P} (hz : z ∈ I • (⊤ : Submodule B P)) :
    ∃ (n : ℕ) (b : Fin n → B) (p : Fin n → P), (∀ i, b i ∈ I) ∧ ∑ i, b i • p i = z := by
  refine Submodule.smul_induction_on hz
    (fun r hr m _ => ⟨1, fun _ => r, fun _ => m, fun _ => hr, by simp⟩) ?_
  rintro x y ⟨n, b, p, hb, rfl⟩ ⟨n', b', p', hb', rfl⟩
  refine ⟨n + n', Fin.append b b', Fin.append p p', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hb, hb']
  · simp [Fin.sum_univ_add]

theorem ker_inf_map_le_map_mul_ker_of_flat :
    ∀ (B P A : Type) [CommRing B] [CommRing P] [CommRing A] [Algebra B P] [Algebra B A]
      [Module.Flat B A] (Ψ : P →ₐ[B] A), Function.Surjective Ψ → ∀ I : Ideal B,
      RingHom.ker Ψ ⊓ I.map (algebraMap B P) ≤ I.map (algebraMap B P) * RingHom.ker Ψ := by
  intro B P A _ _ _ _ _ _ Ψ hΨ I z hz
  have hz1 : Ψ z = 0 := RingHom.mem_ker.1 hz.1
  have hz2 : z ∈ I • (⊤ : Submodule B P) := by
    rw [Ideal.smul_top_eq_map]; exact hz.2
  obtain ⟨n, b, p, hb, rfl⟩ := exists_fin_sum_of_mem_ideal_smul_top I hz2
  have h0 : ∑ i, b i • Ψ (p i) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, map_smul] using hz1
  obtain ⟨k, c, a, hx, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := B) (M := A)
    (f := b) (x := fun i => Ψ (p i)) h0
  choose q hq using fun j => hΨ (a j)
  have hzero : ∑ i, ∑ j, (b i * c i j) • q j = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul, hc j, zero_smul]
  have key : ∑ i, b i • p i = ∑ i, b i • (p i - ∑ j, c i j • q j) := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, hzero, sub_zero]
  rw [key]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hb i)) ?_
  rw [RingHom.mem_ker]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_smul, hq, ← hx i, sub_self]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMapLeMapMulKerOfFlatTargetStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_inf_map_le_map_mul_ker_of_flat_target : ∀ (B P A : Type) [CommRing B] [CommRing P] [CommRing A] [Algebra B P] [Algebra B A] [Module.Flat B A] (Ψ : P →ₐ[B] A), Function.Surjective Ψ → ∀ I : Ideal B, RingHom.ker Ψ ⊓ I.map (algebraMap B P) ≤ I.map (algebraMap B P) * RingHom.ker Ψ := by
  first | exact @GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat | exact GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat | (intros; apply GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSquarePresentationOfFlat
open scoped TensorProduct

namespace GlobalTheory

theorem lift_square_presentation_of_flat : ∀ (O B A k H σ : Type) [CommRing O] [IsLocalRing O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Module.Flat B A] [Field k] [CommRing H] [Algebra k H] [Fintype σ] (ε : A →ₐ[O] O) (π : O →+* k) (ρ : A →+* H) (εH : H →ₐ[k] k) (x : σ → A), Function.Surjective π → RingHom.ker π = IsLocalRing.maximalIdeal O → (∀ c : O, ρ (algebraMap O A c) = algebraMap k H (π c)) → (∀ a, εH (ρ a) = π (ε a)) → RingHom.ker ρ = (RingHom.ker (π.comp ((ε : A →+* O).comp (algebraMap B A)))).map (algebraMap B A) → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A)).FG → ∀ g : σ → MvPolynomial σ k, (∀ i, MvPolynomial.aeval (fun j => ρ (x j)) (g i) = 0) → RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (εH.comp (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H)) * RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) → ∃ f : σ → MvPolynomial σ B, (∀ i, MvPolynomial.aeval x (f i) = 0) ∧ RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) := by
  intro O B A k H σ _ _ _ _ _ _ _ _ _ _ _ _ _ ε π ρ εH x hπ hker hρO hε hρ hx hfg g hg hJ
  classical
  set τ : B →+* k := π.comp ((ε : A →+* O).comp (algebraMap B A)) with hτ
  have hτb : ∀ b, τ b = π (ε (algebraMap B A b)) := fun b => rfl
  have hτO : ∀ c, τ (algebraMap O B c) = π c := by
    intro c
    rw [hτb, ← IsScalarTower.algebraMap_apply, AlgHom.commutes]
    rfl
  have hτs : Function.Surjective τ := by
    intro y
    obtain ⟨c, rfl⟩ := hπ y
    exact ⟨_, hτO c⟩
  have hρB : ∀ b, ρ (algebraMap B A b) = algebraMap k H (τ b) := by
    intro b
    have h1 : b - algebraMap O B (ε (algebraMap B A b)) ∈ RingHom.ker τ := by
      rw [RingHom.mem_ker, map_sub, hτO, hτb, sub_self]
    have h2 : algebraMap B A (b - algebraMap O B (ε (algebraMap B A b))) ∈ RingHom.ker ρ := by
      rw [hρ]
      exact Ideal.mem_map_of_mem _ h1
    rw [RingHom.mem_ker, map_sub, map_sub, ← IsScalarTower.algebraMap_apply, hρO,
      sub_eq_zero] at h2
    rw [h2, hτb]
  set Ψ : MvPolynomial σ B →ₐ[B] A := MvPolynomial.aeval x with hΨ
  set Φ : MvPolynomial σ k →ₐ[k] H := MvPolynomial.aeval (fun j => ρ (x j)) with hΦ
  set T : MvPolynomial σ B →+* MvPolynomial σ k := MvPolynomial.map τ with hT
  have hcomm : ∀ F, ρ (Ψ F) = Φ (T F) := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp [hΨ, hΦ, hT, hρB]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp]
      simp [hΨ, hΦ, hT]
  have hTs : Function.Surjective T := MvPolynomial.map_surjective τ hτs
  have hTk : RingHom.ker T = (RingHom.ker τ).map (algebraMap B (MvPolynomial σ B)) :=
    MvPolynomial.ker_map τ
  have hlift : ∀ G, Φ G = 0 → ∃ F, Ψ F = 0 ∧ T F = G := by
    intro G hG
    obtain ⟨F0, rfl⟩ := hTs G
    have h1 : Ψ F0 ∈ ((RingHom.ker τ).map (algebraMap B (MvPolynomial σ B))).map
        (Ψ : MvPolynomial σ B →+* A) := by
      rw [Ideal.map_map, AlgHom.comp_algebraMap, ← hρ, RingHom.mem_ker, hcomm, hG]
    rw [Ideal.mem_map_iff_of_surjective (Ψ : MvPolynomial σ B →+* A) hx] at h1
    obtain ⟨F1, hF1, hF⟩ := h1
    rw [← hTk, RingHom.mem_ker] at hF1
    refine ⟨F0 - F1, ?_, ?_⟩
    · rw [map_sub, sub_eq_zero]
      exact hF.symm
    · rw [map_sub, hF1, sub_zero]
  choose f hf hfT using fun i => hlift (g i) (hg i)
  refine ⟨f, hf, ?_⟩
  let η : MvPolynomial σ B →ₐ[O] O := ε.comp (Ψ.restrictScalars O)
  have hη : ∀ F, η F = ε (Ψ F) := fun F => rfl
  have hn : ∀ F, F ∈ (IsLocalRing.maximalIdeal O).comap η ↔ εH (Φ (T F)) = 0 := by
    intro F
    rw [Ideal.mem_comap, ← hker, RingHom.mem_ker, ← hcomm, hε, hη]
  have key : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔
      (IsLocalRing.maximalIdeal O).comap η * RingHom.ker Ψ := by
    have hle : Ideal.span (Set.range g) ⊔ RingHom.ker (εH.comp Φ) * RingHom.ker Φ ≤
        (Ideal.span (Set.range f) ⊔
          (IsLocalRing.maximalIdeal O).comap η * RingHom.ker Ψ).map T := by
      rw [Ideal.map_sup, Ideal.map_mul]
      refine sup_le_sup ?_ (Ideal.mul_mono ?_ ?_)
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        rw [← hfT i]
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
      · intro G hG
        obtain ⟨F, rfl⟩ := hTs G
        exact Ideal.mem_map_of_mem _ ((hn F).2 hG)
      · intro G hG
        obtain ⟨F, hF, rfl⟩ := hlift G hG
        exact Ideal.mem_map_of_mem _ hF
    have hS : Ideal.span (Set.range f) ⊔
        (IsLocalRing.maximalIdeal O).comap η * RingHom.ker Ψ ≤ RingHom.ker Ψ := by
      refine sup_le ?_ Ideal.mul_le_right
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hf i
    have hp : (RingHom.ker τ).map (algebraMap B (MvPolynomial σ B)) ≤
        (IsLocalRing.maximalIdeal O).comap η := by
      rw [← hTk]
      intro F hF
      rw [hn, (RingHom.mem_ker).1 hF, map_zero, map_zero]
    intro F hF
    have h1 : T F ∈ RingHom.ker Φ := by
      rw [RingHom.mem_ker, ← hcomm, (RingHom.mem_ker).1 hF, map_zero]
    obtain ⟨F1, hF1, hF'⟩ := (Ideal.mem_map_iff_of_surjective T hTs).1 (hle (hJ h1))
    have h2 : F - F1 ∈ RingHom.ker Ψ ⊓
        (RingHom.ker τ).map (algebraMap B (MvPolynomial σ B)) := by
      refine ⟨sub_mem hF (hS hF1), ?_⟩
      rw [← hTk]
      show T (F - F1) = 0
      rw [map_sub, hF', sub_self]
    have h3 := Ideal.mul_mono_left hp
      (GlobalTheory.T.ker_inf_map_le_map_mul_ker_of_flat_target B (MvPolynomial σ B) A Ψ hx (RingHom.ker τ) h2)
    have h4 : F = F1 + (F - F1) := by ring
    rw [h4]
    exact add_mem hF1 (Ideal.mem_sup_right h3)
  exact GlobalTheory.T.le_sup_ker_mul_of_le_sup_maximal_mul_section O (MvPolynomial σ B) η _ _ hfg key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSquarePresentationOfFlatStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_square_presentation_of_flat_alt : ∀ (O B A k H σ : Type) [CommRing O] [IsLocalRing O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Module.Flat B A] [Field k] [CommRing H] [Algebra k H] [Fintype σ] (ε : A →ₐ[O] O) (π : O →+* k) (ρ : A →+* H) (εH : H →ₐ[k] k) (x : σ → A), Function.Surjective π → RingHom.ker π = IsLocalRing.maximalIdeal O → (∀ c : O, ρ (algebraMap O A c) = algebraMap k H (π c)) → (∀ a, εH (ρ a) = π (ε a)) → RingHom.ker ρ = (RingHom.ker (π.comp ((ε : A →+* O).comp (algebraMap B A)))).map (algebraMap B A) → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A)).FG → ∀ g : σ → MvPolynomial σ k, (∀ i, MvPolynomial.aeval (fun j => ρ (x j)) (g i) = 0) → RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (εH.comp (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H)) * RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) → ∃ f : σ → MvPolynomial σ B, (∀ i, MvPolynomial.aeval x (f i) = 0) ∧ RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) := by
  first | exact @GlobalTheory.lift_square_presentation_of_flat | exact GlobalTheory.lift_square_presentation_of_flat | (intros; apply GlobalTheory.lift_square_presentation_of_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentMapInjectiveOfSquarePresentationAtPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentMapInjectiveOfSquarePresentationAtPoint
open scoped TensorProduct

namespace GlobalTheory.CotangentSquare

open MvPolynomial

variable {O B σ : Type} [CommRing O] [CommRing B]

def firstOrderKer (η : MvPolynomial σ B →+* O) : Ideal (MvPolynomial σ B) where
  carrier := {F | η F = 0 ∧ ∀ l, η (pderiv l F) = 0}
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    exact ⟨by simp [hF, hG], fun l => by simp [hF' l, hG' l]⟩
  zero_mem' := ⟨by simp, fun l => by simp⟩
  smul_mem' := by
    rintro G F ⟨hF, hF'⟩
    exact ⟨by simp [hF], fun l => by simp [pderiv_mul, hF, hF' l]⟩

theorem pderiv_comb [Fintype σ] (η : MvPolynomial σ B →+* O) (f g : σ → MvPolynomial σ B)
    (hf : ∀ i, η (f i) = 0) (k : MvPolynomial σ B) (hk : k ∈ firstOrderKer η) (l : σ) :
    η (pderiv l (∑ i, g i * f i + k)) = ∑ i, η (g i) * η (pderiv l (f i)) := by
  have := hk.2 l
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, pderiv_mul, hf, this]

theorem det_ne_zero_of_mul_eq [Fintype σ] [DecidableEq σ] [IsDomain O] {N J : Matrix σ σ O}
    {c : O} (hc : c ≠ 0) (h : N * J = c • (1 : Matrix σ σ O)) : J.det ≠ 0 := by
  intro hJ
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, hJ, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ hc this.symm

theorem cotangent_map_injective_of_square_presentation : ∀ (O B A σ : Type) [CommRing O] [IsDomain O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Fintype σ] (ε : A →ₐ[O] O) (x : σ → A) (f : σ → MvPolynomial σ B) (c : O), c ≠ 0 → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ i, MvPolynomial.aeval x (f i) = 0) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ a ∈ RingHom.ker ε, c • a ∈ RingHom.ker ε ^ 2 ⊔ ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A)) → ∀ b : B, algebraMap B A b ∈ RingHom.ker ε ^ 2 → b ∈ ((RingHom.ker ε).comap (algebraMap B A)) ^ 2 := by
  intro O B A σ _ _ _ _ _ _ _ _ _ ε x f c hc hsurj hf hker hc2 b hb
  classical
  set Ψ := (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) with hΨ
  let η : MvPolynomial σ B →+* O := (ε : A →+* O).comp (Ψ : MvPolynomial σ B →+* A)
  have hη : ∀ F, η F = ε (Ψ F) := fun F => rfl
  set q := (RingHom.ker ε).comap Ψ with hq
  have hqmem : ∀ F, F ∈ q ↔ η F = 0 := fun F => by
    rw [hq, Ideal.mem_comap, RingHom.mem_ker, hη]
  have hkerq : RingHom.ker Ψ ≤ q := fun F hF => by
    rw [hqmem, hη, (RingHom.mem_ker).1 hF, map_zero]
  have hηf : ∀ i, η (f i) = 0 := fun i => by rw [hη, hf i, map_zero]
  set K := firstOrderKer η with hK
  have hq2 : q ^ 2 ≤ K := by
    rw [pow_two]
    refine Ideal.mul_le.2 fun a ha b' hb' => ?_
    rw [hqmem] at ha hb'
    exact ⟨by simp [ha, hb'], fun l => by simp [pderiv_mul, ha, hb']⟩
  have hkerL : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ q ^ 2 := by
    refine hker.trans (sup_le_sup_left ?_ _)
    rw [pow_two]; exact Ideal.mul_mono_right hkerq
  have hkerK : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ K := hkerL.trans (sup_le_sup_left hq2 _)
  have hsq : RingHom.ker ε ^ 2 = (q ^ 2).map Ψ := by
    rw [Ideal.map_pow, hq, Ideal.map_comap_of_surjective Ψ hsurj]
  have lift : ∀ (L : Ideal (MvPolynomial σ B)), RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ L →
      ∀ F, Ψ F ∈ L.map Ψ → F ∈ Ideal.span (Set.range f) ⊔ L := by
    intro L hL F hF
    obtain ⟨G, hG, hGF⟩ := (Ideal.mem_map_iff_of_surjective Ψ hsurj).1 hF
    have h1 : F - G ∈ RingHom.ker Ψ := by rw [RingHom.mem_ker, map_sub, hGF, sub_self]
    have h2 : F = (F - G) + G := by ring
    rw [h2]; exact Ideal.add_mem _ (hL h1) (Ideal.mem_sup_right hG)
  have hIB : ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A) ≤ K.map Ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, RingHom.mem_ker] at hi
    rw [Ideal.mem_comap]
    have : algebraMap B A i = Ψ (C i) := by simp [hΨ]
    rw [this]
    refine Ideal.mem_map_of_mem _ ⟨?_, fun l => by simp⟩
    rw [hη]; simpa [hΨ] using hi
  let Jac : Matrix σ σ O := fun i l => η (pderiv l (f i))
  have hrow : ∀ j, ∃ g : σ → MvPolynomial σ B, ∀ l,
      (if j = l then c else 0) = ∑ i, η (g i) * Jac i l := by
    intro j
    set F := C (algebraMap O B c) * (X j - C (algebraMap O B (ε (x j)))) with hF
    have ha : x j - algebraMap O A (ε (x j)) ∈ RingHom.ker ε := by
      rw [RingHom.mem_ker]; simp
    have hΨF : Ψ F = c • (x j - algebraMap O A (ε (x j))) := by
      simp [hF, hΨ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
    have hmem : Ψ F ∈ K.map Ψ := by
      rw [hΨF]
      refine (sup_le ?_ hIB) (hc2 _ ha)
      rw [hsq]; exact Ideal.map_mono hq2
    have hF2 := lift K hkerK F hmem
    rw [Submodule.mem_sup] at hF2
    obtain ⟨s, hs, k, hk, hsk⟩ := hF2
    obtain ⟨g, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
    refine ⟨g, fun l => ?_⟩
    have e1 := pderiv_comb η f g hηf k hk l
    rw [hsk] at e1
    rw [← e1, hF]
    by_cases hjl : j = l
    · subst hjl
      simp [pderiv_X_self, hη, hΨ, ← IsScalarTower.algebraMap_apply]
    · simp [hjl, pderiv_X_of_ne (Ne.symm hjl)]
  choose g hg using hrow
  let N : Matrix σ σ O := fun j i => η (g j i)
  have hNJ : N * Jac = c • (1 : Matrix σ σ O) := by
    ext j l
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, ← hg j l]
    split_ifs <;> simp
  have hdet : Jac.det ≠ 0 := det_ne_zero_of_mul_eq hc hNJ
  have hCb : C b ∈ Ideal.span (Set.range f) ⊔ q ^ 2 := by
    refine lift _ hkerL (C b) ?_
    rw [← hsq]; simpa [hΨ] using hb
  rw [Submodule.mem_sup] at hCb
  obtain ⟨s, hs, k, hk, hsk⟩ := hCb
  obtain ⟨g', rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
  have hv : Matrix.vecMul (fun i => η (g' i)) Jac = 0 := by
    funext l
    have e1 := pderiv_comb η f g' hηf k (hq2 hk) l
    rw [hsk] at e1
    simp only [pderiv_C, map_zero] at e1
    change ∑ i, η (g' i) * Jac i l = 0
    exact e1.symm
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  have hCq : C b ∈ q ^ 2 := by
    rw [← hsk]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => ?_) hk
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ (hkerq ?_)
    · rw [hqmem]; exact congrFun hv0 i
    · rw [RingHom.mem_ker]; exact hf i
  let ev : MvPolynomial σ B →ₐ[B] B := aeval (fun j => algebraMap O B (ε (x j)))
  have hev : ((ε : A →+* O).comp (algebraMap B A)).comp (ev : MvPolynomial σ B →+* B) = η := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ev, η, hΨ]
    · intro i; simp [ev, η, hΨ, ← IsScalarTower.algebraMap_apply]
  have hqev : q.map ev ≤ (RingHom.ker ε).comap (algebraMap B A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [hqmem] at hF
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← hF, ← hev]
    rfl
  have : b = ev (C b) := by simp [ev]
  rw [this]
  exact Ideal.pow_right_mono hqev 2 (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hCq)

end GlobalTheory.CotangentSquare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentMapInjectiveOfSquarePresentationAtPointStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cotangent_map_injective_of_square_presentation_at_point : ∀ (O B A σ : Type) [CommRing O] [IsDomain O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Fintype σ] (ε : A →ₐ[O] O) (x : σ → A) (f : σ → MvPolynomial σ B) (c : O), c ≠ 0 → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ i, MvPolynomial.aeval x (f i) = 0) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ a ∈ RingHom.ker ε, c • a ∈ RingHom.ker ε ^ 2 ⊔ ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A)) → ∀ b : B, algebraMap B A b ∈ RingHom.ker ε ^ 2 → b ∈ ((RingHom.ker ε).comap (algebraMap B A)) ^ 2 := by
  first | exact @GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation | exact GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation | (intros; apply GlobalTheory.CotangentSquare.cotangent_map_injective_of_square_presentation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationSquareAtPointOfLocalFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationSquareAtPointOfLocalFactor
open scoped TensorProduct

namespace GlobalTheory

theorem sqloc_present : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (e : A), ε e = 1 → IsIdempotentElem e → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] (A ⧸ Ideal.span {1 - e})) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → ∀ (r : ℕ) (a : Fin r → A), Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin r) k →ₐ[k] A) → ∃ (s : ℕ) (y : Fin s → A) (g : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k), (∀ i, MvPolynomial.aeval (Sum.elim y a) (g i) = 0) ∧ RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (ε.comp (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A)) * RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) := by
  intro k A _ _ _ ε e he hidem ⟨s, φ, g', hφ, hker⟩ r a ha
  classical
  choose y hy using fun i : Fin s => Ideal.Quotient.mk_surjective (I := Ideal.span {1 - e}) (φ (MvPolynomial.X i))
  choose h hh using fun j : Fin r => hφ (Ideal.Quotient.mk (Ideal.span {1 - e}) (a j))
  set Ψ : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A := MvPolynomial.aeval (Sum.elim y a) with hΨ
  have hΨsurj : Function.Surjective Ψ := by
    intro x
    obtain ⟨p, hp⟩ := ha x
    refine ⟨MvPolynomial.rename Sum.inr p, ?_⟩
    rw [hΨ, MvPolynomial.aeval_rename, Sum.elim_comp_inr]
    exact hp
  obtain ⟨u, hu⟩ := hΨsurj e
  set κ : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] MvPolynomial (Fin s) k :=
    MvPolynomial.aeval (Sum.elim MvPolynomial.X h) with hκdef
  have hκ : (Ideal.Quotient.mkₐ k (Ideal.span {1 - e})).comp Ψ = φ.comp κ := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | j
    · simp [hΨ, hκdef, hy]
    · simp [hΨ, hκdef, hh]
  have hκF : ∀ F, Ideal.Quotient.mk (Ideal.span {1 - e}) (Ψ F) = φ (κ F) := by
    intro F
    have := congrArg (fun f => f F) hκ
    simpa using this
  let G : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k :=
    Sum.elim (fun i => MvPolynomial.rename Sum.inl (g' i))
      (fun j => MvPolynomial.X (Sum.inr j) - MvPolynomial.rename Sum.inl (h j))
  have hκr : ∀ p, κ (MvPolynomial.rename Sum.inl p) = p := by
    intro p
    rw [hκdef, MvPolynomial.aeval_rename, Sum.elim_comp_inl, MvPolynomial.aeval_X_left_apply]
  have hκX : ∀ j, κ (MvPolynomial.X (Sum.inr j)) = h j := by
    intro j
    rw [hκdef, MvPolynomial.aeval_X, Sum.elim_inr]
  have hg'ker : ∀ i, φ (g' i) = 0 := by
    intro i
    have : g' i ∈ RingHom.ker φ := hker ▸ Ideal.subset_span ⟨i, rfl⟩
    simpa using this
  have hΨG : ∀ i, Ideal.Quotient.mk (Ideal.span {1 - e}) (Ψ (G i)) = 0 := by
    intro i
    rw [hκF]
    rcases i with i | j
    · simp only [G, Sum.elim_inl, hκr, hg'ker]
    · simp only [G, Sum.elim_inr, map_sub, hκr, hκX, sub_self, map_zero]
  have hΨuG : ∀ i, Ψ (u * G i) = 0 := by
    intro i
    have hm : Ψ (G i) ∈ Ideal.span {1 - e} := Ideal.Quotient.eq_zero_iff_mem.mp (hΨG i)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hm
    rw [map_mul, hu, ← hc]
    have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hidem.eq, sub_self]
    calc e * (c * (1 - e)) = c * (e * (1 - e)) := by ring
      _ = 0 := by rw [h0, mul_zero]
  refine ⟨s, y, fun i => u * G i, hΨuG, ?_⟩
  rw [← hΨ]
  intro F hF
  rw [RingHom.mem_ker] at hF

  have hFG : F ∈ Ideal.span (Set.range G) := by
    have hq : (Ideal.Quotient.mkₐ k (Ideal.span (Set.range G))).comp
        ((MvPolynomial.rename Sum.inl).comp κ) = Ideal.Quotient.mkₐ k (Ideal.span (Set.range G)) := by
      apply MvPolynomial.algHom_ext
      intro i
      rcases i with i | j
      · simp only [AlgHom.comp_apply, hκdef, MvPolynomial.aeval_X, Sum.elim_inl,
          MvPolynomial.rename_X]
      · simp only [AlgHom.comp_apply, hκX, Ideal.Quotient.mkₐ_eq_mk]
        rw [Ideal.Quotient.eq]
        rw [← neg_sub, neg_mem_iff]
        exact Ideal.subset_span ⟨Sum.inr j, rfl⟩
    have h1 : F - MvPolynomial.rename Sum.inl (κ F) ∈ Ideal.span (Set.range G) := by
      have := congrArg (fun f => f F) hq
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
      rw [← neg_sub, neg_mem_iff]
      exact Ideal.Quotient.eq.mp this
    have hmem : κ F ∈ Ideal.span (Set.range g') := by
      rw [← hker, RingHom.mem_ker, ← hκF, hF, map_zero]
    have h2 : MvPolynomial.rename Sum.inl (κ F) ∈ Ideal.span (Set.range G) := by
      have := Ideal.mem_map_of_mem (MvPolynomial.rename (R := k) (Sum.inl : Fin s → Fin s ⊕ Fin r)) hmem
      rw [Ideal.map_span] at this
      refine Ideal.span_mono ?_ this
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, rfl⟩
    have := Ideal.add_mem _ h1 h2
    simpa using this
  have hsplit : F = u * F + (1 - u) * F := by ring
  rw [hsplit]
  refine Submodule.add_mem_sup ?_ ?_
  · obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hFG
    refine (Ideal.mem_span_range_iff_exists_fun).mpr ⟨c, ?_⟩
    rw [← hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · apply Ideal.mul_mem_mul
    · rw [RingHom.mem_ker]
      simp [hu, he]
    · exact hF

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationSquareAtPointOfLocalFactorStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_presentation_square_at_point_of_localFactor : ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (e : A), ε e = 1 → IsIdempotentElem e → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] (A ⧸ Ideal.span {1 - e})) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → ∀ (r : ℕ) (a : Fin r → A), Function.Surjective (MvPolynomial.aeval a : MvPolynomial (Fin r) k →ₐ[k] A) → ∃ (s : ℕ) (y : Fin s → A) (g : Fin s ⊕ Fin r → MvPolynomial (Fin s ⊕ Fin r) k), (∀ i, MvPolynomial.aeval (Sum.elim y a) (g i) = 0) ∧ RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (ε.comp (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A)) * RingHom.ker (MvPolynomial.aeval (Sum.elim y a) : MvPolynomial (Fin s ⊕ Fin r) k →ₐ[k] A) := by
  first | exact @GlobalTheory.sqloc_present | exact GlobalTheory.sqloc_present | (intros; apply GlobalTheory.sqloc_present <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorAtAugmentationCounitalComul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorAtAugmentationCounitalComul
open scoped TensorProduct

namespace GlobalTheory

theorem localFactor_counital_descends :
    ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ e : A, ε e = 1 ∧ IsIdempotentElem e ∧ ∃ (ε' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] k) (Δ' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] (A ⧸ Ideal.span {1 - e}) ⊗[k] (A ⧸ Ideal.span {1 - e})), ((∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.lid k (A ⧸ Ideal.span {1 - e}) (LinearMap.rTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a) ∧ (∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.rid k (A ⧸ Ideal.span {1 - e}) (LinearMap.lTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a)) ∧ IsNilpotent (RingHom.ker ε') := by
  intro k A _ _ _ _ ε Δ ⟨hL, hR⟩
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  set I : Ideal A := RingHom.ker ε with hI
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes
    (⟨fun m => OrderDual.toDual (I ^ m), fun a b h => Ideal.pow_le_pow_right h⟩ : ℕ →o (Ideal A)ᵒᵈ)
  have hst : ∀ m, n ≤ m → I ^ n = I ^ m := fun m hm => hn m hm
  set N := n + 1 with hN
  set J : Ideal A := I ^ N with hJ
  have hJJ : IsIdempotentElem J := by
    show J * J = J
    rw [hJ, ← pow_add, ← hst (N + N) (by omega), hst N (by omega)]
  have hfg : J.FG := IsNoetherian.noetherian J
  obtain ⟨e', he', hJe⟩ := (Ideal.isIdempotentElem_iff_of_fg J hfg).mp hJJ
  have he'J : e' ∈ J := by rw [hJe]; exact Submodule.mem_span_singleton_self e'
  have hJI : J ≤ I := Ideal.pow_le_self (by omega)
  have he'0 : ε e' = 0 := hJI he'J
  refine ⟨1 - e', by simp [he'0], he'.one_sub, ?_⟩
  have hspan : Ideal.span {1 - (1 - e')} = J := by
    rw [sub_sub_cancel, hJe]
  rw [hspan]
  set mk : A →ₐ[k] A ⧸ J := Ideal.Quotient.mkₐ k J with hmk
  let ε' : A ⧸ J →ₐ[k] k := Ideal.Quotient.liftₐ J ε (fun a ha => hJI ha)
  have hε' : ∀ a, ε' (mk a) = ε a := fun a => rfl
  have hnil : ∀ y ∈ RingHom.ker ε', IsNilpotent y := by
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J y
    have ha : a ∈ I := by rw [RingHom.mem_ker] at hy ⊢; rw [← hε']; exact hy
    refine ⟨N, ?_⟩
    rw [← map_pow]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.pow_mem_pow ha N)
  let φ : (A ⧸ J) ⊗[k] (A ⧸ J) →ₐ[k] k := Algebra.TensorProduct.productMap ε' ε'
  let Δ'' : A →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := (Algebra.TensorProduct.map mk mk).comp Δ
  have hφ : ∀ t : A ⊗[k] A, φ (Algebra.TensorProduct.map mk mk t)
      = ε (TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [φ, hε', mul_comm]
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
  have hφΔ : ∀ a, φ (Δ'' a) = ε a := by
    intro a
    show φ (Algebra.TensorProduct.map mk mk (Δ a)) = ε a
    rw [hφ, hR]
  let iL : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := Algebra.TensorProduct.includeLeft
  let iR : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := Algebra.TensorProduct.includeRight
  have key : ∀ t : (A ⧸ J) ⊗[k] (A ⧸ J), t - algebraMap k _ (φ t) ∈ nilradical _ := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      set u := x - algebraMap k (A ⧸ J) (ε' x) with hu
      set v := y - algebraMap k (A ⧸ J) (ε' y) with hv
      have hu0 : IsNilpotent u := hnil _ (by simp [RingHom.mem_ker, u])
      have hv0 : IsNilpotent v := hnil _ (by simp [RingHom.mem_ker, v])
      have hL : iL u ∈ nilradical _ :=
        mem_nilradical.2 (hu0.map _)
      have hR' : iR v ∈ nilradical _ :=
        mem_nilradical.2 (hv0.map _)
      have heq : x ⊗ₜ[k] y - algebraMap k _ (φ (x ⊗ₜ[k] y)) =
          iL u * iR v
          + algebraMap k _ (ε' y) * iL u
          + algebraMap k _ (ε' x) * iR v := by
        have h1 : x ⊗ₜ[k] y = iL x * iR y := by
          simp [iL, iR, Algebra.TensorProduct.tmul_mul_tmul]
        have h2 : iL x = iL u + algebraMap k _ (ε' x) := by
          rw [← AlgHom.commutes iL, ← map_add (f := _)]; simp [u]
        have h3 : iR y = iR v + algebraMap k _ (ε' y) := by
          rw [← AlgHom.commutes iR, ← map_add (f := _)]; simp [v]
        have h4 : φ (x ⊗ₜ[k] y) = ε' x * ε' y := by simp [φ]
        rw [h4, map_mul, h1, h2, h3]; ring
      rw [heq]
      exact add_mem (add_mem (Ideal.mul_mem_right _ _ hL) (Ideal.mul_mem_left _ _ hL)) (Ideal.mul_mem_left _ _ hR')
    | add s t hs ht =>
      have := add_mem hs ht
      convert this using 1
      simp only [map_add (f := _)]; abel
  have hkill : ∀ a ∈ J, Δ'' a = 0 := by
    have h0 : Δ'' e' = 0 := by
      apply (he'.map Δ'').eq_zero_of_isNilpotent
      have := mem_nilradical.1 (key (Δ'' e'))
      rwa [hφΔ, he'0, map_zero, sub_zero] at this
    intro a ha
    rw [hJe] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, h0, mul_zero]
  let Δ' : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := Ideal.Quotient.liftₐ J Δ'' hkill
  have hΔ' : ∀ a, Δ' (mk a) = Algebra.TensorProduct.map mk mk (Δ a) := fun a => rfl
  refine ⟨ε', Δ', ⟨?_, ?_⟩, ?_⟩
  · intro a'
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J a'
    have gen : ∀ t : A ⊗[k] A, TensorProduct.lid k (A ⧸ J) (LinearMap.rTensor (A ⧸ J) ε'.toLinearMap
        (Algebra.TensorProduct.map mk mk t)) = mk (TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [hε']
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    rw [← hmk, hΔ', gen, hL]
  · intro a'
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J a'
    have gen : ∀ t : A ⊗[k] A, TensorProduct.rid k (A ⧸ J) (LinearMap.lTensor (A ⧸ J) ε'.toLinearMap
        (Algebra.TensorProduct.map mk mk t)) = mk (TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [hε']
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    rw [← hmk, hΔ', gen, hR]
  · rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro y hy
    exact mem_nilradical.2 (hnil y hy)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorAtAugmentationCounitalComulStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFactor_at_augmentation_counital_comul : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ e : A, ε e = 1 ∧ IsIdempotentElem e ∧ ∃ (ε' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] k) (Δ' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] (A ⧸ Ideal.span {1 - e}) ⊗[k] (A ⧸ Ideal.span {1 - e})), ((∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.lid k (A ⧸ Ideal.span {1 - e}) (LinearMap.rTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a) ∧ (∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.rid k (A ⧸ Ideal.span {1 - e}) (LinearMap.lTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a)) ∧ IsNilpotent (RingHom.ker ε') := by
  first | exact @GlobalTheory.localFactor_counital_descends | exact GlobalTheory.localFactor_counital_descends | (intros; apply GlobalTheory.localFactor_counital_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemSqCounitKer
open scoped TensorProduct

theorem GlobalTheory.PDivGroup.mulP_mem_sq_counit : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], (p : O) ≠ 0 → ¬IsUnit (p : O) → (∀ a : O, ∃ b : O, b ^ p = a) → ∀ (G : GlobalTheory.PDivGroup p O) (n : ℕ) (b : G.A n), G.mulP n b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 := by
  intro p hp O _ _ _ hp0 hpu hroot G n b hb

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 hpu
  haveI : CharP (IsLocalRing.ResidueField O) p := (CharP.charP_iff_prime_eq_zero hp.out).2 hpk
  haveI : ExpChar (IsLocalRing.ResidueField O) p := ExpChar.prime hp.out
  haveI : PerfectRing (IsLocalRing.ResidueField O) p :=
    PerfectRing.ofSurjective _ p (fun y => by
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨c, hc⟩ := hroot a
      exact ⟨IsLocalRing.residue O c, by rw [frobenius_def, ← map_pow, hc]⟩)

  letI : Algebra (G.A n) (G.A (n + 1)) :=
    ((G.mulP n : G.A n →ₐ[O] G.A (n + 1)) : G.A n →+* G.A (n + 1)).toAlgebra
  haveI : IsScalarTower O (G.A n) (G.A (n + 1)) :=
    IsScalarTower.of_algebraMap_eq fun c => ((G.mulP n : G.A n →ₐ[O] G.A (n + 1)).commutes c).symm
  haveI : Module.Flat (G.A n) (G.A (n + 1)) := GlobalTheory.T.mulP_flat' p O G n
  have hε : ∀ b : G.A n, Bialgebra.counitAlgHom O (G.A (n + 1)) (algebraMap (G.A n) (G.A (n + 1)) b) =
      Bialgebra.counitAlgHom O (G.A n) b := fun b => by
    rw [Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply]
    exact CoalgHomClass.counit_comp_apply (G.mulP n) b
  have hker : (RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1)))).comap (algebraMap (G.A n) (G.A (n + 1))) =
      RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) := by
    ext b
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, hε]

  obtain ⟨ρ, hρ⟩ : ∃ ρ : G.A (n + 1) →+* IsLocalRing.ResidueField O ⊗[O] G.A 1,
      ∀ a, ρ a = 1 ⊗ₜ G.resOne n a :=
    ⟨(Algebra.TensorProduct.includeRight : G.A 1 →ₐ[O] IsLocalRing.ResidueField O ⊗[O] G.A 1).toRingHom.comp
      ((G.resOne n : G.A (n + 1) →ₐ[O] G.A 1) : G.A (n + 1) →+* G.A 1), fun _ => rfl⟩
  have hπs : Function.Surjective (algebraMap O (IsLocalRing.ResidueField O)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]; exact IsLocalRing.residue_surjective
  have hπk : RingHom.ker (algebraMap O (IsLocalRing.ResidueField O)) = IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue]
  have hfib := GlobalTheory.T.pDivGroup_mulP_unit_fiber_eq_level_one p O (IsLocalRing.ResidueField O) hπs G n
  have hρs : Function.Surjective ρ := fun h => by
    obtain ⟨a, ha⟩ := hfib.1 h
    exact ⟨a, by rw [hρ]; exact ha⟩
  have hkerρ : RingHom.ker ρ = (RingHom.ker ((algebraMap O (IsLocalRing.ResidueField O)).comp
      ((Bialgebra.counitAlgHom O (G.A (n + 1)) : G.A (n + 1) →+* O).comp (algebraMap (G.A n) (G.A (n + 1)))))).map
      (algebraMap (G.A n) (G.A (n + 1))) := by
    have hcomp : (algebraMap O (IsLocalRing.ResidueField O)).comp
        ((Bialgebra.counitAlgHom O (G.A (n + 1)) : G.A (n + 1) →+* O).comp (algebraMap (G.A n) (G.A (n + 1)))) =
        (algebraMap O (IsLocalRing.ResidueField O)).comp (Bialgebra.counitAlgHom O (G.A n) : G.A n →+* O) :=
      RingHom.ext fun b => by
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [hε]
    rw [hcomp]
    ext a
    rw [RingHom.mem_ker, hρ]
    exact hfib.2 a
  have hρalg : ∀ c : O, ρ (algebraMap O (G.A (n + 1)) c) =
      algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)
        (algebraMap O (IsLocalRing.ResidueField O) c) := fun c => by
    rw [hρ, AlgHomClass.commutes, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight.commutes c)
  have hεH : ∀ a, Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) (ρ a) =
      algebraMap O (IsLocalRing.ResidueField O) (Bialgebra.counitAlgHom O (G.A (n + 1)) a) := fun a => by
    rw [hρ, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply, TensorProduct.counit_tmul,
      CoalgHomClass.counit_comp_apply, Algebra.smul_def, mul_comm]
    simp

  have hlaws : (∀ a : IsLocalRing.ResidueField O ⊗[O] G.A 1, TensorProduct.lid (IsLocalRing.ResidueField O) _
      (LinearMap.rTensor _ (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)).toLinearMap
        (Bialgebra.comulAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) a)) = a) ∧
      (∀ a : IsLocalRing.ResidueField O ⊗[O] G.A 1, TensorProduct.rid (IsLocalRing.ResidueField O) _
      (LinearMap.lTensor _ (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)).toLinearMap
        (Bialgebra.comulAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1) a)) = a) := by
    constructor
    · intro a
      rw [Bialgebra.comulAlgHom_apply]
      erw [Coalgebra.rTensor_counit_comul]
      simp
    · intro a
      rw [Bialgebra.comulAlgHom_apply]
      erw [Coalgebra.lTensor_counit_comul]
      simp
  obtain ⟨e, he1, hei, ε', Δ', hlaws', hnil⟩ := GlobalTheory.T.localFactor_at_augmentation_counital_comul _ _ _ _ hlaws
  have hpres := GlobalTheory.T.exists_square_presentation_of_counit_isNilpotent_ker p _ _ ε' Δ' hlaws' hnil

  obtain ⟨r, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType O (G.A (n + 1)))
  have hfa : f₀ = MvPolynomial.aeval (fun i => f₀ (MvPolynomial.X i)) :=
    MvPolynomial.algHom_ext fun i => by rw [MvPolynomial.aeval_X]
  have hmap : ∀ {τ : Type} (x : τ → G.A (n + 1)) (q : MvPolynomial τ O),
      MvPolynomial.aeval (fun j => ρ (x j)) (MvPolynomial.map (algebraMap O (IsLocalRing.ResidueField O)) q) =
        ρ (MvPolynomial.aeval x q) := by
    intro τ x q
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]
    congr 1
    exact RingHom.ext fun c => (hρalg c).symm
  have haH : Function.Surjective (MvPolynomial.aeval (fun i => ρ (f₀ (MvPolynomial.X i))) :
      MvPolynomial (Fin r) (IsLocalRing.ResidueField O) →ₐ[IsLocalRing.ResidueField O] _) := fun h => by
    obtain ⟨y, rfl⟩ := hρs h
    obtain ⟨q, rfl⟩ := hf₀ y
    exact ⟨_, (hmap (fun i => f₀ (MvPolynomial.X i)) q).trans (by rw [← hfa])⟩
  obtain ⟨s, y, g, hg0, hgker⟩ := GlobalTheory.T.exists_presentation_square_at_point_of_localFactor _ _ _ e he1 hei hpres r _ haH
  choose yt hyt using fun i => hρs (y i)
  obtain ⟨x, hxd⟩ : ∃ x : Fin s ⊕ Fin r → G.A (n + 1), x = Sum.elim yt (fun i => f₀ (MvPolynomial.X i)) := ⟨_, rfl⟩
  have hx : (fun j => ρ (x j)) = Sum.elim y (fun i => ρ (f₀ (MvPolynomial.X i))) := by
    funext j
    cases j <;> simp [hxd, hyt]
  have hxs : Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin s ⊕ Fin r) (G.A n) →ₐ[G.A n] G.A (n + 1)) := by
    intro z
    obtain ⟨q, rfl⟩ := hf₀ z
    refine ⟨MvPolynomial.map (algebraMap O (G.A n)) (MvPolynomial.rename Sum.inr q), ?_⟩
    rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename, hfa, hxd]
    rfl
  haveI : Module.FinitePresentation O (G.A (n + 1)) := Module.finitePresentation_of_projective _ _
  haveI : Algebra.FinitePresentation O (G.A (n + 1)) := Algebra.FinitePresentation.of_finitePresentation _ _
  haveI : Algebra.FinitePresentation (G.A n) (G.A (n + 1)) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation O _ _
  have hFG : (RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin s ⊕ Fin r) (G.A n) →ₐ[G.A n] G.A (n + 1))).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective _ hxs
  obtain ⟨f, hf0, hfker⟩ := GlobalTheory.T.lift_square_presentation_of_flat_alt O (G.A n) (G.A (n + 1)) (IsLocalRing.ResidueField O) _ (Fin s ⊕ Fin r)
    (Bialgebra.counitAlgHom O (G.A (n + 1))) (algebraMap O (IsLocalRing.ResidueField O)) ρ
    (Bialgebra.counitAlgHom (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] G.A 1)) x
    hπs hπk hρalg hεH hkerρ hxs hFG g (by rw [hx]; exact hg0) (by rw [hx]; exact hgker)
  have hpt : ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))), (p : O) • a ∈
      RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 ⊔
        ((RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1)))).comap (algebraMap (G.A n) (G.A (n + 1)))).map
          (algebraMap (G.A n) (G.A (n + 1))) := by
    rw [hker]
    exact GlobalTheory.T.natCast_smul_mem_augIdealSq_sup_map_mulP p O G n
  have := GlobalTheory.T.cotangent_map_injective_of_square_presentation_at_point O (G.A n) (G.A (n + 1)) (Fin s ⊕ Fin r) (Bialgebra.counitAlgHom O (G.A (n + 1))) x f (p : O)
    hp0 hxs hf0 hfker hpt b hb
  rwa [hker] at this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemSqCounitKerStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulP_mem_sq_counit_ker : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], (p : O) ≠ 0 → ¬IsUnit (p : O) → (∀ a : O, ∃ b : O, b ^ p = a) → ∀ (G : GlobalTheory.PDivGroup p O) (n : ℕ) (b : G.A n), G.mulP n b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 := by
  first | exact @GlobalTheory.PDivGroup.mulP_mem_sq_counit | exact GlobalTheory.PDivGroup.mulP_mem_sq_counit | (intros; apply GlobalTheory.PDivGroup.mulP_mem_sq_counit <;> assumption)
end
