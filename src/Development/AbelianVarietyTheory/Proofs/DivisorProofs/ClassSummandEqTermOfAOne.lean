module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyOfRegAfOfFixL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntOfDenLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugacyClassPartEqWeightMulKottwitzPointSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningProductIsoPreservesCubicalStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralTestFunctionSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMarkedPairClassesDegreeOneTermNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralTestFunctionFirst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingValuationSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRegularConjugateLocalScalarNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRegularConjugateLocalScalarNorm
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxRegLoc

theorem local_class_scalar_norm_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β →
    ∀ y₀ : grp G β, (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ S : Finset ℕ, ∀ (y : grp G β) (g : G.GAf), f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 →
    ∀ c : G.Cˣ, (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
      inC G ℚ_[ℓ] (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G L f hf β x t hx hβ y₀ hsep hdeg
  have hcomm : ∀ a b : G.C, Commute a (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) →
      Commute b (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) → Commute a b :=
    fun a b ha hb => GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G _ hsep hdeg a b ha hb
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.exists_compact_support_twistedHeckeTestFunction p G L f hf
  have hev := eventually_compL_mem_intPts p G Ω hΩc
  have hlat := GlobalTheory.T.eventually_kottwitz_lattice_separable_minpoly p G (y₀ : G.Cˣ × ℚˣ).1 hsep hdeg
  have hnorm := GlobalTheory.T.eventually_tauFixed_unit_centralizer_is_norm p G β hβ (y₀ : G.Cˣ × ℚˣ).1 _ y₀.2.1 hsep hdeg
  have hstab := GlobalTheory.FinClsLoc.intC_stab p G β
  obtain ⟨S, hS⟩ := GlobalTheory.FinClsLoc.exists_finset_forall_prime_awayP_padic p _ (hev.and (hlat.and (hnorm.and hstab)))
  refine ⟨S, fun y g hfy c hc ℓ _ hℓ => ?_⟩
  obtain ⟨w, ⟨hev', hlat', hnorm', hmul, hstar, hβi, hβi'⟩, ⟨e⟩⟩ := hS ℓ hℓ
  apply GlobalTheory.T.localTwistedNormConclusion_transfer_ringEquiv p G (w.1.adicCompletion ℚ) ℚ_[ℓ] e
  have hint := hev' _ (hΩ _ hfy)
  obtain ⟨k, lam, hk1, hk2, hk3⟩ := GlobalTheory.T.exists_local_conj_trivialization_at_place_awayP p G β x t hx y g c (y₀ : G.Cˣ × ℚˣ).1 hc w
  obtain ⟨z, m, hz, hm, hm', hkzm⟩ := hlat' k (by rw [hk1]; exact hint.1) (by rw [hk2]; exact hint.2.1)
  have hap := GlobalTheory.grp_conj_unit_props p G β hβ y y₀ c hc (GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc)
  have hinv := starT_invol G (w.1.adicCompletion ℚ)
  have hbb : inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hβ' : (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (β : G.C))).unop = inC G (w.1.adicCompletion ℚ) (β : G.C) := by
    show (starT G.star (w.1.adicCompletion ℚ) ((1 : w.1.adicCompletion ℚ) ⊗ₜ (β : G.C))).unop = (1 : w.1.adicCompletion ℚ) ⊗ₜ (β : G.C)
    rw [starT_tmul]
    exact congrArg (TensorProduct.tmul ℚ (1 : w.1.adicCompletion ℚ)) hβ
  have hY' : inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C) *
      (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))).unop =
      algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (algebraMap ℚ (w.1.adicCompletion ℚ) ((y₀ : G.Cˣ × ℚˣ).2 : ℚ)) * inC G (w.1.adicCompletion ℚ) (β : G.C) := by
    have h := congrArg (inC G (w.1.adicCompletion ℚ)) y₀.2.1
    rw [map_mul, map_mul, map_mul] at h
    have e1 : inC G (w.1.adicCompletion ℚ) (sh G (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) =
        (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))).unop :=
      (starT_tmul G.star (w.1.adicCompletion ℚ) 1 _).symm
    have e2 : inC G (w.1.adicCompletion ℚ) (algebraMap ℚ G.C ((y₀ : G.Cˣ × ℚˣ).2 : ℚ)) =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (algebraMap ℚ (w.1.adicCompletion ℚ) ((y₀ : G.Cˣ × ℚˣ).2 : ℚ)) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C).commutes _
    rw [e1, e2] at h
    exact h
  have hN : ∀ m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = m * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) →
      Commute (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m' →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
        (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro m' hm'v hcm hτ
    have hss : (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = 1 := by
      rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
    have h1 : (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop *
        ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) = 1 := by
      rw [hm'v]
      calc _ = (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * ((starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop *
            (inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C)) *
            (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop) * ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) := by
            simp only [mul_assoc]
        _ = 1 := by rw [hbb, mul_one, hss, mul_one, Units.mul_inv]
    have hinv' := Units.inv_eq_of_mul_eq_one_right h1
    refine hnorm' m' hcm ?_ ?_ hτ
    · rw [hm'v]; exact hmul _ _ (hmul _ _ hm (hstar _ hm)) hβi'
    · rw [hinv']; exact hmul _ _ (hmul _ _ hβi (hstar _ hm')) hm'
  have halg := GlobalTheory.twisted_norm_local_step (starT G.star (w.1.adicCompletion ℚ)) hinv
    (Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom β)
    (Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom (y₀ : G.Cˣ × ℚˣ).1) k z m
    (inC G (w.1.adicCompletion ℚ) (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))
    lam (Units.map (algebraMap ℚ (w.1.adicCompletion ℚ)).toMonoidHom (y₀ : G.Cˣ × ℚˣ).2) hβ' hY'
    (hap.2.1.map (inC G (w.1.adicCompletion ℚ))) hk3 hkzm hz hN
  obtain ⟨z', hz', hz'eq⟩ := halg
  exact ⟨lam, z', hz', hz'eq⟩

end GlobalTheory.CxRegLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRegularConjugateLocalScalarNormStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.harrisTaylor_regular_conjugate_local_scalar_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β →
    ∀ y₀ : grp G β, (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ S : Finset ℕ, ∀ (y : grp G β) (g : G.GAf), f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 →
    ∀ c : G.Cˣ, (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) ∧
      inC G ℚ_[ℓ] (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C)) := by
  first | exact @GlobalTheory.CxRegLoc.local_class_scalar_norm_sep | exact GlobalTheory.CxRegLoc.local_class_scalar_norm_sep
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.ClsReg

theorem classes_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ P : Polynomial G.F, ∃ Y : Finset (grp G β), ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → (∃ a : Dat G v β, FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0) → ∃ y₀ ∈ Y, ∃ γ : grp G β, y = γ * y₀ * γ⁻¹ := by
  intro p _ G _ v _ L f hf K' f' _ β x t hx hreg hβ _ P
  by_cases hne : ∃ y₀ : grp G β, minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P ∧
      ∃ a : Dat G v β, FixL G v β y₀ a.2.1 ∧
        f (a.1.1⁻¹ * toAfF G β x t hx y₀ * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y₀ * a.1.2) ≠ 0
  swap
  · exact ⟨∅, fun y hy ha => absurd ⟨y, hy, ha⟩ hne⟩
  obtain ⟨y₀, hP₀, a₀, hfix₀, ha₀⟩ := hne
  obtain ⟨hdeg₀, hsep₀⟩ := hreg y₀ a₀.1.1 (left_ne_zero_of_mul ha₀) ⟨a₀.2.1, a₀.2.2, hfix₀⟩
  obtain ⟨hy₀, -⟩ := y₀.prop
  obtain ⟨S, hS⟩ := GlobalTheory.T.harrisTaylor_regular_conjugate_local_scalar_norm p G L f hf β x t hx hβ y₀ hsep₀ hdeg₀
  obtain ⟨A, hA⟩ := GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular p G β hβ ((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) (((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) hy₀ hsep₀ hdeg₀ S
  have key : ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → ∀ g : G.GAf,
      f (g⁻¹ * toAfF G β x t hx y * g) ≠ 0 → ∃ a' ∈ A, ∃ b : Bool, ∃ (c : G.Cˣ) (r : ℚˣ) (e : G.Cˣ),
        (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) ∧
        Commute (e : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ decide (0 < (r : ℚ)) = b ∧
        (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a' * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
    intro y hy g hg
    obtain ⟨c, hc⟩ := units_conj_of_minpoly_eq_of_separable G ((y : G.Cˣ × ℚˣ).1) ((y₀ : G.Cˣ × ℚˣ).1)
      (by rw [hy, hP₀]) hsep₀ hdeg₀
    have h2 := GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc
    obtain ⟨hu, hcm, hfix⟩ := GlobalTheory.grp_conj_unit_props p G β hβ y y₀ c hc h2
    obtain ⟨a', ha', r, e, he, hre⟩ := hA _ hu hcm hfix (fun ℓ _ hℓ => hS y g hg c hc ℓ hℓ)
    exact ⟨a', ha', decide (0 < (r : ℚ)), c, r, e, hc, he, rfl, hre⟩
  let D : G.C × Bool → grp G β → Prop := fun ab y => ∃ (c : G.Cˣ) (r : ℚˣ) (e : G.Cˣ),
        (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((c⁻¹ : G.Cˣ) : G.C) ∧
        Commute (e : G.C) (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ decide (0 < (r : ℚ)) = ab.2 ∧
        (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * ab.1 * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C)))
  let ρ : G.C × Bool → grp G β := fun ab => if h : ∃ y, D ab y then h.choose else 1
  refine ⟨(A ×ˢ (Finset.univ : Finset Bool)).image ρ, ?_⟩
  rintro y hy ⟨a, _, ha⟩
  obtain ⟨a', ha', b, hD⟩ := key y hy a.1.1 (left_ne_zero_of_mul ha)
  have hex : ∃ y, D (a', b) y := ⟨y, hD⟩
  refine ⟨ρ (a', b), Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨ha', Finset.mem_univ _⟩), ?_⟩
  have hρ : ρ (a', b) = hex.choose := dif_pos hex
  rw [hρ]
  obtain ⟨c', r', e', hc', he', hb', hre'⟩ := hex.choose_spec
  dsimp only at hb' hre'
  obtain ⟨c, r, e, hc, he, hb, hre⟩ := hD
  have h2 : (hex.choose : G.Cˣ × ℚˣ).2 = (y : G.Cˣ × ℚˣ).2 := by
    rw [GlobalTheory.grp_factor_eq_of_conj p G β _ y₀ c' hc', GlobalTheory.grp_factor_eq_of_conj p G β y y₀ c hc]
  refine GlobalTheory.Div.conj_of_twist p G β hex.choose y ((y₀ : G.Cˣ × ℚˣ).1) c' c (e * e'⁻¹) ((r : ℚ) / r') hc' hc h2 ?_ ?_ ?_
  · rw [Units.val_mul]
    exact he.mul_left he'.units_inv_left
  · have hr : (0 < (r : ℚ)) ↔ (0 < (r' : ℚ)) := by
      rw [← decide_eq_decide, hb, hb']
    rcases lt_or_gt_of_ne r'.ne_zero with h | h
    · have hn : ¬ (0 < (r : ℚ)) := fun h0 => absurd (hr.1 h0) (not_lt.2 h.le)
      exact div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 hn) r.ne_zero) h
    · exact div_pos (hr.2 h) h
  · rw [hre', hre]
    exact conj_rel_alg' G β e e' a' r r'

end GlobalTheory.LKCx.ClsReg
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.orbital_integral_test_function_first : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ P : Polynomial G.F, ∃ Y : Finset (grp G β), ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → (∃ a : Dat G v β, FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0) → ∃ y₀ ∈ Y, ∃ γ : grp G β, y = γ * y₀ * γ⁻¹ := by
  first | exact @GlobalTheory.LKCx.ClsReg.classes_finite | exact GlobalTheory.LKCx.ClsReg.classes_finite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalTermRealTrivialisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianQuasiFiniteFinitePart
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.FinPolysIrr

theorem eig_norm_sq_of_a_one (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hβ : sh G β = β) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1)
    (y : grp G β) (a : PosV G v β) (hfix : FixL G v β y a.1) (w : InfinitePlace G.F) (μ : ℂ)
    (x : Fin G.n → ℂ) (hx : x ≠ 0) (hμ : G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *ᵥ x = μ • x) :
    ‖μ‖ ^ 2 = ((((y : G.Cˣ × ℚˣ).2 : ℚ)) : ℝ) := by
  obtain ⟨-, -, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G w β hβ hR
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G w β y
  have hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero
  have hsig := G.sig w
  refine GlobalTheory.eig_norm_sq_of_similitude G.n (G.gram w) (herm G w β) (toV G w β y : Matrix (Fin G.n) (Fin G.n) ℂ)
    (G.gram_herm w) Z _ ?_ ?_ hZ hs0 ?_ ?_ μ x hx hμ
  · rcases hsig with h | h <;> omega
  · have := G.n_pos
    rcases hsig with h | h <;> omega
  · rw [Complex.ofReal_ratCast]; exact hsim
  · by_cases hw : w = v
    · subst hw
      obtain ⟨c, hc⟩ := hfix
      exact Or.inr ⟨c, a.1, hc, a.2⟩
    · left
      have h1 : sigPosH (G.gram_herm w) ≠ 1 := by
        intro h1
        have hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := ha.le
        have := Fintype.card_le_one_iff.1 hcard ⟨w, h1⟩ ⟨v, hv⟩
        exact hw (congrArg Subtype.val this)
      rcases hsig with h | h
      · exact absurd h.1 h1
      · exact h.1

theorem minpoly_coeff_bdd_of_a_one (p : ℕ) [Fact p.Prime] (G : HTGroup p) (ha : G.a = 1)
    (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (hβ : sh G β = β)
    (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) (S : ℝ) : ∃ B : ℝ, ∀ (y : grp G β) (a : PosV G v β),
    FixL G v β y a.1 → (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S → ∀ (φ : G.F →+* ℂ) (k : ℕ),
    ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  refine ⟨max (√(max S 0)) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩
  intro y a hfix hS φ k
  set γ : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hγ
  have hint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hdeg : (minpoly G.F γ).natDegree ≤ G.n ^ 2 := G.rankC ▸ minpoly.natDegree_le γ
  have hbd : ∀ (w : InfinitePlace G.F) (z : ℂ), (minpoly G.F γ).eval₂ w.embedding z = 0 → ‖z‖ ≤ √(max S 0) := by
    intro w z hz
    obtain ⟨x, hx, hzx⟩ := GlobalTheory.LKCx.PolyArch.roots_eig_any p G w γ z hz
    have h2 := eig_norm_sq_of_a_one p G ha v hv β hβ hR y a hfix w z x hx hzx
    have h3 : ‖z‖ ^ 2 ≤ max S 0 := h2 ▸ le_max_of_le_left hS
    simpa using Real.abs_le_sqrt h3
  have hroots : ∀ z ∈ ((minpoly G.F γ).map φ).roots, ‖z‖ ≤ √(max S 0) := by
    intro z hz
    have hr : (minpoly G.F γ).eval₂ φ z = 0 := by
      have := (Polynomial.mem_roots'.1 hz).2
      rwa [Polynomial.IsRoot, Polynomial.eval_map] at this
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · rw [← h] at hr; exact hbd _ z hr
    · have hr' : (minpoly G.F γ).eval₂ (InfinitePlace.mk φ).embedding (starRingEnd ℂ z) = 0 := by
        rw [h]
        have := congrArg (starRingEnd ℂ) hr
        rw [map_zero, Polynomial.hom_eval₂] at this
        convert this using 2
      simpa using hbd _ _ hr'
  have := Polynomial.coeff_bdd_of_roots_le φ (minpoly.monic hint) (IsAlgClosed.splits _) hdeg hroots k
  rwa [Polynomial.coeff_map] at this

end GlobalTheory.LKCx.FinPolysIrr

namespace GlobalTheory.LKCx


open GlobalTheory.LKCx.FinPolysIrr in
theorem finite_minpoly_fix_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} := by
  intro p _ G ha v hv L f hf K' f' hf' β x t hx hsym hR
  obtain ⟨D, hD, hDy⟩ := GlobalTheory.T.minpoly_bounded_denominators p G L f hf β x t hx
  obtain ⟨Bp, hBp⟩ := GlobalTheory.T.minpoly_padic_bounded p G K' f' hf' β
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.bounded_denominator_integral_power G.F p Bp
  obtain ⟨S, hS⟩ := GlobalTheory.T.similitudeFactor_formGroup_bounded_of_test_support p G L f hf K' f' hf' β x t hx
  obtain ⟨B, hB⟩ := minpoly_coeff_bdd_of_a_one p G ha v hv β hsym hR S
  have hpD : 0 < p ^ m₀ * D := Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _) hD
  refine (GlobalTheory.T.finite_monic_bounded_polynomials G.F (G.n ^ 2) (p ^ m₀ * D) B hpD).subset ?_
  rintro P ⟨y, a, rfl, hfix, hne⟩
  have h1 : f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) ≠ 0 := left_ne_zero_of_mul hne
  have h2 : f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0 := right_ne_zero_of_mul hne
  have hint : IsIntegral G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := Algebra.IsIntegral.isIntegral _
  refine ⟨minpoly.monic hint, ?_, fun k => ⟨?_, fun φ => hB y a.2 hfix (hS y a.1.1 a.1.2 h1 h2) φ k⟩⟩
  · rw [← G.rankC]; exact minpoly.natDegree_le _
  · have := hm₀ _ D (hDy y a.1.1 h1 k) (fun φ => hBp y a.1.2 h2 φ k)
    push_cast
    simpa [mul_assoc] using this

end GlobalTheory.LKCx
end
end

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbital_term_real_trivialisation : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → Set.Finite {P : Polynomial G.F | ∃ (y : grp G β) (a : Dat G v β), P = minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∧ FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0} := by
  first | (exact @GlobalTheory.LKCx.finite_minpoly_fix_a_one) | (exact GlobalTheory.LKCx.finite_minpoly_fix_a_one) | (intros; apply GlobalTheory.LKCx.finite_minpoly_fix_a_one  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightSupportFiniteOfFiniteFixing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightSupportFiniteOfFiniteFixing
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

theorem support_cxF_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → Set.Finite {y : grp G β | FixL G v β y z ∧ f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0}) → ∀ a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K', (Function.support (GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a)).Finite := by
  intro p _ G v wt Kf f _ K' f' _ β x t hx hfin a
  by_cases hpos : 0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
      (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re
  · refine (hfin (LeftCosets.rep _ _ a.1) _ hpos).subset ?_
    intro y hy
    rw [Function.mem_support] at hy
    unfold cxF at hy
    split_ifs at hy with hc
    · exact ⟨hc.2, left_ne_zero_of_mul hy⟩
    · exact absurd rfl hy
  · convert Set.finite_empty
    ext y
    simp only [Function.mem_support, Set.mem_empty_iff_false, iff_false, not_not]
    unfold cxF
    rw [if_neg (fun hc => hpos hc.1)]

end GlobalTheory.CxUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairWeightSupportFiniteOfFiniteFixingStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairWeight_support_finite_of_finite_fixing : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → Set.Finite {y : grp G β | FixL G v β y z ∧ f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0}) → ∀ a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K', (Function.support (GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a)).Finite := by
  first | (exact @GlobalTheory.CxUnfold.support_cxF_finite) | (exact GlobalTheory.CxUnfold.support_cxF_finite) | (intros; apply GlobalTheory.CxUnfold.support_cxF_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumConjClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumsOverConjugacyClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsEqFinsumConjClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumConjClassesCentralizerOrbitsEqPairOrbits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumConjClassesCentralizerOrbitsEqPairOrbits
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

noncomputable section

namespace GlobalTheory.OrbitUnfold

def conjClassesEquivOrbits (Γ : Type) [Group Γ] :
    ConjClasses Γ ≃ MulAction.orbitRel.Quotient Γ (ConjSelf Γ) :=
  Quotient.congr (⟨of, val, fun _ => rfl, fun _ => rfl⟩ : Γ ≃ ConjSelf Γ) (by
    intro a b
    show IsConj a b ↔ of a ∈ MulAction.orbit Γ (of b)
    rw [isConj_comm, isConj_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, congrArg of hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, congrArg val hc⟩)

theorem conjClassesEquivOrbits_mk {Γ : Type} [Group Γ] (γ : Γ) :
    conjClassesEquivOrbits Γ (Quotient.mk (IsConj.setoid Γ) γ) =
      Quotient.mk (MulAction.orbitRel Γ (ConjSelf Γ)) (of γ) := rfl

theorem finsum_conjClasses_centralizer_orbits {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (_hstab : ∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite)
    (hsupp : ∀ y : Y, (Function.support (F y)).Finite)
    (hfin : {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite) :
    ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y,
      ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} :
        Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) = pairSum F := by
  set_option backward.isDefEq.respectTransparency false in
    set e := conjClassesEquivOrbits Γ
    have key := GlobalTheory.T.finsum_orbitRel_fibred_equivariant (H := Γ) (X := Y × ConjSelf Γ) (B := ConjSelf Γ) (E := Y)
      Prod.snd (fun _ _ => rfl) (fun b => Subgroup.centralizer {val b})
      (fun b => by rw [stabilizer_eq_centralizer])
      (fun b y => (y, b)) (fun b y y' h => congrArg Prod.fst h) (fun _ _ => rfl)
      (fun b x hx => ⟨x.1, Prod.ext rfl hx.symm⟩)
      (fun b h hh y => by
        have : h • b = b := by
          rw [← MulAction.mem_stabilizer_iff, stabilizer_eq_centralizer]; exact hh
        show (h • y, b) = (h • y, h • b)
        rw [this])
      (fun q => of (Quotient.out (e.symm q)))
      (fun q => by
        show Quotient.mk _ (of (Quotient.out (e.symm q))) = q
        have hout : ∀ c : ConjClasses Γ, (Quotient.mk (IsConj.setoid Γ) (Quotient.out c) : ConjClasses Γ) = c :=
          fun c => Quotient.out_eq c
        rw [← conjClassesEquivOrbits_mk, hout, Equiv.apply_symm_apply])
      (fun o => pairTerm F (Quotient.out o))
      (GlobalTheory.T.finite_support_stabilizerWeightedPairTerm F hF hsupp hfin)
    unfold pairSum
    rw [key, ← finsum_comp_equiv e]
    refine finsum_congr (fun c => ?_)
    change Quotient (IsConj.setoid Γ) at c
    change ConjClasses Γ at c
    change (Quotient (IsConj.setoid Γ)) at c
    rw [e.symm_apply_apply]
    dsimp only [ConjSelf.val, ConjSelf.of]
    refine finsum_congr (fun o => ?_)
    rw [pairTerm_out F hF]
    unfold pairTerm
    rw [stabilizer_pair]
    rfl

end GlobalTheory.OrbitUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumConjClassesCentralizerOrbitsEqPairOrbitsStatement
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_conjClasses_centralizer_orbits_eq_pairOrbits : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) = pairSum F := by
  first | exact @GlobalTheory.OrbitUnfold.finsum_conjClasses_centralizer_orbits | exact GlobalTheory.OrbitUnfold.finsum_conjClasses_centralizer_orbits | (intros; apply GlobalTheory.OrbitUnfold.finsum_conjClasses_centralizer_orbits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedOrbitSumEqPairOrbitSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedOrbitSumEqPairOrbitSum
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

namespace GlobalTheory.OrbitUnfold

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

theorem card_stabilizer_pair_eq (y : Y) (γ : ConjSelf Γ) :
    Nat.card (MulAction.stabilizer Γ (y, γ)) =
      Nat.card (MulAction.stabilizer (MulAction.stabilizer Γ y) γ) := by
  have hmap : (MulAction.stabilizer (MulAction.stabilizer Γ y) γ).map
      (MulAction.stabilizer Γ y).subtype = MulAction.stabilizer Γ (y, γ) := by
    ext η
    simp only [Subgroup.mem_map, MulAction.mem_stabilizer_iff, Subgroup.coe_subtype, Prod.smul_mk,
      Prod.mk.injEq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨η, h1⟩, h2, rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

end GlobalTheory.OrbitUnfold

namespace GlobalTheory.OrbitUnfold

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

theorem inner_sum_eq (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) (y : Y)
    (hfin : (MulAction.stabilizer Γ y : Set Γ).Finite) (hsupp : (Function.support (F y)).Finite) :
    ∑ᶠ o' : MulAction.orbitRel.Quotient (MulAction.stabilizer Γ y) (ConjSelf Γ),
        pairTerm F (y, Quotient.out o') =
      ((Nat.card (MulAction.stabilizer Γ y) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F y γ := by
  haveI : Finite (MulAction.stabilizer Γ y) := hfin.to_subtype
  have hinv : ∀ (k : MulAction.stabilizer Γ y) (z : ConjSelf Γ),
      F y (val (k • z)) = F y (val z) := by
    intro k z
    have hk : (k : Γ) • y = y := k.2
    have e1 : val (k • z) = (k : Γ) * val z * (k : Γ)⁻¹ := rfl
    have e2 := hF (k : Γ) y (val z)
    rw [hk] at e2
    rw [e1, e2]
  have hs : (Function.support (fun z : ConjSelf Γ => F y (val z))).Finite := hsupp
  have key := GlobalTheory.T.finsum_orbits_inv_stabilizer_card_mass (K := MulAction.stabilizer Γ y) (Z := ConjSelf Γ)
    (fun z => F y (val z)) hinv hs
  refine Eq.trans ?_ key
  refine finsum_congr fun o' => ?_
  unfold pairTerm
  rw [card_stabilizer_pair_eq]

theorem orbitSum_eq_pairSum (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (hstab : ∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite)
    (hsupp : ∀ y : Y, (Function.support (F y)).Finite)
    (horb : {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite) :
    ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y,
        ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ =
      pairSum F := by
  have hg := GlobalTheory.T.finite_support_stabilizerWeightedPairTerm F hF hsupp horb
  have hπ : ∀ (h : Γ) (x : Y × ConjSelf Γ), (h • x).1 = h • x.1 := fun _ _ => rfl
  have hinj : ∀ y : Y, Function.Injective (fun γ : ConjSelf Γ => (y, γ)) :=
    fun y a b hab => (Prod.mk.inj hab).2
  have hsurj : ∀ (y : Y) (x : Y × ConjSelf Γ), x.1 = y → ∃ e : ConjSelf Γ, (y, e) = x := by
    rintro y ⟨a, b⟩ rfl
    exact ⟨b, rfl⟩
  have hequi : ∀ (y : Y), ∀ h ∈ MulAction.stabilizer Γ y, ∀ e : ConjSelf Γ,
      ((y, h • e) : Y × ConjSelf Γ) = h • (y, e) := by
    intro y h hh e
    have hh' : h • y = y := hh
    rw [Prod.smul_mk, hh']
  have h := GlobalTheory.T.finsum_orbitRel_fibred_equivariant (H := Γ) (X := Y × ConjSelf Γ) (B := Y) (E := ConjSelf Γ) Prod.fst
    hπ (fun y => MulAction.stabilizer Γ y) (fun _ => le_rfl)
    (fun y γ => (y, γ)) hinj (fun _ _ => rfl) hsurj hequi
    Quotient.out (fun q => Quotient.out_eq q)
    (fun o => pairTerm F (Quotient.out o)) hg
  unfold pairSum
  rw [h]
  refine finsum_congr fun q => ?_
  rw [← inner_sum_eq F hF (Quotient.out q) (hstab _) (hsupp _)]
  refine finsum_congr fun o' => ?_
  exact (pairTerm_out F hF (Quotient.out q, Quotient.out o')).symm

end GlobalTheory.OrbitUnfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedOrbitSumEqPairOrbitSumStatement
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedOrbitSum_eq_pairOrbitSum : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = pairSum F := by
  first | exact @GlobalTheory.OrbitUnfold.orbitSum_eq_pairSum | exact GlobalTheory.OrbitUnfold.orbitSum_eq_pairSum | (intros; apply GlobalTheory.OrbitUnfold.orbitSum_eq_pairSum <;> assumption)
end
end

open GlobalTheory.LKCount GlobalTheory.OrbitUnfold

namespace GlobalTheory.OrbitUnfold

theorem finsum_orbits_eq_finsum_conjClasses : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) := by
  intro Γ Y _ _ F hF hst hs ho
  rw [GlobalTheory.T.weightedOrbitSum_eq_pairOrbitSum F hF hst hs ho, GlobalTheory.T.finsum_conjClasses_centralizer_orbits_eq_pairOrbits F hF hst hs ho]

end GlobalTheory.OrbitUnfold
end

open MulAction

namespace GlobalTheory.OrbitUnfold

section Restrict

variable {G Y Y' : Type} [Group G] [MulAction G Y] [MulAction G Y']

theorem out_mk_mem_orbit (x : Y) :
    Quotient.out (Quotient.mk (orbitRel G Y) x) ∈ orbit G x :=
  orbitRel_apply.mp (Quotient.mk_out (s := orbitRel G Y) x)

theorem injective_mk_comp_out (i : Y' → Y) (hi : Function.Injective i)
    (heq : ∀ (η : G) (y : Y'), i (η • y) = η • i y) :
    Function.Injective (fun o : orbitRel.Quotient G Y' =>
      (Quotient.mk (orbitRel G Y) (i (Quotient.out o)) : orbitRel.Quotient G Y)) := by
  intro o₁ o₂ h
  have h' : i (Quotient.out o₁) ∈ orbit G (i (Quotient.out o₂)) :=
    orbitRel_apply.mp (Quotient.exact h)
  obtain ⟨η, hη⟩ := h'
  simp only at hη
  rw [← heq] at hη
  have h2 := hi hη
  rw [← Quotient.out_eq o₁, ← Quotient.out_eq o₂]
  exact Quotient.sound (orbitRel_apply.mpr ⟨η, h2⟩)

theorem finsum_orbits_restrict (i : Y' → Y) (hi : Function.Injective i)
    (heq : ∀ (η : G) (y : Y'), i (η • y) = η • i y) (g : Y → ℂ) (g' : Y' → ℂ)
    (hgg : ∀ y, g' y = g (i y)) (hg : ∀ (η : G) (y : Y), g (η • y) = g y)
    (h0 : ∀ y, g y ≠ 0 → y ∈ Set.range i) :
    ∑ᶠ o : orbitRel.Quotient G Y, g (Quotient.out o) =
      ∑ᶠ o : orbitRel.Quotient G Y', g' (Quotient.out o) := by
  have hgo : ∀ x : Y, g (Quotient.out (Quotient.mk (orbitRel G Y) x)) = g x := by
    intro x
    obtain ⟨η, hη⟩ := out_mk_mem_orbit (G := G) x
    simp only at hη
    rw [← hη, hg]
  have hφ := injective_mk_comp_out i hi heq
  have hsupp : Function.support (fun o : orbitRel.Quotient G Y => g (Quotient.out o)) ⊆
      Set.range (fun o : orbitRel.Quotient G Y' =>
        (Quotient.mk (orbitRel G Y) (i (Quotient.out o)) : orbitRel.Quotient G Y)) := by
    intro o ho
    obtain ⟨y, hy⟩ := h0 _ ho
    refine ⟨Quotient.mk (orbitRel G Y') y, ?_⟩
    obtain ⟨η, hη⟩ := out_mk_mem_orbit (G := G) y
    simp only at hη
    show Quotient.mk (orbitRel G Y) (i (Quotient.out (Quotient.mk (orbitRel G Y') y))) = o
    rw [← hη, heq, hy]
    conv_rhs => rw [← Quotient.out_eq o]
    exact Quotient.sound (orbitRel_apply.mpr (mem_orbit _ _))
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ _
    (fun x hx => ⟨fun _ => hsupp hx, fun _ => trivial⟩), finsum_mem_range hφ]
  exact finsum_congr fun o => by rw [hgo, hgg]

end Restrict

section Stab

variable {Γ Y : Type} [Group Γ] [MulAction Γ Y]

def finiteStabilizerSubMulAction (Γ Y : Type) [Group Γ] [MulAction Γ Y] : SubMulAction Γ Y where
  carrier := {y | (stabilizer Γ y : Set Γ).Finite}
  smul_mem' η y hy := by
    show (stabilizer Γ (η • y) : Set Γ).Finite
    rw [stabilizer_smul_eq_stabilizer_map_conj, Subgroup.coe_map]
    exact Set.Finite.image _ hy

theorem mem_stabilizer_conj_iff (η x : Γ) (y : Y) :
    x ∈ stabilizer Γ y ↔ η * x * η⁻¹ ∈ stabilizer Γ (η • y) := by
  simp only [mem_stabilizer_iff, mul_smul, inv_smul_smul]
  exact (smul_left_cancel_iff η).symm

theorem natCard_stabilizer_inf_smul (K : Subgroup Γ) (η : Γ) (hK : ∀ x, x ∈ K ↔ η * x * η⁻¹ ∈ K)
    (y : Y) : Nat.card (stabilizer Γ (η • y) ⊓ K : Subgroup Γ) = Nat.card (stabilizer Γ y ⊓ K : Subgroup Γ) := by
  symm
  refine Nat.card_congr ((MulAut.conj η).toEquiv.subtypeEquiv fun x => ?_)
  simp only [Subgroup.mem_inf, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  rw [mem_stabilizer_conj_iff η x y, hK x]

theorem natCard_stabilizer_smul (η : Γ) (y : Y) :
    Nat.card (stabilizer Γ (η • y)) = Nat.card (stabilizer Γ y) := by
  symm
  refine Nat.card_congr ((MulAut.conj η).toEquiv.subtypeEquiv fun x => ?_)
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  exact mem_stabilizer_conj_iff η x y

theorem mem_iff_conj_mem (K : Subgroup Γ) {η : Γ} (hη : η ∈ K) (x : Γ) :
    x ∈ K ↔ η * x * η⁻¹ ∈ K := by
  constructor
  · intro h; exact K.mul_mem (K.mul_mem hη h) (K.inv_mem hη)
  · intro h
    have := K.mul_mem (K.mul_mem (K.inv_mem hη) h) hη
    simpa [mul_assoc] using this

theorem stabilizer_inf_centralizer_infinite (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) (y : Y)
    (hs : (Function.support (F y)).Finite) (c : Γ) (hc : F y c ≠ 0)
    (hinf : (stabilizer Γ y : Set Γ).Infinite) :
    ((stabilizer Γ y ⊓ Subgroup.centralizer {c} : Subgroup Γ) : Set Γ).Infinite := by
  haveI : Infinite (stabilizer Γ y) := hinf.to_subtype
  haveI : Finite (Function.support (F y)) := hs.to_subtype
  let f : stabilizer Γ y → Function.support (F y) := fun η =>
    ⟨(η : Γ) * c * (η : Γ)⁻¹, by
      show F y _ ≠ 0
      have h1 : (η : Γ) • y = y := η.2
      have := hF η y c
      rw [h1] at this
      rw [this]; exact hc⟩
  obtain ⟨z, hz⟩ := Finite.exists_infinite_fiber f
  obtain ⟨⟨η₀, hη₀⟩⟩ : Nonempty ↑(f ⁻¹' {z}) := inferInstance
  refine Set.infinite_of_injective_forall_mem (α := ↑(f ⁻¹' {z}))
    (f := fun η => (η₀ : Γ)⁻¹ * ((η : stabilizer Γ y) : Γ)) ?_ ?_
  · intro a b hab
    have : ((a : stabilizer Γ y) : Γ) = ((b : stabilizer Γ y) : Γ) := mul_left_cancel hab
    exact Subtype.ext (Subtype.ext this)
  · intro ⟨η, hη⟩
    have E : (η : Γ) * c * (η : Γ)⁻¹ = (η₀ : Γ) * c * (η₀ : Γ)⁻¹ := by
      have h1 : f η = z := hη
      have h2 : f η₀ = z := hη₀
      have := congrArg Subtype.val (h1.trans h2.symm)
      exact this
    refine Subgroup.mem_inf.mpr ⟨(stabilizer Γ y).mul_mem ((stabilizer Γ y).inv_mem η₀.2) η.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h2 : (η₀ : Γ)⁻¹ * ((η : Γ) * h * (η : Γ)⁻¹) * η = (η₀ : Γ)⁻¹ * ((η₀ : Γ) * h * (η₀ : Γ)⁻¹) * η := by
      rw [E]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at h2
    simp only [mul_assoc]
    exact h2.symm

end Stab

theorem finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) := by
  intro Γ Y _ _ F hF hs ho
  let S := finiteStabilizerSubMulAction Γ Y
  have hstabS : ∀ y : S, stabilizer Γ y = stabilizer Γ (y : Y) := fun y =>
    SubMulAction.stabilizer_of_subMul y
  have hF' : ∀ (η : Γ) (y : S) (γ : Γ), F ((η • y : S) : Y) (η * γ * η⁻¹) = F (y : Y) γ :=
    fun η y γ => hF η y γ
  have hst' : ∀ y : S, (stabilizer Γ y : Set Γ).Finite := fun y => by rw [hstabS]; exact y.2
  have hs' : ∀ y : S, (Function.support (fun γ => F (y : Y) γ)).Finite := fun y => hs y
  have ho' : {o : orbitRel.Quotient Γ S | ∃ γ, F ((Quotient.out o : S) : Y) γ ≠ 0}.Finite := by
    have hφ := injective_mk_comp_out (G := Γ) (Y := Y) (Y' := S) Subtype.val
      Subtype.val_injective (fun _ _ => rfl)
    refine (ho.preimage hφ.injOn).subset ?_
    rintro o ⟨γ, hγ⟩
    obtain ⟨η, hη⟩ := out_mk_mem_orbit (G := Γ) ((Quotient.out o : S) : Y)
    simp only at hη
    refine ⟨η * γ * η⁻¹, ?_⟩
    show F (Quotient.out (Quotient.mk (orbitRel Γ Y) ((Quotient.out o : S) : Y))) (η * γ * η⁻¹) ≠ 0
    rw [← hη, hF]; exact hγ
  have key := finsum_orbits_eq_finsum_conjClasses (fun (y : S) γ => F (y : Y) γ) hF' hst' hs' ho'
  refine Eq.trans ?_ (key.trans (finsum_congr fun c => ?_))
  · refine finsum_orbits_restrict (G := Γ) Subtype.val Subtype.val_injective (fun _ _ => rfl)
      (fun y => ((Nat.card (stabilizer Γ y) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F y γ)
      (fun y : S => ((Nat.card (stabilizer Γ y) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (y : Y) γ)
      (fun y => by simp only [hstabS]) (fun η y => ?_) (fun y hy => ?_)
    · simp only [natCard_stabilizer_smul]
      congr 1
      rw [← finsum_comp_equiv (MulAut.conj η).toEquiv]
      refine finsum_congr fun γ => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      exact hF η y γ
    · by_contra hn
      apply hy
      have hinf : ¬ (stabilizer Γ y : Set Γ).Finite := fun h => hn ⟨⟨y, h⟩, rfl⟩
      haveI : Infinite (stabilizer Γ y) := Set.Infinite.to_subtype hinf
      rw [Nat.card_eq_zero_of_infinite (α := stabilizer Γ y), Nat.cast_zero, inv_zero, zero_mul]
  · set c' := Quotient.out c
    refine (finsum_orbits_restrict (G := Subgroup.centralizer {c'}) (Y := Y) (Y' := S)
      Subtype.val Subtype.val_injective (fun _ _ => rfl)
      (fun y => ((Nat.card (stabilizer Γ y ⊓ Subgroup.centralizer {c'} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y c')
      (fun y : S => ((Nat.card (stabilizer Γ y ⊓ Subgroup.centralizer {c'} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
        F (y : Y) c')
      (fun y => by simp only [hstabS]) (fun η y => ?_) (fun y hy => ?_)).symm
    · have hc : (η : Γ) * c' * (η : Γ)⁻¹ = c' := by
        have := Subgroup.mem_centralizer_iff.mp η.2 c' (Set.mem_singleton _)
        rw [← this, mul_inv_cancel_right]
      have hFc := hF η y c'
      rw [hc] at hFc
      simp only [Subgroup.smul_def]
      rw [natCard_stabilizer_inf_smul _ (η : Γ) (mem_iff_conj_mem _ η.2) y, hFc]
    · by_contra hn
      apply hy
      have hinf : ¬ (stabilizer Γ y : Set Γ).Finite := fun h => hn ⟨⟨y, h⟩, rfl⟩
      by_cases hc : F y c' = 0
      · simp [hc]
      have hI := stabilizer_inf_centralizer_infinite F hF y (hs y) c' hc hinf
      have h0 : Nat.card (stabilizer Γ y ⊓ Subgroup.centralizer {c'} : Subgroup Γ) = 0 := by
        haveI : Infinite (stabilizer Γ y ⊓ Subgroup.centralizer {c'} : Subgroup Γ) := hI.to_subtype
        exact Nat.card_eq_zero_of_infinite
      rw [h0, Nat.cast_zero, inv_zero, zero_mul]

end GlobalTheory.OrbitUnfold
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_sum_conj_classes : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → (∀ y : Y, (Function.support (F y)).Finite) → {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite → ∑ᶠ o : MulAction.orbitRel.Quotient Γ Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o)) : ℕ) : ℂ)⁻¹ * ∑ᶠ γ : Γ, F (Quotient.out o) γ = ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) := by
  first | (exact @GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer) | (exact GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer) | (intros; apply GlobalTheory.OrbitUnfold.finsum_orbits_eq_finsum_conjClasses_of_any_stabilizer  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerOrbitSumConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootModelPointHeightDegree
namespace GlobalTheory.ClassPart

private lemma summand_conj {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) (η : Γ) (y : Y) (γ : Γ) :
    ((Nat.card (MulAction.stabilizer Γ (η • y) ⊓ Subgroup.centralizer {η * γ * η⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ *
        F (η • y) (η * γ * η⁻¹) =
      ((Nat.card (MulAction.stabilizer Γ y ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y γ := by
  rw [hF]
  congr 3
  symm
  apply Nat.card_congr
  refine Equiv.subtypeEquiv (MulAut.conj η).toEquiv ?_
  intro s
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
    MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff, mul_smul, inv_smul_smul, smul_left_cancel_iff]
  refine and_congr_right (fun _ => ?_)
  change s * γ = γ * s ↔ (η * s * η⁻¹) * (η * γ * η⁻¹) = (η * γ * η⁻¹) * (η * s * η⁻¹)
  rw [show η * s * η⁻¹ * (η * γ * η⁻¹) = η * (s * γ) * η⁻¹ by group,
    show η * γ * η⁻¹ * (η * s * η⁻¹) = η * (γ * s) * η⁻¹ by group, mul_left_inj, mul_right_inj]

theorem orbitSum_conj : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → ∀ (γ g : Γ), ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) γ = ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {g * γ * g⁻¹}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {g * γ * g⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (g * γ * g⁻¹) := by
  intro Γ Y _ _ F hF γ g
  set S : Γ → Y → ℂ := fun c y =>
    ((Nat.card (MulAction.stabilizer Γ y ⊓ Subgroup.centralizer {c} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F y c with hSdef
  have hS : ∀ (η : Γ) (y : Y) (c : Γ), S (η * c * η⁻¹) (η • y) = S c y := fun η y c => summand_conj F hF η y c
  have hZ : ∀ (c : Γ) (ζ : Γ), ζ ∈ Subgroup.centralizer {c} → ∀ y, S c (ζ • y) = S c y := by
    intro c ζ hζ y
    have hcj : ζ * c * ζ⁻¹ = c := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hζ
      rw [hζ]; group
    have := hS ζ y c
    rwa [hcj] at this
  set γ' := g * γ * g⁻¹ with hγ'
  have hrel : ∀ a b : Y, (MulAction.orbitRel (Subgroup.centralizer {γ}) Y) a b ↔
      (MulAction.orbitRel (Subgroup.centralizer {γ'}) Y) (g • a) (g • b) := by
    intro a b
    simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subtype.exists, Subgroup.mk_smul]
    constructor
    · rintro ⟨ζ, hζ, h⟩
      refine ⟨g * ζ * g⁻¹, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hζ ⊢
        rw [hγ']
        change (g * ζ * g⁻¹) * (g * γ * g⁻¹) = (g * γ * g⁻¹) * (g * ζ * g⁻¹)
        rw [show g * ζ * g⁻¹ * (g * γ * g⁻¹) = g * (ζ * γ) * g⁻¹ by group,
          show g * γ * g⁻¹ * (g * ζ * g⁻¹) = g * (γ * ζ) * g⁻¹ by group, hζ]
      · rw [← h]; simp [mul_smul]
    · rintro ⟨ζ, hζ, h⟩
      refine ⟨g⁻¹ * ζ * g, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hζ ⊢
        rw [hγ'] at hζ
        have h2 : g⁻¹ * (g * γ * g⁻¹ * ζ) * g = g⁻¹ * (ζ * (g * γ * g⁻¹)) * g := by rw [hζ]
        rw [show g⁻¹ * (g * γ * g⁻¹ * ζ) * g = γ * (g⁻¹ * ζ * g) by group,
          show g⁻¹ * (ζ * (g * γ * g⁻¹)) * g = g⁻¹ * ζ * g * γ by group] at h2
        exact h2.symm
      · have := congrArg (g⁻¹ • ·) h
        simpa [mul_smul] using this
  let e : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y ≃
      MulAction.orbitRel.Quotient (Subgroup.centralizer {γ'}) Y :=
    Quotient.congr (MulAction.toPerm g) hrel
  change ∑ᶠ o, S γ (Quotient.out o) = ∑ᶠ o, S γ' (Quotient.out o)
  rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro o
  have hmk : (Quotient.mk _ (Quotient.out (e o)) : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ'}) Y) =
      Quotient.mk _ (g • Quotient.out o) := by
    rw [Quotient.out_eq]
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have hr := Quotient.exact hmk
  have hr' : Quotient.out (e o) ∈ MulAction.orbit (Subgroup.centralizer {γ'}) (g • Quotient.out o) := hr
  rw [MulAction.mem_orbit_iff] at hr'
  obtain ⟨ζ, hζ⟩ := hr'
  rw [← hζ, Subgroup.smul_def, hZ γ' ζ ζ.2, hγ', hS]

end GlobalTheory.ClassPart
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_orbit_sum_conjugate : ∀ {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ), (∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ) → ∀ (γ g : Γ), ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {γ}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {γ} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) γ = ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {g * γ * g⁻¹}) Y, ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {g * γ * g⁻¹} : Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (g * γ * g⁻¹) := by
  first | (exact @GlobalTheory.ClassPart.orbitSum_conj) | (exact GlobalTheory.ClassPart.orbitSum_conj) | (intros; apply GlobalTheory.ClassPart.orbitSum_conj <;> assumption)
end

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx.CxReg

open GlobalTheory.LKCx.Regroup

variable {p : ℕ} [Fact p.Prime]

theorem sep_of_regAf (G : HTGroup p) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1) (f : G.GAf → ℂ)
    (hreg : ∀ g, f g ≠ 0 → RegAf G g) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (hsym : sh G β = β) (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) :
    (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) := by
  rintro y h hne ⟨z, hz, hfix⟩
  exact GlobalTheory.LKCx.minpoly_of_regAf_of_fixL p G v hv β hsym hR x t hx y h ⟨z, hz⟩ hfix (hreg _ hne)

theorem finite_pts_reg (G : HTGroup p) (ha : G.a = 1) (v : InfinitePlace G.F) (hv : sigPosH (G.gram_herm v) = 1)
    (L : G.Level) (f : G.GAf → ℂ) (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f)
    (hreg : ∀ g, f g ≠ 0 → RegAf G g) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ)
    (hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f') (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (hsym : sh G β = β) (htr : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) :
    Set.Finite {q : Pts G v β x t hx L.K.toSubgroup K' | ∃ y : grp G β, FixL G v β y (Quot.out q).2.1 ∧
      f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) *
        f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) ≠ 0} := by
  have hsep := sep_of_regAf G v hv f hreg β x t hx hsym htr
  obtain ⟨Y, hY⟩ := Classical.axiomOfChoice
    (fun P => GlobalTheory.T.orbital_integral_test_function_first p G ha v hv L f hf K' f' hf' β x t hx hsep hsym htr P)
  refine ((GlobalTheory.T.orbital_term_real_trivialisation p G ha v hv L f hf K' f' hf' β x t hx hsym htr).biUnion
    (fun P _ => (Y P).finite_toSet.biUnion
      (fun y₀ _ => GlobalTheory.T.orbital_integral_test_function_second p G ha v hv L f hf K' f' hf' β x t hx hsep hsym htr y₀))).subset ?_
  rintro q ⟨y, hy, hne⟩
  obtain ⟨y₀, hy₀, γ, rfl⟩ := hY _ y rfl ⟨Quot.out q, hy, hne⟩
  simp only [Set.mem_iUnion]
  exact ⟨_, ⟨γ * y₀ * γ⁻¹, Quot.out q, rfl, hy, hne⟩, y₀, hy₀, γ, hy, hne⟩

theorem class_summand_eq_term_of_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) → ∀ (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : grp G P.β), (r : G.Cˣ × ℚˣ) = (P.γ, P.c) → (if (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v P.β *ᵥ z)).re ∧ FixL G v P.β r z) then wt (minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * pointSum ((toAfF G P.β x t hx).comp (Subgroup.centralizer {r}).subtype) ((toP1 G P.β).comp (Subgroup.centralizer {r}).subtype) (MonoidHom.id (Gr G 1)) Kf K' (toAfF G P.β x t hx r) (toP1 G P.β r) f f' else 0) = (if ∃ μ, P.Mark μ then wt P.pol * P.term Kf f 1 K' f' else 0) := by
  intro p _ G hG v hv wt Kf f K' f' hf hf' P x t hx r hr
  have hiff := fix_iff_mark G hG v hv P r hr
  by_cases hm : ∃ μ, P.Mark μ
  · rw [if_pos (hiff.2 hm), if_pos hm]
    obtain ⟨μ, hμ⟩ := hm
    have hpos := cent_sim_pos p G P μ hG hμ
    set e := centEquiv G P hpos r hr with he
    have h1 : (toAfF G P.β x t hx).comp (Subgroup.centralizer {r}).subtype =
        (P.toAf x t hx).comp e.toMonoidHom := by
      ext1 y; rfl
    have h2 : (toP1 G P.β).comp (Subgroup.centralizer {r}).subtype = (P.toQr 1 1).comp e.toMonoidHom := by
      ext1 y
      show inclG G 1 (locC G y.1.1) = (MulAut.conj (1 : Gr G 1)⁻¹) (inclG G 1 (locC G y.1.1))
      simp
    have h3 : toAfF G P.β x t hx r = P.toAf x t hx P.self := by
      obtain ⟨r, hr'⟩ := r
      simp only at hr
      subst hr
      rfl
    have h4 : toP1 G P.β r = inclG G 1 P.atP := by
      show inclG G 1 (locC G (r : G.Cˣ × ℚˣ)) = _
      rw [hr]; rfl
    have h5 : minpoly G.F (((r : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P.pol := by
      rw [hr]; rfl
    rw [h1, h2, h3, h4, h5, GlobalTheory.pointSum_comp_mulEquiv, GlobalTheory.T.orbital_term_point_sum p G P Kf f K' f' hf hf' x t hx]
  · rw [if_neg (fun h => hm (hiff.1 h)), if_neg hm]

end GlobalTheory.LKCx.CxReg

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
