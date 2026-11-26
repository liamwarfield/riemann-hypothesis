module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminingLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransportOfLatClaims

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumCoordinateIsAlgebraic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumCoordinateIsAlgebraic
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.ToricCoordAlg

theorem isAlgebraic_coordIn : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ)
    (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀)
    (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s)
    (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ)
    (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := by
  intro hA K _ _ d δ ι h2 hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q χ T hV
  classical
  obtain ⟨hQ, hχ, hfin, S, hS, rfl⟩ := hV
  have htriv := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hE h𝔣 hQ hχ
  have : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, GlobalTheory.TwistedTransportProof.coordIn_eq, Finset.mul_sum]
  refine (mem_algebraicClosure_iff (F := ℚ) (E := ℂ)).1 (sum_mem fun q _ => ?_)
  have e : coordIn E d s κ Ω₀ 1 * (((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * S q 0) =
      ((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * coordIn E d s κ Ω₀ (S q 0) := by
    rw [GlobalTheory.TwistedTransportProof.coordIn_eq d s κ Ω₀ (S q 0)]; ring
  rw [e]
  have h1 := hA K d δ ι h2 hd hδ Λ₀ Ω₀ hΛ hΩ E I φ s 𝔣 Q ⟨hE, hφ, hφK, hs, h𝔣, hQ⟩ κ q.out (S q) (hS q)
  have h3 : IsAlgebraic ℚ ((finPart χ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ)) :=
    (GlobalTheory.ToricRatioBridge.isAlgebraic_finPart hχ.2.2.1 htriv q.out).mul
      (GlobalTheory.TwistedTransportProof.isAlgebraic_modF_pow q.out s)
  refine mul_mem (inv_mem ?_) ?_ <;> rw [mem_algebraicClosure_iff] <;> assumption

end GlobalTheory.ToricCoordAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumCoordinateIsAlgebraicStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricSum_coordinate_isAlgebraic : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := by
  first | exact @GlobalTheory.ToricCoordAlg.isAlgebraic_coordIn | exact GlobalTheory.ToricCoordAlg.isAlgebraic_coordIn | (intros; apply GlobalTheory.ToricCoordAlg.isAlgebraic_coordIn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjToricPeriodCoordinateSumOverClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjToricPeriodCoordinateSumOverClasses
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.ConjCoordToric

theorem lamF_mul {E : Type} [Field E] [NumberField E] (s : ℕ) (χ : HChar E) (y y' : (Af E)ˣ) :
    lamF s χ (y * y') = lamF s χ y * lamF s χ y' := by
  unfold lamF
  rw [map_mul, Units.val_mul, IdeleModule.modF_mul, mul_pow]
  push_cast
  ring

theorem coordIn_eq_mul {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) :
    coordIn E d s κ Ω T = coordIn E d s κ Ω 1 * T := by
  unfold GlobalTheory.ToricTransport.coordIn
  ring

theorem exists_latSum {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E))
    (h : ∀ q : PicO c, ∃ S, IsLatSum φ (2 * s) κ (lattice c q.out) S) (y : (Af E)ˣ) :
    ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : PicO c, q = QuotientGroup.mk y := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ := h q
  have hq' : (QuotientGroup.mk q.out : PicO c) = QuotientGroup.mk y := by rw [QuotientGroup.out_eq', hq]
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq')
  have hy : y = Units.map (algebraMap E (Af E)).toMonoidHom α * q.out * u := by
    have : y = q.out * (Units.map (algebraMap E (Af E)).toMonoidHom α * u) := by rw [hau]; group
    rw [this]
    ac_rfl
  rw [hy, GlobalTheory.ClassInv.lattice_princ_mul_unit _ α hu]
  exact ⟨_, (GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _ κ α S hS).1⟩

theorem conj_coordIn_toric : ∀ (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ κ' : I → ℕ) (hκ' : IsConjWt φ g κ κ') (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ χ' : HChar E) (T T' : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T) (hV' : IsConjSum φ s κ' 𝔣 Q g χ χ' T'), g (coordIn E d s κ Ω₀ T) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * T') := by
  intro hC K _ _ d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E _ _ _ _ I _ φ hE hφ hφK s hs κ κ' hκ' 𝔣 h𝔣 Q χ χ' T T' hV hV'
  classical
  obtain ⟨hAux, hVal, -, S, hS, rfl⟩ := hV
  obtain ⟨⟨hlam, hInf'⟩, hfin', S'', hS'', rfl⟩ := hV'
  haveI : Fintype (PicO (condQ 𝔣 Q)) := Fintype.ofFinite _
  have hunit' : ∀ u ∈ hatOUnits (condQ 𝔣 Q), finPart χ' u = 1 := by
    intro u hu
    have h1 : lamF s χ' u = 1 := by
      rw [hlam]
      unfold lamF
      rw [GlobalTheory.ClassInv.finPart_unit hVal hu, ObjModel.modF_unit hu]
      simp
    unfold lamF at h1
    rw [ObjModel.modF_unit hu] at h1
    simp at h1
    exact h1
  have hex : ∀ q : PicO (condQ 𝔣 Q), ∃ S', IsLatSum φ (2 * s) κ' (lattice (condQ 𝔣 Q) (q.out * (upIdele K E t)⁻¹)) S' :=
    fun q => exists_latSum hφ s κ' (condQ 𝔣 Q) (fun q => ⟨S'' q, hS'' q⟩) _
  choose S' hS' using hex
  have hLC : ∀ q : PicO (condQ 𝔣 Q), g (coordIn E d s κ Ω₀ 1 * S q 0) =
      coordIn E d s κ Ω₁ 1 * ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' q 0) := fun q => by
    rw [← coordIn_eq_mul, ← coordIn_eq_mul]
    exact hC K d δ ι h2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ hT E I φ s 𝔣 Q ⟨hE, hφ, hφK, hs, h𝔣, hAux⟩ κ κ' hκ' q.out (S q) (S' q)
      (hS q) (hS' q)
  have hCI : ∀ q : PicO (condQ 𝔣 Q), (lamF s χ' (q.out * (upIdele K E t)⁻¹))⁻¹ * S' q 0 =
      (lamF s χ' (q * QuotientGroup.mk (upIdele K E t)⁻¹).out)⁻¹ * S'' (q * QuotientGroup.mk (upIdele K E t)⁻¹) 0 := by
    intro q
    refine GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ' (condQ 𝔣 Q) χ' hInf' hunit' _ _ (S' q) (S'' _) ?_
      (hS' q) (hS'' _)
    rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
  have hsum : ∀ (ψ : HChar E) (R : PicO (condQ 𝔣 Q) → ℂ → ℂ),
      (∑ᶠ q : PicO (condQ 𝔣 Q), ((finPart ψ q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * R q 0) =
        ∑ q, (lamF s ψ q.out)⁻¹ * R q 0 := fun ψ R => by
    rw [finsum_eq_sum_of_fintype]
    rfl
  rw [hsum, hsum, coordIn_eq_mul (E := E) d s κ Ω₀, coordIn_eq_mul (E := E) d s κ Ω₁]
  calc g (coordIn E d s κ Ω₀ 1 * ∑ q, (lamF s χ q.out)⁻¹ * S q 0)
      = ∑ q, (g (lamF s χ q.out))⁻¹ * g (coordIn E d s κ Ω₀ 1 * S q 0) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [show coordIn E d s κ Ω₀ 1 * ((lamF s χ q.out)⁻¹ * S q 0) =
          (lamF s χ q.out)⁻¹ * (coordIn E d s κ Ω₀ 1 * S q 0) by ring, map_mul, map_inv₀]
    _ = ∑ q, (lamF s χ' q.out)⁻¹ * (coordIn E d s κ Ω₁ 1 * ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * S' q 0)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hlam, hLC]
    _ = ∑ q, coordIn E d s κ Ω₁ 1 * (((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ *
          ((lamF s χ' (q * QuotientGroup.mk (upIdele K E t)⁻¹).out)⁻¹ * S'' (q * QuotientGroup.mk (upIdele K E t)⁻¹) 0) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← hCI q]
        have hm : lamF s χ' q.out = lamF s χ' (q.out * (upIdele K E t)⁻¹) * lamF s χ' (upIdele K E t) := by
          rw [← lamF_mul, inv_mul_cancel_right]
        rw [hm, mul_inv]
        ring
    _ = coordIn E d s κ Ω₁ 1 * (((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ *
          ∑ q, (lamF s χ' q.out)⁻¹ * S'' q 0 := by
        rw [Finset.mul_sum]
        exact Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk (upIdele K E t)⁻¹ : PicO (condQ 𝔣 Q))) _ _ fun q => rfl
    _ = _ := by ring

end GlobalTheory.ConjCoordToric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjToricPeriodCoordinateSumOverClassesStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_toricPeriodCoordinate_sum_over_classes : ∀ (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ κ' : I → ℕ) (hκ' : IsConjWt φ g κ κ') (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ χ' : HChar E) (T T' : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T) (hV' : IsConjSum φ s κ' 𝔣 Q g χ χ' T'), g (coordIn E d s κ Ω₀ T) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * T') := by
  first | exact @GlobalTheory.ConjCoordToric.conj_coordIn_toric | exact GlobalTheory.ConjCoordToric.conj_coordIn_toric | (intros; apply GlobalTheory.ConjCoordToric.conj_coordIn_toric <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisConjHeckeCharacterFinitePartEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisConjHeckeCharacterFinitePartEqOne
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CMVal.NormConj

theorem norm_sigma_ratio {E : Type} [Field E] [NumberField E] [IsCMField E] (σ : ℂ ≃+* ℂ) (φ : E →+* ℂ) (α : Eˣ) :
    ‖σ (φ (α : E) / starRingEnd ℂ (φ (α : E)))‖ = 1 := by
  rw [← IsCMField.complexEmbedding_complexConj, map_div₀]
  have e2 : σ (φ (IsCMField.complexConj E (α : E))) = starRingEnd ℂ (((σ : ℂ →+* ℂ).comp φ) (α : E)) := by
    rw [← IsCMField.complexEmbedding_complexConj]; rfl
  have e1 : σ (φ (α : E)) = ((σ : ℂ →+* ℂ).comp φ) (α : E) := rfl
  have h0 : ((σ : ℂ →+* ℂ).comp φ) (α : E) ≠ 0 := by simp
  rw [e2, e1, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h0)]

end GlobalTheory.CMVal.NormConj


open GlobalTheory.CMVal.NormConj in
theorem GlobalTheory.CMVal.norm_conj_finPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E)
    (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ),
    ‖σ (finPart χ y : ℂ)‖ = 1 := by
  intro E _ _ _ I _ φ _ s κ c hc χ hinf hχ σ y
  classical
  have hfin := GlobalTheory.CMVal.PicFin.finite_picO E c hc
  have hpos : 0 < Nat.card (PicO c) := Nat.card_pos
  have hmem : y ^ Nat.card (PicO c) ∈ (princ ⊔ hatOUnits c : Subgroup (Af E)ˣ) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  obtain ⟨p, ⟨α, rfl⟩, u, hu, hpu⟩ := Subgroup.mem_sup.1 hmem
  set h := Nat.card (PicO c)
  have hf : ((finPart χ y : ℂ)) ^ h = ((χ.inf α : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hpu, map_mul, hχ u hu, mul_one,
      eq_inv_of_mul_eq_one_left (finPart_mul_inf χ α), Units.val_inv_eq_inv_val]
  have hn : ‖σ (finPart χ y : ℂ)‖ ^ h = 1 := by
    rw [← norm_pow, ← map_pow, hf, (hasInfRatio_iff χ φ _).1 hinf α, map_inv₀, norm_inv, map_prod, norm_prod]
    simp only [map_zpow₀, norm_zpow, norm_sigma_ratio, one_zpow, Finset.prod_const_one, inv_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').1 hn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisConjHeckeCharacterFinitePartEqOneStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_galois_conj_heckeCharacter_finitePart_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E) (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ), ‖σ (finPart χ y : ℂ)‖ = 1 := by
  first | exact @GlobalTheory.CMVal.norm_conj_finPart | exact GlobalTheory.CMVal.norm_conj_finPart | (intros; apply GlobalTheory.CMVal.norm_conj_finPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributedIdealClassesOfHilbertClassFieldJ
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributedIdealClassesOfHilbertClassFieldJ
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
open GlobalTheory.Published
open scoped IntermediateField

noncomputable section

namespace GlobalTheory.EquidistJ

theorem card_ext_mul_finrank (L M : IntermediateField ℚ ℂ) (hML : M ≤ L) [FiniteDimensional ℚ L] (σ : ℂ ≃+* ℂ) :
    Nat.card {τ : L →+* ℂ // ∀ x : L, (x : ℂ) ∈ M → τ x = σ x} * Module.finrank ℚ M = Module.finrank ℚ L := by
  let E := IntermediateField.extendScalars hML
  have hEL : Module.finrank ℚ E = Module.finrank ℚ L := rfl
  have hEpos : 0 < Module.finrank ℚ E := by rw [hEL]; exact Module.finrank_pos
  haveI : FiniteDimensional ℚ E := Module.finite_of_finrank_pos hEpos
  haveI : FiniteDimensional M E := FiniteDimensional.right ℚ M E
  let ι : L →+* E :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let ι' : E →+* L :=
    { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  let e : {τ : L →+* ℂ // ∀ x : L, (x : ℂ) ∈ M → τ x = σ x} ≃ (E →ₐ[M] ℂ) :=
    { toFun := fun τ =>
        { toRingHom := σ.symm.toRingHom.comp (τ.1.comp ι')
          commutes' := fun m => by
            change σ.symm (τ.1 ⟨m.1, hML m.2⟩) = m.1
            rw [τ.2 ⟨m.1, hML m.2⟩ m.2]
            exact σ.symm_apply_apply _ }
      invFun := fun f => ⟨σ.toRingHom.comp (f.toRingHom.comp ι), fun x hx => by
          change σ (f ⟨x.1, x.2⟩) = σ x.1
          congr 1
          exact f.commutes ⟨x.1, hx⟩⟩
      left_inv := fun τ => Subtype.ext (RingHom.ext fun x => by
          change σ (σ.symm (τ.1 ⟨x.1, x.2⟩)) = τ.1 x
          rw [σ.apply_symm_apply])
      right_inv := fun f => AlgHom.ext fun x => by
          change σ.symm (σ (f ⟨x.1, x.2⟩)) = f x
          rw [σ.symm_apply_apply] }
  set_option synthInstance.maxHeartbeats 200000 in
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, AlgHom.card M E ℂ, mul_comm,
      Module.finrank_mul_finrank ℚ M E, hEL]

theorem equidistributed_of_hilbertClassFieldJ : ∀ (hH : GlobalTheory.Published.HilbertClassFieldJ) {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair) (hΛ : IsLatOf φK 1 ΛK) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔞 : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ Λ : PeriodPair, IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) Λ ∧ jLat Λ = σ (jLat ΛK)), Equidistributed φK (jLat ΛK) 𝔞 := by
  intro hH K _ _ _ h2 φK ΛK hΛ 𝔞 h𝔞
  letI : Algebra K ℂ := φK.toAlgebra
  have hj : ∀ Λ : PeriodPair, jLat Λ = (latticeCurve Λ).j := fun Λ => by rw [latticeCurve_j_eq]; rfl
  have hlat : ∀ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : PeriodPair),
      IsLatOf φK (𝔟 : FractionalIdeal (𝓞 K)⁰ K) Λ → IsIdealLattice 𝔟 Λ := fun _ _ h => h
  obtain ⟨-, hfin, hcl, -, hrange⟩ := hH K h2 ΛK (hlat 1 ΛK hΛ)
  set H : IntermediateField K ℂ := K⟮(latticeCurve ΛK).j⟯ with hHdef
  have hpos : 0 < Module.finrank K H := hfin ▸ Fintype.card_pos
  haveI : FiniteDimensional K H := Module.finite_of_finrank_pos hpos
  have hj0 : (latticeCurve ΛK).j ∈ H := IntermediateField.mem_adjoin_simple_self K _
  have hj0' : jLat ΛK ∈ H := by rw [hj]; exact hj0
  have halg : IsAlgebraic ℚ (jLat ΛK) := by
    rw [hj]
    exact (IntermediateField.isAlgebraic_iff.1
      (Algebra.IsAlgebraic.isAlgebraic (⟨_, hj0⟩ : H))).restrictScalars ℚ
  have hclass : ∀ σ σ' : ℂ ≃+* ℂ, Fixes φK σ → Fixes φK σ' →
      (ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') ↔ σ (jLat ΛK) = σ' (jLat ΛK)) := by
    intro σ σ' hσ hσ'
    obtain ⟨Λ, hl, hjl⟩ := h𝔞 σ hσ
    obtain ⟨Λ', hl', hjl'⟩ := h𝔞 σ' hσ'
    rw [← hjl, ← hjl', hj, hj]
    exact (hcl _ _ Λ Λ' (hlat _ _ hl) (hlat _ _ hl')).symm
  refine ⟨halg, hclass, ?_⟩
  intro L hLf hLg hKL hjL C
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective C
  obtain ⟨Lb, hLb⟩ := exists_isIdealLattice h2 (FractionalIdeal.mk0 K I)
  have hinv : (latticeCurve Lb).j ∈ idealInvariants K := ⟨_, Lb, hLb, rfl⟩
  rw [← hrange] at hinv
  obtain ⟨g, hg⟩ := hinv
  haveI : NumberField H := NumberField.of_module_finite K H
  haveI : Countable H := (Module.finBasis ℚ H).equivFun.injective.countable
  obtain ⟨σC, hσC⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq H.val.toRingHom
    (H.val.toRingHom.comp g.toAlgHom.toRingHom)
  have hfixC : Fixes φK σC := fun x => by
    have := hσC (algebraMap K H x)
    exact (by simpa using this : σC (algebraMap K ℂ x) = algebraMap K ℂ x)
  have hσCj : σC (jLat ΛK) = jLat Lb := by
    have := hσC (IntermediateField.AdjoinSimple.gen K (latticeCurve ΛK).j)
    rw [hj, hj]
    simpa [hg] using this
  have hclC : ClassGroup.mk K (𝔞 σC) = ClassGroup.mk0 I := by
    obtain ⟨Λ, hl, hjl⟩ := h𝔞 σC hfixC
    rw [← ClassGroup.mk_mk0 K]
    refine (hcl _ _ Λ Lb (hlat _ _ hl) hLb).1 ?_
    rw [← hj, hjl, hσCj, hj]
  let L' : IntermediateField K ℂ := L.toSubfield.toIntermediateField hKL
  have hHL : H ≤ L' := IntermediateField.adjoin_simple_le_iff.2 (by rw [← hj]; exact hjL)
  haveI : FiniteDimensional ℚ L := hLf
  haveI : Countable L := (Module.finBasis ℚ L).equivFun.injective.countable
  have hcount := card_ext_mul_finrank L (H.restrictScalars ℚ) (fun x hx => hHL hx) σC
  have hM : Module.finrank ℚ (H.restrictScalars ℚ) = Module.finrank ℚ K * Module.finrank K H := by
    rw [Module.finrank_mul_finrank ℚ K H]
    rfl
  rw [hM, h2, hfin] at hcount
  have hiff : ∀ τ : L →+* ℂ, (∃ σ : ℂ ≃+* ℂ, Fixes φK σ ∧ (∀ x : L, σ (x : ℂ) = τ x) ∧
      ClassGroup.mk K (𝔞 σ) = ClassGroup.mk0 I) ↔ ∀ x : L, (x : ℂ) ∈ H.restrictScalars ℚ → τ x = σC x := by
    intro τ
    constructor
    · rintro ⟨σ, hσ, hστ, hcσ⟩ x hx
      have e : σ (jLat ΛK) = σC (jLat ΛK) := (hclass σ σC hσ hfixC).1 (hcσ.trans hclC.symm)
      rw [hj] at e
      let a : H →ₐ[K] ℂ := ((AlgEquiv.ofRingEquiv (f := σ) hσ).toAlgHom).comp H.val
      let b : H →ₐ[K] ℂ := ((AlgEquiv.ofRingEquiv (f := σC) hfixC).toAlgHom).comp H.val
      have hab : a = b := by
        refine IntermediateField.algHom_ext_of_eq_adjoin K rfl ?_
        rintro y rfl
        exact e
      rw [← hστ x]
      exact DFunLike.congr_fun hab ⟨x, hx⟩
    · intro hτ
      obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq L.val.toRingHom τ
      have hσf : Fixes φK σ := fun x => by
        have h1 := hσ ⟨φK x, hKL x⟩
        have h2 := hτ ⟨φK x, hKL x⟩ (H.algebraMap_mem x)
        have h3 := hfixC x
        exact h1.trans (h2.trans h3)
      refine ⟨σ, hσf, fun x => hσ x, ?_⟩
      refine ((hclass σ σC hσf hfixC).2 ?_).trans hclC
      have h1 := hσ ⟨jLat ΛK, hjL⟩
      have h2 := hτ ⟨jLat ΛK, hjL⟩ hj0'
      exact h1.trans h2
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  linarith

end GlobalTheory.EquidistJ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquidistributedIdealClassesOfHilbertClassFieldJStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equidistributed_idealClasses_of_hilbertClassFieldJ : ∀ (hH : GlobalTheory.Published.HilbertClassFieldJ) {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair) (hΛ : IsLatOf φK 1 ΛK) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔞 : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ Λ : PeriodPair, IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) Λ ∧ jLat Λ = σ (jLat ΛK)), Equidistributed φK (jLat ΛK) 𝔞 := by
  first | exact @GlobalTheory.EquidistJ.equidistributed_of_hilbertClassFieldJ | exact GlobalTheory.EquidistJ.equidistributed_of_hilbertClassFieldJ | (intros; apply GlobalTheory.EquidistJ.equidistributed_of_hilbertClassFieldJ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIdeleModuleExistsRat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIdeleModuleExistsRat
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.CMVal.ModFRat

theorem modF_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := by
  intro E _ _ y
  refine ⟨∏ᶠ v : HeightOneSpectrum (𝓞 E), ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))), ?_⟩
  have h := MonoidHom.map_finprod_of_injective ((Rat.castHom ℝ : ℚ →+* ℝ) : ℚ →* ℝ) Rat.cast_injective
    (fun v : HeightOneSpectrum (𝓞 E) => ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))))
  simp only [MonoidHom.coe_coe, Rat.coe_castHom, Rat.cast_zpow, Rat.cast_natCast] at h
  rw [h]
  rfl

end GlobalTheory.CMVal.ModFRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIdeleModuleExistsRatStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteIdele_module_exists_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := by
  first | exact @GlobalTheory.CMVal.ModFRat.modF_rat | exact GlobalTheory.CMVal.ModFRat.modF_rat | (intros; apply GlobalTheory.CMVal.ModFRat.modF_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFieldExistsSqrtNegDiscr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFieldExistsSqrtNegDiscr
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_sq_eq_neg_of_discr_eq_neg : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := by
  classical
  intro K _ _ d h2 hd
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  haveI : IsGalois ℚ K := inferInstance
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨σ, hσ, huniq⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[ℚ] K)).1 hcard
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, σ} := by
    ext y
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hy : y = 1
    · exact Or.inl hy
    · exact Or.inr (huniq y hy)
  have htr : ∀ x : K, algebraMap ℚ K (Algebra.trace ℚ K x) = x + σ x := by
    intro x
    rw [_root_.trace_eq_sum_automorphisms, huniv, Finset.sum_pair (Ne.symm hσ)]
    rfl
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 :=
    Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis (integralBasis K), h2])
  let b : Fin 2 → K := fun i => integralBasis K (e.symm i)
  have hb : ⇑(integralBasis K) ∘ ⇑e.symm = b := rfl
  have key : algebraMap ℚ K (discr K : ℚ) = (b 0 * σ (b 1) - b 1 * σ (b 0)) ^ 2 := by
    rw [coe_discr, ← Algebra.discr_reindex ℚ (integralBasis K) e, hb, Algebra.discr_def,
      Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, map_sub, map_mul, htr]
    ring
  refine ⟨b 0 * σ (b 1) - b 1 * σ (b 0), ?_⟩
  rw [← key, hd]
  push_cast
  simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticFieldExistsSqrtNegDiscrStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticField_exists_sqrt_neg_discr : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := by
  first | exact @GlobalTheory.exists_sq_eq_neg_of_discr_eq_neg | exact GlobalTheory.exists_sq_eq_neg_of_discr_eq_neg | (intros; apply GlobalTheory.exists_sq_eq_neg_of_discr_eq_neg <;> assumption)
end
end

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn coordIn_div)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.TransportProof
theorem exists_sq_eq_neg : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := GlobalTheory.T.quadraticField_exists_sqrt_neg_discr

theorem nrm_eq_modF : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h : IsInvIdealOf t 𝔞), nrm 𝔞 = modF t := GlobalTheory.T.fractionalIdealNorm_eq_finiteIdeleModule

theorem modF_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := GlobalTheory.T.finiteIdele_module_exists_rat

theorem modF_upIdele : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ), modF (upIdele K E t) = modF t ^ Module.finrank K E := GlobalTheory.T.modF_finiteIdeleUpToExtension

theorem card_eq_finrank : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2), Fintype.card I = Module.finrank K E := GlobalTheory.T.isCMTypeOfEmbeddings_card_eq_finrank

theorem norm_conj_finPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E) (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ), ‖σ (finPart χ y : ℂ)‖ = 1 := GlobalTheory.T.norm_galois_conj_heckeCharacter_finitePart_eq_one

theorem algebraic_coordIn_toric : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := GlobalTheory.T.toricSum_coordinate_isAlgebraic

theorem conj_coordIn_toric : ∀ (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ κ' : I → ℕ) (hκ' : IsConjWt φ g κ κ') (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ χ' : HChar E) (T T' : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T) (hV' : IsConjSum φ s κ' 𝔣 Q g χ χ' T'), g (coordIn E d s κ Ω₀ T) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * T') := GlobalTheory.T.conj_toricPeriodCoordinate_sum_over_classes

theorem equidistributed_of_j : ∀ (hH : GlobalTheory.Published.HilbertClassFieldJ) {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair) (hΛ : IsLatOf φK 1 ΛK) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔞 : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ Λ : PeriodPair, IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) Λ ∧ jLat Λ = σ (jLat ΛK)), Equidistributed φK (jLat ΛK) 𝔞 := GlobalTheory.T.equidistributed_idealClasses_of_hilbertClassFieldJ

theorem isTotallyComplex_of_discr_neg {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    (h : discr K < 0) : IsTotallyComplex K := by
  have hs := sign_discr K
  rw [Int.sign_eq_neg_one_of_neg h] at hs
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h2] at hr
  have hc : InfinitePlace.nrComplexPlaces K = 1 := by
    rcases Nat.even_or_odd (InfinitePlace.nrComplexPlaces K) with he | ho
    · rw [he.neg_one_pow] at hs; norm_num at hs
    · obtain ⟨k, hk⟩ := ho; omega
  exact nrRealPlaces_eq_zero_iff.1 (by omega)

theorem disc_j_of_torsTransport {K : Type} [Field K] [NumberField K] {ι : K →+* ℂ} {g : ℂ ≃+* ℂ} {t : (Af K)ˣ}
    {Λ₀ Λ₁ : PeriodPair} {Ω₀ Ω₁ : ℂ} (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) :
    Ω₁ ^ 12 = latDisc Λ₁ ∧ jLat Λ₁ = g (jLat Λ₀) := by
  obtain ⟨h0, h1, -, -, -, ha, hb, -⟩ := hT
  have e0 : (Λ₀.g₂ / Ω₀ ^ 4) ^ 3 - 27 * (Λ₀.g₃ / Ω₀ ^ 6) ^ 2 = 1 := by
    have : latDisc Λ₀ / Ω₀ ^ 12 = 1 := by rw [← hΩ, div_self (pow_ne_zero _ h0)]
    rw [← this, latDisc]; field_simp
  have e1 : (Λ₁.g₂ / Ω₁ ^ 4) ^ 3 - 27 * (Λ₁.g₃ / Ω₁ ^ 6) ^ 2 = 1 := by
    rw [← ha, ← hb]
    have := congrArg g e0
    simpa [map_sub, map_pow, map_mul, map_ofNat] using this
  have hD : Ω₁ ^ 12 = latDisc Λ₁ := by
    rw [latDisc]; field_simp at e1; linear_combination -e1
  refine ⟨hD, ?_⟩
  have j0 : jLat Λ₀ = 1728 * (Λ₀.g₂ / Ω₀ ^ 4) ^ 3 := by
    rw [jLat, ← hΩ]; field_simp
  have j1 : jLat Λ₁ = 1728 * (Λ₁.g₂ / Ω₁ ^ 4) ^ 3 := by
    rw [jLat, ← hD]; field_simp
  rw [j0, j1, map_mul, map_pow, ha, map_ofNat]

theorem condQ_ne_bot {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣)
    (Q : Finset (HeightOneSpectrum (OF E))) : condQ 𝔣 Q ≠ ⊥ := by
  unfold condQ
  rw [← Ideal.zero_eq_bot]
  refine mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)

theorem norm_lamF_conj_up {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E]
    [Algebra K E] {I : Type} [Fintype I] (h2 : Module.finrank ℚ K = 2) (φ : I → E →+* ℂ) (hE : UnramFin E)
    (hφ : IsCMType φ) (s : ℕ) (κ κ' : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣)
    (Q : Finset (HeightOneSpectrum (OF E))) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (χ χ' : HChar E) (hχ : IsValChar φ s κ 𝔣 Q χ)
    (σ : ℂ ≃+* ℂ) (hc : IsConjChar φ s κ' σ χ χ') (t : (Af K)ˣ) :
    ‖lamF s χ' (upIdele K E t)‖ = modF t ^ (s * Fintype.card I) := by
  have hu := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hE h𝔣 hQ hχ
  have h1 := norm_conj_finPart φ hφ s κ (condQ 𝔣 Q) (condQ_ne_bot h𝔣 Q) χ hχ.2.2.1 hu σ (upIdele K E t)
  obtain ⟨q, hq⟩ := modF_rat (upIdele K E t)
  have hpos := GlobalTheory.CMVal.IdeleModule.modF_pos (upIdele K E t)
  rw [hc.1, lamF, map_mul, norm_mul, h1, one_mul]
  have e : (((modF (upIdele K E t)) ^ s : ℝ) : ℂ) = ((q ^ s : ℚ) : ℂ) := by rw [hq]; push_cast; rfl
  rw [e, map_ratCast, ← e]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hpos _), modF_upIdele, ← card_eq_finrank φ hφ h2,
    ← pow_mul, mul_comm]

theorem beta_eq_coordIn_pow (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ)
    (Ω T : ℂ) (Λ : PeriodPair) (h : Ω ^ 12 = latDisc Λ) : beta E d s κ Λ T = coordIn E d s κ Ω T ^ 12 := by
  rw [beta_eq, coordIn, div_pow, ← h, ← pow_mul, ← pow_mul, mul_comm 12]

theorem transportFor_of (hA : LatAlg) (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (hd : 0 < d)
    (δ : K) (hδ : δ ^ 2 = -(d : K)) (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair)
    (hΛ : IsLatOf φK 1 ΛK) (Ω₀ : ℂ) (hΩ₀ : Ω₀ ^ 12 = latDisc ΛK) (hΩ₀0 : Ω₀ ≠ 0)
    (t : (ℂ ≃+* ℂ) → (Af K)ˣ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : (ℂ ≃+* ℂ) → PeriodPair)
    (Ω : (ℂ ≃+* ℂ) → ℂ)
    (hT : ∀ σ, Fixes φK σ →
      TorsTransport φK σ (t σ) ΛK (Λ σ) Ω₀ (Ω σ) ∧ IsInvIdealOf (t σ) (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K))
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (hE : UnramFin E)
    (I : Type) [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = φK)
    (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (hs : 1 ≤ s) (h𝔣 : IsBaseCond 𝔣) :
    TransportFor d φK ΛK t 𝔞 Λ φ s κ 𝔣 := by
  have hC0 : (C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (cmValueConst_pos E hd (by omega) κ).ne'
  have conj : ∀ σ, Fixes φK σ → ∀ κ', IsConjWt φ σ κ κ' → ∀ Q χ T χ' T', IsValSum φ s κ 𝔣 Q χ T →
      IsConjSum φ s κ' 𝔣 Q σ χ χ' T' →
      σ (coordIn E d s κ Ω₀ T) = coordIn E d s κ (Ω σ) ((((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^
        (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') := by
    intro σ hσ κ' hκ' Q χ T χ' T' hV hV'
    rw [nrm_eq_modF _ _ (hT σ hσ).2]
    exact conj_coordIn_toric hC d δ φK h2 hd hδ σ (t σ) ΛK (Λ σ) Ω₀ (Ω σ) hΩ₀ (hT σ hσ).1 φ hE hφ hφK s hs
      κ κ' hκ' 𝔣 h𝔣 Q χ χ' T T' hV hV'
  refine ⟨fun Q χ T hV => ⟨?_, fun σ hσ κ' hκ' χ' T' hV' => ?_⟩,
    fun Q₁ Q₂ χ₁ χ₂ T₁ T₂ hV₁ hV₂ hT₂ => ⟨?_, fun σ hσ κ' hκ' χ₁' χ₂' T₁' T₂' hV₁' hV₂' => ?_⟩⟩
  · rw [beta_eq_coordIn_pow E d s κ Ω₀ T ΛK hΩ₀]
    exact (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q χ T hV).pow 12
  · have hD := (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).1
    set N := nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) with hN
    have hN0 : N ≠ 0 := nrm_ne_zero _
    have hNpos : 0 < N := lt_of_le_of_ne (by rw [hN, nrm]; exact_mod_cast FractionalIdeal.absNorm_nonneg _) hN0.symm
    have e : σ (beta E d s κ ΛK T) = beta E d s κ (Λ σ)
        ((((N : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') := by
      rw [beta_eq_coordIn_pow E d s κ Ω₀ T ΛK hΩ₀, map_pow, conj σ hσ κ' hκ' Q χ T χ' T' hV hV',
        beta_eq_coordIn_pow E d s κ (Ω σ) _ (Λ σ) hD]
    have hl := norm_lamF_conj_up h2 φ hE hφ s κ κ' 𝔣 h𝔣 Q hV.1 χ χ' hV.2.1 σ hV'.1 (t σ)
    rw [← nrm_eq_modF _ _ (hT σ hσ).2, ← hN] at hl
    refine ⟨by rw [e, beta_eq]; ring, ?_⟩
    rw [e, beta_eq, norm_div, norm_pow, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, hl, norm_pow, norm_pow,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hNpos,
      abs_of_pos (cmValueConst_pos E hd (by omega) κ)]
    have hDn : ‖latDisc (Λ σ)‖ ≠ 0 := norm_ne_zero_iff.2 (latDisc_ne_zero _)
    field_simp
    ring
  · rw [← coordIn_div E hd hs κ hΩ₀0 T₁ T₂, div_eq_mul_inv]
    exact (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q₁ χ₁ T₁ hV₁).mul
      (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q₂ χ₂ T₂ hV₂).inv
  · have hΩσ : Ω σ ≠ 0 := (hT σ hσ).1.2.1
    set m : ℂ := (((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (∑ i, κ i)) with hm
    have hm0 : m ≠ 0 := pow_ne_zero _ (by exact_mod_cast nrm_ne_zero _)
    have c1 := conj σ hσ κ' hκ' Q₁ χ₁ T₁ χ₁' T₁' hV₁ hV₁'
    have c2 := conj σ hσ κ' hκ' Q₂ χ₂ T₂ χ₂' T₂' hV₂ hV₂'
    have hc2 : coordIn E d s κ Ω₀ T₂ ≠ 0 := by
      rw [coordIn]; exact div_ne_zero (mul_ne_zero hC0 hT₂) (pow_ne_zero _ hΩ₀0)
    have hT2' : T₂' ≠ 0 := by
      rintro rfl
      have := (map_ne_zero σ).2 hc2
      rw [c2, mul_zero, coordIn, mul_zero, zero_div] at this
      exact this rfl
    refine ⟨hT2', ?_⟩
    rw [← coordIn_div E hd hs κ hΩ₀0 T₁ T₂, map_div₀, c1, c2, coordIn_div E hd hs κ hΩσ, mul_assoc, mul_assoc,
      mul_div_mul_left _ _ (inv_ne_zero hm0)]

theorem transport_of (hH : GlobalTheory.Published.HilbertClassFieldJ) (hA : LatAlg) (hC : LatConj) : Transport := by
  intro K _ _ d hd h2 hdisc φK ΛK hΛ
  have hTC : IsTotallyComplex K := isTotallyComplex_of_discr_neg h2 (by rw [hdisc]; omega)
  obtain ⟨δ, hδ⟩ := exists_sq_eq_neg K d h2 hdisc
  obtain ⟨Ω₀, hΩ₀⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc ΛK) (by norm_num : 0 < 12)
  have hΩ₀0 : Ω₀ ≠ 0 := by rintro rfl; exact latDisc_ne_zero ΛK (by rw [← hΩ₀]; norm_num)
  have key : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ (t : (Af K)ˣ) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : PeriodPair) (Ω : ℂ),
      TorsTransport φK σ t ΛK Λ Ω₀ Ω ∧ IsInvIdealOf t (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ∧
        IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λ := by
    intro σ hσ
    letI : Algebra K ℂ := φK.toAlgebra
    obtain ⟨X, hX, ξ, hξ, hTr⟩ := GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport h2 φK ΛK Ω₀ hΛ hΩ₀0
    haveI := hX
    let σK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := σ) hσ
    obtain ⟨t, ht⟩ := GlobalTheory.EllipticCM.exists_transports h2 σK one_ne_zero hξ
    obtain ⟨Λ₁, Ω₁, h1⟩ := hTr σK t ht
    obtain ⟨𝔞, h𝔞t, h𝔞Λ⟩ := h1.2.2.2.2.1
    have h𝔞0 : 𝔞 ≠ 0 := by
      rintro rfl
      have hm : Λ₁.ω₁ ∈ (Λ₁.lattice : Set ℂ) := PeriodPair.ω₁_mem_lattice Λ₁
      rw [h𝔞Λ] at hm
      obtain ⟨x, hx, hx'⟩ := hm
      have hx0 : x = 0 := by simpa using hx
      rw [hx0, map_zero] at hx'
      exact (by simpa using Λ₁.indep.ne_zero 0 : Λ₁.ω₁ ≠ 0) hx'.symm
    exact ⟨t, Units.mk0 𝔞 h𝔞0, Λ₁, Ω₁, h1, h𝔞t, h𝔞Λ⟩
  haveI : Nonempty PeriodPair := ⟨ΛK⟩
  choose! t 𝔞 Λ Ω hT using key
  refine ⟨t, 𝔞, Λ, fun σ hσ => ⟨(hT σ hσ).2.1, (hT σ hσ).2.2, (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).2⟩,
    equidistributed_of_j hH h2 φK ΛK hΛ 𝔞
      (fun σ hσ => ⟨Λ σ, (hT σ hσ).2.2, (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).2⟩), ?_⟩
  intro E _ _ _ _ _ hE I _ φ hcard hφ hφK s κ 𝔣 hs hκ h𝔣
  exact transportFor_of hA hC d (by omega) δ hδ h2 φK ΛK hΛ Ω₀ hΩ₀ hΩ₀0 t 𝔞 Λ Ω
    (fun σ hσ => ⟨(hT σ hσ).1, (hT σ hσ).2.1⟩) E hE I φ hφ hφK s κ 𝔣 hs h𝔣

end GlobalTheory.TransportProof
