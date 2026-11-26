module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSigmaCompactConeInter

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPair
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPair
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial

open GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial

theorem rootPolyNum : RootPolynomialNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x c G hG hc q L Q hQ a
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q :
      MvPolynomial (Fin (N + q)) ℤ).IsHomogeneous d := by
    have h3 := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show c + (d - c) = d by omega] at h3
  have hZ : ⇑(Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
      (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) = divCycle P (C a) := by
    funext W
    simp [FlagTypings.divCycle_eq]
  have hfin : (Function.support (divCycle P (C a))).Finite := by
    rw [← hZ]
    exact Finsupp.hasFiniteSupport _
  have hcast : Fin.append x L ∘ Fin.castAdd q = x := by
    funext i
    simp [Fin.append_left]
  have hnat : Fin.append x L ∘ Fin.natAdd N = L := by
    funext j
    simp [Fin.append_right]
  have key : ∀ W : Ideal (MRing ι O), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
      (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) (specialIdeal W) d (Fin.append x L)
      (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
      ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
    intro W
    rw [BundleExamples.polyNum_eq_classNum (Fin.append x L) (Equiv.refl _) (Fin.append x L) rfl hH W]
    simp only [Equiv.coe_refl, rename_id_apply]
    rw [plainPolynomialPairNumber.classNum_mul_tail _ L _ hnat]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [plainPairNumber.classNum_rename _ (Fin.castAdd_injective _ _), hcast]
  rw [BundleExamples.vEval_eq, hZ]
  simp only [key, cycEval_eq_sum hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
  ring

theorem main : ChernClassOnFlagPair.Statement :=
  ChernClassOnFlagPair.proof
    (JoinPointFlagModel.proof FlagPairCharacterisation.proof JoinPointModel.proof
      JoinPointVerticalDivisor.proof)
    (JoinPointNumbers.proof JoinPointIdeal.proof JoinDivCycle.proof JoinVariety.proof
      JoinIntNum.proof PairNumberJoinLeft.verticalComponentFibre)
    GlobalTheory.T.flag_model_value_independent GlobalTheory.T.flag_model_root_independent plainPolynomialPairNumber.proof rootPolyNum
    (PairNumberExpansionIndependence.proof GlobalTheory.T.vertical_divisors_commute) dividedDifferenceExpansion.proof

end GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPairStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_class_on_flag_pair : GroundTheory.Heights₂.Heights.NumbersDVR.ChernClassOnFlagPair.Statement := by
  first | exact @GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial.main | exact GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial.main | (intros; apply GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifference
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifference
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem ck_rootNum_eq_pairNum_on_flagPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d → fnField O (joinCoord x z) = fnField O x → ∀ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB → IsPull O x z E' E'B → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K ⊕ K' → ℤ) (f g : Fin N → MRing (Sum.elim ι ι') O), IsFlagPair ϖ (joinCoord x z) EB E'B w w' b b' f g → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ∑ μ ∈ Q.support, Q.coeff μ * pairNum (pointIdeal O (joinCoord x z)) b b' f g (psumExpansion N k) (classList (fun j => pullDeg (K' := K') (L j)) μ)) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O x d N E G L Q a = ∑ μ ∈ Q.support, Q.coeff μ * cycEval (fun W => classNum b G (classList (fun j => pullDeg (K' := K') (L j)) μ) W) (divCycle (pointIdeal O (joinCoord x z)) (C a))) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hW N V _ _ E E' hEE' K' _ _ ι' _ z hm hb EB E'B hp hp'
    w w' b b' f g hfp
  have hprime : (mcIdeal O x).IsPrime := hW.2.1.1
  obtain ⟨-, hB⟩ := (BundleExamples.isModelOver_iff O _ d).mp hm
  have hB' : IsModelOver (pointIdeal O (joinCoord x z)) d := hB
  haveI hprimeB : (pointIdeal O (joinCoord x z)).IsPrime := hm.2.1.1
  have hI := IntNumIsFieldIntersection.full (IsLocalRing.ResidueField O) (K ⊕ K') (Sum.elim ι ι')
  refine ⟨fun k hk1 hk2 q L Q hQ => ?_, fun c G hsym hG hc q L Q hQ a ha => ?_⟩
  · obtain ⟨φ, -, -, hd, hd', hf, hg⟩ :=
      ((FlagPairCharacterisation.proof O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) N V EB E'B ϖ hϖ
        hB'.multiProj).1 w w' b b' f g).mp hfp
    let F₀ : FlagModel O x d N E E' :=
      { K' := K', ι' := ι', z := z, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (FlagModel O x d N E E') := ⟨F₀⟩
    have hv : F₀.value O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
        (psum (Fin N) ℤ k) L L (fun _ => 1) (fun _ => 1) Q =
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          (pointIdeal O (joinCoord x z)) d
          (Fin.append b fun l => pullDeg (K' := K') (L l))
          (Fin.append b' fun l => pullDeg (K' := K') (L l))
          (Fin.append f fun _ => 1) (Fin.append g fun _ => 1)
          (rename (Fin.castAdd q) (psum (Fin N) ℤ k) * rename (Fin.natAdd N) Q) := by
      show GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O _ _ d (Fin.append φ.deg _)
        (Fin.append φ.deg' _) (Fin.append φ.f fun _ => rename (liftVar ι') (1 : MRing ι O))
        (Fin.append φ.g fun _ => rename (liftVar ι') (1 : MRing ι O)) _ = _
      rw [hd, hd', hf, hg, map_one]
      rfl
    unfold ck
    rw [dite_eq_left hne]
    refine (GlobalTheory.T.flag_model_value_independent O Ω K ι x d N V E E' hW hEE'
      (Classical.choice hne) F₀ _ _ (ChernClassOnFlagPair.fieldNum_spec _ _) hI (psum (Fin N) ℤ k)
      (psum_isSymmetric _ _ k) q L L (fun _ => 1) (fun _ => 1)
      (fun l => ChernClassOnFlagPair.isVertDiv_one hprime _ (sub_self _)) k Q hk2
      (isHomogeneous_psum N k) hQ).trans ?_
    refine hv.trans ((plainPolynomialPairNumber.proof O (K ⊕ K') (Sum.elim ι ι')
      (pointIdeal O (joinCoord x z)) d N b b' f g k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) hk2 q _ Q hQ).trans ?_)
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hlen : (classList (fun j => pullDeg (K' := K') (L j)) μ).length + k = d + 1 := by
      have h := hQ (mem_support_iff.mp hμ)
      rw [ChernClassOnFlagPair.length_classList, Finsupp.degree_eq_weight_one]
      have : Finsupp.weight (fun _ => 1) μ = Finsupp.weight 1 μ := rfl
      omega
    rw [PairNumberExpansionIndependence.proof GlobalTheory.T.vertical_divisors_commute O ϖ hϖ (K ⊕ K') (Sum.elim ι ι')
      (pointIdeal O (joinCoord x z)) d hB' N b b' f g hfp.vertical k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) _ (psumExpansion N k)
      (dividedDifferenceExpansion.proof N k _ (isHomogeneous_psum N k)) (isPairExpansion_psum N k)
      _ hlen]
  · have hsame : SameGeneric O x E E := fun s _ =>
      ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
        fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
    obtain ⟨φ, -, -, hd, -, -, -⟩ :=
      ((FlagPairCharacterisation.proof O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) N V EB EB ϖ hϖ
        hB'.multiProj).1 w w b b _ _).mp (ChernClassOnFlagPair.isFlagPair_self hfp.flag)
    let F₀ : FlagModel O x d N E E :=
      { K' := K', ι' := ι', z := z, model := hm, birat := hb, EB := EB, E'B := EB,
        pull := hp, pull' := hp, flag := φ }
    have hne : Nonempty (FlagModel O x d N E E) := ⟨F₀⟩
    unfold rootNum
    rw [dite_eq_left hne]
    refine (GlobalTheory.T.flag_model_root_independent O Ω K ι x d N V E E hW hsame
      (Classical.choice hne) F₀ _ _ (ChernClassOnFlagPair.fieldNum_spec _ _) hI c G hsym hG hc q L Q hQ a
      ha).trans ?_
    have h6 := RootPolynomialNumber.proof O (K ⊕ K') (Sum.elim ι ι') (pointIdeal O (joinCoord x z)) d N b
      c G hG hc q (fun j => pullDeg (K' := K') (L j)) Q hQ a
    rw [← hd] at h6 ⊢
    exact h6

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifferenceStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_generic_flag_difference : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d → fnField O (joinCoord x z) = fnField O x → ∀ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB → IsPull O x z E' E'B → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K ⊕ K' → ℤ) (f g : Fin N → MRing (Sum.elim ι ι') O), IsFlagPair ϖ (joinCoord x z) EB E'B w w' b b' f g → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ∑ μ ∈ Q.support, Q.coeff μ * pairNum (pointIdeal O (joinCoord x z)) b b' f g (psumExpansion N k) (classList (fun j => pullDeg (K' := K') (L j)) μ)) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O x d N E G L Q a = ∑ μ ∈ Q.support, Q.coeff μ * cycEval (fun W => classNum b G (classList (fun j => pullDeg (K' := K') (L j)) μ) W) (divCycle (pointIdeal O (joinCoord x z)) (C a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_eq_pairNum_on_flagPair | exact GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_eq_pairNum_on_flagPair | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_eq_pairNum_on_flagPair <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BallAverageFibreCount
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreCountRotationInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreCountRotationInvariant
set_option maxSynthPendingDepth 1

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv

noncomputable section

theorem measurePreserving_swapMat (m n : ℕ) :
    MeasurePreserving (fun (π : Fin m → Fin n → ℂ) (j : Fin n) (i : Fin m) => π i j)
      volume volume := by
  have h1 := (measurePreserving_curry_matrix m n).symm (MeasurableEquiv.curry (Fin m) (Fin n) ℂ)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : Fin n × Fin m => ℂ)
    (Equiv.prodComm (Fin m) (Fin n))
  have h3 := measurePreserving_curry_matrix n m
  have h4 := h3.comp (h2.comp h1)
  have h5 : (fun (π : Fin m → Fin n → ℂ) (j : Fin n) (i : Fin m) => π i j) =
      (MeasurableEquiv.curry (Fin n) (Fin m) ℂ) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin m => ℂ)
          (Equiv.prodComm (Fin m) (Fin n))) ∘
          (MeasurableEquiv.curry (Fin m) (Fin n) ℂ).symm := by
    funext π j i
    simp only [MeasurableEquiv.coe_curry_symm, MeasurableEquiv.curry, Function.comp]
    simp only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Function.curry_apply,
      MeasurableEquiv.coe_piCongrLeft]
    exact (Equiv.piCongrLeft_apply_apply (fun _ : Fin n × Fin m => ℂ)
      (Equiv.prodComm (Fin m) (Fin n)) (Function.uncurry π) (i, j)).symm
  rw [h5]
  exact h4

theorem transpose_mem_unitaryGroup' {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin m) ℂ) : Aᵀ ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.1 hA
  have h2 : (star A * A)ᵀ = 1 := by rw [h, Matrix.transpose_one]
  rw [Matrix.transpose_mul] at h2
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose, Matrix.transpose_map] using h2

def colAct {m n : ℕ} (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (π : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ :=
  fun i j => ∑ k, unitMat V i k * π k j

theorem colAct_eq_mul {m n : ℕ} (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (π : Fin m → Fin n → ℂ) :
    colAct V π = (unitMat V * (Matrix.of π : Matrix (Fin m) (Fin n) ℂ)) := by
  funext i j
  simp [colAct, Matrix.mul_apply]

theorem colAct_symm_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ) :
    colAct V.symm (colAct V π) = π := by
  have h : unitMat V.symm * unitMat V = 1 := by simpa using unitMat_mul_symm V.symm
  rw [colAct_eq_mul, colAct_eq_mul]
  show unitMat V.symm * (unitMat V * Matrix.of π) = π
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  rfl

theorem colAct_eq_swap {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ) :
    colAct V π = fun i j => ((fun k => π k j) ᵥ* (unitMat V)ᵀ) i := by
  funext i j
  simp [colAct, Matrix.vecMul, dotProduct, mul_comm]

theorem measurePreserving_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    MeasurePreserving (colAct (n := n) V) volume volume := by
  have h1 : MeasurePreserving (fun (ρ : Fin n → Fin m → ℂ) (j : Fin n) => ρ j ᵥ* (unitMat V)ᵀ)
      volume volume :=
    volume_preserving_pi fun _ =>
      measurePreserving_vecMul (transpose_mem_unitaryGroup' (unitMat_mem V))
  have h2 := (measurePreserving_swapMat n m).comp (h1.comp (measurePreserving_swapMat m n))
  convert h2 using 1
  funext π
  rw [colAct_eq_swap]
  rfl

def colActEquiv {m n : ℕ} (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    (Fin m → Fin n → ℂ) ≃ᵐ (Fin m → Fin n → ℂ) where
  toFun := colAct V
  invFun := colAct V.symm
  left_inv := colAct_symm_colAct V
  right_inv π := by simpa using colAct_symm_colAct V.symm π
  measurable_toFun := (measurePreserving_colAct V).measurable
  measurable_invFun := (measurePreserving_colAct V.symm).measurable

theorem matGauss_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ) :
    matGauss (colAct V π) = matGauss π := by
  simp only [matGauss]
  congr 3
  rw [colAct_eq_swap, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact sum_norm_sq_vecMul (transpose_mem_unitaryGroup' (unitMat_mem V)) (fun k => π k j)

theorem linProj_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : linProj (colAct V π) y = V (linProj π y) := by
  ext i
  rw [unitary_apply_eq_sum]
  simp only [linProj, colAct]
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem linProj_smul {m n : ℕ} (π : Fin m → Fin n → ℂ) (c : ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : linProj π (c • y) = c • linProj π y := by
  ext i
  simp only [linProj, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cntOver_colAct {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsScaleStable S)
    {w : EuclideanSpace ℂ (Fin (e + 1))} (hw : w ≠ 0)
    (V : EuclideanSpace ℂ (Fin (e + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (e + 1)))
    (hV : V w = ((‖w‖ : ℝ) : ℂ) • firstCoordVec (e + 1)) (π : Fin (e + 1) → Fin n → ℂ) :
    cntOver S (colAct V π) (firstCoordVec (e + 1)) = cntOver S π w := by
  set c : ℂ := ((‖w‖ : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact_mod_cast norm_ne_zero_iff.2 hw
  have himg : ptsOver S (colAct V π) (firstCoordVec (e + 1)) =
      (fun y => c⁻¹ • y) '' ptsOver S π w := by
    ext z
    constructor
    · rintro ⟨hzS, hz⟩
      refine ⟨c • z, ⟨hS z hzS c hc0, ?_⟩, by simp [smul_smul, hc0]⟩
      apply V.injective
      rw [linProj_smul, map_smul, ← linProj_colAct, hz, hV]
    · rintro ⟨y, ⟨hyS, hy⟩, rfl⟩
      refine ⟨hS y hyS _ (inv_ne_zero hc0), ?_⟩
      rw [linProj_smul, linProj_colAct, hy, hV, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hinj : Set.InjOn (fun y : EuclideanSpace ℂ (Fin n) => c⁻¹ • y) (ptsOver S π w) :=
    (MulAction.injective₀ (inv_ne_zero hc0)).injOn
  simp only [cntOver]
  rw [himg, hinj.encard_image]

theorem lintegral_matGauss_cntOver :
    ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S →
      ∀ (w : EuclideanSpace ℂ (Fin (e + 1))), w ≠ 0 → ∀ T : ℝ≥0∞ → ℝ≥0∞,
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π w) =
          ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  intro n e S hS w hw T
  obtain ⟨U, -, -, hU⟩ := exists_unitary_leadCoordPlane (n := e + 1) (m := e + 1) (by omega) le_rfl
    ⊤ (by simp) w trivial
  have hV : U.symm w = ((‖w‖ : ℝ) : ℂ) • firstCoordVec (e + 1) := by
    rw [U.symm_apply_eq, hU]
  have hemb : MeasurableEmbedding (colAct (n := n) U.symm) :=
    (colActEquiv U.symm).measurableEmbedding
  have key := (measurePreserving_colAct (n := n) U.symm).lintegral_comp_emb hemb
    (fun π => matGauss π * T (cntOver S π (firstCoordVec (e + 1))))
  refine Eq.trans ?_ key
  refine lintegral_congr fun π => ?_
  simp only [matGauss_colAct, cntOver_colAct hS hw U.symm hV]

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreCountRotationInvariantStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_count_rotation_invariant : ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S →
  ∀ (w : EuclideanSpace ℂ (Fin (e + 1))), w ≠ 0 → ∀ T : ℝ≥0∞ → ℝ≥0∞,
    ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π w) =
      ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv.lintegral_matGauss_cntOver | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv.lintegral_matGauss_cntOver | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv.lintegral_matGauss_cntOver <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TXgzChowMahlerE0reduce
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

theorem PositivityTheory.Xgn.t_xgz_chow_mahler_e0reduce : ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S → IsSigmaCompact S →
  ∀ T : ℝ≥0∞ → ℝ≥0∞, Measurable T →
    ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1), T (cntOver S π w) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  intro n e S hS hσ T hT
  have hG : Measurable fun π : Fin (e + 1) → Fin n → ℂ => matGauss π := by
    unfold matGauss
    exact (by fun_prop : Continuous fun π : Fin (e + 1) → Fin n → ℂ =>
      Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2)).measurable.ennreal_ofReal
  have hC : Measurable (fun p : (Fin (e + 1) → Fin n → ℂ) × EuclideanSpace ℂ (Fin (e + 1)) =>
      T (cntOver S p.1 p.2)) := hT.comp (GlobalTheory.T.measurable_fibre_count_over n (e + 1) S hσ)
  have hF : Measurable (Function.uncurry fun (π : Fin (e + 1) → Fin n → ℂ)
      (w : EuclideanSpace ℂ (Fin (e + 1))) => matGauss π * T (cntOver S π w)) :=
    (hG.comp measurable_fst).mul hC
  have h1 : ∀ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1), T (cntOver S π w) =
      ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1),
        matGauss π * T (cntOver S π w) := by
    intro π
    rw [lintegral_const_mul' _ _ (by unfold matGauss; exact ENNReal.ofReal_ne_top)]
  have h0 : ∀ᵐ w : EuclideanSpace ℂ (Fin (e + 1)), w ≠ 0 := by
    rw [ae_iff]
    simp
  simp_rw [h1]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  rw [lintegral_congr_ae ((ae_restrict_of_ae h0).mono fun w hw => GlobalTheory.T.fibre_count_rotation_invariant n e S hS w hw T),
    setLIntegral_const, mul_comm]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BallAverageFibreCount
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.ball_average_fibre_count : ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S → IsSigmaCompact S →
  ∀ T : ℝ≥0∞ → ℝ≥0∞, Measurable T →
    ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1), T (cntOver S π w) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  first | exact @PositivityTheory.Xgn.t_xgz_chow_mahler_e0reduce | exact PositivityTheory.Xgn.t_xgz_chow_mahler_e0reduce
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BallAverageFibreCountStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_average_fibre_count : ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S → IsSigmaCompact S →
  ∀ T : ℝ≥0∞ → ℝ≥0∞, Measurable T →
    ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1), T (cntOver S π w) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ball_average_fibre_count | exact GlobalTheory.CompanionTheory.Relay.ball_average_fibre_count | (intros; apply GlobalTheory.CompanionTheory.Relay.ball_average_fibre_count <;> assumption)
end
end
