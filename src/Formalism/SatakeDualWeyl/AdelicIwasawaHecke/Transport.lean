module

public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Transport
noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

theorem transport_cT_map {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (σ' : B →+* B)
    (φ : A →+* B) (h : φ.comp σ = σ'.comp φ) {m p : Type} (M : Matrix m p A) :
    cT σ' (M.map φ) = (cT σ M).map φ := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  exact (RingHom.congr_fun h (M j i)).symm

theorem transport_bc_mem {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n]
    [DecidableEq n] (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ)
    (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' (J.map φ) := by
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((g : Matrix n n A).map φ) * J.map φ * (g : Matrix n n A).map φ = J.map φ
  rw [transport_cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem transport_symm_comp {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (σ' : B →+* B)
    (φ : A ≃+* B) (h : (φ : A →+* B).comp σ = σ'.comp φ) :
    (φ.symm : B →+* A).comp σ' = σ.comp φ.symm := by
  ext x
  have h1 := RingHom.congr_fun h (φ.symm x)
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h1 ⊢
  rw [← h1, RingEquiv.symm_apply_apply]

theorem unitary_group_transport : Formalism.UG.UJTransport := by
  intro A B _ _ n _ _ σ σ' φ h J
  have hs := transport_symm_comp σ σ' φ h
  refine ⟨{ toFun := fun g => ⟨bc (φ : A →+* B) g, transport_bc_mem σ σ' φ h J g g.2⟩
            invFun := fun g => ⟨bc (φ.symm : B →+* A) g, by
              have hm := transport_bc_mem σ' σ (φ.symm : B →+* A) hs (J.map φ) g g.2
              have hJ : (J.map φ).map (φ.symm : B →+* A) = J := by ext i j; simp
              rwa [hJ] at hm⟩
            left_inv := fun g => by
              apply Subtype.ext; apply Units.ext; ext i j; simp [bc]
            right_inv := fun g => by
              apply Subtype.ext; apply Units.ext; ext i j; simp [bc]
            map_mul' := fun a b => by
              apply Subtype.ext; simp }, fun g => rfl⟩

theorem split_group_points : Formalism.UG.SplitPts := by
  intro F E _ _ _ n _ _ σ J R _ _ φ hφ
  have hc : (φ : E ⊗[F] R →+* R × R).comp (sigR σ R) = (swapR R).comp φ := RingHom.ext hφ
  obtain ⟨e, he⟩ := unitary_group_transport (E ⊗[F] R) (R × R) n (sigR σ R) (swapR R) φ hc
    (J.map (inclE (F := F) R))
  exact ⟨e, he⟩

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Upqcpt
noncomputable section

open Matrix

namespace Formalism.UG.P

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cT_conj_eq_star (M : Matrix n n ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = star M := by
  unfold Formalism.UG.cT
  ext i j
  simp [Matrix.star_apply, Matrix.transpose_apply, Matrix.map_apply]

theorem isCompact_of_unitary {T : Set (Matrix n n ℂ)} (hT : IsClosed T)
    (hU : ∀ M ∈ T, star M * M = 1) : IsCompact T := by
  have hsub : T ⊆ (Set.pi Set.univ (fun _ : n => Set.pi Set.univ
      (fun _ : n => Metric.closedBall (0 : ℂ) 1)) : Set (Matrix n n ℂ)) := by
    intro M hM i _ j _
    have h := congrFun (congrFun (hU M hM) j) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
    have key : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
      intro z
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    simp only [key] at h
    rw [← Complex.ofReal_sum, ← Complex.ofReal_one, Complex.ofReal_inj] at h
    have hle : Complex.normSq (M i j) ≤ 1 := by
      rw [← h]
      exact Finset.single_le_sum (f := fun x => Complex.normSq (M x j))
        (fun x _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    rw [Metric.mem_closedBall, dist_zero_right]
    have h2 : ‖M i j‖ ^ 2 ≤ 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact hle
    nlinarith [norm_nonneg (M i j)]
  have hK : IsCompact (Set.pi Set.univ (fun _ : n => Set.pi Set.univ
      (fun _ : n => Metric.closedBall (0 : ℂ) 1)) : Set (Matrix n n ℂ)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 1))
  exact hK.of_isClosed_subset hT hsub

private theorem mul_star_eq_one_of_star_mul_eq_one {M : Matrix n n ℂ} (h : star M * M = 1) : M * star M = 1 := by
  exact mul_eq_one_comm.mp h

theorem isCompact_units_of_unitary {T : Set (Matrix n n ℂ)} (hT : IsClosed T)
    (hU : ∀ M ∈ T, star M * M = 1) :
    IsCompact {g : GL n ℂ | (g : Matrix n n ℂ) ∈ T} := by
  have hK : IsCompact T := isCompact_of_unitary hT hU
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp hK
  let f : T → GL n ℂ := fun M =>
    ⟨M.1, star M.1, mul_star_eq_one_of_star_mul_eq_one (hU M.1 M.2), hU M.1 M.2⟩
  have hf : Continuous f := by
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  have hS : {g : GL n ℂ | (g : Matrix n n ℂ) ∈ T} = Set.range f := by
    ext g
    constructor
    · intro hg
      exact ⟨⟨g, hg⟩, Units.ext rfl⟩
    · rintro ⟨M, rfl⟩
      exact M.2
  rw [hS]
  exact isCompact_range hf

theorem mem_Upq_iff (p q : ℕ) (g : GL (Fin p ⊕ Fin q) ℂ) :
    g ∈ Formalism.UG.Upq p q ↔
      star (g : Matrix _ _ ℂ) * Formalism.UG.Jpq p q * (g : Matrix _ _ ℂ) = Formalism.UG.Jpq p q := by
  unfold Formalism.UG.Upq UJ
  simp [cT_conj_eq_star]; done

theorem Jpq_zero (p : ℕ) : Formalism.UG.Jpq p 0 = 1 := by
  unfold Formalism.UG.Jpq
  rw [← Matrix.fromBlocks_one]
  congr 1
  ext i j
  exact i.elim0

theorem indefinite_unitary_compact : Formalism.UG.UpqCompact := by
  intro p
  have hT : IsClosed {M : Matrix (Fin p ⊕ Fin 0) (Fin p ⊕ Fin 0) ℂ | star M * M = 1} :=
    isClosed_eq (continuous_star.mul continuous_id) continuous_const
  have h := isCompact_units_of_unitary hT (fun M hM => hM)
  convert h using 1
  ext g
  simp only [SetLike.mem_coe, mem_Upq_iff, Jpq_zero, mul_one, Set.mem_setOf_eq]

theorem Jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  unfold Formalism.UG.Jpq
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases h : i = j <;> simp [h, Matrix.one_apply, Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply]
  · by_cases h : i = j <;> simp [h, Matrix.one_apply, Matrix.diagonal_apply]

theorem Jpq_mul_self (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  rw [Jpq_eq_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  rcases i with i | i <;> simp

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SplitUnitaryGroupIso
noncomputable section

open Matrix

namespace Formalism.UG.P

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem split_mat_ext {M N : Matrix n n (R × R)} (h1 : M.map Prod.fst = N.map Prod.fst)
    (h2 : M.map Prod.snd = N.map Prod.snd) : M = N := by
  ext i j
  · simpa using congrFun (congrFun h1 i) j
  · simpa using congrFun (congrFun h2 i) j

theorem split_map_fst_mul (M N : Matrix n n (R × R)) :
    (M * N).map Prod.fst = M.map Prod.fst * N.map Prod.fst := by
  ext i j
  simp [Matrix.mul_apply, Prod.fst_sum]

theorem split_map_snd_mul (M N : Matrix n n (R × R)) :
    (M * N).map Prod.snd = M.map Prod.snd * N.map Prod.snd := by
  ext i j
  simp [Matrix.mul_apply, Prod.snd_sum]

theorem split_cT_fst (g : Matrix n n (R × R)) :
    (cT (swapR R) g).map Prod.fst = (g.map Prod.snd)ᵀ := by
  ext i j
  simp [cT, swapR, Matrix.map_apply, Matrix.transpose_apply]

theorem split_cT_snd (g : Matrix n n (R × R)) :
    (cT (swapR R) g).map Prod.snd = (g.map Prod.fst)ᵀ := by
  ext i j
  simp [cT, swapR, Matrix.map_apply, Matrix.transpose_apply]

theorem splitJ_fst (J₁ : Matrix n n R) : (splitJ J₁).map Prod.fst = J₁ := by
  ext i j
  simp [splitJ, Matrix.map_apply]

theorem splitJ_snd (J₁ : Matrix n n R) : (splitJ J₁).map Prod.snd = J₁ᵀ := by
  ext i j
  simp [splitJ, Matrix.map_apply, Matrix.transpose_apply]

theorem split_mem_iff (J₁ : Matrix n n R) (g : GL n (R × R)) :
    g ∈ Formalism.UG.UJ (swapR R) (splitJ J₁) ↔
      ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * (g : Matrix n n (R × R)).map Prod.fst
        = J₁ := by
  constructor
  · intro h
    have h' := congrArg (fun M : Matrix n n (R × R) => M.map Prod.fst)
      (show cT (swapR R) (g : Matrix n n (R × R)) * splitJ J₁ * (g : Matrix n n (R × R)) = splitJ J₁ from h)
    simpa only [split_map_fst_mul, split_cT_fst, splitJ_fst] using h'
  · intro h
    show cT (swapR R) (g : Matrix n n (R × R)) * splitJ J₁ * (g : Matrix n n (R × R)) = splitJ J₁
    apply split_mat_ext
    · rw [split_map_fst_mul, split_map_fst_mul, split_cT_fst, splitJ_fst, h]
    · rw [split_map_snd_mul, split_map_snd_mul, split_cT_snd, splitJ_snd]
      have h' := congrArg Matrix.transpose h
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at h'
      rw [← Matrix.mul_assoc] at h'
      exact h'

theorem split_conj_mul (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) {P Q : Matrix n n R}
    (hPQ : P * Q = 1) : (J₁ * P * J₁⁻¹) * (J₁ * Q * J₁⁻¹) = 1 := by
  have h1 : J₁⁻¹ * J₁ = 1 := Matrix.nonsing_inv_mul _ hJ
  have h2 : J₁ * J₁⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJ
  calc (J₁ * P * J₁⁻¹) * (J₁ * Q * J₁⁻¹) = J₁ * (P * (J₁⁻¹ * J₁) * Q) * J₁⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, hPQ, Matrix.mul_one, h2]

def pairMat (X Y : Matrix n n R) : Matrix n n (R × R) := fun i j => (X i j, Y i j)

theorem pairMat_fst (X Y : Matrix n n R) : (pairMat X Y).map Prod.fst = X := by
  ext i j
  rfl

theorem pairMat_snd (X Y : Matrix n n R) : (pairMat X Y).map Prod.snd = Y := by
  ext i j
  rfl

theorem pairMat_mul_eq_one {X Y X' Y' : Matrix n n R} (h1 : X * X' = 1) (h2 : Y * Y' = 1) :
    pairMat X Y * pairMat X' Y' = 1 := by
  apply split_mat_ext
  · rw [split_map_fst_mul, pairMat_fst, pairMat_fst, h1]
    exact (Matrix.map_one _ rfl rfl).symm
  · rw [split_map_snd_mul, pairMat_snd, pairMat_snd, h2]
    exact (Matrix.map_one _ rfl rfl).symm

theorem split_injective (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (g g' : GL n (R × R))
    (hg : g ∈ Formalism.UG.UJ (swapR R) (splitJ J₁)) (hg' : g' ∈ Formalism.UG.UJ (swapR R) (splitJ J₁))
    (h : (g : Matrix n n (R × R)).map Prod.fst = (g' : Matrix n n (R × R)).map Prod.fst) :
    g = g' := by
  have hF : (g : Matrix n n (R × R)).map Prod.fst * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst = 1 := by
    rw [← split_map_fst_mul, Units.mul_inv]
    exact Matrix.map_one _ rfl rfl
  have e1 := (split_mem_iff J₁ g).mp hg
  have e2 := (split_mem_iff J₁ g').mp hg'
  rw [← h] at e2
  have k1 : ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ =
      J₁ * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst := by
    calc ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁
        = ((g : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * ((g : Matrix n n (R × R)).map Prod.fst *
            ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst) := by rw [hF, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e1]
  have k2 : ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ =
      J₁ * ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst := by
    calc ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁
        = ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ * J₁ * ((g : Matrix n n (R × R)).map Prod.fst *
            ((g⁻¹ : GL n (R × R)) : Matrix n n (R × R)).map Prod.fst) := by rw [hF, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e2]
  have k3 : ((g : Matrix n n (R × R)).map Prod.snd)ᵀ = ((g' : Matrix n n (R × R)).map Prod.snd)ᵀ := by
    have h3 := congrArg (fun M : Matrix n n R => M * J₁⁻¹) (k1.trans k2.symm)
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one] using h3
  have k4 := congrArg Matrix.transpose k3
  rw [Matrix.transpose_transpose, Matrix.transpose_transpose] at k4
  exact Units.ext (split_mat_ext h k4)

theorem split_surjective (J₁ : Matrix n n R) (hJ : IsUnit J₁.det) (h : GL n R) :
    ∃ g : GL n (R × R), g ∈ Formalism.UG.UJ (swapR R) (splitJ J₁) ∧ bc (RingHom.fst R R) g = h := by
  have hS : (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ * (J₁ * (h : Matrix n n R) * J₁⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, split_conj_mul J₁ hJ (Units.mul_inv h), Matrix.transpose_one]
  have hSi : (J₁ * (h : Matrix n n R) * J₁⁻¹)ᵀ * (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, split_conj_mul J₁ hJ (Units.inv_mul h), Matrix.transpose_one]
  refine ⟨⟨pairMat (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ,
    pairMat ((h⁻¹ : GL n R) : Matrix n n R) (J₁ * (h : Matrix n n R) * J₁⁻¹)ᵀ,
    pairMat_mul_eq_one (Units.mul_inv h) hS, pairMat_mul_eq_one (Units.inv_mul h) hSi⟩, ?_, ?_⟩
  · apply (split_mem_iff J₁ _).mpr
    show ((pairMat (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ).map Prod.snd)ᵀ * J₁ *
      (pairMat (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ).map Prod.fst = J₁
    rw [pairMat_snd, pairMat_fst, Matrix.transpose_transpose]
    calc J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹ * J₁ * (h : Matrix n n R)
        = J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * (J₁⁻¹ * J₁) * (h : Matrix n n R) := by
          simp only [Matrix.mul_assoc]
      _ = J₁ := by
          rw [Matrix.nonsing_inv_mul _ hJ, Matrix.mul_one, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  · exact Units.ext (pairMat_fst (h : Matrix n n R) (J₁ * ((h⁻¹ : GL n R) : Matrix n n R) * J₁⁻¹)ᵀ)

theorem split_unitary_group_iso : Formalism.UG.SplitIso := by
  intro R _ n _ _ J₁ hJ
  refine ⟨MulEquiv.ofBijective ((bc (RingHom.fst R R)).comp (Formalism.UG.UJ (swapR R) (splitJ J₁)).subtype) ⟨?_, ?_⟩,
    fun g => rfl⟩
  · intro a b hab
    apply Subtype.ext
    apply split_injective J₁ hJ a b a.2 b.2
    exact congrArg (fun u : GL n R => (u : Matrix n n R)) hab
  · intro h
    obtain ⟨g, hg, he⟩ := split_surjective J₁ hJ h
    exact ⟨⟨g, hg⟩, he⟩

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AssocFin
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G] (K : Subgroup G)

private lemma smul_quotient_mk (g x : G) : (g • (x : G ⧸ K)) = ((g * x : G) : G ⧸ K) := rfl

private lemma subgroup_smul_quotient_mk (k : K) (x : G) : (k • (x : G ⧸ K)) = (((k : G) * x : G) : G ⧸ K) := rfl

theorem stabilizer_coset_eq (s : G) :
    MulAction.stabilizer K ((s : G ⧸ K)) = (K.map (MulAut.conj s).toMonoidHom).subgroupOf K := by
  ext k
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_map, subgroup_smul_quotient_mk,
    QuotientGroup.eq]
  constructor
  · intro hk
    refine ⟨s⁻¹ * k * s, ?_, ?_⟩
    · have := K.inv_mem hk
      simpa [mul_assoc] using this
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨t, ht, hts⟩
    rw [← hts]
    simpa [MulAut.conj_apply, mul_assoc] using K.inv_mem ht

theorem orbit_coset_finite (hK : IsCommensurated K) (s : G) :
    (MulAction.orbit K ((s : G ⧸ K))).Finite := by
  unfold IsCommensurated at hK
  let H := (K.map (MulAut.conj s).toMonoidHom).subgroupOf K
  haveI : H.FiniteIndex := ⟨hK s⟩
  haveI : Finite (K ⧸ MulAction.stabilizer K ((s : G ⧸ K))) := by
    rw [stabilizer_coset_eq K s]
    exact Subgroup.finite_quotient_of_finiteIndex
  exact Set.finite_coe_iff.mp ((MulAction.orbitEquivQuotientStabilizer K _).finite_iff.mpr this)

theorem finite_supp_translate (hK : IsCommensurated K) {k : Type} [Zero k] (f : G → k)
    (hf : FinDosetSupp K f) (h : G) :
    {x : G ⧸ K | f (h * x.out) ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ =>
    (orbit_coset_finite K hK s).image (fun y : G ⧸ K => h⁻¹ • y)).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hx
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨a • ((s : G ⧸ K)), ⟨a, rfl⟩, ?_⟩
  simp only [smul_quotient_mk, subgroup_smul_quotient_mk]
  rw [← QuotientGroup.out_eq' x, QuotientGroup.eq]
  have hx' : x.out = h⁻¹ * ((a : G) * s * b) := by rw [← hab]; group
  rw [hx']
  convert b.2 using 1
  group

theorem finite_supp_inv (hK : IsCommensurated K) {k : Type} [Zero k] (f : G → k)
    (hf : FinDosetSupp K f) (g : G) :
    {y : G ⧸ K | f (y.out⁻¹ * g) ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ =>
    (orbit_coset_finite K hK s⁻¹).image (fun y : G ⧸ K => g • y)).subset ?_
  intro y hy
  obtain ⟨s, hs, a, b, hab⟩ := hS _ hy
  refine Set.mem_biUnion (Finset.mem_coe.2 hs) ⟨b⁻¹ • (((s⁻¹ : G)) : G ⧸ K), ⟨b⁻¹, rfl⟩, ?_⟩
  simp only [smul_quotient_mk, subgroup_smul_quotient_mk, Subgroup.coe_inv]
  rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
  have hy' : y.out = g * ((a : G) * s * b)⁻¹ := by rw [← hab]; group
  rw [hy']
  convert K.inv_mem a.2 using 1
  group

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckebasic
noncomputable section

open Classical

namespace Formalism.UG.P

open Formalism.UG

section Generic

variable {G : Type} [Group G]

theorem mem_dc_iff (K : Subgroup G) (g x : G) :
    x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) ↔
      ∃ a : K, ∃ b : K, x = (a : G) * g * b := by
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, a.2, b, b.2, rfl⟩

theorem mem_dc_one (K : Subgroup G) (x : G) :
    x ∈ DoubleCoset.doubleCoset (1 : G) (K : Set G) (K : Set G) ↔ x ∈ K := by
  rw [mem_dc_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    rw [mul_one]
    exact K.mul_mem a.2 b.2
  · intro hx
    exact ⟨⟨x, hx⟩, 1, by simp⟩

theorem ind_biInv (k : Type) [CommRing k] (K : Subgroup G) (T : Set G)
    (hT : ∀ a b : K, ∀ x : G, x ∈ T → (a : G) * x * b ∈ T) :
    IsBiInv K (T.indicator (1 : G → k)) := by
  unfold IsBiInv
  intro a b x
  by_cases hx : x ∈ T
  · simp [Set.indicator_apply, hx, hT a b x hx]
  · have h' : (a : G) * x * b ∉ T := by
      intro h
      apply hx
      have := hT a⁻¹ b⁻¹ _ h
      simpa [mul_assoc] using this
    simp [Set.indicator_apply, hx, h']

theorem dc_stable (K : Subgroup G) (g : G) (a b : K) (x : G)
    (hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) :
    (a : G) * x * b ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := by
  rw [mem_dc_iff] at hx ⊢
  obtain ⟨c, d, rfl⟩ := hx
  exact ⟨a * c, d * b, by simp [mul_assoc]⟩

theorem mem_hecke_iff (k : Type) [CommRing k] (K : Subgroup G) (f : G → k) :
    f ∈ Hecke k K ↔ IsBiInv K f ∧ FinDosetSupp K f := Iff.rfl

theorem dosetInd_of_mem (k : Type) [CommRing k] (K : Subgroup G) (g x : G)
    (hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) : dosetInd k K g x = 1 := by
  simp [dosetInd, hx]

theorem dosetInd_of_not_mem (k : Type) [CommRing k] (K : Subgroup G) (g x : G)
    (hx : x ∉ DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) : dosetInd k K g x = 0 := by
  simp [dosetInd, hx]

end Generic

theorem double_coset_indicator_mem : Formalism.UG.DosetIndMem := by
  unfold Formalism.UG.DosetIndMem
  intro G _ K k _ g
  rw [mem_hecke_iff]
  refine ⟨ind_biInv k K _ (fun a b x hx => dc_stable K g a b x hx), ?_⟩
  refine ⟨{g}, fun x hx => ⟨g, Finset.mem_singleton_self g, (mem_dc_iff K g x).1 ?_⟩⟩
  by_contra h
  exact hx (dosetInd_of_not_mem k K g x h)

section Basis

variable {G : Type} [Group G]

end Basis

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Ipindep
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

theorem mem_stabAt_mul_iff (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) (δ : Γ) :
    δ ∈ stabAt Γ K ((γ : G) * g * κ) ↔ γ⁻¹ * δ * γ ∈ stabAt Γ K g := by
  simp only [stabAt, Set.mem_ofPred_eq]
  have e : ((γ : G) * g * κ)⁻¹ * (δ : G) * ((γ : G) * g * κ) =
      (κ : G)⁻¹ * (g⁻¹ * ((γ⁻¹ * δ * γ : Γ) : G) * g) * κ := by
    push_cast; group
  rw [e, K.mul_mem_cancel_right κ.2, K.mul_mem_cancel_left (K.inv_mem κ.2)]

theorem card_stabAt_mul (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) :
    Nat.card (stabAt Γ K ((γ : G) * g * κ)) = Nat.card (stabAt Γ K g) := by
  refine Nat.card_congr
    { toFun := fun δ => ⟨γ⁻¹ * δ.1 * γ, (mem_stabAt_mul_iff Γ K g γ κ δ.1).1 δ.2⟩
      invFun := fun δ => ⟨γ * δ.1 * γ⁻¹, (mem_stabAt_mul_iff Γ K g γ κ _).2 (by
        convert δ.2 using 2; group)⟩
      left_inv := fun δ => Subtype.ext (by group)
      right_inv := fun δ => Subtype.ext (by group) }

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

abbrev conjInter (K : Subgroup G) (s : G) : Subgroup K :=
  (K.map (MulAut.conj s).toMonoidHom).subgroupOf K

theorem finite_quot_conjInter {K : Subgroup G} (hK : IsCommensurated K) (s : G) :
    Finite (K ⧸ conjInter K s) := by
  unfold IsCommensurated at hK
  haveI : (conjInter K s).FiniteIndex := ⟨hK s⟩
  exact Subgroup.finite_quotient_of_finiteIndex

theorem mul_eq_out_mul (K : Subgroup G) (s : G) (k : K) :
    ∃ k' : K, (k : G) * s =
      (((QuotientGroup.mk k : K ⧸ conjInter K s).out : K) : G) * s * k' := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (conjInter K s) k
  have hmem : ((h⁻¹ : conjInter K s) : K) ∈ conjInter K s := (h⁻¹).2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hmem
  obtain ⟨m, hmK, hm⟩ := hmem
  refine ⟨⟨m, hmK⟩, ?_⟩
  rw [hh]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, InvMemClass.coe_inv] at hm
  have hm' : s * m = ((h : K) : G)⁻¹ * s := by
    rw [← hm]; group
  simp only [Subgroup.coe_mul]
  rw [mul_assoc _ s, hm']
  group

theorem finite_cosets_in_doset {K : Subgroup G} (hK : IsCommensurated K) (s : G) :
    {x : G ⧸ K | ∃ a b : K, x.out = (a : G) * s * b}.Finite := by
  haveI := finite_quot_conjInter hK s
  refine (Set.finite_range
    (fun y : K ⧸ conjInter K s => ((((y.out : K) : G) * s : G) : G ⧸ K))).subset ?_
  rintro x ⟨a, b, hx⟩
  obtain ⟨k', hk'⟩ := mul_eq_out_mul K s a
  refine ⟨QuotientGroup.mk a, ?_⟩
  dsimp only
  have hxx : (QuotientGroup.mk x.out : G ⧸ K) = x := Quotient.out_eq x
  rw [← hxx, hx, hk', QuotientGroup.eq]
  have e : ((((QuotientGroup.mk a : K ⧸ conjInter K s).out : K) : G) * s)⁻¹ *
      ((((QuotientGroup.mk a : K ⧸ conjInter K s).out : K) : G) * s * k' * b) = k' * b := by
    group
  rw [e]
  exact K.mul_mem k'.2 b.2

theorem finite_support_cosets {k : Type} [Zero k] {K : Subgroup G} (hK : IsCommensurated K)
    {f : G → k} (hf : FinDosetSupp K f) :
    {x : G ⧸ K | f x.out ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ => finite_cosets_in_doset hK s).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, h⟩ := hS _ hx
  exact Set.mem_biUnion hs ⟨a, b, h⟩

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LinSubstIsHomogeneous
noncomputable section

open MvPolynomial

namespace Formalism.UG.P

variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]

theorem linSubst_isHomogeneous (M : Matrix n n O) {k : ℕ} {P : MvPolynomial n O}
    (hP : P.IsHomogeneous k) : (linSubst O n M P).IsHomogeneous k := by
  have h := hP.aeval (fun i => ∑ j, C (M i j) * X j) (n := 1)
    (fun i => IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _))
  simpa [linSubst] using h

theorem nabla_subspace_stable : Formalism.UG.NablaStable := by
  intro O _ n _ _ k g P hP
  rw [nabla, mem_homogeneousSubmodule] at hP ⊢
  exact linSubst_isHomogeneous _ hP

end Formalism.UG.P
end
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Actions
namespace Formalism.UG.P

open Matrix MvPolynomial

theorem linSubst_comp (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]
    (M N : Matrix n n O) :
    (Formalism.UG.linSubst O n M).comp (Formalism.UG.linSubst O n N) = Formalism.UG.linSubst O n (N * M) := by
  apply MvPolynomial.algHom_ext
  intro i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.linSubst, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

theorem linSubst_one (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Formalism.UG.linSubst O n 1 = AlgHom.id O _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [Formalism.UG.linSubst, Matrix.one_apply]

theorem polynomial_action_mul_holds : Formalism.UG.PolyActMul := by
  intro O _ n _ _ g h
  refine ⟨?_, ?_⟩
  · unfold Formalism.UG.polyAct
    rw [linSubst_comp, _root_.mul_inv_rev, Units.val_mul]
  · unfold Formalism.UG.polyAct
    rw [inv_one, Units.val_one, linSubst_one]

end Formalism.UG.P
end

section -- merged from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AutomorphicFormsDecompositionHolds
noncomputable section

namespace Formalism.UG.P

open Formalism.UG

section Rep

variable {G : Type} [Group G] (Γ K : Subgroup G)

theorem mem_AMFK_iff {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    (ρK : Representation k K W) (f : G → W) :
    f ∈ AMFK k Γ K ρK ↔ ∀ γ : Γ, ∀ g : G, ∀ κ : K, f ((γ : G) * g * κ) = ρK κ⁻¹ (f g) := Iff.rfl

theorem exists_rep (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c) (g : G) :
    ∃ p : Γ × K, g = (p.1 : G) * s (DoubleCoset.mk Γ K g) * (p.2 : G) := by
  have h := (@DoubleCoset.eq _ _ Γ K (s (DoubleCoset.mk Γ K g)) g).1 (hs _)
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

variable {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

end Rep

theorem automorphic_forms_level_finite_holds : Formalism.UG.AMFKFinite := by
  intro G _ Γ K k _ _ W _ _ _ ρK hfin
  have hsurj : ∀ c : ClassSet Γ K, ∃ g : G, DoubleCoset.mk Γ K g = c := by
    intro c
    obtain ⟨g, hg⟩ := Quotient.exists_rep c
    exact ⟨g, hg⟩
  let s : ClassSet Γ K → G := fun c => (hsurj c).choose
  have hs : ∀ c, DoubleCoset.mk Γ K (s c) = c := fun c => (hsurj c).choose_spec
  let L : AMFK k Γ K ρK →ₗ[k] (ClassSet Γ K → W) :=
    LinearMap.pi fun c => (LinearMap.proj (s c)).comp (AMFK k Γ K ρK).subtype
  have hinj : Function.Injective L := by
    intro f g hfg
    apply Subtype.ext
    funext x
    obtain ⟨p, hp⟩ := exists_rep Γ K s hs x
    have hf := (mem_AMFK_iff Γ K ρK (f : G → W)).1 f.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hg := (mem_AMFK_iff Γ K ρK (g : G → W)).1 g.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hfc := congrFun hfg (DoubleCoset.mk Γ K x)
    change (f : G → W) (s (DoubleCoset.mk Γ K x)) = (g : G → W) (s (DoubleCoset.mk Γ K x)) at hfc
    rw [← hp] at hf hg
    rw [hf, hg, hfc]
  exact Module.Finite.of_injective L hinj

end Formalism.UG.P
end
end
