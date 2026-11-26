module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.FixOfPerp

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XphiLinInd
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HpkMulVecMulVec
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ProdIicCastLE
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ExistsKmat
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

theorem exists_K (hk : 1 ≤ k) (c u : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0) :
    ∃ κL : EE k r ≃ₗᵢ[ℂ] EE k r, (∀ a, κL (c a) = u a) ∧ ∀ x, κL (HE k r x) = HE k r (κL x) := by
  have hF : ∀ w : Fin (r + 1) → EE k r, Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (HE k r (w b)) = 0) →
      Orthonormal ℂ (Sum.elim w (fun a => HE k r (w a))) := by
    intro w hw hwi
    rw [orthonormal_iff_ite] at hw ⊢
    rintro (a | a) (b | b)
    · simp [hw]
    · simp [hwi]
    · simp [HE_adj, hwi]
    · simp [HE_adj, HE_HE, hw]
  have hcard : Module.finrank ℂ (EE k r) = Fintype.card ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1)) := by
    simp; omega
  have hres : ∀ w : Fin (r + 1) ⊕ Fin (r + 1) → EE k r, Orthonormal ℂ w →
      Orthonormal ℂ ((Set.range (Sum.inl : _ → (Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1))).restrict
        (Sum.elim w 0)) := by
    intro w hw
    rw [orthonormal_iff_ite] at hw ⊢
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    change inner ℂ (w p) (w q) = _
    rw [hw p q]
    by_cases hpq : p = q
    · subst hpq; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hpq, if_neg]; intro h; exact hpq (Sum.inl_injective (congrArg Subtype.val h))
  obtain ⟨bP, hbP⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ (hF c hc hci))
  obtain ⟨bQ, hbQ⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ (hF u hu hui))
  have hP : ∀ p, bP (Sum.inl p) = Sum.elim c (fun a => HE k r (c a)) p := fun p => hbP _ ⟨p, rfl⟩
  have hQ : ∀ p, bQ (Sum.inl p) = Sum.elim u (fun a => HE k r (u a)) p := fun p => hbQ _ ⟨p, rfl⟩
  set κL := bP.repr.trans bQ.repr.symm with hκL
  have hκb : ∀ i, κL (bP i) = bQ i := fun i => by simp [hκL]
  have hc1 : ∀ a, κL (c a) = u a := fun a => by
    have := hκb (Sum.inl (Sum.inl a)); rwa [hP, hQ] at this
  have hc2 : ∀ a, κL (HE k r (c a)) = HE k r (u a) := fun a => by
    have := hκb (Sum.inl (Sum.inr a)); rwa [hP, hQ] at this
  have hfix : ∀ (b : OrthonormalBasis ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1)) ℂ (EE k r))
      (w : Fin (r + 1) → EE k r), Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (HE k r (w b)) = 0) →
      (∀ p, b (Sum.inl p) = Sum.elim w (fun a => HE k r (w a)) p) →
      ∀ j, HE k r (b (Sum.inr j)) = b (Sum.inr j) := by
    intro b w hw hwi hb j
    refine fix_of_perp w hw hwi _ (fun a => ?_) (fun a => ?_)
    · have := hb (Sum.inl a); simp only [Sum.elim_inl] at this
      rw [← this]; exact b.orthonormal.2 (by simp)
    · have := hb (Sum.inr a); simp only [Sum.elim_inr] at this
      rw [← this]; exact b.orthonormal.2 (by simp)
  refine ⟨κL, hc1, fun x => ?_⟩
  have key : (κL.toLinearEquiv.toLinearMap).comp (HE k r) = (HE k r).comp κL.toLinearEquiv.toLinearMap := by
    refine bP.toBasis.ext fun i => ?_
    simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rcases i with (a | a) | j
    · rw [hP, Sum.elim_inl, hc2, hc1]
    · rw [hP, Sum.elim_inr, HE_HE, hc1, hc2, HE_HE]
    · rw [hfix bP c hc hci hP j, hκb, hfix bQ u hu hui hQ j]
  simpa using LinearMap.congr_fun key x

theorem exists_Kmat (hk : 1 ≤ k) (c u : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0) :
    ∃ κ ∈ Kset k r, ∀ a, (WithLp.toLp 2 (κ *ᵥ (c a).ofLp) : EE k r) = u a := by
  obtain ⟨κL, hκc, hκH⟩ := exists_K hk c u hc hu hci hui
  set κ : Mat k r := Matrix.toEuclideanLin.symm κL.toLinearEquiv.toLinearMap with hκdef
  have hκ : ∀ v, (WithLp.toLp 2 (κ *ᵥ v) : EE k r) = κL (WithLp.toLp 2 v) := by
    intro v
    have h1 : Matrix.toEuclideanLin κ = κL.toLinearEquiv.toLinearMap := LinearEquiv.apply_symm_apply _ _
    have := LinearMap.congr_fun h1 (WithLp.toLp 2 v)
    rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp] at this
    exact this
  have hunit : κᴴ * κ = 1 := by
    ext i j
    have h2 : inner ℂ (WithLp.toLp 2 (κ *ᵥ Pi.single i 1) : EE k r) (WithLp.toLp 2 (κ *ᵥ Pi.single j 1)) =
        inner ℂ (WithLp.toLp 2 (Pi.single i 1) : EE k r) (WithLp.toLp 2 (Pi.single j 1)) := by
      rw [hκ, hκ, LinearIsometryEquiv.inner_map_map]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, dotProduct] at h2
    simp only [Matrix.mul_apply, conjTranspose_apply, one_apply]
    convert h2 using 1
    · refine Finset.sum_congr rfl fun m _ => ?_
      simp [mulVec_single, mul_comm]
    · simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  have hv : ∀ v, κ *ᵥ (Hpk k r *ᵥ v) = Hpk k r *ᵥ (κ *ᵥ v) := by
    intro v
    have := hκH (WithLp.toLp 2 v)
    rw [HE_apply, WithLp.ofLp_toLp, ← hκ, ← hκ, HE_apply, WithLp.ofLp_toLp] at this
    simpa using congrArg WithLp.ofLp this
  have hcomm : κ * Hpk k r = Hpk k r * κ := by
    ext i j
    have := congrFun (hv (Pi.single j 1)) i
    rw [mulVec_mulVec, mulVec_mulVec] at this
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  refine ⟨κ, ⟨?_, hunit⟩, fun a => ?_⟩
  · show κᴴ * Hpk k r * κ = Hpk k r
    rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, hunit, Matrix.one_mul]
  · rw [hκ, WithLp.toLp_ofLp, hκc]

theorem inner_bvec (i : Fin (2 * r + k + 1)) (v : Fin (2 * r + k + 1) → ℂ) :
    inner ℂ (WithLp.toLp 2 (bvec i) : EE k r) (WithLp.toLp 2 v) = v i := by
  first
    | (simp [bvec, PiLp.inner_apply, Pi.single_apply])
    | (show inner ℂ (EuclideanSpace.single i (1 : ℂ)) (WithLp.toLp 2 v : EE k r) = v i
       rw [EuclideanSpace.inner_single_left]; simp)

theorem phiV_apply (b : Fin (r + 1)) (i : Fin (2 * r + k + 1)) :
    phiV k r b i = if b.val < r then (if i.val = 2 * r + k - b.val then 1 else 0) else
      ((Real.sqrt 2)⁻¹ : ℂ) * ((if i.val = r then 1 else 0) + (if i.val = r + k then 1 else 0)) := by
  unfold phiV
  by_cases hb : (b : ℕ) < r
  · rw [dite_eq_left hb, if_pos hb]
    show (Pi.single (esI k r ⟨b.val, hb⟩) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i = _
    rw [Pi.single_apply]
    by_cases hi : (i : ℕ) = 2 * r + k - b.val
    · rw [if_pos hi, if_pos (show i = esI k r ⟨b.val, hb⟩ from Fin.ext hi)]
    · rw [if_neg hi, if_neg (show ¬ i = esI k r ⟨b.val, hb⟩ from fun h => hi (congrArg Fin.val h))]
  · rw [dite_eq_right hb, if_neg hb]
    simp [epsV, bvec, Pi.single_apply, Fin.ext_iff]
    have e1 : ((wI k r 0 : Fin (2 * r + k + 1)) : ℕ) = r := by first | rfl | simp [wI]
    have e2 : ((wI k r (Fin.last k) : Fin (2 * r + k + 1)) : ℕ) = r + k := by first | rfl | simp [wI]
    rw [e1, e2]

theorem toLp_phiV (a : Fin (r + 1)) : (WithLp.toLp 2 (phiV k r a) : EE k r) =
    if a.val < r then WithLp.toLp 2 (bvec ⟨2 * r + k - a.val, by omega⟩) else
      ((Real.sqrt 2)⁻¹ : ℂ) • (WithLp.toLp 2 (bvec ⟨r, by omega⟩) + WithLp.toLp 2 (bvec ⟨r + k, by omega⟩)) := by
  ext i
  by_cases ha : a.val < r
  · simp [ha, phiV_apply, bvec, Pi.single_apply, Fin.ext_iff]
  · simp [ha, phiV_apply, bvec, Pi.single_apply, Fin.ext_iff, mul_add, mul_ite]

theorem hcc : star ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
    first
      | (rw [star_inv₀]; congr 1; exact Complex.conj_ofReal _)
      | simp
  rw [hs, ← mul_inv, h2]; norm_num

theorem qe_orth (hk : 1 ≤ k) : Orthonormal ℂ (fun a => (WithLp.toLp 2 (phiV k r a) : EE k r)) := by
  have key : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := hcc
  rw [orthonormal_iff_ite]
  intro a b
  have hA := a.isLt
  have hB := b.isLt
  rw [toLp_phiV]
  by_cases ha : a.val < r
  · rw [if_pos ha, inner_bvec, phiV_apply]
    split_ifs <;> first
      | rfl
      | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff] at *) <;> omega)
      | simp
  · rw [if_neg ha, inner_smul_left, inner_add_left, inner_bvec, inner_bvec, phiV_apply, phiV_apply]
    split_ifs <;> first
      | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff] at *) <;> omega)
      | (exfalso; exact ‹¬a = b› (Fin.ext (by omega)))
      | (exfalso; simp_all; done)
      | (exfalso; simp_all <;> omega)
      | (simp; done)
      | (simp only [add_zero, zero_add, mul_one]; linear_combination (2 : ℂ) * key)

end ReciprocityTheory.ChartRestriction.DS.Xi.GS
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

theorem pe_eq (a : Fin (r + 1)) :
    (WithLp.toLp 2 (phiV' k r a) : EE k r) = HE k r (WithLp.toLp 2 (phiV k r a)) := by
  rw [HE_apply, WithLp.ofLp_toLp]; rfl

theorem pe_orth (hk : 1 ≤ k) : Orthonormal ℂ (fun a => (WithLp.toLp 2 (phiV' k r a) : EE k r)) := by
  have h := qe_orth (k := k) (r := r) hk
  rw [orthonormal_iff_ite] at h ⊢
  intro a b; simp only [pe_eq, HE_adj, HE_HE]; exact h a b

theorem pe_iso (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    inner ℂ (WithLp.toLp 2 (phiV' k r a) : EE k r) (HE k r (WithLp.toLp 2 (phiV' k r b))) = 0 := by
  rw [pe_eq, pe_eq, HE_HE, HE_adj, HE_apply, WithLp.ofLp_toLp, toLp_phiV a]
  by_cases ha : a.val < r
  · rw [if_pos ha, inner_bvec, hpk_mulVec, phiV_apply]
    simp only [sigI_val, sgnI]
    split_ifs <;> first | rfl | (exfalso; omega) | simp
  · rw [if_neg ha, inner_smul_left, inner_add_left, inner_bvec, inner_bvec, hpk_mulVec, hpk_mulVec,
      phiV_apply, phiV_apply]
    simp only [sigI_val, sgnI, starRingEnd_apply]
    split_ifs <;> first | rfl | (exfalso; omega) | ring | simp

theorem phiV'_linInd' (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) :=
  (pe_orth hk).linearIndependent.map' (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap
    (LinearEquiv.ker _)

theorem phiV'_iso' (hk : 1 ≤ k) (a b : Fin (r + 1)) : herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := by
  rw [herm_eq]; exact pe_iso hk b a

theorem sum_castLE {M : Type*} [AddCommMonoid M] {l : ℕ} (h : l + 1 ≤ r + 1) (f : Fin (r + 1) → M)
    (hf : ∀ b : Fin (r + 1), l < b.val → f b = 0) :
    ∑ b, f b = ∑ b : Fin (l + 1), f (Fin.castLE h b) := by
  rw [show (∑ b : Fin (l + 1), f (Fin.castLE h b)) = ∑ b ∈ Finset.univ.map (Fin.castLEEmb h), f b by rw [Finset.sum_map]; rfl]
  refine (Finset.sum_subset (Finset.subset_univ _) fun b _ hb => hf b ?_).symm
  by_contra hcon
  exact hb (Finset.mem_map.2 ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem prod_Iic_castLE (l : Fin (r + 1)) (g : Fin (r + 1) → ℝ) :
    ∏ j ∈ Finset.Iic l, g j = ∏ j : Fin (l.val + 1), g (Fin.castLE (by omega) j) := by
  rw [show (∏ j : Fin (l.val + 1), g (Fin.castLE (by omega) j)) =
      ∏ j ∈ Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)), g j by
    rw [Finset.prod_map]; rfl]
  congr 1
  ext j
  simp only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · intro hj; exact ⟨⟨j.val, by rw [Fin.le_def] at hj; omega⟩, Fin.ext rfl⟩
  · rintro ⟨b, rfl⟩; rw [Fin.le_def]; simp; omega

theorem iw_core (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (hk : 1 ≤ k)
    (hY : LinearIndependent ℂ Y) (hiso : ∀ a b, herm (Hpk k r) (Y a) (Y b) = 0) :
    ∃ κ ∈ Kset k r, ∃ τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ j, τ j j ≠ 0) ∧ (∀ a, Y a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) ∧
      ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l Y := by
  obtain ⟨u, τ, hu, hτ, hd, hwe, hspan⟩ := gs_fac (fun a => (WithLp.toLp 2 (Y a) : EE k r)) (linInd_toLp Y hY)
  have hwi : ∀ a b, inner ℂ (WithLp.toLp 2 (Y a) : EE k r) (HE k r (WithLp.toLp 2 (Y b))) = 0 :=
    fun a b => by rw [← herm_eq]; exact hiso b a
  have hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0 := by
    intro a b
    obtain ⟨ca, hca⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan a)
    obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan b)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hca, ← hcb, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, inner_smul_left, inner_smul_right, hwi, mul_zero, mul_zero]
  obtain ⟨κ, hκK, hκ⟩ := exists_Kmat hk _ u (pe_orth hk) hu (fun a b => pe_iso hk a b) hui
  have hκ' : ∀ b, u b = WithLp.toLp 2 (κ *ᵥ phiV' k r b) := fun b => (hκ b).symm
  refine ⟨κ, hκK, τ, hτ, hd, fun a => ?_, fun l => ?_⟩
  · have h1 : (WithLp.toLp 2 (Y a) : EE k r) = ∑ b, τ b a • (WithLp.toLp 2 (κ *ᵥ phiV' k r b) : EE k r) := by
      rw [hwe a]; simp only [hκ']
    have h2 := congrArg (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)) h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h2
    simpa using h2
  · rw [ga_eq]
    have hle : l.val + 1 ≤ r + 1 := by omega
    have hsub : ∀ a : Fin (l.val + 1), (WithLp.toLp 2 (Y (Fin.castLE hle a)) : EE k r) =
        ∑ b : Fin (l.val + 1), (τ.submatrix (Fin.castLE hle) (Fin.castLE hle)) b a • u (Fin.castLE hle b) := by
      intro a
      rw [hwe (Fin.castLE hle a)]
      refine sum_castLE hle _ fun b hb => ?_
      have hlt : Fin.castLE hle a < b := by
        rw [Fin.lt_def, Fin.val_castLE]; have := a.isLt; omega
      rw [show τ b (Fin.castLE hle a) = 0 from hτ hlt, zero_smul]
    have hτl : (τ.submatrix (Fin.castLE hle) (Fin.castLE hle)).BlockTriangular id :=
      fun i j hij => hτ (show Fin.castLE hle j < Fin.castLE hle i from hij)
    have hdet := det_gram_of (fun a : Fin (l.val + 1) => (WithLp.toLp 2 (Y (Fin.castLE hle a)) : EE k r))
      (fun b => u (Fin.castLE hle b)) (τ.submatrix (Fin.castLE hle) (Fin.castLE hle))
      (hu.comp _ (Fin.castLE_injective hle)) hτl hsub
    rw [hdet, Complex.ofReal_re, prod_Iic_castLE]
    rfl

end ReciprocityTheory.ChartRestriction.DS.Xi.GS

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem phiV'_linInd (k r : ℕ) (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) := GS.phiV'_linInd' hk

theorem phiV'_iso (k r : ℕ) (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := GS.phiV'_iso' hk a b

theorem iwB : IW := fun k r Y hk hY hiso => by
  obtain ⟨κ, hκ, τ, h1, -, h3, h4⟩ := GS.iw_core Y hk hY hiso
  exact ⟨κ, hκ, τ, h1, h3, h4⟩

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section herm
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

theorem herm_UH' [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : g ∈ UH H) (u v : ι → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ v) = herm H u v := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    hg']

theorem herm_sum_l {α : Type*} (c : α → ℂ) (s : Finset α) (u : α → ι → ℂ) (w : ι → ℂ) :
    herm H (∑ j ∈ s, c j • u j) w = ∑ j ∈ s, c j * herm H (u j) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [herm, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
      smul_eq_mul]

theorem herm_sum_r {α : Type*} (c : α → ℂ) (s : Finset α) (u : ι → ℂ) (w : α → ι → ℂ) :
    herm H u (∑ j ∈ s, c j • w j) = ∑ j ∈ s, star (c j) * herm H u (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [herm, star_add, star_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem mat_eq_of_mulVec' [DecidableEq ι] {A B : Matrix ι ι ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h v])

end herm

section hpk
variable (k r : ℕ)

theorem hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h]
    simp only [Matrix.mulVec, dotProduct, hpk_out k r h]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro j _ hj
      have hj' : j.val ≠ 2 * r + k - i.val := fun hc => hj (Fin.ext hc)
      simp [hj']
    · simp
  · rw [if_neg h]
    simp only [Matrix.mulVec, dotProduct, hpk_mid k r h]
    rw [Finset.sum_eq_single i]
    · by_cases h2 : i.val = r + k <;> simp [h2]
    · intro j _ hj
      have hj' : j.val ≠ i.val := fun hc => hj (Fin.ext hc)
      simp [hj']
    · simp

theorem hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  rw [hpk_mulVec]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, hpk_mulVec, if_pos (by dsimp only; omega)]
    congr 1
    ext
    dsimp only
    omega
  · rw [if_neg h]
    split_ifs with h2
    · rw [hpk_mulVec, if_neg h, if_pos h2, neg_neg]
    · rw [hpk_mulVec, if_neg h, if_neg h2]

theorem hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec' fun v => by rw [← Matrix.mulVec_mulVec, hpk_mulVec_mulVec, Matrix.one_mulVec]

variable {k r}

theorem uh_inv_mul {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hpk_sq]
  rw [Matrix.inv_eq_left_inv hl, hl]

theorem uh_mul_inv {g : Mat k r} (hg : g ∈ GV k r) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (uh_inv_mul hg))

theorem herm_inv {x : Mat k r} (hx : x ∈ GV k r) (g : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((x⁻¹ * g) *ᵥ v) w = herm (Hpk k r) (g *ᵥ v) (x *ᵥ w) := by
  rw [← herm_UH' (Hpk k r) hx, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, uh_mul_inv hx,
    Matrix.one_mul]

end hpk

section tri

theorem sub_mul_tri {n m : ℕ} (h : m ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (A * B).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE h) (Fin.castLE h) * B.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hemb : ∑ l : Fin m, A (Fin.castLE h i) (Fin.castLE h l) * B (Fin.castLE h l) (Fin.castLE h j) =
      ∑ l ∈ Finset.univ.map (Fin.castLEEmb h), A (Fin.castLE h i) l * B l (Fin.castLE h j) := by
    rw [Finset.sum_map]
    rfl
  rw [hemb]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro l _ hl
  have hlm : m ≤ l.val := by
    by_contra hc
    push_neg at hc
    exact hl (Finset.mem_map.mpr ⟨⟨l.val, hc⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  have hjl : id (Fin.castLE h j) < id l := by
    show (Fin.castLE h j).val < l.val
    have := j.isLt
    simp only [Fin.coe_castLE]
    omega
  rw [hB hjl, mul_zero]

theorem sub_tri_mul {n m : ℕ} (h : m ≤ n) (A B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (Bᴴ * A).submatrix (Fin.castLE h) (Fin.castLE h) =
      (B.submatrix (Fin.castLE h) (Fin.castLE h))ᴴ * A.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hemb : ∑ l : Fin m, star (B (Fin.castLE h l) (Fin.castLE h i)) * A (Fin.castLE h l) (Fin.castLE h j) =
      ∑ l ∈ Finset.univ.map (Fin.castLEEmb h), star (B l (Fin.castLE h i)) * A l (Fin.castLE h j) := by
    rw [Finset.sum_map]
    rfl
  rw [hemb]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro l _ hl
  have hlm : m ≤ l.val := by
    by_contra hc
    push_neg at hc
    exact hl (Finset.mem_map.mpr ⟨⟨l.val, hc⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  have hil : id (Fin.castLE h i) < id l := by
    show (Fin.castLE h i).val < l.val
    have := i.isLt
    simp only [Fin.coe_castLE]
    omega
  rw [hB hil, star_zero, zero_mul]

theorem tri_sub {n m : ℕ} (h : m ≤ n) (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.BlockTriangular id) :
    (B.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id :=
  fun i j hij => hB (show (Fin.castLE h j).val < (Fin.castLE h i).val from hij)

end tri

section dl
variable {k r : ℕ}

def Pm (k r : ℕ) (g : Mat k r) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun a b => herm (Hpk k r) (g *ᵥ phiV' k r b) (phiV' k r a)

def cl (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : Fin (r + 1)) : ℝ≥0 :=
  ∏ j : Fin (l.val + 1), ‖τ (Fin.castLE (show l.val + 1 ≤ r + 1 by omega) j)
    (Fin.castLE (show l.val + 1 ≤ r + 1 by omega) j)‖₊

theorem dl_eq (l : Fin (r + 1)) (g : Mat k r) :
    Dl k r l g = ((Pm k r g).submatrix (Fin.castLE (show l.val + 1 ≤ r + 1 by omega))
      (Fin.castLE (show l.val + 1 ≤ r + 1 by omega))).det := rfl

theorem pm_left {x κ : Mat k r} (hx : x ∈ GV k r) (hκ : κ ∈ GV k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hY : ∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) (g : Mat k r) :
    Pm k r (x⁻¹ * g) = τᴴ * Pm k r (κ⁻¹ * g) := by
  ext a b
  simp only [Pm, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [herm_inv hx, hY a, herm_sum_r]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [herm_inv hκ]

theorem pm_right {y κ : Mat k r} (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hY : ∀ a, y *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) (g : Mat k r) :
    Pm k r (g * y) = Pm k r (g * κ) * τ := by
  ext a b
  simp only [Pm, Matrix.of_apply, Matrix.mul_apply]
  have e : (g * y) *ᵥ phiV' k r b = ∑ c, τ c b • ((g * κ) *ᵥ phiV' k r c) := by
    rw [← Matrix.mulVec_mulVec, hY b, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  rw [e, herm_sum_l]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem dl_left {x κ : Mat k r} (hx : x ∈ GV k r) (hκ : κ ∈ GV k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (hY : ∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b))
    (g : Mat k r) (l : Fin (r + 1)) : ‖Dl k r l (x⁻¹ * g)‖₊ = cl τ l * ‖Dl k r l (κ⁻¹ * g)‖₊ := by
  rw [dl_eq, dl_eq, pm_left hx hκ τ hY, sub_tri_mul _ _ _ hτ, Matrix.det_mul,
    Matrix.det_conjTranspose, Matrix.det_of_upperTriangular (tri_sub _ τ hτ), nnnorm_mul,
    nnnorm_star, nnnorm_prod]
  rfl

theorem dl_right {y κ : Mat k r} (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hτ : τ.BlockTriangular id) (hY : ∀ a, y *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b))
    (g : Mat k r) (l : Fin (r + 1)) : ‖Dl k r l (g * y)‖₊ = cl τ l * ‖Dl k r l (g * κ)‖₊ := by
  rw [dl_eq, dl_eq, pm_right τ hY, sub_mul_tri _ _ _ hτ, Matrix.det_mul,
    Matrix.det_of_upperTriangular (tri_sub _ τ hτ), nnnorm_mul, nnnorm_prod, mul_comm]
  rfl

theorem fsE_fac (s : Fin (r + 1) → ℝ) (g1 g2 : Mat k r) (c : Fin (r + 1) → ℝ≥0)
    (h : ∀ l, ‖Dl k r l g1‖₊ = c l * ‖Dl k r l g2‖₊) :
    FsE k r s g1 = (∏ l, ((c l : ℝ≥0∞)) ^ (-s l)) * FsE k r s g2 := by
  unfold FsE
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [h l, ENNReal.coe_mul, ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top]

end dl

end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

section fs
variable {k r : ℕ}

theorem iic_eq (l : Fin (r + 1)) :
    Finset.Iic l = Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)) := by
  ext c
  simp only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and, Fin.le_def]
  constructor
  · intro hc; exact ⟨⟨c.val, by omega⟩, Fin.ext rfl⟩
  · rintro ⟨a, rfl⟩
    have := a.isLt
    simp only [Fin.castLEEmb_apply, Fin.val_castLE]
    omega

theorem ofReal_fsR (s : Fin (r + 1) → ℝ) (x : Mat k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hGa : ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l (fun a => x *ᵥ phiV' k r a))
    (hpos : ∀ l, 0 < Ga k r l (fun a => x *ᵥ phiV' k r a)) :
    ENNReal.ofReal (fsR k r s x) = ∏ l, ((cl τ l : ℝ≥0∞)) ^ (-s l) := by
  unfold fsR
  rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hpos l).le _)]
  refine Finset.prod_congr rfl fun l _ => ?_
  have ht : Ga k r l (fun a => x *ᵥ phiV' k r a) = ((cl τ l : ℝ)) ^ 2 := by
    rw [← hGa l, iic_eq, Finset.prod_map, Finset.prod_pow, cl, NNReal.coe_prod]
    rfl
  have hc : 0 < (cl τ l : ℝ) := by
    have h0 := hpos l
    rw [ht] at h0
    exact lt_of_le_of_ne (NNReal.coe_nonneg _) (fun he => by rw [← he] at h0; simp at h0)
  rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← ENNReal.ofReal_rpow_of_pos hc,
    ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  ring

theorem xphi_linInd (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    LinearIndependent ℂ (fun a => x *ᵥ phiV' k r a) := by
  have hinj : Function.Injective (Matrix.mulVecLin x) := fun u v huv => by
    have h2 := congrArg (fun w => x⁻¹ *ᵥ w) huv
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, uh_inv_mul hx] using h2
  exact (phiV'_linInd k r hk).map' (Matrix.mulVecLin x) (LinearMap.ker_eq_bot.2 hinj)

theorem iw_at (hIW : IW) (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∃ τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) ∧
      ∀ s, ENNReal.ofReal (fsR k r s x) = ∏ l, ((cl τ l : ℝ≥0∞)) ^ (-s l) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hGa⟩ := hIW k r (fun a => x *ᵥ phiV' k r a) hk (xphi_linInd hk hx)
    (fun a b => by rw [herm_UH' _ hx]; exact phiV'_iso k r hk a b)
  exact ⟨κ, hκ, τ, hτ, hY, fun s => ofReal_fsR s x τ hGa (fun l => GS.ga_pos k r _ (xphi_linInd hk hx) l)⟩

theorem fsE_left (hIW : IW) (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∀ (s : Fin (r + 1) → ℝ) (g : Mat k r),
      FsE k r s (x⁻¹ * g) = ENNReal.ofReal (fsR k r s x) * FsE k r s (κ⁻¹ * g) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hf⟩ := iw_at hIW hk hx
  refine ⟨κ, hκ, fun s g => ?_⟩
  rw [hf s]
  exact fsE_fac s _ _ _ (dl_left hx hκ.1 τ hτ hY g)

theorem fsE_right (hIW : IW) (hk : 1 ≤ k) {y : Mat k r} (hy : y ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∀ (s : Fin (r + 1) → ℝ) (g : Mat k r),
      FsE k r s (g * y) = ENNReal.ofReal (fsR k r s y) * FsE k r s (g * κ) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hf⟩ := iw_at hIW hk hy
  refine ⟨κ, hκ, fun s g => ?_⟩
  rw [hf s]
  exact fsE_fac s _ _ _ (dl_right τ hτ hY g)

theorem fsR_nonneg {k r : ℕ} (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) (s : Fin (r + 1) → ℝ) :
    0 ≤ fsR k r s x :=
  Finset.prod_nonneg fun l _ => Real.rpow_nonneg (GS.ga_pos k r _ (xphi_linInd hk hx) l).le _

end fs

section meas
variable {k r : ℕ}

theorem cont_lmul (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) :=
  Continuous.matrix_mul continuous_const continuous_id

theorem cont_rmul (a : Mat k r) : Continuous (rmulF a : Mt k r → Mt k r) :=
  Continuous.matrix_mul continuous_id continuous_const

def lmulE {a : Mat k r} (ha : a ∈ GV k r) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv g := by
    show a⁻¹ * (a * Matrix.of g) = g
    rw [← Matrix.mul_assoc, uh_inv_mul ha, Matrix.one_mul]; rfl
  right_inv g := by
    show a * (a⁻¹ * Matrix.of g) = g
    rw [← Matrix.mul_assoc, uh_mul_inv ha, Matrix.one_mul]; rfl
  measurable_toFun := (cont_lmul a).measurable
  measurable_invFun := (cont_lmul a⁻¹).measurable

def rmulE {a : Mat k r} (ha : a ∈ GV k r) : Mt k r ≃ᵐ Mt k r where
  toFun := rmulF a
  invFun := rmulF a⁻¹
  left_inv g := by
    show Matrix.of g * a * a⁻¹ = g
    rw [Matrix.mul_assoc, uh_mul_inv ha, Matrix.mul_one]; rfl
  right_inv g := by
    show Matrix.of g * a⁻¹ * a = g
    rw [Matrix.mul_assoc, uh_inv_mul ha, Matrix.mul_one]; rfl
  measurable_toFun := (cont_rmul a).measurable
  measurable_invFun := (cont_rmul a⁻¹).measurable

theorem lmul_int {a : Mat k r} (ha : a ∈ GV k r) {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    (f : Mt k r → ℝ≥0∞) : ∫⁻ g, f (lmulM a g) ∂μ = ∫⁻ g, f g ∂μ := by
  have h := lintegral_map_equiv f (lmulE ha) (μ := μ)
  rw [show ⇑(lmulE ha) = lmulM a from rfl, hμ.left a ha] at h
  exact h.symm

theorem rmul_int {a : Mat k r} (ha : a ∈ GV k r) {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    (f : Mt k r → ℝ≥0∞) : ∫⁻ g, f (rmulF a g) ∂μ = ∫⁻ g, f g ∂μ := by
  have h := lintegral_map_equiv f (rmulE ha) (μ := μ)
  rw [show ⇑(rmulE ha) = rmulF a from rfl, hμ.right a ha] at h
  exact h.symm

end meas

end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B HermitianLiftIdentities

theorem tLeftH (hIW : IW) (hB2 : InductiveHeisenbergInputs) : TLeft := by
  intro k r s μG Φ hk hμ _ hK x hx
  obtain ⟨κ, hκ, hF⟩ := fsE_left hIW hk hx
  have h1 : ∀ g : Mt k r, κ⁻¹ * Matrix.of (lmulM κ g) = Matrix.of g := fun g => by
    show κ⁻¹ * (κ * Matrix.of g) = Matrix.of g
    rw [← Matrix.mul_assoc, uh_inv_mul hκ.1, Matrix.one_mul]
  calc ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g) ∂μG
      = ∫⁻ g, ENNReal.ofReal (fsR k r s x) * (Φ g * FsE k r s (κ⁻¹ * Matrix.of g)) ∂μG := by
        refine lintegral_congr fun g => ?_
        rw [hF s]; ring
    _ = ENNReal.ofReal (fsR k r s x) * ∫⁻ g, Φ g * FsE k r s (κ⁻¹ * Matrix.of g) ∂μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
        rw [← lmul_int hκ.1 hμ (fun g => Φ g * FsE k r s (κ⁻¹ * Matrix.of g))]
        refine congrArg _ (lintegral_congr fun g => ?_)
        simp only [hK κ hκ g, h1]

theorem tBothH (hIW : IW) (hB2 : InductiveHeisenbergInputs) : TBoth := by
  intro k r s μG Φ hk hμ hΦ hK x hx y hy
  obtain ⟨κ, hκ, hF⟩ := fsE_right hIW hk hy
  have hL := tLeftH hIW hB2 k r s μG Φ hk hμ hΦ (fun κ hκ g => (hK κ hκ g).1) x hx
  have h1 : ∀ g : Mt k r, x⁻¹ * Matrix.of (rmulF κ g) = x⁻¹ * Matrix.of g * κ := fun g => by
    show x⁻¹ * (Matrix.of g * κ) = x⁻¹ * Matrix.of g * κ
    rw [Matrix.mul_assoc]
  calc ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g * y) ∂μG
      = ∫⁻ g, ENNReal.ofReal (fsR k r s y) * (Φ g * FsE k r s (x⁻¹ * Matrix.of g * κ)) ∂μG := by
        refine lintegral_congr fun g => ?_
        rw [hF s]; ring
    _ = ENNReal.ofReal (fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g * κ) ∂μG :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g) ∂μG := by
        rw [← rmul_int hκ.1 hμ (fun g => Φ g * FsE k r s (x⁻¹ * Matrix.of g))]
        refine congrArg _ (lintegral_congr fun g => ?_)
        simp only [(hK κ hκ g).2, h1]
    _ = _ := by
        rw [hL, ENNReal.ofReal_mul (fsR_nonneg hk hx s)]
        ring

end ReciprocityTheory.ChartRestriction.DS.Xi
