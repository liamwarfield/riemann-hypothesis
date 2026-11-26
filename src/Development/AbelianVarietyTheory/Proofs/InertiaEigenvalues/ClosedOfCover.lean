module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfCrystallineBreuilKisinFrame
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistableBoundedJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisAtEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFrameLimitLatticeBreuilKisinTower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LayerDdRBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodRingGaloisInvariantsIffConst
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthInertiaRestrictionCocyclesLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfBreuilKisinFrameIsDeRham
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfBreuilKisinFrameIsDeRham
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem isDR_of_frame_isDR : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsDR → Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) := by
  intro l _ K bk τ hτ P AI T N d ρ F hF
  obtain ⟨Y, Y', hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  obtain ⟨B, Q, -, hQ, -, -, hinv⟩ := GlobalTheory.T.exists_invariant_basis_deRham_breuilKisin l K bk τ hτ C N d (fun g => (ρ g).val) F Y hF hY
  have hQ' : IsUnit (T.eD.symm.mapMatrix Q) := hQ.map T.eD.symm.mapMatrix
  refine GlobalTheory.PMon.isDR_of_periodMatrix l P (Fin d) K (Fin d → ℚ_[l]) (Pi.basisFun ℚ_[l] (Fin d)) (qRep ρ) hQ'.unit ?_
  intro g
  have hg := hinv g
  simp only [IsUnit.unit_spec]
  ext i j
  apply T.eD.injective
  have hij := congrFun (congrFun hg i) j
  rw [LinearMap.toMatrix_eq_toMatrix']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [qRep, Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, RingEquiv.mapMatrix_apply] at hij ⊢
  simp only [MonoidHom.comp_apply, MonoidHom.coe_coe, Units.coeHom_apply, RingHom.mapMatrix_apply, AlgEquiv.coe_toAlgHom, Matrix.toLinAlgEquiv'_apply, LinearMap.toMatrix'_toLin',
    Matrix.map_apply, T.actD, RingEquiv.apply_symm_apply] at ⊢
  rw [← hij]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  have e : LinearMap.toMatrix' (Matrix.toLinAlgEquiv' ((algebraMap ℤ_[l] ℚ_[l]).mapMatrix (ρ g : Matrix (Fin d) (Fin d) ℤ_[l]))) =
      (algebraMap ℤ_[l] ℚ_[l]).mapMatrix (ρ g : Matrix (Fin d) (Fin d) ℤ_[l]) :=
    LinearMap.toMatrix'_toLin' _
  erw [e]
  exact T.zD ((ρ g : Matrix (Fin d) (Fin d) ℤ_[l]) i x)

end GlobalTheory.BKLim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfBreuilKisinFrameIsDeRhamStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeRham_of_breuilKisinFrame_isDeRham : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsDR → Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) := by
  first | exact @GlobalTheory.BKLim.isDR_of_frame_isDR | exact GlobalTheory.BKLim.isDR_of_frame_isDR | (intros; apply GlobalTheory.BKLim.isDR_of_frame_isDR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetEqOfPowerSumsZpowEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetEqOfPowerSumsZpowEq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem multiset_eq_of_powerSums_zpow_eq : ∀ (k : Type) [Field k] [CharZero k] (z : k), z ≠ 0 →
    (∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1) → ∀ J J' : Multiset ℤ,
    (∀ n : ℕ, (J.map fun h => (z ^ h) ^ n).sum = (J'.map fun h => (z ^ h) ^ n).sum) → J = J' := by
  intro k _ _ z hz hroot J J' hsum

  have hlt : ∀ a b : ℤ, a < b → z ^ a ≠ z ^ b := by
    intro a b hab heq
    have h1 : z ^ (b - a) = 1 := by
      rw [zpow_sub₀ hz, heq, div_self (zpow_ne_zero _ hz)]
    have h2 : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
    rw [← h2, zpow_natCast] at h1
    exact hroot _ (by omega) h1
  have hinj : Function.Injective (fun h : ℤ => z ^ h) := by
    intro a b hab
    simp only at hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt a b h hab
    · exact hlt b a h hab.symm

  let χ : ℤ → (Multiplicative ℕ →* k) := fun h => powersHom k (z ^ h)
  have hχ : Function.Injective χ := (powersHom k).injective.comp hinj
  have hli := (linearIndependent_monoidHom (Multiplicative ℕ) k).comp χ hχ
  rw [linearIndependent_iff'] at hli

  have key : ∀ (M : Multiset ℤ) (s : Finset ℤ), M.toFinset ⊆ s → ∀ f : ℤ → k,
      (M.map f).sum = ∑ h ∈ s, (M.count h : k) * f h := by
    intro M s hs f
    rw [Finset.sum_multiset_map_count]
    simp_rw [nsmul_eq_mul]
    apply Finset.sum_subset hs
    intro x _ hx
    rw [Multiset.mem_toFinset] at hx
    simp [Multiset.count_eq_zero.mpr hx]
  set s : Finset ℤ := (J + J').toFinset with hs
  have hJ : J.toFinset ⊆ s := by
    intro x hx; rw [Multiset.mem_toFinset] at hx; rw [hs, Multiset.mem_toFinset]
    exact Multiset.mem_add.mpr (Or.inl hx)
  have hJ' : J'.toFinset ⊆ s := by
    intro x hx; rw [Multiset.mem_toFinset] at hx; rw [hs, Multiset.mem_toFinset]
    exact Multiset.mem_add.mpr (Or.inr hx)
  have hzero := hli s (fun h => (J.count h : k) - (J'.count h : k)) (by
    funext m
    have e := hsum (Multiplicative.toAdd m)
    rw [key J s hJ, key J' s hJ'] at e
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    simp only [χ, powersHom_apply, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact e)
  refine Multiset.ext.mpr (fun a => ?_)
  by_cases ha : a ∈ s
  · have := hzero a ha
    rw [sub_eq_zero] at this
    exact_mod_cast this
  · rw [hs, Multiset.mem_toFinset, Multiset.mem_add, not_or] at ha
    rw [Multiset.count_eq_zero.mpr ha.1, Multiset.count_eq_zero.mpr ha.2]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetEqOfPowerSumsZpowEqStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiset_eq_of_power_sums_zpow_eq : ∀ (k : Type) [Field k] [CharZero k] (z : k), z ≠ 0 → (∀ i : ℕ, 1 ≤ i → z ^ i ≠ 1) → ∀ J J' : Multiset ℤ, (∀ n : ℕ, (J.map fun h => (z ^ h) ^ n).sum = (J'.map fun h => (z ^ h) ^ n).sum) → J = J' := by
  first | exact @GlobalTheory.multiset_eq_of_powerSums_zpow_eq | exact GlobalTheory.multiset_eq_of_powerSums_zpow_eq | (intros; apply GlobalTheory.multiset_eq_of_powerSums_zpow_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateIffDiagonalAdaptedBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateIffDiagonalAdaptedBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.HTDiag

theorem theta_zero_of_pow_eq {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] (θ : R →+* S)
    {t w v : R} {n m : ℕ} (ht : t ≠ 0) (hθt : θ t = 0) (hv : θ v = 0 → v = 0)
    (h : t ^ n * w = t ^ m * v) (hnm : n ≠ m) : θ w = 0 := by
  rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have e : t ^ (n + k + 1) = t ^ n * t ^ (k + 1) := by ring
    rw [e, mul_assoc] at h
    have hw : w = t ^ (k + 1) * v := mul_left_cancel₀ (pow_ne_zero n ht) h
    rw [hw, map_mul, map_pow, hθt, zero_pow (Nat.succ_ne_zero k), zero_mul]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have e : t ^ (m + k + 1) = t ^ m * t ^ (k + 1) := by ring
    rw [e, mul_assoc] at h
    have hv' : v = t ^ (k + 1) * w := (mul_left_cancel₀ (pow_ne_zero m ht) h).symm
    have hv0 : v = 0 := hv (by rw [hv', map_mul, map_pow, hθt, zero_pow (Nat.succ_ne_zero k), zero_mul])
    rw [hv0, mul_zero] at h
    have h' : t ^ (k + 1) * w = 0 := (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ ht)
    have hw : w = 0 := (mul_eq_zero.1 h').resolve_left (pow_ne_zero _ ht)
    rw [hw, map_zero]

end GlobalTheory.BKLim.HTDiag


open GlobalTheory.BKLim.HTDiag in
theorem GlobalTheory.BKLim.isHT_iff_diag : ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (C : Core l), C.InvdR → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (H : Hodge C ξ ρ K') (z : ℂ_[l]) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), K.1 ≤ K'.1 → (u * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) ↔ IsHT C ξ ρ z u) := by
  intro l _ K K' C hI ξ hξ a ρ H z u hKK'
  constructor
  · intro hm K'' p q x y hfix hxy
    obtain ⟨hdom, hinj, hF, -⟩ := BdRField.bdR_isField l
    haveI := hdom
    set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι

    have hxiker : xi C.ε ∈ Ideal.span {ξ} := by
      rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c0, hc0⟩ := Ideal.mem_span_singleton'.1 hxiker
    have hXu : IsUnit (ι (aDp l ξ)) := by
      have h1 := TiedUnif.isUnit_xi (core_isEps l C)
      rw [← hc0, map_mul, map_mul] at h1
      exact isUnit_of_mul_isUnit_right h1
    set e := ι (aDp l ξ) with he
    obtain ⟨i0, hie⟩ : ∃ i0, i0 * e = 1 := ⟨_, hXu.val_inv_mul⟩
    have ht0 : aDp l ξ ≠ 0 := by
      intro h0
      rw [he, h0, map_zero, mul_zero] at hie
      exact zero_ne_one (hinj (by rw [map_zero, map_one]; exact hie))

    have hVdet : IsUnit H.V.det := (Matrix.isUnit_iff_isUnit_det _).1 H.unit
    set W := H.V⁻¹ with hW
    have hVW : H.V * W = 1 := Matrix.mul_nonsing_inv _ hVdet
    have hWV : W * H.V = 1 := Matrix.nonsing_inv_mul _ hVdet
    have hWVι : W.map ι * H.V.map ι = 1 := by
      rw [← Matrix.map_mul, hWV, Matrix.map_one _ (map_zero _) (map_one _)]

    set d : Fin a → Per.BdR l := fun k => i0 ^ H.q * e ^ H.p k with hd
    set d' : Fin a → Per.BdR l := fun k => e ^ H.q * i0 ^ H.p k with hd'
    have hdd : ∀ k, d' k * d k = 1 := fun k => by
      calc d' k * d k = (i0 * e) ^ H.q * (i0 * e) ^ H.p k := by simp only [hd, hd']; ring
        _ = 1 := by rw [hie, one_pow, one_pow, one_mul]
    have hQ : H.Q = H.V.map ι * Matrix.diagonal d := by
      ext i k
      rw [Matrix.mul_diagonal, Matrix.map_apply]
      have h := H.Q_eq i k
      simp only [map_mul, map_pow] at h
      rw [← he] at h
      calc H.Q i k = (i0 * e) ^ H.q * H.Q i k := by rw [hie, one_pow, one_mul]
        _ = i0 ^ H.q * (e ^ H.q * H.Q i k) := by ring
        _ = ι (H.V i k) * d k := by rw [h]; simp only [hd]; ring
    set Qi := Matrix.diagonal d' * W.map ι with hQi
    have hQiQ : Qi * H.Q = 1 := by
      rw [hQi, hQ, Matrix.mul_assoc, ← Matrix.mul_assoc (W.map ι), hWVι, Matrix.one_mul,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1; funext k; exact hdd k
    have hQQi : H.Q * Qi = 1 := mul_eq_one_comm.1 hQiQ
    set av := Qi *ᵥ x with hav
    have hxa : x = H.Q *ᵥ av := by rw [hav, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]

    let K3 : FinExt l := ⟨K'.1 ⊔ K''.1, by
      haveI := K'.2; haveI := K''.2; exact IntermediateField.finiteDimensional_sup _ _⟩
    have hmono : ∀ {A B : FinExt l}, A.1 ≤ B.1 → ∀ g, g ∈ GK B → g ∈ GK A := fun h g hg =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (h hx)
    have h3' : K'.1 ≤ K3.1 := le_sup_left
    have h3'' : K''.1 ≤ K3.1 := le_sup_right
    have h3 : K.1 ≤ K3.1 := hKK'.trans h3'

    have hinv : ∀ g : GQ l, g ∈ GK K3 → ∀ j, Per.σD g (av j) = av j := by
      intro g hg
      let g' : ↥(GK K) := ⟨g, hmono h3 g hg⟩
      have h1 := hfix g' (hmono h3'' g hg)
      have h2 := H.inv g' (hmono h3' g hg)
      have hσx : (fun i => Per.σD (g' : GQ l) (x i)) =
          H.Q.map (Per.σD (g' : GQ l)) *ᵥ (fun k => Per.σD (g' : GQ l) (av k)) := by
        funext i
        rw [hxa]
        exact RingHom.map_mulVec _ _ _ i
      rw [hσx, Matrix.mulVec_mulVec, h2] at h1
      have h4 : av = (fun k => Per.σD (g' : GQ l) (av k)) := by
        calc av = Qi *ᵥ x := hav
          _ = Qi *ᵥ (H.Q *ᵥ (fun k => Per.σD (g' : GQ l) (av k))) := by rw [h1]
          _ = _ := by rw [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
      intro j
      exact (congrFun h4 j).symm
    choose c hcK hc using fun j => hI K3 (av j) (fun g hg => hinv g hg j)

    have hWx : ∀ k, e ^ q * (W.map ι *ᵥ x) k = e ^ p * (W.map ι *ᵥ (fun i => ι (y i))) k := by
      have hv : e ^ q • x = e ^ p • (fun i => ι (y i)) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hxy i, map_mul, map_pow]
      intro k
      have := congrFun (congrArg (fun v => W.map ι *ᵥ v) hv) k
      simpa [Matrix.mulVec_smul] using this
    have hD : ∀ k, aDp l ξ ^ (H.q + p) * (W *ᵥ y) k = aDp l ξ ^ (q + H.p k) * C.o (c k) := by
      intro k
      apply hinj
      have hck : ι (C.o (c k)) = av k := hc k
      rw [map_mul, map_mul, map_pow, map_pow, hck, RingHom.map_mulVec]
      have hak : av k = d' k * (W.map ι *ᵥ x) k := by
        rw [hav, hQi, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
      rw [hak]
      calc e ^ (H.q + p) * (W.map ι *ᵥ (fun i => ι (y i))) k = e ^ H.q * (e ^ p * (W.map ι *ᵥ (fun i => ι (y i))) k) := by ring
        _ = e ^ H.q * (e ^ q * (W.map ι *ᵥ x) k) := by rw [hWx k]
        _ = (i0 * e) ^ H.p k * (e ^ H.q * (e ^ q * (W.map ι *ᵥ x) k)) := by rw [hie, one_pow, one_mul]
        _ = e ^ (q + H.p k) * (d' k * (W.map ι *ᵥ x) k) := by simp only [hd']; ring

    have hθξ : Per.θD l (aDp l ξ) = 0 := by
      rw [(thetaD_props l).2.2.2.1 ξ]
      have : Per.θ l ξ = 0 := RingHom.mem_ker.1 (hξ ▸ Ideal.mem_span_singleton_self ξ)
      rw [this]; rfl
    have hkey : ∀ k, z ^ ((H.p k : ℤ) - H.q) * Per.θD l ((W *ᵥ y) k) =
        z ^ ((p : ℤ) - q) * Per.θD l ((W *ᵥ y) k) := by
      intro k
      by_cases hk : (H.p k : ℤ) - H.q = (p : ℤ) - q
      · rw [hk]
      · have hz : Per.θD l ((W *ᵥ y) k) = 0 := by
          refine theta_zero_of_pow_eq (Per.θD l) ht0 hθξ ?_ (hD k) ?_
          · intro h0
            rw [C.o_sec.th] at h0
            have : c k = 0 := by
              first
                | exact (algebraMap (Om l) ℂ_[l]).injective (by simpa using h0)
                | exact UniformSpace.Completion.coe_injective _ (by simpa using h0)
            rw [this, map_zero]
          · intro hn; apply hk; omega
        rw [hz, mul_zero, mul_zero]

    have hyw : y = H.V *ᵥ (W *ᵥ y) := by rw [Matrix.mulVec_mulVec, hVW, Matrix.one_mulVec]
    have hθy : (fun i => Per.θD l (y i)) = H.V.map (Per.θD l) *ᵥ (fun k => Per.θD l ((W *ᵥ y) k)) := by
      funext i
      conv_lhs => rw [hyw]
      exact RingHom.map_mulVec _ _ _ i
    have hdiag : Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) *ᵥ (fun k => Per.θD l ((W *ᵥ y) k)) =
        z ^ ((p : ℤ) - q) • (fun k => Per.θD l ((W *ᵥ y) k)) := by
      funext k
      rw [Matrix.mulVec_diagonal, hkey k]; rfl
    rw [hθy, Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hdiag, Matrix.mulVec_smul]
  · intro hHT
    ext i j
    have h := hHT K' (H.p j) H.q (fun i => H.Q i j) (fun i => H.V i j) ?_ ?_
    · have := congrFun h i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mul_diagonal, Matrix.map_apply, Matrix.mul_apply]
      simp only [Matrix.map_apply]
      rw [this, mul_comm]
    · intro g hg
      funext i
      have := congrFun (congrFun (H.inv g hg) i) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    · intro i; exact H.Q_eq i j
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsHodgeTateIffDiagonalAdaptedBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHodgeTate_iff_diagonal_adapted_basis : ∀ (l : ℕ) [Fact l.Prime] (K K' : FinExt l) (C : Core l), C.InvdR → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (H : Hodge C ξ ρ K') (z : ℂ_[l]) (u : Matrix (Fin a) (Fin a) (ℂ_[l])), K.1 ≤ K'.1 → (u * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((H.p i : ℤ) - H.q)) ↔ IsHT C ξ ρ z u) := by
  first | exact @GlobalTheory.BKLim.isHT_iff_diag | exact GlobalTheory.BKLim.isHT_iff_diag | (intros; apply GlobalTheory.BKLim.isHT_iff_diag; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePowEqAlongLatticeTowerCover
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePowEqAlongLatticeTowerCover
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
noncomputable section

namespace GlobalTheory.CoverTrace

section Ultra

variable {E : Type} [NormedField E] [IsUltrametricDist E]

theorem norm_dot_le {ι : Type} [Fintype ι] {x y : ι → E} {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hx : ∀ i, ‖x i‖ ≤ α) (hy : ∀ i, ‖y i‖ ≤ β) : ‖x ⬝ᵥ y‖ ≤ α * β := by
  unfold dotProduct
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hα hβ) fun i _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hx i) (hy i) (norm_nonneg _) hα

theorem norm_mulVec_le {ι κ : Type} [Fintype κ] {A : Matrix ι κ E} {y : κ → E} {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : ∀ i j, ‖A i j‖ ≤ α) (hy : ∀ j, ‖y j‖ ≤ β) (i : ι) :
    ‖(A *ᵥ y) i‖ ≤ α * β :=
  norm_dot_le hα hβ (fun j => hA i j) hy

theorem norm_mul_le' {ι κ μ : Type} [Fintype κ] {A : Matrix ι κ E} {C : Matrix κ μ E} {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : ∀ i j, ‖A i j‖ ≤ α) (hC : ∀ i j, ‖C i j‖ ≤ β) (i : ι) (k : μ) :
    ‖(A * C) i k‖ ≤ α * β := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hα hβ) fun j _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA i j) (hC j k) (norm_nonneg _) hα

theorem norm_pow_le {ι : Type} [Fintype ι] [DecidableEq ι] {U : Matrix ι ι E} {B : ℝ} (hB : 1 ≤ B)
    (hU : ∀ i j, ‖U i j‖ ≤ B) (n : ℕ) (i j : ι) : ‖(U ^ n) i j‖ ≤ B ^ n := by
  induction n generalizing i j with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ', pow_succ']
    exact norm_mul_le' (by linarith) (pow_nonneg (by linarith) n) hU ih i j

theorem norm_comm_pow_le {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {U : Matrix ι ι E} {U' : Matrix κ κ E} {P : Matrix ι κ E} {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hU : ∀ i j, ‖U i j‖ ≤ B) (hU' : ∀ i j, ‖U' i j‖ ≤ B) (hc : ∀ i j, ‖(U * P - P * U') i j‖ ≤ δ)
    (n : ℕ) (i : ι) (j : κ) : ‖(U ^ n * P - P * U' ^ n) i j‖ ≤ B ^ n * δ := by
  induction n generalizing i j with
  | zero => simp [hδ]
  | succ n ih =>
    have e : U ^ (n + 1) * P - P * U' ^ (n + 1) = U * (U ^ n * P - P * U' ^ n) + (U * P - P * U') * U' ^ n := by
      rw [pow_succ', pow_succ', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      abel
    have hB0 : 0 ≤ B := by linarith
    have hBn : 1 ≤ B ^ n := one_le_pow₀ hB
    rw [e, Matrix.add_apply]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · have := norm_mul_le' hB0 (mul_nonneg (pow_nonneg hB0 n) hδ) hU ih i j
      calc _ ≤ _ := this
        _ = B ^ (n + 1) * δ := by ring
    · have := norm_mul_le' hδ (pow_nonneg hB0 n) hc (norm_pow_le hB hU' n) i j
      calc _ ≤ _ := this
        _ ≤ B ^ (n + 1) * δ := by
          rw [pow_succ]
          nlinarith [mul_nonneg (mul_nonneg hδ (pow_nonneg hB0 n)) (sub_nonneg.2 hB)]

theorem core {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι ι E) (U' : Matrix κ κ E) (P : Matrix ι κ E) (t v : ι → E) (v' T' : κ → E)
    (B τ ε δ : ℝ) (hB : 1 ≤ B) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hU : ∀ i j, ‖U i j‖ ≤ B) (hU' : ∀ i j, ‖U' i j‖ ≤ B) (ht : ∀ i, ‖t i‖ ≤ τ) (hv' : ∀ s, ‖v' s‖ ≤ 1)
    (hv : ∀ i, ‖(v - P *ᵥ v') i‖ ≤ ε) (hc : ∀ i j, ‖(U * P - P * U') i j‖ ≤ δ)
    (hT : ∀ s, ‖(t ᵥ* P - T') s‖ ≤ ε) (n : ℕ) :
    ‖(U ^ n *ᵥ v) ⬝ᵥ t - (U' ^ n *ᵥ v') ⬝ᵥ T'‖ ≤ B ^ n * ε * τ + B ^ n * δ * τ + B ^ n * ε := by
  have hB0 : 0 ≤ B := by linarith
  have hBn : 0 ≤ B ^ n := pow_nonneg hB0 n
  have e1 : ((P * U' ^ n) *ᵥ v') ⬝ᵥ t = (U' ^ n *ᵥ v') ⬝ᵥ (t ᵥ* P) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
  have e2 : U ^ n *ᵥ (P *ᵥ v') = (U ^ n * P) *ᵥ v' := Matrix.mulVec_mulVec _ _ _
  have e : (U ^ n *ᵥ v) ⬝ᵥ t - (U' ^ n *ᵥ v') ⬝ᵥ T' =
      (U ^ n *ᵥ (v - P *ᵥ v')) ⬝ᵥ t + ((U ^ n * P - P * U' ^ n) *ᵥ v') ⬝ᵥ t + (U' ^ n *ᵥ v') ⬝ᵥ (t ᵥ* P - T') := by
    rw [Matrix.mulVec_sub, Matrix.sub_mulVec, sub_dotProduct, sub_dotProduct, dotProduct_sub, e1, e2]
    ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact norm_dot_le (mul_nonneg hBn hε) hτ (norm_mulVec_le hBn hε (norm_pow_le hB hU n) hv) ht
  · have := norm_dot_le (mul_nonneg (mul_nonneg hBn hδ) zero_le_one) hτ
      (norm_mulVec_le (mul_nonneg hBn hδ) zero_le_one (norm_comm_pow_le hB hδ hU hU' hc n) hv') ht
    simpa using this
  · have := norm_dot_le (mul_nonneg hBn zero_le_one) hε (norm_mulVec_le hBn zero_le_one (norm_pow_le hB hU' n) hv') hT
    simpa [mul_comm] using this

theorem eq_zero_of_le_pow {x K r : ℝ} (hx : 0 ≤ x) (hK : 0 ≤ K) (hr0 : 0 ≤ r) (hr : r < 1)
    (h : ∀ N : ℕ, x ≤ K * r ^ N) : x = 0 := by
  by_contra hne
  have hpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hpos (by linarith : (0 : ℝ) < K + 1)) hr
  have h1 : (K + 1) * r ^ N < x := by
    rw [lt_div_iff₀ (by linarith)] at hN; linarith
  have h2 := h N
  nlinarith [pow_nonneg hr0 N]

end Ultra

section Concrete

variable {l : ℕ} [Fact l.Prime]

theorem norm_zC (x : ℤ_[l]) : ‖((algebraMap (Om l) ℂ_[l]).comp (zOm l)) x‖ = ‖x‖ := by
  show ‖((zOm l x : Om l) : ℂ_[l])‖ = ‖x‖
  rw [PadicComplex.norm_extends]
  show ‖algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] x)‖ = ‖x‖
  rw [PadicAlgCl.norm_extends]
  exact PadicInt.padic_norm_e_of_padicInt x

theorem norm_zC_le_of_dvd {x : ℤ_[l]} {m : ℕ} (h : (l : ℤ_[l]) ^ m ∣ x) :
    ‖((algebraMap (Om l) ℂ_[l]).comp (zOm l)) x‖ ≤ ((l : ℝ) ^ m)⁻¹ := by
  obtain ⟨y, rfl⟩ := h
  rw [norm_zC, norm_mul, norm_pow, PadicInt.norm_p, inv_pow]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one y)

theorem norm_gal_C (σ : GQ l) (x : Om l) : ‖algebraMap (Om l) ℂ_[l] (σ x)‖ = ‖x‖ := by
  show ‖((σ x : Om l) : ℂ_[l])‖ = ‖x‖
  rw [PadicComplex.norm_extends]
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem gal_zOm (σ : GQ l) (x : ℤ_[l]) : σ (zOm l x) = zOm l x := by
  show σ (algebraMap ℚ_[l] (Om l) (algebraMap ℤ_[l] ℚ_[l] x)) = _
  rw [AlgEquiv.commutes]
  rfl

theorem trace_sum_smul_map {a : ℕ} {ι : Type} [Fintype ι] (w : ι → ℂ_[l])
    (M : ι → Matrix (Fin a) (Fin a) (Om l)) (f : Om l →+* ℂ_[l]) :
    (∑ i, w i • (M i).map f).trace = w ⬝ᵥ fun i => f (M i).trace := by
  rw [Matrix.trace_sum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, smul_eq_mul]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.trace, map_sum]

end Concrete

theorem trace_pow_eq : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (L₀ : FinExt l) (a : ℕ), 1 ≤ a → ∀ (r : Γ →* GL (Fin a) (Om l)) (Cl : Set (Γ →* GL (Fin a) (Om l))) (Cv : Cover L₀ r Cl) (σ : GQ l) (U : Matrix (Fin Cv.d) (Fin Cv.d) (ℂ_[l])) (U' : ∀ m, Matrix (Fin (Cv.tw.d' m)) (Fin (Cv.tw.d' m)) (ℂ_[l])) (Bd : ℝ) (S : ℕ → ℂ_[l]), S 0 = a → (∀ i j, ‖U i j‖ ≤ Bd) → (∀ m i j, ‖U' m i j‖ ≤ Bd) → (∀ n, ∃ m, n ≤ m ∧ ∀ i j, ‖(U * (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) - (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U' m) i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹) → (∀ m k n, (∑ i, ((U' m ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l ((Cv.lay m).e s))) i • ((Cv.lay m).b i k).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = S n) → ∀ n, (∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (Cv.e s))) i • (Cv.b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = S n := by
  intro l _ Γ _ _ L₀ a ha r Cl Cv σ U U' Bd S hS0 hU hU' hcomm htr
  let f : Om l →+* ℂ_[l] := (algebraMap (Om l) ℂ_[l]).comp (σ : Om l →+* Om l)
  let Z : ℤ_[l] →+* ℂ_[l] := (algebraMap (Om l) ℂ_[l]).comp (zOm l)
  have hfZ : ∀ x, f (zOm l x) = Z x := fun x => by
    show algebraMap (Om l) ℂ_[l] (σ (zOm l x)) = _
    rw [gal_zOm]; rfl
  have hfn : ∀ x, ‖f x‖ = ‖x‖ := norm_gal_C σ
  let t : Fin Cv.d → ℂ_[l] := fun i => f (Cv.b i).trace
  let v : Fin Cv.d → ℂ_[l] := fun s => Z (Cv.e s)
  have key' : ∀ m k n, (U' m ^ n *ᵥ (fun s => Z ((Cv.lay m).e s))) ⬝ᵥ (fun s => f ((Cv.lay m).b s k).trace) = S n :=
    fun m k n => by rw [← htr m k n]; exact (trace_sum_smul_map _ _ f).symm
  intro n
  rw [show (∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (Cv.e s))) i •
      (Cv.b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = (U ^ n *ᵥ v) ⬝ᵥ t from trace_sum_smul_map _ _ f]
  have hX0 : (U ^ 0 *ᵥ v) ⬝ᵥ t = a := by
    rw [pow_zero, Matrix.one_mulVec]
    have h1 := congrArg (fun M => f M.trace) Cv.reads.one
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace_sum, Matrix.trace_smul, map_sum, smul_eq_mul, map_mul, hfZ, Matrix.trace_one,
      Fintype.card_fin, map_natCast] at h1
    simpa [dotProduct, v, t] using h1
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  set B : ℝ := max Bd 1 with hBdef
  have hB : 1 ≤ B := le_max_right _ _
  have hB0 : 0 ≤ B := by linarith
  set τ : ℝ := ∑ i, ‖t i‖ with hτdef
  have hτ : 0 ≤ τ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have ht : ∀ i, ‖t i‖ ≤ τ := fun i => Finset.single_le_sum (fun j _ => norm_nonneg (t j)) (Finset.mem_univ i)
  have est : ∀ N : ℕ, ∃ C : ℂ_[l], ∀ n, ‖(U ^ n *ᵥ v) ⬝ᵥ t - C * S n‖ ≤
      (B ^ n * τ + B ^ n * B * τ + B ^ n) * ((l : ℝ) ^ N)⁻¹ := by
    intro N
    obtain ⟨m, hmN, hm⟩ := hcomm N
    have hεN : 0 ≤ ((l : ℝ) ^ N)⁻¹ := inv_nonneg.2 (pow_nonneg hl0.le N)
    have hε : ((l : ℝ) ^ m)⁻¹ ≤ ((l : ℝ) ^ N)⁻¹ := inv_anti₀ (pow_pos hl0 N) (pow_le_pow_right₀ hl1.le hmN)
    let P : Matrix (Fin Cv.d) (Fin (Cv.tw.d' m)) ℂ_[l] := (Cv.tw.Pi m).map Z
    let v' : Fin (Cv.tw.d' m) → ℂ_[l] := fun s => Z ((Cv.lay m).e s)
    let t' : Fin (Cv.lay m).m → Fin (Cv.tw.d' m) → ℂ_[l] := fun k s => f ((Cv.lay m).b s k).trace
    let T' : Fin (Cv.tw.d' m) → ℂ_[l] := ∑ k, f ((Cv.lay m).c k) • t' k
    refine ⟨∑ k, f ((Cv.lay m).c k), fun n => ?_⟩
    have hT'n : (U' m ^ n *ᵥ v') ⬝ᵥ T' = (∑ k, f ((Cv.lay m).c k)) * S n := by
      simp only [T', dotProduct_sum, dotProduct_smul, smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by rw [key' m k n]
    rw [← hT'n]
    have hv' : ∀ s, ‖v' s‖ ≤ 1 := fun s => (norm_zC _).trans_le (PadicInt.norm_le_one _)
    have hv : ∀ i, ‖(v - P *ᵥ v') i‖ ≤ ((l : ℝ) ^ N)⁻¹ := by
      intro i
      have e : (P *ᵥ v') i = Z ((Cv.tw.Pi m *ᵥ (Cv.lay m).e) i) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp [P, v', Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [Pi.sub_apply, e, norm_sub_rev, ← map_sub]
      have hd := Cv.unit m i
      rw [Pi.sub_apply] at hd
      exact (norm_zC_le_of_dvd hd).trans hε
    have hc : ∀ i j, ‖(U * P - P * U' m) i j‖ ≤ B * ((l : ℝ) ^ N)⁻¹ := fun i j =>
      (hm i j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hεN)
    have hT : ∀ s, ‖(t ᵥ* P - T') s‖ ≤ ((l : ℝ) ^ N)⁻¹ := by
      intro s
      have h := Cv.trace m s
      have e : (t ᵥ* P - T') s = f ((∑ i, zOm l (Cv.tw.Pi m i s) • Cv.b i).trace -
          ∑ k, (Cv.lay m).c k * ((Cv.lay m).b s k).trace) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, Matrix.trace_sum, map_sum, map_sum]
        simp only [Pi.sub_apply, Matrix.vecMul, dotProduct, T', t', t, P, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.trace_smul, map_mul, hfZ, Matrix.map_apply]
        congr 1
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [e, hfn]
      exact h.trans hε
    have hc' := core U (U' m) P t v v' T' B τ (((l : ℝ) ^ N)⁻¹) (B * ((l : ℝ) ^ N)⁻¹) hB hτ hεN
      (mul_nonneg hB0 hεN) (fun i j => (hU i j).trans (le_max_left _ _))
      (fun i j => (hU' m i j).trans (le_max_left _ _)) ht hv' hv hc hT n
    calc _ ≤ _ := hc'
      _ = _ := by ring
  have ha0 : (a : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hapos : 0 < ‖(a : ℂ_[l])‖ := norm_pos_iff.2 ha0
  have hKn : 0 ≤ B ^ n * τ + B ^ n * B * τ + B ^ n := by
    have := pow_nonneg hB0 n
    have h2 := mul_nonneg this hτ
    have h3 := mul_nonneg (mul_nonneg this hB0) hτ
    linarith
  have hK0 : 0 ≤ B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0 := by
    have h3 := mul_nonneg hB0 hτ
    simp only [pow_zero, one_mul]
    linarith
  have hbound : ∀ N : ℕ, ‖(U ^ n *ᵥ v) ⬝ᵥ t - S n‖ ≤
      ((B ^ n * τ + B ^ n * B * τ + B ^ n) + (B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0) * ‖S n‖ / ‖(a : ℂ_[l])‖) *
        ((l : ℝ)⁻¹) ^ N := by
    intro N
    obtain ⟨C, hC⟩ := est N
    have h0 := hC 0
    rw [hX0, hS0] at h0
    have hC1 : ‖C - 1‖ * ‖(a : ℂ_[l])‖ ≤ (B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0) * ((l : ℝ) ^ N)⁻¹ := by
      rw [← norm_mul, show (C - 1) * (a : ℂ_[l]) = -((a : ℂ_[l]) - C * a) by ring, norm_neg]
      exact h0
    have hCb : ‖C - 1‖ ≤ (B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0) * ((l : ℝ) ^ N)⁻¹ / ‖(a : ℂ_[l])‖ := by
      rw [le_div_iff₀ hapos]; exact hC1
    rw [show (U ^ n *ᵥ v) ⬝ᵥ t - S n = ((U ^ n *ᵥ v) ⬝ᵥ t - C * S n) + (C - 1) * S n by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    calc _ ≤ (B ^ n * τ + B ^ n * B * τ + B ^ n) * ((l : ℝ) ^ N)⁻¹ +
          (B ^ 0 * τ + B ^ 0 * B * τ + B ^ 0) * ((l : ℝ) ^ N)⁻¹ / ‖(a : ℂ_[l])‖ * ‖S n‖ :=
          add_le_add (hC n) (mul_le_mul_of_nonneg_right hCb (norm_nonneg _))
      _ = _ := by rw [inv_pow]; field_simp
  have hz := eq_zero_of_le_pow (norm_nonneg _)
    (add_nonneg hKn (div_nonneg (mul_nonneg hK0 (norm_nonneg _)) (norm_nonneg _)))
    (inv_nonneg.2 hl0.le) (inv_lt_one_of_one_lt₀ hl1) hbound
  exact sub_eq_zero.1 (norm_eq_zero.1 hz)

end GlobalTheory.CoverTrace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePowEqAlongLatticeTowerCoverStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pow_eq_along_latticeTowerCover : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (L₀ : FinExt l) (a : ℕ), 1 ≤ a → ∀ (r : Γ →* GL (Fin a) (Om l)) (Cl : Set (Γ →* GL (Fin a) (Om l))) (Cv : Cover L₀ r Cl) (σ : GQ l) (U : Matrix (Fin Cv.d) (Fin Cv.d) (ℂ_[l])) (U' : ∀ m, Matrix (Fin (Cv.tw.d' m)) (Fin (Cv.tw.d' m)) (ℂ_[l])) (Bd : ℝ) (S : ℕ → ℂ_[l]), S 0 = a → (∀ i j, ‖U i j‖ ≤ Bd) → (∀ m i j, ‖U' m i j‖ ≤ Bd) → (∀ n, ∃ m, n ≤ m ∧ ∀ i j, ‖(U * (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) - (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U' m) i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹) → (∀ m k n, (∑ i, ((U' m ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l ((Cv.lay m).e s))) i • ((Cv.lay m).b i k).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = S n) → ∀ n, (∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (Cv.e s))) i • (Cv.b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = S n := by
  first | exact @GlobalTheory.CoverTrace.trace_pow_eq | exact GlobalTheory.CoverTrace.trace_pow_eq | (intros; apply GlobalTheory.CoverTrace.trace_pow_eq; all_goals assumption)
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CovClose

variable {l : ℕ} [Fact l.Prime]

theorem exists_gal_inv {K : FinExt l} (τ' : ↥K.1 →ₐ[ℚ_[l]] Om l) : ∃ σ : GQ l, ∀ x : ↥K.1, σ (τ' x) = (x : Om l) := by
  let φ : Om l →ₐ[ℚ_[l]] Om l := τ'.liftNormal (Om l)
  have hb : Function.Bijective φ := Algebra.IsAlgebraic.algHom_bijective φ
  let e : Om l ≃ₐ[ℚ_[l]] Om l := AlgEquiv.ofBijective φ hb
  refine ⟨e.symm, fun x => ?_⟩
  have h1 : φ (algebraMap ↥K.1 (Om l) x) = τ' x := AlgHom.liftNormal_commutes τ' (Om l) x
  have h2 : e (x : Om l) = τ' x := h1
  rw [← h2]
  exact e.symm_apply_apply _

def modelOf {Γ : Type} [Group Γ] {a : ℕ} (ρ₁ : Γ →* GL (Fin a) (Om l)) (L : FinExt l)
    (h : ∀ g i j, (ρ₁ g).val i j ∈ L.1) : Γ →* GL (Fin a) ↥L.1 :=
  MonoidHom.toHomUnits
    { toFun := fun g => Matrix.of fun i j => (⟨(ρ₁ g).val i j, h g i j⟩ : ↥L.1)
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, Units.val_one, Matrix.one_apply, map_one]
        split_ifs <;> simp
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply, Units.val_mul] }

theorem modelOf_apply {Γ : Type} [Group Γ] {a : ℕ} (ρ₁ : Γ →* GL (Fin a) (Om l)) (L : FinExt l)
    (h : ∀ g i j, (ρ₁ g).val i j ∈ L.1) (g : Γ) (i j : Fin a) :
    (((modelOf ρ₁ L h g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j := by
  simp [modelOf]

def repOf {Γ : Type} [Group Γ] {a : ℕ} {L : FinExt l} (r : Γ →* GL (Fin a) ↥L.1) :
    Representation ↥L.1 Γ (Fin a → ↥L.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ↥L.1 ≃ₐ[↥L.1] _) : _ →* _).comp ((Units.coeHom _).comp r)

theorem repOf_apply {Γ : Type} [Group Γ] {a : ℕ} {L : FinExt l} (r : Γ →* GL (Fin a) ↥L.1) (g : Γ) (v : Fin a → ↥L.1) :
    repOf r g v = (r g).val *ᵥ v := by
  simp [repOf, Matrix.toLinAlgEquiv'_apply]

theorem isSst_resQ' (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsSst P (GlobalTheory.PstCoeff.resQ ρ) := by
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : Module.finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) =
      Module.finrank ℚ_[l] LL * Module.finrank LL ↥(Dst P ρ) := by
    rw [hD, Module.finrank_mul_finrank]
    rfl
  rw [IsSst, e, h, ← Module.finrank_mul_finrank ℚ_[l] LL V]
  ring

theorem isDR_of_isSst (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) {K L : FinExt l} {a : ℕ}
    (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)) (h : IsSst P R) : Formalism.MainNotions.N.IsDR (P.PD K) R := by
  haveI := L.2
  haveI : FiniteDimensional ℚ_[l] (Fin a → ↥L.1) := Module.Finite.trans ↥L.1 _
  exact (GlobalTheory.PstCoeff.isDR_resQ_iff P R).mp
    (GlobalTheory.sst_isDR l P AI T K _ (GlobalTheory.PstCoeff.resQ R) (isSst_resQ' P R h))

theorem conj_diag {k : Type} [Field k] {a : ℕ} (W : Matrix (Fin a) (Fin a) k) (hW : IsUnit W) (d : Fin a → k) :
    (W * diagonal d * W⁻¹) * W = W * diagonal d ∧
      ∀ n : ℕ, ((W * diagonal d * W⁻¹) ^ n).trace = ∑ i, d i ^ n := by
  have hdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det W).mp hW
  refine ⟨by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul W hdet, Matrix.mul_one], fun n => ?_⟩
  have e : W⁻¹ = ((hW.unit⁻¹ : (Matrix (Fin a) (Fin a) k)ˣ) : Matrix (Fin a) (Fin a) k) := by
    rw [Matrix.coe_units_inv, IsUnit.unit_spec]
  have e2 : W * diagonal d * W⁻¹ = ((hW.unit : (Matrix (Fin a) (Fin a) k)ˣ) : Matrix (Fin a) (Fin a) k) * diagonal d *
      ((hW.unit⁻¹ : (Matrix (Fin a) (Fin a) k)ˣ) : Matrix (Fin a) (Fin a) k) := by
    rw [← e, IsUnit.unit_spec]
  rw [e2, Units.conj_pow]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  rfl

theorem map_eq_of_count {a : ℕ} (f : Fin a → ℤ) (J : Multiset ℤ)
    (h : ∀ n : ℤ, (((Finset.univ.filter fun i => f i = n).card : ℕ) : ℤ) = (J.count n : ℤ)) :
    Finset.univ.val.map f = J := by
  ext n
  rw [Multiset.count_map]
  have h1 : (Multiset.filter (fun i => n = f i) Finset.univ.val).card =
      (Finset.univ.filter fun i => f i = n).card := by
    rw [Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr fun x _ => eq_comm
  rw [h1]
  exact_mod_cast h n

theorem sum_pow_eq {k : Type} [Field k] {a : ℕ} (f : Fin a → ℤ) (z : k) (n : ℕ) :
    ∑ i, (z ^ f i) ^ n = ((Finset.univ.val.map f).map fun h => (z ^ h) ^ n).sum := by
  rw [Multiset.map_map]
  rfl

theorem lay_pos {Γ : Type} [Group Γ] [TopologicalSpace Γ] {a : ℕ} (ha : 1 ≤ a) {L₀ : FinExt l}
    {r : Γ →* GL (Fin a) (Om l)} {Cl : Set (Γ →* GL (Fin a) (Om l))} (Cv : Cover L₀ r Cl) : 0 < (Cv.lay 1).m := by
  by_contra hm
  have hm0 : (Cv.lay 1).m = 0 := by omega
  have hd' : Cv.tw.d' 1 = 0 := by
    by_contra hd
    have h0 := (Cv.lay 1).indep.ne_zero ⟨0, by omega⟩
    apply h0
    funext k
    exact absurd k.2 (by omega)
  haveI : IsEmpty (Fin (Cv.tw.d' 1)) := by rw [hd']; infer_instance
  have hd : Cv.d = 0 := by
    by_contra hd
    obtain ⟨S, hS⟩ := (Cv.tw.onto 1).surj
    have h1 := hS ⟨0, by omega⟩ ⟨0, by omega⟩
    have h1' : (l : ℤ_[l]) ∣ 1 := by simpa [Matrix.mul_apply, Matrix.one_apply] using h1
    have hu := PadicInt.isUnit_iff.mp (isUnit_of_dvd_one h1')
    rw [PadicInt.norm_p] at hu
    have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    rw [inv_eq_one] at hu
    linarith
  haveI : IsEmpty (Fin Cv.d) := by rw [hd]; infer_instance
  have h1 := Cv.reads.one
  simp at h1
  have h2 := congrFun (congrFun h1 ⟨0, ha⟩) ⟨0, ha⟩
  simp at h2

end GlobalTheory.CovClose

namespace GlobalTheory.CovClose


set_option maxHeartbeats 1000000 in
theorem closed_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ), 1 ≤ a → (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L₀.1) → ∀ (r : ↥(GK K) →* GL (Fin a) (Om l)) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (Cv : Cover L₀ r Cl) (J : (↥K.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ), (∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD K) R τ n = ((J (L.1.val.comp τ)).count n : ℤ))) → ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (r g).val i j) → Formalism.MainNotions.N.IsDR (P.PD K) R ∧ (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD K) R τ n = ((J (L.1.val.comp τ)).count n : ℤ)) ∧ ((∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsCrys (P.PD K) R)) → IsCrys (P.PD K) R) := by
  intro l _ K L₀ P AI T a ha hL₀ r Cl Cv J hCl L r' R hL hR hr'
  obtain ⟨bk⟩ := GlobalTheory.BSP.nonempty_bk_of_finExt l K
  obtain ⟨τp, hτp⟩ := GlobalTheory.BSP.exists_isPer l K bk
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hCd : C.InvdR := hC.invdR
  have hξ : Ideal.span {bk.ev bk.E} = RingHom.ker (Per.θ l) := bk.span_ev
  haveI := K.2

  let N : ℕ := Finset.univ.sup fun τ' : ↥K.1 →ₐ[ℚ_[l]] Om l => ((J τ').map Int.natAbs).sup
  have hN : ∀ τ', ∀ n ∈ J τ', |n| ≤ (N : ℤ) := by
    intro τ' n hn
    rw [Int.abs_eq_natAbs]
    have h1 : n.natAbs ≤ ((J τ').map Int.natAbs).sup := Multiset.le_sup (Multiset.mem_map_of_mem _ hn)
    have h2 : ((J τ').map Int.natAbs).sup ≤ N :=
      Finset.le_sup (f := fun τ' : ↥K.1 →ₐ[ℚ_[l]] Om l => ((J τ').map Int.natAbs).sup) (Finset.mem_univ τ')
    exact_mod_cast h1.trans h2

  have hsstCl : ∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R :=
    fun ρ₁ h L r' R h1 h2 h3 => (hCl ρ₁ h L r' R h1 h2 h3).1
  have hsst : ∀ m, IsSst P (qRep (Cv.tw.ρ' m)) := fun m =>
    (GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer l K L₀ P AI T a Cl _ (Cv.tw.ρ' m) (Cv.lay m)).1 hsstCl
  have hfr : ∀ m, ∃ F : Frame bk N (Cv.tw.d' m) (fun g => (Cv.tw.ρ' m g).val),
      F.IsDR ∧ (IsCrys (P.PD K) (qRep (Cv.tw.ρ' m)) → F.IsCr) := fun m =>
    GlobalTheory.T.exists_breuilKisinFrame_semistable_boundedJumps l K bk τp hτp P AI T N _ (Cv.tw.ρ' m) (Cv.cont' m) (hsst m)
      (GlobalTheory.T.layer_DdR_bounds_alt l K L₀ P AI T a Cl J N hL₀ hN _ (Cv.tw.ρ' m) (Cv.lay m) hCl)
  choose F hFdr hFcr using hfr
  obtain ⟨F₀, hF₀dr, hF₀cr, rr, hlink⟩ := GlobalTheory.T.exists_deRhamFrame_limitLattice_breuilKisinTower l K bk τp hτp Cv.d N Cv.ρ Cv.tw F hFdr
  have hdr0 : Formalism.MainNotions.N.IsDR (P.PD K) (qRep Cv.ρ) := GlobalTheory.T.isDeRham_of_breuilKisinFrame_isDeRham l K bk τp hτp P AI T N Cv.d Cv.ρ F₀ hF₀dr
  have hread := GlobalTheory.T.deRham_crystalline_of_lattice_reads l K L₀ P AI T a Cv.d Cv.ρ r Cv.b Cv.e Cv.reads L r' R hL hR hr'
  have hdrR : Formalism.MainNotions.N.IsDR (P.PD K) R := hread.1 hdr0
  refine ⟨hdrR, ?_, fun hcr => hread.2 (GlobalTheory.T.isCrys_of_crystallineBreuilKisinFrame l K bk τp hτp P AI T N Cv.d Cv.ρ F₀
    (hF₀cr fun m => hFcr m ((GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer l K L₀ P AI T a Cl _ (Cv.tw.ρ' m) (Cv.lay m)).2 hcr)))⟩

  intro τK
  obtain ⟨σ, hσ⟩ := exists_gal_inv (L.1.val.comp τK)
  have hσ' : ∀ x : ↥K.1, σ ((τK x : ↥L.1) : Om l) = (x : Om l) := hσ
  obtain ⟨g, z, hz, hzr⟩ := GlobalTheory.T.exists_galois_elem_cyclotomic_period_not_root_of_unity l K bk
  have hz0 : z ≠ 0 := by
    obtain ⟨w, -, hw⟩ := hz
    rintro rfl
    simp at hw

  have hex : ∀ m, ∃ (H : Hodge C (bk.ev bk.E) (fun g => (Cv.tw.ρ' m g).val.map (zOm l)) K)
      (Y : Matrix (Fin (Cv.tw.d' m)) (Fin (Cv.tw.d' m)) (Ainf l))
      (U' : Matrix (Fin (Cv.tw.d' m)) (Fin (Cv.tw.d' m)) ℂ_[l]),
      Y.map (inclW l) = inclW l τp ^ N • (F m).T ∧
      U' * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * ((F m).ε g).map ((Per.θD l).comp (aDp l)) ∧
      U' * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal fun i => z ^ ((H.p i : ℤ) - H.q) := by
    intro m
    obtain ⟨H, -⟩ := GlobalTheory.T.exists_hodge_basis_deRham_lattice l K P AI T C hC (bk.ev bk.E) hξ _ (Cv.tw.ρ' m)
      (GlobalTheory.sst_isDR l P AI T K _ (qRep (Cv.tw.ρ' m)) (hsst m))
    obtain ⟨Y, -, hY, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τp hτp N _ _ (F m).toPre
    obtain ⟨U', h1, h2⟩ := (GlobalTheory.T.adaptedBasis_theta_galoisFixed_poles l K bk τp hτp C hCd N _ _ (F m) Y (hFdr m) hY H).1 g z hz
    exact ⟨H, Y, U', hY, h1, h2⟩
  choose Hm Ym U' hYm hU'Y hU'V using hex
  obtain ⟨H0, -⟩ := GlobalTheory.T.exists_hodge_basis_deRham_lattice l K P AI T C hC (bk.ev bk.E) hξ _ Cv.ρ hdr0
  obtain ⟨Y0, -, hY0, -⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τp hτp N _ _ F₀.toPre
  obtain ⟨U, hUY, hUV⟩ := (GlobalTheory.T.adaptedBasis_theta_galoisFixed_poles l K bk τp hτp C hCd N _ _ F₀ Y0 hF₀dr hY0 H0).1 g z hz
  obtain ⟨Bd, hBd⟩ := GlobalTheory.T.theta_conj_bounded_compatible_breuilKisin_frames l K bk τp hτp N
  have hBdm := fun (m n : ℕ) => hBd N Cv.d (Cv.tw.d' m) n _ _ F₀ (F m) Y0 (Ym m) rfl hY0 (hYm m) g U (U' m) hUY (hU'Y m)
  have hUb : ∀ i j, ‖U i j‖ ≤ Bd := (hBdm 0 0).1
  have hU'b : ∀ m i j, ‖U' m i j‖ ≤ Bd := fun m => (hBdm m 0).2.1
  have hcomp : ∀ n, ∃ m, n ≤ m ∧ ∀ i j, ‖(U * (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) -
      (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U' m) i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹ := by
    intro n
    obtain ⟨m, hnm, R₁, -, hdiv, -⟩ := hlink n
    exact ⟨m, hnm, (hBdm m n).2.2 (Cv.tw.Pi m) R₁
      (fun g i j => (pow_dvd_pow _ hnm).trans ((Cv.tw.onto m).equi g i j)) hdiv⟩

  let S : ℕ → ℂ_[l] := fun n => ((J (L.1.val.comp τK)).map fun h => (z ^ h) ^ n).sum

  have hlay : ∀ m (k : Fin (Cv.lay m).m), ∃ u : Matrix (Fin a) (Fin a) ℂ_[l], ∀ n,
      (∑ i, ((U' m ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l ((Cv.lay m).e s))) i •
        ((Cv.lay m).b i k).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = (u ^ n).trace ∧
      (u ^ n).trace = S n := by
    intro m k
    let rk := modelOf ((Cv.lay m).rep k) ((Cv.lay m).L k) ((Cv.lay m).rep_mem k)
    have hrk : ∀ g i j, (((rk g).val i j : ↥((Cv.lay m).L k).1) : Om l) = ((Cv.lay m).rep k g).val i j :=
      fun g i j => modelOf_apply _ _ _ g i j
    obtain ⟨hsk, hmk⟩ := hCl ((Cv.lay m).rep k) ((Cv.lay m).mem k) ((Cv.lay m).L k) rk (repOf rk) ((Cv.lay m).le k) (repOf_apply rk) hrk
    let τk : ↥K.1 →ₐ[ℚ_[l]] ↥((Cv.lay m).L k).1 :=
      (L.1.val.comp τK).codRestrict ((Cv.lay m).L k).1.toSubalgebra (fun x => (Cv.lay m).le k (hL₀ _ x))
    have hσk : ∀ x : ↥K.1, σ ((τk x : ↥((Cv.lay m).L k).1) : Om l) = (x : Om l) := hσ
    obtain ⟨K', Hk, hKK', hcard⟩ := GlobalTheory.T.exists_hodge_basis_at_embedding l K ((Cv.lay m).L k) P AI T C hC (bk.ev bk.E) hξ a rk (repOf rk)
      (repOf_apply rk) (isDR_of_isSst P AI T _ hsk) τk σ hσk
    have hcτ : ((Cv.lay m).L k).1.val.comp τk = L.1.val.comp τK := AlgHom.ext fun _ => rfl
    have hms : Finset.univ.val.map (fun i => (Hk.p i : ℤ) - Hk.q) = J (L.1.val.comp τK) :=
      map_eq_of_count _ _ fun n => by rw [hcard n, hmk τk n, hcτ]
    have hW : IsUnit (Hk.V.map (Per.θD l)) := Hk.unit.map (Per.θD l).mapMatrix
    obtain ⟨huW, htr⟩ := conj_diag _ hW fun i => z ^ ((Hk.p i : ℤ) - Hk.q)
    have hHT := (GlobalTheory.T.isHodgeTate_iff_diagonal_adapted_basis l K K' C hCd (bk.ev bk.E) hξ a _ Hk z _ hKK').1 huW
    have hρ : (fun g => (rk g).val.map fun x => σ (x : Om l)) = fun g => ((Cv.lay m).rep k g).val.map σ := by
      funext g
      ext i j
      simp only [Matrix.map_apply, hrk]
    have hmv : ∀ u, IsHT C (bk.ev bk.E) (fun g => (rk g).val.map fun x => σ (x : Om l)) z u →
        IsHT C (bk.ev bk.E) (fun g => ((Cv.lay m).rep k g).val.map σ) z u := fun u h => hρ ▸ h
    replace hHT := hmv _ hHT
    refine ⟨Hk.V.map (Per.θD l) * Matrix.diagonal (fun i => z ^ ((Hk.p i : ℤ) - Hk.q)) * (Hk.V.map (Per.θD l))⁻¹,
      fun n => ⟨?_, ?_⟩⟩
    · exact (congrArg Matrix.trace (GlobalTheory.T.hodgeTateOperator_pow_eq_sum l K C (bk.ev bk.E) a _ (Cv.tw.ρ' m) ((Cv.lay m).rep k) (fun s => (Cv.lay m).b s k) (Cv.lay m).e
        ((Cv.lay m).reads k) σ z (Hm m) (U' m) _ (hU'V m) hHT n)).symm
    · rw [htr n, sum_pow_eq (fun i => (Hk.p i : ℤ) - Hk.q) z n, hms]
  have hS0 : S 0 = a := by
    obtain ⟨u, hu⟩ := hlay 1 ⟨0, lay_pos ha Cv⟩
    rw [← (hu 0).2, pow_zero, Matrix.trace_one, Fintype.card_fin]
  have hlayS : ∀ m k n, (∑ i, ((U' m ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l ((Cv.lay m).e s))) i •
      ((Cv.lay m).b i k).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = S n := by
    intro m k n
    obtain ⟨u, hu⟩ := hlay m k
    exact (hu n).1.trans (hu n).2
  have hcov := GlobalTheory.T.trace_pow_eq_along_latticeTowerCover l (↥(GK K)) L₀ a ha r Cl Cv σ U U' Bd S hS0 hUb hU'b hcomp hlayS

  obtain ⟨K', HR, hKK', hcard⟩ := GlobalTheory.T.exists_hodge_basis_at_embedding l K L P AI T C hC (bk.ev bk.E) hξ a r' R hR hdrR τK σ hσ'
  have hW : IsUnit (HR.V.map (Per.θD l)) := HR.unit.map (Per.θD l).mapMatrix
  obtain ⟨huW, htr⟩ := conj_diag _ hW fun i => z ^ ((HR.p i : ℤ) - HR.q)
  have hHT := (GlobalTheory.T.isHodgeTate_iff_diagonal_adapted_basis l K K' C hCd (bk.ev bk.E) hξ a _ HR z _ hKK').1 huW
  have hρ : (fun g => (r' g).val.map fun x => σ (x : Om l)) = fun g => (r g).val.map σ := by
    funext g
    ext i j
    simp only [Matrix.map_apply, hr']
  have hmv : ∀ u, IsHT C (bk.ev bk.E) (fun g => (r' g).val.map fun x => σ (x : Om l)) z u →
      IsHT C (bk.ev bk.E) (fun g => (r g).val.map σ) z u := fun u h => hρ ▸ h
  replace hHT := hmv _ hHT
  have hnat := GlobalTheory.T.hodgeTateOperator_pow_eq_sum l K C (bk.ev bk.E) a Cv.d Cv.ρ r Cv.b Cv.e Cv.reads σ z H0 U _ hUV hHT
  have hpow : ∀ n : ℕ, ((Finset.univ.val.map fun i => (HR.p i : ℤ) - HR.q).map fun h => (z ^ h) ^ n).sum =
      ((J (L.1.val.comp τK)).map fun h => (z ^ h) ^ n).sum := by
    intro n
    rw [← sum_pow_eq]
    exact (htr n).symm.trans ((congrArg Matrix.trace (hnat n)).trans (hcov n))
  have hms := GlobalTheory.T.multiset_eq_of_power_sums_zpow_eq ℂ_[l] z hz0 hzr _ _ hpow
  intro n
  rw [← hcard n, ← hms, Multiset.count_map]
  have h1 : (Multiset.filter (fun i => n = (HR.p i : ℤ) - HR.q) Finset.univ.val).card =
      (Finset.univ.filter fun i => (HR.p i : ℤ) - HR.q = n).card := by
    rw [Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr fun x _ => eq_comm
  rw [h1]

end GlobalTheory.CovClose
