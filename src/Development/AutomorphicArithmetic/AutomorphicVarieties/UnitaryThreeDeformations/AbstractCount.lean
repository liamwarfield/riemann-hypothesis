module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsCoord
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsRelations
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TangentCoordEqZeroOfNonposWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPtOfIsPtHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CzBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TypeIOfTwoSigned
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ContinuousCompOfFilteredContinuity

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.NormTwoEqOne
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem norm_two_eq_one {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [CharZero O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (h : IsUnit (2 : O)) : ‖(2 : PadicAlgCl l)‖ = 1 := by
  have h2 : IsUnit (2 : ℤ_[l]) := by
    by_contra hn
    have hl : (l : ℤ) ∣ 2 := by
      rw [PadicInt.isUnit_iff] at hn
      have hlt : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one _) (by simpa using hn)
      exact PadicInt.norm_int_lt_one_iff_dvd 2 |>.1 hlt
    have hinj : Function.Injective (algebraMap ℤ_[l] O) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      by_contra hx0
      have e := PadicInt.unitCoeff_spec hx0
      rw [e, map_mul, map_pow, map_natCast] at hx
      rcases mul_eq_zero.1 hx with h1 | h1
      · exact ((Units.isUnit _).map (algebraMap ℤ_[l] O)).ne_zero h1
      · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
    haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    exact hn (isUnit_of_map_unit (algebraMap ℤ_[l] O) 2 (by rwa [map_ofNat]))
  have h3 : ‖(2 : ℚ_[l])‖ = 1 := by
    have := PadicInt.isUnit_iff.1 h2
    rw [PadicInt.norm_def] at this
    exact_mod_cast this
  rw [← map_ofNat (algebraMap ℚ_[l] (PadicAlgCl l)) 2, norm_algebraMap', h3]

theorem UpperTheory.V.UnitaryThreeInertia.conj_of_matIso :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ g₁, F.Marked g₁ → ∀ (r : Γ →* GG (m := 3) (R := PadicAlgCl l)), F.IsCharZeroPt g₁ r →
      ∀ r' : Γ →* GG (m := 3) (R := PadicAlgCl l), F.IsCharZeroPt g₁ r' → TypeI F.η r →
        MatIso F.η.ker (mats r) (mats r') → ∃ t, r' = conjBy (tor (PadicAlgCl l) t) r := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg r hr r' hr' hI hiso
  obtain ⟨m, n, -, hz, hz1, -⟩ := isCharZeroPt_basic F hF g₁ hg r hr
  obtain ⟨m', n', -, hz', hz1', -⟩ := isCharZeroPt_basic F hF g₁ hg r' hr'
  refine conjBy_tor_of_iso F.η r r' F.c g₁ two_ne_zero m m' hF.ηc hg.1 n n' ?_ ?_ ?_ (Or.inl hI) hiso
  · rw [← norm_ne_zero_iff, hz1]; exact one_ne_zero
  · rw [← norm_ne_zero_iff, hz1']; exact one_ne_zero
  · intro e
    have h2 := norm_two_eq_one (l := l) hF.two
    have hle := IsUltrametricDist.norm_add_le_max
      (zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)))
      (-(zeta F.c g₁ r' - zeta F.c g₁ (F.rz (PadicAlgCl l))))
    rw [norm_neg] at hle
    have hlt := lt_of_le_of_lt hle (max_lt hz hz')
    have e2 : zeta F.c g₁ r - zeta F.c g₁ (F.rz (PadicAlgCl l)) +
        -(zeta F.c g₁ r' - zeta F.c g₁ (F.rz (PadicAlgCl l))) = 2 * zeta F.c g₁ r := by
      rw [e]; ring
    rw [e2, norm_mul, h2, hz1, mul_one] at hlt
    exact lt_irrefl _ hlt
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsPtHomAct
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem exists_act {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ]
    {R : Type} [CommRing R] [Algebra O R] (u : Γ →* GG (m := 3) (R := R)) (W : WPres O ℤ R)
    (hW : ∀ j, W.part j = wpart O u j) {K : Type} [CommRing K] [Algebra O K] (ξ : Sring (O := O) u →ₐ[O] K) (t : Kˣ) :
    ∃ ξt : Sring (O := O) u →ₐ[O] K, ∀ (j : ℤ) x (hx : x ∈ wpart O u j),
      ξt ⟨x, mem_Sring u hx⟩ = ((t ^ j : Kˣ) : K) * ξ ⟨x, mem_Sring u hx⟩ := by
  have hA : W.A = Sring (O := O) u := by
    ext x
    show x ∈ ⨆ j, W.part j ↔ x ∈ ⨆ j, wpart O u j
    simp only [hW]
  refine ⟨(act W.gr (zpowersHom Kˣ t) (ξ.comp (Subalgebra.inclusion hA.le))).comp
    (Subalgebra.inclusion hA.ge), fun j x hx => ?_⟩
  have hx' : Subalgebra.inclusion hA.ge ⟨x, mem_Sring u hx⟩ ∈ W.gr j := by
    show x ∈ W.part j
    rwa [hW]
  rw [AlgHom.comp_apply, act_of_mem W.gr _ _ hx']
  rfl

theorem UpperTheory.V.UnitaryThreeInertia.isPtHom_act :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
      (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    Module.Finite O (wpart O u 0) →
    ∀ (ξ : Sring (O := O) u →ₐ[O] (PadicAlgCl l)) (r : Γ →* GG (m := 3) (R := PadicAlgCl l)), IsPtHom u ξ r →
    ∀ (ξ' : Sring (O := O) u →ₐ[O] (PadicAlgCl l)) (t : (PadicAlgCl l)ˣ), IsPtHom u ξ' (conjBy (tor (PadicAlgCl l) t) r) ↔
      ∀ (j : ℤ) x (hx : x ∈ wpart O u j), ξ' ⟨x, mem_Sring u hx⟩ = ((t ^ j : (PadicAlgCl l)ˣ) : (PadicAlgCl l)) * ξ ⟨x, mem_Sring u hx⟩ := by
  intro l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg R _ _ _ u hu hfin ξ r hr ξ' t
  obtain ⟨hm, hri, -⟩ := conjBy_tor r t
  constructor
  · intro h
    obtain ⟨W, hW, -⟩ := exists_adapted F hF g₁ hg u hu
    obtain ⟨ξt, hξt⟩ := exists_act u W hW.part ξ t
    have e : ξ' = ξt := by
      refine AlgHom.ext_of_eq_adjoin (sring_eq_adjoin F hF g₁ hg u hu hfin).1 ?_
      rintro _ ⟨g, a, b, -, rfl⟩
      refine Eq.trans ?_ (hξt _ _ (entry_mem u g a b)).symm
      have h1 := congrFun (congrFun (h g).2 a) b
      rw [hm, (hr g).2] at h1
      exact h1.symm
    rw [e]
    exact hξt
  · intro h g
    refine ⟨(hri g).trans (hr g).1, ?_⟩
    ext a b
    rw [hm, (hr g).2]
    exact (h _ _ (entry_mem u g a b)).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.NormBoundOfIntegralValues
open IsLocalRing UpperTheory.V.Alg

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem norm_abs (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)]
    (a : O) (ha : a ≠ 0) :
    ‖algebraMap O (PadicAlgCl l) a‖ ^ (UpperTheory.V.Base.eO l O).toNat =
      ((l : ℝ)⁻¹) ^ (IsDiscreteValuationRing.addVal O a).toNat := by
  have hle : ∀ x : O, ‖algebraMap O (PadicAlgCl l) x‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).algebraMap)
  have hu : ∀ u : Oˣ, ‖algebraMap O (PadicAlgCl l) (u : O)‖ = 1 := by
    intro u
    have h1 : ‖algebraMap O (PadicAlgCl l) (u : O)‖ * ‖algebraMap O (PadicAlgCl l) ((u⁻¹ : Oˣ) : O)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : Oˣ)
    have h4 := norm_nonneg (algebraMap O (PadicAlgCl l) (u : O))
    nlinarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have key : ∀ x : O, x ≠ 0 → ‖algebraMap O (PadicAlgCl l) x‖ =
      ‖algebraMap O (PadicAlgCl l) ϖ‖ ^ (IsDiscreteValuationRing.addVal O x).toNat := by
    intro x hx
    obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [IsDiscreteValuationRing.addVal_def x u hϖ n h, h]
    simp [hu]
  have hl0 : (l : O) ≠ 0 := by
    intro h
    have h' : algebraMap O (PadicAlgCl l) (l : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h'
  have hl : ‖algebraMap O (PadicAlgCl l) (l : O)‖ = (l : ℝ)⁻¹ := by
    have : algebraMap O (PadicAlgCl l) (l : O) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have he : UpperTheory.V.Base.eO l O = IsDiscreteValuationRing.addVal O (l : O) :=
    (UpperTheory.V.Base.dvrFacts l O).2.2.2.2.2.2.2.1
  rw [he, ← hl, key a ha, key _ hl0, ← pow_mul, ← pow_mul, mul_comm]

theorem UpperTheory.norm_bound_of_integral_values :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)],
        IsNVal O (PadicAlgCl l) (fun x => ((UpperTheory.V.Base.eO l O).toNat : ℝ) * UpperTheory.V.UnitaryThreeInertia.vl1 l x) := by
  intro l _ O _ _ _ _ _ _ _ _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hv : ∀ x, UpperTheory.V.UnitaryThreeInertia.vl1 l x = -Real.logb l ‖x‖ := fun x => by
    rw [UpperTheory.V.UnitaryThreeInertia.vl1, Real.logb, neg_div]
  simp only [hv]
  refine ⟨fun x y hx hy => ?_, fun x y hx hy hxy => ?_, fun a ha => ?_⟩
  · rw [norm_mul, Real.logb_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy)]
    ring
  · have h := IsUltrametricDist.norm_add_le_max x y
    have hp := norm_pos_iff.2 hxy
    rcases le_max_iff.1 h with h | h
    · refine min_le_of_left_le (mul_le_mul_of_nonneg_left (neg_le_neg ?_) (Nat.cast_nonneg _))
      exact Real.logb_le_logb_of_le hl hp h
    · refine min_le_of_right_le (mul_le_mul_of_nonneg_left (neg_le_neg ?_) (Nat.cast_nonneg _))
      exact Real.logb_le_logb_of_le hl hp h
  · have h := congrArg (Real.logb l) (norm_abs l O a ha)
    rw [Real.logb_pow, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one hl] at h
    linarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.PtSign
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem wtPart_decomp {O σ : Type} [CommRing O] (wt : σ → ℤ) (j : ℤ) (s : Finset σ) :
    ∀ f ∈ wtPart O wt j, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → MvPowerSeries.coeff n f = 0) →
      ∃ g : σ → MvPowerSeries σ O, (∀ i, g i ∈ wtPart O wt (j - wt i)) ∧
        f = ∑ i ∈ s, MvPowerSeries.X i * g i := by
  classical
  intro f hf hs
  let P : (σ →₀ ℕ) → σ → Prop := fun n i => ∃ h : ∃ k ∈ s, n k ≠ 0, h.choose = i
  let g : σ → MvPowerSeries σ O := fun i m =>
    if P (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hg : ∀ i m, MvPowerSeries.coeff m (g i) =
      if P (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 :=
    fun _ _ => rfl
  refine ⟨g, fun i m hm => ?_, ?_⟩
  · rw [hg]
    split_ifs
    · apply hf
      rw [map_add (f := _)]
      intro h
      apply hm
      have : (Finsupp.weight wt) (Finsupp.single i 1) = wt i := by
        rw [Finsupp.weight_apply, Finsupp.sum_single_index] <;> simp
      omega
    · rfl
  · have key : ∀ n i, MvPowerSeries.coeff n (MvPowerSeries.X i * g i) =
        if P n i then MvPowerSeries.coeff n f else 0 := by
      intro n i
      rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
      by_cases hle : Finsupp.single i 1 ≤ n
      · rw [if_pos hle, one_mul, hg, tsub_add_cancel_of_le hle]
      · have hP : ¬ P n i := by
          rintro ⟨h, hc⟩
          apply hle
          rw [Finsupp.single_le_iff, ← hc]
          exact Nat.one_le_iff_ne_zero.mpr h.choose_spec.2
        rw [if_neg hle, if_neg hP]
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [key]
    by_cases h : ∃ k ∈ s, n k ≠ 0
    · have hP : ∀ i, P n i ↔ h.choose = i := fun i => ⟨fun ⟨_, e⟩ => e, fun e => ⟨h, e⟩⟩
      simp_rw [hP]
      rw [Finset.sum_ite_eq, if_pos h.choose_spec.1]
    · have hP : ∀ i, ¬ P n i := fun i ⟨h', _⟩ => h h'
      simp only [hP, if_false, Finset.sum_const_zero]
      push_neg at h
      exact hs n h

private theorem vanish_of_entries {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ]
    (F : Frame O G Γ ι) {R : Type} [CommRing R] [Algebra O R] (u : Γ →* GG (m := 3) (R := R)) (W : WPres O ℤ R)
    (hW : F.Adapted u W) {K : Type} [CommRing K] [Algebra O K] (ξ : Sring (O := O) u →ₐ[O] K) (M : AddSubmonoid ℤ)
    (h : ∀ g, F.η g = 1 → ∀ a b, wt a b ∉ M → ptMat u ξ g a b = 0) (j : ℤ) (hj : j ∉ M) (x : R)
    (hx : x ∈ wpart (O := O) u j) : ξ ⟨x, mem_Sring u hx⟩ = 0 := by
  classical
  haveI := W.fin
  have hmemz : ∀ i, W.z i ∈ Sring (O := O) u := fun i =>
    mem_Sring u (j := W.wt i) (by rw [← hW.part]; exact W.z_mem i)
  have hzero : ∀ i, W.wt i ∉ M → ξ ⟨W.z i, hmemz i⟩ = 0 := by
    intro i hi
    obtain ⟨g, a, b, hη, hw, hz⟩ := hW.var i
    have hab : a ≠ b := by
      rintro rfl
      apply hi
      rw [hw]
      simp [wt]
    have hrz : ((F.rz R) g).mat a b = 0 := by
      show algebraMap O R ((((tor O) (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) a b) = 0
      rw [tor_val, Matrix.diagonal_apply_ne _ hab, map_zero]
    have h1 : ξ ⟨W.z i, hmemz i⟩ = ptMat u ξ g a b := by
      show ξ ⟨W.z i, hmemz i⟩ = ξ ⟨(u g).mat a b, _⟩
      congr 1
      exact Subtype.ext (show W.z i = (u g).mat a b by rw [hz, hrz, sub_zero])
    rw [h1]
    exact h g hη a b (hw ▸ hi)
  rw [← hW.part] at hx
  obtain ⟨f, hf, hfx⟩ := hx
  subst hfx
  let s := Finset.univ.filter (fun i => W.wt i ∉ M)
  have hs : ∀ n : W.σ →₀ ℕ, (∀ i ∈ s, n i = 0) → MvPowerSeries.coeff n f = 0 := by
    intro n hn
    apply hf
    intro hw
    apply hj
    rw [← hw, Finsupp.weight_apply]
    refine AddSubmonoid.sum_mem M fun c hc => ?_
    by_cases hcM : W.wt c ∈ M
    · exact nsmul_mem hcM _
    · exact absurd (hn c (by simp [s, hcM])) (Finsupp.mem_support_iff.mp hc)
  obtain ⟨g, hg, hfg⟩ := wtPart_decomp W.wt j s f hf hs
  have hmemg : ∀ i, W.π (g i) ∈ Sring (O := O) u := fun i =>
    mem_Sring u (j := j - W.wt i) (by rw [← hW.part]; exact ⟨g i, hg i, rfl⟩)
  have hsum : (⟨W.π.toLinearMap f, mem_Sring u (by rw [← hW.part]; exact ⟨f, hf, rfl⟩)⟩ : Sring (O := O) u) =
      ∑ i ∈ s, (⟨W.z i, hmemz i⟩ : Sring (O := O) u) * ⟨W.π (g i), hmemg i⟩ := by
    apply Subtype.ext
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hfg, map_sum, WPres.z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [map_mul, hzero i (Finset.mem_filter.mp hi).2, zero_mul]

theorem UpperTheory.V.UnitaryThreeInertia.isPtHom_sign :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    ∀ {K : Type} [CommRing K] [Algebra O K] (ξ : Sring (O := O) u →ₐ[O] K)
    (r : Γ →* GG (m := 3) (R := K)), IsPtHom u ξ r →
      (Upper F.η r ↔ ∀ j < 0, ∀ x (hx : x ∈ wpart (O := O) u j), ξ ⟨x, mem_Sring u hx⟩ = 0) ∧
      (Lower F.η r ↔ ∀ j > 0, ∀ x (hx : x ∈ wpart (O := O) u j), ξ ⟨x, mem_Sring u hx⟩ = 0) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg₁ R _ _ _ u hu K _ _ ξ r hr
  obtain ⟨W, hW, _⟩ := exists_adapted F hF g₁ hg₁ u hu
  have hent : ∀ g a b, (r g).mat a b = ptMat u ξ g a b := fun g a b => by rw [(hr g).2]
  let Mp : AddSubmonoid ℤ :=
    { carrier := {n | 0 ≤ n}
      add_mem' := by
        intro a b ha hb
        show 0 ≤ a + b
        exact add_nonneg ha hb
      zero_mem' := le_refl (0 : ℤ) }
  let Mn : AddSubmonoid ℤ :=
    { carrier := {n | n ≤ 0}
      add_mem' := by
        intro a b ha hb
        show a + b ≤ 0
        exact add_nonpos ha hb
      zero_mem' := le_refl (0 : ℤ) }
  have hMp : ∀ n : ℤ, n ∈ Mp ↔ 0 ≤ n := fun _ => Iff.rfl
  have hMn : ∀ n : ℤ, n ∈ Mn ↔ n ≤ 0 := fun _ => Iff.rfl
  refine ⟨⟨fun hU j hj x hx => ?_, fun hv g hg a b hab => ?_⟩, ⟨fun hL j hj x hx => ?_, fun hv g hg a b hab => ?_⟩⟩
  · refine vanish_of_entries F u W hW ξ Mp (fun g hg a b hab => ?_) j (by rw [hMp]; omega) x hx
    rw [← hent]
    exact hU g ((MonoidHom.mem_ker).mpr hg) a b (by rw [hMp] at hab; omega)
  · rw [hent]
    exact hv (wt a b) hab _ (entry_mem u g a b)
  · refine vanish_of_entries F u W hW ξ Mn (fun g hg a b hab => ?_) j (by rw [hMn]; omega) x hx
    rw [← hent]
    exact hL g ((MonoidHom.mem_ker).mpr hg) a b (by rw [hMn] at hab; omega)
  · rw [hent]
    exact hv (wt a b) hab _ (entry_mem u g a b)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.PrecompleteOfPowLe
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia.MP

section Tsz

variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]

private theorem tsz_local [IsLocalRing O] : IsLocalRing (TrivSqZeroExt O M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _

private theorem tsz_mem_max [IsLocalRing O] [IsLocalRing (TrivSqZeroExt O M)] (x : TrivSqZeroExt O M) :
    x ∈ maximalIdeal (TrivSqZeroExt O M) ↔ x.fst ∈ maximalIdeal O := by
  simp [TrivSqZeroExt.isUnit_iff_isUnit_fst]

private theorem precomplete_of_pow_le {A : Type} [CommRing A] {I J : Ideal A} (hJ : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [IsPrecomplete J A] : IsPrecomplete I A :=
  _root_.UpperTheory.Reformulated.B.Qk41.precomplete_of_pow_le hJ he

private theorem tsz_isCO [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    [Module.Finite O M] : IsCO O (TrivSqZeroExt O M) := by
  have h1 : IsLocalRing (TrivSqZeroExt O M) := tsz_local
  have h2 : Module.Finite O (TrivSqZeroExt O M) := inferInstanceAs (Module.Finite O (O × M))
  have h3 := IsNoetherianRing.of_finite O (TrivSqZeroExt O M)
  have h4 := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal O) (TrivSqZeroExt O M)
  have hJ : (maximalIdeal O).map (algebraMap O (TrivSqZeroExt O M)) ≤ maximalIdeal _ := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, tsz_mem_max]
    exact hx
  have he : maximalIdeal (TrivSqZeroExt O M) ^ 2 ≤ (maximalIdeal O).map (algebraMap O (TrivSqZeroExt O M)) := by
    rw [pow_two, Ideal.mul_le]
    intro x hx y hy
    rw [tsz_mem_max] at hx hy
    have : x * y = algebraMap O _ x.fst * y + algebraMap O _ y.fst * TrivSqZeroExt.inr x.snd := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx))
      (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hy))
  have h5 := precomplete_of_pow_le hJ he
  exact { complete := ⟨⟩
          isLocalHom := ⟨fun a ha => by simpa [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.algebraMap_eq_inl] using ha⟩
          res_surj := fun x => ⟨x.fst, by rw [tsz_mem_max]; simp [TrivSqZeroExt.algebraMap_eq_inl]⟩ }

end Tsz

section PS

variable {O A σ : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype σ]

private theorem exists_sum_X_mul (p : MvPowerSeries σ O) (hp : MvPowerSeries.constantCoeff p = 0) :
    ∃ r : σ → MvPowerSeries σ O, p = ∑ i, MvPowerSeries.X i * r i := by
  classical
  have hc : ∀ n : σ →₀ ℕ, n ≠ 0 → ∃ i, n i ≠ 0 := fun n hn => by
    by_contra h
    push Not at h
    exact hn (Finsupp.ext h)
  choose c hc using hc
  let q : σ → MvPowerSeries σ O := fun i n =>
    if h : n ≠ 0 then (if c n h = i then MvPowerSeries.coeff n p else 0) else 0
  have hq : ∀ i n, MvPowerSeries.coeff n (q i) =
      if h : n ≠ 0 then (if c n h = i then MvPowerSeries.coeff n p else 0) else 0 := fun _ _ => rfl
  have hs : p = ∑ i, q i := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hq]
    by_cases h : n ≠ 0
    · simp [dif_pos h]
    · simp only [dif_neg h, Finset.sum_const_zero]
      push Not at h
      subst h
      simpa using hp
  have hd : ∀ i, MvPowerSeries.X i ∣ q i := fun i => by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [hq]
    split_ifs with h1 h2
    · exact absurd (h2 ▸ hm) (hc m h1)
    · rfl
    · rfl
  choose r hr using hd
  exact ⟨r, hs.trans (Finset.sum_congr rfl fun i _ => hr i)⟩

private theorem coeff_X_mul (i j : σ) (r : MvPowerSeries σ O) [DecidableEq σ] :
    MvPowerSeries.coeff (Finsupp.single j 1) (MvPowerSeries.X i * r) =
      if i = j then MvPowerSeries.constantCoeff r else 0 := by
  split_ifs with h
  · subst h
    have := MvPowerSeries.coeff_add_monomial_mul (m := Finsupp.single i 1) (n := 0) (φ := r) (1 : O)
    simpa [MvPowerSeries.X_def] using this
  · exact MvPowerSeries.X_dvd_iff.1 (dvd_mul_right _ _) _ (Finsupp.single_eq_of_ne h)

private theorem map_lin (φ : MvPowerSeries σ O →ₐ[O] A)
    (hφ : ∀ i j, φ (MvPowerSeries.X i) * φ (MvPowerSeries.X j) = 0) (p : MvPowerSeries σ O) :
    φ p = algebraMap O A (MvPowerSeries.constantCoeff p) +
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) p • φ (MvPowerSeries.X i) := by
  classical
  have h0 : ∀ p : MvPowerSeries σ O, ∃ r : σ → MvPowerSeries σ O,
      p = algebraMap O _ (MvPowerSeries.constantCoeff p) + ∑ i, MvPowerSeries.X i * r i := fun p => by
    obtain ⟨r, hr⟩ := exists_sum_X_mul (p - algebraMap O _ (MvPowerSeries.constantCoeff p))
      (by simp [MvPowerSeries.algebraMap_apply])
    exact ⟨r, by rw [← hr]; ring⟩
  have h1 : ∀ i (r : MvPowerSeries σ O), φ (MvPowerSeries.X i * r) =
      MvPowerSeries.constantCoeff r • φ (MvPowerSeries.X i) := fun i r => by
    obtain ⟨s, hs⟩ := h0 r
    conv_lhs => rw [hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_add (f := _), map_sum, AlgHom.commutes, mul_add, Finset.mul_sum, ← mul_assoc, hφ, zero_mul,
      Finset.sum_const_zero, add_zero, Algebra.smul_def]
    exact mul_comm _ _
  obtain ⟨r, hr⟩ := h0 p
  have h2 : ∀ j, MvPowerSeries.coeff (Finsupp.single j 1) p = MvPowerSeries.constantCoeff (r j) := fun j => by
    conv_lhs => rw [hr]
    simp [coeff_X_mul, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
  conv_lhs => rw [hr]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, AlgHom.commutes, h1, h2]

end PS

section Point

private def Tm (C : Type) [CommRing C] : Matrix (Fin 3) (Fin 3) C := !![0, 0, 0; 1, 0, 0; 0, -1, 0]

private theorem Tm_wt (C : Type) [CommRing C] (a b : Fin 3) (h : wt a b ≠ -1) : Tm C a b = 0 := by
  fin_cases a <;> fin_cases b <;> first | rfl | exact absurd rfl h

private theorem deform_eq {D C : Type} [Group D] [CommRing C] {r r' r'' : D →* GG (m := 3) (R := C)}
    {γ : D → Matrix (Fin 3) (Fin 3) C} (h' : IsDeform r γ r') (h'' : IsDeform r γ r'') : r' = r'' :=
  MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ((h' g).2.trans (h'' g).2.symm))
    ((h' g).1.trans (h'' g).1.symm)

variable {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] (F : Frame O G Γ ι)
  (C : Type) [CommRing C] [Algebra O C]

private theorem rz_eq : F.rz C = r0 F.η ((Units.map (algebraMap O C).toMonoidHom).comp F.Ψ) := by
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
  show ((tor O (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O).map (algebraMap O C) = (tor C _ : GL (Fin 3) C)
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  rw [MonoidHom.comp_apply, ← map_zpow (Units.map (algebraMap O C).toMonoidHom)]
  rfl

private theorem rz_mat (g : Γ) : (F.rz C g).mat = Matrix.diagonal fun i => algebraMap O C (psi F.Ψ i g) := by
  show ((tor O (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O).map (algebraMap O C) = _
  rw [tor_val, Matrix.diagonal_map (map_zero _)]
  rfl

private theorem ad_Tm (g : Γ) (x : C) :
    adRep (F.rz C) g (x • Tm C) = (algebraMap O C ((F.Ψ g)⁻¹ : Oˣ) * x) • Tm C := by
  rw [rz_eq]
  ext a b
  rw [adRep_baseLift_apply]
  have h : (if F.η g = 1 then (x • Tm C) a b else -(x • Tm C) b.rev a.rev) = x * Tm C a b := by
    split_ifs
    · rfl
    · fin_cases a <;> fin_cases b <;> simp [Tm, Fin.rev]
  rw [h]
  by_cases hw : wt a b = -1
  · rw [hw, _root_.zpow_neg_one, MonoidHom.comp_apply, ← map_inv, Matrix.smul_apply, smul_eq_mul, mul_assoc]
    rfl
  · simp [Tm_wt C a b hw]

end Point

private theorem exists_pt
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι]
    (F : Frame O G Γ ι) (hF : F.Ok) (g₁ : Γ) {C : Type} [CommRing C] [IsLocalRing C] [Algebra O C]
    [IsLocalHom (algebraMap O C)] (I : Ideal C) (hI : I * I = ⊥) (hIm : I ≤ maximalIdeal C) (ζ : Γ → C)
    (hζ : ∀ g, ζ g ∈ I) (hlc : IsLocallyConstant ζ)
    (hcoc : ∀ g h, ζ (g * h) = ζ g + algebraMap O C ((F.Ψ g)⁻¹ : Oˣ) * ζ h)
    (hU : ∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, ζ (F.loc v s) = 0)
    (hT : ∀ v ∈ F.Tb, ∃ m ∈ I, ∀ g : F.D v, ζ (F.loc v g) = algebraMap O C ((F.Ψ (F.loc v g))⁻¹ : Oˣ) * m - m)
    (hN : algebraMap O C (F.Ψ g₁) * ζ g₁ = algebraMap O C (F.Ψ (gstar F.c g₁)) * ζ (gstar F.c g₁)) :
    ∃ r : Γ →* GG (m := 3) (R := C), F.IsPt g₁ r ∧
      ∀ g a b, (r g).mat a b = (F.rz C g).mat a b + algebraMap O C (Tm O a b * psi F.Ψ b g) * ζ g := by
  have h0 := isPt_rz F hF g₁ (R := C)
  have hent : ∀ x ∈ I, EntIn I (x • Tm C) := fun x hx a b => I.mul_mem_right _ hx
  obtain ⟨r, hr⟩ := exists_isDeform I (F.rz C) (fun g => ζ g • Tm C) hI (fun g => hent _ (hζ g))
    (fun g h => by simp only [ad_Tm, hcoc, add_smul])
  have hr2 : ∀ g, (r g).mat = (1 + ζ g • Tm C) * (F.rz C g).mat := fun g => (hr g).2
  have hT' : ∀ a b, algebraMap O C (Tm O a b) = Tm C a b := fun a b => by
    fin_cases a <;> fin_cases b <;> simp [Tm]
  have hm : ∀ g a b, (r g).mat a b = (F.rz C g).mat a b + algebraMap O C (Tm O a b * psi F.Ψ b g) * ζ g := by
    intro g a b
    rw [hr2, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, rz_mat, Matrix.mul_diagonal, map_mul, hT',
      Matrix.smul_apply, smul_eq_mul]
    ring
  have hc : ζ F.c = 0 := by
    have h1 : ζ 1 = 0 := by simpa using hcoc 1 1
    have h2 := hcoc F.c F.c
    rw [hF.csq, h1, hF.Ψc] at h2
    have h3 : algebraMap O C 2 * ζ F.c = 0 := by
      rw [map_ofNat, two_mul]; simpa using h2.symm
    exact (hF.two.map (algebraMap O C)).mul_right_eq_zero.1 h3
  refine ⟨r, ⟨⟨⟨⟨fun g => (hr g).1, fun g a b => ?_⟩, fun v => ?_⟩, ⟨?_, ?_, ?_⟩⟩, fun n => ?_⟩, hm⟩
  · have := h0.red g a b
    rw [Matrix.sub_apply] at this ⊢
    rw [hm, add_sub_right_comm]
    exact add_mem this (Ideal.mul_mem_left _ _ (hIm (hζ g)))
  · by_cases hv : v ∈ F.Tb
    · obtain ⟨m, hmI, hmv⟩ := hT v hv
      obtain ⟨h, hh, hd⟩ := isDeform_cob I ((F.rz C).comp (F.loc v)) ((-m) • Tm C) hI (hent _ (neg_mem hmI))
      have e : r.comp (F.loc v) = conjBy h ((F.rz C).comp (F.loc v)) := by
        refine deform_eq (fun g => ?_) hd
        have e1 : cob ((F.rz C).comp (F.loc v)) ((-m) • Tm C) g = ζ (F.loc v g) • Tm C := by
          show (-m) • Tm C - adRep (F.rz C) (F.loc v g) ((-m) • Tm C) = _
          rw [ad_Tm, hmv, ← sub_smul]
          congr 1
          ring
        rw [e1]
        exact hr (F.loc v g)
      rw [e]
      refine (cond_conj F h fun a b => ?_).1 v _ (h0.loc v)
      rw [hh, add_sub_cancel_left]
      exact hIm (hent _ (neg_mem hmI) a b)
    · refine ⟨fun e => absurd (e ▸ Set.mem_insert _ _) hv, fun e => absurd (Set.mem_insert_of_mem _ e) hv,
        fun _ s hs => ?_⟩
      refine Eq.trans ?_ ((h0.loc v).2.2 hv s hs)
      refine SemidirectProduct.ext (Units.ext ?_) (hr _).1
      have := hr2 (F.loc v s)
      rw [hU v hv s hs, zero_smul, add_zero, Matrix.one_mul] at this
      exact this
  · rw [hr2, hc, zero_smul, add_zero, Matrix.one_mul, h0.norm.atc]
  · have := h0.norm.z12
    simp only [zmat, Matrix.sub_apply] at this ⊢
    rw [hm, hm]
    simpa [Tm] using this
  · have := h0.norm.z21
    simp only [zmat, Matrix.sub_apply] at this ⊢
    rw [hm, hm]
    have e : ∀ g, Tm O 1 0 * psi F.Ψ 0 g = F.Ψ g := fun g => by simp [Tm, psi, wt1]
    rw [e, e, hN, add_sub_add_right_eq_sub, this]
  · have e : (fun g => (r g).mat.map (Ideal.Quotient.mk (maximalIdeal C ^ n))) = fun g =>
        (1 + ζ g • Tm C).map (Ideal.Quotient.mk (maximalIdeal C ^ n)) *
          (F.rz C g).mat.map (Ideal.Quotient.mk (maximalIdeal C ^ n)) := by
      funext g
      rw [hr2, Matrix.map_mul]
    rw [e]
    exact (hlc.comp fun x => (1 + x • Tm C).map (Ideal.Quotient.mk (maximalIdeal C ^ n))).mul (h0.cont n)

private theorem coord
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι]
    (F : Frame O G Γ ι) (hF : F.Ok) (g₁ : Γ) {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (u : Γ →* GG (m := 3) (R := R)) (hu : F.IsUniv g₁ u)
    (W : WPres O ℤ R) (g : W.σ → Γ) (a b : W.σ → Fin 3)
    (hz : ∀ i, W.z i = (u (g i)).mat (a i) (b i) - (F.rz R (g i)).mat (a i) (b i))
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] (n : Γ → M) (hlc : IsLocallyConstant n)
    (hcoc : ∀ g h, n (g * h) = n g + (((F.Ψ g)⁻¹ : Oˣ) : O) • n h)
    (hU : ∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, n (F.loc v s) = 0)
    (hT : ∀ v ∈ F.Tb, ∃ m, ∀ g : F.D v, n (F.loc v g) = (((F.Ψ (F.loc v g))⁻¹ : Oˣ) : O) • m - m)
    (hN : (F.Ψ g₁ : O) • n g₁ = (F.Ψ (gstar F.c g₁) : O) • n (gstar F.c g₁)) :
    (∀ p, W.π p = 0 → ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) p •
      ((Tm O (a i) (b i) * psi F.Ψ (b i) (g i)) • n (g i)) = 0) ∧
    ((∀ i, (Tm O (a i) (b i) * psi F.Ψ (b i) (g i)) • n (g i) = 0) → n = 0) := by
  letI : Module Oᵐᵒᵖ M := Module.compHom M ((RingHom.id O).fromOpposite mul_comm)
  haveI : IsCentralScalar O M := ⟨fun _ _ => rfl⟩
  haveI : IsCO O (TrivSqZeroExt O M) := tsz_isCO
  have hmul : ∀ (c : O) (m : M), algebraMap O (TrivSqZeroExt O M) c * TrivSqZeroExt.inr m =
      TrivSqZeroExt.inr (c • m) := fun c m => TrivSqZeroExt.inl_mul_inr c m
  let I : Ideal (TrivSqZeroExt O M) := RingHom.ker (TrivSqZeroExt.fstHom O O M)
  have hI : ∀ x, x ∈ I ↔ x.fst = 0 := fun x => Iff.rfl
  obtain ⟨r, hr, hm⟩ := exists_pt F hF g₁ I
    (by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      rw [hI] at hx hy
      rw [Ideal.mem_bot]
      ext <;> simp [hx, hy])
    (fun x hx => by rw [tsz_mem_max, (hI x).1 hx]; exact zero_mem _)
    (fun g => TrivSqZeroExt.inr (n g)) (fun g => rfl) (hlc.comp _)
    (fun g h => by rw [hmul, hcoc, TrivSqZeroExt.inr_add])
    (fun v hv s hs => by rw [hU v hv s hs, TrivSqZeroExt.inr_zero])
    (fun v hv => by
      obtain ⟨m, hm⟩ := hT v hv
      exact ⟨TrivSqZeroExt.inr m, rfl, fun g => by rw [hmul, hm, TrivSqZeroExt.inr_sub]⟩)
    (by rw [hmul, hmul, hN])
  simp only [hmul] at hm
  obtain ⟨f, hf, -⟩ := hu.univ _ r hr
  have e1 : ∀ g a b, f ((u g).mat a b) = (r g).mat a b := fun g a b =>
    congrArg (fun r : Γ →* GG (m := 3) (R := TrivSqZeroExt O M) => (r g).mat a b) hf
  have hX : ∀ i, (f.comp W.π) (MvPowerSeries.X i) =
      TrivSqZeroExt.inr ((Tm O (a i) (b i) * psi F.Ψ (b i) (g i)) • n (g i)) := fun i => by
    have e2 : f ((F.rz R (g i)).mat (a i) (b i)) = (F.rz _ (g i)).mat (a i) (b i) := f.commutes _
    show f (W.z i) = _
    rw [hz, map_sub, e1, e2, hm, add_sub_cancel_left]
  have key : ∀ p, (f (W.π p)).snd = ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) p •
      ((Tm O (a i) (b i) * psi F.Ψ (b i) (g i)) • n (g i)) := fun p => by
    have := map_lin (f.comp W.π) (fun i j => by rw [hX, hX, TrivSqZeroExt.inr_mul_inr]) p
    rw [AlgHom.comp_apply] at this
    rw [this]
    simp only [hX, TrivSqZeroExt.snd_add, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl, zero_add,
      TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_inr]
  refine ⟨fun p hp => by rw [← key, hp, map_zero, TrivSqZeroExt.snd_zero], fun h => funext fun s => ?_⟩
  obtain ⟨p, hp⟩ := W.surj ((u s).mat 1 0)
  have h1 := key p
  simp only [h, smul_zero, Finset.sum_const_zero] at h1
  rw [hp, e1, hm, rz_mat] at h1
  have h2 : (F.Ψ s : O) • n s = 0 := by simpa [Tm, psi, wt1] using h1
  exact ((F.Ψ s).isUnit.smul_eq_zero).1 h2

private theorem exists_norm {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Ψ : Γ →* Oˣ) (a : O)
    (c g₁ : Γ) (hc : Ψ c = 1) (hg : IsUnit ((Ψ g₁ : O) ^ 2 - 1)) :
    ∃ N : H1 (oqRep Ψ⁻¹ a) →ₗ[O] (Γ → OQ a),
      (∀ z : Z1 (oqRep Ψ⁻¹ a), ∃ m, N (Submodule.Quotient.mk z) = z.1 - d0 (oqRep Ψ⁻¹ a) m) ∧
      ∀ x, (Ψ g₁ : O) • N x g₁ = (Ψ (gstar c g₁) : O) • N x (gstar c g₁) := by
  have hρ : ∀ g (m : OQ a), oqRep Ψ⁻¹ a g m = (((Ψ g)⁻¹ : Oˣ) : O) • m := fun _ _ => rfl
  let l : (Γ → OQ a) →ₗ[O] OQ a :=
    (Ψ g₁ : O) • LinearMap.proj g₁ - (Ψ (gstar c g₁) : O) • LinearMap.proj (gstar c g₁)
  have hl : ∀ y, l y = (Ψ g₁ : O) • y g₁ - (Ψ (gstar c g₁) : O) • y (gstar c g₁) := fun _ => rfl
  have hs : Ψ (gstar c g₁) = (Ψ g₁)⁻¹ := by simp [gstar, hc]
  have hw : IsUnit ((((Ψ g₁)⁻¹ : Oˣ) : O) - Ψ g₁) := by
    have : (((Ψ g₁)⁻¹ : Oˣ) : O) - Ψ g₁ = -(((Ψ g₁)⁻¹ : Oˣ) : O) * ((Ψ g₁ : O) ^ 2 - 1) := by
      linear_combination (Ψ g₁ : O) * (Ψ g₁).inv_mul
    rw [this]
    exact (Units.isUnit _).neg.mul hg
  obtain ⟨w, hw⟩ := hw
  have hld : ∀ m, l (d0 (oqRep Ψ⁻¹ a) m) = (w : O) • m := fun m => by
    rw [hl, amitsur_d0_apply, amitsur_d0_apply, hρ, hρ, smul_sub, smul_sub, smul_smul, smul_smul, Units.mul_inv, Units.mul_inv,
      hs, hw, sub_smul]
    abel
  let N₀ : (Γ → OQ a) →ₗ[O] (Γ → OQ a) := LinearMap.id - (d0 (oqRep Ψ⁻¹ a)).comp (((w⁻¹ : Oˣ) : O) • l)
  have hN₀ : ∀ y, N₀ y = y - d0 (oqRep Ψ⁻¹ a) (((w⁻¹ : Oˣ) : O) • l y) := fun _ => rfl
  refine ⟨Submodule.liftQ _ (N₀.comp (Z1 (oqRep Ψ⁻¹ a)).subtype) ?_, fun z => ⟨_, hN₀ z.1⟩, fun x => ?_⟩
  · rintro z ⟨m, hm⟩
    show N₀ z.1 = 0
    have hm' : z.1 = d0 (oqRep Ψ⁻¹ a) m := hm.symm
    rw [hN₀, hm', hld, smul_smul, Units.inv_mul, one_smul, sub_self]
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← sub_eq_zero, ← hl]
    show l (N₀ z.1) = 0
    rw [hN₀, map_sub, hld, smul_smul, Units.mul_inv, one_smul, sub_self]

private theorem exists_rep {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ]
    [TopologicalSpace Γ] (F : Frame O G Γ ι) (a : O) (x : H1 (oqRep F.Ψ⁻¹ a)) (hx : x ∈ F.ShaO a) :
    ∃ z : Z1 (oqRep F.Ψ⁻¹ a), x = Submodule.Quotient.mk z ∧
      (∀ v ∉ F.Tb, ∀ s ∈ F.Nv v, z.1 (F.loc v s) = 0) ∧
      ∀ v ∈ F.Tb, ∃ m, ∀ g : F.D v, z.1 (F.loc v g) = oqRep F.Ψ⁻¹ a (F.loc v g) m - m := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨0, rfl, fun _ _ _ _ => rfl, fun _ _ => ⟨0, fun _ => by simp⟩⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, rfl, h1, h2⟩ := hx
    obtain ⟨z', rfl, h1', h2'⟩ := hy
    refine ⟨z + z', rfl, fun v hv s hs => ?_, fun v hv => ?_⟩
    · rw [Submodule.coe_add, Pi.add_apply, h1 v hv s hs, h1' v hv s hs, add_zero]
    · obtain ⟨m, hm⟩ := h2 v hv
      obtain ⟨m', hm'⟩ := h2' v hv
      exact ⟨m + m', fun g => by rw [Submodule.coe_add, Pi.add_apply, hm, hm', map_add (f := _)]; abel⟩
  | smul c x _ hx =>
    obtain ⟨z, rfl, h1, h2⟩ := hx
    refine ⟨c • z, rfl, fun v hv s hs => ?_, fun v hv => ?_⟩
    · rw [Submodule.coe_smul, Pi.smul_apply, h1 v hv s hs, smul_zero]
    · obtain ⟨m, hm⟩ := h2 v hv
      exact ⟨c • m, fun g => by rw [Submodule.coe_smul, Pi.smul_apply, hm, map_smul, smul_sub]⟩

private theorem lc_smul {O Γ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace Γ]
    (f : Γ → O) (hf : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal O ^ n) (f g))
    (a : O) (ha : a ≠ 0) (m : OQ a) : IsLocallyConstant fun g => f g • m := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  have hle : maximalIdeal O ^ n ≤ Ideal.span {a} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    exact hn.dvd
  have := (hf n).comp fun y => (show OQ a from Ideal.Quotient.factor hle y) * m
  refine (congrArg IsLocallyConstant (funext fun g => ?_)).mp this
  exact (Algebra.smul_def (f g) m).symm

end UpperTheory.V.UnitaryThreeInertia.MP

open UpperTheory.V.UnitaryThreeInertia.MP in
theorem UpperTheory.V.UnitaryThreeInertia.mprime_coord :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    ∀ (W : WPres O ℤ R), F.Adapted u W → ∀ a : O, a ≠ 0 → ∃ d : F.ShaO a →+ (W.σ → O ⧸ Ideal.span {a}), Function.Injective d ∧
      (∀ x i, W.wt i ≠ -1 → d x i = 0) ∧ ∀ x f, W.π f = 0 → ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f • d x i = 0 := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg R _ _ _ u hu W hW a ha
  choose g p q _ hwt hz using hW.var
  obtain ⟨N, hN1, hN2⟩ := exists_norm F.Ψ a F.c g₁ hF.Ψc hg.2
  haveI : Module.Finite O (OQ a) := inferInstanceAs (Module.Finite O (O ⧸ Ideal.span {a}))
  have hρ : ∀ g (m : OQ a), oqRep F.Ψ⁻¹ a g m = (((F.Ψ g)⁻¹ : Oˣ) : O) • m := fun _ _ => rfl
  let d : F.ShaO a →+ (W.σ → OQ a) :=
    { toFun := fun x i => (Tm O (p i) (q i) * psi F.Ψ (q i) (g i)) • N x.1 (g i)
      map_zero' := funext fun i => by simp
      map_add' := fun x y => funext fun i => by simp }
  have key : ∀ x : F.ShaO a, (∀ f, W.π f = 0 → ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f • d x i = 0) ∧
      ((∀ i, d x i = 0) → N x.1 = 0) := fun x => by
    obtain ⟨z, hxz, h1, h2⟩ := exists_rep F a x.1 x.2
    obtain ⟨m, hm⟩ := hN1 z
    rw [← hxz] at hm
    have hn : ∀ s, N x.1 s = z.1 s - ((((F.Ψ s)⁻¹ : Oˣ) : O) • m - m) := fun s => congrFun hm s
    refine coord F hF g₁ u hu W g p q hz (N x.1) ?_ (fun s t => ?_) (fun v hv s hs => ?_) (fun v hv => ?_) (hN2 _)
    · rw [show N x.1 = _ from funext hn]
      have hΨ : IsLocallyConstant fun s => (((F.Ψ s)⁻¹ : Oˣ) : O) • m :=
        lc_smul _ (fun n => by simpa only [Function.comp_def, map_inv] using (hF.Ψ_cont n).comp_continuous continuous_inv) a ha m
      exact ((IsLocallyConstant.iff_continuous _).2 z.2.1).sub (hΨ.sub (IsLocallyConstant.const m))
    · rw [hn, hn, hn, z.2.2, hρ, map_mul, mul_inv, Units.val_mul, mul_smul, smul_sub, smul_sub]
      abel
    · have : F.Ψ (F.loc v s) = 1 := hF.teich v hv s hs
      rw [hn, h1 v hv s hs, this]
      simp
    · obtain ⟨m', hm'⟩ := h2 v hv
      exact ⟨m' - m, fun s => by rw [hn, hm', hρ, smul_sub]; abel⟩
  refine ⟨d, (injective_iff_map_eq_zero d).2 fun x hx => ?_, fun x i hi => ?_, fun x => (key x).1⟩
  · have h0 := (key x).2 fun i => congrFun hx i
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
    obtain ⟨m, hm⟩ := hN1 z
    rw [hz, h0, eq_comm, sub_eq_zero] at hm
    exact Subtype.ext (hz.symm.trans ((Submodule.Quotient.mk_eq_zero _).2 ⟨m, hm.symm⟩))
  · show (Tm O (p i) (q i) * psi F.Ψ (q i) (g i)) • N x.1 (g i) = 0
    rw [Tm_wt O _ _ (hwt i ▸ hi), zero_mul, zero_smul]
end

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem conjBy_one' {R : Type} [CommRing R] {D : Type} [Group D] (r : D →* GG (m := 3) (R := R)) :
    conjBy 1 r = r := by
  apply MonoidHom.ext; intro g; simp [conjBy, GG.ofGL]

theorem UpperTheory.V.UnitaryThreeInertia.abstract_count :
    LemmaM → LemmaM' → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → F.Count → F.VanE → F.Cl1 → F.Xpp → ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG (m := 3) (R := R)), F.IsUniv g₁ u →
    Module.Finite O (wpart O u 0) → ∀ (φ : Γ) (Good : (Γ →* GG (m := 3) (R := PadicAlgCl l)) → Prop),
      (∀ (ξ : Sring (O := O) u →ₐ[O] (PadicAlgCl l)) (r : Γ →* GG (m := 3) (R := PadicAlgCl l)), IsPtHom u ξ r → TypeI F.η r → Good r) →
      (∀ r, F.IsCharZeroPt g₁ r → TypeI F.η r → Good r → F.Rigid r ∧ (r φ).mat.trace ≠ (F.rz (PadicAlgCl l) φ).mat.trace) →
      ∃ (n : ℕ) (r : Fin n → (Γ →* GG (m := 3) (R := PadicAlgCl l))) (V : ℕ), (∀ i, F.IsCharZeroPt g₁ (r i) ∧ TypeI F.η (r i) ∧ Good (r i)) ∧
        (∀ i i', MatIso F.η.ker (mats (r i)) (mats (r i')) → i = i') ∧ (∀ a : O, a ≠ 0 → F.shaLen a ≤ V) ∧
        (V : ℝ) ≤ 2 * (Base.eO l O).toNat * ∑ i, vl1 l ((r i φ).mat.trace - (F.rz (PadicAlgCl l) φ).mat.trace) := by
  intro hM hM' l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hOk hLV hC hVE hCl hX g₁ hm R _ _ _ u hU hfin φ Good hGood hRig
  obtain ⟨W, hAd, hMin⟩ := exists_adapted F hOk g₁ hm u hU
  obtain ⟨h, hpush⟩ := hasOrigin F hOk g₁ hm u hU W hAd
  obtain ⟨f, hf, hker⟩ := exists_relations F hOk hLV hC g₁ hm u hU W hAd hMin
  have hent : ∀ g x y, W.origin h ((u g).mat x y) = (r0 F.η F.Ψ g).mat x y := by
    intro g x y
    exact congrArg (fun q => (q g).mat x y) hpush
  have hpt : ∀ ξ : Sring (O := O) u →ₐ[O] PadicAlgCl l, ∃ r, IsPtHom u ξ r :=
    fun ξ => (existsUnique_isPtHom u ξ).exists
  have hval : ∀ (ξ : Sring (O := O) u →ₐ[O] PadicAlgCl l) r, IsPtHom u ξ r → ∀ g x y,
      ξ ⟨(u g).mat x y, mem_Sring u (entry_mem u g x y)⟩ = (r g).mat x y := by
    intro ξ r hr g x y
    rw [(hr g).2]
    rfl
  have halg : ∀ c : O, algebraMap O R c ∈ wpart O u 0 := by
    intro c R' _ _ _ f₁ f₂ t _
    simp
  have hdiag : ∀ i : Fin 3, (u φ).mat i i ∈ wpart O u 0 := by
    intro i
    simpa [wt] using entry_mem u φ i i
  set a : R := (u φ).mat.trace - algebraMap O R ((r0 F.η F.Ψ φ).mat.trace) with ha_def
  have ha0 : a ∈ wpart O u 0 :=
    Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => hdiag i) (halg _)
  have hξa : ∀ (ξ : Sring (O := O) u →ₐ[O] PadicAlgCl l) r, IsPtHom u ξ r →
      ξ ⟨a, mem_Sring u ha0⟩ = (r φ).mat.trace - (F.rz (PadicAlgCl l) φ).mat.trace := by
    intro ξ r hr
    have hsplit : (⟨a, mem_Sring u ha0⟩ : Sring (O := O) u) =
        ∑ i, ⟨(u φ).mat i i, mem_Sring u (hdiag i)⟩ - algebraMap O (Sring (O := O) u) ((r0 F.η F.Ψ φ).mat.trace) := by
      apply Subtype.ext
      simp [a, Matrix.trace]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsplit, map_sub, map_sum, AlgHom.commutes]
    simp only [Matrix.trace, Matrix.diag]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => hval ξ r hr φ i i
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [Frame.rz, map_sum]
  have hao : W.origin h a = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [a, Matrix.trace, map_sum, hent]
  have hfacts : ∀ (ξ : Sring (O := O) u →ₐ[O] PadicAlgCl l) r, IsPtHom u ξ r →
      (¬∀ j < 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      (¬∀ j > 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      F.IsCharZeroPt g₁ r ∧ TypeI F.η r ∧ Good r := by
    intro ξ r hr hneg hpos
    have hs := isPtHom_sign F hOk g₁ hm u hU ξ r hr
    have hz := isCharZeroPt_of_isPtHom F hOk g₁ hm u hU hfin ξ r hr
    have hT := typeI_of_twoSigned F hOk hLV hX g₁ hm r hz (fun h' => hneg (hs.1.1 h')) (fun h' => hpos (hs.2.1 h'))
    exact ⟨hz, hT, hGood ξ r hr hT⟩
  have hwt2 : ∀ x y : Fin 3, -2 ≤ wt x y ∧ wt x y ≤ 2 := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp [wt, wt1]
  have hwt : ∀ s : W.σ, -2 ≤ W.wt s ∧ W.wt s ≤ 2 := by
    intro s
    obtain ⟨g, x, y, -, hw, -⟩ := hAd.var s
    rw [hw]
    exact hwt2 x y
  have hcard : ∀ j : ℤ, ((Module.finrank (ResidueField O) (F.Ob j) : ℕ) : ℤ) +
      (if j = -1 then -1 else if j = 1 ∨ j = 2 then 1 else 0) ≤ (Nat.card {i // W.wt i = j} : ℤ) := by
    intro j
    obtain ⟨-, -, hd⟩ := hC j
    have hle := finrank_H1L_le F hOk hLV hC g₁ hm u hU W hAd j
    change _ + Frame.defect j ≤ _
    rw [← hd]
    omega
  have horig : ∀ (ξ : Sring (O := O) u →ₐ[O] PadicAlgCl l),
      (∀ j < 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      (∀ j > 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      ∀ (j : ℤ) (x : R) (hx : x ∈ wpart O u j),
        ξ ⟨x, mem_Sring u hx⟩ = algebraMap O (PadicAlgCl l) (W.origin h x) := by
    intro ξ hneg hpos j x hx
    obtain ⟨r, hr⟩ := hpt ξ
    have hs := isPtHom_sign F hOk g₁ hm u hU ξ r hr
    have hz := isCharZeroPt_of_isPtHom F hOk g₁ hm u hU hfin ξ r hr
    have hrz := eq_rz_of_diag F hOk hCl g₁ hm r hz (hs.1.2 hneg) (hs.2.2 hpos)
    let ξ0 : Sring (O := O) u →ₐ[O] PadicAlgCl l :=
      (Algebra.ofId O (PadicAlgCl l)).comp ((W.origin h).comp (Sring (O := O) u).val)
    have h0 : IsPtHom u ξ0 (F.rz (PadicAlgCl l)) := by
      intro g
      refine ⟨?_, ?_⟩
      · rw [← hrz]
        exact (hr g).1
      · ext x y
        simp [ptMat, ξ0, Frame.rz, hent]
    have hr' : IsPtHom u ξ (conjBy ((tor (PadicAlgCl l)) 1) (F.rz (PadicAlgCl l))) := by
      rw [map_one, conjBy_one', ← hrz]
      exact hr
    have := (isPtHom_act F hOk g₁ hm u hU hfin ξ0 _ h0 ξ 1).1 hr' j x hx
    simpa [ξ0] using this
  have hder : ∀ (ξ : Sring (O := O) u →ₐ[O] PadicAlgCl l),
      (¬∀ j < 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      (¬∀ j > 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      ∀ D ∈ PtDer ξ (PadicAlgCl l), ∃ c, ∀ (j : ℤ) (x : R) (hx : x ∈ wpart O u j),
        D ⟨x, mem_Sring u hx⟩ = c * j * ξ ⟨x, mem_Sring u hx⟩ := by
    intro ξ hneg hpos D hD
    obtain ⟨r, hr⟩ := hpt ξ
    obtain ⟨hz, hT, hG⟩ := hfacts ξ r hr hneg hpos
    exact tangent_eq_orbit F hOk g₁ hm u hU hfin ξ r hr (hRig r hz hT hG).1 D hD
  have hne : ∀ (ξ : Sring (O := O) u →ₐ[O] PadicAlgCl l),
      (¬∀ j < 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      (¬∀ j > 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      ξ ⟨a, mem_Sring u ha0⟩ ≠ 0 := by
    intro ξ hneg hpos
    obtain ⟨r, hr⟩ := hpt ξ
    obtain ⟨hz, hT, hG⟩ := hfacts ξ r hr hneg hpos
    rw [hξa ξ r hr]
    exact sub_ne_zero.mpr (hRig r hz hT hG).2
  obtain ⟨n, ξs, V, hnt, hinj, hlen, hV⟩ :=
    Abs.coord_count hM hM' O (PadicAlgCl l) (fun x => ((Base.eO l O).toNat : ℝ) * vl1 l x) norm_bound_of_integral_values
      R W h (wpart O u) hAd.part hwt (fun j => Module.finrank (ResidueField O) (F.Ob j)) f hf hker
      hcard (tangent_coord_eq_zero_of_nonpos_weight F hOk hVE g₁ hm u hU W hAd) hfin horig hder a ha0 hao hne
  choose rr hrr using hpt
  refine ⟨n, fun i => rr (ξs i), V, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hfacts (ξs i) _ (hrr _) (hnt i).1 (hnt i).2
  · intro i i' hiso
    obtain ⟨hz, hT, -⟩ := hfacts (ξs i) _ (hrr _) (hnt i).1 (hnt i).2
    obtain ⟨hz', -, -⟩ := hfacts (ξs i') _ (hrr _) (hnt i').1 (hnt i').2
    obtain ⟨t, ht⟩ := conj_of_matIso F hOk g₁ hm _ hz _ hz' hT hiso
    apply hinj i i' t
    have h2 := hrr (ξs i')
    rw [ht] at h2
    exact (isPtHom_act F hOk g₁ hm u hU hfin (ξs i) _ (hrr _) (ξs i') t).1 h2
  · intro c hc
    obtain ⟨d, hdi, hd1, hd2⟩ := mprime_coord F hOk g₁ hm u hU W hAd c hc
    exact hlen c hc _ d hdi hd1 hd2
  · have hsum : ∀ i, ξs i ⟨a, mem_Sring u ha0⟩ =
        (rr (ξs i) φ).mat.trace - (F.rz (PadicAlgCl l) φ).mat.trace := fun i => hξa _ _ (hrr _)
    simp only [hsum] at hV
    rw [mul_assoc, Finset.mul_sum]
    exact hV
