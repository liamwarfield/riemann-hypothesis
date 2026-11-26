module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RegCoset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.UnipTorsion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSep
private theorem exists_element_separating_powers {G K : Type} [Group G] [Field K] (l : ℕ) [Fact l.Prime] [CharP K l] {n : ℕ}
    (ψ : Fin n → G →* (PowerSeries K)ˣ) (N V : Subgroup G) (hV : V.index ≠ 0)
    (hred : ∀ g ∈ N, ∀ a b, PowerSeries.constantCoeff (ψ a g : PowerSeries K) =
      PowerSeries.constantCoeff (ψ b g : PowerSeries K))
    (hsep : ∀ a b, a ≠ b → ∃ g ∈ N, ψ a g ≠ ψ b g) :
    ∃ g ∈ N, g ∈ V ∧ ∀ a b, a ≠ b → ∀ m : ℕ, 0 < m → ψ a g ^ m ≠ ψ b g ^ m := by
  haveI : CharP (PowerSeries K) l := charP_of_injective_ringHom (PowerSeries.C_injective (R := K)) l
  have tf : ∀ g ∈ N, ∀ a b (m : ℕ), 0 < m → (ψ a g / ψ b g) ^ m = 1 → ψ a g / ψ b g = 1 := by
    intro g hg a b m hm h
    apply Units.ext
    apply UpperTheory.V.Pr.T.oneUnitTF l _ m hm.ne'
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
      have hinv : PowerSeries.constantCoeff ((ψ b g)⁻¹ : (PowerSeries K)ˣ).val *
          PowerSeries.constantCoeff ((ψ b g : (PowerSeries K)ˣ) : PowerSeries K) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      have hc : PowerSeries.constantCoeff (((ψ a g / ψ b g : (PowerSeries K)ˣ) : PowerSeries K) - 1) = 0 := by
        rw [map_sub, div_eq_mul_inv, Units.val_mul, map_mul, hred g hg a b, mul_comm, hinv, map_one, sub_self]
      rw [hc]
      exact not_isUnit_zero
    · rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  let χ : {p : Fin n × Fin n // p.1 ≠ p.2} → ↥(N ⊓ V) →* (PowerSeries K)ˣ :=
    fun p => (ψ p.1.1 / ψ p.1.2).comp (N ⊓ V).subtype
  obtain ⟨h, hh⟩ := UpperTheory.V.Pr.commonFree ↥(N ⊓ V) (PowerSeries K)ˣ {p : Fin n × Fin n // p.1 ≠ p.2} χ 1 one_pos
    (by
      intro p h m hm hpow
      rw [pow_one]
      exact tf h (Subgroup.mem_inf.mp h.2).1 _ _ m hm hpow)
    (by
      intro p
      obtain ⟨g, hgN, hne⟩ := hsep _ _ p.2
      obtain ⟨k, hk, -, hkV⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hV g
      refine ⟨⟨g ^ k, Subgroup.mem_inf.mpr ⟨N.pow_mem hgN k, hkV⟩⟩, ?_⟩
      rw [pow_one]
      intro h1
      apply hne
      have h2 : (ψ p.1.1 g / ψ p.1.2 g) ^ k = 1 := by
        simpa [χ, div_pow, map_pow] using h1
      exact div_eq_one.mp (tf g hgN _ _ k hk h2))
  refine ⟨h, (Subgroup.mem_inf.mp h.2).1, (Subgroup.mem_inf.mp h.2).2, ?_⟩
  intro a b hab m hm heq
  apply hh ⟨(a, b), hab⟩ m hm
  simp [χ, div_pow, heq]

theorem UpperTheory.V.Pr.niceSep :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → ∀ U : Subgroup T.G.G₀, IsOpen (U : Set T.G.G₀) → ∀ v, ∃ g : T.G.Gv v, T.G.φ v g ∈ U ⊓ T.G.G' ∧ UpperTheory.V.Pr.FreeRatios fun i => y.ψ v i g |> Units.map (algebraMap y.A y.Fr).toMonoidHom := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hnice hmat hψ U hU v
  haveI : CharP (IsLocalRing.ResidueField O) l := UpperTheory.V.Fr.IsCoef.char
  haveI : CharP y.K l :=
    charP_of_injective_algebraMap (algebraMap (IsLocalRing.ResidueField O) y.K).injective l
  let N : Subgroup (T.G.Gv v) := (F.Nv (T.K.e v)).comap (T.K.lam v).toMonoidHom
  let V : Subgroup (T.G.Gv v) := U.comap (T.G.φ v)
  have hV : V.index ≠ 0 := by
    rw [Subgroup.index_ne_zero_iff_finite]
    exact Subgroup.quotient_finite_of_isOpen V (hU.preimage (T.G.φ_cont v))
  have hred : ∀ g ∈ N, ∀ a b, PowerSeries.constantCoeff (y.ψ v a g : PowerSeries y.K) =
      PowerSeries.constantCoeff (y.ψ v b g : PowerSeries y.K) := by
    intro g hg a b
    have key : ∀ i, PowerSeries.constantCoeff (y.ψ v i g : PowerSeries y.K) =
        algebraMap (IsLocalRing.ResidueField O) y.K (T.r.psib v i g : IsLocalRing.ResidueField O) :=
      fun i => congrArg Units.val (DFunLike.congr_fun (y.ψ_red v i) g)
    have hΨ : F.Ψ ((F.loc0 (T.K.e v) (T.K.lam v g) : F.del.ker) : F.Γ) = 1 :=
      T.ok.Ψ_N (T.K.e v) (T.K.lam v g) hg
    rw [key a, key b, T.K.psib, T.K.psib, T.K.chib, T.K.chib, ← T.K.lam_loc, hΨ, one_zpow, one_zpow]
  have hsep : ∀ a b, a ≠ b → ∃ g ∈ N, y.ψ v a g ≠ y.ψ v b g := by
    intro a b hab
    have hc := hnice.sep (T.K.e v) a b hab
    simp only [UpperTheory.V.Fr.NRep.Coin, not_forall] at hc
    obtain ⟨g', hg', hne⟩ := hc
    refine ⟨(T.K.lam v).symm g', ?_, ?_⟩
    · show (T.K.lam v) ((T.K.lam v).symm g') ∈ F.Nv (T.K.e v)
      simpa using hg'
    · intro heq
      apply hne
      rw [hψ] at heq
      simp only [UpperTheory.V.Pr.TwLink.twψ, MonoidHom.mul_apply, MonoidHom.comp_apply] at heq
      have h2 := congrArg Units.val (mul_right_cancel heq)
      simp [UpperTheory.V.Fr.NRep.map] at h2
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      convert h2 using 4
      all_goals exact ((T.K.lam v).apply_symm_apply g').symm
  obtain ⟨g, hgN, hgV, hfree⟩ := exists_element_separating_powers l (y.ψ v) N V hV hred hsep
  refine ⟨g, ⟨hgV, ?_⟩, ?_⟩
  · show T.G.ε ((T.G.φ v g : T.G.η.ker) : T.G.Γ) = 1
    rw [← T.K.π_eps, ← T.K.lam_loc]
    exact (Subgroup.mem_inf.mp hgN).2
  · intro a b hab m hm heq
    apply hfree a b hab m hm
    apply Units.ext
    apply IsFractionRing.injective y.A y.Fr
    have h2 := congrArg Units.val heq
    simpa [Units.val_pow_eq_pow_val, map_pow] using h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceIrrE
open Matrix Polynomial IsLocalRing UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Pr

private def IsBlockDiagFinThree {A : Type} [CommRing A] (M : Matrix (Fin 3) (Fin 3) A) : Prop :=
  M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 1 = 0

private lemma submatrix_corners_three {A : Type} (M : Matrix (Fin 3) (Fin 3) A) :
    M.submatrix ![0, 2] ![0, 2] = !![M 0 0, M 0 2; M 2 0, M 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma charpoly_block_three {A : Type} [CommRing A] (M : Matrix (Fin 3) (Fin 3) A) (h : IsBlockDiagFinThree M) :
    M.charpoly = (X - C (M 1 1)) * (M.submatrix ![0, 2] ![0, 2]).charpoly := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [submatrix_corners_three, Matrix.charpoly, det_fin_three, det_fin_two]
  simp [charmatrix_apply, h1, h2, h3, h4]
  ring

private def corner {G A : Type} [Group G] [CommRing A] (m : G →* Matrix (Fin 3) (Fin 3) A) (h : ∀ g, IsBlockDiagFinThree (m g)) :
    G →* Matrix (Fin 2) (Fin 2) A where
  toFun g := (m g).submatrix ![0, 2] ![0, 2]
  map_one' := by
    rw [submatrix_corners_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g g' := by
    obtain ⟨h1, h2, h3, h4⟩ := h g
    rw [submatrix_corners_three, submatrix_corners_three, submatrix_corners_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h4]

private lemma mid_eq {D κ : Type} [Field κ] (m : D → Matrix (Fin 3) (Fin 3) κ) (h : ∀ g, IsBlockDiagFinThree (m g))
    (ψ : Fin 3 → D → κ) (ho : ∀ g, ordProd m ψ g = 0) : ∃ i, ∀ g, m g 1 1 = ψ i g := by
  by_contra hc
  push Not at hc
  choose g hg using hc
  have h0 := congrFun (congrFun (ho g) 1) 1
  obtain ⟨a1, a2, a3, a4⟩ := h (g 0)
  obtain ⟨b1, b2, b3, b4⟩ := h (g 2)
  simp [ordProd, List.ofFn_succ, Matrix.mul_apply, Fin.sum_univ_three, a2, a3, b1, b4, sub_eq_zero] at h0
  rcases h0 with h0 | h0 | h0
  · exact hg 0 h0
  · exact hg 1 h0
  · exact hg 2 h0

private lemma core {G D κ k A : Type} [Group G] [Group D] [Field κ] [IsAlgClosed κ] [Field k] [CommRing A]
    (m : G →* Matrix (Fin 3) (Fin 3) A) (h : ∀ g, IsBlockDiagFinThree (m g)) (φ : A →+* κ) (hφ : Function.Injective φ)
    (hirr : MatIrr (⊤ : Subgroup G) fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2])
    (red : A →+* k) (χ : Fin 2 → G →* kˣ) (h0 : ∀ g, red (m g 0 0) = χ 0 g) (h2 : ∀ g, red (m g 2 2) = χ 1 g)
    (h02 : ∀ g, red (m g 0 2) * red (m g 2 0) = 0) (ι : D →* G) (ψ : Fin 3 → D →* κˣ)
    (hch : ∀ g, ((m (ι g)).map φ).charpoly = chPoly ψ g)
    (ho : ∀ g, ordProd (fun s => (m (ι s)).map φ) (fun i s => (ψ i s : κ)) g = 0)
    (U : Subgroup G) [U.Normal] (hs : ∃ g, ι g ∈ U ∧ ∀ a b, a ≠ b → ψ a g ≠ ψ b g)
    (hχ : ∃ g, χ 0 (ι g) ≠ χ 1 (ι g)) :
    MatIrr U fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2] := by
  have hb : ∀ g, IsBlockDiagFinThree ((m g).map φ) := fun g => by
    obtain ⟨h1, h2, h3, h4⟩ := h g
    simp [IsBlockDiagFinThree, h1, h2, h3, h4]
  obtain ⟨i, hi⟩ := mid_eq _ (fun s => hb (ι s)) _ ho
  let σ : G →* GL (Fin 2) κ := (corner ((φ.mapMatrix : Matrix (Fin 3) (Fin 3) A →+* _).toMonoidHom.comp m) hb).toHomUnits
  have hσ : gm σ = fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2] := rfl
  rw [← hσ] at hirr ⊢
  refine irrNormal G κ k A 2 Nat.prime_two σ hirr φ red χ hφ (fun g => ?_) D ι (fun a => ψ (i.succAbove a))
    (fun g => ?_) U (fun a b hab => ?_) ?_
  · refine ⟨((m g).submatrix ![0, 2] ![0, 2]).charpoly, ?_, ?_⟩
    · rw [← Matrix.charpoly_map]; rfl
    · rw [← Matrix.charpoly_map]
      simp only [submatrix_corners_three, Matrix.charpoly, det_fin_two, chPoly, Fin.prod_univ_two]
      simp [charmatrix_apply, h0, h2, mul_eq_zero.1 (h02 g)]
  · have e := hch g
    rw [charpoly_block_three _ (hb _), hi, chPoly, Fin.prod_univ_succAbove _ i] at e
    exact mul_left_cancel₀ (X_sub_C_ne_zero _) e
  · obtain ⟨g, hg, hg'⟩ := hs
    exact ⟨g, hg, hg' _ _ fun e => hab (Fin.succAbove_right_injective e)⟩
  · obtain ⟨g, hg⟩ := hχ
    exact ⟨0, 1, g, hg⟩

end UpperTheory.V.Pr

open Matrix Polynomial IsLocalRing UpperTheory.V UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Pr in
theorem UpperTheory.V.Pr.niceIrrE :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (T : UpperTheory.V.Pr.Setup F 3) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → L.ρ.TE (RingHom.ker j) → ∀ U : Subgroup T.G.G₀, IsOpen (U : Set T.G.G₀) → UpperTheory.V.U3.MatIrr (U ⊓ T.G.G') fun g => (UpperTheory.V.W.mat (UpperTheory.V.W.pushRep (algebraMap y.Fr y.Fb) y.ρF) g).submatrix ![0, 2] ![0, 2] := by
  intro l _ O _ _ _ _ _ F T x L y j hj hN hρ hψ hE U hU
  have hj' : IsLocalHom (j : L.R →+* y.A) := ⟨hj.map_nonunit⟩
  obtain ⟨-, hbar, hid, htri⟩ := loc_rho T.ok T.n23 T.S x L
  have hO : IsLocalHom (algebraMap O L.R) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 := ha.map j
    rw [AlgHom.commutes, PowerSeries.isUnit_iff_constantCoeff] at h1
    have h2 : residue O a = 0 := (residue_eq_zero_iff a).2 hna
    have h3 : PowerSeries.constantCoeff (algebraMap O y.A a) = algebraMap (ResidueField O) y.K (residue O a) := by
      rw [PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C, IsScalarTower.algebraMap_apply O (ResidueField O) y.K]
      rfl
    rw [h3, h2, map_zero] at h1
    exact not_isUnit_zero h1
  have hb := (hbar (ResidueField.map (algebraMap O L.R)) fun a => ResidueField.map_residue _ _).1
  set φ : y.A →+* y.Fb := (algebraMap y.Fr y.Fb).comp (algebraMap y.A y.Fr) with hφ
  have hφi : Function.Injective φ := (algebraMap y.Fr y.Fb).injective.comp (IsFractionRing.injective y.A y.Fr)
  set ρ := L.ρ.map (j : L.R →+* y.A) with hρd
  set f : T.S.A →+* y.Fb := φ.comp ((j : L.R →+* y.A).comp (L.ι : T.S.A →+* L.R)) with hf
  have hfρ : T.S.u.map f = ρ.map φ := rfl
  have hker : RingHom.ker f = L.im (RingHom.ker j) := by
    ext a
    simp only [hf, RingHom.mem_ker, Space.Loc.im, Ideal.mem_comap, RingHom.comp_apply, map_eq_zero_iff _ hφi]
    rfl
  have hTE : T.S.u.TE (RingHom.ker f) := by
    rw [hker]
    obtain ⟨a, b, c⟩ := hid (RingHom.ker j)
    exact ⟨⟨fun h => hE.1.1 (a.2 h), fun h => hE.1.2 (b.2 h)⟩, rfl, c.1 hE.2.2⟩
  have hirr := typeE T.ok T.S y.Fb f hTE
  have hodd : ∀ g a b, Odd (w 3 a - w 3 b) → ρ.r g a b = 0 := fun g a b h =>
    hE.2.2 (Ideal.subset_span ⟨g, a, b, h, rfl⟩)
  have hV : Nonempty T.G.Vl := by
    rw [T.K.e.nonempty_congr]
    by_contra hc
    rw [not_nonempty_iff] at hc
    have := T.big.1
    simp [Frame.d] at this
  obtain ⟨v⟩ := hV
  have hfi : U.FiniteIndex := by
    haveI : CompactSpace T.G.G₀ :=
      isCompact_iff_compactSpace.1 (T.G.η.ker.isClosed_of_isOpen T.G.η_open).isCompact
    haveI := U.quotient_finite_of_isOpen hU
    exact Subgroup.finiteIndex_of_finite_quotient
  have hU' : IsOpen (U.normalCore : Set T.G.G₀) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (U.normalCore_isClosed (U.isClosed_of_isOpen hU))
  obtain ⟨g₁, hg₁, hfree⟩ := niceSep l O F 3 T x L y j hj hN hρ hψ _ hU' v
  haveI : T.G.G'.Normal := MonoidHom.normal_ker _
  let lam : T.G.Gv v →* F.Gv (T.K.e v) := (T.K.lam v).toMulEquiv.toMonoidHom
  have hlam : ∀ s, T.K.π (T.G.φ v s) = F.loc0 _ (lam s) := fun s => (T.K.lam_loc v s).symm
  let k' : ResidueField O →+* ResidueField y.A :=
    (ResidueField.map (j : L.R →+* y.A)).comp (ResidueField.map (algebraMap O L.R))
  have hres : ∀ z : L.R, residue y.A (j z) = ResidueField.map (j : L.R →+* y.A) (residue L.R z) := fun z =>
    (ResidueField.map_residue (j : L.R →+* y.A) z).symm
  have key := core (ρ.r.comp T.K.π)
    (fun g => ⟨hodd _ _ _ (by decide), hodd _ _ _ (by decide), hodd _ _ _ (by decide), hodd _ _ _ (by decide)⟩) φ hφi
    (fun W hW => hirr W fun g _ u hu => by
      obtain ⟨g', rfl⟩ := T.K.π_surj g
      exact hW g' trivial u hu)
    (residue y.A) (fun a => W.pushCh k' (((F.Ψ.comp F.del.ker.subtype).comp T.K.π) ^ w 3 (![0, 2] a)))
    (fun g => (hres _).trans (congrArg _ (hb (T.K.π g) 0))) (fun g => (hres _).trans (congrArg _ (hb (T.K.π g) 2)))
    (fun g => by
      by_cases hx : T.S.u.triP ≤ x
      · have h1 : L.ρ.r (T.K.π g) 2 0 ∈ maximalIdeal L.R := by
          have := hx (Ideal.subset_span ⟨T.K.π g, 2, 0, by decide, rfl⟩)
          rw [← L.lies] at this
          exact this
        refine mul_eq_zero_of_right _ ((hres _).trans ?_)
        rw [(residue_eq_zero_iff _).2 h1, map_zero]
      · have h1 : L.ρ.r (T.K.π g) 0 2 ∈ maximalIdeal L.R :=
          (htri hx).2 (Ideal.subset_span ⟨T.K.π g, 0, 2, by decide, rfl⟩)
        refine mul_eq_zero_of_left ((hres _).trans ?_) _
        rw [(residue_eq_zero_iff _).2 h1, map_zero])
    (T.G.φ v) (fun i => ((ρ.map φ).ψ (T.K.e v) i).comp lam)
    (fun g => by
      have h := congrArg (Polynomial.map f) (o1 T.ok T.n23 T.S (T.K.e v) (lam g))
      rw [← Matrix.charpoly_map, Polynomial.map_prod] at h
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
      rw [MonoidHom.comp_apply, hlam]
      exact h)
    (fun g => by
      have h := (ρ.map φ).ord (T.K.e v) fun i => lam (g i)
      simp only [MonoidHom.comp_apply, hlam]
      exact h)
    (U.normalCore ⊓ T.G.G') ⟨g₁, hg₁, fun a b hab e => hfree a b hab 1 one_pos (by
      have e1 : φ (ρ.ψ (T.K.e v) a (lam g₁)) = φ (ρ.ψ (T.K.e v) b (lam g₁)) := congrArg Units.val e
      have e2 : ρ.ψ (T.K.e v) a (lam g₁) = ρ.ψ (T.K.e v) b (lam g₁) := Units.ext (hφi e1)
      have e3 : y.ψ v a g₁ = y.ψ v b g₁ := by
        rw [hψ]
        exact congrArg (· * _) e2
      simp only [e3])⟩
    (by
      obtain ⟨g, hg⟩ := T.ok.f3 (T.K.e v)
      obtain ⟨s, rfl⟩ := (T.K.lam v).surjective g
      refine ⟨s, fun e => hg ?_⟩
      have e1 : k' ((F.Ψ (T.K.π (T.G.φ v s)) ^ w 3 0 : (ResidueField O)ˣ) : ResidueField O) =
          k' ((F.Ψ (T.K.π (T.G.φ v s)) ^ w 3 2 : (ResidueField O)ˣ) : ResidueField O) := congrArg Units.val e
      have e2 := Units.ext (k'.injective e1)
      rw [hlam, show w 3 0 = 1 by decide, show w 3 2 = -1 by decide, zpow_one, _root_.zpow_neg_one] at e2
      rw [sq]
      exact mul_eq_one_iff_eq_inv.2 e2)
  intro Y hW
  refine key Y fun g hg u hu => ?_
  have h1 := hW g ⟨U.normalCore_le hg.1, hg.2⟩ u hu
  have h2 : (W.mat (W.pushRep (algebraMap y.Fr y.Fb) y.ρF) g).submatrix ![0, 2] ![0, 2] =
      φ (T.K.κA y.A g) • (((ρ.r.comp T.K.π) g).map φ).submatrix ![0, 2] ![0, 2] := by
    ext a b
    show φ (UpperTheory.V.W.mat y.ρ g _ _) = _
    rw [hρ]
    exact map_mul φ _ _
  simp only [h2, smul_mulVec] at h1
  exact (Y.smul_mem_iff (((T.K.κA y.A g).isUnit.map φ).ne_zero)).1 h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceIrr
open IsLocalRing Matrix Polynomial UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.W UpperTheory.V.Pr

private theorem chi_map_ofRep {n : ℕ} {A K G : Type} [CommRing A] [CommRing K] [Group G] (f : A →+* K)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    ((GDet.ofRep ρ).map f).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly.map f := by
  letI : Algebra A K[X] := ((algebraMap K K[X]).comp f).toAlgebra
  rw [← Matrix.charpoly_map]
  change (GDet.repAlg ρ K[X] _).det = (Matrix.charmatrix _).det
  congr 1
  ext i j : 1
  have h : ∀ a, algebraMap A K[X] a = C (f a) := fun _ => rfl
  by_cases hij : i = j
  · subst hij
    simp [GDet.repAlg, h]
  · simp [GDet.repAlg, h, hij]

private theorem charpoly_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : HasFlag r κ) (s : H) : (gm r s).charpoly = chPoly κ s := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (gm r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

private theorem irr_twist {G H k : Type} [Group G] [Group H] [Field k] {n : ℕ} (a : G → Matrix (Fin n) (Fin n) k)
    (b : H → Matrix (Fin n) (Fin n) k) (π : G → H) (hπ : Function.Surjective π) (c : G → kˣ)
    (h : ∀ g, a g = (c g : k) • b (π g)) (hb : MatIrr ⊤ b) : MatIrr ⊤ a := by
  intro W hW
  refine hb W fun s _ v hv => ?_
  obtain ⟨g, rfl⟩ := hπ s
  have h1 := W.smul_mem ((c g)⁻¹ : kˣ) (hW g trivial v hv)
  rwa [h, Matrix.smul_mulVec, smul_smul, Units.inv_mul, one_smul] at h1

private theorem w_ne {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (a : kˣ) (ha : a ^ 2 ≠ 1) :
    ∃ i j : Fin n, a ^ w n i ≠ a ^ w n j := by
  rcases hn with rfl | rfl
  · refine ⟨0, 1, fun h => ha ?_⟩
    have h1 : a ^ (1 : ℤ) = a ^ (-1 : ℤ) := h
    rw [zpow_one, _root_.zpow_neg_one] at h1
    rw [sq]
    exact mul_eq_one_iff_eq_inv.2 h1
  · refine ⟨0, 2, fun h => ha ?_⟩
    have h1 : a ^ (1 : ℤ) = a ^ (-1 : ℤ) := h
    rw [zpow_one, _root_.zpow_neg_one] at h1
    rw [sq]
    exact mul_eq_one_iff_eq_inv.2 h1

theorem UpperTheory.V.Pr.niceIrr :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → L.ρ.TI (RingHom.ker j) → ∀ U : Subgroup T.G.G₀, IsOpen (U : Set T.G.G₀) → UpperTheory.V.U3.MatIrr (U ⊓ T.G.G') (UpperTheory.V.W.mat (UpperTheory.V.W.pushRep (algebraMap y.Fr y.Fb) y.ρF)) := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hp h1 h2 hI U hU
  classical
  let φ : y.A →+* y.Fb := (algebraMap y.Fr y.Fb).comp (algebraMap y.A y.Fr)
  have hφ : Function.Injective φ := (algebraMap y.Fr y.Fb).injective.comp (IsFractionRing.injective y.A y.Fr)
  have hm : ∀ g, gm (pushRep (algebraMap y.Fr y.Fb) y.ρF) g = (mat y.ρ g).map φ := fun g => rfl
  have hn : n.Prime := by
    rcases T.n23 with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three

  have hirr : MatIrr ⊤ (gm (pushRep (algebraMap y.Fr y.Fb) y.ρF)) := by
    let f : T.S.A →+* y.Fb := φ.comp ((j : L.R →+* y.A).comp (L.ι : T.S.A →+* L.R))
    have hker : RingHom.ker f = L.im (RingHom.ker j) := by
      ext a
      exact (map_eq_zero_iff φ hφ).trans Iff.rfl
    obtain ⟨k1, k2, k3⟩ := (loc_rho T.ok T.n23 T.S x L).2.2.1 (RingHom.ker j)
    have hTI : T.S.u.TI (RingHom.ker f) := by
      rw [hker]
      exact ⟨⟨fun h => hI.1.1 (k1.2 h), fun h => hI.1.2 (k2.2 h)⟩, fun h3 h => hI.2 h3 (k3.2 h)⟩
    refine irr_twist _ _ T.K.π T.K.π_surj (fun g => Units.map φ.toMonoidHom (T.K.κA y.A g)) (fun g => ?_)
      ((types T.ok T.n23 T.S y.Fb f).1.2 hTI)
    rw [hm, h1]
    ext a b
    exact map_mul φ _ _

  have hred : RedTo (pushRep (algebraMap y.Fr y.Fb) y.ρF) φ (PowerSeries.constantCoeff : y.A →+* y.K)
      fun i => pushCh (algebraMap (ResidueField O) y.K) (T.r.chib i) := by
    intro g
    refine ⟨(mat y.ρ g).charpoly, by rw [hm, Matrix.charpoly_map], ?_⟩
    have h := congrArg (fun D => GDet.chi D (MonoidAlgebra.single g 1)) y.red
    simp only [Resid.Dbar, chi_map_ofRep] at h
    rw [h]
    change (Matrix.diagonal _).charpoly.map _ = _
    rw [Matrix.charpoly_diagonal, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl

  have hV : Nonempty F.V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    have h := T.big.1
    simp [Frame.d] at h
  obtain ⟨v'⟩ := hV
  obtain ⟨v, rfl⟩ := T.K.e.surjective v'

  have hfi : U.FiniteIndex := by
    haveI : CompactSpace T.G.G₀ :=
      isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ T.G.η_open).isCompact
    haveI := Subgroup.quotient_finite_of_isOpen U hU
    exact Subgroup.finiteIndex_of_finite_quotient
  have hUo : IsOpen (U.normalCore : Set T.G.G₀) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (Subgroup.normalCore_isClosed U (Subgroup.isClosed_of_isOpen U hU))
  haveI : T.G.G'.Normal := MonoidHom.normal_ker _
  have key := irrNormal T.G.G₀ y.Fb y.K y.A n hn (pushRep (algebraMap y.Fr y.Fb) y.ρF) hirr φ _ _ hφ hred
    (T.G.Gv v) (T.G.φ v) (fun i => pushCh φ (y.ψ v i)) (fun g => ?_) (U.normalCore ⊓ T.G.G') (fun a b hab => ?_) ?_
  · intro W hW
    exact key W fun g hg => hW g ⟨U.normalCore_le hg.1, hg.2⟩
  · have h := congrArg (Polynomial.map (algebraMap y.Fr y.Fb)) (charpoly_flag _ _ (y.flag v) g)
    rw [← Matrix.charpoly_map, chPoly, Polynomial.map_prod] at h
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
    exact h
  · obtain ⟨g, hg, hfr⟩ := niceSep l O F n T x L y j hj hp h1 h2 U.normalCore hUo v
    refine ⟨g, hg, fun h => hfr a b hab 1 one_pos ?_⟩
    rw [pow_one, pow_one]
    exact Units.ext ((algebraMap y.Fr y.Fb).injective (congrArg Units.val h))
  · obtain ⟨s, hs⟩ := T.ok.f3 (T.K.e v)
    obtain ⟨g, rfl⟩ := (T.K.lam v).surjective s
    obtain ⟨a, b, hab⟩ := w_ne T.n23 _ hs
    refine ⟨a, b, g, fun h => hab ?_⟩
    have h3 : T.r.chib a (T.G.φ v g) = T.r.chib b (T.G.φ v g) :=
      Units.ext ((algebraMap (ResidueField O) y.K).injective (congrArg Units.val h))
    rw [T.K.chib, T.K.chib, ← T.K.lam_loc] at h3
    exact mul_right_cancel h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceTypeE
set_option linter.overlappingInstances false

open Matrix UpperTheory.V UpperTheory.V.W UpperTheory.V.U3

namespace UpperTheory.V.Pr

private def blk {H K : Type} [Group H] [CommRing K] (ρ : H →* GL (Fin 3) K)
    (hz : ∀ g, mat ρ g 0 1 = 0 ∧ mat ρ g 1 0 = 0 ∧ mat ρ g 1 2 = 0 ∧ mat ρ g 2 1 = 0) :
    H →* GL (Fin 2) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => (mat ρ g).submatrix ![0, 2] ![0, 2]
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
      map_mul' := fun g h => by
        obtain ⟨a1, a2, a3, a4⟩ := hz g
        obtain ⟨b1, b2, b3, b4⟩ := hz h
        ext i j
        simp only [map_mul, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
        fin_cases i <;> fin_cases j <;>
          simp [map_mul, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, a1, a2, a3, a4, b1, b2, b3, b4] }

private def mid {H K : Type} [Group H] [CommRing K] (ρ : H →* GL (Fin 3) K)
    (hz : ∀ g, mat ρ g 0 1 = 0 ∧ mat ρ g 1 0 = 0 ∧ mat ρ g 1 2 = 0 ∧ mat ρ g 2 1 = 0) :
    H →* GL (Fin 1) K :=
  MonoidHom.toHomUnits
    { toFun := fun g => (mat ρ g).submatrix ![1] ![1]
      map_one' := by
        ext i j
        fin_cases i; fin_cases j; simp
      map_mul' := fun g h => by
        obtain ⟨a1, a2, a3, a4⟩ := hz g
        ext i j
        simp only [map_mul, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
        fin_cases i; fin_cases j
        simp [map_mul, Matrix.mul_apply, Fin.sum_univ_three, a2, a3] }

private def eqv : Fin 3 ≃ Fin 2 ⊕ Fin 1 where
  toFun := ![.inl 0, .inr 0, .inl 1]
  invFun := Sum.elim ![0, 2] ![1]
  left_inv := by decide
  right_inv := by decide

private theorem irr_one {H K : Type} [Group H] [Field K] (U : Subgroup H) (a : H → Matrix (Fin 1) (Fin 1) K) :
    MatIrr U a := by
  intro W _
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have h0 : v 0 ≠ 0 := fun h => hv0 (funext fun i => by fin_cases i; exact h)
    rw [eq_top_iff]
    intro u _
    have hu : u = (u 0 / v 0) • v := funext fun i => by
      fin_cases i
      simp [div_mul_cancel₀ _ h0]
    rw [hu]
    exact W.smul_mem _ hv

private theorem hom_zero {H K : Type} [Group H] [Field K] (U : Subgroup H) (a : H → Matrix (Fin 2) (Fin 2) K)
    (b : H → Matrix (Fin 1) (Fin 1) K) (h : MatIrr U a) (M : Matrix (Fin 1) (Fin 2) K)
    (hM : ∀ g ∈ U, M * a g = b g * M) : M = 0 := by
  have hinv : ∀ g ∈ U, ∀ v ∈ LinearMap.ker M.mulVecLin, a g *ᵥ v ∈ LinearMap.ker M.mulVecLin := by
    intro g hg v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hM g hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  rcases h _ hinv with hb | ht
  · have hv : ![M 0 1, -M 0 0] ∈ LinearMap.ker M.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      ext i
      fin_cases i
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    rw [hb, Submodule.mem_bot] at hv
    have h1 := congrFun hv 0
    have h2 := congrFun hv 1
    simp at h1 h2
    ext i j
    fin_cases i
    fin_cases j <;> simp [h1, h2]
  · ext i j
    have hj : (Pi.single j 1 : Fin 2 → K) ∈ LinearMap.ker M.mulVecLin := by
      rw [ht]
      trivial
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hj
    have := congrFun hj i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

private theorem tw_form {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {F : Fr.Frame l (IsLocalRing.ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
    {A : Type} [CommRing A] [Algebra O A] (ρ : Fr.NRep F n A) (g : G.G₀) :
    (K.tw ρ g)ᵀ * Jmat A n * K.tw ρ (G.conj g) = ((G.eps O A g ^ (1 - (n : ℤ)) : Aˣ) : A) • Jmat A n := by
  have hc : ∀ h : F.G0, F.conj h = F.star h⁻¹ := fun h => by simp [Fr.Frame.star]
  have hr : (ρ.r (K.π g))ᵀ * Jmat A n * ρ.r (F.conj (K.π g)) = Jmat A n := by
    rw [hc, ρ.pol]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc _ (Jmat A n) (Jmat A n), Jmat_mul_Jmat, Matrix.mul_one, ← Matrix.transpose_mul,
      ← map_mul, inv_mul_cancel, map_one, Matrix.transpose_one, Matrix.one_mul]
  have hκ : (K.κA A g : A) * (K.κA A (G.conj g) : A) = ((G.eps O A g ^ (1 - (n : ℤ)) : Aˣ) : A) := by
    have := congrArg (fun u : Oˣ => ((Units.map (algebraMap O A : O →* A) u : Aˣ) : A)) (K.κ_conj g)
    simp [TwLink.κA, GFrame.eps, pushCh, map_zpow] at this ⊢
    rw [this]
    rfl
  simp only [TwLink.tw, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    K.π_conj, hr, smul_smul]
  rw [← hκ, mul_comm]

private theorem blk_form {K : Type} [CommRing K] (X Y : Matrix (Fin 3) (Fin 3) K) (c : K)
    (hX : X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 1 2 = 0 ∧ X 2 1 = 0) (hY : Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 1 2 = 0 ∧ Y 2 1 = 0)
    (h : Xᵀ * Jmat K 3 * Y = c • Jmat K 3) :
    (X.submatrix ![0, 2] ![0, 2])ᵀ * Jmat K 2 * Y.submatrix ![0, 2] ![0, 2] = c • Jmat K 2 ∧
    (X.submatrix ![1] ![1])ᵀ * Jmat K 1 * Y.submatrix ![1] ![1] = c • Jmat K 1 := by
  obtain ⟨x1, x2, x3, x4⟩ := hX
  obtain ⟨y1, y2, y3, y4⟩ := hY
  have he : ∀ i j, (Xᵀ * Jmat K 3 * Y) i j = (c • Jmat K 3) i j := fun i j => by rw [h]
  constructor
  · ext i j
    have := he (![0, 2] i) (![0, 2] j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three] at this ⊢
    fin_cases i <;> fin_cases j <;>
      simp [Jmat, x1, x2, x3, x4, y1, y2, y3, y4] at this ⊢ <;>
      linear_combination this
  · ext i j
    have := he 1 1
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.smul_apply,
      Fin.sum_univ_one, Fin.sum_univ_three] at this ⊢
    fin_cases i
    fin_cases j
    simp [Jmat, x1, x2, x3, x4, y1, y2, y3, y4] at this ⊢
    linear_combination this

private def JU (K : Type) [CommRing K] (n : ℕ) : GL (Fin n) K := ⟨Jmat K n, Jmat K n, Jmat_mul_Jmat n, Jmat_mul_Jmat n⟩

end UpperTheory.V.Pr

theorem UpperTheory.V.Pr.niceTypeE :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (T : UpperTheory.V.Pr.Setup F 3) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → L.ρ.TE (RingHom.ker j) → y.TypeE := by
  intro l _ O _ _ _ _ _ F T x L y j hj hN hmat hψ hTE
  have hee : L.ρ.ee ≤ RingHom.ker j := hTE.2.2
  have hz0 : ∀ g (i k : Fin 3), Odd (Fr.w 3 i - Fr.w 3 k) → mat y.ρ g i k = 0 := by
    intro g i k hodd
    have hm : L.ρ.r (T.K.π g) i k ∈ RingHom.ker j := hee (Ideal.subset_span ⟨_, i, k, hodd, rfl⟩)
    rw [RingHom.mem_ker] at hm
    rw [hmat]
    simp [TwLink.tw, Fr.NRep.map, hm]
  have hz : ∀ g, mat y.ρF g 0 1 = 0 ∧ mat y.ρF g 1 0 = 0 ∧ mat y.ρF g 1 2 = 0 ∧ mat y.ρF g 2 1 = 0 := by
    intro g
    have e : ∀ i k, Odd (Fr.w 3 i - Fr.w 3 k) → mat y.ρF g i k = 0 := fun i k h => by
      show algebraMap y.A y.Fr (mat y.ρ g i k) = 0
      rw [hz0 g i k h, map_zero]
    refine ⟨e 0 1 ?_, e 1 0 ?_, e 1 2 ?_, e 2 1 ?_⟩ <;> decide
  have hF : ∀ g, (mat y.ρF g)ᵀ * Jmat y.Fr 3 * mat y.ρF (T.G.conj g) =
      ((T.G.eps O y.Fr g ^ (1 - ((3 : ℕ) : ℤ)) : y.Frˣ) : y.Fr) • Jmat y.Fr 3 := by
    intro g
    have h := UpperTheory.V.Pr.tw_form T.K (L.ρ.map (j : L.R →+* y.A)) g
    rw [← hmat] at h
    have h2 := congrArg (fun M => M.map (algebraMap y.A y.Fr)) h
    have heps : (T.G.eps O y.Fr g ^ (1 - ((3 : ℕ) : ℤ)) : y.Frˣ) =
        Units.map (algebraMap y.A y.Fr : y.A →* y.Fr) (T.G.eps O y.A g ^ (1 - ((3 : ℕ) : ℤ))) := by
      rw [map_zpow]
      congr 1
    have hs : ∀ (c : y.A) (M : Matrix (Fin 3) (Fin 3) y.A),
        (c • M).map (algebraMap y.A y.Fr) = algebraMap y.A y.Fr c • M.map (algebraMap y.A y.Fr) := fun c M => by
      ext
      simp
    rw [heps]
    simp only [Matrix.map_mul, Matrix.transpose_map, Jmat_map] at h2
    rw [hs, Jmat_map] at h2
    exact h2
  have hB := fun g => UpperTheory.V.Pr.blk_form _ _ _ (hz g) (hz (T.G.conj g)) (hF g)
  have hb : ∀ g, mat (UpperTheory.V.Pr.blk y.ρF hz) g = (mat y.ρF g).submatrix ![0, 2] ![0, 2] := fun g => rfl
  have hm : ∀ g, mat (UpperTheory.V.Pr.mid y.ρF hz) g = (mat y.ρF g).submatrix ![1] ![1] := fun g => rfl
  have hirr := UpperTheory.V.Pr.niceIrrE l O F T x L y j hj hN hmat hψ hTE ⊤ isOpen_univ
  rw [top_inf_eq] at hirr
  have hirr1 : MatIrr T.G.G' (mat (pushRep (algebraMap y.Fr y.Fb) (UpperTheory.V.Pr.blk y.ρF hz))) := hirr
  refine ⟨2, 1, by norm_num, le_rfl, UpperTheory.V.Pr.eqv, 1, UpperTheory.V.Pr.blk y.ρF hz, UpperTheory.V.Pr.mid y.ρF hz,
    ?_, ⟨UpperTheory.V.Pr.JU _ 2, ?_⟩, ⟨UpperTheory.V.Pr.JU _ 1, ?_⟩, hirr1, UpperTheory.V.Pr.irr_one _ _, ?_⟩
  · intro g
    have h1 : ((1 * y.ρF g * 1⁻¹ : GL (Fin 3) y.Fr) : Matrix (Fin 3) (Fin 3) y.Fr) = mat y.ρF g := by
      simp [mat]
    obtain ⟨a1, a2, a3, a4⟩ := hz g
    rw [h1, hb, hm]
    ext (i | i) (k | k) <;> fin_cases i <;> fin_cases k
    all_goals first
      | rfl
      | (simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
         first | exact a1 | exact a2 | exact a3 | exact a4)
  · intro g
    rw [hb, hb]
    exact (hB g).1
  · intro g
    rw [hm, hm]
    exact (hB g).2
  · intro M hM
    exact UpperTheory.V.Pr.hom_zero _ _ _ hirr1 M hM
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSpecializationTwistSatisfiesThirdCondition
open Matrix Polynomial IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg

namespace UpperTheory.V.Pr

private lemma open_basis {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (O : Set G) (hO : IsOpen O) (h1 : (1 : G) ∈ O) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ (V : Set G) ⊆ O := by
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1
  exact ⟨H.toSubgroup, H.isOpen', hH⟩

private lemma strong_of {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] {m : ℕ} (G' V : Subgroup G) (hV : IsOpen (V : Set G))
    (r : G →* GL (Fin m) κ) (hc : LinClosed (gm r))
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') (gm r)) :
    StrongIrr (r.comp (V ⊓ G').subtype) := by
  refine strongIrrOfOpen _ κ m _ (fun f => (hc f).preimage continuous_subtype_val) ?_
  intro U hU W hW
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 hU
  have h1 : (1 : G) ∈ O := by
    have : (1 : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G')) := U.one_mem
    rw [← hOU] at this
    exact this
  obtain ⟨V', hV', hsub⟩ := open_basis (O ∩ V) (hO.inter hV) ⟨h1, V.one_mem⟩
  refine hirr V' hV' W fun g hg => ?_
  have h2 := hsub hg.1
  have h3 : (⟨g, h2.2, hg.2⟩ : ↥(V ⊓ G')) ∈ (U : Set ↥(V ⊓ G')) := by
    rw [← hOU]; exact h2.1
  exact hW _ h3

private lemma coset_in {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (U : Set G) (hU : IsOpen U) (s : G) (hs : s ∈ U) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ h ∈ V, s * h ∈ U := by
  obtain ⟨V, hV, hsub⟩ := open_basis ((fun h => s * h) ⁻¹' U) (hU.preimage (continuous_const.mul continuous_id))
    (by simpa using hs)
  exact ⟨V, hV, fun h hh => hsub hh⟩

private lemma cosetI {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] {n : ℕ} (hn : n ≤ 3) (G' : Subgroup G)
    (r : G →* GL (Fin n) κ) (hc : LinClosed (gm r))
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') (gm r))
    (hsep : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ u ∈ U ⊓ G', ∃ α : Fin n → κˣ, FreeRatios α ∧
      (gm r u).charpoly = ∏ i, (X - C ((α i : κˣ) : κ)))
    (U : Set G) (hU : IsOpen U) (hne : (U ∩ (G' : Set G)).Nonempty) :
    ∃ σ ∈ U ∩ (G' : Set G), (gm r σ).charpoly.Separable := by
  obtain ⟨s, hs, hs'⟩ := hne
  obtain ⟨V, hV, hsV⟩ := coset_in U hU s hs
  obtain ⟨u, hu, α, hα, hch⟩ := hsep V hV
  obtain ⟨h, hh⟩ := regCoset _ κ n hn _ (strong_of G' V hV r hc hirr) ⟨u, hu⟩ α hα hch (r s)
  refine ⟨s * h, ⟨hsV _ h.2.1, G'.mul_mem hs' h.2.2⟩, ?_⟩
  simp only [gm, map_mul, Units.val_mul]
  exact hh

private lemma sub_eq {κ : Type} (M : Matrix (Fin 3) (Fin 3) κ) :
    M.submatrix ![0, 2] ![0, 2] = !![M 0 0, M 0 2; M 2 0, M 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private def cornerHom {G κ : Type} [Group G] [Field κ] (r : G →* GL (Fin 3) κ)
    (hb : ∀ g, gm r g 0 1 = 0 ∧ gm r g 1 0 = 0 ∧ gm r g 1 2 = 0 ∧ gm r g 2 1 = 0) :
    G →* Matrix (Fin 2) (Fin 2) κ where
  toFun g := (gm r g).submatrix ![0, 2] ![0, 2]
  map_one' := by
    rw [sub_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gm]
  map_mul' g h := by
    obtain ⟨a1, a2, a3, a4⟩ := hb g
    obtain ⟨b1, b2, b3, b4⟩ := hb h
    simp only [gm] at a1 a2 a3 a4 b1 b2 b3 b4
    rw [sub_eq, sub_eq, sub_eq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [gm, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, *]

private def midHom {G κ : Type} [Group G] [Field κ] (r : G →* GL (Fin 3) κ)
    (hb : ∀ g, gm r g 0 1 = 0 ∧ gm r g 1 0 = 0 ∧ gm r g 1 2 = 0 ∧ gm r g 2 1 = 0) : G →* κ where
  toFun g := gm r g 1 1
  map_one' := by simp [gm]
  map_mul' g h := by
    obtain ⟨a1, a2, a3, a4⟩ := hb g
    simp only [gm] at a1 a2 a3 a4
    simp [gm, Matrix.mul_apply, Fin.sum_univ_three, *]

private lemma charpoly_block {κ : Type} [Field κ] (M : Matrix (Fin 3) (Fin 3) κ)
    (hb : M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 1 = 0) :
    M.charpoly = (M.submatrix ![0, 2] ![0, 2]).charpoly * (X - C (M 1 1)) := by
  obtain ⟨a1, a2, a3, a4⟩ := hb
  rw [sub_eq]
  simp only [Matrix.charpoly, det_fin_three, det_fin_two]
  simp [charmatrix_apply, *]
  ring

private lemma cosetE {G κ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [Field κ] (G' : Subgroup G)
    (r : G →* GL (Fin 3) κ) (hc : LinClosed (gm r))
    (hb : ∀ g, gm r g 0 1 = 0 ∧ gm r g 1 0 = 0 ∧ gm r g 1 2 = 0 ∧ gm r g 2 1 = 0)
    (hirr : ∀ U : Subgroup G, IsOpen (U : Set G) → MatIrr (U ⊓ G') fun g => (gm r g).submatrix ![0, 2] ![0, 2])
    (hsep : ∀ U : Subgroup G, IsOpen (U : Set G) → ∃ u ∈ U ⊓ G', ∃ α : Fin 3 → κˣ, FreeRatios α ∧
      (gm r u).charpoly = ∏ i, (X - C ((α i : κˣ) : κ)))
    (U : Set G) (hU : IsOpen U) (hne : (U ∩ (G' : Set G)).Nonempty) :
    ∃ σ ∈ U ∩ (G' : Set G), (gm r σ).charpoly.Separable := by
  obtain ⟨s, hs, hs'⟩ := hne
  obtain ⟨V, hV, hsV⟩ := coset_in U hU s hs
  obtain ⟨u, hu, α, hα, hch⟩ := hsep V hV
  let σ : G →* GL (Fin 2) κ := (cornerHom r hb).toHomUnits
  let ψ : G →* κˣ := (midHom r hb).toHomUnits
  have hσ : ∀ g, gm σ g = (gm r g).submatrix ![0, 2] ![0, 2] := fun g => rfl
  have hψ : ∀ g, ((ψ g : κˣ) : κ) = gm r g 1 1 := fun g => rfl
  have hcp : ∀ g, (gm r g).charpoly = (gm σ g).charpoly * (X - C ((ψ g : κˣ) : κ)) := fun g =>
    charpoly_block _ (hb g)
  have hcσ : LinClosed (gm σ) := fun f =>
    hc (f ∘ₗ
      { toFun := fun M : Matrix (Fin 3) (Fin 3) κ => M.submatrix ![0, 2] ![0, 2]
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl })
  obtain ⟨k, hk⟩ : ∃ k, α k = ψ u := by
    have h1 := congrArg (Polynomial.eval ((ψ u : κˣ) : κ)) ((hcp u).symm.trans hch)
    rw [eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, eval_prod, eq_comm, Finset.prod_eq_zero_iff] at h1
    obtain ⟨k, -, hk⟩ := h1
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hk
    exact ⟨k, Units.ext hk.symm⟩
  have hch2 : (gm σ u).charpoly = ∏ i : Fin 2, (X - C ((α (k.succAbove i) : κˣ) : κ)) := by
    have h1 := (hcp u).symm.trans hch
    rw [Fin.prod_univ_succAbove _ k, hk, mul_comm] at h1
    exact mul_left_cancel₀ (X_sub_C_ne_zero _) h1
  have hfree : FreeRatios ![α (k.succAbove 0), α (k.succAbove 1), ψ u] := by
    have e : ![α (k.succAbove 0), α (k.succAbove 1), ψ u] = α ∘ ![k.succAbove 0, k.succAbove 1, k] := by
      funext i
      fin_cases i <;> simp [hk]
    have inj : Function.Injective (![k.succAbove 0, k.succAbove 1, k] : Fin 3 → Fin 3) := by
      clear hk hch2 e
      revert k
      decide
    rw [e]
    exact fun i j hij => hα _ _ (inj.ne hij)
  obtain ⟨h, hh⟩ := regCosetE _ κ _ (ψ.comp (V ⊓ G').subtype) (strong_of G' V hV σ hcσ hirr) ⟨u, hu⟩
    (fun i => α (k.succAbove i)) hfree hch2 (σ s) (ψ s)
  refine ⟨s * h, ⟨hsV _ h.2.1, G'.mul_mem hs' h.2.2⟩, ?_⟩
  rw [hcp]
  simp only [gm, map_mul σ, map_mul ψ, Units.val_mul (σ s)]
  exact hh

private lemma charpoly_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : W.HasFlag r κ) (s : H) :
    (W.mat r s).charpoly = ∏ i, (X - C ((κ i s : kˣ) : k)) := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨h1, h2⟩ := hg s
  have h3 := Matrix.charpoly_of_upperTriangular ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
    (fun i j hij => h1 i j hij)
  simp only [h2] at h3
  rw [← h3, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  rfl

end UpperTheory.V.Pr

theorem UpperTheory.V.Pr.nice_specialization_twist_satisfies_third_condition :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → y.N3 := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hnice hρ hψ U hU hne
  haveI : CompactSpace T.G.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ T.G.η_open).isCompact
  let r : T.G.G₀ →* GL (Fin n) y.Fb := W.pushRep (algebraMap y.Fr y.Fb) y.ρF
  have hr : ∀ g, gm r g = (W.mat y.ρF g).map (algebraMap y.Fr y.Fb) := fun g => rfl
  have hc : LinClosed (gm r) :=
    linClosedOfAdic T.G.G₀ y.A y.Fb ((algebraMap y.Fr y.Fb).comp (algebraMap y.A y.Fr))
      ((algebraMap y.Fr y.Fb).injective.comp (IsFractionRing.injective y.A y.Fr)) n (fun g => W.mat y.ρ g) y.cont
  obtain ⟨v⟩ : Nonempty T.G.Vl := by
    rw [T.K.e.nonempty_congr]
    by_contra h
    rw [not_nonempty_iff] at h
    have := T.big.1
    simp [Fr.Frame.d] at this
  have hsep : ∀ V : Subgroup T.G.G₀, IsOpen (V : Set T.G.G₀) → ∃ u ∈ V ⊓ T.G.G', ∃ α : Fin n → y.Fbˣ, FreeRatios α ∧
      (gm r u).charpoly = ∏ i, (X - C ((α i : y.Fbˣ) : y.Fb)) := by
    intro V hV
    obtain ⟨g, hg, hfree⟩ := niceSep l O F n T x L y j hj hnice hρ hψ V hV v
    refine ⟨_, hg, fun i => Units.map (algebraMap y.Fr y.Fb).toMonoidHom
      (Units.map (algebraMap y.A y.Fr).toMonoidHom (y.ψ v i g)), fun a b hab m hm h => hfree a b hab m hm ?_, ?_⟩
    · refine Units.map_injective (f := (algebraMap y.Fr y.Fb).toMonoidHom) (algebraMap y.Fr y.Fb).injective ?_
      rw [map_pow, map_pow]
      exact h
    · have h1 : (W.mat y.ρF (T.G.φ v g)).charpoly = _ := charpoly_flag _ _ (y.flag v) g
      rw [hr, Matrix.charpoly_map, h1, Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Polynomial.map_sub, map_X, map_C]
      rfl
  suffices h : ∃ σ ∈ U ∩ (T.G.G' : Set T.G.G₀), (gm r σ).charpoly.Separable by
    obtain ⟨σ, h1, h2⟩ := h
    rw [hr, Matrix.charpoly_map, Polynomial.separable_map] at h2
    exact ⟨σ, h1, h2⟩
  by_cases hE : n = 3 ∧ L.ρ.ee ≤ RingHom.ker j
  · obtain ⟨rfl, hE⟩ := hE
    have hz : ∀ g a b, Odd (Fr.w 3 a - Fr.w 3 b) → gm r g a b = 0 := by
      intro g a b hab
      have h1 : j (L.ρ.r (T.K.π g) a b) = 0 := hE (Ideal.subset_span ⟨_, a, b, hab, rfl⟩)
      have h2 : W.mat y.ρ g a b = 0 := by
        rw [hρ]
        show _ * j (L.ρ.r (T.K.π g) a b) = 0
        rw [h1, mul_zero]
      show algebraMap y.Fr y.Fb (algebraMap y.A y.Fr (W.mat y.ρ g a b)) = 0
      rw [h2, map_zero, map_zero]
    exact cosetE T.G.G' r hc
      (fun g => ⟨hz g 0 1 (by decide), hz g 1 0 (by decide), hz g 1 2 (by decide), hz g 2 1 (by decide)⟩)
      (niceIrrE l O F T x L y j hj hnice hρ hψ ⟨hnice.off, rfl, hE⟩) hsep U hU hne
  · exact cosetI (by rcases T.n23 with h | h <;> omega) T.G.G' r hc
      (niceIrr l O F n T x L y j hj hnice hρ hψ ⟨hnice.off, fun h3 h => hE ⟨h3, h⟩⟩) hsep U hU hne
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSpecializationTwistSatisfiesFirstCondition
theorem UpperTheory.V.Pr.nice_specialization_twist_satisfies_first_condition :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → y.N1 := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hN hm hψ v
  obtain ⟨g, hgU, hfr⟩ := UpperTheory.V.Pr.niceSep l O F n T x L y j hj hN hm hψ ⊤
    (by simp) v
  have hG : T.G.φ v g ∈ T.G.G' := (Subgroup.mem_inf.mp hgU).2
  have he : (T.G.eps O y.A) (T.G.φ v g) = 1 := by
    rw [UpperTheory.V.W.GFrame.G', MonoidHom.mem_ker] at hG
    have hG' : T.G.ε ↑(T.G.φ v g) = 1 := hG
    simp [UpperTheory.V.W.GFrame.eps, UpperTheory.V.W.pushCh, hG']
  refine ⟨fun i k hik h => hfr i k hik 1 one_pos (by simp [h]), fun i k hik h => ?_⟩
  apply hfr i k (ne_of_lt hik) 1 one_pos
  simp [h, MonoidHom.mul_apply, he]
end

theorem UpperTheory.V.Pr.niceOf :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n), T.NiceOf := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hp h1 h2
  refine ⟨UpperTheory.V.Pr.nice_specialization_twist_satisfies_first_condition l O F n T x L y j hj hp h1 h2, UpperTheory.V.Pr.nice_specialization_twist_satisfies_third_condition l O F n T x L y j hj hp h1 h2,
    fun hI => ?_, fun hE => ?_⟩
  · have h := UpperTheory.V.Pr.niceIrr l O F n T x L y j hj hp h1 h2 hI ⊤ (by simp)
    rw [top_inf_eq] at h
    exact h
  · obtain rfl : n = 3 := hE.2.1
    exact UpperTheory.V.Pr.niceTypeE l O F T x L y j hj hp h1 h2 hE
