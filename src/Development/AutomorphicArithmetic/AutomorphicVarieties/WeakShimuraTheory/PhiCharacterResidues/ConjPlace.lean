module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

open scoped Pointwise in
private theorem val_lt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (t : G F Ω) (y : Ω) :
    (t⁻¹ • A).valuation y < 1 ↔ A.valuation (t y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_inv_pointwise_smul_iff,
    ValuationSubring.mem_inv_pointwise_smul_iff]
  simp only [AlgEquiv.smul_def, map_inv₀, map_eq_zero]

open scoped Pointwise in
private theorem conj_place {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (t : G F Ω) :
    IsPlaceOver (t⁻¹ • A) v ∧ ∀ σ ∈ Ine (F := F) A, t⁻¹ * σ * t ∈ Ine (F := F) (t⁻¹ • A) := by
  refine ⟨fun x => ?_, fun σ hσ => ?_⟩
  · rw [val_lt, AlgEquiv.commutes]
    exact h x
  · obtain ⟨hd, hi⟩ := hσ
    refine ⟨?_, fun x hx => ?_⟩
    · rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hd ⊢
      rw [mul_smul, mul_smul, smul_inv_smul, hd]
    · rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_inv_pointwise_smul_iff,
        AlgEquiv.smul_def] at hx
      rw [val_lt, map_sub]
      have := hi (t x) ((ValuationSubring.valuation_le_one_iff A _).2 hx)
      simpa [AlgEquiv.mul_apply, mul_inv_apply] using this

theorem UpperTheory.V.Ws.phiKer :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev), Function.Surjective V.pr ∧ Topology.IsQuotientMap V.pr ∧ ∀ U : Subgroup (G L Ω), IsClosed (U : Set (G L Ω)) → (∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ V.S' → Ine (F := L) A ≤ U) → V.pr.ker ≤ U := by
  intro l _ L Ω _ _ _ _ _ _ s V
  have hres : ∀ (g : G L Ω) (x : Ω), W.resP L Ω g x = g x := fun _ _ => rfl
  have hinj : Function.Injective (W.resP L Ω) := fun a b h =>
    AlgEquiv.ext fun x => by rw [← hres a x, ← hres b x, h]
  have hsurj : Function.Surjective V.pr := by
    rintro ⟨y, hy⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (NS Ω V.S') y
    obtain ⟨g, rfl⟩ := (V.hη g').1 hy
    exact ⟨g, rfl⟩
  have hcont : Continuous V.pr := V.pr_cont W.continuous_resP
  haveI : IsClosed ((NS Ω V.S' : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) := isClosed_NS Ω V.S'
  haveI : T2Space (GS Ω V.S') := by
    unfold GS
    infer_instance
  refine ⟨hsurj, (hcont.isClosedMap).isQuotientMap hcont hsurj, fun U hU hI g hg => ?_⟩
  open scoped Pointwise in
  have hsm : ∀ (g : G L Ω) (B : ValuationSubring Ω), W.resP L Ω g • B = g • B := by
    intro g B
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def,
      AlgEquiv.smul_def, hres]
  have hM : IsClosed ((U.map (W.resP L Ω) : Subgroup (G (W.Lp L) Ω)) : Set (G (W.Lp L) Ω)) := by
    rw [Subgroup.coe_map]
    exact ((hU.isCompact).image W.continuous_resP).isClosed
  have hle : NS Ω V.S' ≤ U.map (W.resP L Ω) := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ hM
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro c hc
    rw [Group.mem_conjugatesOfSet_iff] at hc
    obtain ⟨a, ha, hac⟩ := hc
    obtain ⟨d, rfl⟩ := isConj_iff.1 hac
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq, exists_prop] at ha
    obtain ⟨v, hv, A, hA, haA⟩ := ha
    have key := conj_place hA d⁻¹
    simp only [inv_inv] at key
    obtain ⟨hA', hconj⟩ := key
    have hb := hconj a haA
    obtain ⟨g0, hg0⟩ := s.unr _ v hA' hb
    refine ⟨g0, hI _ v hA' hv ?_, hg0⟩
    rw [← hg0] at hb
    obtain ⟨hd, hi⟩ := hb
    refine ⟨?_, fun x hx => ?_⟩
    · open scoped Pointwise in
      rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff] at hd ⊢
      open scoped Pointwise in
      rwa [← hsm]
    · have := hi x hx
      rwa [hres] at this
  have hgN : W.resP L Ω g ∈ NS Ω V.S' := by
    rw [MonoidHom.mem_ker, Subtype.ext_iff] at hg
    exact (QuotientGroup.eq_one_iff _).1 hg
  obtain ⟨u, hu, hug⟩ := hle hgN
  rw [← hinj hug]
  exact hu
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolySmulUnit
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem charpoly_smul_unit {R n : Type} [CommRing R] [Nontrivial R] [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (c : R) (hc : IsUnit c) : (c • M).charpoly = M.charpoly.scaleRoots c := by
  have hinj : ∀ p q : R[X], p.comp (C c * X) = q.comp (C c * X) → p = q := by
    intro p q h
    ext i
    have hi := congrArg (fun r => r.coeff i) h
    simp only [comp_C_mul_X_coeff] at hi
    exact (hc.pow i).mul_right_cancel hi
  have key : (Polynomial.eval₂RingHom C (C c * X)).mapMatrix (Matrix.charmatrix (c • M)) =
      C c • Matrix.charmatrix M := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.charmatrix_apply_eq, Matrix.smul_apply, C_mul, mul_sub]
    · simp [Matrix.charmatrix_apply_ne _ _ _ h, Matrix.smul_apply, C_mul]
  have hL : (c • M).charpoly.comp (C c * X) = C c ^ Fintype.card n * M.charpoly := by
    calc (c • M).charpoly.comp (C c * X)
        = Polynomial.eval₂RingHom C (C c * X) (Matrix.charmatrix (c • M)).det := rfl
      _ = (C c • Matrix.charmatrix M).det := by rw [RingHom.map_det, key]
      _ = C c ^ Fintype.card n * M.charpoly := by rw [Matrix.det_smul]; rfl
  have hR : (M.charpoly.scaleRoots c).comp (C c * X) = C c ^ Fintype.card n * M.charpoly := by
    ext i
    rw [comp_C_mul_X_coeff, coeff_scaleRoots, ← C_pow, coeff_C_mul, Matrix.charpoly_natDegree_eq_dim]
    by_cases hi : i ≤ Fintype.card n
    · rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hi, mul_comm]
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim]; omega)]
      simp
  apply hinj
  rw [hL, hR]

theorem UpperTheory.V.Ws.phiCpMap :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ g, (X.cp (resLe T.F_le g)).Monic ∧ (X.cp (resLe T.F_le g)).natDegree = 4 ∧ (K.cpT X n g).Monic ∧ (K.cpT X n g).map (algebraMap X.B X.A) = (K.rho X n g).charpoly := by
  intro Ω _ _ _ l _ c D T c' h K X n g
  have hinj : Function.Injective (algebraMap X.B X.A) := X.inj
  haveI : Nontrivial X.A := hinj.nontrivial
  have hmap := X.cp_map (resLe T.F_le g)
  have hmon : (X.cp (resLe T.F_le g)).Monic :=
    monic_of_injective hinj (by rw [hmap]; exact Matrix.charpoly_monic _)
  have hdeg : (X.cp (resLe T.F_le g)).natDegree = 4 := by
    rw [← natDegree_map_eq_of_injective hinj, hmap, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  have hmonT : (K.cpT X n g).Monic := by
    show ((X.cp (resLe T.F_le g)).scaleRoots _).leadingCoeff = 1
    rw [leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots_natDegree]
    exact hmon
  refine ⟨hmon, hdeg, hmonT, ?_⟩
  have hu : IsUnit (K.sc n g) := by
    simp only [UpperTheory.V.Ws.Link.sc]
    exact (Units.isUnit _).mul ((Units.isUnit _).pow n)
  show ((X.cp (resLe T.F_le g)).scaleRoots _).map (algebraMap X.B X.A) = _
  rw [map_scaleRoots _ _ _ (by rw [hmon.leadingCoeff, map_one]; exact one_ne_zero), hmap,
    UpperTheory.V.Ws.Link.rho_apply, charpoly_smul_unit _ _ (hu.map _), ← IsScalarTower.algebraMap_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolyGspConjInvScaled
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.AdjEqConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private def formJ (R : Type) [CommRing R] : M4 R := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

private theorem formJ_mul (R : Type) [CommRing R] : (formJ R).transpose * formJ R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [formJ, Matrix.mul_apply, Fin.sum_univ_four]

private theorem adj_eq_conj {R : Type} [CommRing R] (M : M4 R) :
    adj M = formJ R * (M.transpose * (formJ R).transpose) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [formJ, adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four]

theorem UpperTheory.V.Ws.phiAdj :
    ∀ {R : Type} [CommRing R] (ν : R) (M N : M4 R), IsGSp ν M → M * N = 1 → (ν • N).charpoly = M.charpoly := by
  intro R _ ν M N hM hMN
  have h1 : adj M = ν • N := by
    have h2 : adj M * M * N = ν • N := by
      unfold IsGSp at hM
      rw [hM, smul_mul_assoc, one_mul]
    rw [mul_assoc, hMN, mul_one] at h2
    exact h2
  rw [← h1, adj_eq_conj, Matrix.charpoly_mul_comm, mul_assoc, formJ_mul, mul_one, Matrix.charpoly_transpose]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.PhiConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiConj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D) (s : W.HidaSetting l T.L Ω), ∃ cF : G T.F Ω, ∀ g : G T.L Ω, ∃ g' : G T.L Ω, W.resP T.L Ω g' = s.c * W.resP T.L Ω g * s.c⁻¹ ∧ resLe T.F_le g' = cF * resLe T.F_le g * cF⁻¹ := by
  intro Ω _ _ _ l _ c D T s
  obtain ⟨j, hj⟩ := s.hc
  have hfixF : ∀ x : T.F, s.c (x : Ω) = x := by
    intro x
    have hr := IsTotallyReal.complexEmbedding_isReal (j.comp (algebraMap T.F Ω))
    have := RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.1 hr) x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at this
    apply j.injective
    rw [hj]
    exact this
  have hstab : ∀ (τ : G (W.Lp T.L) Ω) (x : T.L), ∃ y : T.L, τ (x : Ω) = y := by
    intro τ x
    exact ⟨τ.restrictNormal T.L x, (AlgEquiv.restrictNormal_commutes τ T.L x).symm⟩
  let cF : G T.F Ω := AlgEquiv.ofRingEquiv (f := s.c.toRingEquiv) (fun x => hfixF x)
  refine ⟨cF, fun g => ?_⟩
  let σ : G (W.Lp T.L) Ω := s.c * W.resP T.L Ω g * s.c⁻¹
  have hσ : ∀ x : T.L, σ (x : Ω) = x := by
    intro x
    obtain ⟨y, hy⟩ := hstab s.c⁻¹ x
    have h1 : g (y : Ω) = y := g.commutes y
    have h2 : s.c (y : Ω) = x := by
      rw [← hy]
      exact mul_inv_apply (σ := s.c) (x : Ω)
    show s.c (g (s.c⁻¹ (x : Ω))) = x
    rw [hy, h1, h2]
  let g' : G T.L Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => hσ x)
  refine ⟨g', ?_, ?_⟩
  · ext x
    rfl
  · ext x
    rfl
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem charpoly_gsp_conj_inv_scaled {R Γ : Type} [CommRing R] [Group Γ] (r : Γ →* M4 R) (x y : Γ) (ν s s' t : R)
    (hr : IsGSp ν (r x)) (hs : s * s' = 1) (ht : t = s * ν) :
    (t • r (y * x * y⁻¹)⁻¹).charpoly = (s • r x).charpoly := by
  have h1 : IsGSp (s * s * ν) (s • r x) := by
    have ha : adj (s • r x) = s • adj (r x) := by
      ext i j
      simp only [adj_apply, Matrix.smul_apply]
      rw [smul_comm]
    unfold IsGSp at hr ⊢
    rw [ha, Matrix.smul_mul, Matrix.mul_smul, hr, smul_smul, smul_smul]
  have h2 : (s • r x) * (s' • r x⁻¹) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, one_smul, ← map_mul, mul_inv_cancel, map_one]
  have h3 := phiAdj _ _ _ h1 h2
  rw [← h3, smul_smul]
  have h4 : s * s * ν * s' = t := by rw [ht]; linear_combination (s * ν) * hs
  rw [h4]
  have h5 : t • r (y * x * y⁻¹)⁻¹ = r y * ((t • r x⁻¹) * r y⁻¹) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, ← map_mul, ← map_mul]
    congr 2
    group
  rw [h5, Matrix.charpoly_mul_comm, Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one]

theorem UpperTheory.V.Ws.phiPol :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ g, ∃ g', K.V.pr g' = (K.V.frame.conj (K.V.pr g))⁻¹ ∧ (((K.V.frame.eps c'.O X.A (K.V.pr g) ^ (1 - ((4 : ℕ) : ℤ)) : X.Aˣ) : X.A) • K.rho X n g').charpoly = (K.rho X n g).charpoly := by
  intro Ω _ _ _ l _ c D T c' h K X n g
  obtain ⟨cF, hc⟩ := phiConj T K.s
  obtain ⟨g₂, h1, h2⟩ := hc g
  refine ⟨g₂⁻¹, ?_, ?_⟩
  · rw [map_inv]
    congr 1
    apply Subtype.ext
    change toGS Ω K.V.S' (W.resP T.L Ω g₂) = toGS Ω K.V.S' K.s.c * toGS Ω K.V.S' (W.resP T.L Ω g) * (toGS Ω K.V.S' K.s.c)⁻¹
    rw [h1, map_mul, map_mul, map_inv]
  · obtain ⟨k1, k2, -⟩ := K.conj g g₂ h1
    have he : K.V.frame.eps c'.O X.A (K.V.pr g) =
        Units.map (algebraMap c'.O X.A : c'.O →* X.A) (chiO T.L Ω l c'.O g) := by
      have : K.V.ε (toGS Ω K.V.S' (W.resP T.L Ω g)) = cycZ T.L Ω l g := DFunLike.congr_fun K.V.hε (W.resP T.L Ω g)
      apply Units.ext
      change algebraMap c'.O X.A (algebraMap ℤ_[l] c'.O (K.V.ε (toGS Ω K.V.S' (W.resP T.L Ω g)) : ℤ_[l]ˣ)) = _
      rw [this]
      rfl
    rw [Link.rho_apply, Link.rho_apply, smul_smul, map_inv, h2, he]
    refine charpoly_gsp_conj_inv_scaled X.P.r _ _ _ _ (algebraMap c'.O X.A (K.sc n g⁻¹)) _ (X.pair.mult (resLe T.F_le g)) ?_ ?_
    · rw [← map_mul, ← Link.sc_mul, mul_inv_cancel, Link.sc_one, map_one]
    · have hb : K.β g₂⁻¹ = K.β g := by rw [map_inv]; exact (eq_inv_of_mul_eq_one_left k2).symm
      rw [← map_zpow, Units.coe_map]
      change algebraMap c'.O X.A _ * _ = _ * algebraMap c'.O X.A (inc h (D.th (resQ T.L g)))
      rw [← map_mul, ← map_mul]
      congr 1
      simp only [Link.sc, hb]
      set e := chiO T.L Ω l c'.O g
      have e1 : ((e ^ (1 - ((4 : ℕ) : ℤ)) : c'.Oˣ) : c'.O) * (e : c'.O) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
        norm_num
      have e2 : ((K.κ g₂⁻¹ : c'.Oˣ) : c'.O) * K.κ g₂ = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      generalize ((e ^ (1 - ((4 : ℕ) : ℤ)) : c'.Oˣ) : c'.O) = u at e1 ⊢
      generalize ((K.κ g₂⁻¹ : c'.Oˣ) : c'.O) = v at e2 ⊢
      generalize (inc h (D.th (resQ T.L g)) : c'.O) = θ at k1 ⊢
      generalize ((K.β g : c'.Oˣ) : c'.O) ^ n = b
      linear_combination (-u * v * b) * k1 + (b * (K.κ g : c'.O) * θ * u * (e : c'.O) ^ 3) * e2 + (b * (K.κ g : c'.O) * θ) * e1
end
