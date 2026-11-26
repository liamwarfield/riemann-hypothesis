module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigDiag
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem rigDiag_fst_mul {K : Type} [Field K] (M N : Matrix (Fin 3) (Fin 3) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.fst = M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.fst := by
  ext i j
  simp [Matrix.mul_apply, TrivSqZeroExt.fst_sum]

private theorem rigDiag_snd_mul {K : Type} [Field K] (M N : Matrix (Fin 3) (Fin 3) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.snd =
      M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.snd + M.map TrivSqZeroExt.snd * N.map TrivSqZeroExt.fst := by
  ext i j
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, Finset.sum_add_distrib]

private theorem rigDiag_conj_mat {R D : Type} [CommRing R] [Group D] (h : GL (Fin 3) R)
    (r : D →* GG (m := 3) (R := R)) (s : D)
    (hs : (r s).right = 1) :
    (h : Matrix (Fin 3) (Fin 3) R) * (conjBy h⁻¹ r s).mat = (r s).mat * h := by
  simp [conjBy, GG.mat, GG.ofGL, SemidirectProduct.mul_left, SemidirectProduct.inv_left, hs]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units h), Matrix.one_mul]

theorem UpperTheory.V.UnitaryThreeInertia.rig_diag :
    ∀ {O K D : Type} [CommRing O] [IsLocalRing O] [Field K] [Algebra O K] [Group D]
      (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG (m := 3) (R := K))
      (y : D → Matrix (Fin 3) (Fin 3) K) (r' : D →* GG (m := 3) (R := DualNumber K))
      (h : GL (Fin 3) (DualNumber K)),
      (∀ s ∈ I, η s = 1) → HasMult η r →
      IsDeform ((GG.map (algebraMap K (DualNumber K))).comp r)
        (fun g => (y g).map (TrivSqZeroExt.inr : K → DualNumber K)) r' →
      DiagIn η Ψ I r' h → ∃ X, ∀ s ∈ I, y s = adRep r s X - X := by
  intro O K D _ _ _ _ _ η Ψ I r y r' h hI hm hd hD
  set H : Matrix (Fin 3) (Fin 3) (DualNumber K) := (h : Matrix (Fin 3) (Fin 3) (DualNumber K)) with hH
  set Hi : Matrix (Fin 3) (Fin 3) (DualNumber K) := (↑h⁻¹ : Matrix (Fin 3) (Fin 3) (DualNumber K)) with hHi
  refine ⟨-(H.map TrivSqZeroExt.snd * Hi.map TrivSqZeroExt.fst), fun s hs => ?_⟩
  have hη : η s = 1 := hI s hs
  have hr1 : (r s).right = 1 := (hm s).trans hη
  have hd1 := hd s
  have hr'1 : (r' s).right = 1 := by
    rw [hd1.1]
    simpa [GG.map] using hr1
  have hmat : (r' s).mat = (1 + (y s).map TrivSqZeroExt.inr) * (r s).mat.map (algebraMap K (DualNumber K)) := by
    rw [hd1.2]
    simp [GG.map, GG.mat]
  have hker : s ∈ η.ker := hη
  have hoff : ∀ a b, ((conjBy h⁻¹ r' s).mat a b).snd = 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [hD.ine s hs hη a]
      rfl
    · rcases lt_or_gt_of_ne (show wt a b ≠ 0 by revert a b; decide) with hlt | hlt
      · rw [hD.tri s hker a b hlt]
        rfl
      · rw [hD.low s hker a b hlt]
        rfl
  set C := (conjBy h⁻¹ r' s).mat with hC
  set R := (r s).mat with hR
  set h0 := H.map TrivSqZeroExt.fst
  set h1 := H.map TrivSqZeroExt.snd
  set g0 := Hi.map TrivSqZeroExt.fst
  set C0 := C.map TrivSqZeroExt.fst
  have hc : H * C = (r' s).mat * H := rigDiag_conj_mat h r' s hr'1
  have hCs : C.map TrivSqZeroExt.snd = 0 := by
    ext a b
    exact hoff a b
  have hM0 : (r' s).mat.map TrivSqZeroExt.fst = R := by
    rw [hmat, rigDiag_fst_mul]
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl, apply_ite TrivSqZeroExt.fst, ite_mul]
  have hM1 : (r' s).mat.map TrivSqZeroExt.snd = y s * R := by
    rw [hmat, rigDiag_snd_mul]
    ext a b
    simp [Matrix.one_apply, Matrix.mul_apply, TrivSqZeroExt.algebraMap_eq_inl,
      apply_ite TrivSqZeroExt.fst, apply_ite TrivSqZeroExt.snd]
  have e0 : h0 * C0 = R * h0 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.fst) hc
    simpa only [rigDiag_fst_mul, hM0] using this
  have e1 : h1 * C0 = R * h1 + y s * R * h0 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.snd) hc
    simp only [rigDiag_snd_mul, hM0, hM1, hCs, Matrix.mul_zero, zero_add] at this
    exact this
  have hinv1 : Hi * H = 1 := by
    rw [hHi, hH, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv2 : H * Hi = 1 := by
    rw [hHi, hH, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgh : g0 * h0 = 1 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.fst) hinv1
    simp only [rigDiag_fst_mul] at this
    rw [this]
    ext a b
    simp [Matrix.one_apply]
    split_ifs <;> rfl
  have hhg : h0 * g0 = 1 := by
    have := congrArg (fun M => M.map TrivSqZeroExt.fst) hinv2
    simp only [rigDiag_fst_mul] at this
    rw [this]
    ext a b
    simp [Matrix.one_apply]
    split_ifs <;> rfl
  have hRR : R * (↑(r s).left⁻¹ : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hR, GG.mat, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e2 : C0 = g0 * R * h0 := by
    rw [← one_mul C0, ← hgh, mul_assoc, e0, ← mul_assoc]
  have e3 : y s * R = h1 * g0 * R - R * (h1 * g0) := by
    have k : y s * R * h0 = h1 * C0 - R * h1 := by
      rw [e1]
      abel
    calc y s * R = y s * R * h0 * g0 := by rw [mul_assoc (y s * R), hhg, mul_one]
      _ = (h1 * C0 - R * h1) * g0 := by rw [k]
      _ = h1 * g0 * R - R * (h1 * g0) := by
        rw [e2]
        simp only [sub_mul, mul_assoc, hhg, mul_one]
  have e4 : y s = y s * R * (↑(r s).left⁻¹ : Matrix (Fin 3) (Fin 3) K) := by
    rw [mul_assoc, hRR, mul_one]
  rw [e4, e3]
  simp only [adRep, GG.ad, MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, GG.adFun, hr1, ite_true]
  rw [← hR]
  simp only [sub_mul, mul_assoc, hRR, mul_one, mul_neg, neg_mul, sub_neg_eq_add]
  abel
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigSub
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem rs_dvd {l : ℕ} [Fact l.Prime] (n : ℕ) (a : ℤ_[l]) :
    PadicInt.toZModPow n a = 1 ↔ (l : ℤ_[l]) ^ n ∣ a - 1 := by
  rw [← sub_eq_zero, ← map_one (PadicInt.toZModPow n), ← map_sub, ← RingHom.mem_ker,
    PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

private theorem rs_cls (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime] (k : ℕ)
    [NeZero (l ^ k)] (σ : Formalism.ConjugateSelfDual.G ℚ Ω) (h : PadicInt.toZModPow k (cycZ ℚ Ω l σ : ℤ_[l]) = 1) :
    UpperTheory.V.Chr.cls ℚ Ω (l ^ k) σ = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : ∀ i : ℕ, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  refine (UpperTheory.V.Chr.clsFacts ℚ Ω (l ^ k)).2.2.1 σ 1 fun ζ hζ => ?_
  have key := cyclotomicCharacter.spec (L := Ω) l (n := k)
    (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G ℚ Ω) Ω σ) ζ hζ
  have h' : PadicInt.toZModPow k ((cyclotomicCharacter Ω l
      (MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G ℚ Ω) Ω σ) : ℤ_[l]ˣ) : ℤ_[l]) = 1 := h
  rw [h'] at key
  rw [Units.val_one]
  exact key

private theorem rs_unit {l : ℕ} [hl : Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] (hO : ¬ IsUnit (l : O))
    (y : O) (k : ℕ) (h : IsUnit (y - 1)) : IsUnit (y ^ l ^ k - 1) := by
  have key : ∀ x : O, IsUnit x ↔ IsLocalRing.residue O x ≠ 0 := fun x => by
    rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  rw [key] at h ⊢
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 hO
  haveI : CharP (IsLocalRing.ResidueField O) l :=
    ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hl.out hl0)
  rw [map_sub, map_one] at h
  rw [map_sub, map_pow, map_one]
  have e := sub_pow_char_pow (IsLocalRing.residue O y) 1 k (p := l)
  rw [one_pow] at e
  rw [← e]
  exact pow_ne_zero _ h

theorem UpperTheory.V.UnitaryThreeInertia.rig_sub :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ → ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F → ∃ H : Subgroup (F.D F.vl), H.Normal ∧ IsOpen (H : Set (F.D F.vl)) ∧ H ≤ (F.ηv F.vl).ker ∧ (∀ s ∈ H, s ∈ F.Iv F.vl → F.Ψv F.vl s = UpperTheory.V.Base.chiO ℚ Ω l c.O (s : Formalism.ConjugateSelfDual.G ℚ Ω) ^ (e : ℤ)) ∧ ∃ g ∈ H, IsUnit ((F.Ψv F.vl g : c.O) ^ 2 - 1) ∧ ‖((cycZ ℚ Ω l (g : Formalism.ConjugateSelfDual.G ℚ Ω) : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ < 1 := by
  intro Ω iF iC iA l hl c N iN e ψ o₁ hD S A F hF
  haveI := c.dvr
  haveI := c.fin
  haveI : NeZero (l ^ N.factorization l) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨x, hx1, hx2, hx3⟩ :=
    UpperTheory.V.UnitaryThreeInertia.exists_sigma Ω c e ψ o₁ hD S A F hF F.vl (Set.mem_insert _ _)
  have hη : ∀ s : F.D F.vl, F.ηv F.vl s = UpperTheory.V.UnitaryThreeInertia.eta4 Ω (s : Formalism.ConjugateSelfDual.G ℚ Ω) :=
    fun s => DFunLike.congr_fun hF.η _
  have hΨ : ∀ s : F.D F.vl, F.Ψv F.vl s =
      UpperTheory.V.Chr.Psi l e (UpperTheory.V.Chr.dirG ℚ Ω ψ) (s : Formalism.ConjugateSelfDual.G ℚ Ω) :=
    fun s => DFunLike.congr_fun hF.Ψ _
  have hO : ¬ IsUnit (l : c.O) := by
    intro hu
    haveI := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    have h1 : IsUnit (algebraMap ℤ_[l] c.O (l : ℤ_[l])) := by rwa [map_natCast]
    have h2 := isUnit_of_map_unit (algebraMap ℤ_[l] c.O) _ h1
    rw [PadicInt.isUnit_iff, PadicInt.norm_p, inv_eq_one] at h2
    have h3 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
    exact absurd h2 (ne_of_gt h3)
  let H : Subgroup (F.D F.vl) := (F.ηv F.vl).ker ⊓
    ((UpperTheory.V.Chr.dirG ℚ Ω (UpperTheory.V.HV.comp l ψ)).comp (F.D F.vl).subtype).ker
  refine ⟨H, inferInstance, ?_, inf_le_left, ?_, ?_⟩
  · let K : Subgroup (Formalism.ConjugateSelfDual.G ℚ Ω) := (UpperTheory.V.Chr.cls ℚ Ω 4).ker ⊓ (UpperTheory.V.Chr.cls ℚ Ω N).ker
    have hK : IsOpen (K : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) :=
      (UpperTheory.V.Chr.clsFacts ℚ Ω 4).1.inter (UpperTheory.V.Chr.clsFacts ℚ Ω N).1
    refine Subgroup.isOpen_mono (H₁ := K.comap (F.D F.vl).subtype) ?_
      (by rw [Subgroup.coe_comap]; exact hK.preimage continuous_subtype_val)
    intro s hs
    have hs' := Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hs)
    have h4 : UpperTheory.V.Chr.cls ℚ Ω 4 (s : Formalism.ConjugateSelfDual.G ℚ Ω) = 1 := hs'.1
    have hN : UpperTheory.V.Chr.cls ℚ Ω N (s : Formalism.ConjugateSelfDual.G ℚ Ω) = 1 := hs'.2
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [MonoidHom.mem_ker, hη]
      show MulChar.toUnitHom ZMod.χ₄ (UpperTheory.V.Chr.cls ℚ Ω 4 (s : Formalism.ConjugateSelfDual.G ℚ Ω)) = 1
      rw [h4, map_one]
    · show MulChar.toUnitHom (UpperTheory.V.HV.comp l ψ) (UpperTheory.V.Chr.cls ℚ Ω N (s : Formalism.ConjugateSelfDual.G ℚ Ω)) = 1
      rw [hN, map_one]
  · intro s hs hI
    have hs2 : UpperTheory.V.Chr.dirG ℚ Ω (UpperTheory.V.HV.comp l ψ) (s : Formalism.ConjugateSelfDual.G ℚ Ω) = 1 :=
      (Subgroup.mem_inf.1 hs).2
    have hI' : (s : Formalism.ConjugateSelfDual.G ℚ Ω) ∈ Ine (A F.vl) := by
      have h0 : (s : Formalism.ConjugateSelfDual.G ℚ Ω) ∈ F.I F.vl := hI
      rwa [hF.I] at h0
    have hv : (A F.vl).valuation (l : Ω) < 1 := by
      have := (hF.isOver F.vl (l : 𝓞 ℚ)).2 hF.vl
      simpa using this
    have hc := ((UpperTheory.V.HV.compIne Ω N l hl.out (A F.vl) hv).2 c.O ψ).1 _ hI'
    rw [hΨ, UpperTheory.V.Chr.Psi, MonoidHom.mul_apply, hc, hs2, mul_one]
    first
      | exact MonoidHom.zpow_apply _ _ _
      | simp [MonoidHom.zpow_apply, MonoidHom.pow_apply]
  · have hdx : (l : ℤ_[l]) ∣ ((cycZ ℚ Ω l (x : Formalism.ConjugateSelfDual.G ℚ Ω) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
      have h1 : PadicInt.toZModPow 1 ((cycZ ℚ Ω l (x : Formalism.ConjugateSelfDual.G ℚ Ω) : ℤ_[l]ˣ) : ℤ_[l]) = 1 :=
        congrArg Units.val hx3
      simpa using (rs_dvd 1 _).1 h1
    have hpow : (l : ℤ_[l]) ^ (N.factorization l + 1) ∣
        ((cycZ ℚ Ω l ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
      rw [Subgroup.coe_pow, map_pow, Units.val_pow_eq_pow_val]
      have := dvd_sub_pow_of_dvd_sub hdx (N.factorization l)
      rwa [one_pow] at this
    have hg : UpperTheory.V.Chr.cls ℚ Ω (l ^ N.factorization l)
        ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω) = 1 :=
      rs_cls Ω l (N.factorization l) _
        ((rs_dvd _ _).2 (dvd_trans (pow_dvd_pow _ (Nat.le_succ _)) hpow))
    have hpr : UpperTheory.V.HV.proj l N (UpperTheory.V.Chr.cls ℚ Ω N
        ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω)) = 1 := by
      rw [← MonoidHom.mem_ker, (UpperTheory.V.HV.projFacts N l hl.out).2.2.2.2.2.2.1, MonoidHom.mem_ker]
      have hc := DFunLike.congr_fun
        ((UpperTheory.V.Chr.clsFacts ℚ Ω N).2.1 (l ^ N.factorization l) (Nat.ordProj_dvd N l))
        ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω)
      rw [MonoidHom.comp_apply] at hc
      rw [hc]
      exact hg
    refine ⟨x ^ l ^ N.factorization l, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_pow, hx1, one_pow]
    · show MulChar.toUnitHom (UpperTheory.V.HV.comp l ψ)
        (UpperTheory.V.Chr.cls ℚ Ω N ((x ^ l ^ N.factorization l : F.D F.vl) : Formalism.ConjugateSelfDual.G ℚ Ω)) = 1
      simp only [UpperTheory.V.HV.comp, MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq,
        Equiv.apply_symm_apply, MonoidHom.comp_apply, hpr, map_one]
    · rw [map_pow, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul]
      exact rs_unit hO _ _ hx2
    · rw [PadicInt.norm_lt_one_iff_dvd]
      exact dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero _)) hpow
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GaussianFieldRangeEqKerQuarticChar
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem prim4 {L : Type} [Field L] [CharZero L] {i : L} (hi : i * i = -1) : IsPrimitiveRoot i (2 ^ 2) := by
  have hne : (1 : L) ≠ -1 := by
    intro h
    have h2 : (2 : L) = 0 := by linear_combination h
    exact two_ne_zero h2
  rw [IsPrimitiveRoot.iff (by norm_num)]
  refine ⟨by linear_combination (i * i - 1) * hi, ?_⟩
  intro l hl hl4
  norm_num at hl4
  interval_cases l
  · intro h1
    exact hne (by linear_combination hi - (i + 1) * h1)
  · intro h2
    exact hne (by linear_combination hi - h2)
  · intro h3
    exact hne (by linear_combination (1 - i ^ 2 + i) * hi + (i - 1) * h3)

private theorem adj_top {K : Type} [Field K] [NumberField K] (h : Module.finrank ℚ K = 2) {i : K} (hi : i * i = -1) :
    Algebra.adjoin ℚ {i} = ⊤ := by
  have hnb : i ∉ (⊥ : Subalgebra ℚ K) := by
    rw [Algebra.mem_bot]
    rintro ⟨q, hq⟩
    have hq2 : algebraMap ℚ K (q * q) = algebraMap ℚ K (-1) := by
      rw [map_mul, hq, hi, map_neg, map_one]
    have hq3 := (algebraMap ℚ K).injective hq2
    nlinarith [mul_self_nonneg q]
  have hS : Algebra.adjoin ℚ {i} ≠ ⊥ := by
    intro hb
    apply hnb
    rw [← hb]
    exact Algebra.subset_adjoin rfl
  have hle : Module.finrank ℚ (Subalgebra.toSubmodule (Algebra.adjoin ℚ {i})) ≤ 2 :=
    h ▸ Submodule.finrank_le _
  have hpos : 0 < Module.finrank ℚ (Algebra.adjoin ℚ {i}) := Module.finrank_pos
  have hne1 : Module.finrank ℚ (Algebra.adjoin ℚ {i}) ≠ 1 :=
    fun h1 => hS (Subalgebra.finrank_eq_one_iff.mp h1)
  have h2 : Module.finrank ℚ (Subalgebra.toSubmodule (Algebra.adjoin ℚ {i})) = Module.finrank ℚ K := by
    have : Module.finrank ℚ (Subalgebra.toSubmodule (Algebra.adjoin ℚ {i})) =
        Module.finrank ℚ (Algebra.adjoin ℚ {i}) := rfl
    omega
  apply Subalgebra.toSubmodule_injective
  rw [Algebra.top_toSubmodule]
  exact Submodule.eq_top_of_finrank_eq h2

open UpperTheory.V UpperTheory.V.Base in
private theorem fix_iff (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ζ : Ω) (hζ : IsPrimitiveRoot ζ 4)
    (σ : G ℚ Ω) : σ ζ = ζ ↔ eta4 Ω σ = 1 := by
  have hspec := UpperTheory.V.Chr.cls_spec (k := ℚ) 4 σ ζ hζ.pow_eq_one
  have key : ∀ u : (ZMod 4)ˣ, u = 1 ∨ u = -1 := by decide
  have heta : eta4 Ω σ = MulChar.toUnitHom ZMod.χ₄ (UpperTheory.V.Chr.cls ℚ Ω 4 σ) := rfl
  rcases key (UpperTheory.V.Chr.cls ℚ Ω 4 σ) with hu | hu
  · rw [heta, hu, map_one]
    simp only [iff_true]
    rw [hspec, hu, Units.val_one, show ZMod.val (1 : ZMod 4) = 1 from rfl, pow_one]
  · rw [heta, hu]
    have hm : MulChar.toUnitHom ZMod.χ₄ (-1) ≠ 1 := by
      intro h
      have h' := congrArg (fun x : ℤˣ => (x : ℤ)) h
      simp only [MulChar.coe_toUnitHom, Units.val_neg, Units.val_one] at h'
      revert h'
      decide
    have hz : σ ζ ≠ ζ := by
      rw [hspec, hu]
      have h3 : (((-1 : (ZMod 4)ˣ) : ZMod 4)).val = 3 := rfl
      rw [h3]
      intro h
      have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
      have hsq : ζ ^ 2 = 1 := by
        apply mul_right_cancel₀ hζ0
        linear_combination h
      exact hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) hsq
    exact iff_of_false hz hm

theorem UpperTheory.V.UnitaryThreeInertia.gaussian_field_range_eq_ker_quartic_char :
    (∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K), IsQi K) ∧ ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsScalarTower ℚ K Ω], IsQi K →
      (Base.galEmb ℚ K Ω).range = (eta4 Ω).ker ∧ discr K = -4 := by
  have sq_of_prim : ∀ {L : Type} [Field L] {z : L}, IsPrimitiveRoot z 4 → z * z = -1 := by
    intro L _ z hz
    have h4 : z ^ 4 = 1 := hz.pow_eq_one
    have h2 : z ^ 2 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    have hprod : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd (sub_eq_zero.mp h) h2
    · linear_combination h
  refine ⟨⟨CyclotomicField 4 ℚ, inferInstance, inferInstance, ?_, ?_⟩, ?_⟩
  · exact IsCyclotomicExtension.Rat.isCMField (CyclotomicField 4 ℚ) (S := {4}) ⟨4, rfl, by norm_num⟩
  · refine ⟨?_, ⟨IsCyclotomicExtension.zeta 4 ℚ (CyclotomicField 4 ℚ),
      sq_of_prim (IsCyclotomicExtension.zeta_spec 4 ℚ (CyclotomicField 4 ℚ))⟩⟩
    rw [IsCyclotomicExtension.Rat.finrank 4 (CyclotomicField 4 ℚ)]
    decide
  · intro Ω _ _ _ K _ _ _ _ hK
    obtain ⟨hrank, i, hi⟩ := hK
    have hadj := adj_top hrank hi
    have hprim : IsPrimitiveRoot (algebraMap K Ω i) 4 := by
      have := prim4 (L := Ω) (i := algebraMap K Ω i) (by rw [← map_mul, hi, map_neg, map_one])
      simpa using this
    refine ⟨?_, ?_⟩
    · ext σ
      rw [MonoidHom.mem_ker, ← fix_iff Ω _ hprim σ, UpperTheory.V.Base.range_galEmb,
        UpperTheory.V.Base.mem_galOf]
      constructor
      · intro h
        exact h i
      · intro h x
        have hφ : (σ.toAlgHom).comp (IsScalarTower.toAlgHom ℚ K Ω) = IsScalarTower.toAlgHom ℚ K Ω := by
          apply AlgHom.ext_of_adjoin_eq_top hadj
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact h
        exact congrArg (fun φ : K →ₐ[ℚ] Ω => φ x) hφ
    · haveI : IsCyclotomicExtension {2 ^ 2} ℚ K := by
        rw [IsCyclotomicExtension.iff_singleton]
        refine ⟨⟨i, prim4 hi⟩, ?_⟩
        intro x
        have hle : Algebra.adjoin ℚ {i} ≤ Algebra.adjoin ℚ {b : K | b ^ (2 ^ 2) = 1} := by
          apply Algebra.adjoin_mono
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (prim4 hi).pow_eq_one
        apply hle
        rw [hadj]
        trivial
      rw [IsCyclotomicExtension.Rat.discr_prime_pow 2 2 K]
      have ht : Nat.totient (2 ^ 2) = 2 := by decide
      rw [ht]
      norm_num
end
