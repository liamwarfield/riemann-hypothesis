module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocFour
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pLocFour :
    LocFour := by
  intro F _ _ v tr nm hΔ u hu
  haveI : CharZero (HeightOneSpectrum.adicCompletion F v) :=
    (RingHom.charZero_iff (algebraMap F (HeightOneSpectrum.adicCompletion F v)).injective).mp inferInstance
  have h2 : (2 : HeightOneSpectrum.adicCompletion F v) ≠ 0 := two_ne_zero
  have hD : ((tr : HeightOneSpectrum.adicCompletion F v) ^ 2 - 4 * nm) ≠ 0 := by
    have h := (Int.cast_ne_zero (α := HeightOneSpectrum.adicCompletion F v)).mpr hΔ
    push_cast at h
    exact h
  set D : HeightOneSpectrum.adicCompletion F v := (tr : HeightOneSpectrum.adicCompletion F v) ^ 2 - 4 * nm
    with hDdef
  let c : Fin 5 → HeightOneSpectrum.adicCompletion F v := ![1, -(D / 4), 1, -(D / 4), -u]
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    fin_cases i <;> simp [c, hD, hu]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.LocalQuad.isotropic_adicCompletion_of_five_le F v (ι := Fin 5) (by simp) c
  obtain ⟨z, hz4, hz⟩ := GlobalTheory.HermLocal.exists_zero_coord h2 hc hx0 hx 4
  have hz' : z 0 ^ 2 + -(D / 4) * z 1 ^ 2 + z 2 ^ 2 + -(D / 4) * z 3 ^ 2 + -u * z 4 ^ 2 = 0 := by
    rw [Fin.sum_univ_five] at hz
    simpa [c] using hz
  obtain ⟨w, hw⟩ : ∃ w, z 4 * w = 1 := ⟨(z 4)⁻¹, mul_inv_cancel₀ hz4⟩
  refine ⟨z 0 * w - tr / 2 * (z 1 * w), z 1 * w, z 2 * w - tr / 2 * (z 3 * w), z 3 * w, ?_⟩
  unfold qf
  rw [hDdef] at hz'
  linear_combination w ^ 2 * hz' + u * (z 4 * w + 1) * hw
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadMap
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pPadMap :
    PadMap := by
  intro F _ _ w
  set u : HeightOneSpectrum (𝓞 ℚ) := HeightOneSpectrum.under (𝓞 ℚ) w with hu
  set v : HeightOneSpectrum ℤ := GlobalTheory.NormLevelCompare.primeCorr.symm u with hv
  have hw : HeightOneSpectrum.under (𝓞 ℚ) w = GlobalTheory.NormLevelCompare.primeCorr v := by
    rw [hv, Equiv.apply_symm_apply]
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  let f₁ := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv.toRingHom
  letI : Algebra ℚ (HeightOneSpectrum.adicCompletion ℚ
      (Rat.HeightOneSpectrum.primesEquiv.symm (Rat.HeightOneSpectrum.primesEquiv v))) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ _
  let f₂ := (Padic.adicCompletionEquiv (𝓞 ℚ)
    (Rat.HeightOneSpectrum.primesEquiv v)).toRingEquiv.toRingHom
  refine ⟨v, ((GlobalTheory.LFun.complMap (F := ℚ) (E := F) hw).comp f₂).comp f₁, ?_⟩
  intro q hq
  have hgen : Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator u := by
    change (Rat.HeightOneSpectrum.primesEquiv v).1 = (Rat.HeightOneSpectrum.primesEquiv u).1
    simp [hv, GlobalTheory.NormLevelCompare.primeCorr]
  set p := Rat.HeightOneSpectrum.natGenerator u with hp
  have hdvd : (p : ℤ) ∣ q := by
    have hfix : Rat.IsIntegralClosure.intEquiv ℤ q = q := by
      simpa using map_intCast (Rat.IsIntegralClosure.intEquiv ℤ) q
    have hmem : q ∈ v.asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) := by
      rw [← hfix]
      exact (Ideal.apply_mem_of_equiv_iff).2 hq
    rw [← Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_span_singleton, hgen] at hmem
    exact hmem
  have hpu : ((p : ℕ) : 𝓞 ℚ) ∈ u.asIdeal := by
    have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff u (n := p)).1 dvd_rfl
    rw [← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) p] at h
    exact (Ideal.apply_mem_of_equiv_iff).1 h
  have hpw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
    have h : algebraMap (𝓞 ℚ) (𝓞 F) (p : 𝓞 ℚ) ∈ w.asIdeal := hpu
    simpa using h
  obtain ⟨k, rfl⟩ := hdvd
  push_cast
  exact Ideal.mul_mem_right _ _ (by exact_mod_cast hpw)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PIsoEx
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pIsoEx :
    NormTwo → BlockMat → IsoEx := by
  intro hN hB E _ _ _ A n hn
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨x, y, hxy, hint⟩ := hN E A
  have hinv : ∀ z, cF E (cF E z) = z := fun z => GlobalTheory.CompanionTheory.OnlyStab.conjFin_invol z
  have hfix : cF E (algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E)) =
      algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) := by
    refine (conjFin_algebraMap _ _).trans (congrArg _ ?_)
    change IsCMField.complexConj E (A.c : E) = (A.c : E)
    rw [← A.bar_eq, A.c_real]
  obtain ⟨a, ha, hS⟩ := hB _ (cF E) hinv _ x y hfix hxy m
  refine ⟨a, ?_, ?_⟩
  · have hd : (Matrix.diagonal fun i => ((A.dg (2 * m + 1) i : 𝓞 E) : E)).map
        (algebraMap E (FiniteAdeleRing (𝓞 E) E)) =
        Matrix.diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then 1 else
          algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E)) := by
      rw [Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      simp only [Arith.dg]
      split_ifs <;> simp
    rw [hd]
    exact ha
  · intro w q hq hg hqw
    obtain ⟨h1, h2, h3, h4⟩ := hint w q hq hg hqw
    have hc : algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) ∈
        (w.adicCompletionIntegers E).toSubring.comap (pLoc E w) := by
      change Valued.v (algebraMap E (w.adicCompletion E) (A.c : E)) ≤ 1
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (A.c : E)).trans_le
        (HeightOneSpectrum.valuation_le_one w A.c)
    have hall := hS ((w.adicCompletionIntegers E).toSubring.comap (pLoc E w)) h1 h2 h3 h4 hc
    rw [GlobalTheory.HenQ.Basic.mem_KGL_iff]
    refine ⟨fun i j => (hall i j).1, fun i j => ?_⟩
    rw [← map_inv]
    exact (hall i j).2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PZSqFin
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private theorem norm_padicEquiv_of_valued_eq_one (v : HeightOneSpectrum ℤ) (u : v.adicCompletion ℚ)
    (hu : Valued.v u = 1) : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ = 1 := by
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hmem : ∀ w : v.adicCompletion ℚ, Valued.v w ≤ 1 →
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v w‖ ≤ 1 := by
    intro w hw
    have hw' : w ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hw
    have := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo hw'
    simpa using this
  have h1 := hmem u hu.le
  have h2 := hmem u⁻¹ (by rw [map_inv₀, hu, inv_one])
  have h3 : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ *
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hu0, map_one, norm_one]
  have h4 := norm_nonneg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u)
  have h5 := norm_nonneg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u⁻¹)
  nlinarith

theorem UpperTheory.Gal.G1.pZSqFin :
    PadicSqFin → ZSqFin := by
  intro hP v
  obtain ⟨m, κ, hκ⟩ := hP (Rat.HeightOneSpectrum.primesEquiv v).1
  refine ⟨m, fun u => κ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u), ?_⟩
  intro u u' hu hu' huu
  obtain ⟨x, hx⟩ := hκ _ _ (norm_padicEquiv_of_valued_eq_one v u hu)
    (norm_padicEquiv_of_valued_eq_one v u' hu') huu
  refine ⟨(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x, ?_⟩
  have h := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm hx
  rw [map_mul, map_pow] at h
  simpa using h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PFinCls
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pFinCls :
    UnitCls → FinCongr → InfCongr → DefSign → RelOf → FinCls := by
  classical
  intro hU hF hI hD hR E _ _ _ A n p _ S
  obtain ⟨I, hI0, κ, hκ⟩ := hU p (A.tr ^ 2 - 4 * A.nm) (ne_of_lt A.disc_neg)
  have key : ∀ (B B' : DForm S.G) x t x' t', Triv S.G (AfP p) ↑B.β x t →
      Triv S.G (AfP p) ↑B'.β x' t' → κ t = κ t' → B.Rel B' := by
    intro B B' x t x' t' hT hT' hk
    obtain ⟨s, hs, hloc⟩ := hκ t t' hk
    obtain ⟨hM1, hM2, hM3⟩ := hD E A n p S B
    obtain ⟨hN1, hN2, hN3⟩ := hD E A n p S B'
    have hs0 : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
    have hsym : ∀ a b, (IsCMField.complexConj E) (((s : E) • (mat S ↑B.β * (A.H n)⁻¹)) a b) =
        ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)) b a := by
      intro a b
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_ratCast, hM1 a b]
    have hdet : ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)).det ≠ 0 := by
      rw [Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ hs0) hM2
    obtain ⟨P, hP, hPeq⟩ := GlobalTheory.HermGlobal.congr_of_local_complex (F := maximalRealSubfield E)
      (σ := IsCMField.complexConj E) (IsCMField.complexConj_ne_one E) hsym hN1 hdet hN2
      (fun w => hF E A n p S B B' x x' t t' hT hT' s hs hloc w)
      (by
        intro τ hτ
        have herm : ∀ N : Matrix (Fin n) (Fin n) E,
            (∀ a b, (IsCMField.complexConj E) (N a b) = N b a) → (N.map τ).IsHermitian := by
          intro N hN
          ext i j
          simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
          rw [← hN j i, hτ, starRingEnd_apply]
        have hsm : ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)).map τ =
            (s : ℂ) • (mat S ↑B.β * (A.H n)⁻¹).map τ := by
          ext i j
          simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_ratCast]
        apply hI n _ _ (herm _ hsym) (herm _ hN1)
          (if InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ then 1 else -1)
        · intro v hv
          rw [hsm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
            Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero, mul_left_comm]
          exact mul_pos (by exact_mod_cast hs) (hM3 τ v hv)
        · intro v hv
          exact hN3 τ v hv)
    exact hR E A n p S B B' s hs P hP hPeq
  haveI := hI0
  let tOf : DForm S.G → (AfP p)ˣ := fun B => B.trivAf.choose_spec.choose
  have htOf : ∀ B : DForm S.G, Triv S.G (AfP p) ↑B.β B.trivAf.choose (tOf B) :=
    fun B => B.trivAf.choose_spec.choose_spec
  refine Finite.of_injective (fun q : DFCls S.G => κ (tOf (Quot.out (r := DForm.Rel) q))) ?_
  intro q q' h
  rw [← Quot.out_eq q, ← Quot.out_eq q']
  exact Quot.sound (key _ _ _ _ _ _ (htOf _) (htOf _) h)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PFinCongr
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pFinCongr :
    PadMap → LocRoot → TrivMat → CongrScale → SplitCongr → DefSign → FinCongr := by
  classical
  intro hPad hLoc hTriv hScale hSplit hD E _ _ _ A n p _ S B B' x x' t t' hT hT' s hs hloc w
  set D : ℤ := A.tr ^ 2 - 4 * A.nm with hDdef
  have hD0 : D ≠ 0 := ne_of_lt A.disc_neg
  set θ : E := (A.ω : E) - (A.bar A.ω : E) with hθdef
  have hθc : (IsCMField.complexConj E) θ = -θ := by
    rw [hθdef, map_sub, A.bar_eq, IsCMField.complexConj_apply_apply]
    ring
  have hθ2 : θ ^ 2 = (D : E) := by
    have h1 : ((A.ω + A.bar A.ω : 𝓞 E) : E) = ((A.tr : 𝓞 E) : E) := by rw [A.tr_eq]
    have h2 : ((A.ω * A.bar A.ω : 𝓞 E) : E) = ((A.nm : 𝓞 E) : E) := by rw [A.nm_eq]
    have c1 : ((A.tr : 𝓞 E) : E) = (A.tr : E) := map_intCast (algebraMap (𝓞 E) E) A.tr
    have c2 : ((A.nm : 𝓞 E) : E) = (A.nm : E) := map_intCast (algebraMap (𝓞 E) E) A.nm
    rw [c1] at h1
    rw [c2] at h2
    push_cast at h1 h2
    rw [hθdef, hDdef]
    push_cast
    linear_combination ((A.ω : E) + (A.bar A.ω : E) + (A.tr : E)) * h1 - 4 * h2
  obtain ⟨hM1, hM2, hM3⟩ := hD E A n p S B
  obtain ⟨hN1, hN2, hN3⟩ := hD E A n p S B'
  have hs0 : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
  have hsym : ∀ a b, (IsCMField.complexConj E) (((s : E) • (mat S ↑B.β * (A.H n)⁻¹)) a b) =
      ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)) b a := by
    intro a b
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_ratCast, hM1 a b]
  have hdet : ((s : E) • (mat S ↑B.β * (A.H n)⁻¹)).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs0) hM2
  obtain ⟨v, ι, hv⟩ := hPad (maximalRealSubfield E) w
  by_cases hvp : v.asIdeal = Ideal.span {(p : ℤ)}
  · have hpw : ((p : ℤ) : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal :=
      hv _ (by rw [hvp]; exact Ideal.subset_span rfl)
    obtain ⟨hnd, hr⟩ := (S.good).1
    obtain ⟨ρ, hρ, -⟩ := hLoc (maximalRealSubfield E) w A.tr A.nm p (Fact.out) (by exact_mod_cast hpw) hnd hr
    refine hSplit E n _ _ hsym hN1 hdet hN2 (HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w)
      θ D hD0 hθc hθ2 (2 * (ρ : HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) - A.tr) ?_
    have hρ' := congrArg (fun z : HeightOneSpectrum.adicCompletionIntegers (maximalRealSubfield E) w =>
      (z : HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w)) hρ
    push_cast at hρ'
    rw [hDdef]
    push_cast
    linear_combination 4 * hρ'
  · let v' : AwayP p := ⟨v, hvp⟩
    obtain ⟨a, b, hab⟩ := hloc v'
    let ψ : AfP p →+* HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w :=
      ι.comp (AfP.eval v').toRingHom
    have hH' : (A.H n).map (cj E) = A.H n := by
      have h := congrArg Matrix.transpose (A.herm n)
      rw [Matrix.transpose_transpose] at h
      rw [h]
      exact Matrix.diagonal_transpose _
    obtain ⟨X, hX, hXeq⟩ := hTriv E n (A.H n) (A.herm n) hH' (A.det_ne n) (AfP p)
      (HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) ψ (mat S ↑B.β) x ↑t hT
    obtain ⟨X', hX', hXeq'⟩ := hTriv E n (A.H n) (A.herm n) hH' (A.det_ne n) (AfP p)
      (HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) ψ (mat S ↑B'.β) x' ↑t' hT'
    have ht0 : ψ ↑t' ≠ 0 := (t'.isUnit.map ψ).ne_zero
    have heq : ψ ↑t' = (s : HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) * ψ ↑t *
        (ι a ^ 2 - (D : HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w) * ι b ^ 2) := by
      show ι (AfP.eval v' ↑t') = _
      rw [hab, map_mul, map_mul, map_sub, map_mul, map_pow, map_pow, map_intCast]
      congr 2
      exact eq_ratCast (ι.comp (algebraMap ℚ _)) s
    exact hScale E n (A.H n)⁻¹ _ _ (HeightOneSpectrum.adicCompletion (maximalRealSubfield E) w)
      θ D hθc hθ2 (ψ ↑t) (ψ ↑t') (ι a) (ι b) s ht0 heq X X' hX hX' hXeq hXeq'
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PInfCongr
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

open scoped MatrixOrder ComplexOrder in
private lemma exists_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B ∧ A = Bᴴ * B := by
  have h0 : 0 ≤ A := hA.posSemidef.nonneg
  have h1 := CFC.sqrt_mul_sqrt_self A h0
  have h2 : IsSelfAdjoint (CFC.sqrt A) := (CFC.sqrt_nonneg A).isSelfAdjoint
  refine ⟨CFC.sqrt A, ?_, ?_⟩
  · have hu : IsUnit (CFC.sqrt A * CFC.sqrt A) := by
      rw [h1]
      exact hA.isUnit
    exact isUnit_of_mul_isUnit_left hu
  · rw [← Matrix.star_eq_conjTranspose, h2.star_eq, h1]

open scoped ComplexOrder in
private lemma smul_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) {ε : ℝ}
    (h : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < ε * (star x ⬝ᵥ (M *ᵥ x)).re) : ((ε : ℂ) • M).PosDef := by
  have hH : ((ε : ℂ) • M).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hM.eq]
    simp
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH ?_
  intro x hx
  have him := hM.im_star_dotProduct_mulVec_self x
  have e : star x ⬝ᵥ ((ε : ℂ) • M) *ᵥ x = (ε : ℂ) * (star x ⬝ᵥ M *ᵥ x) := by
    simp [Matrix.smul_mulVec, dotProduct_smul]
  rw [e, Complex.lt_def]
  simp only [RCLike.im_to_complex] at him
  constructor
  · simpa [him] using h x hx
  · simp [him]

theorem UpperTheory.Gal.G1.pInfCongr :
    InfCongr := by
  intro n G G' hG hG' ε h h'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, by simp, ?_⟩
    exact Subsingleton.elim _ _
  have hε : (ε : ℂ) ≠ 0 := by
    intro h0
    have hx : (fun i : Fin n => if i = ⟨0, hn⟩ then (1 : ℂ) else 0) ≠ 0 := by
      intro hz
      have := congrFun hz ⟨0, hn⟩
      simp at this
    have := h _ hx
    rw [Complex.ofReal_eq_zero.1 h0] at this
    simp at this
  obtain ⟨B, hB, hBe⟩ := exists_factor (smul_posDef hG h)
  obtain ⟨C, hC, hCe⟩ := exists_factor (smul_posDef hG' h')
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hB
  have hCd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
  set P := B⁻¹ * C with hP
  have hBP : B * P = C := by
    rw [hP, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv B hBd, Matrix.one_mul]
  have key : (ε : ℂ) • G' = (ε : ℂ) • (Pᴴ * G * P) := by
    calc (ε : ℂ) • G' = Cᴴ * C := hCe
      _ = (B * P)ᴴ * (B * P) := by rw [hBP]
      _ = Pᴴ * (Bᴴ * B) * P := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = Pᴴ * ((ε : ℂ) • G) * P := by rw [hBe]
      _ = (ε : ℂ) • (Pᴴ * G * P) := by rw [Matrix.mul_smul, Matrix.smul_mul]
  have hG'P : G' = Pᴴ * G * P := smul_right_injective _ hε key
  refine ⟨P.map (starRingEnd ℂ), ?_, ?_⟩
  · have hdet := (starRingEnd ℂ).map_det P
    rw [RingHom.mapMatrix_apply] at hdet
    rw [← hdet, map_ne_zero, hP, Matrix.det_mul]
    exact ((Matrix.isUnit_nonsing_inv_det B hBd).mul hCd).ne_zero
  · have e1 : (P.map (starRingEnd ℂ))ᵀ = Pᴴ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    have e2 : (P.map (starRingEnd ℂ)).map (starRingEnd ℂ) = P := by
      ext i j
      simp
    rw [e1, e2]
    exact hG'P
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PCongrScale
noncomputable section

open NumberField Matrix
open scoped TensorProduct

namespace UpperTheory.Gal.G1

private theorem congr_core {n : ℕ} {B : Type*} [CommRing B] (σ : B →+* B)
    (Nb N'b Mb X X' : Matrix (Fin n) (Fin n) B) (τ τ' s z : B)
    (hz : IsUnit z) (hX : IsUnit X.det) (hX' : IsUnit X'.det)
    (hτ : τ' = s * τ * (z * σ z))
    (h : X * Nb * (X.map σ)ᵀ = τ • Mb)
    (h' : X' * N'b * (X'.map σ)ᵀ = τ' • Mb) :
    ∃ P : Matrix (Fin n) (Fin n) B, IsUnit P.det ∧ N'b = Pᵀ * (s • Nb) * P.map σ := by
  have hW : X'⁻¹ * X' = 1 := Matrix.nonsing_inv_mul _ hX'
  have hW' : (X'.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hW]
    simp
  have hWd : IsUnit (X'⁻¹).det := by
    have : (X'⁻¹).det * X'.det = 1 := by rw [← Matrix.det_mul, hW, Matrix.det_one]
    exact IsUnit.of_mul_eq_one _ this
  have hzX : (z • X).map σ = σ z • X.map σ := by
    ext i j
    simp
  refine ⟨(X'⁻¹ * (z • X))ᵀ, ?_, ?_⟩
  · rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_smul]
    exact hWd.mul ((hz.pow _).mul hX)
  · have hP : ((X'⁻¹ * (z • X))ᵀ).map σ = σ z • ((X.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ) := by
      have e : (X'⁻¹ * (z • X)).map σ = (X'⁻¹).map σ * (σ z • X.map σ) := by
        rw [Matrix.map_mul, hzX]
      rw [Matrix.transpose_map, e, Matrix.transpose_mul, Matrix.transpose_smul, Matrix.smul_mul]
    rw [Matrix.transpose_transpose, hP]
    calc N'b = X'⁻¹ * X' * N'b * ((X'.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ) := by
          rw [hW, hW', Matrix.one_mul, Matrix.mul_one]
      _ = X'⁻¹ * (X' * N'b * (X'.map σ)ᵀ) * ((X'⁻¹).map σ)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = X'⁻¹ * ((s * (z * σ z)) • (X * Nb * (X.map σ)ᵀ)) * ((X'⁻¹).map σ)ᵀ := by
          rw [h', h, hτ, smul_smul]
          congr 3
          ring
      _ = X'⁻¹ * (z • X) * (s • Nb) * (σ z • ((X.map σ)ᵀ * ((X'⁻¹).map σ)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
          congr 1
          ring

theorem pCongrScale : CongrScale := by
  intro E _ _ _ n M N N' K _ _ θ D hθ hD t t' a b s ht' ht X X' hX hX' h h'
  let F := maximalRealSubfield E
  let B := K ⊗[F] E
  let σ := GlobalTheory.HermGlobal.baseConj (IsCMField.complexConj E) K
  let cB : K →+* B := algebraMap K B
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have hmul : ∀ x y : E, inE K (x * y) = inE K x * inE K y := fun x y => by
    simp [inE, Algebra.TensorProduct.tmul_mul_tmul]
  have hrat : ∀ q : ℚ, inE K (q : E) = cB (q : K) := fun q => by
    have e : ((Algebra.TensorProduct.includeRight : E →ₐ[F] B) : E →+* B).comp (Rat.castHom E) =
        cB.comp (Rat.castHom K) := RingHom.ext_rat _ _
    exact congrArg (fun f : ℚ →+* B => f q) e
  have hint : inE K (D : E) = cB (D : K) := by
    have := hrat (D : ℚ)
    simpa using this
  set z : B := cB a + cB b * inE K θ with hzdef
  have hσθ : σ (inE K θ) = -inE K θ := by
    show (1 : K) ⊗ₜ[F] (IsCMField.complexConj E θ) = _
    rw [hθ, TensorProduct.tmul_neg]
  have hσc : ∀ x : K, σ (cB x) = cB x := fun x => σ.commutes x
  have hσz : σ z = cB a - cB b * inE K θ := by
    rw [hzdef, map_add (f := _), map_mul, hσc, hσc, hσθ]
    ring
  have hθθ : inE K θ * inE K θ = cB (D : K) := by
    rw [← hmul, ← pow_two, hD, hint]
  have hnorm : z * σ z = cB (a ^ 2 - D * b ^ 2) := by
    rw [hσz, hzdef, map_sub, map_mul, map_pow, map_pow]
    linear_combination (-(cB b) ^ 2) * hθθ
  have hu : (a ^ 2 - D * b ^ 2) ≠ 0 := fun h0 => ht' (by rw [ht, h0, mul_zero])
  have hzu : IsUnit z := by
    have : IsUnit (z * σ z) := by
      rw [hnorm]
      exact (IsUnit.mk0 _ hu).map cB
    exact isUnit_of_mul_isUnit_left this
  have hsm : ∀ (c : K) (A : Matrix (Fin n) (Fin n) B), c • A = cB c • A := fun c A => by
    ext i j
    simp [Algebra.smul_def, cB]
  obtain ⟨P, hP, hE⟩ := congr_core (σ : B →+* B) (N.map (inE K)) (N'.map (inE K)) (M.map (inE K)) X X'
    (cB t) (cB t') (inE K (s : E)) z hzu hX hX' (by
      have hn2 : z * (σ : B →+* B) z = cB (a ^ 2 - D * b ^ 2) := hnorm
      rw [hn2, hrat, ht, map_mul, map_mul])
    (by rw [← hsm]; exact h) (by rw [← hsm]; exact h')
  refine ⟨P, hP, ?_⟩
  have hN : ((s : E) • N).map (fun x => (1 : K) ⊗ₜ[F] x) = inE K (s : E) • N.map (inE K) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    exact hmul _ _
  rw [hN]
  exact hE

end UpperTheory.Gal.G1
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PAdFour
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem UpperTheory.Gal.G1.exists_local (hF : LocFour) (hU : LocUnit) (hR : LocRoot) (hS : SplitRep)
    (F : Type) [Field F] [NumberField F] (tr nm : ℤ) (hd : tr ^ 2 - 4 * nm ≠ 0) (c : 𝓞 F) (hc : c ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ f : Fin 4 → v.adicCompletion F,
      algebraMap F (v.adicCompletion F) (c : F) * (qf tr nm (f 0) (f 1) + qf tr nm (f 2) (f 3)) = 1 ∧
      (c ∉ v.asIdeal → (((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal ∨
        ∃ q : ℕ, q.Prime ∧ (q : 𝓞 F) ∈ v.asIdeal ∧ ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧
          ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm) → ∀ i, f i ∈ v.adicCompletionIntegers F) := by
  have hcF : (c : F) ≠ 0 := by simpa using hc
  have hcv : algebraMap F (v.adicCompletion F) (c : F) ≠ 0 := by
    simpa using hcF
  by_cases hg : c ∉ v.asIdeal ∧ (((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal ∨
        ∃ q : ℕ, q.Prime ∧ (q : 𝓞 F) ∈ v.asIdeal ∧ ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm ∧
          ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm)
  · obtain ⟨hcm, hor⟩ := hg
    have hval : Valued.v (algebraMap F (v.adicCompletion F) (c : F)) = 1 := by
      refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (c : F)).trans ?_
      have h0 : v.valuation F (c : F) = v.intValuation c := HeightOneSpectrum.valuation_of_algebraMap v c
      rw [h0]
      first
        | exact (HeightOneSpectrum.intValuation_eq_one_iff v).2 hcm
        | exact le_antisymm (v.intValuation_le_one c)
            (not_lt.1 fun h => hcm ((v.intValuation_lt_one_iff_mem c).1 h))
    have hval' : Valued.v (algebraMap F (v.adicCompletion F) (c : F))⁻¹ = 1 := by
      rw [map_inv₀, hval, inv_one]
    let c1 : v.adicCompletionIntegers F := ⟨_, hval.le⟩
    let c2 : v.adicCompletionIntegers F := ⟨_, hval'.le⟩
    have h12 : c2 * c1 = 1 := Subtype.ext (inv_mul_cancel₀ hcv)
    have hu : IsUnit c2 := isUnit_iff_exists_inv.2 ⟨c1, h12⟩
    obtain ⟨a, b, hab⟩ : ∃ a b : v.adicCompletionIntegers F, qf tr nm a b = c2 := by
      rcases hor with h | ⟨q, hq, hqv, hqd, hr⟩
      · exact hU F v tr nm h c2 hu
      · obtain ⟨ρ, h1, h2⟩ := hR F v tr nm q hq hqv hqd hr
        exact hS _ tr nm ρ h1 h2 c2
    have hab' : qf tr nm (a : v.adicCompletion F) (b : v.adicCompletion F)
        = (algebraMap F (v.adicCompletion F) (c : F))⁻¹ := by
      have := congrArg (Subtype.val) hab
      simpa [qf] using this
    refine ⟨![a, b, 0, 0], ?_, fun _ _ i => ?_⟩
    · simp only [Matrix.cons_val]
      have h0 : qf tr nm (0 : v.adicCompletion F) 0 = 0 := by simp [qf]
      rw [hab', h0, add_zero, mul_inv_cancel₀ hcv]
    · fin_cases i
      · exact a.2
      · exact b.2
      · exact zero_mem _
      · exact zero_mem _
  · obtain ⟨a, b, a', b', h⟩ := hF F v tr nm hd _ (inv_ne_zero hcv)
    refine ⟨![a, b, a', b'], ?_, fun h1 h2 => absurd ⟨h1, h2⟩ hg⟩
    simp only [Matrix.cons_val]
    rw [h, mul_inv_cancel₀ hcv]

theorem UpperTheory.Gal.G1.pAdFour :
    LocFour → LocUnit → LocRoot → SplitRep → AdFour := by
  intro hF hU hR hS F _ _ tr nm hd c hc
  choose f hf1 hf2 using exists_local hF hU hR hS F tr nm hd c hc
  have hD : ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ≠ 0 := by
    have : (2 * (tr ^ 2 - 4 * nm) : ℤ) ≠ 0 := mul_ne_zero two_ne_zero hd
    exact_mod_cast this
  have hI : Ideal.span {((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) * c} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hD hc
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) * c ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors hI).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have hev : ∀ i, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, f v i ∈ v.adicCompletionIntegers F := by
    intro i
    refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
    by_contra h
    have h1 : c ∉ v.asIdeal := fun hm => h (Ideal.mul_mem_left _ _ hm)
    have h2 : ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F) ∉ v.asIdeal := fun hm => h (Ideal.mul_mem_right _ _ hm)
    exact hv (hf2 v h1 (Or.inl h2) i)
  let A : Fin 4 → FiniteAdeleRing (𝓞 F) F := fun i => ⟨fun v => f v i, hev i⟩
  refine ⟨A, ?_, ?_⟩
  · refine FiniteAdeleRing.ext _ fun v => ?_
    have := hf1 v
    let φ : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
      { toFun := fun x => x v
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have key : φ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (c : F) *
        (qf tr nm (A 0) (A 1) + qf tr nm (A 2) (A 3))) = φ 1 := by
      simp only [qf, map_mul, map_add (f := _), map_pow, map_intCast, map_one]
      have hA : ∀ i, φ (A i) = f v i := fun _ => rfl
      have hc' : φ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (c : F)) =
          algebraMap F (v.adicCompletion F) (c : F) := rfl
      rw [hc']
      simp only [hA]
      simpa only [qf] using this
    exact key
  · intro v q hq hqv hqd hr hcv i
    exact hf2 v hcv (Or.inr ⟨q, hq, hqv, hqd, hr⟩) i
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PScale
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma val_alg (v : HeightOneSpectrum ℤ) (s : ℚ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) s) = v.valuation ℚ s :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v s

private lemma exists_gen (v : HeightOneSpectrum ℤ) :
    ∃ q : ℕ, q ≠ 0 ∧ v.asIdeal = Ideal.span {(q : ℤ)} := by
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal v.asIdeal
  have hg' : v.asIdeal = Ideal.span {g} := hg
  refine ⟨g.natAbs, ?_, ?_⟩
  · intro h0
    apply v.ne_bot
    rw [hg', Int.natAbs_eq_zero.mp h0]
    simp
  · rw [hg', Ideal.span_singleton_eq_span_singleton]
    exact Int.associated_natAbs g

private lemma val_nat (v : HeightOneSpectrum ℤ) (q : ℕ) :
    v.valuation ℚ (q : ℚ) = v.intValuation (q : ℤ) := by
  rw [← v.valuation_of_algebraMap (K := ℚ)]
  simp

private lemma val_self (v : HeightOneSpectrum ℤ) {q : ℕ} (h0 : q ≠ 0)
    (h : v.asIdeal = Ideal.span {(q : ℤ)}) : v.valuation ℚ (q : ℚ) = WithZero.exp (-1 : ℤ) := by
  rw [val_nat]
  exact HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast h0) h

private lemma val_other (v w : HeightOneSpectrum ℤ) {q : ℕ}
    (h : v.asIdeal = Ideal.span {(q : ℤ)}) (hne : w ≠ v) : w.valuation ℚ (q : ℚ) = 1 := by
  rw [val_nat]
  apply le_antisymm (w.intValuation_le_one _)
  rw [← not_lt, w.intValuation_lt_one_iff_mem]
  intro hm
  apply hne
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [h, Ideal.span_le]
    simpa using hm
  exact HeightOneSpectrum.ext ((v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)

private lemma finite_ne_one (p : ℕ) (t : (AfP p)ˣ) :
    {v : AwayP p | Valued.v (AfP.eval v (t : AfP p)) ≠ 1}.Finite := by
  have ht := (t : AfP p).2
  have hti := ((t⁻¹ : (AfP p)ˣ) : AfP p).2
  refine (Filter.eventually_cofinite.mp (ht.and hti)).subset ?_
  intro v hv hboth
  apply hv
  obtain ⟨h1, h2⟩ := hboth
  have h1' : Valued.v (AfP.eval v (t : AfP p)) ≤ 1 := h1
  have h2' : Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) ≤ 1 := h2
  have hm : Valued.v (AfP.eval v (t : AfP p)) * Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  apply le_antisymm h1'
  calc (1 : WithZero (Multiplicative ℤ)) = _ := hm.symm
    _ ≤ Valued.v (AfP.eval v (t : AfP p)) * 1 := mul_le_mul_right h2' _
    _ = _ := mul_one _

private lemma val_ne_zero (p : ℕ) (t : (AfP p)ˣ) (v : AwayP p) :
    Valued.v (AfP.eval v (t : AfP p)) ≠ 0 := by
  intro h
  have hm : Valued.v (AfP.eval v (t : AfP p)) * Valued.v (AfP.eval v ((t⁻¹ : (AfP p)ˣ) : AfP p)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  rw [h, zero_mul] at hm
  exact zero_ne_one hm

theorem UpperTheory.Gal.G1.pScale :
    Scale := by
  intro p t
  classical
  choose q hq0 hq using fun v : AwayP p => exists_gen v.1
  let n : AwayP p → ℤ := fun v => WithZero.log (Valued.v (AfP.eval v (t : AfP p)))
  let S := (finite_ne_one p t).toFinset
  refine ⟨∏ v ∈ S, ((q v : ℚ) ^ (-n v)), ?_, ?_⟩
  · apply Finset.prod_pos
    intro v _
    apply zpow_pos
    exact_mod_cast Nat.pos_of_ne_zero (hq0 v)
  · intro w
    rw [val_alg, map_prod]
    have hterm : ∀ v ∈ S, w.1.valuation ℚ ((q v : ℚ) ^ (-n v)) =
        if v = w then WithZero.exp (n v) else 1 := by
      intro v _
      rw [map_zpow₀]
      split_ifs with hvw
      · subst hvw
        rw [val_self v.1 (hq0 v) (hq v), ← WithZero.exp_zsmul]
        simp
      · rw [val_other v.1 w.1 (hq v) (fun h => hvw (Subtype.ext h.symm)), _root_.one_zpow]
    rw [Finset.prod_congr rfl hterm, Finset.prod_ite_eq']
    split_ifs with hw
    · exact (WithZero.exp_log (val_ne_zero p t w)).symm
    · have : ¬ Valued.v (AfP.eval w (t : AfP p)) ≠ 1 := by
        intro h
        apply hw
        simpa [S] using h
      exact not_not.mp this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PBlockMat
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pBlockMat :
    BlockMat := by
  intro R _ σ hσ c x y hc h m
  let b : Matrix (Fin 2) (Fin 2) R := !![x, -σ y; y, σ x]
  let b' : Matrix (Fin 2) (Fin 2) R := !![c * σ x, c * σ y; -(c * y), c * x]
  let M : Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R :=
    fromBlocks 1 0 0 (blockDiagonal fun _ => b)
  let M' : Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R :=
    fromBlocks 1 0 0 (blockDiagonal fun _ => b')
  let e : Fin 1 ⊕ (Fin 2 × Fin m) ≃ Fin (2 * m + 1) :=
    ((Equiv.refl (Fin 1)).sumCongr finProdFinEquiv).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  have hbd : (fromBlocks 1 0 0 (blockDiagonal fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) R)) :
      Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R) = 1 := by
    have h1 : (blockDiagonal fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) R)) = 1 :=
      blockDiagonal_one
    rw [h1, fromBlocks_one]
  have hbb' : b * b' = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, b', Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination h | ring
  have hb'b : b' * b = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, b', Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination h | ring
  have hu : (b.map σ)ᵀ * diagonal (fun _ : Fin 2 => c) * b = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, Matrix.mul_apply, Fin.sum_univ_two, hσ] <;>
      first | linear_combination h | ring
  have hM : M * M' = 1 := by
    simp only [M, M', fromBlocks_multiply]
    rw [← blockDiagonal_mul]
    simp only [hbb', Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    exact hbd
  have hM' : M' * M = 1 := by
    simp only [M, M', fromBlocks_multiply]
    rw [← blockDiagonal_mul]
    simp only [hb'b, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    exact hbd
  have hD : (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) ∘ e =
      Sum.elim (fun _ => 1) (fun _ => c) := by
    funext p
    rcases p with p | p
    · have hp : p = 0 := Subsingleton.elim _ _
      subst hp
      simp [e]
      intro hne
      exact (hne (Fin.ext (by simp))).elim
    · simp [e]
  have hd2 : (diagonal fun _ : Fin 2 × Fin m => c) =
      blockDiagonal fun _ : Fin m => diagonal fun _ : Fin 2 => c := by
    rw [blockDiagonal_diagonal]
  have hcore : (M.map σ)ᵀ *
      diagonal ((fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) ∘ e) * M = 1 := by
    rw [hD, ← fromBlocks_diagonal]
    simp only [M, fromBlocks_map, fromBlocks_transpose, blockDiagonal_map _ _ (map_zero σ),
      blockDiagonal_transpose, hd2]
    simp only [fromBlocks_multiply, Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one]
    rw [← blockDiagonal_mul, ← blockDiagonal_mul]
    simp only [hu]
    simpa using hbd
  have hbS : ∀ (S : Subring R), x ∈ S → y ∈ S → σ x ∈ S → σ y ∈ S → c ∈ S →
      (∀ i j, b i j ∈ S) ∧ ∀ i j, b' i j ∈ S := by
    intro S hx hy hsx hsy hcS
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [b] <;>
        first | assumption | exact S.neg_mem hsy
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [b'] <;>
        first | exact S.neg_mem (S.mul_mem hcS hy) | exact S.mul_mem hcS hsx | exact S.mul_mem hcS hsy | exact S.mul_mem hcS hx | exact S.mul_mem hcS hy
  have hblk : ∀ (S : Subring R) (N : Matrix (Fin 2) (Fin 2) R), (∀ i j, N i j ∈ S) →
      ∀ p q, (fromBlocks 1 0 0 (blockDiagonal fun _ : Fin m => N) :
        Matrix (Fin 1 ⊕ (Fin 2 × Fin m)) (Fin 1 ⊕ (Fin 2 × Fin m)) R) p q ∈ S := by
    intro S N hN p q
    rcases p with p | ⟨i, k⟩ <;> rcases q with q | ⟨j, l⟩
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]
      split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    · simp only [fromBlocks_apply₁₂, Matrix.zero_apply]
      exact S.zero_mem
    · simp only [fromBlocks_apply₂₁, Matrix.zero_apply]
      exact S.zero_mem
    · simp only [fromBlocks_apply₂₂, blockDiagonal_apply]
      split_ifs
      · exact hN _ _
      · exact S.zero_mem
  refine ⟨⟨reindex e e M, reindex e e M', ?_, ?_⟩, ?_, ?_⟩
  · rw [reindex_apply, reindex_apply, submatrix_mul_equiv, hM, submatrix_one_equiv]
  · rw [reindex_apply, reindex_apply, submatrix_mul_equiv, hM', submatrix_one_equiv]
  · have hDD : diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) =
        (diagonal ((fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) ∘ e)).submatrix
          e.symm e.symm := by
      rw [submatrix_diagonal_equiv]
      congr 1
      funext i
      simp
    show ((reindex e e M).map σ)ᵀ *
        diagonal (fun i : Fin (2 * m + 1) => if (i : ℕ) = 0 then (1 : R) else c) * reindex e e M = 1
    rw [hDD, reindex_apply, ← submatrix_map, transpose_submatrix, submatrix_mul_equiv,
      submatrix_mul_equiv, hcore, submatrix_one_equiv]
  · intro S hx hy hsx hsy hcS i j
    obtain ⟨h1, h2⟩ := hbS S hx hy hsx hsy hcS
    exact ⟨hblk S b h1 _ _, hblk S b' h2 _ _⟩
end
