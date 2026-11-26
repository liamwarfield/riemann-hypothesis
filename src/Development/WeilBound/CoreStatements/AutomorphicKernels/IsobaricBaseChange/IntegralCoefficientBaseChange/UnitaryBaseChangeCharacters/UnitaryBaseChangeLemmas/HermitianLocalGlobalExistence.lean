module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAll
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.IntegralUnitaryConjugacyLattice

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ExistsPolyOfCommute
open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.UsideLeaf.UnitaryLocalCharpoly

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

instance isLocalRing_intL : IsLocalRing (intL L) :=
  inferInstanceAs (IsLocalRing (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)

theorem isCsr_charpoly {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (M J Ji : Matrix (Fin n) (Fin n) R)
    (hJ : Ji * J = 1) (hM : cT s M * J * M = J) : GlobalTheory.UTr.IsCsr s M.charpoly := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hJ' : J * Ji = 1 := mul_eq_one_comm.1 hJ
  let u : (Matrix (Fin n) (Fin n) R)ˣ := ⟨Ji, J, hJ, hJ'⟩
  set N := Ji * cT s M * J with hNdef
  have hNM : N * M = 1 := by
    rw [hNdef, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s M), hM, hJ]
  have hdeg : M.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdegN : N.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hNc : N.charpoly = (cT s M).charpoly := by
    have := Matrix.charpoly_units_conj u (cT s M)
    rw [← Matrix.coe_units_inv] at this
    exact this
  have hmap : M.charpoly.map s = N.charpoly := by
    rw [hNc, ← Matrix.charpoly_map, ← Matrix.charpoly_transpose]; rfl
  have hrev : (M.charpoly.map s).reflect n = N.charpolyRev := by
    rw [hmap, ← Matrix.reverse_charpoly, Polynomial.reverse, hdegN]
  have hdetN : N.det * M.det = 1 := by rw [← Matrix.det_mul, hNM, Matrix.det_one]
  have hNd : N.det = s M.det := by
    have h1 : N.det = (cT s M).det := by
      rw [hNdef, Matrix.det_mul, Matrix.det_mul, mul_comm (Ji.det), mul_assoc, ← Matrix.det_mul, hJ,
        Matrix.det_one, mul_one]
    rw [h1, cT, Matrix.det_transpose, RingHom.map_det]; rfl
  have h0 : M.charpoly.coeff 0 = (-1) ^ n * M.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
      one_pow, one_mul]
  have hs0 : s (M.charpoly.coeff 0) = (-1) ^ n * N.det := by
    rw [h0, map_mul, map_pow, map_neg, map_one, hNd]
  refine ⟨Matrix.charpoly_monic M, ?_⟩
  rw [hdeg, hrev, Matrix.charpolyRev, hs0]
  have hA : (1 - (X : R[X]) • N.map C) * M.map C = -charmatrix M := by
    rw [sub_mul, one_mul, smul_mul_assoc, ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero C) (map_one C),
      charmatrix, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply, neg_sub]; rfl
  have e1 : (1 - (X : R[X]) • N.map C).det * C M.det = (-1) ^ n * M.charpoly := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_mul, hA, Matrix.det_neg, Fintype.card_fin]; rfl
  have e2 : C N.det * C M.det = (1 : R[X]) := by rw [← C_mul, hdetN, C_1]
  rw [C_mul, C_pow, C_neg, C_1]
  linear_combination (-C N.det) * e1 + (1 - (X : R[X]) • N.map C).det * e2

theorem exists_poly_of_commute {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (M x : Matrix (Fin n) (Fin n) O)
    (hs : M.charpoly.Separable) (hc : x * M = M * x) : ∃ p : O[X], x = aeval M p := by
  have cyclic : ∃ v, IsUnit (GlobalTheory.ClassParam.krylov M v) := by
    haveI : Subsingleton (MaximalSpectrum O) := ⟨fun a b =>
      MaximalSpectrum.ext ((IsLocalRing.eq_maximalIdeal a.isMaximal).trans
        (IsLocalRing.eq_maximalIdeal b.isMaximal).symm)⟩
    obtain ⟨w, hw⟩ := GlobalTheory.RegSS.Semilocal.cyclicSemilocal_of_cyclicField GlobalTheory.RegSS.cyclicField _ (Fin n) M hs
    let σ : Equiv.Perm (Fin n) := (Fintype.equivFin (Fin n)).trans (finCongr (Fintype.card_fin n))
    have hk : GlobalTheory.RegSS.krylov M w = (GlobalTheory.ClassParam.krylov M w).submatrix id σ := by
      ext i j
      simp [GlobalTheory.RegSS.krylov, GlobalTheory.ClassParam.krylov, σ]
    rw [hk, Matrix.det_permute'] at hw
    exact ⟨w, (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hw)⟩
  obtain ⟨v, hv⟩ := cyclic
  set K := GlobalTheory.ClassParam.krylov M v with hK
  have key : ∀ r : Matrix (Fin n) (Fin n) O, r * M = M * r →
      r * K = GlobalTheory.ClassParam.krylov M (r *ᵥ v) := by
    intro r hr
    have hc : Commute r M := hr
    ext i j
    simp only [hK, GlobalTheory.ClassParam.krylov, Matrix.of_apply, Matrix.mul_apply]
    rw [Matrix.mulVec_mulVec, ← (hc.pow_right (j : ℕ)).eq, ← Matrix.mulVec_mulVec]
    rfl
  have hKd : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).1 hv
  set c : Fin n → O := K⁻¹ *ᵥ (x *ᵥ v) with hcdef
  let p : O[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  have hp : aeval M p = ∑ i : Fin n, c i • M ^ (i : ℕ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [p, map_sum, map_mul, aeval_C, aeval_X_pow, Algebra.smul_def]
  have hpv : aeval M p *ᵥ v = x *ᵥ v := by
    have h1 : aeval M p *ᵥ v = K *ᵥ c := by
      rw [hp]
      ext k
      simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul,
        hK, GlobalTheory.ClassParam.krylov, Matrix.of_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [h1, hcdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hKd, Matrix.one_mulVec]
  have hpc : aeval M p * M = M * aeval M p := by
    have e1 : aeval M (p * X) = aeval M p * M := by rw [map_mul, aeval_X]
    have e2 : aeval M (X * p) = M * aeval M p := by rw [map_mul, aeval_X]
    rw [← e1, ← e2, mul_comm]
  refine ⟨p, ?_⟩
  have e : x * K = aeval M p * K := by rw [key x hc, key _ hpc, hpv]
  have := congrArg (· * K⁻¹) e
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKd, Matrix.mul_one] using this

end GlobalTheory.UsideLeaf.UnitaryLocalCharpoly
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.NormStep
open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.UsideLeaf.UnitaryLocalCharpoly

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem norm_step [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) {n : ℕ}
    (γ J Ji Hn Hi : Matrix (Fin n) (Fin n) L) (Q₀ : (intL L)[X])
    (hγ : ∀ i j, γ i j ∈ intL L) (hJ : ∀ i j, J i j ∈ intL L) (hJi : ∀ i j, Ji i j ∈ intL L)
    (hH : ∀ i j, Hn i j ∈ intL L) (hHi : ∀ i j, Hi i j ∈ intL L)
    (hJJ : J * Ji = 1) (hHH : Hn * Hi = 1) (hJh : cT σ J = J) (hHh : cT σ Hn = Hn)
    (hγJ : cT σ γ * J * γ = J) (hγH : cT σ γ * Hn * γ = Hn)
    (hch : γ.charpoly = Q₀.map (intL L).subtype) (hsep : Q₀.Separable) :
    ∃ b : GL (Fin n) L, b.val * γ = γ * b.val ∧ cT σ b.val * J * b.val = Hn := by
  set sO := GlobalTheory.NormEq.sigO σ h.2.1 with hsO
  let Φ : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L := (intL L).subtype.mapMatrix
  have hΦinj : Function.Injective Φ := fun a b hab => by
    ext i j; exact congrFun (congrFun hab i) j
  have hΦcT : ∀ M, Φ (cT sO M) = cT σ (Φ M) := fun M => rfl
  let γO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨γ i j, hγ i j⟩
  let JO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨J i j, hJ i j⟩
  let JiO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨Ji i j, hJi i j⟩
  let HO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨Hn i j, hH i j⟩
  let HiO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨Hi i j, hHi i j⟩
  have eγ : Φ γO = γ := rfl
  have eJ : Φ JO = J := rfl
  have eJi : Φ JiO = Ji := rfl
  have eH : Φ HO = Hn := rfl
  have eHi : Φ HiO = Hi := rfl
  have hJJO : JO * JiO = 1 := hΦinj (by rw [map_mul, map_one, eJ, eJi, hJJ])
  have hJJO' : JiO * JO = 1 := mul_eq_one_comm.1 hJJO
  have hHHO : HO * HiO = 1 := hΦinj (by rw [map_mul, map_one, eH, eHi, hHH])
  have hHHO' : HiO * HO = 1 := mul_eq_one_comm.1 hHHO
  have hγJO : cT sO γO * JO * γO = JO := hΦinj (by rw [map_mul, map_mul, hΦcT, eγ, eJ, hγJ])
  have hγHO : cT sO γO * HO * γO = HO := hΦinj (by rw [map_mul, map_mul, hΦcT, eγ, eH, hγH])
  have hJhO : cT sO JO = JO := hΦinj (by rw [hΦcT, eJ, hJh])
  have hHhO : cT sO HO = HO := hΦinj (by rw [hΦcT, eH, hHh])
  have hchO : γO.charpoly = Q₀ := by
    apply Polynomial.map_injective _ (intL L).subtype_injective
    rw [← hch, ← eγ]
    exact (Matrix.charpoly_map γO (intL L).subtype).symm
  have hsepO : γO.charpoly.Separable := hchO ▸ hsep
  have hcsr : GlobalTheory.UTr.IsCsr sO Q₀ := hchO ▸ isCsr_charpoly sO γO JO JiO hJJO' hγJO
  let P : GlobalTheory.UTr.Csr sO := ⟨Q₀, hcsr⟩
  have hg : aeval γO P.1 = 0 := by
    show aeval γO Q₀ = 0
    rw [← hchO]; exact Matrix.aeval_self_charpoly γO
  let ev := GlobalTheory.UTr.evalMat P γO hg
  have hev : ∀ r : (intL L)[X], ev (aeval (GlobalTheory.UTr.root P) r) = aeval γO r := fun r => by
    rw [← aeval_algHom_apply, GlobalTheory.UTr.evalMat_root]
  have hevinj : Function.Injective ev := by
    refine (injective_iff_map_eq_zero ev).2 fun z hz => ?_
    obtain ⟨r, rfl⟩ := GlobalTheory.UTr.exists_aeval_root P z
    rw [hev] at hz
    have hd := GlobalTheory.T.charpoly_dvd_of_aeval_eq_zero_alt (intL L) n γO r hsepO hz
    rw [hchO] at hd
    exact (GlobalTheory.UTr.aeval_root_eq_zero_iff P).2 hd

  let γiO := JiO * cT sO γO * JO
  have hγi : γiO * γO = 1 := by
    show JiO * cT sO γO * JO * γO = 1
    rw [Matrix.mul_assoc JiO, Matrix.mul_assoc JiO, hγJO, hJJO']
  let gU : UJ sO JO := ⟨⟨γO, γiO, mul_eq_one_comm.1 hγi, hγi⟩, hγJO⟩
  have hcT : ∀ z, cT sO (ev z) * JO = JO * ev (GlobalTheory.UTr.conj P z) := fun z => GlobalTheory.UTr.cT_evalMat P gU hg z

  have hxc : (JiO * HO) * γO = γO * (JiO * HO) := by
    have hA : cT sO γO * (JO * γO * JiO) = 1 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hγJO, hJJO]
    have hA' : (JO * γO * JiO) * cT sO γO = 1 := mul_eq_one_comm.1 hA
    calc JiO * HO * γO = JiO * ((JO * γO * JiO) * cT sO γO) * HO * γO := by rw [hA', Matrix.mul_one]
      _ = γO * JiO * (cT sO γO * HO * γO) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc JiO JO, hJJO', Matrix.one_mul]
      _ = γO * (JiO * HO) := by rw [hγHO, Matrix.mul_assoc]
  obtain ⟨p, hp⟩ := exists_poly_of_commute γO (JiO * HO) hsepO hxc
  let tz : GlobalTheory.UTr.Alg P := aeval (GlobalTheory.UTr.root P) p
  have htO : ev tz = JiO * HO := by rw [hev, ← hp]

  let tiO := HiO * JO
  have htiO : (JiO * HO) * tiO = 1 := by
    show JiO * HO * (HiO * JO) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc HO, hHHO, Matrix.one_mul, hJJO']
  have hdet : IsUnit (ev tz).det := by
    rw [htO]
    exact isUnit_iff_exists_inv.2 ⟨tiO.det, by rw [← Matrix.det_mul, htiO, Matrix.det_one]⟩
  have hunit : IsUnit tz := by
    have h0 : aeval tz (ev tz).charpoly = 0 := hevinj (by
      rw [← aeval_algHom_apply, map_zero]; exact Matrix.aeval_self_charpoly (ev tz))
    have hc0 : IsUnit ((ev tz).charpoly.coeff 0) := by
      have := Matrix.det_eq_sign_charpoly_coeff (ev tz)
      rw [this] at hdet
      exact isUnit_of_mul_isUnit_right hdet
    have e := congrArg (aeval tz) (X_mul_divX_add (ev tz).charpoly)
    rw [h0, map_add (f := _), map_mul, aeval_X, aeval_C] at e
    have hu : IsUnit (tz * aeval tz (ev tz).charpoly.divX) := by
      rw [eq_neg_of_add_eq_zero_left e]
      exact (hc0.map _).neg
    exact isUnit_of_mul_isUnit_left hu
  let T : (GlobalTheory.UTr.Alg P)ˣ := hunit.unit

  have hcTJi : cT sO JiO = JiO := by
    have h1 : cT sO JiO * JO = 1 := by
      rw [← hJhO, ← cT_mul, hJJO, cT_one]
    calc cT sO JiO = cT sO JiO * (JO * JiO) := by rw [hJJO, Matrix.mul_one]
      _ = JiO := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hconj : GlobalTheory.UTr.conj P tz = tz := by
    apply hevinj
    have h1 : JO * ev (GlobalTheory.UTr.conj P tz) = JO * ev tz := by
      rw [← hcT, htO, cT_mul, hHhO, hcTJi, Matrix.mul_assoc, hJJO', Matrix.mul_one, ← Matrix.mul_assoc, hJJO,
        Matrix.one_mul]
    have h2 := congrArg (JiO * ·) h1
    simpa only [← Matrix.mul_assoc, hJJO', Matrix.one_mul] using h2
  have hT : T ∈ GlobalTheory.UTr.plus P := (GlobalTheory.UTr.mem_plus (P := P)).2 (by rw [IsUnit.unit_spec]; exact hconj)
  have hsepP : (P : (intL L)[X]).Separable := hsep
  obtain ⟨u, hu⟩ := GlobalTheory.NormEq.normU_surj L σ ϖ q h P hsepP T hT
  have hu' : (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u = tz := by
    have := congrArg (fun z : (GlobalTheory.UTr.Alg P)ˣ => (z : GlobalTheory.UTr.Alg P)) hu
    simpa [GlobalTheory.UTr.normU, T] using this
  let Ψ : GlobalTheory.UTr.Alg P →* Matrix (Fin n) (Fin n) L := (Φ.comp ev.toRingHom : GlobalTheory.UTr.Alg P →+* _)
  refine ⟨Units.map Ψ u, ?_, ?_⟩
  · show Φ (ev u) * γ = γ * Φ (ev u)
    rw [← eγ, ← map_mul, ← map_mul]
    congr 1
    rw [← GlobalTheory.UTr.evalMat_root P γO hg, ← map_mul, ← map_mul, mul_comm]
  · show cT σ (Φ (ev u)) * J * Φ (ev u) = Hn
    rw [← hΦcT, ← eJ, ← map_mul, ← map_mul, hcT, Matrix.mul_assoc, ← map_mul, mul_comm (GlobalTheory.UTr.conj P _), hu',
      htO, ← Matrix.mul_assoc, hJJO, Matrix.one_mul, eH]

end GlobalTheory.UsideLeaf.UnitaryLocalCharpoly
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.LatticeStep
open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.UsideLeaf.UnitaryLocalCharpoly

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem lattice_step {n : ℕ} (γ γi : Matrix (Fin n) (Fin n) L) (Q₀ : (intL L)[X])
    (hγ : ∀ i j, γ i j ∈ intL L) (hγi : ∀ i j, γi i j ∈ intL L) (hγγ : γ * γi = 1)
    (hch : γ.charpoly = Q₀.map (intL L).subtype) (hsep : Q₀.Separable) (k : GL (Fin n) L)
    (hk : ∀ i j, ((k⁻¹ : GL (Fin n) L).val * γ * k.val) i j ∈ intL L)
    (hki : ∀ i j, ((k⁻¹ : GL (Fin n) L).val * γi * k.val) i j ∈ intL L) :
    ∃ a g : GL (Fin n) L, a.val * γ = γ * a.val ∧ k = a * g ∧ (∀ i j, g.val i j ∈ intL L) ∧
      (∀ i j, (g⁻¹ : GL (Fin n) L).val i j ∈ intL L) := by
  set f : intL L →+* L := (intL L).subtype with hf
  have finj : Function.Injective f := Subtype.val_injective
  set γ' : Matrix (Fin n) (Fin n) L := (k⁻¹ : GL (Fin n) L).val * γ * k.val with hγ'
  let γ₀ : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨γ i j, hγ i j⟩
  let γ₁ : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨γ' i j, hk i j⟩
  have e₀ : γ₀.map f = γ := by
    ext i j
    rfl
  have e₁ : γ₁.map f = γ' := by
    ext i j
    rfl
  have cγ' : γ'.charpoly = γ.charpoly := by
    rw [hγ', Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have c₀ : γ₀.charpoly = Q₀ := by
    apply Polynomial.map_injective f finj
    rw [← Matrix.charpoly_map, e₀, hch]
  have c₁ : γ₁.charpoly = Q₀ := by
    apply Polynomial.map_injective f finj
    rw [← Matrix.charpoly_map, e₁, cγ', hch]
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.BCT.UnitStable.exists_cyclic γ₀ (c₀ ▸ hsep)
  obtain ⟨v₁, hv₁⟩ := GlobalTheory.BCT.UnitStable.exists_cyclic γ₁ (c₁ ▸ hsep)
  set u₀ := hv₀.unit
  set u₁ := hv₁.unit
  set C := GlobalTheory.Orb.companionMat n Q₀
  have h₀ : γ₀ * (u₀ : Matrix (Fin n) (Fin n) (intL L)) = u₀ * C := by
    have := GlobalTheory.Orb.mul_krylov_eq γ₀ v₀
    rw [c₀] at this
    simpa [u₀] using this
  have h₁ : γ₁ * (u₁ : Matrix (Fin n) (Fin n) (intL L)) = u₁ * C := by
    have := GlobalTheory.Orb.mul_krylov_eq γ₁ v₁
    rw [c₁] at this
    simpa [u₁] using this
  set u := u₀ * u₁⁻¹
  have hu : γ₀ * (u : Matrix (Fin n) (Fin n) (intL L)) = u * γ₁ := by
    have e : ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * γ₁ = C * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) := by
      calc ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * γ₁
          = ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * (γ₁ * (u₁ : Matrix (Fin n) (Fin n) (intL L)) * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L))) := by rw [Units.mul_inv_cancel_right]
        _ = ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * ((u₁ : Matrix (Fin n) (Fin n) (intL L)) * C * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L))) := by rw [h₁]
        _ = C * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) := by simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]
    rw [Units.val_mul, ← Matrix.mul_assoc, h₀, Matrix.mul_assoc, Matrix.mul_assoc, e]
  set F : Matrix (Fin n) (Fin n) (intL L) →* Matrix (Fin n) (Fin n) L := (f.mapMatrix : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L).toMonoidHom
  set g : GL (Fin n) L := Units.map F u
  have hgval : g.val = (u : Matrix (Fin n) (Fin n) (intL L)).map f := rfl
  have hginv : (g⁻¹ : GL (Fin n) L).val = ((u⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)).map f := rfl
  have hgg : γ * g.val = g.val * γ' := by
    rw [hgval, ← e₀, ← e₁, ← Matrix.map_mul, ← Matrix.map_mul, hu]
  have hgi : (g⁻¹ : GL (Fin n) L).val * γ = γ' * (g⁻¹ : GL (Fin n) L).val := by
    calc (g⁻¹ : GL (Fin n) L).val * γ
        = (g⁻¹ : GL (Fin n) L).val * (γ * g.val * (g⁻¹ : GL (Fin n) L).val) := by rw [Units.mul_inv_cancel_right]
      _ = (g⁻¹ : GL (Fin n) L).val * (g.val * γ' * (g⁻¹ : GL (Fin n) L).val) := by rw [hgg]
      _ = γ' * (g⁻¹ : GL (Fin n) L).val := by simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]
  refine ⟨k * g⁻¹, g, ?_, by group, fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_assoc, hgi, hγ']
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
  · rw [hgval]
    exact ((u : Matrix (Fin n) (Fin n) (intL L)) i j).2
  · rw [hginv]
    exact (((u⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) i j).2

end GlobalTheory.UsideLeaf.UnitaryLocalCharpoly
end
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.UsideLeaf.hermitian_local_global_existence

theorem mem_intL_iff {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) :
    x ∈ intL (w.adicCompletion E) ↔ x ∈ w.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valuation.mem_integer_iff _ _

theorem mem_KGL_iff {E : Type} [Field E] [NumberField E] (w : Pl E) {n : ℕ} (g : GL (Fin n) (w.adicCompletion E)) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, g.val i j ∈ intL (w.adicCompletion E)) ∧
      (∀ i j, (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val i j ∈ intL (w.adicCompletion E)) := by
  constructor
  · rintro ⟨g0, rfl⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [mem_intL_iff]
      exact (g0.val i j).2
    · rw [← map_inv, mem_intL_iff]
      exact ((g0⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    let O := Ov E w
    have hO : ∀ x, x ∈ intL (w.adicCompletion E) → x ∈ O := fun x hx => (mem_intL_iff w x).1 hx
    let a : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, hO _ (h1 i j)⟩
    let b : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹ : GL (Fin n) _).val i j, hO _ (h2 i j)⟩
    have hinj : Function.Injective (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _) :=
      fun x y hxy => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hxy i) j)
    have ha : O.subtype.mapMatrix a = g.val := rfl
    have hb : O.subtype.mapMatrix b = (g⁻¹ : GL (Fin n) _).val := rfl
    have hab : a * b = 1 := hinj (by rw [map_mul, ha, hb, map_one]; exact g.mul_inv)
    have hba : b * a = 1 := hinj (by rw [map_mul, ha, hb, map_one]; exact g.inv_mul)
    refine ⟨⟨a, b, hab, hba⟩, ?_⟩
    ext i j
    rfl

section Util

variable {A : Type} [CommRing A]

theorem cT_cT (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (M : Matrix (Fin n) (Fin n) A) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem cT_map {E K : Type} [CommRing E] [CommRing K] (φ : E →+* K) (τ : E →+* E) (σ : K →+* K)
    (h : ∀ x, σ (φ x) = φ (τ x)) {n : ℕ} (M : Matrix (Fin n) (Fin n) E) : cT σ (M.map φ) = (cT τ M).map φ := by
  ext i j; simp [cT, h]

theorem int_mul {K : Type} [Ring K] (S : Subring K) {n : ℕ} {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, M i j ∈ S) (hN : ∀ i j, N i j ∈ S) : ∀ i j, (M * N) i j ∈ S := fun i j => by
  rw [Matrix.mul_apply]; exact S.sum_mem fun k _ => S.mul_mem (hM i k) (hN k j)

theorem int_cT {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K)
    (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, M i j ∈ intL K) : ∀ i j, cT σ M i j ∈ intL K := fun i j => by
  have h := hM j i
  simp only [intL, Valuation.mem_integer_iff] at h ⊢
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, hσ]
  exact h

end Util

theorem sep_int {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K)
    (hγ : ∀ i j, γ i j ∈ intL K) (A B : K[X]) (hA : ∀ i, A.coeff i ∈ intL K) (hB : ∀ i, B.coeff i ∈ intL K)
    (hAB : A * γ.charpoly + B * derivative γ.charpoly = 1) :
    ∃ Q₀ : (intL K)[X], γ.charpoly = Q₀.map (intL K).subtype ∧ Q₀.Separable := by
  let γO : Matrix (Fin n) (Fin n) (intL K) := fun i j => ⟨γ i j, hγ i j⟩
  have hγO : γO.map (intL K).subtype = γ := by ext i j; rfl
  have hlift : ∀ C : K[X], (∀ i, C.coeff i ∈ intL K) → ∃ CO : (intL K)[X], CO.map (intL K).subtype = C := by
    intro C hC
    have : C ∈ Polynomial.lifts (intL K).subtype :=
      (Polynomial.lifts_iff_coeff_lifts _).2 fun i => ⟨⟨_, hC i⟩, rfl⟩
    obtain ⟨p, hp⟩ := this
    exact ⟨p, hp⟩
  obtain ⟨AO, hAO⟩ := hlift A hA
  obtain ⟨BO, hBO⟩ := hlift B hB
  refine ⟨γO.charpoly, by rw [← Matrix.charpoly_map, hγO], ?_⟩
  refine ⟨AO, BO, Polynomial.map_injective (intL K).subtype Subtype.val_injective ?_⟩
  rw [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map, hAO, hBO,
    ← Matrix.charpoly_map, hγO, hAB, Polynomial.map_one]

theorem local_good (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (γ₀ : GL (Fin n) E)
    (H₀ : Matrix (Fin n) (Fin n) E) (hH₀ : IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀)
    (hd : H₀.det ≠ 0)
    (hγH : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀)
    (A B : E[X]) (hAB : A * γ₀.val.charpoly + B * derivative γ₀.val.charpoly = 1)
    (w : Pl E) (hw : ¬ IsSplitAt w)
    (h1 : ∀ i j, algebraMap E (w.adicCompletion E) (γ₀.val i j) ∈ w.adicCompletionIntegers E)
    (h2 : ∀ i j, algebraMap E (w.adicCompletion E) ((γ₀⁻¹ : GL (Fin n) E).val i j) ∈ w.adicCompletionIntegers E)
    (h3 : ∀ i j, algebraMap E (w.adicCompletion E) (H₀ i j) ∈ w.adicCompletionIntegers E)
    (h4 : ∀ i j, algebraMap E (w.adicCompletion E) (H₀⁻¹ i j) ∈ w.adicCompletionIntegers E)
    (h5 : ∀ i, algebraMap E (w.adicCompletion E) (A.coeff i) ∈ w.adicCompletionIntegers E)
    (h6 : ∀ i, algebraMap E (w.adicCompletion E) (B.coeff i) ∈ w.adicCompletionIntegers E)
    (Hw : Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (hHw : IsHerm (cj w) Hw ∧ Hw.det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * Hw *
      γ₀.val.map (algebraMap E (w.adicCompletion E)) = Hw)
    (k m : GL (Fin n) (w.adicCompletion E))
    (hk : k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w (n := n))
    (hm : m ∈ GlobalTheory.LFun.KGL w (n := n)) (hkm : m.val = cT (cj w) k.val * Hw * k.val) :
    ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) =
      γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧
      Hw = cT (cj w) c.val * H₀.map (algebraMap E (w.adicCompletion E)) * c.val := by
  set φ : E →+* (w.adicCompletion E) := algebraMap E (w.adicCompletion E) with hφ
  set τ : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hτ
  obtain ⟨-, hinv, hiso, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨hext, ⟨ϖ, q, hUI, -⟩, -⟩ := hns hw
  have hext' : ∀ x, cj w (φ x) = φ (τ x) := hext
  have hcT : ∀ M : Matrix (Fin n) (Fin n) E, cT (cj w) (M.map φ) = (cT τ M).map φ := cT_map φ τ (cj w) hext'
  set γw := γ₀.val.map φ with hγw
  set γiw := (γ₀⁻¹ : GL (Fin n) E).val.map φ with hγiw
  set J := H₀.map φ with hJ
  set Ji := H₀⁻¹.map φ with hJi
  have hI : ∀ x : E, φ x ∈ w.adicCompletionIntegers E → φ x ∈ intL (w.adicCompletion E) := fun x hx => (mem_intL_iff w _).2 hx
  have iγ : ∀ i j, γw i j ∈ intL (w.adicCompletion E) := fun i j => hI _ (h1 i j)
  have iγi : ∀ i j, γiw i j ∈ intL (w.adicCompletion E) := fun i j => hI _ (h2 i j)
  have iJ : ∀ i j, J i j ∈ intL (w.adicCompletion E) := fun i j => hI _ (h3 i j)
  have iJi : ∀ i j, Ji i j ∈ intL (w.adicCompletion E) := fun i j => hI _ (h4 i j)
  have hmap1 : (1 : Matrix (Fin n) (Fin n) E).map φ = 1 := Matrix.map_one _ (map_zero φ) (map_one φ)
  have hγγ : γw * γiw = 1 := by rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, hmap1]
  have hJJ : J * Ji = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), hmap1]
  have hJh : cT (cj w) J = J := by rw [hcT]; exact congrArg (fun M => M.map φ) hH₀
  have hγJ : cT (cj w) γw * J * γw = J := by
    rw [hcT, ← Matrix.map_mul, ← Matrix.map_mul, hγH]

  have hABw : A.map φ * γw.charpoly + B.map φ * derivative γw.charpoly = 1 := by
    rw [hγw, Matrix.charpoly_map, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul,
      ← Polynomial.map_add, hAB, Polynomial.map_one]
  obtain ⟨Q₀, hch, hsep⟩ := sep_int γw iγ (A.map φ) (B.map φ) (fun i => by rw [Polynomial.coeff_map]; exact hI _ (h5 i))
    (fun i => by rw [Polynomial.coeff_map]; exact hI _ (h6 i)) hABw

  obtain ⟨hk1, hk2⟩ := (mem_KGL_iff w _).1 hk
  have hkv : (k⁻¹ * GeneralLinearGroup.map φ γ₀ * k).val = (k⁻¹ : GL (Fin n) (w.adicCompletion E)).val * γw * k.val := rfl
  have hkiv : ((k⁻¹ * GeneralLinearGroup.map φ γ₀ * k)⁻¹ : GL (Fin n) (w.adicCompletion E)).val =
      (k⁻¹ : GL (Fin n) (w.adicCompletion E)).val * γiw * k.val := by
    rw [show (k⁻¹ * GeneralLinearGroup.map φ γ₀ * k)⁻¹ = k⁻¹ * GeneralLinearGroup.map φ γ₀⁻¹ * k by
      rw [map_inv]; group]
    rfl
  obtain ⟨a, g, hac, rfl, ig, igi⟩ := GlobalTheory.UsideLeaf.UnitaryLocalCharpoly.lattice_step γw γiw Q₀ iγ iγi hγγ hch hsep k
    (fun i j => hkv ▸ hk1 i j) (fun i j => hkiv ▸ hk2 i j)
  obtain ⟨im, imi⟩ := (mem_KGL_iff w _).1 hm

  set σ := cj w
  set Hn := cT σ a.val * Hw * a.val with hHn
  have hcTg : cT σ (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * cT σ g.val = 1 := by
    rw [← cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one]
  have hHn' : Hn = cT σ (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * m.val * (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val := by
    rw [hkm, Units.val_mul, cT_mul]
    calc Hn = (cT σ (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * cT σ g.val) * Hn * (g.val * (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val) := by
          rw [hcTg, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [hHn, Matrix.mul_assoc]
  set Hi := g.val * (m⁻¹ : GL (Fin n) (w.adicCompletion E)).val * cT σ g.val with hHi
  have iH : ∀ i j, Hn i j ∈ intL (w.adicCompletion E) := by
    rw [hHn']; exact int_mul _ (int_mul _ (int_cT σ hiso igi) im) igi
  have iHi : ∀ i j, Hi i j ∈ intL (w.adicCompletion E) := int_mul _ (int_mul _ ig imi) (int_cT σ hiso ig)
  have hHH : Hn * Hi = 1 := by
    rw [hHn', hHi]
    calc cT σ (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * m.val * (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * (g.val * (m⁻¹ : GL (Fin n) (w.adicCompletion E)).val * cT σ g.val)
        = cT σ (g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * (m.val * (((g⁻¹ : GL (Fin n) (w.adicCompletion E)).val * g.val) * (m⁻¹ : GL (Fin n) (w.adicCompletion E)).val)) *
          cT σ g.val := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Matrix.mul_one, ← cT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one]
  have hHh : cT σ Hn = Hn := by
    rw [hHn, cT_mul, cT_mul, cT_cT σ hinv, hHw.1, Matrix.mul_assoc]
  have hγH' : cT σ γw * Hn * γw = Hn := by
    calc cT σ γw * Hn * γw = cT σ (a.val * γw) * Hw * (a.val * γw) := by
          rw [hHn, cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ (γw * a.val) * Hw * (γw * a.val) := by rw [hac]
      _ = cT σ a.val * (cT σ γw * Hw * γw) * a.val := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = Hn := by rw [hHw.2.2]

  obtain ⟨b, hbc, hbJ⟩ := GlobalTheory.UsideLeaf.UnitaryLocalCharpoly.norm_step σ ϖ q hUI γw J Ji Hn Hi Q₀ iγ iJ iJi iH iHi hJJ hHH hJh
    hHh hγJ hγH' hch hsep
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · have hai : (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val * γw = γw * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val := by
      calc (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val * γw = (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val * (γw * a.val) * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val * (a.val * γw) * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val := by rw [hac]
        _ = _ := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [Units.val_mul, Matrix.mul_assoc, hai, ← Matrix.mul_assoc, hbc, Matrix.mul_assoc]
  · calc Hw = cT σ (a.val * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val) * Hw * (a.val * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, cT_one, Matrix.one_mul, Matrix.mul_one]
      _ = cT σ (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val * Hn * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val := by
          rw [hHn, cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val * (cT σ b.val * J * b.val) * (a⁻¹ : GL (Fin n) (w.adicCompletion E)).val := by rw [hbJ]
      _ = _ := by rw [Units.val_mul, cT_mul]; simp only [Matrix.mul_assoc]

theorem eventually_int {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : Pl E in cofinite, algebraMap E (w.adicCompletion E) x ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) x).2

theorem eventually_int_coeff {E : Type} [Field E] [NumberField E] (A : E[X]) :
    ∀ᶠ w : Pl E in cofinite, ∀ i, algebraMap E (w.adicCompletion E) (A.coeff i) ∈ w.adicCompletionIntegers E := by
  have h := (Filter.eventually_all_finset A.support).2 fun i _ => eventually_int (A.coeff i)
  filter_upwards [h] with w hw i
  by_cases hi : i ∈ A.support
  · exact hw i hi
  · rw [Polynomial.notMem_support_iff.1 hi, map_zero]
    exact zero_mem _

theorem eventually_int_mat {E : Type} [Field E] [NumberField E] {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    ∀ᶠ w : Pl E in cofinite, ∀ i j, algebraMap E (w.adicCompletion E) (M i j) ∈ w.adicCompletionIntegers E :=
  Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_int (M i j)

end GlobalTheory.UsideLeaf.hermitian_local_global_existence

theorem GlobalTheory.UsideLeaf.hermitian_local_global_existence.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ k m : GL (Fin n) (w.adicCompletion E), k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w (n := n) ∧ m ∈ GlobalTheory.LFun.KGL w (n := n) ∧ m.val = cT (cj w) k.val * H w * k.val) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H w = cT (cj w) c.val * H₀.map (algebraMap E (w.adicCompletion E)) * c.val) := by
  intro E _ _ _ hU n γ₀ hEll H₀ hH₀ hd hγH H hH hlat
  obtain ⟨A, B, hAB⟩ := hEll.2.2.1
  filter_upwards [hlat, GlobalTheory.UsideLeaf.hermitian_local_global_existence.eventually_int_mat γ₀.val,
    GlobalTheory.UsideLeaf.hermitian_local_global_existence.eventually_int_mat (γ₀⁻¹ : GL (Fin n) E).val,
    GlobalTheory.UsideLeaf.hermitian_local_global_existence.eventually_int_mat H₀, GlobalTheory.UsideLeaf.hermitian_local_global_existence.eventually_int_mat H₀⁻¹,
    GlobalTheory.UsideLeaf.hermitian_local_global_existence.eventually_int_coeff A, GlobalTheory.UsideLeaf.hermitian_local_global_existence.eventually_int_coeff B]
    with w hw h1 h2 h3 h4 h5 h6 hns
  obtain ⟨k, m, hk, hm, hkm⟩ := hw hns
  exact GlobalTheory.UsideLeaf.hermitian_local_global_existence.local_good E hU n γ₀ H₀ hH₀ hd hγH A B hAB w hns h1 h2 h3 h4 h5 h6 (H w) (hH w hns)
    k m hk hm hkm
