module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocFour
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSplitCongr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSplitRep
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pSplitRep :
    SplitRep := by
  intro R _ tr nm ρ hρ hd u
  obtain ⟨w, hw⟩ := hd.exists_right_inv
  refine ⟨1 - ((tr : R) - ρ) * ((u - 1) * w), (u - 1) * w, ?_⟩
  unfold qf
  linear_combination ((u - 1) * w) ^ 2 * hρ + (u - 1) * hw
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadicUnitNorm
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma UpperTheory.Gal.G1.normInt_eq_one {q : ℕ} [Fact q.Prime] {n : ℤ} (h : ¬ (q : ℤ) ∣ n) :
    ‖(n : ℤ_[q])‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun hlt => h ((PadicInt.norm_int_lt_one_iff_dvd n).mp hlt))

private lemma UpperTheory.Gal.G1.norm_lt_one_iff_toZMod {q : ℕ} [Fact q.Prime] (x : ℤ_[q]) :
    ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

private lemma UpperTheory.Gal.G1.norm_eq_one_of_toZMod {q : ℕ} [Fact q.Prime] {x : ℤ_[q]}
    (h : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun hlt => h ((UpperTheory.Gal.G1.norm_lt_one_iff_toZMod x).mp hlt))

private lemma UpperTheory.Gal.G1.hens {q : ℕ} [Fact q.Prime] (c d a : ℤ_[q]) (h2 : ‖(2 : ℤ_[q])‖ = 1)
    (hc : ‖c‖ = 1) (ha : ‖a‖ = 1) (h : ‖c * a ^ 2 + d‖ < 1) : ∃ z : ℤ_[q], c * z ^ 2 + d = 0 := by
  let F : Polynomial ℤ_[q] := Polynomial.C c * Polynomial.X ^ 2 + Polynomial.C d
  have hF : ∀ t, Polynomial.aeval t F = c * t ^ 2 + d := by
    intro t; simp [F]
  have hF' : ∀ t, Polynomial.aeval t (Polynomial.derivative F) = c * (2 * t) := by
    intro t
    simp [F]
    exact Or.inl (Or.inl one_add_one_eq_two)
  have hn : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1 := by
    rw [hF', norm_mul, norm_mul, hc, h2, ha]; simp
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [hn, hF]; simpa using h)
  exact ⟨z, by rwa [hF] at hz⟩

theorem UpperTheory.Gal.G1.pPadicUnitNorm :
    PadicUnitNorm := by
  intro q _ D hqD u hu
  have hq2 : ¬ (q : ℤ) ∣ 2 := fun h => hqD (Dvd.dvd.mul_right h D)
  have hqd : ¬ (q : ℤ) ∣ D := fun h => hqD (Dvd.dvd.mul_left h 2)
  have h2 : ‖(2 : ℤ_[q])‖ = 1 := by
    have := UpperTheory.Gal.G1.normInt_eq_one (q := q) hq2
    simpa using this
  have hD : ‖(D : ℤ_[q])‖ = 1 := UpperTheory.Gal.G1.normInt_eq_one hqd
  have hodd : Fintype.card (ZMod q) % 2 = 1 := by
    rw [ZMod.card]
    rcases (Fact.out : q.Prime).eq_two_or_odd with h | h
    · subst h; exact absurd (by norm_num) hq2
    · exact h
  let U : ℤ_[q] := ⟨u, hu.le⟩
  have hU : ‖U‖ = 1 := hu
  have hUc : ((U : ℤ_[q]) : ℚ_[q]) = u := rfl
  have hub : PadicInt.toZMod U ≠ 0 := fun h0 =>
    absurd hU ((UpperTheory.Gal.G1.norm_lt_one_iff_toZMod U).mpr h0).ne
  have hDb : -(D : ZMod q) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hqd
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2)
    (g := Polynomial.C (-(D : ZMod q)) * Polynomial.X ^ 2 + Polynomial.C 0 * Polynomial.X
      + Polynomial.C (-PadicInt.toZMod U))
    (by simp) (Polynomial.degree_quadratic hDb) hodd
  have hab' : a ^ 2 - (D : ZMod q) * b ^ 2 - PadicInt.toZMod U = 0 := by
    simp at hab
    linear_combination hab
  let x0 : ℤ_[q] := (a.val : ℤ_[q])
  let y0 : ℤ_[q] := (b.val : ℤ_[q])
  have hx : PadicInt.toZMod x0 = a := by simp [x0]
  have hy : PadicInt.toZMod y0 = b := by simp [y0]
  have hDz : PadicInt.toZMod (D : ℤ_[q]) = (D : ZMod q) := by simp
  have key : ‖x0 ^ 2 - (D : ℤ_[q]) * y0 ^ 2 - U‖ < 1 := by
    rw [UpperTheory.Gal.G1.norm_lt_one_iff_toZMod]
    simp only [map_sub, map_mul, map_pow, hx, hy, hDz]
    exact hab'
  have hor : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨ha0, hb0⟩ := hcon
    apply hub
    rw [ha0, hb0] at hab'
    simpa using hab'
  rcases hor with ha | hb
  · have hx1 : ‖x0‖ = 1 := UpperTheory.Gal.G1.norm_eq_one_of_toZMod (by rwa [hx])
    obtain ⟨z, hz⟩ := UpperTheory.Gal.G1.hens 1 (-((D : ℤ_[q]) * y0 ^ 2 + U)) x0 h2 (by simp) hx1 (by
      have e : 1 * x0 ^ 2 + -((D : ℤ_[q]) * y0 ^ 2 + U) = x0 ^ 2 - (D : ℤ_[q]) * y0 ^ 2 - U := by ring
      rw [e]; exact key)
    refine ⟨z, y0, ?_⟩
    have h3 := congrArg (fun t : ℤ_[q] => (t : ℚ_[q])) hz
    simp only [PadicInt.coe_add, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_neg, PadicInt.coe_one,
      PadicInt.coe_zero, PadicInt.coe_intCast, hUc] at h3
    linear_combination -h3
  · have hy1 : ‖y0‖ = 1 := UpperTheory.Gal.G1.norm_eq_one_of_toZMod (by rwa [hy])
    obtain ⟨z, hz⟩ := UpperTheory.Gal.G1.hens (D : ℤ_[q]) (U - x0 ^ 2) y0 h2 hD hy1 (by
      have e : (D : ℤ_[q]) * y0 ^ 2 + (U - x0 ^ 2) = -(x0 ^ 2 - (D : ℤ_[q]) * y0 ^ 2 - U) := by ring
      rw [e, norm_neg]; exact key)
    refine ⟨x0, z, ?_⟩
    have h3 := congrArg (fun t : ℤ_[q] => (t : ℚ_[q])) hz
    simp only [PadicInt.coe_add, PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_zero, PadicInt.coe_intCast, hUc] at h3
    linear_combination h3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PRelOf
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.G1

private theorem key_mat {E : Type} [Field E] {n : ℕ} (H Q b b' R : Matrix (Fin n) (Fin n) E) (hd : H.det ≠ 0) (s : E)
    (h : b' * H⁻¹ = Q * (s • (b * H⁻¹)) * R) : b' = s • (Q * b * (H⁻¹ * R * H)) := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.2 hd
  have h1 : b' = (b' * H⁻¹) * H := (Matrix.nonsing_inv_mul_cancel_right _ _ hu).symm
  rw [h1, h]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem pRelOf : RelOf := by
  intro E _ _ _ A n p _ S B B' s hs P hP h
  have hH := A.det_ne n
  have key := key_mat (A.H n) Pᵀ (mat S ↑B.β) (mat S ↑B'.β) (P.map ⇑(IsCMField.complexConj E)) hH
    (s : E) h
  have hdetT : IsUnit (Pᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hP
  have hu : IsUnit Pᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr hdetT
  have hHc : (A.H n).map ⇑(IsCMField.complexConj E) = A.H n := by
    have h1 := A.herm n
    calc (A.H n).map ⇑(IsCMField.complexConj E) = (((A.H n).map (cj E))ᵀ)ᵀ :=
          (Matrix.transpose_transpose _).symm
      _ = (A.H n)ᵀ := by rw [h1]
      _ = A.H n := by simp [Arith.H]
  have hsh : MulOpposite.unop (hermStar (A.H n) hH Pᵀ) = (A.H n)⁻¹ * P.map ⇑(IsCMField.complexConj E) * A.H n := by
    rw [hermStar_apply]
    change ((A.H n).map ⇑(IsCMField.complexConj E))⁻¹ * ((Pᵀ).map ⇑(IsCMField.complexConj E))ᵀ *
      (A.H n).map ⇑(IsCMField.complexConj E) = _
    rw [hHc, Matrix.transpose_map, Matrix.transpose_transpose]
  refine ⟨hu.unit, s, hs, ?_⟩
  change mat S ↑B'.β = algebraMap ℚ (Matrix (Fin n) (Fin n) E) s *
    (Pᵀ * mat S ↑B.β * MulOpposite.unop (hermStar (A.H n) hH Pᵀ))
  rw [hsh, key, ← Algebra.smul_def, ← algebraMap_smul E s, eq_ratCast]

end UpperTheory.Gal.G1
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PNormTwo
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pNormTwo :
    AdFour → NormTwo := by
  intro hA E _ _ _ A
  let F : Type := maximalRealSubfield E
  have hcF : (A.c : E) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff E, ← A.bar_eq, A.c_real]
  let cf : F := ⟨(A.c : E), hcF⟩
  have hcfE : algebraMap F E cf = (A.c : E) := rfl
  have hcint : IsIntegral ℤ cf := by
    have h : IsIntegral ℤ (algebraMap F E cf) := by rw [hcfE]; exact A.c.2
    exact (isIntegral_algebraMap_iff ).1 h
  let c0 : 𝓞 F := ⟨cf, hcint⟩
  have hc0 : ((c0 : 𝓞 F) : F) = cf := rfl
  have hc0ne : c0 ≠ 0 := by
    intro h
    have h1 : ((c0 : 𝓞 F) : F) = 0 := by rw [h]; simp
    have h2 : (A.c : E) = 0 := by
      rw [← hcfE, ← hc0, h1, map_zero]
    exact A.c_ne h2
  obtain ⟨a, ha1, ha2⟩ := hA F A.tr A.nm A.disc_neg.ne c0 hc0ne
  let ι := GlobalTheory.AdeleBaseChange.adMap F E
  let ω' : FiniteAdeleRing (𝓞 E) E := algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.ω : E)
  let ωb : FiniteAdeleRing (𝓞 E) E := algebraMap E (FiniteAdeleRing (𝓞 E) E) ((A.bar A.ω : 𝓞 E) : E)
  have hfix : ∀ x : F, (IsCMField.complexConj E).toRingEquiv (algebraMap F E x) = algebraMap F E x := fun x =>
    (IsCMField.complexConj_eq_self_iff E _).2 x.2
  have hcι : ∀ z, cF E (ι z) = ι z := fun z => GlobalTheory.DefU.ClassFin.conjFin_adMap _ hfix z
  have hcω : cF E ω' = ωb := by
    show conjFin _ (algebraMap E _ _) = _
    rw [conjFin_algebraMap]
    show algebraMap E _ (IsCMField.complexConj E (A.ω : E)) = _
    rw [← A.bar_eq]
  have hsum : ω' + ωb = (A.tr : FiniteAdeleRing (𝓞 E) E) := by
    have h : (A.ω : E) + ((A.bar A.ω : 𝓞 E) : E) = (A.tr : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) A.tr_eq
      simpa using this
    show algebraMap E _ _ + algebraMap E _ _ = _
    rw [← map_add (f := _), h, map_intCast]
  have hprod : ω' * ωb = (A.nm : FiniteAdeleRing (𝓞 E) E) := by
    have h : (A.ω : E) * ((A.bar A.ω : 𝓞 E) : E) = (A.nm : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) A.nm_eq
      simpa using this
    show algebraMap E _ _ * algebraMap E _ _ = _
    rw [← map_mul, h, map_intCast]
  have hnorm : ∀ s t, (ι s + ι t * ω') * cF E (ι s + ι t * ω') = ι (qf A.tr A.nm s t) := by
    intro s t
    rw [map_add (f := _), map_mul, hcι, hcι, hcω]
    simp only [qf, map_add (f := _), map_mul, map_pow, map_intCast]
    linear_combination (ι s * ι t) * hsum + (ι t) ^ 2 * hprod
  have hcalg : algebraMap E (FiniteAdeleRing (𝓞 E) E) (A.c : E) =
      ι (algebraMap F (FiniteAdeleRing (𝓞 F) F) ((c0 : 𝓞 F) : F)) := by
    rw [GlobalTheory.AdeleBaseChange.adMap_algebraMap]
    rfl
  refine ⟨ι (a 0) + ι (a 1) * ω', ι (a 2) + ι (a 3) * ω', ?_, ?_⟩
  · rw [hnorm, hnorm, hcalg, ← map_add (f := _), ← map_mul, ha1, map_one]
  · intro w q hq hG hqw
    let v : HeightOneSpectrum (𝓞 F) := w.under (𝓞 F)
    have hqv : (q : 𝓞 F) ∈ v.asIdeal := by
      show algebraMap (𝓞 F) (𝓞 E) (q : 𝓞 F) ∈ w.asIdeal
      rw [map_natCast]
      exact hqw
    have hcv : c0 ∉ v.asIdeal := by
      intro hc
      have hcw : A.c ∈ w.asIdeal := hc
      obtain ⟨e, hcop, -, c', hc'⟩ := hG.2
      have hew : (e : 𝓞 E) ∈ w.asIdeal := hc' ▸ w.asIdeal.mul_mem_right c' hcw
      have hb := Nat.isCoprime_iff_coprime.2 hcop
      obtain ⟨u, u', huu⟩ := hb
      have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
        have h2 : (u : 𝓞 E) * (e : 𝓞 E) + (u' : 𝓞 E) * (q : 𝓞 E) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huu
        rw [← h2]
        exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hew) (w.asIdeal.mul_mem_left _ hqw)
      exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    have hai : ∀ i, a i v ∈ v.adicCompletionIntegers F :=
      ha2 v q hq hqv hG.1.1 hG.1.2 hcv
    have hιi : ∀ i, pLoc E w (ι (a i)) ∈ w.adicCompletionIntegers E := fun i =>
      GlobalTheory.AdeleBaseChange.locMap_int w _ (hai i)
    have hωi : pLoc E w ω' ∈ w.adicCompletionIntegers E :=
      HeightOneSpectrum.coe_mem_adicCompletionIntegers w A.ω
    have hωbi : pLoc E w ωb ∈ w.adicCompletionIntegers E :=
      HeightOneSpectrum.coe_mem_adicCompletionIntegers w (A.bar A.ω)
    have hform : ∀ i j, pLoc E w (ι (a i) + ι (a j) * ω') ∈ w.adicCompletionIntegers E := fun i j => by
      rw [map_add (f := _), map_mul]
      exact add_mem (hιi i) (mul_mem (hιi j) hωi)
    have hformc : ∀ i j, pLoc E w (cF E (ι (a i) + ι (a j) * ω')) ∈ w.adicCompletionIntegers E := fun i j => by
      rw [map_add (f := _), map_mul, hcι, hcι, hcω, map_add (f := _), map_mul]
      exact add_mem (hιi i) (mul_mem (hιi j) hωbi)
    exact ⟨hform 0 1, hform 2 3, hformc 0 1, hformc 2 3⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PTrivMat
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pTrivMat :
    TrivMat := by
  intro E _ _ _ n H hH hH' hd R _ _ K _ _ ψ β x t hx
  let L := K ⊗[↥(maximalRealSubfield E)] E
  letI : Algebra ℚ L := ((algebraMap K L).comp (ψ.comp (algebraMap ℚ R))).toAlgebra
  let s : R →+* L := (algebraMap K L).comp ψ
  let e : E →+* L := Algebra.TensorProduct.includeRight.toRingHom
  let f : R →ₐ[ℚ] Matrix (Fin n) (Fin n) L := ((algebraMap L (Matrix (Fin n) (Fin n) L)).comp s).toRatAlgHom
  let g : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Matrix (Fin n) (Fin n) L := (e.mapMatrix).toRatAlgHom
  have hfg : ∀ a b, Commute (f a) (g b) := fun a b => Algebra.commutes (s a) (g b)
  let φ := Algebra.TensorProduct.lift f g hfg
  have hφ : ∀ (r : R) (m : Matrix (Fin n) (Fin n) E), φ (r ⊗ₜ m) = s r • m.map e := by
    intro r m
    show f r * g m = _
    rw [Algebra.smul_def]
    rfl
  let c := GlobalTheory.HermGlobal.baseConj (IsCMField.complexConj E) K
  have hc1 : ∀ y : E, c (e y) = e (cj E y) := by
    intro y
    simp [c, e, GlobalTheory.HermGlobal.baseConj]
  have hc2 : ∀ r : R, c (s r) = s r := by
    intro r
    show c (ψ r ⊗ₜ 1) = ψ r ⊗ₜ 1
    simp [c, GlobalTheory.HermGlobal.baseConj]
  have hHu : IsUnit H.det := isUnit_iff_ne_zero.mpr hd
  have hinv : (H.map e)⁻¹ = H⁻¹.map e := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hHu, Matrix.map_one _ (map_zero e) (map_one e)]
  have hright : H.map e * H⁻¹.map e = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hHu, Matrix.map_one _ (map_zero e) (map_one e)]
  have hmap : ∀ (r : R) (m : Matrix (Fin n) (Fin n) E),
      (s r • m.map e).map c = s r • (m.map (cj E)).map e := by
    intro r m
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hc1, hc2]
  have hH2 : H.map ⇑(↑(IsCMField.complexConj E) : E →+* E) = H := hH'
  have hstar : ∀ y, φ (MulOpposite.unop ((starT (hermStar H hd) R) y)) =
      H⁻¹.map e * ((φ y).map c)ᵀ * H.map e := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [starT_tmul, hermStar_apply, hφ, hφ, hmap, hH2, Matrix.map_mul, Matrix.map_mul,
        Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_map]
    | add a b ha hb =>
      simp only [map_add (f := _), MulOpposite.unop_add, ha, hb]
      rw [Matrix.map_add _ (map_add c), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  refine ⟨φ x, ?_, ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).mp (x.isUnit.map φ)
  · have key := congrArg φ hx
    rw [map_mul, map_mul, hstar, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, hφ, hφ, map_one, one_smul, Matrix.map_one _ (map_zero e) (map_one e)] at key
    show φ x * (β * H⁻¹).map e * ((φ x).map c)ᵀ = ψ t • H⁻¹.map e
    have hsm : ψ t • H⁻¹.map e = s t • H⁻¹.map e := (algebraMap_smul L (ψ t) _).symm
    rw [hsm]
    calc φ x * (β * H⁻¹).map e * ((φ x).map c)ᵀ
        = φ x * β.map e * (H⁻¹.map e * ((φ x).map c)ᵀ * H.map e) * H⁻¹.map e := by
          rw [Matrix.map_mul]
          simp only [Matrix.mul_assoc, hright, Matrix.mul_one]
      _ = s t • H⁻¹.map e := by
          rw [key, Matrix.smul_mul, Matrix.one_mul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PDefSign
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem re_dot_swap {n : ℕ} (y x : Fin n → ℂ) : (star y ⬝ᵥ x).re = (star x ⬝ᵥ y).re := by
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

private theorem def_of_inv {n : ℕ} (M Mi : Matrix (Fin n) (Fin n) ℂ) (h1 : Mi * M = 1) (s : ℝ)
    (h : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < s * (star y ⬝ᵥ (Mi *ᵥ y)).re) (x : Fin n → ℂ) (hx : x ≠ 0) :
    0 < s * (star x ⬝ᵥ (M *ᵥ x)).re := by
  have hy : M *ᵥ x ≠ 0 := by
    intro h0
    apply hx
    have := congrArg (fun v => Mi *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, h1] using this
  have := h _ hy
  rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, re_dot_swap] at this

private theorem def_conj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (s : ℝ)
    (h : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < s * (star y ⬝ᵥ (M *ᵥ y)).re) (x : Fin n → ℂ) (hx : x ≠ 0) :
    0 < s * (star x ⬝ᵥ (M.map (starRingEnd ℂ) *ᵥ x)).re := by
  have hy : star x ≠ 0 := by
    intro h0
    apply hx
    simpa using congrArg star h0
  have key : star x ⬝ᵥ (M.map (starRingEnd ℂ) *ᵥ x) =
      starRingEnd ℂ (star (star x) ⬝ᵥ (M *ᵥ star x)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, Matrix.mulVec, map_sum, map_mul]
  rw [key, Complex.conj_re]
  exact h _ hy

private theorem inv_map_ring {n : ℕ} {R R' : Type*} [Field R] [Field R'] (f : R →+* R') (A : Matrix (Fin n) (Fin n) R)
    (hA : A.det ≠ 0) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),
    Matrix.map_one _ (map_zero f) (map_one f)]

private theorem herm_N {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (H β : Matrix (Fin n) (Fin n) E)
    (hH : H.map (cj E) = H) (hT : Hᵀ = H) (hd : H.det ≠ 0) (hs : H⁻¹ * (β.map (cj E))ᵀ * H = β) (a b : Fin n) :
    IsCMField.complexConj E ((β * H⁻¹) a b) = (β * H⁻¹) b a := by
  have hHi : (H⁻¹).map (cj E) = H⁻¹ := by rw [inv_map_ring _ _ hd, hH]
  have hHiT : (H⁻¹)ᵀ = H⁻¹ := by rw [Matrix.transpose_nonsing_inv, hT]
  have key : ((β * H⁻¹).map (cj E))ᵀ = β * H⁻¹ := by
    rw [Matrix.map_mul, hHi, Matrix.transpose_mul, hHiT]
    conv_rhs => rw [← hs]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), Matrix.mul_one]
  have := congrFun (congrFun key b) a
  rw [Matrix.transpose_apply, Matrix.map_apply] at this
  exact this

theorem UpperTheory.Gal.G1.pDefSign :
    DefSign := by
  classical
  intro E _ _ _ A n p _ S B
  have hT : (A.H n)ᵀ = A.H n := Matrix.diagonal_transpose _
  have hH' : (A.H n).map (cj E) = A.H n := by
    have h := congrArg Matrix.transpose (A.herm n)
    rw [Matrix.transpose_transpose] at h
    rw [h]
    exact hT
  have hsym : (A.H n)⁻¹ * ((mat S ↑B.β).map (cj E))ᵀ * A.H n = mat S ↑B.β := by
    have h := B.sym
    change MulOpposite.unop (hermStar (A.H n) (A.det_ne n) (mat S ↑B.β)) = mat S ↑B.β at h
    rw [hermStar_apply] at h
    change ((A.H n).map (cj E))⁻¹ * ((mat S ↑B.β).map (cj E))ᵀ * (A.H n).map (cj E) = _ at h
    rwa [hH'] at h
  refine ⟨herm_N _ _ hH' hT (A.det_ne n) hsym, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine mul_ne_zero ?_ ?_
    · have hu : IsUnit (mat S ↑B.β) := B.β.isUnit
      exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    · rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact inv_ne_zero (A.det_ne n)
  · intro τ x hx
    set v := InfinitePlace.mk τ with hvdef
    set ε : ℝ := if v = InfinitePlace.mk A.τ₀ then 1 else -1 with hεdef
    have hpos : ∀ y : Fin n → ℂ, y ≠ 0 → 0 < ε *
        (star y ⬝ᵥ ((((A.H n).map v.embedding)ᵀ * (mat S ↑(B.β⁻¹)).map v.embedding) *ᵥ y)).re := by
      intro y hy
      have hp := B.posR v y hy
      have hsig : sigPosH (S.G.gram_herm v) = sigPos (A.herm n) v.embedding := rfl
      rw [hsig] at hp
      have hme : InfinitePlace.mk v.embedding = v := InfinitePlace.mk_embedding v
      by_cases hv : v = InfinitePlace.mk A.τ₀
      · have h1 := ((S.sig v.embedding).1 (by rw [hme]; exact hv)).1
        rw [hεdef, if_pos hv, one_mul]
        exact hp.1 h1
      · have h0 := ((S.sig v.embedding).2 (by rw [hme]; exact hv)).1
        rw [hεdef, if_neg hv, neg_one_mul, neg_pos]
        exact hp.2 (by rw [h0]; exact zero_ne_one)
    have h1 : (((A.H n).map v.embedding)ᵀ * (mat S ↑(B.β⁻¹)).map v.embedding) *
        (mat S ↑B.β * (A.H n)⁻¹).map v.embedding = 1 := by
      have hb : mat S ↑(B.β⁻¹) * mat S ↑B.β = 1 := B.β.inv_mul
      have h2 : A.H n * mat S ↑(B.β⁻¹) * (mat S ↑B.β * (A.H n)⁻¹) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (mat S ↑(B.β⁻¹)), hb, Matrix.one_mul,
          Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (A.det_ne n))]
      rw [← Matrix.transpose_map, hT, ← Matrix.map_mul, ← Matrix.map_mul, h2,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hM := def_of_inv _ _ h1 ε hpos
    rcases InfinitePlace.embedding_mk_eq τ with he | he
    · have he' : v.embedding = τ := he
      rw [he'] at hM
      exact hM x hx
    · have he' : v.embedding = ComplexEmbedding.conjugate τ := he
      rw [he'] at hM
      have hc := def_conj _ ε hM x hx
      have hcc : ((mat S ↑B.β * (A.H n)⁻¹).map (ComplexEmbedding.conjugate τ)).map (starRingEnd ℂ) =
          (mat S ↑B.β * (A.H n)⁻¹).map τ := by
        ext i j
        simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
      rwa [hcc] at hc
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PHenselV
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pHenselV :
    HenselV := by
  intro F _ _ v f a₀ hf h0 h1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := {}
  haveI := IsAdicComplete.henselianRing (v.adicCompletionIntegers F)
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
  obtain ⟨a, ha, hm⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) f hf a₀
    (by rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact h0)
    (h1.map (Ideal.Quotient.mk _))
  refine ⟨a, ha, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  exact hm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PZUnitNorm
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pZUnitNorm :
    PadicUnitNorm → ZUnitNorm := by
  intro hP v D hv u hu
  haveI : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  have hint : ∀ z : v.adicCompletion ℚ, Valued.v z ≤ 1 →
      ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v z‖ ≤ 1 := by
    intro z hz
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn v).mapsTo
      ((HeightOneSpectrum.mem_adicCompletionIntegers ℤ ℚ v).2 hz)
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  have hn : ‖Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u‖ = 1 := by
    apply le_antisymm (hint u hu.le)
    have h1 := hint u⁻¹ (by rw [map_inv₀, hu, inv_one])
    rw [map_inv₀, norm_inv] at h1
    have hne : Rat.HeightOneSpectrum.adicCompletion.padicEquiv v u ≠ 0 := fun h =>
      hu0 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).injective
        (h.trans (map_zero _).symm))
    exact (inv_le_one₀ (norm_pos_iff.2 hne)).1 h1
  have hdiv : ¬ ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ) ∣ 2 * D := by
    intro hd
    apply hv
    have hm : 2 * D ∈ Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ)} :=
      Ideal.mem_span_singleton.2 hd
    rw [Rat.HeightOneSpectrum.span_natGenerator, Ideal.mem_map_of_equiv] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    have hid : Rat.IsIntegralClosure.intEquiv ℤ x = x := by
      simpa using eq_intCast (Rat.IsIntegralClosure.intEquiv ℤ : ℤ →+* ℤ) x
    rw [hid] at hxe
    rw [← hxe]
    exact hx
  obtain ⟨x, y, hxy⟩ := hP _ D hdiv _ hn
  refine ⟨(Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm x,
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm y, ?_⟩
  have h2 := congrArg (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).symm hxy
  simpa using h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocRoot
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma unit_add_nonunit {R : Type*} [CommRing R] [IsLocalRing R] {x y : R}
    (hx : IsUnit x) (hy : ¬ IsUnit y) : IsUnit (x + y) := by
  by_contra h
  have hy' : ¬ IsUnit (-y) := by rwa [IsUnit.neg_iff]
  have := IsLocalRing.nonunits_add h hy'
  rw [add_neg_cancel_right] at this
  exact this hx

private lemma natCast_not_isUnit (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (q : ℕ) (hq : (q : 𝓞 F) ∈ v.asIdeal) :
    ¬ IsUnit (q : v.adicCompletionIntegers F) := by
  intro hu
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hu
  have h1 : v.intValuation (q : 𝓞 F) < 1 := (v.intValuation_lt_one_iff_mem _).2 hq
  have h2 : ((q : v.adicCompletionIntegers F) : v.adicCompletion F) = (q : v.adicCompletion F) := by
    simp
  have h3 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (q : 𝓞 F)
  have h4 := HeightOneSpectrum.valuation_of_algebraMap (K := F) v (q : 𝓞 F)
  push_cast at h3 h4
  rw [h2, h3, h4] at hu
  exact (ne_of_lt h1) hu

theorem UpperTheory.Gal.G1.pLocRoot :
    HenselV → LocRoot := by
  intro hH F _ _ v tr nm q hqp hqv hdisc hr
  obtain ⟨r, k, hk⟩ := hr
  have hq : ¬ IsUnit (q : v.adicCompletionIntegers F) := natCast_not_isUnit F v q hqv
  have hqi : Irreducible (q : ℤ) := (Nat.prime_iff_prime_int.mp hqp).irreducible
  have hint : ∀ n : ℤ, ¬ (q : ℤ) ∣ n → IsUnit (n : v.adicCompletionIntegers F) := by
    intro n hn
    obtain ⟨a, b, hab⟩ := (hqi.coprime_iff_not_dvd).2 hn
    have hab' : ((a : v.adicCompletionIntegers F)) * (q : v.adicCompletionIntegers F)
        + (b : v.adicCompletionIntegers F) * (n : v.adicCompletionIntegers F) = 1 := by
      have := congrArg (fun z : ℤ => (z : v.adicCompletionIntegers F)) hab
      push_cast at this
      exact this
    have hnu : ¬ IsUnit (-((a : v.adicCompletionIntegers F) * (q : v.adicCompletionIntegers F))) := by
      rw [IsUnit.neg_iff]
      exact fun h => hq (isUnit_of_mul_isUnit_right h)
    have hbn := unit_add_nonunit isUnit_one hnu
    rw [← hab', add_neg_cancel_comm] at hbn
    exact isUnit_of_mul_isUnit_right hbn
  have hder : ¬ (q : ℤ) ∣ 2 * r - tr := by
    intro h
    apply hdisc
    have e : tr ^ 2 - 4 * nm = (2 * r - tr) ^ 2 - 4 * (r ^ 2 - tr * r + nm) := by ring
    rw [e, hk]
    exact dvd_sub (dvd_pow h two_ne_zero) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  set f : Polynomial (v.adicCompletionIntegers F) :=
    Polynomial.X ^ 2 - Polynomial.C (tr : v.adicCompletionIntegers F) * Polynomial.X
      + Polynomial.C (nm : v.adicCompletionIntegers F) with hf
  have hmon : f.Monic := by
    rw [hf]
    monicity!
  have hev : ∀ x, f.eval x = x ^ 2 - (tr : v.adicCompletionIntegers F) * x + nm := by
    intro x
    simp [hf]
  have hdev : ∀ x, (Polynomial.derivative f).eval x = 2 * x - (tr : v.adicCompletionIntegers F) := by
    intro x
    simp only [hf, Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_C_mul_X, Polynomial.derivative_C, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_zero]
    push_cast
    ring
  have h0 : ¬ IsUnit (f.eval (r : v.adicCompletionIntegers F)) := by
    rw [hev]
    have := congrArg (fun z : ℤ => (z : v.adicCompletionIntegers F)) hk
    push_cast at this
    rw [this]
    exact fun h => hq (isUnit_of_mul_isUnit_left h)
  have h1 : IsUnit ((Polynomial.derivative f).eval (r : v.adicCompletionIntegers F)) := by
    rw [hdev]
    have := hint _ hder
    push_cast at this
    exact this
  obtain ⟨ρ, hρ, hρr⟩ := hH F v f r hmon h0 h1
  refine ⟨ρ, ?_, ?_⟩
  · rw [hev] at hρ
    exact hρ
  · have h2 : ¬ IsUnit (2 * (ρ - (r : v.adicCompletionIntegers F))) :=
      fun h => hρr (isUnit_of_mul_isUnit_right h)
    have h3 := unit_add_nonunit ((hdev _) ▸ h1) h2
    have e : 2 * (r : v.adicCompletionIntegers F) - tr + 2 * (ρ - r) = 2 * ρ - tr := by ring
    rw [e] at h3
    exact h3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocUnit
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem field_rep (k : Type) [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (d s : k) (hd : d ≠ 0) :
    ∃ a b : k, a ^ 2 - d * b ^ 2 = s := by
  classical
  haveI := Fintype.ofFinite k
  have hc : ringChar k ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := k)
    rw [h] at this
    exact_mod_cast this
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2 - Polynomial.C s) (g := Polynomial.C (-d) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_sub_C (by norm_num) s)
    (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr hd))
    (FiniteField.odd_card_of_char_ne_two hc)
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination hab

private theorem two_ne_zero_residueField_of_isUnit_two (R : Type) [CommRing R] [IsLocalRing R] (h2 : IsUnit (2 : R)) :
    (2 : IsLocalRing.ResidueField R) ≠ 0 := by
  have := (IsLocalRing.residue_ne_zero_iff_isUnit (2 : R)).2 h2
  rwa [map_ofNat] at this

private theorem local_rep (R : Type) [CommRing R] [IsLocalRing R]
    [Finite (IsLocalRing.ResidueField R)]
    (hens : ∀ (f : Polynomial R) (a₀ : R), f.Monic → ¬ IsUnit (f.eval a₀) →
      IsUnit (f.derivative.eval a₀) → ∃ a, f.eval a = 0)
    (h2 : IsUnit (2 : R)) (D u : R) (hD : IsUnit D) (hu : IsUnit u) :
    ∃ X Y : R, X ^ 2 - D * Y ^ 2 = u := by
  classical
  have h2k : (2 : IsLocalRing.ResidueField R) ≠ 0 := two_ne_zero_residueField_of_isUnit_two R h2
  have hDk : IsLocalRing.residue R D ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit D).2 hD
  have huk : IsLocalRing.residue R u ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit u).2 hu
  obtain ⟨a', b', hab'⟩ := field_rep _ h2k (IsLocalRing.residue R D) (IsLocalRing.residue R u) hDk
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a'
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective b'
  have hres : IsLocalRing.residue R (a ^ 2 - D * b ^ 2 - u) = 0 := by
    simp only [map_sub, map_mul, map_pow, hab', sub_self]
  have hnu : ¬ IsUnit (a ^ 2 - D * b ^ 2 - u) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, not_not]
    exact hres
  by_cases ha : IsUnit a
  · obtain ⟨X, hX⟩ := hens (Polynomial.X ^ 2 - Polynomial.C (u + D * b ^ 2)) a
      (Polynomial.monic_X_pow_sub_C _ (by norm_num))
      (by
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        intro hh
        apply hnu
        convert hh using 1
        ring)
      (by
        simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
          sub_zero, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        convert h2.mul ha using 1
        norm_num)
    refine ⟨X, b, ?_⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hX
    linear_combination hX
  · have hb : IsUnit b := by
      by_contra hb
      apply huk
      have ha0 : IsLocalRing.residue R a = 0 :=
        (IsLocalRing.residue_eq_zero_iff a).2 ((IsLocalRing.mem_maximalIdeal a).2 ha)
      have hb0 : IsLocalRing.residue R b = 0 :=
        (IsLocalRing.residue_eq_zero_iff b).2 ((IsLocalRing.mem_maximalIdeal b).2 hb)
      rw [← hab', ha0, hb0]
      ring
    have hDi : D * ↑hD.unit⁻¹ = 1 := hD.mul_val_inv
    obtain ⟨Y, hY⟩ := hens (Polynomial.X ^ 2 - Polynomial.C (↑hD.unit⁻¹ * (a ^ 2 - u))) b
      (Polynomial.monic_X_pow_sub_C _ (by norm_num))
      (by
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        intro hh
        apply hnu
        have e : a ^ 2 - D * b ^ 2 - u = -D * (b ^ 2 - ↑hD.unit⁻¹ * (a ^ 2 - u)) := by
          linear_combination (-(a ^ 2 - u)) * hDi
        rw [e]
        exact hD.neg.mul hh)
      (by
        simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
          sub_zero, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        convert h2.mul hb using 1
        norm_num)
    refine ⟨a, Y, ?_⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hY
    linear_combination (-D) * hY + (-(a ^ 2 - u)) * hDi

theorem UpperTheory.Gal.G1.pLocUnit :
    HenselV → LocUnit := by
  intro hH F _ _ v tr nm hv u hu
  have hunit : IsUnit (((2 * (tr ^ 2 - 4 * nm) : ℤ) : HeightOneSpectrum.adicCompletionIntegers F v)) := by
    have h := (GroundTheory.Global.algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff (K := F) v
      ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F)).not.2 hv
    rw [map_intCast] at h
    by_contra hc
    exact h ((IsLocalRing.mem_maximalIdeal _).2 hc)
  push_cast at hunit
  have h2 : IsUnit (2 : HeightOneSpectrum.adicCompletionIntegers F v) := isUnit_of_mul_isUnit_left hunit
  have hΔ := isUnit_of_mul_isUnit_right hunit
  have h4u : IsUnit (4 * u) := by
    have h4 := h2.mul h2
    norm_num at h4
    exact h4.mul hu
  obtain ⟨X, Y, hXY⟩ := local_rep _ (fun f a₀ hf hn hd => (hH F v f a₀ hf hn hd).imp fun a ha => ha.1)
    h2 _ (4 * u) hΔ h4u
  have hi : (2 : HeightOneSpectrum.adicCompletionIntegers F v) * ↑h2.unit⁻¹ = 1 := h2.mul_val_inv
  refine ⟨↑h2.unit⁻¹ * (X - tr * Y), Y, ?_⟩
  have ha : 2 * (↑h2.unit⁻¹ * (X - tr * Y)) = X - tr * Y := by rw [← mul_assoc, hi, one_mul]
  apply (h2.mul h2).mul_left_cancel
  unfold qf
  linear_combination (2 * (↑h2.unit⁻¹ * (X - tr * Y)) + X - tr * Y + 2 * tr * Y) * ha + hXY
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadicSqFin
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private lemma pow_neg_three_lt_two_norm_sq (q : ℕ) [hq : Fact q.Prime] :
    (q : ℝ) ^ (-3 : ℤ) < ‖(2 : ℤ_[q])‖ ^ 2 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  by_cases h : q = 2
  · subst h
    have h2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ) ^ (-1 : ℤ) := by
      have := PadicInt.norm_p_pow (p := 2) 1
      simpa using this
    rw [h2]
    norm_num
  · have h1 : ‖(2 : ℤ_[q])‖ = 1 := by
      apply le_antisymm (PadicInt.norm_le_one _)
      by_contra hlt
      push_neg at hlt
      have hd := (PadicInt.norm_int_lt_one_iff_dvd (p := q) 2).1 (by exact_mod_cast hlt)
      have hd' : q ∣ 2 := by exact_mod_cast hd
      exact h ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 hd')
    rw [h1, one_pow, _root_.zpow_neg]
    have hlt : (1 : ℝ) < (q : ℝ) ^ (3 : ℤ) := one_lt_zpow₀ (by linarith) (by norm_num)
    exact inv_lt_one_of_one_lt₀ hlt

private lemma sq_of_close (q : ℕ) [hq : Fact q.Prime] (z : ℤ_[q])
    (hz : ‖(1 : ℤ_[q]) - z‖ < ‖(2 : ℤ_[q])‖ ^ 2) : ∃ x : ℤ_[q], x ^ 2 = z := by
  have hn : ‖Polynomial.aeval (1 : ℤ_[q]) (Polynomial.X ^ 2 - Polynomial.C z : Polynomial ℤ_[q])‖ <
      ‖Polynomial.aeval (1 : ℤ_[q])
        (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C z : Polynomial ℤ_[q]))‖ ^ 2 := by
    simpa [Polynomial.derivative_X_pow, one_add_one_eq_two] using hz
  obtain ⟨x, hx, -⟩ := hensels_lemma hn
  refine ⟨x, ?_⟩
  simpa [sub_eq_zero] using hx

theorem UpperTheory.Gal.G1.pPadicSqFin :
    PadicSqFin := by
  intro q hq
  haveI : NeZero (q ^ 3) := ⟨pow_ne_zero 3 hq.out.ne_zero⟩
  refine ⟨Fintype.card (ZMod (q ^ 3)), fun u => Fintype.equivFin (ZMod (q ^ 3))
    (if h : ‖u‖ ≤ 1 then PadicInt.toZModPow 3 ⟨u, h⟩ else 0), ?_⟩
  intro u u' hu hu' hk
  simp only [dif_pos hu.le, dif_pos hu'.le, (Fintype.equivFin _).injective.eq_iff] at hk
  obtain ⟨a, ha⟩ : ∃ a : ℤ_[q], (a : ℚ_[q]) = u ∧ PadicInt.toZModPow 3 a =
      PadicInt.toZModPow 3 ⟨u, hu.le⟩ := ⟨⟨u, hu.le⟩, rfl, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ_[q], (b : ℚ_[q]) = u' ∧ PadicInt.toZModPow 3 b =
      PadicInt.toZModPow 3 ⟨u', hu'.le⟩ := ⟨⟨u', hu'.le⟩, rfl, rfl⟩
  have hmem : b - a ∈ RingHom.ker (PadicInt.toZModPow (p := q) 3) := by
    rw [RingHom.sub_mem_ker_iff, ha.2, hb.2]
    exact hk.symm
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hd : ‖u' - u‖ ≤ (q : ℝ) ^ (-3 : ℤ) := by
    have h1 : ‖b - a‖ ≤ (q : ℝ) ^ (-((3 : ℕ) : ℤ)) := by
      rw [hc, norm_mul, PadicInt.norm_p_pow]
      have hc1 := PadicInt.norm_le_one c
      have hpos : (0 : ℝ) ≤ (q : ℝ) ^ (-((3 : ℕ) : ℤ)) := by positivity
      calc _ ≤ (q : ℝ) ^ (-((3 : ℕ) : ℤ)) * 1 := mul_le_mul_of_nonneg_left hc1 hpos
        _ = _ := mul_one _
    rw [PadicInt.norm_def, PadicInt.coe_sub, ha.1, hb.1] at h1
    simpa using h1
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hz : ‖u' / u‖ ≤ 1 := by
    rw [norm_div, hu, hu']
    simp
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[q], (w : ℚ_[q]) = u' / u := ⟨⟨u' / u, hz⟩, rfl⟩
  obtain ⟨x, hx⟩ := sq_of_close q w (by
    have e : ‖(1 : ℤ_[q]) - w‖ = ‖u' - u‖ := by
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, hw,
        show (1 : ℚ_[q]) - u' / u = (u - u') / u by field_simp, norm_div, hu, div_one,
        norm_sub_rev]
    rw [e]
    exact lt_of_le_of_lt hd (pow_neg_three_lt_two_norm_sq q))
  refine ⟨x, ?_⟩
  have hx' : (x : ℚ_[q]) ^ 2 = u' / u := by
    rw [← hw, ← hx]
    simp
  rw [hx']
  field_simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PUnitCls
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pUnitCls :
    Scale → ZUnitNorm → ZSqFin → UnitCls := by
  intro hScale hNorm hSq p D hD
  choose sc hsc0 hsc using hScale p
  choose m κ hκ using hSq
  have hfin : {v : HeightOneSpectrum ℤ | (2 * D : ℤ) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {(2 * D : ℤ)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      omega
    refine (Ideal.finite_factors h0).subset ?_
    intro v hv
    exact Ideal.dvd_span_singleton.2 hv
  haveI : Finite {v : HeightOneSpectrum ℤ | (2 * D : ℤ) ∈ v.asIdeal} := hfin.to_subtype
  refine ⟨(v : {v : HeightOneSpectrum ℤ | (2 * D : ℤ) ∈ v.asIdeal}) → Option (Fin (m v.1)),
    inferInstance, fun t v => if h : (v.1 : HeightOneSpectrum ℤ).asIdeal ≠ Ideal.span {(p : ℤ)}
      then some (κ v.1 (AfP.eval (⟨v.1, h⟩ : AwayP p) (t : AfP p) /
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc t)))
      else none, ?_⟩
  intro t t' hk
  refine ⟨sc t' / sc t, div_pos (hsc0 t') (hsc0 t), fun v => ?_⟩
  have hunit : ∀ r : (AfP p)ˣ, AfP.eval v (r : AfP p) ≠ 0 := by
    intro r
    have h1 : AfP.eval v (r : AfP p) * AfP.eval v ((r⁻¹ : (AfP p)ˣ) : AfP p) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    exact left_ne_zero_of_mul_eq_one h1
  have hsne : ∀ r : (AfP p)ˣ,
      algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc r) ≠ 0 :=
    fun r => (map_ne_zero _).2 (hsc0 r).ne'
  have hval : ∀ r : (AfP p)ˣ, Valued.v (AfP.eval v (r : AfP p) /
      algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc r)) = 1 := by
    intro r
    rw [map_div₀, hsc r v, div_self]
    exact (Valuation.ne_zero_iff _).2 (hsne r)
  suffices hs : ∃ x y : HeightOneSpectrum.adicCompletion ℚ v.1,
      AfP.eval v (t' : AfP p) / algebraMap ℚ _ (sc t') =
        AfP.eval v (t : AfP p) / algebraMap ℚ _ (sc t) * (x ^ 2 - (D : _) * y ^ 2) by
    obtain ⟨x, y, hxy⟩ := hs
    refine ⟨x, y, ?_⟩
    rw [map_div₀]
    have e := hsne t
    have e' := hsne t'
    rw [div_eq_iff e'] at hxy
    rw [hxy]
    field_simp
  by_cases h2 : (2 * D : ℤ) ∈ v.1.asIdeal
  · have hk' := congrFun hk ⟨v.1, h2⟩
    dsimp only at hk'
    rw [dite_eq_left v.2, dite_eq_left v.2] at hk'
    have hk'' := Option.some.inj hk'
    obtain ⟨z, hz⟩ := hκ v.1 _ _ (hval t) (hval t') hk''
    refine ⟨z, 0, ?_⟩
    rw [hz]
    ring
  · have hne : AfP.eval v (t : AfP p) /
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc t) ≠ 0 :=
      div_ne_zero (hunit t) (hsne t)
    have hv1 : Valued.v ((AfP.eval v (t' : AfP p) /
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc t')) /
        (AfP.eval v (t : AfP p) /
        algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ v.1) (sc t))) = 1 := by
      rw [map_div₀, hval t, hval t', div_one]
    obtain ⟨x, y, hxy⟩ := hNorm v.1 D h2 _ hv1
    refine ⟨x, y, ?_⟩
    rw [← hxy, mul_div_assoc', mul_div_cancel_left₀ _ hne]
end

namespace UpperTheory.Gal.G1

theorem LocFour_holds : LocFour := pLocFour
theorem HenselV_holds : HenselV := pHenselV
theorem SplitRep_holds : SplitRep := pSplitRep
theorem BlockMat_holds : BlockMat := pBlockMat
theorem PadMap_holds : PadMap := pPadMap
theorem Scale_holds : Scale := pScale
theorem PadicUnitNorm_holds : PadicUnitNorm := pPadicUnitNorm
theorem PadicSqFin_holds : PadicSqFin := pPadicSqFin
theorem TrivMat_holds : TrivMat := pTrivMat
theorem CongrScale_holds : CongrScale := pCongrScale
theorem SplitCongr_holds : SplitCongr := pSplitCongr
theorem InfCongr_holds : InfCongr := pInfCongr
theorem DefSign_holds : DefSign := pDefSign
theorem RelOf_holds : RelOf := pRelOf
theorem LocUnit_holds : LocUnit := pLocUnit HenselV_holds
theorem LocRoot_holds : LocRoot := pLocRoot HenselV_holds
theorem ZUnitNorm_holds : ZUnitNorm := pZUnitNorm PadicUnitNorm_holds
theorem ZSqFin_holds : ZSqFin := pZSqFin PadicSqFin_holds
theorem AdFour_holds : AdFour := pAdFour LocFour_holds LocUnit_holds LocRoot_holds SplitRep_holds
theorem UnitCls_holds : UnitCls := pUnitCls Scale_holds ZUnitNorm_holds ZSqFin_holds
theorem FinCongr_holds : FinCongr := pFinCongr PadMap_holds LocRoot_holds TrivMat_holds CongrScale_holds SplitCongr_holds DefSign_holds
theorem NormTwo_holds : NormTwo := pNormTwo AdFour_holds
theorem FinCls_holds : FinCls := pFinCls UnitCls_holds FinCongr_holds InfCongr_holds DefSign_holds RelOf_holds
theorem IsoEx_holds : IsoEx := pIsoEx NormTwo_holds BlockMat_holds

end UpperTheory.Gal.G1
