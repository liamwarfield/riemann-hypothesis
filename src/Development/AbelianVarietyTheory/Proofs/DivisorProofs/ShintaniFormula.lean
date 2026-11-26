module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflection
public import GroundTheory.AutomorphicForms.MacdonaldHecke
public import GroundTheory.GlobalFields.CompletionAtPlace.Inertia

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMulSchurPolynomialJacobiTrudi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmEqSumFilterPerm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmEqSumFilterPerm
open scoped Classical

namespace GlobalTheory.JSW

theorem esymm_eq_sum_filter_perm (n j : ℕ) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.esymm (Fin n) ℤ j =
      ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
        ∏ k ∈ J, (MvPolynomial.X (σ k) : MvPolynomial (Fin n) ℤ) := by
  rw [← MvPolynomial.rename_esymm (Fin n) ℤ j σ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.rename_X,
    Finset.powersetCard_eq_filter, Finset.powerset_univ]

theorem esymm_mul_alternant (n : ℕ) (m : Fin n → ℕ) (j : ℕ) :
    MvPolynomial.esymm (Fin n) ℤ j *
        Matrix.det (Matrix.of fun i k : Fin n =>
          (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m k) =
      ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
        Matrix.det (Matrix.of fun i k : Fin n =>
          (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (m k + if k ∈ J then 1 else 0)) := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [esymm_eq_sum_filter_perm n j σ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [mul_smul_comm]
  congr 1
  simp only [pow_add, Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero,
    Finset.prod_ite_mem, Finset.univ_inter]
  ring

end GlobalTheory.JSW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmEqSumFilterPermStatement
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.esymm_mul_det_pow_eq_sum_det_shifted : ∀ (n : ℕ) (m : Fin n → ℕ) (j : ℕ), MvPolynomial.esymm (Fin n) ℤ j * Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m k) = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (m k + if k ∈ J then 1 else 0)) := by
  first | exact @GlobalTheory.JSW.esymm_mul_alternant | exact GlobalTheory.JSW.esymm_mul_alternant | (intros; apply GlobalTheory.JSW.esymm_mul_alternant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMulSchurPolynomialJacobiTrudi
open scoped Classical

open MvPolynomial in
theorem GlobalTheory.JSW.PieriDeterminant.vdm_ne (n : ℕ) : Matrix.det (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) ≠ 0 := by
  have h : (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin n) ℤ))).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply, id, Fin.revPerm_apply, Fin.val_rev]
    rw [show n - 1 - (j : ℕ) = n - ((j : ℕ) + 1) by omega]
  rw [h, Matrix.det_permute']
  refine mul_ne_zero (by simp [Units.ne_zero]) ?_
  rw [Matrix.det_vandermonde_ne_zero_iff]
  exact MvPolynomial.X_injective

namespace GlobalTheory.JSW.PieriDeterminant

theorem adj {n : ℕ} (l : Fin n → ℕ) (hl : Antitone l) (J : Finset (Fin n)) :
    ∀ d : ℕ, ∀ a b : Fin n, (b : ℕ) = a + d + 1 → l a = l b → a ∉ J → b ∈ J →
      ∃ a' b' : Fin n, (b' : ℕ) = a' + 1 ∧ l a' = l b' ∧ a' ∉ J ∧ b' ∈ J := by
  intro d
  induction d with
  | zero => intro a b h1 h2 h3 h4; exact ⟨a, b, by omega, h2, h3, h4⟩
  | succ d ih =>
    intro a b h1 h2 h3 h4
    have hc : (a : ℕ) + 1 < n := by have := b.isLt; omega
    let c : Fin n := ⟨a + 1, hc⟩
    have hac : a ≤ c := by show (a : ℕ) ≤ a + 1; omega
    have hcb : c ≤ b := by show (a : ℕ) + 1 ≤ b; omega
    have hlc : l c = l a := le_antisymm (hl hac) (h2 ▸ hl hcb)
    by_cases hcJ : c ∈ J
    · exact ⟨a, c, rfl, hlc.symm, h3, hcJ⟩
    · exact ih c b (by show (b : ℕ) = a + 1 + d + 1; omega) (hlc.trans h2) hcJ h4

theorem det_zero {n : ℕ} (l : Fin n → ℕ) (hl : Antitone l) (J : Finset (Fin n))
    (hJ : ¬ Antitone (l + (fun i => if i ∈ J then 1 else 0))) :
    Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
      ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) = 0 := by
  obtain ⟨a, b, hab, hlt⟩ : ∃ a b : Fin n, a ≤ b ∧ ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) a <
      ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) b := by
    simp only [Antitone, not_forall, not_le] at hJ
    obtain ⟨a, b, h1, h2⟩ := hJ; exact ⟨a, b, h1, h2⟩
  simp only [Pi.add_apply] at hlt
  have hla := hl hab
  have hA : a ∉ J := by intro h; simp only [h, if_true] at hlt; split_ifs at hlt <;> omega
  have hB : b ∈ J := by by_contra h; simp only [h, if_false] at hlt; split_ifs at hlt <;> omega
  have hE : l a = l b := by simp only [hA, hB, if_true, if_false] at hlt; omega
  have hne : a ≠ b := by rintro rfl; exact hA hB
  obtain ⟨a', b', h1, h2, h3, h4⟩ :=
    adj l hl J ((b : ℕ) - a - 1) a b (by have : (a : ℕ) < b := lt_of_le_of_ne hab (fun h => hne (Fin.ext h)); omega) hE hA hB
  refine Matrix.det_zero_of_column_eq (i := a') (j := b') (fun h => by rw [h] at h1; omega) (fun i => ?_)
  simp only [Matrix.of_apply, h3, h4, if_true, if_false]
  congr 1
  have := b'.isLt
  omega

end GlobalTheory.JSW.PieriDeterminant

open MvPolynomial in
theorem GlobalTheory.JSW.esymm_mul_schur : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → ∀ j ≤ n, MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j ∧ Antitone (l + (fun i => if i ∈ J then 1 else 0))), GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) := by
  intro n l hl j _
  apply mul_right_cancel₀ (GlobalTheory.JSW.PieriDeterminant.vdm_ne n)
  have h1 := GlobalTheory.T.esymm_mul_det_pow_eq_sum_det_shifted n (fun k => l k + n - 1 - k) j
  beta_reduce at h1
  calc MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l * _
      = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
          Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
            ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) := by
        rw [mul_assoc, GlobalTheory.T.schur_mul_vandermonde_det_eq_det n l hl, h1]
    _ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter
          (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))),
          Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
            ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) := by
        refine (Finset.sum_filter_of_ne fun J _ hJ => ?_).symm
        by_contra h
        exact hJ (GlobalTheory.JSW.PieriDeterminant.det_zero l hl J h)
    _ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter
          (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))),
          GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) *
            Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        rw [GlobalTheory.T.schur_mul_vandermonde_det_eq_det n _ (Finset.mem_filter.1 hJ).2]
        have e : ∀ k : Fin n, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) k + n - 1 - (k : ℕ) =
            (l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0 := by
          intro k; have := k.isLt; simp only [Pi.add_apply]; split_ifs <;> omega
        simp only [e]
    _ = _ := by rw [Finset.filter_filter, Finset.sum_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMulSchurPolynomialJacobiTrudiStatement
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.esymm_mul_schurPolynomialJacobiTrudi : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → ∀ j ≤ n, MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j ∧ Antitone (l + (fun i => if i ∈ J then 1 else 0))), GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) := by
  first | exact @GlobalTheory.JSW.esymm_mul_schur | exact GlobalTheory.JSW.esymm_mul_schur | (intros; apply GlobalTheory.JSW.esymm_mul_schur <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWhittakerTorusHeckeRecursion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWhittakerTorusHeckeRecursion
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

noncomputable section

namespace GlobalTheory.WhittakerRecursion

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
open scoped ValuativeRel

theorem lamS_perm {n : ℕ} (S T : Finset (Fin n)) (h : S.card = T.card) :
    ∃ σ : Equiv.Perm (Fin n), Spherical.lamS T ∘ σ = Spherical.lamS S := by
  classical
  let e : {x // x ∈ S} ≃ {x // x ∈ T} := Finset.equivOfCardEq h
  refine ⟨e.extendSubtype, funext fun i => ?_⟩
  by_cases hi : i ∈ S
  · have := Equiv.extendSubtype_mem e i hi
    simp [Spherical.lamS, hi, this]
  · have := Equiv.extendSubtype_not_mem e i hi
    simp [Spherical.lamS, hi, this]

theorem mem_minusculeSet_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) F) :
    g ∈ Spherical.minusculeSet F n r ↔ ∃ a ∈ GLnLocal.integralGL F n, ∃ b ∈ GLnLocal.integralGL F n,
      (g : Matrix (Fin n) (Fin n) F) = (a : Matrix (Fin n) (Fin n) F) *
        Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r * (b : Matrix (Fin n) (Fin n) F) := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter fun i => i.val < r
  have hT : T.card = r := by
    simp [T, Fin.card_filter_val_lt, hr]
  have hD : ((Iwasawa.torusPow F n (Spherical.lamS T) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Formalism.UG.diagJ n (GLnLocal.uniformizer F : F) r := by
    rw [Iwasawa.coe_torusPow, Formalism.UG.diagJ]
    congr 1
    funext i
    by_cases hi : i.val < r <;> simp [Spherical.lamS, T, hi]
  have hU : ∀ (S : Finset (Fin n)) c, Spherical.unipC (F := F) S c ∈ GLnLocal.integralGL F n := by
    intro S c
    have := (Spherical.torusPow_conj_unipC_mem (l := 0) antitone_const S c).2
    have h0 : Iwasawa.torusPow F n 0 = 1 := Units.ext (by simp [Iwasawa.coe_torusPow])
    simpa [h0] using this
  rw [← hD]
  constructor
  · intro hg
    obtain ⟨S, hS, c, hc⟩ := Spherical.exists_gMat hg
    have hk := QuotientGroup.eq.1 hc
    obtain ⟨σ, hσ⟩ := lamS_perm S T (hS.trans hT.symm)
    have hp := GLnLocal.permGL_mem_integralGL F n σ
    refine ⟨_, mul_mem (hU S c) (inv_mem hp), _, mul_mem hp hk, ?_⟩
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    have h1 := Spherical.permGL_conj_torusPow (F := F) σ (Spherical.lamS T)
    rw [hσ] at h1
    rw [Spherical.gMat, ← h1]
    group
  · rintro ⟨a, ha, b, hb, e⟩
    rw [← Units.val_mul, ← Units.val_mul] at e
    have e' := Units.ext e
    have h0 := Spherical.gMat_mem_minusculeSet (F := F) T (fun _ => 0)
    rw [hT] at h0
    have := Spherical.mul_mem_minusculeSet h0 (mul_mem ha (inv_mem (hU T fun _ => 0))) hb
    rw [e']
    convert this using 1
    rw [Spherical.gMat]
    group

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem finsum_minuscule {f : GL (Fin n) F → ℂ} (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hN : ∀ u ∈ unipotent F n ⊓ integralGL F n, ∀ g, f (u * g) = f g) {l : Fin n → ℤ} (hl : Antitone l) (r : ℕ) :
    ∑ᶠ x : GL (Fin n) F ⧸ integralGL F n,
        (minusculeSet F n r).indicator (fun _ => (1 : ℂ)) x.out • f (torusPow F n l * x.out) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, (kappa F S : ℂ) * f (torusPow F n (l + lamS S)) := by
  letI : Fintype 𝓀[F] := Fintype.ofFinite _
  letI : MeasurableSpace (GL (Fin n) F) := borel _
  haveI : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  set Cs : Finset (GL (Fin n) F ⧸ integralGL F n) := (Finset.univ.powersetCard r).biUnion
    fun S => Finset.univ.image fun c : Pairs S → 𝓀[F] => (QuotientGroup.mk (gMat S c) : _)
  rw [finsum_eq_sum_of_support_subset (s := Cs)]
  · rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun S hS => ?_
      have hSr := (Finset.mem_powersetCard.1 hS).2
      rw [Finset.sum_image fun c _ c' _ h => gMat_injective S h]
      refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) (sum_gMat_torusPow hN hl S)
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (integralGL F n) (gMat S c)
      have hm := mul_mem_minusculeSet (hSr ▸ gMat_mem_minusculeSet (F := F) S c) (one_mem _) k.2
      rw [one_mul] at hm
      rw [hk, Set.indicator_of_mem hm, one_smul, ← mul_assoc, hf _ k k.2]
    · intro S _ S' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨c', -, hc'⟩ := Finset.mem_image.1 hx'
      have := congrArg (fun x : GL (Fin n) F ⧸ integralGL F n => iwasawaExponent F n x.out) hc'
      simp only [iwasawaExponent_out, iwasawaExponent_gMat] at this
      exact hne (lamS_injective this).symm
  · intro x hx
    have hm : x.out ∈ minusculeSet F n r := by
      by_contra hm
      apply hx
      simp only [Set.indicator_of_notMem hm, zero_smul]
    obtain ⟨S, hS, c, hc⟩ := exists_gMat hm
    rw [QuotientGroup.out_eq'] at hc
    exact Finset.mem_biUnion.2 ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS⟩,
      Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc⟩⟩

theorem sqrtQ_zpow (m : ℤ) : sqrtQ F ^ m = (qF F : ℂ) ^ ((m : ℂ) / 2) := by
  rw [div_eq_inv_mul, Complex.cpow_mul_int]
  congr 1
  rw [sqrtQ, Real.coe_sqrt, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
  simp

theorem cpow_eq_sqrtQ (m : Fin n → ℕ) :
    (qF F : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * ((m k : ℕ) : ℂ))) / 2) =
      sqrtQ F ^ rhoPair (fun i => (m i : ℤ)) := by
  rw [sqrtQ_zpow, rhoPair]
  push_cast
  rfl

end Local

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}


variable (w n) in
theorem integralGL_eq : integralGL (w.adicCompletion E) n = GLint (Fin n) (Ov E w) := by
  have hO : Ov E w = (ValuativeRel.valuation (w.adicCompletion E)).integer :=
    Subring.ext fun x => (GroundTheory.Global.mem_valuationInteger_iff w x).symm
  rw [hO]
  rfl


variable (w) in
theorem isUnifV_uniformizer : IsUnifV E w (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) :=
  GroundTheory.Global.valued_of_irreducible_integer w (GLnLocal.irreducible_uniformizer _)


variable (w) in
theorem Tj_eq_indicator {r : ℕ} (hr : r ≤ n) :
    Tj ℂ n (Ov E w) (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) r =
      (minusculeSet (w.adicCompletion E) n r).indicator fun _ => (1 : ℂ) := by
  unfold Tj
  rw [← integralGL_eq]
  congr 1
  ext g
  exact (mem_minusculeSet_iff hr g).symm

theorem apply_diag_eq {W : GL (Fin n) (w.adicCompletion E) → ℂ}
    (hK : ∀ g, ∀ k ∈ integralGL (w.adicCompletion E) n, W (g * k) = W g)
    {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (m : Fin n → ℕ) :
    W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
      (MulEquiv.piUnits.symm fun i => ϖ ^ m i)) = W (torusPow (w.adicCompletion E) n fun i => (m i : ℤ)) := by
  have hπ := isUnifV_uniformizer w
  set d : Fin n → (w.adicCompletion E)ˣ := fun i => ((uniformizerUnit (w.adicCompletion E))⁻¹ * ϖ) ^ m i
  have hv : ∀ i, Valued.v (d i : w.adicCompletion E) = 1 := fun i => by
    simp only [d, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val, coe_uniformizerUnit, map_pow,
      map_mul, map_inv₀]
    rw [hπ, hϖ, inv_mul_cancel₀ WithZero.coe_ne_zero, one_pow]
  have hd : diagGL (w.adicCompletion E) n d ∈ integralGL (w.adicCompletion E) n := by
    rw [mem_integralGL_iff, ← map_inv]
    constructor <;> intro i j <;> rw [coe_diagGL, Matrix.diagonal_apply] <;> split_ifs
    · exact (GroundTheory.Global.mem_valuationInteger_iff w _).2 (hv i).le
    · exact zero_mem _
    · refine (GroundTheory.Global.mem_valuationInteger_iff w _).2 ?_
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
    · exact zero_mem _
  rw [← hK (torusPow _ _ _) _ hd, torusPow, ← map_mul]
  congr 1
  refine Units.ext ?_
  rw [coe_diagGL]
  change Matrix.diagonal _ = _
  congr 1
  funext i
  simp [d, mul_pow]

theorem recursion : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), ((qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ) k : ℕ) : ℂ))) / 2) * W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ) i))) = (Finset.univ.val.map fun i => (α i : ℂ)).esymm j * ((qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l) k : ℕ) : ℂ))) / 2) * W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i))) := by
  intro E _ _ w n ψ hψ W α hN hK hT ϖ hϖ l hl j hj
  have hKK : integralGL (w.adicCompletion E) n = KGL w (n := n) := integralGL_eq w n
  have hπ := isUnifV_uniformizer w
  have hq : qF (w.adicCompletion E) = qV E w := by
    unfold qF qV
    rw [GroundTheory.Global.natCard_residueField_integer, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : sqrtQ (w.adicCompletion E) ^ (j * (n - j)) = (qV E w : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) := by
    rw [← zpow_natCast, sqrtQ_zpow, hq]
    push_cast [Nat.cast_sub hj]
    rfl
  have hK' : ∀ g, ∀ k ∈ integralGL (w.adicCompletion E) n, W (g * k) = W g := hKK ▸ hK
  have hN' : ∀ u ∈ unipotent (w.adicCompletion E) n ⊓ integralGL (w.adicCompletion E) n, ∀ g, W (u * g) = W g := by
    intro u hu g
    obtain ⟨hu, hi⟩ := (mem_unipotent_inf_integralGL_iff _ n).1 hu
    rw [hN u ((GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => hu.1 hij, hu.2⟩)]
    have h1 : GlobalTheory.Whittaker.superDiag u ∈ Ov E w := by
      unfold GlobalTheory.Whittaker.superDiag
      refine sum_mem fun i _ => sum_mem fun j _ => ?_
      exact (GroundTheory.Global.mem_valuationInteger_iff w _).1 (hi i j)
    have h2 := (hψ 1).2 (one_mem _) _ h1
    rw [one_mul] at h2
    rw [h2, one_mul]
  have hl' : Antitone fun i => (l i : ℤ) := fun a b h => Int.ofNat_le.2 (hl h)
  have h := congrFun (hT _ hπ j hj) (torusPow (w.adicCompletion E) n fun i => (l i : ℤ))
  rw [heckeVec_rightReg (Final.GLintComm E w n) (Tj_mem_hecke hπ j),
    Tj_eq_indicator w hj, hAct, ← integralGL_eq w n, finsum_minuscule hK' hN' hl', satEig, ← hsq,
    Multiset.map_map, Pi.smul_apply, smul_eq_mul] at h
  have h0 : sqrtQ (w.adicCompletion E) ≠ 0 := sqrtQ_ne_zero
  refine mul_left_cancel₀ (pow_ne_zero (j * (n - j)) h0) ?_
  rw [apply_diag_eq hK' hϖ, ← hq, cpow_eq_sqrtQ, Finset.mul_sum]
  have e : (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j) = Finset.univ.powersetCard j := by
    ext J; simp [Finset.mem_powersetCard]
  rw [e]
  refine Eq.trans ?_ ((congrArg (sqrtQ (w.adicCompletion E) ^ rhoPair (fun i => (l i : ℤ)) * ·) h).trans (by
    simp only [Function.comp_def]; ring))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hc : (fun i => (((l + (fun i => if i ∈ S then 1 else 0) : Fin n → ℕ) i : ℕ) : ℤ)) =
      (fun i => (l i : ℤ)) + lamS S := by
    funext i
    simp [lamS]
  have hr : rhoPair ((fun i => (l i : ℤ)) + lamS S) = rhoPair (fun i => (l i : ℤ)) + rhoPair (lamS S) := by
    simp [rhoPair, mul_add, Finset.sum_add_distrib]
  rw [apply_diag_eq hK' hϖ, cpow_eq_sqrtQ, hc, ← kappa_mul_halfModulus hj (Finset.mem_powersetCard.1 hS).2,
    halfModulus_eq, hr, zpow_add₀ h0, zpow_neg]
  have := zpow_ne_zero (rhoPair (lamS S)) h0
  field_simp

end GlobalTheory.WhittakerRecursion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalWhittakerTorusHeckeRecursionStatement
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalWhittaker_torus_hecke_recursion : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), ((qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ) k : ℕ) : ℂ))) / 2) * W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ) i))) = (Finset.univ.val.map fun i => (α i : ℂ)).esymm j * ((qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l) k : ℕ) : ℂ))) / 2) * W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i))) := by
  first | exact @GlobalTheory.WhittakerRecursion.recursion | exact GlobalTheory.WhittakerRecursion.recursion | (intros; apply GlobalTheory.WhittakerRecursion.recursion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PieriRecursionUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PieriRecursionUnique
open scoped Classical

namespace GlobalTheory

theorem pieri_recursion_zero (n : ℕ) (c : ℕ → ℂ) (D : (Fin n → ℕ) → ℂ)
    (hD : ∀ l, ¬ Antitone l → D l = 0)
    (hr : ∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), D (l + (fun i => if i ∈ J then 1 else 0)) = c j * D l)
    (h0 : D 0 = 0) : ∀ μ, D μ = 0 := by
  have main : ∀ s k (μ : Fin n → ℕ), ∑ i, μ i = s →
      n - (Finset.univ.filter (fun i => μ i ≠ 0)).card = k → D μ = 0 := by
    intro s
    refine Nat.strong_induction_on s ?_
    intro s ihs k
    refine Nat.strong_induction_on k ?_
    intro k ihk μ hs hk
    by_cases hμ : Antitone μ
    swap
    · exact hD μ hμ
    by_cases hz : μ = 0
    · subst hz; exact h0
    set J0 : Finset (Fin n) := Finset.univ.filter (fun i => μ i ≠ 0) with hJ0
    set l : Fin n → ℕ := fun i => μ i - 1 with hl
    have hla : Antitone l := fun a b hab => Nat.sub_le_sub_right (hμ hab) 1
    have hj : J0.card ≤ n := by simpa using Finset.card_le_univ J0
    have hlμ : l + (fun i => if i ∈ J0 then 1 else 0) = μ := by
      funext i
      simp only [Pi.add_apply, hl, hJ0, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h <;> omega
    have hsum : ∀ J : Finset (Fin n),
        ∑ i, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) i = ∑ i, l i + J.card := by
      intro J
      simp [Finset.sum_add_distrib, Finset.sum_boole]
    have hDl : D l = 0 := by
      have hlt : ∑ i, l i < s := by
        rw [← hs]
        obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
          by_contra h
          push_neg at h
          exact hz (funext h)
        exact Finset.sum_lt_sum (fun i _ => Nat.sub_le _ _)
          ⟨i, Finset.mem_univ _, by simp only [hl]; omega⟩
      exact ihs _ hlt _ l rfl rfl
    have hsingle : ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = J0.card),
        D (l + (fun i => if i ∈ J then 1 else 0)) = D (l + (fun i => if i ∈ J0 then 1 else 0)) := by
      refine Finset.sum_eq_single_of_mem J0 (by simp) ?_
      intro J hJ hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ
      set ν : Fin n → ℕ := l + (fun i => if i ∈ J then 1 else 0) with hν
      by_cases hνa : Antitone ν
      swap
      · exact hD ν hνa
      have hnsub : ¬ J ⊆ J0 := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega))
      obtain ⟨i, hiJ, hiJ0⟩ := Finset.not_subset.mp hnsub
      have hμi : μ i = 0 := by simpa [hJ0] using hiJ0
      have hνi : 1 ≤ ν i := by simp [hν, hiJ]
      have hsub : insert i J0 ⊆ Finset.univ.filter (fun k => ν k ≠ 0) := by
        intro k hk
        rw [Finset.mem_insert] at hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hk with rfl | hk
        · omega
        · have hk' : μ k ≠ 0 := by simpa [hJ0] using hk
          have hki : k ≤ i := by
            by_contra h
            push_neg at h
            have := hμ h.le
            omega
          have := hνa hki
          omega
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hiJ0] at hcard
      have hcn : (Finset.univ.filter (fun k => ν k ≠ 0)).card ≤ n := by
        simpa using Finset.card_le_univ (Finset.univ.filter (fun k => ν k ≠ 0))
      refine ihk (n - (Finset.univ.filter (fun k => ν k ≠ 0)).card) ?_ ν ?_ rfl
      · omega
      · have h1 := hsum J
        have h2 := hsum J0
        rw [hlμ] at h2
        rw [hν, h1, hJ, ← h2, hs]
    have hrec := hr l hla J0.card hj
    rw [hsingle, hDl, mul_zero, hlμ] at hrec
    exact hrec
  intro μ
  exact main _ _ μ rfl rfl

theorem pieri_recursion_unique : ∀ (n : ℕ) (c : ℕ → ℂ) (V U : (Fin n → ℕ) → ℂ),
    (∀ l, ¬ Antitone l → V l = 0) → (∀ l, ¬ Antitone l → U l = 0) →
    (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), V (l + (fun i => if i ∈ J then 1 else 0)) = c j * V l) →
    (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), U (l + (fun i => if i ∈ J then 1 else 0)) = c j * U l) →
    V 0 = U 0 → V = U := by
  intro n c V U hV hU hrV hrU h0
  have h := pieri_recursion_zero n c (fun l => V l - U l)
    (fun l hl => by simp [hV l hl, hU l hl])
    (fun l hl j hj => by
      simp only [Finset.sum_sub_distrib, hrV l hl j hj, hrU l hl j hj, mul_sub])
    (by simp [h0])
  funext μ
  exact sub_eq_zero.mp (h μ)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PieriRecursionUniqueStatement
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_pieri_recursion_of_eq_zero : ∀ (n : ℕ) (c : ℕ → ℂ) (V U : (Fin n → ℕ) → ℂ), (∀ l, ¬ Antitone l → V l = 0) → (∀ l, ¬ Antitone l → U l = 0) → (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), V (l + (fun i => if i ∈ J then 1 else 0)) = c j * V l) → (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), U (l + (fun i => if i ∈ J then 1 else 0)) = c j * U l) → V 0 = U 0 → V = U := by
  first | exact @GlobalTheory.pieri_recursion_unique | exact GlobalTheory.pieri_recursion_unique | (intros; apply GlobalTheory.pieri_recursion_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniFormula
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

open GlobalTheory.JSW

theorem GlobalTheory.JSW.shintani_formula : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)) = GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * W 1 := by
  intro E _ _ w n ψ hψ W α hN hK hH ϖ hϖ l
  have hvan := GlobalTheory.T.whittaker_diagonal_eq_zero_of_not_antitone E w n ψ hψ W hN hK ϖ hϖ
  have hrec := GlobalTheory.T.sphericalWhittaker_torus_hecke_recursion E w n ψ hψ W α hN hK hH ϖ hϖ
  have hq : ((qV E w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.LFun.qV_ne_zero w)
  have hes : ∀ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => (α i : ℂ)) (MvPolynomial.esymm (Fin n) ℤ j) =
      (Finset.univ.val.map fun i => (α i : ℂ)).esymm j := fun j => by
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℤ]
    rfl
  let V : (Fin n → ℕ) → ℂ := fun m =>
    (qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((m) k : ℕ) : ℂ))) / 2) *
      W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
        (MulEquiv.piUnits.symm fun i => ϖ ^ (m) i))
  let U : (Fin n → ℕ) → ℂ := fun m => if Antitone m then schurAt m (fun i => (α i : ℂ)) * W 1 else 0
  have hVU : V = U := by
    refine GlobalTheory.T.eq_of_pieri_recursion_of_eq_zero n (fun j => (Finset.univ.val.map fun i => (α i : ℂ)).esymm j) V U
      (fun m hm => by simp only [V, hvan m hm, mul_zero]) (fun m hm => by simp only [U, if_neg hm])
      (fun m hm j hj => hrec m hm j hj) (fun m hm j hj => ?_) ?_
    · have hp := congrArg (MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => (α i : ℂ))) (GlobalTheory.T.esymm_mul_schurPolynomialJacobiTrudi n m hm j hj)
      rw [MvPolynomial.eval₂_mul, hes, MvPolynomial.eval₂_sum] at hp
      simp only [U, if_pos hm]
      rw [← Finset.sum_filter, Finset.filter_filter, ← Finset.sum_mul, ← mul_assoc]
      simp only [schurAt]
      rw [hp]
    · have h1 : (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
          (MulEquiv.piUnits.symm fun i => ϖ ^ (0 : Fin n → ℕ) i)) = 1 := by
        ext i j
        simp [Matrix.one_apply, Matrix.diagonal_apply]
      have h0 : (0 : Fin n → ℕ) = fun _ => 0 := rfl
      have ha0 : Antitone (0 : Fin n → ℕ) := antitone_const
      have hs : schurAt (0 : Fin n → ℕ) (fun i => (α i : ℂ)) = 1 := by
        rw [h0, schurAt, GlobalTheory.JSW.schur_zero, MvPolynomial.eval₂_one]
      have hU : U 0 = W 1 := by
        change (if Antitone (0 : Fin n → ℕ) then schurAt 0 (fun i => (α i : ℂ)) * W 1 else 0) = W 1
        rw [if_pos ha0, hs, one_mul]
      rw [hU]
      change _ * W _ = W 1
      rw [h1]
      simp
  have hl := congrFun hVU l
  simp only [V, U] at hl
  by_cases ha : Antitone l
  · rw [if_pos ha] at hl
    have hne : (qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l) k : ℕ) : ℂ))) / 2) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hq]; exact Complex.exp_ne_zero _
    rw [sphW, if_pos ha, neg_div, Complex.cpow_neg, mul_assoc, ← hl, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · rw [hvan l ha, GlobalTheory.JSW.sphW_of_not_antitone _ _ ha, zero_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniFormulaStatement
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_formula_alt : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)) = GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * W 1 := by
  first | exact @GlobalTheory.JSW.shintani_formula | exact GlobalTheory.JSW.shintani_formula | (intros; apply GlobalTheory.JSW.shintani_formula <;> assumption)
end
