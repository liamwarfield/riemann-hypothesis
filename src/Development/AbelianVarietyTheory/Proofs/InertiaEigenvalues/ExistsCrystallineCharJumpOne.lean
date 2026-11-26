module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicPeriodLocalPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvMemDeRhamFilNegOfExactDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvMemDeRhamFilNegOfExactDegree
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.FilInv

theorem pow_mem_Fil {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {b : ℤ} {x : BdR} (hx : x ∈ PD.Fil b) (n : ℕ) :
    x ^ n ∈ PD.Fil (n * b) := by
  induction n with
  | zero => simpa using PD.one_mem
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact PD.Fil_mul _ _ _ _ ih hx

theorem inv_mem_Fil_neg : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a : ℤ) (u v : P.R.BdR), u * v = 1 → u ∈ (P.PD K).Fil a → u ∉ (P.PD K).Fil (a + 1) → v ∈ (P.PD K).Fil (-a) := by
  intro l _ P AI T K a u v huv hu hu1
  obtain ⟨s, hs, hts⟩ := GlobalTheory.TopSteps.CrysRules.exists_inverse_fontaineElement_mem_fil_neg_one T K
  have ht := (P.PD K).mem_filtration_one

  obtain ⟨w, w', hw, hw', hww⟩ : ∃ w w' : P.R.BdR, w ∈ (P.PD K).Fil (-a) ∧ w' ∈ (P.PD K).Fil a ∧
      w * w' = 1 := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg a
    · refine ⟨s ^ n, ((P.PD K).ι (P.PD K).t) ^ n, ?_, ?_, ?_⟩
      · simpa using pow_mem_Fil (P.PD K) hs n
      · simpa using pow_mem_Fil (P.PD K) ht n
      · rw [← mul_pow, mul_comm, hts, one_pow]
    · refine ⟨((P.PD K).ι (P.PD K).t) ^ n, s ^ n, ?_, ?_, ?_⟩
      · simpa using pow_mem_Fil (P.PD K) ht n
      · simpa using pow_mem_Fil (P.PD K) hs n
      · rw [← mul_pow, hts, one_pow]
  have hx0 : u * w ∈ (P.PD K).Fil 0 := by
    simpa using (P.PD K).Fil_mul _ _ _ _ hu hw
  have hx1 : u * w ∉ (P.PD K).Fil 1 := by
    intro h
    apply hu1
    have := (P.PD K).Fil_mul _ _ _ _ h hw'
    rwa [mul_assoc, hww, mul_one, add_comm] at this
  obtain ⟨y, hy, hxy⟩ := ((GlobalTheory.Per.TiedField.tied_field l P AI T).2.2.2.2) K _ hx0 hx1
  have hv : v = w * y := by
    calc v = v * ((u * w) * y) := by rw [hxy, mul_one]
      _ = (u * v) * (w * y) := by ring
      _ = w * y := by rw [huv, one_mul]
  rw [hv]
  simpa using (P.PD K).Fil_mul _ _ _ _ hw hy

end GlobalTheory.FilInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvMemDeRhamFilNegOfExactDegreeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_mem_deRhamFil_neg_of_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a : ℤ) (u v : P.R.BdR), u * v = 1 → u ∈ (P.PD K).Fil a → u ∉ (P.PD K).Fil (a + 1) → v ∈ (P.PD K).Fil (-a) := by
  first | exact @GlobalTheory.FilInv.inv_mem_Fil_neg | exact GlobalTheory.FilInv.inv_mem_Fil_neg | (intros; apply GlobalTheory.FilInv.inv_mem_Fil_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousIntegralUnitCharOfChar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousIntegralUnitCharOfChar
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.ContCharUnitsOL

theorem norm_algHom_apply (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (x : ↥K.1) : ‖((τ₀ x : ↥LL.1) : Om l)‖ = ‖(x : Om l)‖ := by
  have h1 : minpoly ℚ_[l] ((τ₀ x : ↥LL.1) : Om l) = minpoly ℚ_[l] x :=
    minpoly.algHom_eq ((LL.1).val.comp τ₀) ((Subtype.val_injective).comp τ₀.toRingHom.injective) x
  have h2 : minpoly ℚ_[l] (x : Om l) = minpoly ℚ_[l] x :=
    minpoly.algHom_eq (K.1).val Subtype.val_injective x
  show spectralNorm ℚ_[l] (PadicAlgCl l) _ = spectralNorm ℚ_[l] (PadicAlgCl l) _
  unfold spectralNorm
  rw [h1, h2]

theorem continuous_algHom (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :
    Continuous (fun x : ↥K.1 => τ₀ x) := by
  refine AddMonoidHomClass.continuous_of_bound τ₀ 1 (fun x => ?_)
  show ‖((τ₀ x : ↥LL.1) : Om l)‖ ≤ 1 * ‖(x : Om l)‖
  rw [norm_algHom_apply, one_mul]

theorem norm_le_one (l : ℕ) [Fact l.Prime] (K : FinExt l) (c : ↥(GK K) →* (↥(K0 K))ˣ)
    (hc : Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l))) (g : ↥(GK K)) :
    ‖(((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK K
  obtain ⟨B, hB⟩ := (isCompact_univ (X := ↥(GK K))).exists_bound_of_continuousOn hc.continuousOn
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
  have hpow : (((c (g ^ n) : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l) = ((((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) ^ n := by
    simp [map_pow]
  have := hB (g ^ n) (Set.mem_univ _)
  rw [hpow, norm_pow] at this
  linarith

end GlobalTheory.ContCharUnitsOL

namespace GlobalTheory.ContCharUnitsOL

theorem exists_unit_char (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (c : ↥(GK K) →* (↥(K0 K))ˣ)
    (hc : Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l))) :
    ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ,
      Continuous (fun g : ↥(GK K) => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧
      ∀ g : ↥(GK K), (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1) *
        τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1 := by
  let ι : ↥(K0 K) →+* ↥K.1 := algebraMap ↥(K0 K) ↥K.1
  have hι : ∀ x : ↥(K0 K), ((ι x : ↥K.1) : Om l) = (x : Om l) := fun x => rfl
  let v : ↥(GK K) → ↥LL.1 := fun g => τ₀ (ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K)))
  let w : ↥(GK K) → ↥LL.1 := fun g => τ₀ (ι ((c g : (↥(K0 K))ˣ) : ↥(K0 K)))
  have hw : ∀ g, w g ∈ OL LL := fun g => by
    rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
    show ‖((τ₀ _ : ↥LL.1) : Om l)‖ ≤ 1
    rw [norm_algHom_apply, hι]
    exact norm_le_one l K c hc g
  have hv : ∀ g, v g ∈ OL LL := fun g => by
    rw [GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one]
    show ‖((τ₀ _ : ↥LL.1) : Om l)‖ ≤ 1
    rw [norm_algHom_apply, hι, ← map_inv]
    exact norm_le_one l K c hc g⁻¹
  have hvw : ∀ g, v g * w g = 1 := fun g => by
    show τ₀ (ι _) * τ₀ (ι _) = 1
    rw [← map_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, map_one]
  have hwv : ∀ g, w g * v g = 1 := fun g => by rw [mul_comm]; exact hvw g
  let χf : ↥(GK K) → (↥(OL LL))ˣ := fun g =>
    ⟨⟨v g, hv g⟩, ⟨w g, hw g⟩, Subtype.ext (hvw g), Subtype.ext (hwv g)⟩
  let χ : ↥(GK K) →* (↥(OL LL))ˣ :=
    { toFun := χf
      map_one' := by
        apply Units.ext; apply Subtype.ext
        show τ₀ (ι (((c 1)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) = 1
        rw [map_one, inv_one, Units.val_one, map_one, map_one]
      map_mul' := fun g h => by
        apply Units.ext; apply Subtype.ext
        show τ₀ (ι (((c (g * h))⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) =
          τ₀ (ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) * τ₀ (ι (((c h)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K)))
        rw [map_mul, mul_inv, Units.val_mul, map_mul, map_mul] }
  refine ⟨χ, ?_, fun g => hvw g⟩
  show Continuous v
  have hne : ∀ g, (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l) ≠ 0 := fun g h => by
    have : ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 0 := Subtype.ext h
    exact (c g).ne_zero this
  have h1 : Continuous (fun g : ↥(GK K) => ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K))) := by
    refine continuous_induced_rng.2 ?_
    have : (fun g : ↥(GK K) => ((ι (((c g)⁻¹ : (↥(K0 K))ˣ) : ↥(K0 K)) : ↥K.1) : Om l)) =
        fun g => ((((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l))⁻¹ := by
      funext g; rw [hι, Units.val_inv_eq_inv_val]; rfl
    rw [Function.comp_def, this]
    exact hc.inv₀ hne
  exact (continuous_algHom l K LL τ₀).comp h1

end GlobalTheory.ContCharUnitsOL

theorem GlobalTheory.ContCharUnitsOL.main : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ↥(GK K) →* (↥(K0 K))ˣ), Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) → ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g : ↥(GK K) => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ ∀ g : ↥(GK K), (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1 := by
  intro l _ K LL τ₀ c hc
  exact GlobalTheory.ContCharUnitsOL.exists_unit_char l K LL τ₀ c hc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousIntegralUnitCharOfCharStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_integralUnitChar_of_char : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ↥(GK K) →* (↥(K0 K))ˣ), Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) → ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g : ↥(GK K) => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ ∀ g : ↥(GK K), (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1 := by
  first | exact @GlobalTheory.ContCharUnitsOL.main | exact GlobalTheory.ContCharUnitsOL.main | (intros; apply GlobalTheory.ContCharUnitsOL.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpOneAtEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantVectorExactFiltrationDegreeBcris
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantVectorExactFiltrationDegreeBcris
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.exists_letter_vector_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (x : P.R.B), IsUnit x → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ (μ : ↥(GK K) →* (↥LL.1)ˣ) (τ₀' τ' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) (j : ℕ), (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀' ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1) → (∀ a : ↥(K0 K), τ' ((⇑(P.PD K).σ)^[j] a) = τ₀' a) → ∀ d : ℤ, P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil d → P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil (d + 1) → ∃ w ∈ DcrisL (P.PD K) (charRep μ) τ', ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) d ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1) := by
  intro l _ P AI hT K LL x hx c hc μ τ₀' τ' j hμ hτ d hd hd1
  have := (P.PD K).finK₀
  obtain ⟨m, cc, kk, h1, hsum⟩ := GlobalTheory.exists_embedding_idempotent_tensor ℚ_[l] ↥(K0 K) ↥LL.1 τ'
  set y := (⇑P.φB)^[j] x with hy
  set z := P.ιB y with hzdef
  clear_value z y
  let f : ↥(K0 K) →ₗ[ℚ_[l]] P.R.B := (LinearMap.mulRight ℚ_[l] y) ∘ₗ (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B).toLinearMap
  have hB : ∀ s : ↥(K0 K), ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y) = ∑ i, (τ' s * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := by
    intro s
    have := congrArg (LinearMap.lTensor ↥LL.1 f) (hsum s)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [f, map_sum, LinearMap.lTensor_tmul] using this
  have hφK : ∀ k : ↥(K0 K), P.φB (algebraMap ↥(K0 K) P.R.B k) = algebraMap ↥(K0 K) P.R.B ((P.PD K).σ k) := by
    intro k; rw [← P.PD_φ K]; exact (P.PD K).φ_K₀ k
  have hact : ∀ g : ↥(GK K), ∀ n : ℕ, P.actQ (g : GQ l) ((⇑P.φB)^[n] x) = algebraMap ↥(K0 K) P.R.B ((⇑(P.PD K).σ)^[n] (c g : ↥(K0 K))) * (⇑P.φB)^[n] x := by
    intro g n
    have hcomm : ∀ b, P.actQ (g : GQ l) (P.φB b) = P.φB (P.actQ (g : GQ l) b) := by
      intro b
      have := (P.PD K).φ_comm g b
      rw [P.PD_φ, P.PD_φ, P.PD_actB, P.PD_actB] at this
      exact this.symm
    induction n with
    | zero => simpa using hc g
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [hcomm, ih, map_mul, hφK]
  have hterm : ∀ (g : ↥(GK K)) (a : ↥LL.1) (k : ↥(K0 K)),
      actVB (P.PD K) (charRep μ) g (a ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B k * y)) =
        (((μ g : (↥LL.1)ˣ) : ↥LL.1) * a) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B ((⇑(P.PD K).σ)^[j] (c g : ↥(K0 K)) * k) * y) := by
    intro g a k
    simp only [actVB, AlgebraTensorModule.map_tmul]
    congr 1
    change (P.PD K).actB g (algebraMap ↥(K0 K) P.R.B k * y) = _
    rw [map_mul, AlgEquiv.commutes, P.PD_actB, hy, hact g j, map_mul]
    ring
  obtain ⟨w, hw⟩ : ∃ w : ↥LL.1 ⊗[ℚ_[l]] P.R.B, w = ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := ⟨_, rfl⟩
  have hinv : ∀ g : ↥(GK K), actVB (P.PD K) (charRep μ) g w = w := by
    intro g
    set s := (⇑(P.PD K).σ)^[j] (c g : ↥(K0 K))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hw, map_sum, hterm]
    calc ∑ i, (((μ g : (↥LL.1)ˣ) : ↥LL.1) * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y)
        = ((μ g : (↥LL.1)ˣ) : ↥LL.1) • ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y) := by
          rw [Finset.smul_sum]; simp only [TensorProduct.smul_tmul', smul_eq_mul]
      _ = ((μ g : (↥LL.1)ˣ) : ↥LL.1) • ∑ i, (τ' s * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := by rw [hB]
      _ = _ := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [TensorProduct.smul_tmul', smul_eq_mul, ← mul_assoc, hτ, hμ, one_mul]

  have hlet : ∀ a : ↥(K0 K), mulVB (K₀ := ↥(K0 K)) (B := P.R.B) (V := ↥LL.1) (LL := ↥LL.1) a w = τ' a • w := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hw, map_sum, mulVB, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
    have : ∀ i, algebraMap ↥(K0 K) P.R.B a * (algebraMap ↥(K0 K) P.R.B (kk i) * y) = algebraMap ↥(K0 K) P.R.B (a * kk i) * y := by
      intro i; rw [map_mul, mul_assoc]
    simp only [this]
    rw [hB, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  have hι : ∀ k : ↥(K0 K), (P.PD K).ι (algebraMap ↥(K0 K) P.R.B k * y) = algebraMap ↥(K0 K) P.R.BdR k * z := by
    intro k; rw [map_mul, AlgHom.commutes, P.PD_ι, ← hzdef]
  have hιw : ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w = ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.BdR (kk i) * z) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hw, map_sum, ιV, AlgebraTensorModule.map_tmul, LinearMap.id_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact hι (kk i)
  have hmem : ∀ k : ↥(K0 K), algebraMap ↥(K0 K) P.R.BdR k * z ∈ (P.PD K).Fil d := by
    intro k
    rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR, ← Algebra.smul_def]
    exact (P.PD K).Fil d |>.smul_mem _ hd
  refine ⟨w, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold Dcris
    refine (Submodule.mem_iInf _).2 fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hinv g, LinearMap.id_apply, sub_self]
  · refine (Submodule.mem_iInf _).2 fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hlet a, LinearMap.smul_apply, LinearMap.id_apply, sub_self]
  · rw [hιw]
    refine ⟨∑ i, cc i ⊗ₜ[ℚ_[l]] (⟨algebraMap ↥(K0 K) P.R.BdR (kk i) * z, hmem (kk i)⟩ : ↥(((P.PD K).Fil d).restrictScalars ℚ_[l])), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, AlgebraTensorModule.map_tmul]
  · intro hcon
    have hyu : ∀ n : ℕ, IsUnit ((⇑P.φB)^[n] x) := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih => rw [Function.iterate_succ_apply']; exact ih.map P.φB
    have hz : IsUnit z := by rw [hzdef, hy]; exact (hyu j).map P.ιB
    obtain ⟨v, hzv⟩ := hz.exists_right_inv
    have hvz : v * z = 1 := by rw [mul_comm]; exact hzv
    have hv : v ∈ (P.PD K).Fil (-d) := GlobalTheory.FilInv.inv_mem_Fil_neg l P AI hT K d z v hzv hd hd1
    let Mv : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] ↥LL.1 ⊗[ℚ_[l]] P.R.BdR :=
      AlgebraTensorModule.map (LinearMap.id : ↥LL.1 →ₗ[↥LL.1] ↥LL.1) (LinearMap.mulLeft ℚ_[l] v)
    have hvmul : ∀ b ∈ ((P.PD K).Fil (d + 1)).restrictScalars ℚ_[l], LinearMap.mulLeft ℚ_[l] v b ∈ ((P.PD K).Fil 1).restrictScalars ℚ_[l] := by
      intro b hb
      have := (P.PD K).Fil_mul (-d) (d + 1) v b hv hb
      rw [show -d + (d + 1) = 1 by ring] at this
      exact this
    have hMv : ∀ t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1), Mv t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) 1 := by
      rintro t ⟨s, rfl⟩
      refine ⟨AlgebraTensorModule.map (LinearMap.id : ↥LL.1 →ₗ[↥LL.1] ↥LL.1) ((LinearMap.mulLeft ℚ_[l] v).restrict hvmul) s, ?_⟩
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Mv, AlgebraTensorModule.map_tmul]
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    have hE : Mv (ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w) = ∑ i, cc i ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.BdR (kk i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hιw, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Mv, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
      rw [mul_left_comm, hvz, mul_one]
    have hF1 := hMv _ hcon
    rw [hE] at hF1
    let q := (((P.PD K).Fil 1).restrictScalars ℚ_[l]).mkQ
    let h0 : ↥(K0 K) →ₗ[ℚ_[l]] P.R.BdR ⧸ (((P.PD K).Fil 1).restrictScalars ℚ_[l]) :=
      q ∘ₗ (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.BdR).toLinearMap
    have hinj : Function.Injective h0 := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro k hk
      have hk' : algebraMap ↥(K0 K) P.R.BdR k ∈ (P.PD K).Fil 1 := by
        have := (Submodule.Quotient.mk_eq_zero _).1 hk
        exact this
      rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR] at hk'
      have := JsetEmb.field_inter_filtration_one_eq_zero (P.PD K) _ hk'
      exact (map_eq_zero_iff _ (algebraMap ↥(K0 K) ↥K.1).injective).1 this
    have hq : ∀ t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) 1, LinearMap.lTensor ↥LL.1 q t = 0 := by
      rintro t ⟨s, rfl⟩
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.lTensor_tmul]
        rw [show q ((((P.PD K).Fil 1).restrictScalars ℚ_[l]).subtype b) = 0 from (Submodule.Quotient.mk_eq_zero _).2 b.2, tmul_zero]
      | add s t hs ht => rw [map_add (f := _), map_add (f := _), hs, ht, add_zero]
    have hzero : LinearMap.lTensor ↥LL.1 h0 (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i) = 0 := by
      have := hq _ hF1
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [h0, map_sum, LinearMap.lTensor_tmul] using this
    have he : (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i : ↥LL.1 ⊗[ℚ_[l]] ↥(K0 K)) = 0 :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := ↥LL.1) h0 hinj (hzero.trans (map_zero _).symm)
    let Λ : ↥LL.1 ⊗[ℚ_[l]] ↥(K0 K) →ₗ[ℚ_[l]] ↥LL.1 := TensorProduct.lift ((LinearMap.mul ℚ_[l] ↥LL.1).compl₂ τ'.toLinearMap)
    have hΛ : Λ (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i) = 1 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Λ, map_sum, h1]
    rw [he, map_zero] at hΛ
    exact zero_ne_one hΛ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantVectorExactFiltrationDegreeBcrisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (x : P.R.B), IsUnit x → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ (μ : ↥(GK K) →* (↥LL.1)ˣ) (τ₀' τ' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) (j : ℕ), (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀' ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1) → (∀ a : ↥(K0 K), τ' ((⇑(P.PD K).σ)^[j] a) = τ₀' a) → ∀ d : ℤ, P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil d → P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil (d + 1) → ∃ w ∈ DcrisL (P.PD K) (charRep μ) τ', ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) d ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1) := by
  first | exact @GlobalTheory.exists_letter_vector_exact_degree | exact GlobalTheory.exists_letter_vector_exact_degree | (intros; apply GlobalTheory.exists_letter_vector_exact_degree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysCharacterOfCrystallineVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysCharacterOfCrystallineVectors
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LetterCrys

theorem isCrys_of_letters : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) := by
  intro l _ P AI hT K LL hA μ hμ d hw
  haveI := LL.2
  haveI := K.2
  obtain ⟨hgood, -⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := ↥LL.1
      ρ := charRep μ
      cont := fun x => (hμ.mul continuous_const :
        Continuous fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1) * x) }
  obtain ⟨⟨hfin, hle⟩, -, -⟩ :=
    GlobalTheory.Per.FontaineTied.fontCore_all_of_tied l P AI hT K ↥LL.1 ↥(OL LL) hgood A
  haveI : Module.Finite ↥LL.1 ↥(Dcris (P.PD K) (charRep μ)) := hfin
  unfold IsCrys
  refine le_antisymm hle ?_
  have hcard : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 :=
    Formalism.MainNotions.N.JsetEmb.card_emb_good hA.2.2
  have e : K0 K = K.1 := inf_eq_left.2 hA.1
  have hfr : finrank ℚ_[l] ↥(K0 K) = finrank ℚ_[l] ↥K.1 :=
    (IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq
  have hsurj : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) := fun x =>
    ⟨⟨x, x.2, hA.1 x.2⟩, rfl⟩
  let f : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) := fun τ =>
    τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
  have hf : Function.Injective f := fun τ τ' h => AlgHom.ext fun x => by
    obtain ⟨y, rfl⟩ := hsurj x
    exact AlgHom.congr_fun h y
  choose w hwmem hw1 hw2 using hw
  have hne : ∀ τ, w τ ≠ 0 := fun τ h0 => hw2 τ (by rw [h0, map_zero]; exact Submodule.zero_mem _)
  have hind : iSupIndep fun τ => DcrisL (P.PD K) (charRep μ) (f τ) :=
    (GlobalTheory.NL.PhiD.iSupIndep_letter (P.PD K) (charRep μ)).comp hf
  have hli : LinearIndependent ↥LL.1 w := iSupIndep.linearIndependent _ hind hwmem hne
  let w' : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ↥(Dcris (P.PD K) (charRep μ)) := fun τ => ⟨w τ, (hwmem τ).1⟩
  have hli' : LinearIndependent ↥LL.1 w' :=
    LinearIndependent.of_comp (Dcris (P.PD K) (charRep μ)).subtype hli
  have hpos : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) ≠ 0 := by
    rw [hcard]; exact Module.finrank_pos.ne'
  haveI : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := Nat.finite_of_card_ne_zero hpos
  haveI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  have h2 := hli'.fintype_card_le_finrank
  rw [← Nat.card_eq_fintype_card, hcard] at h2
  rw [Module.finrank_self, mul_one, hfr]
  exact h2

end GlobalTheory.LetterCrys
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysCharacterOfCrystallineVectorsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrys_character_of_crystalline_vectors : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → ∀ d : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℤ, (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)), ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ) ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d τ + 1)) → IsCrys (P.PD K) (charRep μ) := by
  first | exact @GlobalTheory.LetterCrys.isCrys_of_letters | exact GlobalTheory.LetterCrys.isCrys_of_letters | (intros; apply GlobalTheory.LetterCrys.isCrys_of_letters <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpOneAtEmbedding
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.HWL

theorem charRep_crys_jump_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  intro l _ P AI hT K LL hA τ₀ x hx _hφn hF1 hF2 hφj c hc μ hcont hμ
  let ι0 := IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1
  have hsurj : Function.Surjective ι0 := fun y =>
    ⟨⟨y.1, IntermediateField.mem_inf.2 ⟨y.2, hA.1 y.2⟩⟩, Subtype.ext rfl⟩
  obtain ⟨emb, hbij, hemb⟩ := GlobalTheory.HWL.exists_letters l P K 1 LL hA.2.2
  haveI : NeZero (finrank ℚ_[l] ↥(K0 K)) := ⟨by haveI := (P.PD K).finK₀; exact Module.finrank_pos.ne'⟩
  have hit : ∀ (j : ℕ) (i : ZMod (finrank ℚ_[l] ↥(K0 K))) (a : ↥(K0 K)),
      emb i ((⇑(P.PD K).σ)^[j] a) = emb (i - j) a := by
    intro j
    induction j with
    | zero => intro i a; simp
    | succ j ih =>
      intro i a
      rw [Function.iterate_succ_apply, ih]
      have h := DFunLike.congr_fun (hemb (i - j - 1)) a
      rw [sub_add_cancel] at h
      rw [AlgHom.comp_apply] at h
      rw [h]
      congr 1
      push_cast
      ring_nf
  obtain ⟨i₀, hi₀⟩ := hbij.2 (τ₀.comp ι0)
  have hμ' : ∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * (τ₀.comp ι0) ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1 :=
    fun g => hμ g
  have key : ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ w ∈ DcrisL (P.PD K) (charRep μ) (τ.comp ι0),
      ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (if τ = τ₀ then 1 else 0) ∧
      ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) ((if τ = τ₀ then 1 else 0) + 1) := by
    intro τ
    obtain ⟨i, hi⟩ := hbij.2 (τ.comp ι0)
    have hj : ∀ a : ↥(K0 K), (τ.comp ι0) ((⇑(P.PD K).σ)^[(i - i₀).val] a) = (τ₀.comp ι0) a := by
      intro a
      rw [← hi, ← hi₀, hit, ZMod.natCast_zmod_val, sub_sub_cancel]
    by_cases hτ : τ = τ₀
    · subst hτ
      have h0 : (i - i₀).val = 0 := by
        rw [hbij.1 (hi.trans hi₀.symm), sub_self, ZMod.val_zero]
      rw [h0] at hj
      have := GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris l P AI hT K LL x hx c hc μ (τ.comp ι0) (τ.comp ι0) 0 hμ' hj 1
        (by simpa using hF1) (by simpa [show (1 : ℤ) + 1 = 2 by norm_num] using hF2)
      simpa using this
    · have hpos : 0 < (i - i₀).val := by
        rw [Nat.pos_iff_ne_zero]
        intro h0
        rw [ZMod.val_eq_zero, sub_eq_zero] at h0
        subst h0
        apply hτ
        have hc' : τ.comp ι0 = τ₀.comp ι0 := hi.symm.trans hi₀
        refine AlgHom.ext fun y => ?_
        obtain ⟨z, rfl⟩ := hsurj y
        exact DFunLike.congr_fun hc' z
      have hlt : (i - i₀).val < finrank ℚ_[l] ↥(K0 K) := ZMod.val_lt _
      obtain ⟨h1, h2⟩ := hφj _ hpos hlt
      have := GlobalTheory.T.exists_invariant_vector_exact_filtrationDegree_Bcris l P AI hT K LL x hx c hc μ (τ₀.comp ι0) (τ.comp ι0) (i - i₀).val hμ' hj 0
        h1 (by simpa using h2)
      simpa [hτ] using this
  have hcrys := GlobalTheory.T.isCrys_character_of_crystalline_vectors l P AI hT K LL hA μ hcont (fun τ => if τ = τ₀ then 1 else 0) key
  exact ⟨hcrys, GlobalTheory.T.crystalline_character_jumps_of_exact_degree l P AI hT K LL hA μ hcont (fun τ => if τ = τ₀ then 1 else 0) key hcrys⟩

end GlobalTheory.HWL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineCharacterJumpOneAtEmbeddingStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_character_jump_one_at_embedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ μ : ↥(GK K) →* (↥LL.1)ˣ, Continuous (fun g : ↥(GK K) => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  first | exact @GlobalTheory.HWL.charRep_crys_jump_one | exact GlobalTheory.HWL.charRep_crys_jump_one | (intros; apply GlobalTheory.HWL.charRep_crys_jump_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisPeriodRatioMemUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisPeriodRatioMemUnramified
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.PeriodQuot

theorem iter_mul {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (f : A →ₐ[R] A)
    (j : ℕ) (a b : A) : f^[j] (a * b) = f^[j] a * f^[j] b := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_mul]

theorem iter_one {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (f : A →ₐ[R] A)
    (j : ℕ) : f^[j] (1 : A) = 1 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_one]

theorem iter_natCast_mul {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (f : A →ₐ[R] A)
    (j m q : ℕ) (a : A) : f^[j] ((m : A) ^ q * a) = (m : A) ^ q * f^[j] a := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem galois_periodRatio_mem_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x := by
  intro l _ P AI hT K x hx hn h1 h2 hj g
  obtain ⟨u, rfl⟩ := hx
  set n := finrank ℚ_[l] ↥(K0 K) with hn_def
  have npos : 0 < n := by
    haveI := (P.PD K).finK₀
    exact Module.finrank_pos
  set y : P.R.B := ((u⁻¹ : (P.R.B)ˣ) : P.R.B) with hy
  have huy : (u : P.R.B) * y = 1 := u.mul_inv
  set c : P.R.B := P.actQ (g : GQ l) u * y with hc
  have hcx : P.actQ (g : GQ l) u = c * u := by rw [hc, mul_assoc, u.inv_mul, mul_one]
  have hcomm : ∀ b, P.φB (P.actQ (g : GQ l) b) = P.actQ (g : GQ l) (P.φB b) := by
    intro b
    have := (P.PD K).φ_comm g b
    rwa [P.PD_φ, P.PD_actB, P.PD_actB, P.PD_φ] at this
  have hcommj : ∀ j b, (⇑P.φB)^[j] (P.actQ (g : GQ l) b) = P.actQ (g : GQ l) ((⇑P.φB)^[j] b) :=
    fun j b => (Function.Commute.iterate_left (f := ⇑P.φB) (g := ⇑(P.actQ (g : GQ l)))
      (fun b => hcomm b) j) b

  have hlB : IsUnit ((l : ℕ) : P.R.B) := by
    have h0 : ((l : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have := (isUnit_iff_ne_zero.mpr h0).map (algebraMap ℚ_[l] P.R.B)
    simpa using this

  have hφc : (⇑P.φB)^[n] c = c := by
    have hu : IsUnit ((l : P.R.B) * u) := hlB.mul u.isUnit
    apply hu.mul_left_injective
    show (⇑P.φB)^[n] c * ((l : P.R.B) * u) = c * ((l : P.R.B) * u)
    rw [← hn, ← iter_mul, ← hcx, hcommj, hn, map_mul, map_natCast, hcx]
    ring

  have hpow : ∀ q : ℕ, (⇑P.φB)^[n * q] (u : P.R.B) = (l : P.R.B) ^ q * u := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, hn,
        show (l : P.R.B) * (u : P.R.B) = (l : P.R.B) ^ 1 * u by rw [pow_one],
        iter_natCast_mul, ih, ← mul_assoc, ← pow_add, add_comm 1 q]
  have hsmul : ∀ (q : ℕ) (z : P.R.B), P.ιB ((l : P.R.B) ^ q * z) =
      (((l : ↥K.1) ^ q : ↥K.1)) • P.ιB z := by
    intro q z
    rw [map_mul, map_pow, map_natCast, Algebra.smul_def, map_pow, map_natCast]
  have hne : ∀ q : ℕ, ((l : ↥K.1) ^ q : ↥K.1) ≠ 0 := fun q =>
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  have hdeg : ∀ j : ℕ, ∃ d : ℤ, P.ιB ((⇑P.φB)^[j] (u : P.R.B)) ∈ (P.PD K).Fil d ∧
      P.ιB ((⇑P.φB)^[j] (u : P.R.B)) ∉ (P.PD K).Fil (d + 1) := by
    intro j
    have hj_eq : j = j % n + n * (j / n) := (Nat.mod_add_div j n).symm
    have hw : (⇑P.φB)^[j] (u : P.R.B) = (l : P.R.B) ^ (j / n) * (⇑P.φB)^[j % n] u := by
      conv_lhs => rw [hj_eq]
      rw [Function.iterate_add_apply, hpow, iter_natCast_mul]
    rw [hw, hsmul]
    rcases Nat.eq_zero_or_pos (j % n) with h0 | hr
    · refine ⟨1, ?_, ?_⟩
      · rw [h0, Function.iterate_zero_apply]
        exact Submodule.smul_mem _ _ h1
      · rw [h0, Function.iterate_zero_apply, Submodule.smul_mem_iff _ (hne _)]
        simpa using h2
    · obtain ⟨ha, hb⟩ := hj (j % n) hr (Nat.mod_lt _ npos)
      refine ⟨0, Submodule.smul_mem _ _ ha, ?_⟩
      rw [Submodule.smul_mem_iff _ (hne _)]
      simpa using hb
  have hF : ∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0 := by
    intro j
    obtain ⟨d, hd1, hd2⟩ := hdeg j
    have hinv : P.ιB ((⇑P.φB)^[j] (u : P.R.B)) * P.ιB ((⇑P.φB)^[j] y) = 1 := by
      rw [← map_mul, ← iter_mul, huy, iter_one, map_one]
    have hyF := GlobalTheory.T.inv_mem_deRhamFil_neg_of_exact_degree l P AI hT K d _ _ hinv hd1 hd2
    have hgF : P.ιB (P.actQ (g : GQ l) ((⇑P.φB)^[j] (u : P.R.B))) ∈ (P.PD K).Fil d := by
      have := (P.PD K).ι_comm g ((⇑P.φB)^[j] (u : P.R.B))
      rw [P.PD_ι, P.PD_actB, P.PD_ι] at this
      rw [this]
      exact (P.PD K).Fil_G g d _ hd1
    have := (P.PD K).Fil_mul d (-d) _ _ hgF hyF
    rw [add_neg_cancel] at this
    rw [hc, iter_mul, hcommj, map_mul]
    exact this
  obtain ⟨a, ha⟩ := GlobalTheory.T.mem_unramified_of_frobenius_iterate_fixed_fil l P AI hT K c hφc hF
  exact ⟨a, by rw [hcx, ha]⟩

end GlobalTheory.PeriodQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisPeriodRatioMemUnramifiedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_periodRatio_mem_unramified_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] x = (l : P.R.B) * x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → (∀ j : ℕ, 0 < j → j < finrank ℚ_[l] ↥(K0 K) → P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil 0 ∧ P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil 1) → ∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x := by
  first | exact @GlobalTheory.PeriodQuot.galois_periodRatio_mem_unramified | exact GlobalTheory.PeriodQuot.galois_periodRatio_mem_unramified | (intros; apply GlobalTheory.PeriodQuot.galois_periodRatio_mem_unramified <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterOfBcrisUnitFilOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterOfBcrisUnitFilOne
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LtCharCont

open GlobalTheory.ExpImage Filter Topology Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

theorem oB_mem {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (w : Om l) :
    oB P w ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om w
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem norm_th_le_of_mem_Lat {P : LocPrime l} {AI : LocAinf l P} (Θ : ThetaL P AI) {n : ℕ}
    {y : P.R.BdR} (hy : y ∈ Lat AI 1 n) : ‖Θ.θ y‖ ≤ ‖(l : ℚ_[l])‖ ^ n := by
  obtain ⟨a, ha⟩ := hy
  have hy0 : y ∈ FilB P 0 := Lat_mem_zero AI ⟨a, ha⟩
  have hi0 : io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ FilB P 0 := io_mem AI _
  have hd0 : y - io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ FilB P 0 := sub_mem hy0 hi0
  have h1 : Θ.θ (y - io AI (((l : ℕ) : Ainf l) ^ n * a)) = 0 :=
    (Θ.θ_ker _ hd0).2 (by simpa using ha)
  have h2 : Θ.θ y = Θ.θ (io AI (((l : ℕ) : Ainf l) ^ n * a)) := by
    have := Θ.θ_add _ hd0 _ hi0
    rw [sub_add_cancel, h1, zero_add] at this
    exact this
  have e : io AI (((l : ℕ) : Ainf l) ^ n * a) = qB P ((l : ℚ_[l]) ^ n) * io AI a := by
    rw [map_mul, map_pow, map_natCast, map_pow, map_natCast]
  rw [h2, e, Θ.θ_mul _ (qB_mem _) _ (io_mem AI a), norm_mul]
  have e2 : qB P ((l : ℚ_[l]) ^ n) = oB P (algebraMap ℚ_[l] (Om l) ((l : ℚ_[l]) ^ n)) :=
    IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR _
  rw [e2, Θ.θ_Om, PadicComplex.norm_extends]
  have e3 : ‖algebraMap ℚ_[l] (Om l) ((l : ℚ_[l]) ^ n)‖ = ‖(l : ℚ_[l])‖ ^ n := by
    rw [← norm_pow]; exact PadicAlgCl.norm_extends (p := l) _
  rw [e3]
  have := Θ.θ_int a
  rw [← io_apply AI a] at this
  calc _ ≤ ‖(l : ℚ_[l])‖ ^ n * 1 := by gcongr
    _ = _ := mul_one _

theorem continuous_char_of_act : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → P.ιB x ∈ (P.PD K).Fil 1 →
    P.ιB x ∉ (P.PD K).Fil 2 → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ,
    (∀ g : ↥(GK K), P.actQ (g : GQ l) x =
      algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) →
    Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) := by
  intro l _ P AI T K x _hxu hx1 hx2 c hc
  let Θ := GlobalTheory.ThetaTie.thetaL T
  have hF : ∀ (a : ℤ) (y : P.R.BdR), y ∈ (P.PD K).Fil a ↔ y ∈ FilB P a := fun a y =>
    Set.ext_iff.1 (P.PD_Fil K (botExt l) a) y
  have hX1 : P.ιB x ∈ FilB P 1 := (hF 1 _).1 hx1
  have hX2 : P.ιB x ∉ FilB P 2 := fun h => hx2 ((hF 2 _).2 h)
  obtain ⟨s, hs, hts⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one T
  have hb0 : s * P.ιB x ∈ FilB P 0 := by
    have := FilB_mul hs hX1
    simpa using this
  have hθb : Θ.θ (s * P.ιB x) ≠ 0 := by
    intro h0
    have h1 : s * P.ιB x ∈ FilB P 1 := (Θ.θ_ker _ hb0).1 h0
    apply hX2
    have := FilB_mul (tD_mem (P := P)) h1
    have e : tD P * (s * P.ιB x) = P.ιB x := by
      rw [← mul_assoc]
      change P.ιB P.tB * s * P.ιB x = P.ιB x
      rw [hts, one_mul]
    rw [e] at this
    simpa using this
  let cv : ↥(GK K) → Om l := fun g => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)
  let χv : ↥(GK K) → Om l := fun g => algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])
  let uv : ↥(GK K) → Om l := fun g => cv g * (χv g)⁻¹
  have hK0 : ∀ z : ↥(K0 K), P.ιB (algebraMap ↥(K0 K) P.R.B z) = oB P (z : Om l) := fun z =>
    GlobalTheory.LocIota.ιB_algebraMap_Kur P (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) z)
  have hqo : ∀ z : ℚ_[l], qB P z = oB P (algebraMap ℚ_[l] (Om l) z) := fun z =>
    IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR z
  have hact : ∀ g : ↥(GK K), P.actQdR (g : GQ l) (s * P.ιB x) = oB P (uv g) * (s * P.ιB x) := by
    intro g
    have hX : P.actQdR (g : GQ l) (P.ιB x) = oB P (cv g) * P.ιB x := by
      rw [← ιB_act, hc g, map_mul, hK0]
    have ht := act_tD (P := P) (g : GQ l)
    have h1 : P.actQdR (g : GQ l) (tD P) * P.actQdR (g : GQ l) s = 1 := by
      rw [← map_mul]
      change P.actQdR (g : GQ l) (P.ιB P.tB * s) = 1
      rw [hts, map_one]
    have h2 : qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * qB P (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (Units.ne_zero _), map_one]
    have hts' : tD P * s = 1 := hts
    rw [ht] at h1
    have hs' : P.actQdR (g : GQ l) s = qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * s := by
      linear_combination (qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * s) * h1
        - P.actQdR (g : GQ l) s * h2
        - (P.actQdR (g : GQ l) s * qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹
            * qB P (P.χQ (g : GQ l) : ℚ_[l])) * hts'
    have hu : oB P (uv g) = oB P (cv g) * qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ := by
      rw [hqo, map_inv₀]
      change oB P (cv g * (χv g)⁻¹) = _
      rw [map_mul]
    rw [map_mul, hs', hX, hu]
    ring
  have hl : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hθpos : 0 < ‖Θ.θ (s * P.ιB x)‖ := norm_pos_iff.2 hθb
  have htv : Tendsto (fun g : ↥(GK K) => (g : GQ l)) (𝓝 1) (𝓝 1) := by
    simpa using continuous_subtype_val.tendsto (1 : ↥(GK K))
  have huv : Tendsto uv (𝓝 1) (𝓝 1) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hε hθpos) hl
    have hev := (bounded_and_eventually_sub_mem_Lat l P AI T _ hb0 1 n).2
    filter_upwards [htv.eventually hev] with g hg
    rw [hact g] at hg
    have e : oB P (uv g) * (s * P.ιB x) - s * P.ιB x = oB P (uv g - 1) * (s * P.ιB x) := by
      rw [map_sub, map_one]; ring
    rw [e] at hg
    have h3 := norm_th_le_of_mem_Lat Θ hg
    rw [Θ.θ_mul _ (oB_mem T _) _ hb0, Θ.θ_Om, norm_mul, PadicComplex.norm_extends] at h3
    rw [dist_eq_norm]
    have h4 : ‖uv g - 1‖ * ‖Θ.θ (s * P.ιB x)‖ < ε * ‖Θ.θ (s * P.ιB x)‖ := h3.trans_lt hn
    exact lt_of_mul_lt_mul_right h4 hθpos.le
  have hqc : Continuous (algebraMap ℚ_[l] (Om l)) :=
    (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] (Om l))
      (fun z => PadicAlgCl.norm_extends (p := l) z)).continuous
  have hχ : Tendsto χv (𝓝 1) (𝓝 1) := by
    have hcont : Continuous χv :=
      hqc.comp ((GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val)
    simpa [χv] using hcont.tendsto 1
  have hcv1 : Tendsto cv (𝓝 1) (𝓝 1) := by
    have := huv.mul hχ
    rw [mul_one] at this
    refine this.congr fun g => ?_
    have hne : χv g ≠ 0 := by
      simp only [χv, ne_eq, map_eq_zero]
      exact Units.ne_zero _
    exact inv_mul_cancel_right₀ hne (cv g)
  have hmul : ∀ g h : ↥(GK K), cv (g * h) = cv g * cv h := by
    intro g h
    simp [cv, map_mul]
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have t1 : Tendsto (fun g : ↥(GK K) => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    simpa using (continuous_const_mul g₀⁻¹).tendsto g₀
  have t2 := (hcv1.comp t1).const_mul (cv g₀)
  rw [mul_one] at t2
  refine t2.congr fun g => ?_
  change cv g₀ * cv (g₀⁻¹ * g) = cv g
  rw [← hmul, mul_inv_cancel_left]

end GlobalTheory.LtCharCont
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterOfBcrisUnitFilOneStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_galois_character_of_bcris_unit_fil_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → P.ιB x ∈ (P.PD K).Fil 1 → P.ιB x ∉ (P.PD K).Fil 2 → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) := by
  first | exact @GlobalTheory.LtCharCont.continuous_char_of_act | exact GlobalTheory.LtCharCont.continuous_char_of_act | (intros; apply GlobalTheory.LtCharCont.continuous_char_of_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedCharacterOfEigenUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedCharacterOfEigenUnit
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory

theorem absoluteGalois_fixes_unramified_in_crystalline {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (g : ↥(GK K))
    (a : ↥(K0 K)) : P.actQ (g : GQ l) (algebraMap ↥(K0 K) P.R.B a) = algebraMap ↥(K0 K) P.R.B a := by
  have hfix : (g : GQ l) ((a : Om l)) = (a : Om l) :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 (a : Om l) a.2.1
  exact P.actQ_Kur (g : GQ l) (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) a)
    (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) a) hfix

theorem ltChar_hom : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (x : P.R.B), IsUnit x → (∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x) → ∃ c : ↥(GK K) →* (↥(K0 K))ˣ, ∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x := by
  intro l _ P K x hx h
  rcases subsingleton_or_nontrivial P.R.B with hB | hB
  · exact ⟨1, fun g => Subsingleton.elim _ _⟩
  · have hinj : Function.Injective (algebraMap ↥(K0 K) P.R.B) := (algebraMap ↥(K0 K) P.R.B).injective
    have hcan : ∀ a b : ↥(K0 K), algebraMap ↥(K0 K) P.R.B a * x = algebraMap ↥(K0 K) P.R.B b * x → a = b :=
      fun a b e => hinj (hx.mul_left_injective e)
    let f : ↥(GK K) → ↥(K0 K) := fun g : ↥(GK K) => Classical.choose (h g)
    have hf : ∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B (f g) * x :=
      fun g => Classical.choose_spec (h g)
    let F : ↥(GK K) →* ↥(K0 K) :=
      { toFun := f
        map_one' := by
          apply hcan
          rw [← hf, map_one, one_mul, OneMemClass.coe_one, map_one, AlgEquiv.one_apply]
        map_mul' := by
          intro g g'
          apply hcan
          rw [← hf]
          have e1 : P.actQ ((g * g' : ↥(GK K)) : GQ l) x = P.actQ (g : GQ l) (P.actQ (g' : GQ l) x) := by
            rw [Subgroup.coe_mul, map_mul, AlgEquiv.mul_apply]
          rw [e1, hf g', map_mul, absoluteGalois_fixes_unramified_in_crystalline, hf g, map_mul]
          ring }
    refine ⟨F.toHomUnits, fun g => ?_⟩
    rw [MonoidHom.coe_toHomUnits]
    exact hf g

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedCharacterOfEigenUnitStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_character_of_eigen_unit : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (x : P.R.B), IsUnit x → (∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x) → ∃ c : ↥(GK K) →* (↥(K0 K))ˣ, ∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x := by
  first | exact @GlobalTheory.ltChar_hom | exact GlobalTheory.ltChar_hom | (intros; apply GlobalTheory.ltChar_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineCharJumpOne
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LTChar

theorem exists_crystalline_char_jump_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ IsCrys (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) ∧ ∀ τ b, multV (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  intro l _ P AI hT K LL hA τ₀
  haveI := (P.PD K).finK₀
  have hn : 0 < finrank ℚ_[l] ↥(K0 K) := Module.finrank_pos
  obtain ⟨x, hxu, hxφ, hx1, hx2, hxj⟩ := GlobalTheory.T.exists_cyclotomic_period_local_prime l P AI hT K _ hn
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_unramified_character_of_eigen_unit l P K x hxu (GlobalTheory.T.galois_periodRatio_mem_unramified_alt l P AI hT K x hxu hxφ hx1 hx2 hxj)
  have hcont := GlobalTheory.T.continuous_galois_character_of_bcris_unit_fil_one l P AI hT K x hxu hx1 hx2 c hc
  obtain ⟨χ, hχc, hχ⟩ := GlobalTheory.T.exists_continuous_integralUnitChar_of_char l K LL τ₀ c hcont
  exact ⟨χ, hχc, GlobalTheory.T.crystalline_character_jump_one_at_embedding l P AI hT K LL hA τ₀ x hxu hxφ hx1 hx2 hxj c hc _ hχc hχ⟩

end GlobalTheory.LTChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineCharJumpOneStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystalline_char_jump_one_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), CaseA K LL → ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ IsCrys (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) ∧ ∀ τ b, multV (P.PD K) (charRep ((Units.map (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom).comp χ)) τ b = if b = (if τ = τ₀ then 1 else 0) then 1 else 0 := by
  first | exact @GlobalTheory.LTChar.exists_crystalline_char_jump_one | exact GlobalTheory.LTChar.exists_crystalline_char_jump_one | (intros; apply GlobalTheory.LTChar.exists_crystalline_char_jump_one <;> assumption)
end
