module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSum
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Module

namespace GlobalTheory.NL.PhiD

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_letter (τ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ ↔ (∀ g, actVB PD ρ g x = x) ∧
      ∀ c : K₀, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x = τ c • x := by
  simp [DcrisL, Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem phi_injective : Function.Injective (φVB PD (LL := LL) (V := V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V) PD.φ.toLinearMap PD.φ_inj

theorem iota_injective : Function.Injective (ιV PD (LL := LL) (V := V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V)
    (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

theorem phi_mem (τ τ' : K₀ →ₐ[Qp] LL) (h : ∀ c, τ' c = τ (PD.σ c)) :
    ∀ x ∈ DcrisL PD ρ τ', φVB PD (LL := LL) x ∈ DcrisL PD ρ τ := by
  have h1 : ∀ g x, φVB PD (LL := LL) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, φVB, PD.φ_comm]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 : ∀ (c : K₀) (x : V ⊗[Qp] B),
      φVB PD (LL := LL) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVB, φVB, PD.φ_K₀]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  intro x hx
  rw [mem_letter] at hx ⊢
  refine ⟨fun g => by rw [← h1, hx.1], fun c => ?_⟩
  obtain ⟨c, rfl⟩ := PD.σ_bij.2 c
  rw [← h2, hx.2, map_smul, h]

theorem iSupIndep_letter : iSupIndep fun τ : K₀ →ₐ[Qp] LL => DcrisL PD ρ τ := by
  have h := iSupIndep.iInf
    (fun (c : K₀) (a : LL) => Module.End.eigenspace
      (mulVB (Qp := Qp) (K₀ := K₀) (B := B) (V := V) (LL := LL) c) a)
    (fun c => Module.End.eigenspaces_iSupIndep _)
  have h' := h.comp (f := fun τ : K₀ →ₐ[Qp] LL => (τ : K₀ → LL)) DFunLike.coe_injective
  refine h'.mono fun τ x hx => ?_
  simp only [Function.comp, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  exact ((mem_letter PD ρ τ x).1 hx).2

variable [FiniteDimensional LL V] [IsDomain B]

theorem phi_bijOn (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (hV : IsCrys PD ρ)
    (τ τ' : K₀ →ₐ[Qp] LL) (h : ∀ c, τ' c = τ (PD.σ c)) :
    Set.BijOn (φVB PD (LL := LL) (V := V)) (DcrisL PD ρ τ') (DcrisL PD ρ τ) := by
  haveI := GlobalTheory.Per.LetterDim.finite_Dcris PD ρ hV
  haveI : ∀ τ, FiniteDimensional LL ↥(DcrisL PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left
  refine ⟨phi_mem PD ρ τ τ' h, (phi_injective PD).injOn, fun y hy => ?_⟩
  have hi : Function.Injective ((φVB PD (LL := LL) (V := V)).restrict (phi_mem PD ρ τ τ' h)) :=
    fun x y hxy => Subtype.ext (phi_injective PD (congrArg Subtype.val hxy))
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV, GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV])).1 hi
  obtain ⟨x, hx⟩ := hs ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem iSup_letter (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (hV : IsCrys PD ρ) :
    (⨆ τ : K₀ →ₐ[Qp] LL, DcrisL PD ρ τ) = Dcris PD ρ := by
  classical
  haveI := PD.finK₀
  haveI := GlobalTheory.Per.LetterDim.finite_Dcris PD ρ hV
  haveI : ∀ τ, FiniteDimensional LL ↥(DcrisL PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left
  refine Submodule.eq_of_le_of_finrank_eq (iSup_le fun τ => inf_le_left) ?_
  have hinj := (iSupIndep_letter PD ρ).dfinsupp_lsum_injective
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hinj]
  change finrank LL (DirectSum _ fun τ => ↥(DcrisL PD ρ τ)) = _
  rw [Module.finrank_directSum]
  simp only [GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, hc]
  exact hV.symm

end General

theorem phi_letters : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ i : Let K, Set.BijOn (φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) (Di (HW l) h T (i - 1)) (Di (HW l) h T i)) ∧ (⨆ i : Let K, Di (HW l) h T i) = Dcris ((D.loc l).PD K) T.ρ ∧ iSupIndep (fun i : Let K => Di (HW l) h T i) ∧ Function.Injective (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  intro D HW l _ K s LL h W T hV
  haveI := GlobalTheory.RegularRing.isDomain_of_tied (D.locT l) K
  have hc : Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥(K0 K) := by
    rw [← Nat.card_eq_of_bijective _ W.emb_bij, Nat.card_zmod]
  refine ⟨fun i => phi_bijOn _ T.ρ hc hV _ _ fun c => ?_, ?_,
    (iSupIndep_letter ((D.loc l).PD K) T.ρ).comp W.emb_bij.1, iota_injective _⟩
  · have := AlgHom.congr_fun (W.emb_σ (i - 1)) c
    rw [sub_add_cancel] at this
    exact this.symm
  · rw [← iSup_letter _ T.ρ hc hV]
    exact W.emb_bij.2.iSup_comp (fun τ => DcrisL ((D.loc l).PD K) T.ρ τ)

end GlobalTheory.NL.PhiD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSumStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ i : Let K, Set.BijOn (φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) (Di (HW l) h T (i - 1)) (Di (HW l) h T i)) ∧ (⨆ i : Let K, Di (HW l) h T i) = Dcris ((D.loc l).PD K) T.ρ ∧ iSupIndep (fun i : Let K => Di (HW l) h T i) ∧ Function.Injective (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  first | exact @GlobalTheory.NL.PhiD.phi_letters | exact GlobalTheory.NL.PhiD.phi_letters | (intros; apply GlobalTheory.NL.PhiD.phi_letters <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMulLeftDvr
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem continuous_of_mul_left_dvr {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [TopologicalSpace X]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) {a : O} (ha : a ≠ 0) {f : X → O}
    (hf : Continuous fun x => a * f x) : Continuous f := by
  obtain ⟨hopen, hbasis⟩ := isAdic_iff.1 hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hm := hϖ.maximalIdeal_eq
  rw [continuous_iff_continuousAt]
  intro x0
  have h0 : Filter.Tendsto (fun x => f x - f x0) (nhds x0) (nhds 0) := by
    intro s hs
    obtain ⟨n, hn⟩ := hbasis s hs
    have h1 : Continuous fun x => (u : O) * ϖ ^ k * f x - (u : O) * ϖ ^ k * f x0 := hf.sub continuous_const
    have h2 := (h1.isOpen_preimage _ (hopen (k + n))).mem_nhds (x := x0) (by simp)
    rw [Filter.mem_map]
    filter_upwards [h2] with x hx
    apply hn
    simp only [Set.mem_preimage, SetLike.mem_coe, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
    rw [← mul_sub, pow_add, mul_assoc, u.isUnit.dvd_mul_left, mul_dvd_mul_iff_left (pow_ne_zero k hϖ.ne_zero)] at hx
    exact hx
  have := h0.add_const (f x0)
  simpa [ContinuousAt] using this

theorem continuous_of_coeff_dvr {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [TopologicalSpace X]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) {n : ℕ} {M : X → Matrix (Fin n) (Fin n) O} (hM : Continuous M)
    (L : (Fin n → FractionRing O) →ₗ[FractionRing O] FractionRing O) (v : Fin n → FractionRing O) {f : X → O}
    (hf : ∀ x, algebraMap O (FractionRing O) (f x) = L (((M x).map (algebraMap O (FractionRing O))).mulVec v)) :
    Continuous f := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : Fin n × Fin n => L (Pi.single p.1 1) * v p.2)
  choose d hd using hb
  refine continuous_of_mul_left_dvr hO (nonZeroDivisors.coe_ne_zero b) ?_
  have : (fun x => (b : O) * f x) = fun x => ∑ p, ∑ q, d (p, q) * M x p q := by
    funext x
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, hf, LinearMap.pi_apply_eq_sum_univ L]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hd, Finset.mul_sum, Matrix.mulVec, dotProduct, Matrix.map_apply, smul_eq_mul,
      Finset.sum_mul, Algebra.smul_def]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have : (fun j => if p = j then (1 : FractionRing O) else 0) = Pi.single p 1 := by
      funext j; simp [Pi.single_apply, eq_comm]
    rw [this]; ring
  rw [this]
  fun_prop

theorem mapM_twistM_mulVec {O S Γ : Type} [CommRing O] [CommRing S] [Group Γ] {k : ℕ} (f : O →+* S)
    (M : Γ →* Matrix (Fin k) (Fin k) O) (χ : Γ →* Oˣ) (g : Γ) (v : Fin k → S) :
    (mapM f (twistM M χ) g).mulVec v = f (χ g : O) • (mapM f M g).mulVec v := by
  rw [← Matrix.smul_mulVec]
  congr 1
  ext p q
  simp [mapM, twistM]

theorem subTw_blocks : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r → ∀ (π : D.nd.X i) (e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i))), (∀ g u, e ((mapM (toK D.nd i) (rO D.nd i r π) g).mulVec u) = ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec (e u).1, fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)) → ∀ Xs : Set (D.nd.X i), π ∈ Xs → SubTw i r Xs (WpO D.nd i ρ π) ∧ ∀ c ∈ Finset.Icc 1 D.R.t, SubTw i r Xs (chiRatO D.nd i c) := by
  intro D i r ρ hr π e he Xs hπ
  have hO := D.nd.O_adic i
  have hrc : Continuous fun g => rO D.nd i r π g := (hr π).1
  have hχ : ∀ c, Continuous fun g => ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) := fun c => D.nd.chi_cont i c
  have hχi : Continuous fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
    have := (hχ 1).comp (continuous_inv (G := GE D.nd))
    refine this.congr fun g => ?_
    simp
  have hρc : Continuous fun g => rhoO D.nd i ρ π g := by
    refine continuous_matrix fun p q => ?_
    refine continuous_of_coeff_dvr hO hrc
      ((LinearMap.proj p).comp ((LinearMap.fst _ _ _).comp e.toLinearMap)) (e.symm (Pi.single q 1, 0)) fun g => ?_
    have := congrArg (fun z => z.1 p) (he g (e.symm (Pi.single q 1, 0)))
    simp only [LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one] at this
    exact this.symm
  refine ⟨⟨hχi.smul hρc, π, hπ, e.symm.toLinearMap.comp (LinearMap.inl _ _ _),
    e.symm.injective.comp LinearMap.inl_injective, fun g v => ?_⟩, fun c hc => ?_⟩
  · rw [WpO, rTwO, mapM_twistM_mulVec, mapM_twistM_mulVec, map_smul]
    congr 1
    apply e.injective
    rw [he]
    simp
    rfl
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    let c' : Fin D.R.t := ⟨c - 1, by omega⟩
    have hcc : (c' : ℕ) + 1 = c := by simp only [c']; omega
    refine ⟨?_, π, hπ, e.symm.toLinearMap.comp ((LinearMap.inr _ _ _).comp
      ((LinearMap.single _ (fun _ => KK D.nd i) c').comp (LinearMap.proj 0))), ?_, fun g v => ?_⟩
    · have : Continuous fun g => (((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) *
          (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) :=
        ((hχ c).mul hχi).smul continuous_const
      exact this
    · intro v w h
      have h1 := congrArg (fun z => (e z).2 c') h
      funext j
      rw [Subsingleton.elim j 0]
      simpa using h1
    · rw [chiRatO, rTwO, mapM_twistM_mulVec, mapM_twistM_mulVec, map_smul, MonoidHom.mul_apply, Units.val_mul,
        map_mul, mul_comm, mul_smul]
      congr 1
      apply e.injective
      rw [he, map_smul]
      ext j
      · simp
      · by_cases hj : j = c'
        · subst hj
          simp [hcc, mapM, Algebra.smul_def]
        · simp [hj]

end GlobalTheory.Pass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocks
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem stepSub_holds : StepSub := by
  intro D i r ρ hr π hd Xs hπ
  obtain ⟨e, he⟩ := hd
  exact subTw_blocks D i r ρ hr π e he Xs hπ

end GlobalTheory.Pass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocksStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_galois_rep_character_blocks : StepSub := by
  first | exact @GlobalTheory.Pass.stepSub_holds | exact GlobalTheory.Pass.stepSub_holds | (intros; apply GlobalTheory.Pass.stepSub_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopologicalBasisBasicFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopologicalBasisBasicFacts
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.TopBasis

variable {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}

theorem smul_top_ideal (J : Ideal A) : (J • ⊤ : Submodule A A) = J := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem sub_mem_iff (J : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD ((J ^ n • ⊤ : Submodule A A))] ↔ x - y ∈ J ^ n := by
  rw [SModEq.sub_mem, smul_top_ideal]

theorem eq_zero_of_c (TB : TopBasis s I ι) (x : A) (h : ∀ i, TB.c i x = 0) : x = 0 := by
  have hH : IsHausdorff (I.map s) A := TB.complete.toIsHausdorff
  refine hH.haus x fun n => ?_
  rw [sub_mem_iff, ← Ideal.map_pow]
  have := TB.approx x n ∅ (fun i _ => by rw [h i]; exact zero_mem _)
  simpa using this

theorem c_s (TB : TopBasis s I ι) (i : ι) (a : S) (x : A) : TB.c i (x * s a) = a * TB.c i x := by
  rw [mul_comm]; exact TB.c_mul i a x

theorem coeff_unitIndex_baseMap (TB : TopBasis s I ι) (a : S) : TB.c TB.i₀ (s a) = a := by
  have := TB.c_mul TB.i₀ a (TB.b TB.i₀)
  rw [TB.b_i₀, mul_one, ← TB.b_i₀, TB.c_self, mul_one] at this
  exact this

theorem injective (TB : TopBasis s I ι) : Function.Injective s := fun a b h => by
  rw [← coeff_unitIndex_baseMap TB a, h, coeff_unitIndex_baseMap]

theorem c_mem_of_mem_map (TB : TopBasis s I ι) (L : Ideal S) (x : A) (hx : x ∈ L.map s) (i : ι) :
    TB.c i x ∈ L := by
  let J : Ideal A :=
    { carrier := {y | ∀ a : A, ∀ i, TB.c i (a * y) ∈ L}
      add_mem' := fun {y z} hy hz a i => by rw [mul_add, map_add (f := _)]; exact L.add_mem (hy a i) (hz a i)
      zero_mem' := fun a i => by rw [mul_zero, map_zero]; exact L.zero_mem
      smul_mem' := fun b y hy a i => by rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b) i }
  have hle : L.map s ≤ J := Ideal.map_le_iff_le_comap.2 fun y hy a i => by
    show TB.c i (a * s y) ∈ L
    rw [c_s]; exact L.mul_mem_right _ hy
  have := hle hx 1 i
  rwa [one_mul] at this

theorem mem_map_iff (TB : TopBasis s I ι) (L : Ideal S) (n : ℕ) (hL : I ^ n ≤ L) (x : A) :
    x ∈ L.map s ↔ ∀ i, TB.c i x ∈ L := by
  refine ⟨fun hx i => c_mem_of_mem_map TB L x hx i, fun h => ?_⟩
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset → TB.c i x ∈ I ^ n := fun i hi => by
    simpa using hi
  have h1 := Ideal.map_mono (f := s) hL (TB.approx x n _ hF)
  have h2 : ∑ i ∈ (TB.fin x n).toFinset, s (TB.c i x) * TB.b i ∈ L.map s :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (h i))
  simpa using Ideal.add_mem _ h1 h2

open Classical in
theorem c_sum (TB : TopBasis s I ι) (z : ι → S) (F : Finset ι) (i : ι) :
    TB.c i (∑ j ∈ F, s (z j) * TB.b j) = if i ∈ F then z i else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [TB.c_mul]
  split_ifs with hi
  · rw [Finset.sum_eq_single i (fun j _ hj => by rw [TB.c_ne i j (Ne.symm hj), mul_zero])
      (fun h => (h hi).elim), TB.c_self, mul_one]
  · exact Finset.sum_eq_zero fun j hj => by
      rw [TB.c_ne i j (fun e => hi (e ▸ hj)), mul_zero]

theorem exists_c_eq (TB : TopBasis s I ι) (hS : IsHausdorff I S) (z : ι → S)
    (hz : ∀ n : ℕ, {i | z i ∉ I ^ n}.Finite) : ∃ x, ∀ i, TB.c i x = z i := by
  classical
  let F : ℕ → Finset ι := fun n => (hz n).toFinset
  have hFm : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} hmn i hi => by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun h => hi (Ideal.pow_le_pow_right hmn h)
  have hFc : ∀ n i, i ∉ F n → z i ∈ I ^ n := fun n i hi => by
    simpa [F] using hi
  let f : ℕ → A := fun n => ∑ i ∈ F n, s (z i) * TB.b i
  have hP : IsPrecomplete (I.map s) A := TB.complete.toIsPrecomplete
  obtain ⟨x, hx⟩ := hP.prec' f (fun {m n} hmn => by
    rw [sub_mem_iff, ← Ideal.map_pow, ← neg_mem_iff, neg_sub]
    show (∑ i ∈ F n, s (z i) * TB.b i) - ∑ i ∈ F m, s (z i) * TB.b i ∈ _
    rw [← Finset.sum_sdiff (hFm hmn), add_sub_cancel_right]
    exact Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem s (hFc m i (Finset.mem_sdiff.1 hi).2)))
  refine ⟨x, fun i => ?_⟩
  rw [← sub_eq_zero]
  refine hS.haus _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_top_ideal]
  have h1 : TB.c i (f n - x) ∈ I ^ n := by
    have := (sub_mem_iff _ n _ _).1 (hx n)
    rw [← Ideal.map_pow] at this
    exact c_mem_of_mem_map TB _ _ this i
  have h2 : TB.c i (f n) - z i ∈ I ^ n := by
    show TB.c i (∑ j ∈ F n, s (z j) * TB.b j) - z i ∈ I ^ n
    rw [c_sum]
    split_ifs with hi
    · rw [sub_self]; exact zero_mem _
    · rw [zero_sub, neg_mem_iff]; exact hFc n i hi
  have := Ideal.sub_mem _ h2 h1
  rw [map_sub] at this
  simpa using this

theorem map_nonZeroDivisors (TB : TopBasis s I ι) (a : S) (ha : a ∈ nonZeroDivisors S) :
    s a ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun x hx => eq_zero_of_c TB x fun i => ?_, fun x hx => eq_zero_of_c TB x fun i => ?_⟩
  · have := congrArg (TB.c i) hx
    rw [TB.c_mul, map_zero] at this
    first
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ (by rw [mul_comm]; exact this)
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ (by rw [mul_comm]; exact this)
  · have := congrArg (TB.c i) hx
    rw [c_s, map_zero] at this
    first
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ (by rw [mul_comm]; exact this)
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ (by rw [mul_comm]; exact this)

end GlobalTheory.BSP.TopBasis

theorem GlobalTheory.BSP.TopBasis.basic_facts : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι), IsHausdorff I S → (∀ x, (∀ i, TB.c i x = 0) → x = 0) ∧ Function.Injective s ∧ (∀ (L : Ideal S) (n : ℕ), I ^ n ≤ L → ∀ x, x ∈ L.map s ↔ ∀ i, TB.c i x ∈ L) ∧ (∀ z : ι → S, (∀ n : ℕ, {i | z i ∉ I ^ n}.Finite) → ∃ x, ∀ i, TB.c i x = z i) ∧ ∀ a ∈ nonZeroDivisors S, s a ∈ nonZeroDivisors A := by
  intro S A _ _ s I ι TB hS
  exact ⟨TB.eq_zero_of_c, TB.injective, TB.mem_map_iff, TB.exists_c_eq hS, TB.map_nonZeroDivisors⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopologicalBasisBasicFactsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalBasis_basic_facts : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι), IsHausdorff I S → (∀ x, (∀ i, TB.c i x = 0) → x = 0) ∧ Function.Injective s ∧ (∀ (L : Ideal S) (n : ℕ), I ^ n ≤ L → ∀ x, x ∈ L.map s ↔ ∀ i, TB.c i x ∈ L) ∧ (∀ z : ι → S, (∀ n : ℕ, {i | z i ∉ I ^ n}.Finite) → ∃ x, ∀ i, TB.c i x = z i) ∧ ∀ a ∈ nonZeroDivisors S, s a ∈ nonZeroDivisors A := by
  first | exact @GlobalTheory.BSP.TopBasis.basic_facts | exact GlobalTheory.BSP.TopBasis.basic_facts | (intros; apply GlobalTheory.BSP.TopBasis.basic_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeCoefficientsOfPadicIntLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeCoefficientsOfPadicIntLattices
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LocalSituation TensorProduct Module GlobalTheory.Per GlobalTheory.Prism

noncomputable section
namespace GlobalTheory.BSCoeff

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

section Dcris

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

theorem Dcris_resQ : Dcris (P.PD K) (resQ ρ) = (Dcris (P.PD K) ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [Dcris, sub_eq_zero, actVB_resQ]

theorem isCrys_resQ_iff [FiniteDimensional ℚ_[l] LL] : IsCrys (P.PD K) (resQ ρ) ↔ IsCrys (P.PD K) ρ := by
  have e : finrank ℚ_[l] ↥(Dcris (P.PD K) (resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dcris (P.PD K) ρ) := by
    rw [Dcris_resQ, finrank_mul_finrank]
    rfl
  rw [IsCrys, IsCrys, e, ← finrank_mul_finrank ℚ_[l] LL V, mul_left_comm]
  exact Nat.mul_right_inj finrank_pos.ne'

end Dcris

variable {l : ℕ} [Fact l.Prime]

set_option synthInstance.maxHeartbeats 400000

theorem algebraMap_OL (LL : FinExt l) (z : ℤ_[l]) :
    algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z) = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l]) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]; rfl

theorem finite_OL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

variable {G : Type} [Group G] [TopologicalSpace G]

@[reducible] def zlV (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) : Module ℤ_[l] T.V :=
  Module.compHom T.V (algebraMap ℤ_[l] ↥(OL LL))

theorem modO_smul (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (o : ↥(OL LL)) (w : T.V) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ T.modO.toSMul) o w = algebraMap ↥(OL LL) ↥LL.1 o • w := by
  letI := T.modO
  haveI := T.towO
  exact (algebraMap_smul ↥LL.1 o w).symm

theorem zlV_smul (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (z : ℤ_[l]) (w : T.V) :
    (zlV LL T).toSMul.smul z w = (z : ℚ_[l]) • w := by
  change @HSMul.hSMul _ _ _ (@instHSMul _ _ T.modO.toSMul) (algebraMap ℤ_[l] ↥(OL LL) z) w = _
  rw [modO_smul, algebraMap_OL, algebraMap_smul]

theorem zlV_tower (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    letI := zlV LL T
    IsScalarTower ℤ_[l] ℚ_[l] T.V := by
  letI := zlV LL T
  refine ⟨fun z q v => ?_⟩
  change (z • q) • v = (zlV LL T).toSMul.smul z (q • v)
  rw [zlV_smul, smul_smul]
  rfl

theorem finite_compHom {O M : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] :
    letI := Module.compHom M (algebraMap ℤ_[l] O)
    Module.Finite ℤ_[l] M := by
  letI := Module.compHom M (algebraMap ℤ_[l] O)
  haveI : IsScalarTower ℤ_[l] O M := ⟨fun c a x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  exact Module.Finite.trans O M

theorem denom (LL : FinExt l) (c : ↥LL.1) :
    ∃ (z : ℚ_[l]) (a : ↥(OL LL)), c = z • algebraMap ↥(OL LL) ↥LL.1 a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have halg : IsAlgebraic ℤ_[l] c :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).mpr (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨z, hz, hint⟩ := halg.exists_integral_multiple
  have hz' : (z : ℚ_[l]) ≠ 0 := fun h => hz (Subtype.ext h)
  refine ⟨(z : ℚ_[l])⁻¹, ⟨z • c, hint⟩, ?_⟩
  change c = (z : ℚ_[l])⁻¹ • ((z : ℚ_[l]) • c)
  rw [smul_smul, inv_mul_cancel₀ hz', one_smul]

end GlobalTheory.BSCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff GlobalTheory.BSCoeff


set_option maxHeartbeats 1600000 in
theorem bhattScholze_coeff : GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.BhattScholzeCrystallineLattices := by
  intro h l _ K P₀ e hA
  obtain ⟨h1, h2⟩ := h l K P₀ e hA
  refine ⟨fun P AI hS LL T hC => ?_, h2⟩
  letI := zlV LL T
  haveI := zlV_tower LL T
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : FiniteDimensional ℚ_[l] T.V := Module.Finite.trans ↥LL.1 T.V
  haveI : IsModuleTopology ℚ_[l] ↥LL.1 := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology ℚ_[l] T.V := isModuleTopology_of_tower ℚ_[l] ↥LL.1 T.V
  let TZ : Submodule ℤ_[l] T.V :=
    { carrier := (T.L.T : Set T.V)
      add_mem' := fun ha hb => T.L.T.add_mem ha hb
      zero_mem' := T.L.T.zero_mem
      smul_mem' := fun z v hv => T.L.T.smul_mem (algebraMap ℤ_[l] ↥(OL LL) z) hv }
  haveI := finite_OL LL
  haveI : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  have hfin' := finite_compHom (l := l) (O := ↥(OL LL)) (M := ↥T.L.T)
  haveI hfin : Module.Finite ℤ_[l] ↥TZ := hfin'
  have hz : ∀ (z : ℤ_[l]) (v : T.V), z • v = (z : ℚ_[l]) • v := fun z v => zlV_smul LL T z v
  have htf : Module.IsTorsionFree ℤ_[l] ↥TZ := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro z x hx
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    right
    have h' : (z : ℚ_[l]) • (x : T.V) = 0 := by
      rw [← hz]; exact congrArg Subtype.val hx
    have hq : (z : ℚ_[l]) ≠ 0 := fun h0 => hz0 (PadicInt.coe_eq_zero.1 h0)
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left hq)
  have hspan : Submodule.span ℚ_[l] (TZ : Set T.V) = ⊤ := by
    let W : Submodule ↥LL.1 T.V :=
      { carrier := (Submodule.span ℚ_[l] (TZ : Set T.V) : Set T.V)
        add_mem' := fun ha hb => Submodule.add_mem _ ha hb
        zero_mem' := Submodule.zero_mem _
        smul_mem' := by
          intro a x hx
          induction hx using Submodule.span_induction with
          | mem t ht =>
            obtain ⟨q, o, rfl⟩ := denom LL a
            show (q • algebraMap ↥(OL LL) ↥LL.1 o) • t ∈ Submodule.span ℚ_[l] (TZ : Set T.V)
            rw [smul_assoc, ← modO_smul]
            exact Submodule.smul_mem _ q (Submodule.subset_span (T.L.T.smul_mem o ht))
          | zero => simp
          | add x y _ _ hx hy =>
            show a • (x + y) ∈ Submodule.span ℚ_[l] (TZ : Set T.V)
            rw [smul_add]; exact Submodule.add_mem _ hx hy
          | smul q x _ hx =>
            show a • (q • x) ∈ Submodule.span ℚ_[l] (TZ : Set T.V)
            rw [← algebraMap_smul ↥LL.1 q x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
            exact Submodule.smul_mem _ q hx }
    have hW : W = ⊤ := by
      rw [eq_top_iff, ← T.L.span, Submodule.span_le]
      intro t ht
      exact Submodule.subset_span ht
    rw [eq_top_iff]
    intro v _
    have : v ∈ W := hW ▸ Submodule.mem_top
    exact this
  let L : Lattice (O := ℤ_[l]) (resQ T.ρ) :=
    { T := TZ
      stable := fun g x hx => T.L.stable g x hx
      fg := Module.Finite.iff_fg.mp hfin
      free := Module.free_of_finite_type_torsion_free'
      span := hspan }
  obtain ⟨E, j, hR⟩ := h1 P AI hS T.V (resQ T.ρ) L (fun x => T.cont x) ((isCrys_resQ_iff P T.ρ).mpr hC)
  exact ⟨E, j, hR⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeCoefficientsOfPadicIntLatticesStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bhattScholze_coefficients_of_padicInt_lattices : GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.BhattScholzeCrystallineLattices := by
  first | exact @GlobalTheory.bhattScholze_coeff | exact GlobalTheory.bhattScholze_coeff | (intros; apply GlobalTheory.bhattScholze_coeff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictness
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictness
noncomputable section

namespace GlobalTheory.DRSubQuot

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.DRFil

theorem mem_of_invariant {G K B M ι : Type} [Field K] [CommRing B] [Algebra K B] (hF : IsField B)
    [AddCommGroup M] [Module B M] [Module K M] [IsScalarTower K B M]
    (σ : G → B → B) (ρ : G → M →+ M) (hρ : ∀ g b w, ρ g (b • w) = σ g b • ρ g w)
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * σ g b' = σ g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (hinv : ∀ b : B, (∀ g, σ g b = b) → ∃ c : K, algebraMap K B c = b)
    (F : ℤ → Submodule K B) (hFa : Antitone F) (h1 : (1 : B) ∉ F 1)
    (E : ℤ → AddSubgroup M) (hEa : Antitone E) (hEK : ∀ k (c : K) x, x ∈ E k → c • x ∈ E k)
    (k : ι → ℤ) (e : ι → M) (he : ∀ i, e i ∈ E (k i)) (hei : ∀ g i, ρ g (e i) = e i) (a : ℤ) (n : ℕ) :
    ∀ s : Finset ι, s.card = n → ∀ b : ι → B, (∀ i ∈ s, b i ∈ F (a - k i)) →
      (∀ g, ρ g (∑ i ∈ s, b i • e i) = ∑ i ∈ s, b i • e i) → ∑ i ∈ s, b i • e i ∈ E a := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn b hb hy
  by_cases hli : LinearIndepOn K e s
  · haveI := hF.isDomain
    haveI : Module.IsTorsionFree B M := ⟨fun r hr x y hxy => by
      obtain ⟨u, hu⟩ := hF.mul_inv_cancel hr.ne_zero
      have := congrArg (u • ·) hxy
      simpa only [smul_smul, mul_comm u r, hu, one_smul] using this⟩
    have hB := linearIndepOn_finset_iff.1
      (GlobalTheory.Per.FontaineBound.linearIndepOn_of_invariant σ ρ hρ hreg e hei s hli)
    refine (E a).sum_mem fun i hi => ?_
    obtain ⟨c, hc⟩ := hinv (b i) fun g => sub_eq_zero.1 (hB (fun j => σ g (b j) - b j) (by
      have := hy g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, hρ, hei] at this
      simp only [sub_smul, Finset.sum_sub_distrib, this, sub_self]) i hi)
    by_cases hc0 : c = 0
    · rw [← hc, hc0, map_zero, zero_smul]
      exact (E a).zero_mem
    rw [← hc, algebraMap_smul]
    refine hEK _ _ _ (hEa ?_ (he i))
    by_contra hlt
    apply h1
    have h2 := (F _).smul_mem c⁻¹ (hb i hi)
    rw [← hc, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc0, map_one] at h2
    exact hFa (by omega) h2
  · rw [linearIndepOn_finset_iff] at hli
    push Not at hli
    obtain ⟨κ, hκ, i₀, hi₀, hκ₀⟩ := hli
    obtain ⟨i, hi, hmin⟩ := (s.filter fun j => κ j ≠ 0).exists_min_image k
      ⟨i₀, Finset.mem_filter.2 ⟨hi₀, hκ₀⟩⟩
    obtain ⟨his, hκi⟩ := Finset.mem_filter.1 hi
    have hrel : e i = - ∑ j ∈ s.erase i, ((κ i)⁻¹ * κ j) • e j := by
      rw [← Finset.add_sum_erase s _ his] at hκ
      have := congrArg ((κ i)⁻¹ • ·) hκ
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hκi, one_smul, Finset.smul_sum, smul_zero] at this
      exact eq_neg_of_add_eq_zero_left this
    have heq : ∑ j ∈ s, b j • e j = ∑ j ∈ s.erase i, (b j - ((κ i)⁻¹ * κ j) • b i) • e j := by
      rw [← Finset.add_sum_erase s _ his]
      conv_lhs => rw [hrel]
      simp only [smul_neg, Finset.smul_sum, sub_smul, Finset.sum_sub_distrib, smul_assoc,
        smul_comm (b i)]
      abel
    rw [heq] at hy ⊢
    refine ih _ (hn ▸ Finset.card_erase_lt_of_mem his) _ rfl _ (fun j hj => ?_) hy
    have hjs := Finset.mem_of_mem_erase hj
    refine (F _).sub_mem (hb j hjs) ?_
    by_cases hj0 : κ j = 0
    · simp [hj0]
    · have := hmin j (Finset.mem_filter.2 ⟨hjs, hj0⟩)
      exact (F _).smul_mem _ (hFa (by omega) (hb i his))

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x))
include hf

theorem ext_mem_DdR {x : V ⊗[Qp] F} (hx : x ∈ DdR PD ρ) : ext Qp F f x ∈ DdR PD ρ' :=
  (mem_DdR PD _ _).2 fun g => by rw [act_ext PD ρ ρ' f hf, (mem_DdR PD _ _).1 hx]

theorem spans_of_surjective (hs : Function.Surjective f) (h : Spans PD ρ) : Spans PD ρ' := by
  intro y
  obtain ⟨a, ha⟩ := exists_mem_FilV PD (LL := LL) y
  obtain ⟨x, -, rfl⟩ := exists_ext_mem_FilV PD f hs ha
  obtain ⟨m, b, d, hd, rfl⟩ := h x
  exact ⟨m, b, fun i => ext Qp F f (d i), fun i => ext_mem_DdR PD ρ ρ' f hf (hd i), by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ext_mulR]⟩

theorem spans_of_injective [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    [FiniteDimensional LL V] [FiniteDimensional LL V'] (hF : IsField F)
    (hi : Function.Injective f) (h : Spans PD ρ') : Spans PD ρ := by
  have h1 : Spans PD ρ'.dual := spans_dual_of_spans PD ρ' ρ'.dual (Module.Dual.eval LL V') hF
    (fun g x y => by simp [Module.Dual.transpose_apply]) Function.bijective_id h
  have h2 : Spans PD ρ.dual := spans_of_surjective PD ρ'.dual ρ.dual f.dualMap
    (fun g x => by ext v; simp [Module.Dual.transpose_apply, hf]) (LinearMap.dualMap_surjective_of_injective hi) h1
  exact spans_dual_of_spans PD ρ.dual ρ LinearMap.id hF
    (fun g x y => by simp [Module.Dual.transpose_apply]) (Module.bijective_dual_eval LL V) h2

theorem strict_of_surjective (hF : IsField F) (hs : Function.Surjective f) (h : FilSpans PD ρ) (a : ℤ)
    (y : V' ⊗[Qp] F) (hy : y ∈ DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') a) :
    ∃ x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a, ext Qp F f x = y := by
  let φ : F →+* Module.End LL (V' ⊗[Qp] F) :=
    { toFun := fun b => mulR Qp F LL V' b
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul, tmul_add] }
  letI : Module F (V' ⊗[Qp] F) := Module.compHom _ φ
  letI : Module K (V' ⊗[Qp] F) := Module.compHom _ (algebraMap K F)
  haveI : IsScalarTower K F (V' ⊗[Qp] F) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hsm : ∀ (b : F) (x : V' ⊗[Qp] F), b • x = mulR Qp F LL V' b x := fun _ _ => rfl
  obtain ⟨x, hx, rfl⟩ := exists_ext_mem_FilV PD f hs hy.2
  obtain ⟨m, k, b, d, hd, rfl⟩ := h a x hx
  have hsum : ext Qp F f (∑ i, mulR Qp F LL V (b i) (d i)) = ∑ i, b i • ext Qp F f (d i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, ext_mulR, hsm]
  have hinv := (mem_DdR PD _ _).1 hy.1
  rw [hsum] at hinv ⊢
  exact mem_of_invariant (K := K) hF (fun g b => PD.actdR g b) (fun g => (actVdR PD ρ' g).toAddMonoidHom)
    (fun g b w => by
      change actVdR PD ρ' g (mulR Qp F LL V' b w) = mulR Qp F LL V' _ (actVdR PD ρ' g w)
      rw [← sm_one_tmul, act_sm, ← sm_one_tmul]
      simp)
    (GlobalTheory.Per.FontaineBound.frac_dR PD hF) PD.invdR PD.Fil (fil_antitone PD) (one_notMem_fil_one PD)
    (fun c => ((DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) c).map (ext Qp F f)).toAddSubgroup)
    (fun c c' hc => Submodule.map_mono (inf_le_inf_left _ (FilV_antitone PD hc)))
    (by
      rintro c κ _ ⟨z, hz, rfl⟩
      refine ⟨mulR Qp F LL V (algebraMap K F κ) z, ⟨mulR_mem_DdR PD ρ κ hz.1, ?_⟩, ext_mulR f _ z⟩
      have h0 : algebraMap K F κ ∈ PD.Fil 0 := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ _ PD.one_mem
      have := mulR_mem_FilV PD (LL := LL) h0 hz.2
      rwa [zero_add] at this)
    k (fun i => ext Qp F f (d i)) (fun i => ⟨d i, ⟨(hd i).1, (hd i).2.1⟩, rfl⟩)
    (fun g i => (mem_DdR PD _ _).1 (ext_mem_DdR PD ρ ρ' f hf (hd i).1) g) a _ Finset.univ rfl b
    (fun i _ => (hd i).2.2) hinv

end Generic

theorem deRham_sub_quot : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (f : V →ₗ[↥LL.1] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → IsDR (P.PD K) ρ' → IsDR (P.PD K) ρ) ∧ (Function.Surjective f → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (a : ℤ), ∀ y ∈ DdR (P.PD K) ρ' ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V') a, ∃ x ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) a, AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f hf
  have := K.2
  have := LL.2
  refine ⟨fun hi h => isDR_of_spans T K LL ρ (spans_of_injective (P.PD K) ρ ρ' f hf (isField_dR T) hi
    ((filSpans T K LL ρ' h).spans _)), fun hs h => ⟨isDR_of_spans T K LL ρ'
    (spans_of_surjective (P.PD K) ρ ρ' f hf hs ((filSpans T K LL ρ h).spans _)), fun a y hy => ?_⟩⟩
  exact strict_of_surjective (P.PD K) ρ ρ' f hf (isField_dR T) hs (filSpans T K LL ρ h) a y hy

end GlobalTheory.DRSubQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictnessStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_subrep_quotient_and_strictness : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (f : V →ₗ[↥LL.1] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → IsDR (P.PD K) ρ' → IsDR (P.PD K) ρ) ∧ (Function.Surjective f → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (a : ℤ), ∀ y ∈ DdR (P.PD K) ρ' ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V') a, ∃ x ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) a, AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y) := by
  first | exact @GlobalTheory.DRSubQuot.deRham_sub_quot | exact GlobalTheory.DRSubQuot.deRham_sub_quot | (intros; apply GlobalTheory.DRSubQuot.deRham_sub_quot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariants
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem Fits.invB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) : C.InvB := by
  intro K b hb
  set b' : P.R.B := T.eB.symm b with hb'
  have hfix : ∀ g : ↥(GK K), (P.PD K).actB g b' = b' := by
    intro g
    rw [P.PD_actB]
    apply T.eB.injective
    rw [T.actB, hb', RingEquiv.apply_symm_apply]
    exact hb g g.2
  obtain ⟨c, hc⟩ := (P.PD K).invB b' hfix
  refine ⟨IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c, (inf_le_left : K0 K ≤ K.1) c.2, ?_⟩
  rw [← hF.u]
  have : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) c) = b' := hc
  rw [this, hb', RingEquiv.apply_symm_apply]

theorem Fits.invdR {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) : C.InvdR := by
  intro K b hb
  set b' : P.R.BdR := T.eD.symm b with hb'
  have hfix : ∀ g : ↥(GK K), (P.PD K).actdR g b' = b' := by
    intro g
    rw [P.PD_actdR]
    apply T.eD.injective
    rw [T.actD, hb', RingEquiv.apply_symm_apply]
    exact hb g g.2
  obtain ⟨c, hc⟩ := (P.PD K).invdR b' hfix
  refine ⟨(c : Om l), c.2, ?_⟩
  rw [← hF.o]
  have : algebraMap (Om l) P.R.BdR (c : Om l) = b' := hc
  rw [this, hb', RingEquiv.apply_symm_apply]

theorem fits_inv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (C : Core l), Fits T C → C.InvB ∧ C.InvdR :=
  fun _ _ _ _ _ _ hF => ⟨hF.invB, hF.invdR⟩

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingCoreCrystallineDeRhamInvariantsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodRingCore_crystalline_deRham_invariants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → C.InvB ∧ C.InvdR := by
  first | exact @GlobalTheory.MemLoc.fits_inv | exact GlobalTheory.MemLoc.fits_inv | (intros; apply GlobalTheory.MemLoc.fits_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceAdmissibleOfGapConstantLe
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineIneq

theorem one_place_admissible_of_gap_constant_le : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.LiftingTheory.adm22 D HW F := by
  intro D HW F l _ K LL
  exact (GlobalTheory.Per.FontaineBound.fontaineLe_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL).1

end GlobalTheory.FontaineIneq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfield
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem delAt_unitary_triv {D : D7} (C : CharFrame D) (l : ℕ) : (C.delAt l).IsUnitary ∧ (C.delAt l).TrivOn D.host.F := by
  unfold CharFrame.delAt
  split_ifs
  · exact ⟨C.isDel'.unitary, C.isDel'.triv⟩
  · exact ⟨C.isDel.unitary, C.isDel.triv⟩

theorem toricLam0_unitary_trivOnMaxRealSubfield : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m),
    (Z.lam0 l j a).IsUnitary ∧ TrivOnF (Z.lam0 l j a) := by
  intro D Z h l j a
  have hd := delAt_unitary_triv Z.C l
  exact ⟨((Z.C.isMu0 j).unitary.mul hd.1).mul (h.aux a).unitary.inv,
    ((Z.C.isMu0 j).triv.mul hd.2).mul (h.aux a).triv.inv⟩

end GlobalTheory.LamTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfieldStatement
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lam0_isUnitary_and_trivOnF : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m), (Z.lam0 l j a).IsUnitary ∧ TrivOnF (Z.lam0 l j a) := by
  first | exact @GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield | exact GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield | (intros; apply GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield <;> assumption)
end
end
