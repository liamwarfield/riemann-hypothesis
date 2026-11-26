module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdHermitianFibreMeasureInvariantOrbitFiniteNonz
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqConstMulProdInnerOfSlotwise
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeLeSmoothVectors

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain

namespace GlobalTheory.Chain.InnerSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem theta_pureTensorO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) := by
  refine (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1 (fun k f hf => ⟨?_, rfl⟩) f hf P).1
  obtain ⟨τ, i, j⟩ := k
  exact GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hf)
    (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ _ hf)))

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end GlobalTheory.Chain.InnerSteps

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.PlaceVec

open GlobalTheory.AdelicLatMove

variable {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem frMapAdj_eq (x : WO S T) : frMapAdj S T βS βT x =
    ((βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) * ((x.map (toEAf D)).map (cF D))ᵀ * (T.gram.map (eToEAf D) * βT.val) := by
  have e : ((x.map (cA D))ᵀ).map (toEAf D) = ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => toEAf_cA _
  unfold frMapAdj
  rw [Matrix.map_mul, Matrix.map_mul, e]
  simp only [Matrix.mul_assoc]
  rfl

theorem frMapAdj_add (x y : WO S T) : frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
  have e : (((x + y).map (toEAf D)).map (cF D))ᵀ = ((x.map (toEAf D)).map (cF D))ᵀ + ((y.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => ((cF D).comp (toEAf D)).map_add (x j i) (y j i)
  rw [frMapAdj_eq, frMapAdj_eq, frMapAdj_eq, e, Matrix.mul_add, Matrix.add_mul]

theorem cF_cF_toEAf (a : AE D) : cF D (cF D (toEAf D a)) = toEAf D a := by
  rw [← toEAf_cA, ← toEAf_cA, GlobalTheory.DualPairCheck.cA_cA]

theorem sandwich_cancel {R : Type} [CommRing R] {m n : ℕ} (A A' G G' : Matrix (Fin m) (Fin m) R)
    (B B' H H' : Matrix (Fin n) (Fin n) R) (N : Matrix (Fin m) (Fin n) R) (hA : A * A' = 1) (hG : G * G' = 1)
    (hB : B * B' = 1) (hH : H * H' = 1) : (G * A) * ((A' * G') * N * (H * B)) * (B' * H') = N := by
  calc _ = (G * (A * A') * G') * N * (H * (B * B') * H') := by simp only [Matrix.mul_assoc]
    _ = N := by rw [hA, hB, Matrix.mul_one, Matrix.mul_one, hG, hH, Matrix.one_mul, Matrix.mul_one]

theorem gram_map_mul_inv : S.gram.map (eToEAf D) * (S.gram⁻¹).map (eToEAf D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit S),
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem frMapAdj_up : ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, IsIntM (x.map (toEAf D)) → IsIntM (k • frMapAdj S T βS βT x) := by
  obtain ⟨k, hk, h⟩ := exists_nsmul_mul_int ((βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) (T.gram.map (eToEAf D) * βT.val)
  refine ⟨k, hk, fun x hx => ?_⟩
  rw [frMapAdj_eq]
  exact h _ fun i j => cF_mem_int (hx j i)

theorem frMapAdj_down :
    ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, IsIntM (frMapAdj S T βS βT x) → IsIntM (k • x.map (toEAf D)) := by
  obtain ⟨k, hk, h⟩ := exists_nsmul_mul_int (S.gram.map (eToEAf D) * βS.val) ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))
  refine ⟨k, hk, fun x hx i j => ?_⟩
  have h1 := h _ hx
  rw [frMapAdj_eq, sandwich_cancel _ _ _ _ _ _ _ _ _ βS.mul_inv (gram_map_mul_inv S) βT.mul_inv
    (gram_map_mul_inv T)] at h1
  have h2 : cF D (k • cF D (toEAf D (x i j))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := cF_mem_int (h1 j i)
  rw [nsmul_eq_mul, RingHom.map_mul, map_natCast, cF_cF_toEAf, ← nsmul_eq_mul] at h2
  exact h2

theorem thPVecExists : ∀ D : D7, ThPVecExists D := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ hS hT _ _ _ ⟨e, he⟩ f₀ hf₀
  classical
  have hinf := infPart_cA (idemSum_infPart he)
  have hSfull := selfDual_isFullLattice S ΛS hS
  have hTfull := selfDual_isFullLattice T ΛT hT
  obtain ⟨f, hf⟩ := exists_isThetaAt hf₀.1 hS hT (a := cA D e) (by rw [← RingHom.map_mul, idemSum_mul_self he]) hinf
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf₀.1 S T ΛS ΛT hS hT _ e he f₀ hf₀.2.theta hf₀.2.lat).2
    (isSBHalf_of_red hSfull hTfull hinf (frMapAdj S T βS βT) (frMapAdj_add S T βS βT) (frMapAdj_up S T βS βT)
      (frMapAdj_down S T βS βT) (Pg ∪ Q) (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
        rw [omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)])
  exact ⟨f, hf₀, e, he, hf⟩

end GlobalTheory.PlaceVec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.WeilTransport
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.Mem.ThetaNonzero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_isCartanInv {k : ℕ} {G : Matrix (Fin k) (Fin k) ℂ} (hG : G.IsHermitian) (hd : IsUnit G.det) :
    ∃ s, IsCartanInv G s := by
  classical
  let U : Matrix (Fin k) (Fin k) ℂ := hG.eigenvectorUnitary.1
  have h1 : U * star U = 1 := hG.eigenvectorUnitary.2.2
  have h2 : star U * U = 1 := hG.eigenvectorUnitary.2.1
  have hs : G = U * diagonal (fun i => (hG.eigenvalues i : ℂ)) * star U := by
    have := hG.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hne : ∀ i, hG.eigenvalues i ≠ 0 := fun i hi => by
    rw [hG.det_eq_prod_eigenvalues] at hd
    exact hd.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]))
  have mul : ∀ a b : Fin k → ℂ, (U * diagonal a * star U) * (U * diagonal b * star U) =
      U * diagonal (fun i => a i * b i) * star U := fun a b => by
    calc _ = U * (diagonal a * (star U * U) * diagonal b) * star U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one, diagonal_mul_diagonal]
  let e : Fin k → ℝ := fun i => if 0 < hG.eigenvalues i then 1 else -1
  have he : ∀ i, (e i : ℂ) * e i = 1 := fun i => by
    simp only [e]; split_ifs <;> simp
  have hh : (U * diagonal (fun i => (e i : ℂ)) * star U)ᴴ = U * diagonal (fun i => (e i : ℂ)) * star U := by
    simp [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
      Pi.star_def]
  refine ⟨U * diagonal (fun i => (e i : ℂ)) * star U, ?_, ?_, ?_⟩
  · rw [mul]
    simp only [he, diagonal_one, Matrix.mul_one, h1]
  · rw [hh]
    conv_lhs => rw [hs]
    conv_rhs => rw [hs]
    rw [mul, mul]
    congr 3
    funext i
    rw [mul_right_comm, he, one_mul]
  · conv => arg 1; arg 1; rw [hs]
    rw [mul]
    have hp : (diagonal fun i => (hG.eigenvalues i : ℂ) * e i).PosDef := by
      rw [Matrix.posDef_diagonal_iff]
      intro i
      rw [← Complex.ofReal_mul, Complex.zero_lt_real]
      simp only [e]
      split_ifs with h
      · simpa using h
      · have := lt_of_le_of_ne (not_lt.1 h) (hne i)
        linarith
    have hu : IsUnit (star U) := ⟨⟨star U, U, h2, h1⟩, rfl⟩
    have := hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose] at this

theorem exists_thetaO_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) :
    ∃ f, IsThetaFunO ψ S T f ∧ f ≠ 0 := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hs S) (hs T) _ _
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)
  refine ⟨f, ?_, f0⟩
  simpa only [one_mul] using (hf 1).1

theorem exists_of_isCoord {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T V W : HSp D}
    {E : WO S T ≃+ WA V W} (hE : IsCoord S T V W E) : ∃ f, IsThetaFun ψ V W f ∧ f ≠ 0 := by
  obtain ⟨f, hf, f0⟩ := exists_thetaO_ne_zero hψ S T
  have e : (f ∘ E.symm) ∘ E = f := by
    funext x
    simp
  refine ⟨f ∘ E.symm, (hE.theta_iff ψ _).1 (by rwa [e]), fun h => f0 ?_⟩
  rw [← e, h]
  rfl

theorem isCoord_of_le (S T : HSp D) (hr : S.rank ≤ T.rank) :
    IsCoord S T S T ((mulGramInv S T).trans (Matrix.transposeAddEquiv _ _ _)) := {
  cont := (continuous_id.matrix_mul continuous_const).matrix_transpose
  cont' := continuous_id.matrix_transpose.matrix_mul continuous_const
  sympl x y := by
    unfold symplOH symplH
    rw [(GlobalTheory.OrientedSmall.bridgeSmall D S T hr).1]
    rfl
  rat x := by
    constructor
    · rintro ⟨γ, rfl⟩
      have h : (γ * S.gram⁻¹).map (incA D) = mulGramInv S T (γ.map (incA D)) := Matrix.map_mul (f := incA D)
      exact ⟨(γ * S.gram⁻¹).transpose, congrArg Matrix.transpose h⟩
    · rintro ⟨γ, hγ⟩
      have hγ' : γ.transpose.map (incA D) = mulGramInv S T x := congrArg Matrix.transpose hγ
      refine ⟨γ.transpose * S.gram, (Matrix.map_mul (f := incA D)).trans ?_⟩
      rw [← (mulGramInv S T).symm_apply_apply x, ← hγ']
      rfl
  inf x := (map_mulGramInv _ S T x).trans
    ⟨fun h => congrArg Matrix.transpose h, fun h => congrArg Matrix.transpose h⟩
  fin x := (map_mulGramInv _ S T x).trans
    ⟨fun h => congrArg Matrix.transpose h, fun h => congrArg Matrix.transpose h⟩
  part a x h i j := by
    show a * ∑ k, x j k * incA D (S.gram⁻¹ k i) = ∑ k, x j k * incA D (S.gram⁻¹ k i)
    simp only [Finset.mul_sum, ← mul_assoc, h] }

theorem exists_thetaFun_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D), ∃ f, IsThetaFun ψ V W f ∧ f ≠ 0 := by
  intro D ψ hψ V W
  rcases le_or_gt V.rank W.rank with hr | hr
  · exact exists_of_isCoord hψ (isCoord_of_le V W hr)
  · exact exists_of_isCoord hψ (isCoord_large W V hr)

end GlobalTheory.Mem.ThetaNonzero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacter
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.CharLoc

variable {F : Type} [Field F] [NumberField F]

theorem psiV_twist {ψ₀ ψ : AddChar (AF F) ℂ} {a : F} (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x))
    (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    psiV F ψ v y = psiV F ψ₀ v (algebraMap F (Fv F v) a * y) := by
  rw [psiV, psiV, h]
  refine congrArg ψ₀ (Prod.ext (mul_zero _) ?_)
  show algebraMap F (Af F) a * singleV F v y = singleV F v _
  rw [mul_comm, GlobalTheory.SnMass.Inhab.single_mul, mul_comm]
  rfl

theorem psiInf_twist {ψ₀ ψ : AddChar (AF F) ℂ} {a : F} (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x))
    (y : Ainf F) : psiInf F ψ y = psiInf F ψ₀ (algebraMap F (Ainf F) a * y) := by
  rw [psiInf, psiInf, h]
  exact congrArg ψ₀ (Prod.ext rfl (mul_zero _))

theorem eventually_integral (a : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) a).2

theorem ne_one_of_stdAt {v : HeightOneSpectrum (𝓞 F)} {χ : Fv F v → ℂ} (hs : GlobalTheory.SnMass.StdAt v χ) :
    ∃ y, χ y ≠ 1 := by
  by_contra hn
  push Not at hn
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have hd1 : algebraMap F (Fv F v) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hd0
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have h1 := (hs (z * (algebraMap F (Fv F v) (d : F))⁻¹)).1 (fun y _ => hn _) d hd
  rw [inv_mul_cancel_right₀ hd1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h1
  omega

theorem eq_zero_of_std {ψ : AddChar (AF F) ℂ} (h : GlobalTheory.SnMass.IsStdChar F ψ) (z : Ainf F)
    (hz : ∀ y, psiInf F ψ (z * y) = 1) : z = 0 := by
  classical
  funext w
  by_contra hw
  have hw' : z w ≠ 0 := hw
  let y : Ainf F := Pi.single w ((z w)⁻¹ * 2⁻¹)
  have h1 := hz y
  rw [h.2.1, Finset.sum_eq_single w] at h1
  · have e : (z * y) w = 2⁻¹ := by
      show z w * (Pi.single w ((z w)⁻¹ * 2⁻¹) : (v : InfinitePlace F) → v.Completion) w = _
      rw [Pi.single_eq_same, mul_inv_cancel_left₀ hw']
    rw [e, map_inv₀, map_ofNat] at h1
    have e2 : 2 * Real.pi * Complex.I * (((2⁻¹ : ℂ).re : ℝ) : ℂ) = Real.pi * Complex.I := by
      have : (2⁻¹ : ℂ).re = 2⁻¹ := by simp
      rw [this]
      push_cast
      ring
    rw [e2, Complex.exp_pi_mul_I] at h1
    norm_num at h1
  · intro u _ hu
    have e : (z * y) u = 0 := by
      show z u * (Pi.single w ((z w)⁻¹ * 2⁻¹) : (v : InfinitePlace F) → v.Completion) u = _
      rw [Pi.single_eq_of_ne hu, mul_zero]
    rw [e, map_zero, Complex.zero_re]
  · intro hn
    exact absurd (Finset.mem_univ w) hn

theorem char_local : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ v : HeightOneSpectrum (𝓞 F), ∃ y, psiV F ψ v y ≠ 1) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y : Fv F v, (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F) ∧ ∀ x : Ainf F, (∀ y, psiInf F ψ (x * y) = 1) → x = 0 := by
  intro F _ _ _ ψ hψ
  obtain ⟨ψ₀, h₀⟩ := GlobalTheory.SnMass.Inhab.exists_isStdChar F
  obtain ⟨a, ha, h⟩ := GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real F ψ₀ ψ h₀.1 hψ
  refine ⟨fun v => ?_, ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := ne_one_of_stdAt (h₀.2.2 v)
    refine ⟨algebraMap F (Fv F v) a⁻¹ * y, ?_⟩
    rwa [psiV_twist h, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  · obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
    have hd1 : (d : F) ≠ 0 := by exact_mod_cast hd0
    filter_upwards [eventually_integral a, eventually_integral (a * d)⁻¹] with v h1 h2 y
    simp only [psiV_twist h, ← mul_assoc]
    refine (h₀.2.2 v _).trans ⟨fun hy => ?_, fun hy d' _ => ?_⟩
    · have h3 := mul_mem (hy d hd) h2
      rwa [mul_right_comm _ y, ← map_mul, mul_right_comm, ← map_mul, mul_inv_cancel₀ (mul_ne_zero ha hd1),
        map_one, one_mul] at h3
    · exact mul_mem (mul_mem h1 hy) (HeightOneSpectrum.coe_mem_adicCompletionIntegers v d')
  · have h1 := eq_zero_of_std h₀ (algebraMap F (Ainf F) a * x) fun y => by
      rw [mul_assoc, ← psiInf_twist h, hx]
    have h2 := congrArg (algebraMap F (Ainf F) a⁻¹ * ·) h1
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul, mul_zero] using h2

end GlobalTheory.GaugeEx.CharLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalComponentsNontrivialAdelicCharacterStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponents_nontrivial_adelic_character : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → (∀ v : HeightOneSpectrum (𝓞 F), ∃ y, psiV F ψ v y ≠ 1) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ y : Fv F v, (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F) ∧ ∀ x : Ainf F, (∀ y, psiInf F ψ (x * y) = 1) → x = 0 := by
  first | exact @GlobalTheory.GaugeEx.CharLoc.char_local | exact GlobalTheory.GaugeEx.CharLoc.char_local | (intros; apply GlobalTheory.GaugeEx.CharLoc.char_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselConvDefinite

theorem isAniso_of_isDefinite {D : D7} (A : HSp D) (hs : A.SigOK) (hd : A.IsDefinite) : IsAniso A := by
  rw [GlobalTheory.BesselCompare.isAniso_iff]
  intro v hv
  by_contra hne
  have hc := D.sp.cm.cmUnram
  have := hc.1
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  rcases hd τ with h | h
  · have := (GlobalTheory.BaseChangeExistsCompare.sig_pos_iff A hs τ (hc.2.1 τ)).1 h v hne
    simp [hv] at this
  · have := (GlobalTheory.BaseChangeExistsCompare.sig_neg_iff A hs τ (hc.2.1 τ)).1 h v hne
    simp [hv] at this


open Pointwise in
theorem measure_fundamentalDomain_lt_top {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ g : G, ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) (μ : Measure G) [μ.IsHaarMeasure] {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) : μ F < ⊤ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  have hsub : F ⊆ ⋃ γ : Γ, ((γ • K) ∩ F) := by
    intro g hg
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov g
    exact Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ), ⟨k, hk, e.symm⟩, hg⟩
  calc μ F ≤ μ (⋃ γ : Γ, ((γ • K) ∩ F)) := measure_mono hsub
    _ ≤ ∑' γ : Γ, μ ((γ • K) ∩ F) := measure_iUnion_le _
    _ = μ K := (hF.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

section Conj

open GlobalTheory.BesselCompare

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem iA_eq_sum (t : Fin A.rank → AE D) : iA ι t = ∑ l, t l • vecA B (ι (A.frame l)) := by
  rw [iA, frameMat_eq, eMat_mulVec]

theorem vecA_add (x y : B.V) : vecA B (x + y) = vecA B x + vecA B y := by
  funext k; simp [vecA]

theorem vecA_iota (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  rw [iA_eq_sum]
  funext k
  have h : B.frame.repr (ι a) k = ∑ c, A.frame.repr a c * B.frame.repr (ι (A.frame c)) k := by
    conv_lhs => rw [← A.frame.sum_repr a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [vecA, h, map_sum, map_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem embRel_fix {g : GA D B} {h : GA D A} (e : EmbRel B A ι g h) {w : B.V} (hw : ∀ x, B.hD w (ι x) = 0) :
    (mt B g).mulVec (vecA B w) = vecA B w :=
  e.2 (co B w) (by funext i; rw [frameMat_eq, cT_mulVec]; exact hw _)

theorem embRel_iA {g : GA D B} {h : GA D A} (e : EmbRel B A ι g h) (t : Fin A.rank → AE D) :
    (mt B g).mulVec (iA ι t) = iA ι ((mt A h).mulVec t) := by
  rw [iA, iA, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (fun M => Matrix.mulVec M t) e.1

theorem conj_mem_NSet (d : BesselDatum A B ι) {g : GA D B} {h : GA D A} (e : EmbRel B A ι g h) {n : GA D B}
    (hn : n ∈ d.NSet) : g * n * g⁻¹ ∈ d.NSet := by
  have hinv : ∀ {x y}, (mt B g).mulVec x = y → (mt B g⁻¹).mulVec y = x := fun hxy => by
    rw [← hxy, mulVec_inv_cancel]
  have he : ∀ l, (mt B g).mulVec (vecA B (d.e l)) = vecA B (d.e l) := fun l => embRel_fix e (d.eA l)
  have hsum : ∀ c : Fin d.ρ → AE D, (mt B g).mulVec (∑ l, c l • vecA B (d.e l)) = ∑ l, c l • vecA B (d.e l) :=
    fun c => by simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, he]
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc, h1⟩ := hn.1 i
    refine ⟨c, hc, ?_⟩
    unfold actV at h1 ⊢
    rw [mulVec_mul, mulVec_mul, hinv (he i), h1, Matrix.mulVec_add, he, hsum]
  · obtain ⟨a, ha⟩ := exists_rep A (B.hT x ∘ₗ ι)
    have hw : ∀ y, B.hD (x - ι a) (ι y) = 0 := fun y => hD_swap_zero (by
      unfold HSpace.hD
      rw [map_sub, LinearMap.sub_apply, d.isom, ha]; exact sub_self _)
    have hιe : ∀ y i, B.hD (ι y) (d.e i) = 0 := fun y i => hD_swap_zero (d.eA i y)
    have hwe : ∀ i, B.hD (x - ι a) (d.e i) = 0 := fun i => by
      have h1 := hx i
      have h2 := hιe a i
      unfold HSpace.hD at h1 h2 ⊢
      rw [map_sub, h1, h2, sub_zero]
    obtain ⟨c₀, hc₀⟩ := hn.2 _ hwe
    choose c hc using fun k => hn.2 _ (hιe (A.frame k))
    unfold actV at hc₀ hc ⊢
    set t := (mt A h⁻¹).mulVec (vecA A a) with ht
    have hx1 : vecA B x = vecA B (x - ι a) + iA ι (vecA A a) := by rw [← vecA_iota, ← vecA_add, sub_add_cancel]
    have hg : (mt B g).mulVec (vecA B (x - ι a) + iA ι t) = vecA B x := by
      rw [Matrix.mulVec_add, embRel_fix e hw, embRel_iA e, ht, mulVec_cancel_inv, hx1]
    have hn1 : (mt B n).mulVec (vecA B (x - ι a) + iA ι t) =
        (vecA B (x - ι a) + iA ι t) + ∑ l, (c₀ l + ∑ k, t k * c k l) • vecA B (d.e l) := by
      rw [Matrix.mulVec_add, hc₀, iA_eq_sum]
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hc, smul_add, add_smul, Finset.sum_add_distrib,
        Finset.smul_sum, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm (f := fun k l => t k • c k l • vecA B (d.e l))]
      abel
    exact ⟨_, by rw [mulVec_mul, mulVec_mul, hinv hg, hn1, Matrix.mulVec_add, hg, hsum]⟩

theorem conj_mem_N (d : BesselDatum A B ι) {g : GA D B} {h : GA D A} (e : EmbRel B A ι g h) {n : GA D B}
    (hn : n ∈ d.N) : g * n * g⁻¹ ∈ d.N :=
  (Subgroup.closure_le (d.N.comap (MulAut.conj g).toMonoidHom)).2
    (fun _ hm => Subgroup.subset_closure (conj_mem_NSet d e hm)) hn

end Conj

theorem convergesDef : ∀ D : D7, ConvergesDef D := by
  intro D A B ι d ψ hψ hs hd μ 𝓕 hμ ν 𝓝 hν s hs' φ F hφ hF g
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A (isAniso_of_isDefinite A hs hd)
  obtain ⟨s₀, hcont, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι d.isom
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs' h)
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have := hμ.1.1
  have hfin : μ 𝓕 < ⊤ := measure_fundamentalDomain_lt_top (GQ A) hK hcov μ hμ.2
  have hFc : Continuous (rTr B g F) := hF.cont.comp (continuous_id.mul continuous_const)
  have hFl : ∀ γ ∈ GQ B, ∀ x, rTr B g F (γ * x) = rTr B g F x := fun γ hγ x => by
    simp only [rTr, mul_assoc]; exact hF.left γ hγ _
  obtain ⟨-, hc, hb⟩ := GlobalTheory.RootExch.CoefInt.coeff_integrable_continuous D A B ι d ψ hψ ν 𝓝 hν (rTr B g F) hFc hFl
  obtain ⟨M, hM⟩ := hb (s₀ '' K) (hK.image hcont)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hφ.cont.continuousOn
  have hcontI : Continuous fun h => φ h * d.coeff ψ ν 𝓝 (rTr B g F) (s₀ h) := hφ.cont.mul (hc.comp hcont)
  refine Measure.integrableOn_of_bounded (M := C * M) hfin.ne hcontI.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
  rw [norm_mul, hφ.left γ hγ]
  refine mul_le_mul (hC k hk) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hC k hk))
  have h1 : ν 𝓝 < ⊤ := by rw [hν.2.2]; exact ENNReal.one_lt_top
  have h2 := norm_setIntegral_le_of_norm_le_const (μ := ν) (s := 𝓝) (C := M)
    (f := fun n : d.N => rTr B g F ((n : GA D B) * s₀ (γ * k)) * star (d.psiN ψ (n : GA D B))) h1 (fun n _ => by
      have hn : s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ ∈ d.N := conj_mem_N d ((hrel _ _).2 rfl) n.2
      have e : (n : GA D B) * s₀ (γ * k) = s₀ γ * (s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ * s₀ k) := by
        simp only [map_mul, map_inv, inv_inv, mul_assoc, mul_inv_cancel_left]
      rw [norm_mul, norm_star, e, hFl _ (hQ γ hγ), BesselDatum.psiN, hψ.2.1, mul_one]
      exact hM _ hn _ ⟨k, hk, rfl⟩)
  rwa [Measure.real, hν.2.2, ENNReal.toReal_one, mul_one] at h2

end GlobalTheory.BesselConvDefinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdCharLocal

theorem psiV_ne_one_of_trace {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ)
    (hinf : ∀ a : F, psiInf F ψ (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F a : ℚ) : ℂ))) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  by_contra hn
  push Not at hn
  have hs := GlobalTheory.SnMass.Inhab.stdAt_of_psiInf h hinf v
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have hd1 : algebraMap F (Fv F v) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hd0
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have h1 := (hs (z * (algebraMap F (Fv F v) (d : F))⁻¹)).1 (fun y _ => hn _) d hd
  rw [inv_mul_cancel_right₀ hd1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h1
  omega

theorem psiV_ne_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1 := by
  intro D ψ hψ v
  have h := GlobalTheory.StdAdelicChar.isStdChar_inv hψ
  obtain ⟨θ, hθ⟩ := h.2.1
  obtain ⟨y, hy⟩ := psiV_ne_one_of_trace h.1 (fun a => by
    rw [h.2.2 θ hθ, GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _,
      GlobalTheory.StdRat.sum_tauE_eq_trace]
    simp) v
  refine ⟨y, fun h1 => hy ?_⟩
  rw [psiV] at h1 ⊢
  rw [AddChar.inv_apply', h1, inv_one]

end GlobalTheory.StdCharLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAdelicCharacter_localComponent_ne_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1 := by
  first | exact @GlobalTheory.StdCharLocal.psiV_ne_one | exact GlobalTheory.StdCharLocal.psiV_ne_one | (intros; apply GlobalTheory.StdCharLocal.psiV_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRangeMulVec
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.DivisionValues
open scoped InnerProductSpace Matrix

namespace GlobalTheory.Mem.LiftForms

section Core

variable {K V M : Type} [Field K] {σ : K →+* ℂ} [AddCommGroup V] [Module K V]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]


omit [FiniteDimensional ℂ M] in
theorem inner_of_norm_sq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : M →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n)
    (h : ∀ x, ‖f x‖ ^ 2 = n * ‖x‖ ^ 2) (x y : M) : inner ℂ (f x) (f y) = (n : ℂ) * inner ℂ x y := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hn
  have h1 : ∀ x, ‖((((Real.sqrt n)⁻¹ : ℝ) : ℂ) • f) x‖ = ‖x‖ := by
    intro x
    have h2 : ‖f x‖ = Real.sqrt n * ‖x‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), h, mul_pow, Real.sq_sqrt hn.le]
    rw [LinearMap.smul_apply, norm_smul, h2, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    field_simp
  have h3 := (LinearMap.norm_map_iff_inner_map_map _).1 h1 x y
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hn.le] at h3
  rw [← h3, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne']
  simp

omit [FiniteDimensional ℂ M] in
theorem inj_of_norm_sq {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : M →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n)
    (h : ∀ x, ‖f x‖ ^ 2 = n * ‖x‖ ^ 2) : Function.Injective f := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have := h x
  rw [hx, norm_zero] at this
  have h2 : ‖x‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 (show n * ‖x‖ ^ 2 = 0 by rw [← this]; simp) with h | h
    · exact absurd h hn.ne'
    · exact h
  simpa using h2

end Core

section Coord

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hform_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) : hform H x y = star x ⬝ᵥ H *ᵥ y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_mulVec {n a b : ℕ} (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin a) K) (E' : Matrix (Fin n) (Fin b) K)
    (x : Fin a → K) (y : Fin b → K) : hform H (E *ᵥ x) (E' *ᵥ y) = star x ⬝ᵥ (Eᴴ * H * E') *ᵥ y := by
  rw [hform_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem hform_orth {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} {E : Matrix (Fin n) (Fin d) K} {Pr : Matrix (Fin d) (Fin n) K}
    (h : IsOrthProj H E Pr) (z : Fin d → K) (x : Fin n → K) : hform H (E *ᵥ z) (E *ᵥ (Pr *ᵥ x)) = hform H (E *ᵥ z) x := by
  have h1 := hform_mulVec H E (1 - E * Pr) z x
  rw [h.2, Matrix.zero_mulVec, dotProduct_zero, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, sub_eq_zero,
    ← Matrix.mulVec_mulVec] at h1
  exact h1.symm

variable (S : CSD K) {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms)

theorem csum_hform (x y : Fin S.dim → K) :
    S.csum (S.basis.equivFun.symm x : S.Forms) (S.basis.equivFun.symm y : S.Forms) = hform S.H x y :=
  (S.isClassSum x y).symm

theorem act_coord (t : G) (x : Fin S.dim → K) :
    r t (S.basis.equivFun.symm x) = S.basis.equivFun.symm (S.actMat r t *ᵥ x) :=
  Subtype.ext (S.I_actMat r t x).symm

theorem gaOp_coord (a : MonoidAlgebra K G) (x : Fin S.dim → K) :
    S.gaOp r a (S.basis.equivFun.symm x) = S.basis.equivFun.symm (S.gaMat r a *ᵥ x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [CSD.gaOp, CSD.gaMat, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.sum_mulVec, Matrix.smul_mulVec, map_sum,
    map_smul, act_coord]

def lvlForm (P : Subgroup G) (ψ : P →* Kˣ) : (Fin (S.lvlDim r P ψ) → K) →ₗ[K] S.Forms :=
  (S.basis.equivFun.symm : (Fin S.dim → K) →ₗ[K] S.Forms) ∘ₗ (S.lvlE r P ψ).mulVecLin

theorem lvlForm_apply (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) :
    lvlForm S r P ψ x = S.basis.equivFun.symm (S.lvlE r P ψ *ᵥ x) := rfl

theorem lvlForm_injective (P : Subgroup G) (ψ : P →* Kˣ) : Function.Injective (lvlForm S r P ψ) :=
  S.basis.equivFun.symm.injective.comp (image_idempotent_spec K _ _).1

theorem range_lvlE (P : Subgroup G) (ψ : P →* Kˣ) : LinearMap.range (S.lvlE r P ψ).mulVecLin = S.lvlPart r P ψ :=
  (image_idempotent_spec K _ _).2.trans (level_part_spec K S G r P ψ)

theorem range_lvlForm (P : Subgroup G) (ψ : P →* Kˣ) : Set.range (lvlForm S r P ψ) = lvlForms S r P ψ := by
  ext f
  obtain ⟨u, rfl⟩ := S.basis.equivFun.symm.surjective f
  have key : S.basis.equivFun.symm u ∈ lvlForms S r P ψ ↔ u ∈ S.lvlPart r P ψ := by
    refine forall_congr' fun h => ?_
    rw [act_coord, ← map_smul, S.basis.equivFun.symm.injective.eq_iff]
  rw [key, ← range_lvlE]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, S.basis.equivFun.symm.injective hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

theorem csum_lvlForm (P : Subgroup G) (ψ : P →* Kˣ) (x y : Fin (S.lvlDim r P ψ) → K) :
    S.csum (lvlForm S r P ψ x) (lvlForm S r P ψ y) = (Nat.card P : K) * hform (S.lvlH r P ψ) x y := by
  have hc : (Nat.card P : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := P)).ne'
  rw [lvlForm_apply, lvlForm_apply, csum_hform, hform_mulVec, hform_dot, CSD.lvlH, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rfl

theorem mem_lvlNab (P : Subgroup G) (ψ : P →* Kˣ) (x : Fin (S.lvlDim r P ψ) → K) :
    x ∈ S.lvlNab r P ψ ↔ lvlForm S r P ψ x ∈ intForms S := by
  unfold CSD.lvlNab CSD.cutNab CSD.nabLat
  rw [exponent_index_lattice.mem_cutLat, mem_valLatF]
  rfl

end Coord

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem lvlE_lvlOp (h : BlockHyp B ℓ v0 s) (x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) :
    B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ (B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ x) =
      B.S.gaMat B.r (idemOf ℓ.X) *ᵥ (B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ x) := by
  have hc := (idempotent_spec K v0 h.conj G ℓ.X h.irr).2 (lvlIdem ℓ.P ℓ.ψ)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ _ hc.symm).1]

theorem lvlE_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ (B.lE ℓ Z *ᵥ z) = B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, BlockDat.lf_lvlE_lE h]
  rfl

theorem lvlForm_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    lvlForm B.S B.r ℓ.P ℓ.ψ (B.lE ℓ Z *ᵥ z) = B.toF ℓ Z z := by
  rw [lvlForm_apply, lvlE_lE h]
  rfl

theorem range_vE (h : BlockHyp B ℓ v0 s) : LinearMap.range (B.vE ℓ).mulVecLin =
    LinearMap.range (B.S.gaMat B.r (idemOf ℓ.X)).mulVecLin ⊓ B.S.lvlPart B.r ℓ.P ℓ.ψ :=
  good_part_spec K B.S G B.r ℓ.X h.irr ℓ.P ℓ.ψ

theorem lvlOp_lE (h : BlockHyp B ℓ v0 s) (z : Fin (B.dZ ℓ Z) → K) :
    B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) *ᵥ (B.lE ℓ Z *ᵥ z) = B.lE ℓ Z *ᵥ z := by
  apply BlockDat.lf_lvlE_inj
  show B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ _ = B.S.lvlE B.r ℓ.P ℓ.ψ *ᵥ _
  rw [lvlE_lvlOp h, lvlE_lE h]
  have hm : B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ z) ∈ LinearMap.range (B.vE ℓ).mulVecLin := ⟨_, rfl⟩
  rw [range_vE h] at hm
  obtain ⟨⟨u, hu⟩, -⟩ := hm
  rw [← hu, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← (group_action_matrix_hom K B.S G B.r).2,
    (idempotent_spec K v0 h.conj G ℓ.X h.irr).1.idem]

theorem span_range_mulVec {σ : K →+* ℂ} {M : Type} [AddCommGroup M] [Module ℂ M] {n d : ℕ} (J : (Fin n → K) →ₛₗ[σ] M)
    (E : Matrix (Fin n) (Fin d) K) :
    Submodule.span ℂ (J '' Set.range fun z => E *ᵥ z) = Submodule.span ℂ (Set.range fun k => J (E *ᵥ Pi.single k 1)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    have hz : z = ∑ k, z k • (Pi.single k 1 : Fin d → K) := by
      ext i; simp [Pi.single_apply]
    rw [SetLike.mem_coe]
    beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, Matrix.mulVec_sum, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Matrix.mulVec_smul, map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, rfl⟩

variable {σ : K →+* ℂ} {H M ML : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M] [AddCommGroup ML] [Module K ML]



end Block

end GlobalTheory.Mem.LiftForms

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyMemFixed
open NumberField IsDedekindDomain

namespace GlobalTheory.CuspRep.AeFix

theorem eventually_mem_fixed : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (x : π.V), ∀ᶠ v in Filter.cofinite, x ∈ GlobalTheory.PRep.fixed (π.locRep v) (GlobalTheory.LFun.KGL v (n := a)) := by
  intro E _ _ _ a π x
  filter_upwards [GlobalTheory.CuspRep.LocSph.eventually_mem ((π.cusp x.1 x.2).1.level.mem_nhds (by simp))] with w hw
  refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext ?_
  obtain ⟨g, rfl⟩ := hk
  exact hw g

end GlobalTheory.CuspRep.AeFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteSmoothIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteSmoothIrreducible
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift

theorem AllPlus.finite_smooth_irreducible : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), AllPlus M → ∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ ∀ U : Submodule ℂ (M.H τ), (∀ u : Matrix.unitaryGroup (Fin V.rank) ℂ, ∀ x ∈ U, M.σ τ u x ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro D V S M h τ
  obtain ⟨h1, h2, -, -, -, h3, -⟩ := GlobalTheory.CompactModel.model_allPos D V S M τ (funext fun a => h τ a)
  exact ⟨h1, h2, fun U hU => h3 U le_top fun g hg => hU ⟨g, hg.1⟩⟩

end GlobalTheory.DefLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteSmoothIrreducibleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_smooth_irreducible_of_allPlus : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), AllPlus M → ∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ ∀ U : Submodule ℂ (M.H τ), (∀ u : Matrix.unitaryGroup (Fin V.rank) ℂ, ∀ x ∈ U, M.σ τ u x ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first | exact @GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible | exact GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible | (intros; apply GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaIntegralIntegrableContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaIntegralIntegrableContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLiftCont

theorem continuous_integral_of_cocompact {G H : Type*} [TopologicalSpace G] [LocallyCompactSpace G]
    [FirstCountableTopology G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [Countable Γ] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K : G → H → ℂ)
    (hK : Continuous fun p : G × H => K p.1 p.2)
    (hinv : ∀ γ ∈ Γ, ∀ g h, K g (γ * h) = K g h) :
    Continuous fun g => ∫ h in 𝓕, K g h ∂μ := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨N, hN, hN₀⟩ := exists_compact_mem_nhds g₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hK.continuousOn
  have hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ :=
    GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const
      (fun _ _ _ => rfl)
  have hconst' : Integrable (fun _ : H => M) (μ.restrict 𝓕) := by
    exact hconst.re
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ hconst' ?_
  · refine Filter.Eventually.of_forall fun g => ?_
    exact (hK.comp (Continuous.prodMk_right g)).aestronglyMeasurable
  · filter_upwards [hN₀] with g hg
    refine Filter.Eventually.of_forall fun h => ?_
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    rw [hinv γ hγ]
    exact hM (g, c) ⟨hg, hc⟩
  · refine Filter.Eventually.of_forall fun h => ?_
    exact (hK.comp (Continuous.prodMk_left h)).continuousAt

theorem theta_integral_integrable_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (s : WO V W → ℂ) (F : GA D W → ℂ), IsWeilDatumO ψ V W χS χT ω → (∀ τ, (gramAt D W τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → IsThetaFunO ψ V W s → Continuous F → (∀ γ ∈ GQ W, ∀ h, F (γ * h) = F h) → (∀ g, IntegrableOn (fun h => thetaKO ω g h s * F h) 𝓕 ν) ∧ Continuous (Lift.liftInt ν 𝓕 (thetaKO ω) s F) := by
  intro D ψ V W χS χT ω ν 𝓕 s F hω hpos hν h𝓕 hs hF hFinv
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact W hpos
  obtain ⟨hcont, hinv⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω hω s hs
  have hK : Continuous fun p : GA D V × GA D W => thetaKO ω p.1 p.2 s * F p.2 :=
    hcont.mul (hF.comp continuous_snd)
  have hKinv : ∀ γ ∈ GQ W, ∀ g h, thetaKO ω g (γ * h) s * F (γ * h) = thetaKO ω g h s * F h := by
    intro γ hγ g h
    have := hinv 1 (one_mem _) γ hγ g h
    rw [one_mul] at this
    rw [this, hFinv γ hγ]
  refine ⟨fun g => ?_, ?_⟩
  · exact GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain W ν 𝓕 C hν h𝓕 hC hcov _
      (hK.comp (Continuous.prodMk_right g)) (fun γ hγ h => hKinv γ hγ g h)
  · obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
    obtain ⟨_, _, -, -, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
    exact continuous_integral_of_cocompact (GQ W) ν 𝓕 C h𝓕 hC hcov
      (fun g h => thetaKO ω g h s * F h) hK hKinv

end GlobalTheory.DefLiftCont
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteThetaIntegralIntegrableContinuousStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteThetaIntegral_integrable_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (s : WO V W → ℂ) (F : GA D W → ℂ), IsWeilDatumO ψ V W χS χT ω → (∀ τ, (gramAt D W τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → IsThetaFunO ψ V W s → Continuous F → (∀ γ ∈ GQ W, ∀ h, F (γ * h) = F h) → (∀ g, IntegrableOn (fun h => thetaKO ω g h s * F h) 𝓕 ν) ∧ Continuous (Lift.liftInt ν 𝓕 (thetaKO ω) s F) := by
  first | exact @GlobalTheory.DefLiftCont.theta_integral_integrable_continuous | exact GlobalTheory.DefLiftCont.theta_integral_integrable_continuous | (intros; apply GlobalTheory.DefLiftCont.theta_integral_integrable_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumOrientedExists
open Formalism.BasicNotions Formalism.IndefR.Datum

namespace GlobalTheory.Member

theorem vacuum_oriented_exists : ∀ D : D7, VacExistsO D := GlobalTheory.VacuumO.vacExists

end GlobalTheory.Member
end
