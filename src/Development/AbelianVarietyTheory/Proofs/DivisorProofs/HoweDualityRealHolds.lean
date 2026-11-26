module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityCharactersFockTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramesFockMapPolynomialLieActions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneParameterSubgroupUnitaryOfRealPlaceLieA
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneParameterSubgroupUnitaryOfRealPlaceLieA
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD
open GlobalTheory.RealLift.OneParam

theorem exists_line_of_upqD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ Y : ∀ w : InfinitePlace F, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) → ∃ γ ∈ RLines (σ := σ) J, IsGenD τ C γ Y := by
  intro F E _ _ _ _ _ σ β _ _ R S τ J b C hCM hC Y hY
  have := hCM.1
  obtain ⟨ξ, hξ⟩ := exists_moved hCM
  have hξ' : ∀ w, ((τ w).1 ξ).im ≠ 0 := fun w => im_ne_zero hCM hξ (τ w).1
  choose C' hC' using fun w => (hC w).2
  have hL : ∀ w, C' w * C w = 1 := fun w => frame_inv (hC w).1 (hC' w)
  set G : InfinitePlace F → ℝ → Matrix β β ℂ := fun w t => C w * NormedSpace.exp (t • Y w) * C' w with hG
  set f : ℝ → Matrix β β (AE F E) := fun t => 1 + liftM τ ξ (fun w => G w t - 1) with hf
  have hfπ : ∀ t w, (f t).map (piInf (τ w)) = G w t := fun t w => by
    rw [hf, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), OneParam.liftM_map τ hξ', add_sub_cancel]
  have hfat : ∀ t, At (evI F) (f t - 1) := fun t => by
    rw [hf, add_sub_cancel_left]
    exact at_liftM τ ξ _
  have hfadd : ∀ s t, f (s + t) = f s * f t := fun s t => by
    refine (eq_of_at hCM τ ?_ fun w => ?_).symm
    · have e : f s * f t - f (s + t) = (f s - 1) * f t + (f t - 1) - (f (s + t) - 1) := by noncomm_ring
      rw [e]
      exact at_sub (at_add (at_mul_right (hfat s) _) (hfat t)) (hfat _)
    · rw [Matrix.map_mul, hfπ, hfπ, hfπ]
      exact (conj_add (hL w) (Y w) s t).symm
  have hf0 : f 0 = 1 := by
    refine eq_of_at hCM τ (hfat 0) fun w => ?_
    rw [hfπ, Matrix.map_one _ (map_zero _) (map_one _)]
    exact conj_zero (hC' w) (Y w)
  have hfU : ∀ t, (f t)ᵀ * J * (f t).map (cA σ) = J := fun t => by
    refine eq_of_at hCM τ ?_ fun w => ?_
    · have e : (f t)ᵀ * J * (f t).map (cA σ) - J =
          (f t - 1)ᵀ * J * (f t).map (cA σ) + J * (f t - 1).map (cA σ) := by
        have e1 : (f t - 1).map (cA σ) = (f t).map (cA σ) - 1 := by
          rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
          Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      exact at_add (at_mul_right (at_mul_right (at_transpose (hfat t)) _) _)
        (at_mul_left (at_map_cA σ (hfat t)) _)
    · have hc : ((f t).map (cA σ)).map (piInf (τ w)) = (G w t).map star := by
        rw [← hfπ t w, Matrix.map_map, Matrix.map_map]
        congr 1
        funext z
        exact piInf_cA hCM (τ w) z
      rw [Matrix.map_mul, Matrix.map_mul, hc, Matrix.transpose_map, hfπ]
      by_cases hb : b = 0
      · haveI := isEmpty_of_zero (hb ▸ (hC w).1) (hC' w)
        ext i
        exact isEmptyElim i
      · have h1 := conj_unitary (hC w).1 (hC' w) (hY w) t
        rw [Matrix.mul_smul, Matrix.smul_mul] at h1
        exact smul_right_injective _ hb h1
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  have hfc : Continuous f :=
    continuous_const.add ((continuous_liftM τ ξ).comp (continuous_pi fun w =>
      (((continuous_const.matrix_mul (continuous_exp_smul (Y w))).matrix_mul continuous_const).sub continuous_const)))
  let g : ℝ → UG (cA σ) J := fun t => ⟨⟨f t, f (-t), by rw [← hfadd, add_neg_cancel, hf0],
    by rw [← hfadd, neg_add_cancel, hf0]⟩, hfU t⟩
  let γ : Multiplicative ℝ →* UG (cA σ) J :=
    { toFun := fun t => g (Multiplicative.toAdd t)
      map_one' := Subtype.ext (Units.ext hf0)
      map_mul' := fun x y => Subtype.ext (Units.ext (hfadd _ _)) }
  refine ⟨γ, ⟨?_, fun t => hfat _⟩, fun t w => ?_⟩
  · have hu : Continuous fun t : Multiplicative ℝ => ((g (Multiplicative.toAdd t)).1 : GL β (AE F E)) :=
      Units.continuous_iff.2 ⟨hfc.comp continuous_toAdd, (hfc.comp continuous_neg).comp continuous_toAdd⟩
    exact hu.subtype_mk _
  · change (f t).map (piInf (τ w)) * C w = C w * NormedSpace.exp (t • Y w)
    rw [hfπ, hG]
    simp only [Matrix.mul_assoc]
    rw [hL, Matrix.mul_one]

end GlobalTheory.HoweD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneParameterSubgroupUnitaryOfRealPlaceLieAStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oneParameterSubgroup_unitary_of_realPlace_lieAlg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ Y : ∀ w : InfinitePlace F, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) → ∃ γ ∈ RLines (σ := σ) J, IsGenD τ C γ Y := by
  first | exact @GlobalTheory.HoweD.exists_line_of_upqD | exact GlobalTheory.HoweD.exists_line_of_upqD | (intros; apply GlobalTheory.HoweD.exists_line_of_upqD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndefiniteUnitaryLieAlgAddISmulEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndefiniteUnitaryLieAlgAddISmulEq
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem jm_conjTranspose (p q : ℕ) : (Formalism.BasicNotions.TH.Jm p q)ᴴ = Formalism.BasicNotions.TH.Jm p q := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_conjTranspose]
  simp

theorem jm_mul_self (p q : ℕ) : Formalism.BasicNotions.TH.Jm p q * Formalism.BasicNotions.TH.Jm p q = 1 := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

theorem upq_span (p q : ℕ) (Z : Mat p q) : ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  obtain ⟨J, hJ⟩ : ∃ J, J = Formalism.BasicNotions.TH.Jm p q := ⟨_, rfl⟩
  have hJh : Jᴴ = J := hJ ▸ jm_conjTranspose p q
  have hJJ : J * J = 1 := hJ ▸ jm_mul_self p q
  refine ⟨(1/2 : ℂ) • (Z - J * Zᴴ * J), ?_, (-(Complex.I / 2)) • (Z + J * Zᴴ * J), ?_, ?_⟩
  · show _ = _
    rw [← hJ]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp [star_div₀]
    rw [this]
    module
  · show _ = _
    rw [← hJ]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by simp [star_div₀]; ring
    rw [this]
    module
  · rw [smul_smul]
    have : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, mul_div_assoc', Complex.I_mul_I]; ring
    rw [this]
    module

end GlobalTheory.HoweD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndefiniteUnitaryLieAlgAddISmulEqStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_indefiniteUnitaryLieAlg_add_I_smul_eq : ∀ (p q : ℕ) (Z : Mat p q), ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  first | exact @GlobalTheory.HoweD.upq_span | exact GlobalTheory.HoweD.upq_span | (intros; apply GlobalTheory.HoweD.upq_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleContainsFirstMemberCoinvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleContainsFirstMemberCoinvariant
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem coinv_atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h
    simp
  · simp [Function.update_of_ne h]

theorem coinv_sumPl_tprod (w : ι) (L : ∀ i, Module.End ℂ (V i)) (hL : ∀ i, i ≠ w → L i = 0) (f : ∀ i, V i) :
    sumPl L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L w (f w))) := by
  unfold sumPl
  rw [LinearMap.sum_apply, Finset.sum_eq_single w, coinv_atPl_tprod]
  · intro i _ hi
    rw [coinv_atPl_tprod, hL i hi, LinearMap.zero_apply, MultilinearMap.map_update_zero]
  · intro h
    exact absurd (Finset.mem_univ w) h

end Tensor

theorem tensAny_coinv_le_comap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → LinearMap.range Φ = M.Pol ψ τ → ∀ A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ, (∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (τ w))) (A w)) → ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c → GlobalTheory.HoweR.tensAny (fun w => GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w)) ≤ N.comap Φ := by
  intro F E _ _ _ _ _ σ n d X W M ψ om τ P Q R S Φ c N hCM hN hr A hA hact
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨w, hw⟩, rfl⟩
  let e : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w) →ₗ[ℂ] TensD F P Q R S := (PiTensorProduct.tprod ℂ).toLinearMap f w
  have he : ∀ g, e g = PiTensorProduct.tprod ℂ (Function.update f w g) := fun g => rfl
  have key : ∀ Z ∈ upq (P w) (Q w), ∀ g,
      fockAct1 (P w) (Q w) (R w) (S w) Z g - (-c w * Z.trace) • g ∈ (N.comap Φ).comap e := by
    intro Z hZ g
    let Y : ∀ i : InfinitePlace F, Mat (P i) (Q i) := Pi.single w Z
    have hY : ∀ i, Y i ∈ upq (P i) (Q i) := by
      intro i
      by_cases h : i = w
      · subst h
        simpa [Y] using hZ
      · simp [Y, Pi.single_eq_of_ne h, upq]
    obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.T.exists_oneParameterSubgroup_unitary_of_realPlace_lieAlg F E σ (Fin n) P Q τ (incM F X.J) 1 A hCM hA Y hY
    have h1 := hact γ hγ Y hgen (e g)
    have h2 := (actsLaws F (Fin n × Fin d) _ _ 0).1 _ (fun t => map_zero _) h1
    have h3 := hN.2.1 γ hγ _ (hr ▸ LinearMap.mem_range_self Φ (e g)) _ h2
    rw [he, coinv_sumPl_tprod w _ (fun i hi => by simp [Y, Pi.single_eq_of_ne hi])] at h3
    rw [Submodule.mem_comap, Submodule.mem_comap, he]
    simpa [Y, sub_eq_add_neg] using h3
  have hle : GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w) ≤ (N.comap Φ).comap e := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Z, g, rfl⟩
    obtain ⟨Z₁, h₁, Z₂, h₂, rfl⟩ := GlobalTheory.T.exists_indefiniteUnitaryLieAlg_add_I_smul_eq _ _ Z
    have h := Submodule.add_mem _ (key Z₁ h₁ g) (Submodule.smul_mem _ Complex.I (key Z₂ h₂ g))
    rw [SetLike.mem_coe]
    convert h using 1
    simp only [map_add (f := _), map_smul, Matrix.trace_add, Matrix.trace_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    module
  have h := hle hw
  rw [Submodule.mem_comap, he, Function.update_eq_self] at h
  exact h

end GlobalTheory.HoweD

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleContainsFirstMemberCoinvariantStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_submodule_contains_firstMember_coinvariants : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → LinearMap.range Φ = M.Pol ψ τ → ∀ A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ, (∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (τ w))) (A w)) → ActsByD τ A (om.comp (MonoidHom.inl _ _)) Φ (fun w => fockAct1 (P w) (Q w) (R w) (S w)) c → GlobalTheory.HoweR.tensAny (fun w => GlobalTheory.HoweR.coinv (P w) (Q w) (R w) (S w) (-c w)) ≤ N.comap Φ := by
  first | exact @GlobalTheory.HoweD.tensAny_coinv_le_comap | exact GlobalTheory.HoweD.tensAny_coinv_le_comap | (intros; apply GlobalTheory.HoweD.tensAny_coinv_le_comap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleComapStableSecondMember
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleComapStableSecondMember
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem sumPl_single_add_smul {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (L : ∀ w, Module.End ℂ (V w)) (a : ι → ℂ) (w : ι) (hL : ∀ v, v ≠ w → L v = 0) :
    sumPl (fun v => L v + a v • (1 : Module.End ℂ (V v))) =
      atPl w (L w) + (∑ v, a v) • (1 : Module.End ℂ (⨂[ℂ] i, V i)) := by
  have h : ∀ w, atPl w (L w + a w • (1 : Module.End ℂ (V w))) = atPl w (L w) + a w • (1 : Module.End ℂ (⨂[ℂ] i, V i)) := by
    intro w
    have e := (PiTensorProduct.mapMultilinear ℂ V V).map_update_add (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (L w)
      (a w • LinearMap.id)
    have e2 := (PiTensorProduct.mapMultilinear ℂ V V).map_update_smul (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w (a w)
      LinearMap.id
    simp only [PiTensorProduct.mapMultilinear_apply, Function.update_eq_self, PiTensorProduct.map_id] at e e2
    simp only [atPl]
    rw [Module.End.one_eq_id, Module.End.one_eq_id, e, e2]
    rfl
  have h0 : ∀ v, v ≠ w → atPl v (L v) = (0 : Module.End ℂ (⨂[ℂ] i, V i)) := by
    intro v hv
    rw [hL v hv]
    exact (PiTensorProduct.mapMultilinear ℂ V V).map_update_zero (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) v
  simp only [sumPl, h, Finset.sum_add_distrib, Finset.sum_smul]
  rw [Finset.sum_eq_single w (fun v _ hv => h0 v hv) (fun hw => absurd (Finset.mem_univ w) hw)]

theorem stab_comap_of_thetaSubInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → ∀ C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ, (∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (τ w))) (C w)) → ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c → ∀ w, GlobalTheory.HoweR.Stab (GlobalTheory.HoweR.actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (N.comap Φ) := by
  intro F E _ _ _ _ _ σ n d X W M ψ om τ P Q R S Φ c N hCM hN C hC hact w
  have key : ∀ Z ∈ upq (R w) (S w), ∀ y ∈ N.comap Φ,
      GlobalTheory.HoweR.actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w)) Z y
        ∈ N.comap Φ := by
    intro Z hZ y hy
    set Y : ∀ v : InfinitePlace F, Mat (R v) (S v) := Pi.single w Z with hYdef
    have hYw : Y w = Z := by simp [hYdef]
    have hYv : ∀ v, v ≠ w → Y v = 0 := fun v hv => by simp [hYdef, Pi.single_eq_of_ne hv]
    have hY : ∀ v, Y v ∈ upq (R v) (S v) := by
      intro v
      by_cases hv : v = w
      · subst hv; rw [hYw]; exact hZ
      · rw [hYv v hv]; simp [upq]
    obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.T.exists_oneParameterSubgroup_unitary_of_realPlace_lieAlg F E σ (Fin d) R S τ (incM F W.J) Complex.I C hCM hC Y hY
    have hSD := hact γ hγ Y hgen y
    have hD := (actsLaws F (Fin n × Fin d) _ _ (Φ y)).1 _ (fun t => map_zero _) hSD
    have hmem := hN.2.2.2.1 γ hγ (Φ y) hy _ hD
    rw [sumPl_single_add_smul (fun v => fockAct2 (P v) (Q v) (R v) (S v) (Y v)) (fun v => c v * (Y v).trace) w
      (fun v hv => by simp only [hYv v hv, map_zero]), hYw, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul] at hmem
    exact (N.add_mem_iff_left (N.smul_mem _ hy)).1 hmem
  intro Z y hy
  obtain ⟨A, hA, B, hB, rfl⟩ := GlobalTheory.T.exists_indefiniteUnitaryLieAlg_add_I_smul_eq _ _ Z
  rw [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  exact add_mem (key A hA y hy) (Submodule.smul_mem _ _ (key B hB y hy))

end GlobalTheory.HoweD

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftSubmoduleComapStableSecondMemberStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_submodule_comap_stable_secondMember : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (om : Rep σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) (P Q R S : InfinitePlace F → ℕ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (c : InfinitePlace F → ℂ) (N : Submodule ℂ (SInf F (Fin n × Fin d))), IsCMExt F E σ → GlobalTheory.Published.ThetaSubInf M ψ τ om N → ∀ C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ, (∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (τ w))) (C w)) → ActsByD τ C (om.comp (MonoidHom.inr _ _)) Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c → ∀ w, GlobalTheory.HoweR.Stab (GlobalTheory.HoweR.actAt (V := fun w => Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (N.comap Φ) := by
  first | exact @GlobalTheory.HoweD.stab_comap_of_thetaSubInf | exact GlobalTheory.HoweD.stab_comap_of_thetaSubInf | (intros; apply GlobalTheory.HoweD.stab_comap_of_thetaSubInf <;> assumption)
end
end

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
  GlobalTheory.HoweD GlobalTheory.HoweR

namespace GlobalTheory

theorem howeDualityReal_holds : GlobalTheory.Published.HoweDualityReal := by
  intro F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX1 hX2 hW1 hW2 _ _ _ _ hWeil τ hcX hcW
  obtain ⟨P, Q, R, S, A, C, Φ, c, c', hfr, hinj, hrange, hact1, hact2⟩ :=
    GlobalTheory.T.exists_frames_fockMap_polynomial_lie_actions F E σ hCM n d X W M ψ χX χW om hψ hX1 hX2 hW1 hW2 hWeil τ hcX hcW
  obtain ⟨-, hA, hC⟩ := hfr
  have hstab : ∀ N, GlobalTheory.Published.ThetaSubInf M ψ τ om N → ∀ w, Stab (actAt (V := fun w =>
      Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) w (fockAct2 (P w) (Q w) (R w) (S w))) (N.comap Φ) :=
    fun N hN => GlobalTheory.T.thetaLift_submodule_comap_stable_secondMember F E σ n d X W M ψ om τ P Q R S Φ c' N hCM hN C hC hact2
  have hcoinv : ∀ N, GlobalTheory.Published.ThetaSubInf M ψ τ om N →
      tensAny (fun w => coinv (P w) (Q w) (R w) (S w) (-c w)) ≤ N.comap Φ :=
    fun N hN => GlobalTheory.T.thetaLift_submodule_contains_firstMember_coinvariants F E σ n d X W M ψ om τ P Q R S Φ c N hCM hN hrange A hA hact1
  obtain ⟨⟨L, hL⟩, hsum⟩ := GlobalTheory.T.howe_duality_characters_fock_tensor_product (InfinitePlace F) P Q R S (fun w => -c w)
  have hmap : ∀ N, GlobalTheory.Published.ThetaSubInf M ψ τ om N → (N.comap Φ).map Φ = N := by
    intro N hN
    rw [Submodule.map_comap_eq, hrange]
    exact inf_eq_right.mpr hN.1
  refine ⟨⟨L, fun m N hmono hN => hL m (fun i => (N i).comap Φ) ?_
    (fun k => ⟨hstab _ (hN k), hcoinv _ (hN k)⟩)⟩, ?_⟩
  · intro i j hij
    refine lt_of_le_of_ne (Submodule.comap_mono (hmono hij).le) ?_
    intro h
    have h' := congrArg (Submodule.map Φ) h
    rw [hmap _ (hN i), hmap _ (hN j)] at h'
    exact (hmono hij).ne h'
  · intro N N' hN hN' hne hne' heq
    refine hsum (N.comap Φ) (N'.comap Φ) (hstab _ hN) (hcoinv _ hN) ?_ (hstab _ hN') (hcoinv _ hN') ?_ ?_
    · intro h; apply hne; rw [← hmap _ hN, h, Submodule.map_top, hrange]
    · intro h; apply hne'; rw [← hmap _ hN', h, Submodule.map_top, hrange]
    · apply Submodule.map_injective_of_injective hinj
      rw [Submodule.map_sup, hmap _ hN, hmap _ hN', heq, Submodule.map_top, hrange]

end GlobalTheory

end
