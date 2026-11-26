module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFiniteMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalDictionaryInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalDictionaryInertPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocDict

open GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem isConjAt_conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) :
    IsConjAt σ (under_eq_of_isInertAt hw) (conjW σ hw) := fun y => by
  show toCompl _ (sigR (Fv F v) σ ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm (toCompl _ y))) = _
  congr 2
  exact (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply y

theorem conjW_conjW (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hw : Formalism.UG.IsInertAt F E v w)
    (x : w.adicCompletion E) : conjW σ hw (conjW σ hw x) = x := by
  obtain ⟨y, rfl⟩ := InertChart.toCompl_surjective (under_eq_of_isInertAt hw) x
  rw [isConjAt_conjW σ hw, isConjAt_conjW σ hw]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem iotaW_mulVec (hw : Formalism.UG.IsInertAt F E v w) {l m : Type} [Fintype m]
    (M : Matrix l m (w.adicCompletion E)) (y : m → w.adicCompletion E) :
    (fun i => iotaW hw ((M *ᵥ y) i)) = M.map (iotaW hw) *ᵥ fun i => iotaW hw (y i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, iotaW_mul]

theorem map_iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) {l m p : Type} [Fintype m]
    (M : Matrix l m (w.adicCompletion E)) (N : Matrix m p (w.adicCompletion E)) :
    M.map (iotaW hw) * N.map (iotaW hw) = (M * N).map (iotaW hw) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, iotaW_mul]

theorem one_map_iotaW (hw : Formalism.UG.IsInertAt F E v w) (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (iotaW hw) =
      iotaW hw 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem herm_gram {R : Type} [CommRing R] (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) {n : ℕ}
    (A M : Matrix (Fin n) (Fin n) R) (hM : ∀ i j, τ (M i j) = M j i) (i j : Fin n) :
    τ ((Formalism.UG.cT τ A * M * A) i j) = (Formalism.UG.cT τ A * M * A) j i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hτ, hM,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isUnit_of_val_eq_one {t : Formalism.UG.Ov E w} (ht : Valued.v (t : w.adicCompletion E) = 1) : IsUnit t := by
  have h0 : (t : w.adicCompletion E) ≠ 0 := fun h0 => by rw [h0, map_zero] at ht; exact zero_ne_one ht
  have hm : (t : w.adicCompletion E)⁻¹ ∈ Formalism.UG.Ov E w := by
    show _ ∈ w.adicCompletionIntegers E
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ht, inv_one]
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

end GlobalTheory.InertLocDict

namespace GlobalTheory.InertLocDict

open GlobalTheory.InertBigCell

theorem exists_local_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (O : Type) (_ : CommRing O) (c : O →+* O) (ι : O →ₙ+* AE F E) (P Q : Matrix (Fin n) (Fin n) (AE F E))
      (JL : Matrix (Fin n) (Fin n) O),
      IsLocalRing O ∧ (∀ x, c (c x) = x) ∧ IsUnit (2 : O) ∧ (∃ x : O, IsUnit (c x - x)) ∧
      Function.Injective ι ∧ At (evFin F v) (ι 1) ∧ (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) ∧
      (∀ x, cA σ (ι x) = ι (c x)) ∧
      P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧ Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      ι 1 • P = P ∧ ι 1 • Q = Q ∧
      (∀ i j, c (JL j i) = JL i j) ∧ IsUnit JL.det ∧ Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι ∧
      ∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i) := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hw
  have h := under_eq_of_isInertAt hw
  have hc : IsConjAt σ h (conjW σ hw) := isConjAt_conjW σ hw
  have hσ : ∀ x, σ (σ x) = x := InertChart.conj_conj hB.cm
  haveI : IsLocalRing (Formalism.UG.Ov E w) := inferInstanceAs (IsLocalRing (w.adicCompletionIntegers E))
  let c : Formalism.UG.Ov E w →+* Formalism.UG.Ov E w :=
    ((conjW σ hw).comp (Formalism.UG.Ov E w).subtype).codRestrict (Formalism.UG.Ov E w)
      (fun x => InertChart.conj_mem hw hc x.2)
  let ι : Formalism.UG.Ov E w →ₙ+* AE F E :=
    { toFun := fun x => iotaW hw (x : w.adicCompletion E)
      map_mul' := fun x y => iotaW_mul hw _ _
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ _ _ }
  have hι : ∀ x, ι x = iotaW hw (x : w.adicCompletion E) := fun _ => rfl
  have hι1 : ι 1 = iotaW hw 1 := rfl
  have hcv : ∀ x, ((c x : Formalism.UG.Ov E w) : w.adicCompletion E) = conjW σ hw x := fun _ => rfl
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt (L := X.L) hw hX.lat.fg (Submodule.IsLattice.span_eq_top (self := hX.lat))
  have hJ : (X.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX
  obtain ⟨Bm, ⟨k, hk⟩, eB⟩ := InertChart.exists_gram hw hc hJ
    (GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s hB hX v) ha
  have hkij : ∀ i j, ((k.1 i j : Formalism.UG.Ov E w) : w.adicCompletion E) = Bm.1 i j := fun i j => by
    rw [← hk]; rfl
  have hBt : Bm.1ᵀ = a.1ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) * a.1.map (conjW σ hw) := by
    rw [eB, Matrix.transpose_mul, Matrix.transpose_mul, Formalism.UG.cT, Matrix.transpose_transpose, Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  refine ⟨Formalism.UG.Ov E w, inferInstance, c, ι, a.1.map (iotaW hw), (a⁻¹).1.map (iotaW hw), k.1ᵀ, inferInstance,
    fun x => Subtype.ext (conjW_conjW σ hσ hw x), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h2 : (2 : w.adicCompletion E) ≠ 0 := by
      rw [← map_ofNat (algebraMap E (w.adicCompletion E)) 2]
      exact (map_ne_zero _).2 two_ne_zero
    have hm : (2 : w.adicCompletion E)⁻¹ ∈ Formalism.UG.Ov E w := by
      have := complMap_mem h (GlobalTheory.InertLocField.half_mem v (hB.inert v w hw).1)
      rwa [complMap_algebraMap, map_inv₀, map_inv₀, map_ofNat, map_ofNat] at this
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ h2)⟩
  ·
    obtain ⟨x, hx⟩ := InertChart.exists_conj_sub_unit hB.cm hw
    have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have hxm : algebraMap E (w.adicCompletion E) (x : E) ∈ Formalism.UG.Ov E w := by
      show _ ∈ w.adicCompletionIntegers E
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]; exact w.valuation_le_one x
    refine ⟨⟨_, hxm⟩, ?_⟩
    refine isUnit_of_val_eq_one ?_
    show Valued.v (conjW σ hw (algebraMap E _ (x : E)) - algebraMap E _ (x : E)) = 1
    rw [InertChart.conj_algebraMap hc, ← map_sub, hval, hx]
  · exact fun x y hxy => Subtype.ext (iotaW_injective hw hxy)
  · rw [hι1, iotaW_apply]; exact GlobalTheory.InertLocField.at_liftT v _
  · intro y hy
    have h1 := hy _ (GlobalTheory.InertLocField.evFin_one_sub v)
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    rw [hι1, iotaW_one, ← Algebra.smul_def]
    exact h1.symm
  · intro x
    rw [hι, hι, hcv, iotaW_conjW]
  · rw [map_iotaW_mul, Units.mul_inv, one_map_iotaW, hι1]
  · rw [map_iotaW_mul, Units.inv_mul, one_map_iotaW, hι1]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hι1, ← iotaW_mul, one_mul]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hι1, ← iotaW_mul, one_mul]
  · intro i j
    apply Subtype.ext
    rw [hcv, Matrix.transpose_apply, Matrix.transpose_apply, hkij, hkij, eB]
    refine herm_gram (conjW σ hw) (conjW_conjW σ hσ hw) a.1 (X.Jᵀ.map (algebraMap E (w.adicCompletion E)))
      (fun p q => ?_) i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, InertChart.conj_algebraMap hc, hX.herm]
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).1 k.isUnit
  · have e1 : (a.1.map (iotaW hw))ᵀ = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (0 : Matrix (Fin n) (Fin n) (AE F E)) +
        a.1ᵀ.map (iotaW hw) := by
      rw [smul_zero, zero_add, Matrix.transpose_map]
    have e2 : (a.1.map (iotaW hw)).map (cA σ) = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (0 : Matrix (Fin n) (Fin n) (AE F E)) +
        (a.1.map (conjW σ hw)).map (iotaW hw) := by
      rw [smul_zero, zero_add]
      ext i j
      simp only [Matrix.map_apply, iotaW_conjW]
    rw [e1, e2, incM_split hw X.J,
      idem_split_mul _ (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      idem_split_mul _ (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      Matrix.zero_mul, Matrix.zero_mul, smul_zero, zero_add, ← hBt]
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, hι, hkij]
  · intro z
    rw [GlobalTheory.InertSphLat.mem_latAt_iff hw X z]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have e : a.1 *ᵥ ((a⁻¹).1 *ᵥ u) = u := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have hint := (ha ((a⁻¹).1 *ᵥ u)).2 (by rw [e]; exact hu)
      refine ⟨fun i => ⟨_, hint i⟩, ?_⟩
      show (fun i => iotaW hw (u i)) = a.1.map (iotaW hw) *ᵥ fun i => iotaW hw (((a⁻¹).1 *ᵥ u) i)
      rw [← iotaW_mulVec, e]
    · rintro ⟨b, rfl⟩
      refine ⟨a.1 *ᵥ fun i => (b i : w.adicCompletion E), (ha _).1 fun i => (b i).2, ?_⟩
      rw [iotaW_mulVec]
      rfl

end GlobalTheory.InertLocDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalDictionaryInertPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_dictionary_inertPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (O : Type) (_ : CommRing O) (c : O →+* O) (ι : O →ₙ+* _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (P Q : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (JL : Matrix (Fin n) (Fin n) O),
      IsLocalRing O ∧ (∀ x, c (c x) = x) ∧ IsUnit (2 : O) ∧ (∃ x : O, IsUnit (c x - x)) ∧
      Function.Injective ι ∧ At (evFin F v) (ι 1) ∧ (∀ y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) y → ι 1 * y = y) ∧
      (∀ x, cA σ (ι x) = ι (c x)) ∧
      P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧ Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) ∧
      ι 1 • P = P ∧ ι 1 • Q = Q ∧
      (∀ i j, c (JL j i) = JL i j) ∧ IsUnit JL.det ∧ Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι ∧
      ∀ z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i) := by
  first | exact @GlobalTheory.InertLocDict.exists_local_dictionary | exact GlobalTheory.InertLocDict.exists_local_dictionary | (intros; apply GlobalTheory.InertLocDict.exists_local_dictionary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseIntegralMatricesPreservingDoubledLa
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseIntegralMatricesPreservingDoubledLa
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.LatticeStab

variable {A O : Type} [CommRing A] [CommRing O] (ι : O →ₙ+* A) {n : ℕ}

theorem map_mul_of_nonUnital {m : Type} [Fintype m] (G H : Matrix m m O) :
    (G * H).map ι = G.map ι * H.map ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, map_sum, map_mul]

theorem exists_matrix_of_keeps (P : Matrix (Fin n) (Fin n) A) (Λ : Set (Fin n → A))
    (hP : ι 1 • P = P)
    (hΛ : ∀ z, z ∈ Λ ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i))
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A)
    (hM : ∀ z : Fin n ⊕ Fin n → A, z ∘ Sum.inl ∈ Λ → z ∘ Sum.inr ∈ Λ →
      (M *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M *ᵥ z) ∘ Sum.inr ∈ Λ) :
    ∃ G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O,
      M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι := by
  have h0 : (0 : Fin n → A) ∈ Λ :=
    (hΛ 0).2 ⟨0, by ext i; simp [Matrix.mulVec, dotProduct]⟩
  have hcol : ∀ k : Fin n, (fun r => P r k) ∈ Λ := by
    intro k
    refine (hΛ _).2 ⟨Pi.single k 1, ?_⟩
    ext r
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single k]
    · have := congrFun (congrFun hP r) k
      simp only [Matrix.smul_apply, smul_eq_mul] at this
      simp only [Pi.single_eq_same]
      rw [mul_comm]; exact this.symm
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  have hDcol : ∀ j, (fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inl ∈ Λ ∧
      (fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inr ∈ Λ := by
    intro j
    rcases j with k | k
    · have e1 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inl k)) ∘ Sum.inl = fun r => P r k := by
        ext r; simp
      have e2 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inl k)) ∘ Sum.inr = 0 := by
        ext r; simp
      rw [e1, e2]; exact ⟨hcol k, h0⟩
    · have e1 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inr k)) ∘ Sum.inl = 0 := by
        ext r; simp
      have e2 : (fun k' => Matrix.fromBlocks P 0 0 P k' (Sum.inr k)) ∘ Sum.inr = fun r => P r k := by
        ext r; simp
      rw [e1, e2]; exact ⟨h0, hcol k⟩
  have ex : ∀ j, ∃ a b : Fin n → O,
      (M *ᵥ fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inl = P *ᵥ (fun i => ι (a i)) ∧
      (M *ᵥ fun k => Matrix.fromBlocks P 0 0 P k j) ∘ Sum.inr = P *ᵥ (fun i => ι (b i)) := by
    intro j
    obtain ⟨h1, h2⟩ := hM _ (hDcol j).1 (hDcol j).2
    obtain ⟨a, ha⟩ := (hΛ _).1 h1
    obtain ⟨b, hb⟩ := (hΛ _).1 h2
    exact ⟨a, b, ha, hb⟩
  choose a b hab using ex
  refine ⟨Matrix.of fun i j => Sum.elim (a j) (b j) i, ?_⟩
  ext i j
  have hMD : (M * Matrix.fromBlocks P 0 0 P) i j = (M *ᵥ fun k => Matrix.fromBlocks P 0 0 P k j) i := rfl
  rw [hMD]
  rcases i with r | r
  · have := congrFun (hab j).1 r
    simp only [Function.comp] at this
    rw [this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  · have := congrFun (hab j).2 r
    simp only [Function.comp] at this
    rw [this]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

end GlobalTheory.LatticeStab

theorem GlobalTheory.LatticeStab.matrix_in_diag_basis : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (n : ℕ) (P Q : Matrix (Fin n) (Fin n) A)
    (Λ : Set (Fin n → A)), Function.Injective ι → P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) A) →
    Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) A) → ι 1 • P = P → ι 1 • Q = Q →
    (∀ z, z ∈ Λ ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A, M * M' = 1 →
    (∀ z : Fin n ⊕ Fin n → A, z ∘ Sum.inl ∈ Λ → z ∘ Sum.inr ∈ Λ →
      (M *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M *ᵥ z) ∘ Sum.inr ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inr ∈ Λ) →
    ∃ G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, G * G' = 1 ∧
      M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι := by
  intro A O _ _ ι n P Q Λ hinj _hPQ hQP hP _hQ hΛ M M' hMM' hM
  obtain ⟨G, hG⟩ := GlobalTheory.LatticeStab.exists_matrix_of_keeps ι P Λ hP hΛ M
    (fun z h1 h2 => ⟨(hM z h1 h2).1, (hM z h1 h2).2.1⟩)
  obtain ⟨G', hG'⟩ := GlobalTheory.LatticeStab.exists_matrix_of_keeps ι P Λ hP hΛ M'
    (fun z h1 h2 => ⟨(hM z h1 h2).2.2.1, (hM z h1 h2).2.2.2⟩)
  refine ⟨G, G', ?_, hG⟩
  have hDD : Matrix.fromBlocks P 0 0 P * (G * G').map ι = Matrix.fromBlocks P 0 0 P := by
    rw [GlobalTheory.LatticeStab.map_mul_of_nonUnital, ← Matrix.mul_assoc, ← hG, Matrix.mul_assoc, ← hG',
      ← Matrix.mul_assoc, hMM', Matrix.one_mul]
  have hQD : Matrix.fromBlocks Q 0 0 Q * Matrix.fromBlocks P 0 0 P =
      ι 1 • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_multiply]
    simp [hQP]
  have key : ι 1 • (G * G').map ι = ι 1 • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) := by
    have := congrArg (fun X => Matrix.fromBlocks Q 0 0 Q * X) hDD
    simp only [← Matrix.mul_assoc, hQD] at this
    rwa [Matrix.smul_mul, Matrix.one_mul] at this
  ext i j
  apply hinj
  have := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, ← map_mul, one_mul] at this
  rw [this]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseIntegralMatricesPreservingDoubledLaStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_integral_matrices_preserving_doubled_lattice : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (n : ℕ) (P Q : Matrix (Fin n) (Fin n) A)
    (Λ : Set (Fin n → A)), Function.Injective ι → P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) A) →
    Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) A) → ι 1 • P = P → ι 1 • Q = Q →
    (∀ z, z ∈ Λ ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ M M' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A, M * M' = 1 →
    (∀ z : Fin n ⊕ Fin n → A, z ∘ Sum.inl ∈ Λ → z ∘ Sum.inr ∈ Λ →
      (M *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M *ᵥ z) ∘ Sum.inr ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inl ∈ Λ ∧ (M' *ᵥ z) ∘ Sum.inr ∈ Λ) →
    ∃ G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, G * G' = 1 ∧
      M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι := by
  first | exact @GlobalTheory.LatticeStab.matrix_in_diag_basis | exact GlobalTheory.LatticeStab.matrix_in_diag_basis | (intros; apply GlobalTheory.LatticeStab.matrix_in_diag_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSkewHermitianCorrectionOfLocalSoluti
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSkewHermitianCorrectionOfLocalSoluti
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.TransportBack

open Matrix

theorem map_mul_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k p : Type*} [Fintype k]
    (X : Matrix m k R) (Y : Matrix k p R) : (X * Y).map f = X.map f * Y.map f := by
  ext i j; simp [Matrix.mul_apply, map_sum, map_mul]

theorem map_mulVec_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k : Type*} [Fintype k]
    (X : Matrix m k R) (a : k → R) : X.map f *ᵥ (fun i => f (a i)) = fun i => f ((X *ᵥ a) i) := by
  ext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem map_add_gen {R S Fh : Type*} [CommRing R] [CommRing S] [FunLike Fh R S]
    [NonUnitalRingHomClass Fh R S] (f : Fh) {m k : Type*}
    (X Y : Matrix m k R) : (X + Y).map f = X.map f + Y.map f := by
  ext i j; simp

theorem map_one_eq {R S : Type*} [CommRing R] [CommRing S] (ι : R →ₙ+* S) {n : Type*} [DecidableEq n] :
    (1 : Matrix n n R).map ι = ι 1 • (1 : Matrix n n S) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem map_neg_one_eq {R S : Type*} [CommRing R] [CommRing S] (ι : R →ₙ+* S) {n : Type*} [DecidableEq n] :
    (-1 : Matrix n n R).map ι = -(ι 1 • (1 : Matrix n n S)) := by
  ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem assoc_a {R : Type*} [CommRing R] {a b c d e : Type*} [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (D : Matrix d e R) :
    A * B * C * D = A * (B * (C * D)) := by simp only [Matrix.mul_assoc]

theorem assoc_b {R : Type*} [CommRing R] {a b c d : Type*} [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (P₁ Y Q₁ P₂ : Matrix d d R) :
    A * B * C * (P₁ * Y * Q₁) * P₂ = A * (B * (C * (P₁ * (Y * (Q₁ * P₂))))) := by
  simp only [Matrix.mul_assoc]

theorem smul_mid_of {R : Type*} [CommRing R] {a b d : Type*} [Fintype b] [DecidableEq b]
    (s : R) (A : Matrix a b R) (B : Matrix b b R) (C : Matrix b d R) (h : s • B = s • 1) :
    s • (A * B * C) = s • (A * C) := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

theorem smul_last_of {R : Type*} [CommRing R] {a b c d e : Type*} [Fintype b] [Fintype c] [Fintype d]
    (s : R) (A : Matrix a b R) (B : Matrix b c R) (C : Matrix c d R) (Z : Matrix d e R) (h : s • Z = 0) :
    s • (A * B * C * Z) = 0 := by
  rw [← Matrix.mul_smul, h, Matrix.mul_zero]

end GlobalTheory.TransportBack

namespace GlobalTheory.TransportBack
open Matrix

theorem transport_back : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (v : Pl (F := F)) (O : Type) [CommRing O] (c : O →+* O) (ι : O →ₙ+* AE F E)
    (P Q : Matrix (Fin n) (Fin n) (AE F E)) (JL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (ι 1) → (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) → (∀ x, cA σ (ι x) = ι (c x)) →
    P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) → Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) →
    ι 1 • P = P → ι 1 • Q = Q → Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι →
    (∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O)
      (ZL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (M - 1) → M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    ZLᵀ * JL + JL * ZL.map c = 0 →
    IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL).det →
    ∃ Z : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) Z ∧
      (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro F E _ _ _ _ _ σ n X v O _ c ι P Q JL hAe he hc hPQ hQP heP heQ hJ hlat M G ZL hM hMG hZL hN
  have heι : ∀ x, ι 1 * ι x = ι x := fun x => by rw [← map_mul, one_mul]
  have hιe : ∀ x, ι x * ι 1 = ι x := fun x => by rw [← map_mul, mul_one]
  have hee : ι 1 * ι 1 = ι 1 := heι 1
  have hce : cA σ (ι 1) = ι 1 := by rw [hc, map_one]
  have hmapE : ∀ {m k : Type} (Y : Matrix m k O), ι 1 • Y.map ι = Y.map ι := by
    intro m k Y; ext i j; simp [heι]
  have hePY : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n) k (AE F E)), ι 1 • (P * Y) = P * Y := by
    intro k _ Y; rw [← Matrix.smul_mul, heP]
  have hZP : P * ZL.map ι * Q * P = P * ZL.map ι := by
    rw [Matrix.mul_assoc, hQP, Matrix.mul_smul, Matrix.mul_one, hePY]
  have hvec : ∀ a : Fin n → O, Q *ᵥ (P *ᵥ fun i => ι (a i)) = fun i => ι (a i) := by
    intro a; rw [Matrix.mulVec_mulVec, hQP, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i; simp [heι]

  have hAtZ : At (evFin F v) (P * ZL.map ι * Q) := by
    intro u hu
    have hu' : u • Q = 0 := by rw [← heQ, ← smul_assoc, hAe u hu, zero_smul]
    rw [← Matrix.mul_smul, hu', Matrix.mul_zero]

  have hlatZ : ∀ z ∈ GlobalTheory.InertSph.latAt X v, (P * ZL.map ι * Q) *ᵥ z ∈ GlobalTheory.InertSph.latAt X v := by
    intro z hz
    obtain ⟨a, rfl⟩ := (hlat z).1 hz
    refine (hlat _).2 ⟨ZL *ᵥ a, ?_⟩
    rw [Matrix.mulVec_mulVec, hZP, ← Matrix.mulVec_mulVec, map_mulVec_gen]

  have hPcQc : P.map (cA σ) * Q.map (cA σ) = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [← map_mul_gen, hPQ]; ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h, hce]
  have h1 : Pᵀ * incM F X.J = JL.map ι * Q.map (cA σ) := by
    calc Pᵀ * incM F X.J = ι 1 • (Pᵀ * incM F X.J) := by
            rw [← Matrix.smul_mul, ← Matrix.transpose_smul, heP]
      _ = Pᵀ * incM F X.J * (P.map (cA σ) * Q.map (cA σ)) := by
            rw [hPcQc, Matrix.mul_smul, Matrix.mul_one]
      _ = JL.map ι * Q.map (cA σ) := by rw [← Matrix.mul_assoc, hJ]
  have hPc : ι 1 • P.map (cA σ) = P.map (cA σ) := by
    conv_rhs => rw [← heP]
    ext i j; simp [hce]
  have h2 : incM F X.J * P.map (cA σ) = Qᵀ * JL.map ι := by
    calc incM F X.J * P.map (cA σ) = ι 1 • (incM F X.J * P.map (cA σ)) := by
            rw [← Matrix.mul_smul, hPc]
      _ = (P * Q)ᵀ * incM F X.J * P.map (cA σ) := by
            rw [hPQ, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.smul_mul,
              Matrix.one_mul]
      _ = Qᵀ * JL.map ι := by
            rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Pᵀ, hJ]
  have hmapc : (ZL.map ι).map (cA σ) = (ZL.map c).map ι := by
    rw [Matrix.map_map, Matrix.map_map]; congr 1; funext x; exact hc x
  have hJZ : (P * ZL.map ι * Q)ᵀ * incM F X.J + incM F X.J * (P * ZL.map ι * Q).map (cA σ) = 0 := by
    have hz0 : (ZLᵀ * JL + JL * ZL.map c).map ι = 0 := by rw [hZL]; ext i j; simp
    rw [map_add_gen, map_mul_gen, map_mul_gen, Matrix.transpose_map] at hz0
    rw [map_mul_gen, map_mul_gen, hmapc, Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [h1, ← Matrix.mul_assoc (incM F X.J), h2]
    calc _ = Qᵀ * ((ZL.map ι)ᵀ * JL.map ι + JL.map ι * (ZL.map c).map ι) * Q.map (cA σ) := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hz0]; simp

  set N := ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL with hNdef
  set K := (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (P * ZL.map ι * Q) with hK
  have hNab : (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι = Matrix.fromRows (ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))) (-(ι 1 • 1)) := by
    rw [Matrix.fromRows_map, map_one_eq, map_neg_one_eq]
  have hDel : (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O)).map ι = Matrix.fromRows (ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E))) (ι 1 • 1) := by
    rw [Matrix.fromRows_map, map_one_eq]
  have hanti : GlobalTheory.DblVac.antiCols (F := F) (E := E) n * P = Matrix.fromBlocks P 0 0 P * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι := by
    rw [hNab, GlobalTheory.DblVac.antiCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp [Matrix.mul_smul, heP]
  have hdiag : ∀ Y : Matrix (Fin n) (Fin n) (AE F E), (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * (P * Y) = Matrix.fromBlocks P 0 0 P * ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O)).map ι * Y) := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDel, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp [Matrix.mul_smul, heP]
  have hantiT : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n ⊕ Fin n) k (AE F E)), (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * (Matrix.fromBlocks P 0 0 P * Y) = P * (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O)).map ι)ᵀ * Y) := by
    intro k _ Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hNab, GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows, Matrix.transpose_fromRows,
      Matrix.fromCols_mul_fromBlocks, Matrix.mul_fromCols]
    simp [Matrix.mul_smul, heP]
  have hMG' : ∀ {k : Type} [Fintype k] (Y : Matrix (Fin n ⊕ Fin n) k (AE F E)), M * (Matrix.fromBlocks P 0 0 P * Y) = Matrix.fromBlocks P 0 0 P * (G.map ι * Y) := by
    intro k _ Y; rw [← Matrix.mul_assoc, hMG, Matrix.mul_assoc]
  have hQPι : ZL.map ι * (Q * P) = ZL.map ι := by rw [hQP, Matrix.mul_smul, Matrix.mul_one, hmapE]
  have hKP : K * P = P * N.map ι := by
    rw [hK, Matrix.add_mul]
    refine (congrArg₂ (· + ·) (assoc_a _ _ _ _) (assoc_b _ _ _ _ _ _ _)).trans ?_
    rw [hanti, hQPι, hdiag, hMG', hMG', hantiT, hantiT, hNdef]
    simp only [map_add_gen, map_mul_gen, Matrix.transpose_map, Matrix.mul_add, Matrix.mul_assoc]

  have hN1 : N * N⁻¹ = 1 := Matrix.mul_nonsing_inv N hN
  have h2inv : algebraMap F (AE F E) 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap F (AE F E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hMe : ι 1 • (M - 1) = M - 1 := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    apply he
    intro u hu
    have := congrFun (congrFun (hM u hu) i) j
    simpa using this
  have hM1 : (1 - ι 1) • M = (1 - ι 1) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) := by
    rw [sub_smul, one_smul, sub_smul, one_smul, ← sub_eq_zero,
      show M - ι 1 • M - (1 - ι 1 • 1) = (M - 1) - (ι 1 • M - ι 1 • 1) by abel, ← smul_sub, hMe, sub_self]
  have hZe : (1 - ι 1) • (P * ZL.map ι * Q) = 0 := by
    rw [sub_smul, one_smul, ← Matrix.smul_mul, ← Matrix.smul_mul, heP, sub_self]
  have hAA : (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.antiCols n = (2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows]
    refine (Matrix.fromCols_mul_fromRows _ _ _ _).trans ?_
    simp [two_smul]
  have hKe : (1 - ι 1) • K = (1 - ι 1) • ((2 : AE F E) • (1 : Matrix (Fin n) (Fin n) (AE F E))) := by
    rw [hK, smul_add]
    refine (congrArg₂ (· + ·) (smul_mid_of _ _ _ _ hM1) (smul_last_of _ _ _ _ _ hZe)).trans ?_
    rw [add_zero]
    exact congrArg _ hAA
  set R := (algebraMap F (AE F E) 2⁻¹ * (1 - ι 1)) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + P * N⁻¹.map ι * Q with hR
  have hKR : K * R = 1 := by
    have hsec : K * (P * N⁻¹.map ι * Q) = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hKP, Matrix.mul_assoc P, ← map_mul_gen, hN1, map_one_eq,
        Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPQ, smul_smul, hee]
    rw [hR, Matrix.mul_add, hsec, Matrix.mul_smul, Matrix.mul_one, mul_smul, hKe, smul_smul, smul_smul, ← add_smul,
      show algebraMap F (AE F E) 2⁻¹ * (1 - ι 1) * 2 + ι 1 = (1 - ι 1) * (algebraMap F (AE F E) 2⁻¹ * 2) + ι 1 by ring,
      h2inv, mul_one, sub_add_cancel, one_smul]
  have hPz : ∀ w : Fin n → AE F E, (1 - ι 1) • (P *ᵥ w) = 0 := by
    intro w; rw [← Matrix.smul_mulVec, sub_smul, one_smul, heP, sub_self, Matrix.zero_mulVec]
  refine ⟨P * ZL.map ι * Q, hAtZ, hlatZ, hJZ, Matrix.isUnit_det_of_right_inverse hKR, ?_⟩
  intro z hz
  obtain ⟨a, rfl⟩ := (hlat z).1 hz
  rw [Matrix.inv_eq_right_inv hKR]
  refine (hlat _).2 ⟨N⁻¹ *ᵥ a, ?_⟩
  rw [hR, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, mul_smul, hPz, smul_zero, zero_add,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvec, map_mulVec_gen]

end GlobalTheory.TransportBack
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSkewHermitianCorrectionOfLocalSolutiStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_skewHermitian_correction_of_local_solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (v : Pl (F := F)) (O : Type) [CommRing O] (c : O →+* O) (ι : O →ₙ+* _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (P Q : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (ι 1) → (∀ y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) y → ι 1 * y = y) → (∀ x, cA σ (ι x) = ι (c x)) →
    P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) → Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) →
    ι 1 • P = P → ι 1 • Q = Q → Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι →
    (∀ z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O)
      (ZL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (M - 1) → M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    ZLᵀ * JL + JL * ZL.map c = 0 →
    IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL).det →
    ∃ Z : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z ∧
      (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  first | exact @GlobalTheory.TransportBack.transport_back | exact GlobalTheory.TransportBack.transport_back | (intros; apply GlobalTheory.TransportBack.transport_back <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFromBlocksNegOfDiagBasisTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFromBlocksNegOfDiagBasisTransport
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.fromBlocks_unitary_transfer : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (γ : A →+* A) (c : O →+* O) (n : ℕ)
    (P K : Matrix (Fin n) (Fin n) A) (JL : Matrix (Fin n) (Fin n) O),
    Function.Injective ι → (∀ x, γ (ι x) = ι (c x)) → Pᵀ * K * P.map γ = JL.map ι →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ = Matrix.fromBlocks K 0 0 (-K) →
    M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) := by
  intro A O _ _ ι γ c n P K JL hinj hγ hP M G hM hG
  have hmul : ∀ {m : Type} [Fintype m] (X Y : Matrix m m O), (X * Y).map ι = X.map ι * Y.map ι := by
    intro m _ X Y; ext i j; simp [Matrix.mul_apply, map_sum]
  have hneg : (-JL).map ι = -(JL.map ι) := by ext i j; simp
  have hD : (Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P).map γ
      = (Matrix.fromBlocks JL 0 0 (-JL)).map ι := by
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_map, hneg, ← hP]
    simp [Matrix.mul_neg, Matrix.neg_mul]
  have hc : (G.map c).map ι = (G.map ι).map γ := by
    ext i j; simp [hγ]
  apply Matrix.map_injective hinj
  show (Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c).map ι = (Matrix.fromBlocks JL 0 0 (-JL)).map ι
  rw [hmul, hmul, Matrix.transpose_map, hc]
  conv_lhs => rw [← hD]
  have hG' : (Matrix.fromBlocks P 0 0 P * G.map ι).map γ = (Matrix.fromBlocks P 0 0 P).map γ * (G.map ι).map γ := by
    rw [Matrix.map_mul]
  calc (G.map ι)ᵀ * ((Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P).map γ) * (G.map ι).map γ
      = (Matrix.fromBlocks P 0 0 P * G.map ι)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (Matrix.fromBlocks P 0 0 P * G.map ι).map γ := by
        rw [hG', Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = (M * Matrix.fromBlocks P 0 0 P)ᵀ * Matrix.fromBlocks K 0 0 (-K) * (M * Matrix.fromBlocks P 0 0 P).map γ := by rw [hG]
    _ = (Matrix.fromBlocks P 0 0 P)ᵀ * (Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ) * (Matrix.fromBlocks P 0 0 P).map γ := by
        rw [Matrix.map_mul, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hM, hD]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFromBlocksNegOfDiagBasisTransportStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_fromBlocks_neg_of_diag_basis_transport : ∀ (A O : Type) [CommRing A] [CommRing O] (ι : O →ₙ+* A) (γ : A →+* A) (c : O →+* O) (n : ℕ)
    (P K : Matrix (Fin n) (Fin n) A) (JL : Matrix (Fin n) (Fin n) O),
    Function.Injective ι → (∀ x, γ (ι x) = ι (c x)) → Pᵀ * K * P.map γ = JL.map ι →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) A) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    Mᵀ * Matrix.fromBlocks K 0 0 (-K) * M.map γ = Matrix.fromBlocks K 0 0 (-K) →
    M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) := by
  first | exact @GlobalTheory.fromBlocks_unitary_transfer | exact GlobalTheory.fromBlocks_unitary_transfer | (intros; apply GlobalTheory.fromBlocks_unitary_transfer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianCorrectionIsUnitAntidiagCorne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianCorrectionIsUnitAntidiagCorne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem GlobalTheory.HermBlockChange.exists_unit_lower_block : ∀ (O : Type) [CommRing O] (c : O →+* O), IsUnit (2 : O) →
    (∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
      ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
        gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
        ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) →
    ∀ (n : ℕ) (JL : Matrix (Fin n) (Fin n) O) (G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    (∀ i j, c (JL j i) = JL i j) → IsUnit JL.det → G * G' = 1 →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) →
    ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * JL + JL * Z.map c = 0 ∧
      IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * Z).det := by
  intro O _ c h2 hcore n JL G G' hJL hdet hGG' hG
  obtain ⟨a, ha⟩ : ∃ a : O, a * 2 = 1 := ⟨↑(h2.unit⁻¹), by simp⟩
  have ha' : (2 : O) * a = 1 := by rw [mul_comm, ha]
  have hca : c a = a := by
    have h1 : c a * 2 = 1 := by
      have := congrArg c ha
      rwa [map_mul, map_one, map_ofNat] at this
    calc c a = c a * (2 * a) := by rw [ha', mul_one]
      _ = (c a * 2) * a := by ring
      _ = a := by rw [h1, one_mul]
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) O := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) 1 with hΔ
  set Nb : Matrix (Fin n ⊕ Fin n) (Fin n) O := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1) with hNb
  set T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromCols Δ Nb with hTdef
  have hT : T = Matrix.fromBlocks 1 1 1 (-1) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [T, Δ, Nb]
  have hTt : Tᵀ = T := by
    rw [hT, Matrix.fromBlocks_transpose]; simp
  have hTc : T.map c = T := by
    rw [hT, Matrix.fromBlocks_map]; simp
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hTT : T * T = (2 : O) • 1 := by
    rw [hT, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    simp [two_smul]
  set J : Matrix (Fin n) (Fin n) O := (2 : O) • JL with hJ
  set K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromBlocks 0 J J 0 with hK
  set D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromBlocks JL 0 0 (-JL) with hD
  have hTKT : T * K * T = (4 : O) • D := by
    rw [hT, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
    simp [J]
    exact ⟨by rw [← add_smul]; norm_num, by rw [← neg_add, ← add_smul]; norm_num⟩
  have hTDT : T * D * T = K := by
    rw [hT, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [K, J, two_smul]
  have h4 : a * a * 4 = (1 : O) := by linear_combination (2 * a + 1) * ha
  set g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := a • (Tᵀ * G * T) with hg
  have hmapsmul : ∀ (b : O) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O), (b • M).map c = c b • M.map c := by
    intro b M; ext i j; simp
  have hgt : gᵀ = a • (T * Gᵀ * T) := by
    simp only [hg, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hTt, Matrix.mul_assoc]
  have hgc : g.map c = a • (T * G.map c * T) := by
    rw [hg, hTt, hmapsmul, Matrix.map_mul, Matrix.map_mul, hTc, hca]
  have hgK : gᵀ * K * g.map c = K := by
    rw [hgt, hgc]
    calc a • (T * Gᵀ * T) * K * a • (T * G.map c * T)
        = (a * a) • (T * Gᵀ * (T * K * T) * G.map c * T) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (a * a * 4) • (T * (Gᵀ * D * G.map c) * T) := by
          rw [hTKT]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = K := by rw [hG, h4, one_smul, hTDT]
  have hgdet : g * (a • (T * G' * T)) = 1 := by
    rw [hg, hTt]
    calc a • (T * G * T) * a • (T * G' * T)
        = (a * a) • (T * G * (T * T) * G' * T) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (a * a * 2) • (T * (G * G') * T) := by
          rw [hTT]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, Matrix.one_mul]
      _ = 1 := by
          rw [hGG', Matrix.mul_one, hTT, smul_smul, show a * a * 2 * 2 = (1 : O) by linear_combination (2 * a + 1) * ha, one_smul]
  have hJherm : ∀ i j, c (J j i) = J i j := by intro i j; simp only [J, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat, hJL]
  have hJdet : IsUnit J.det := by
    rw [hJ, Matrix.det_smul]; exact (h2.pow _).mul hdet
  obtain ⟨Z, hZ1, hZ2⟩ := hcore n J hJherm hJdet g (Matrix.isUnit_det_of_right_inverse hgdet) hgK
  refine ⟨Z, ?_, ?_⟩
  · have h := congrArg (fun M => a • M) hZ1
    simp only [J, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_smul, ha, one_smul, smul_zero] at h
    exact h
  · have hblk : Tᵀ * G * T = Matrix.fromBlocks (Δᵀ * G * Δ) (Δᵀ * G * Nb) (Nbᵀ * G * Δ) (Nbᵀ * G * Nb) := by
      rw [hTdef, Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    have h21 : g.toBlocks₂₁ = a • (Nbᵀ * G * Δ) := by
      rw [hg, hblk, Matrix.fromBlocks_smul, Matrix.toBlocks_fromBlocks₂₁]
    have h22 : g.toBlocks₂₂ = a • (Nbᵀ * G * Nb) := by
      rw [hg, hblk, Matrix.fromBlocks_smul, Matrix.toBlocks_fromBlocks₂₂]
    have hE : Nbᵀ * G * Nb + Nbᵀ * G * Δ * Z = (2 : O) • (g.toBlocks₂₁ * Z + g.toBlocks₂₂) := by
      rw [h21, h22, Matrix.smul_mul, ← smul_add, smul_smul, ha', one_smul, add_comm]
    rw [hE, Matrix.det_smul]; exact (h2.pow _).mul hZ2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianCorrectionIsUnitAntidiagCorneStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_correction_isUnit_antidiag_corner : ∀ (O : Type) [CommRing O] (c : O →+* O), IsUnit (2 : O) →
    (∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
      ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
        gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
        ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) →
    ∀ (n : ℕ) (JL : Matrix (Fin n) (Fin n) O) (G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    (∀ i j, c (JL j i) = JL i j) → IsUnit JL.det → G * G' = 1 →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) →
    ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * JL + JL * Z.map c = 0 ∧
      IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * Z).det := by
  first | exact @GlobalTheory.HermBlockChange.exists_unit_lower_block | exact GlobalTheory.HermBlockChange.exists_unit_lower_block | (intros; apply GlobalTheory.HermBlockChange.exists_unit_lower_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceTransversalOfLocalCore
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.TransvChoose

theorem exists_transversal : (∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ Z : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z ∧ (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro core F E _ _ _ _ _ σ B n r s X hB hX v w hw g hg
  obtain ⟨O, _, c, ι, P, Q, JL, hloc, hcc, h2, hcx, hinj, hAt, hsupp, hcι, hPQ, hQP, hP, hQ, hJh, hJu, hJ, hlat⟩ :=
    GlobalTheory.T.exists_local_dictionary_inertPlace F E σ B n r s X hB hX v w hw
  haveI := hloc
  obtain ⟨hg1, hg2⟩ := hg
  have hinv : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := by
    simp [GlobalTheory.DblVac.matD]
  obtain ⟨G, G', hGG, hMG⟩ := GlobalTheory.T.exists_inverse_integral_matrices_preserving_doubled_lattice (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) O ι n P Q (GlobalTheory.InertSph.latAt X v : Set (Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) hinj hPQ hQP hP hQ
    (fun z => hlat z) (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv (fun z h1 h2 => by
      obtain ⟨ha, hb⟩ := hg2 z ⟨h1, h2⟩
      exact ⟨ha.1, ha.2, hb.1, hb.2⟩)
  have hgU : (GlobalTheory.DblVac.matD g)ᵀ * Matrix.fromBlocks (incM F X.J) 0 0 (-incM F X.J) * (GlobalTheory.DblVac.matD g).map (cA σ).toRingHom =
      Matrix.fromBlocks (incM F X.J) 0 0 (-incM F X.J) := g.2
  have hU := GlobalTheory.T.unitary_fromBlocks_neg_of_diag_basis_transport (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) O ι (cA σ).toRingHom c n P (incM F X.J) JL hinj hcι hJ (GlobalTheory.DblVac.matD g) G hgU hMG
  obtain ⟨ZL, hZL1, hZL2⟩ := GlobalTheory.T.exists_skewHermitian_correction_isUnit_antidiag_corner O c h2 (fun n J hJ hJd g hgd hgu => core O c hcc h2 hcx n J hJ hJd g hgd hgu)
    n JL G G' hJh hJu hGG hU
  exact GlobalTheory.T.exists_adelic_skewHermitian_correction_of_local_solution F E σ n X v O c ι P Q JL hAt hsupp hcι hPQ hQP hP hQ hJ hlat (GlobalTheory.DblVac.matD g) G ZL hg1 hMG hZL1 hZL2

end GlobalTheory.TransvChoose
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceTransversalOfLocalCoreStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertPlace_transversal_of_localCore : (∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ Z : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z ∧ (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  first | exact @GlobalTheory.TransvChoose.exists_transversal | exact GlobalTheory.TransvChoose.exists_transversal | (intros; apply GlobalTheory.TransvChoose.exists_transversal <;> assumption)
end
