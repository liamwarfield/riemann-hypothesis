module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqConstMulProdInnerOfSlotwise
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
noncomputable section

namespace GlobalTheory.AdelicFrame

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_idem_adele (m : ℕ) (hm : 0 < m) :
    ∃ f ∈ Formalism.UG.intAd F, f * f = f ∧ (∃ w ∈ Formalism.UG.intAd F, f = (m : FiniteAdeleRing (𝓞 F) F) * w) ∧
      ∀ n : ℕ, 0 < n → m.Coprime n → ∃ w ∈ Formalism.UG.intAd F, 1 - f = (n : FiniteAdeleRing (𝓞 F) F) * w := by
  obtain ⟨h1, h2⟩ := integral_finiteAdele_complete_separated F
  refine GlobalTheory.IdealIdele.exists_idem (Formalism.UG.intAd F) (fun y hy => h1 y fun N hN => ?_) (fun x hx hc => ?_) m hm
  · obtain ⟨w, hw, e⟩ := hy N hN
    exact ⟨w, hw, by rw [nsmul_eq_mul]; exact e⟩
  · obtain ⟨y, hy⟩ := h2 x hx fun N k hN hk => by
      obtain ⟨w, hw, e⟩ := hc N k hN hk
      exact ⟨w, hw, by rw [nsmul_eq_mul]; exact e⟩
    refine ⟨y, ?_, fun N hN => ?_⟩
    · obtain ⟨a, ha, e⟩ := hy 1 one_pos
      rw [e, one_smul]
      exact add_mem (hx 1) ha
    · obtain ⟨a, ha, e⟩ := hy N hN
      exact ⟨a, ha, by rw [← nsmul_eq_mul]; exact e⟩

theorem exists_generator_int (B : Ideal (𝓞 E)) (hB : B ≠ ⊥) :
    ∃ y y' : RA F E, y * y' = 1 ∧ y ∈ hat1 F ((B : FractionalIdeal (𝓞 E)⁰ E) : Set E) ∧
      y' ∈ hat1 F (((B : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  obtain ⟨m, n, β, hm, hn, hmn, hmB, hβB, hβ0, hdvd⟩ := GlobalTheory.IdealIdele.exists_local_generator B hB
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := exists_idem_adele F m hm
  obtain ⟨v, hv, hfv⟩ := h3 n hn hmn
  have hβE : (β : E) ≠ 0 := by simpa using hβ0
  have hnat : ∀ (k : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : E),
      ((k : FiniteAdeleRing (𝓞 F) F) * a) ⊗ₜ[F] x = a ⊗ₜ[F] ((k : E) * x) := by
    intro k a x
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F,
      TensorProduct.smul_tmul]
  refine ⟨(1 - f) ⊗ₜ (β : E) + f ⊗ₜ 1, (1 - f) ⊗ₜ (β : E)⁻¹ + f ⊗ₜ 1, ?_, add_mem ?_ ?_, ?_⟩
  · have e1 : (1 - f) * (1 - f) = 1 - f := by linear_combination hff
    have e2 : (1 - f) * f = 0 := by linear_combination -hff
    have e3 : f * (1 - f) = 0 := by linear_combination -hff
    simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, e1, e2, e3, hff, TensorProduct.zero_tmul,
      mul_inv_cancel₀ hβE, mul_one, add_zero, zero_add]
    rw [← TensorProduct.add_tmul, sub_add_cancel, Algebra.TensorProduct.one_def]
  · exact tmul_mem_adelicCompletion_of_integral F (sub_mem (one_mem _) hf : _ ∈ Formalism.UG.intAd F)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hβB)
  · rw [hfw, hnat, mul_one]
    refine tmul_mem_adelicCompletion_of_integral F hw ?_
    have := FractionalIdeal.mem_coeIdeal_of_mem (P := E) (𝓞 E)⁰ hmB
    rwa [map_natCast] at this
  · have := mem_adelicCompletion_mul_inv_fractionalIdeal F (B : FractionalIdeal (𝓞 E)⁰ E) 1 ((1 - f) ⊗ₜ (β : E)⁻¹ + f ⊗ₜ 1)
      (FractionalIdeal.coeIdeal_ne_zero.2 hB) fun x hx => by
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
        obtain ⟨d, hd⟩ := hdvd b hb
        have hd' : (n : E) * algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E β * algebraMap (𝓞 E) E d := by
          rw [← map_mul, ← hd, map_mul, map_natCast]
        simp only [add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        refine add_mem ?_ (tmul_mem_adelicCompletion_of_integral F hf ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩))
        rw [hfv, hnat]
        refine tmul_mem_adelicCompletion_of_integral F hv ((FractionalIdeal.mem_one_iff _).2 ⟨d, ?_⟩)
        rw [mul_left_comm, hd']
        exact (inv_mul_cancel_left₀ hβE _).symm
    rwa [one_mul] at this

theorem exists_generator (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) :
    ∃ y y' : RA F E, y * y' = 1 ∧ y ∈ hat1 F (I : Set E) ∧
      y' ∈ hat1 F ((I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  obtain ⟨a, B, ha, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hB : B ≠ ⊥ := by
    rintro rfl
    simp at hI
  have haE : algebraMap (𝓞 E) E a ≠ 0 := by simpa using ha
  obtain ⟨y, y', h, hy, hy'⟩ := exists_generator_int F B hB
  refine ⟨(1 ⊗ₜ (algebraMap (𝓞 E) E a)⁻¹) * y, (1 ⊗ₜ (algebraMap (𝓞 E) E a)) * y', ?_, ?_, ?_⟩
  · rw [mul_mul_mul_comm, h, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ haE, mul_one, mul_one,
      Algebra.TensorProduct.one_def]
  · exact (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.mem_spanSingleton_self _ _)) _ hy
  · rw [mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
    exact (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.mem_spanSingleton_self _ _)) _ hy'

theorem mem_integral_adelic_lattice_iff (z : RA F E) :
    z ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) ↔
      Algebra.TensorProduct.comm F _ E z ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      have h1 : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
      have h2 : (algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) ∈ Formalism.L2.Herm.intAf F E :=
        Subring.subset_closure (Or.inl ⟨⟨_, c, rfl⟩, rfl⟩)
      have := mul_mem h1 h2
      rwa [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at this
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  · intro hz
    have key : ∀ t ∈ Formalism.L2.Herm.intAf F E, (Algebra.TensorProduct.comm F _ E).symm t ∈
        hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
      intro t ht
      induction ht using Subring.closure_induction with
      | mem z hz =>
        rcases hz with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩
        · exact one_tmul_mem_adelicCompletionOfElementSet F ((FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩)
        · exact tmul_mem_adelicCompletion_of_integral F b.2 (FractionalIdeal.one_mem_one _)
      | zero => rw [map_zero]; exact zero_mem _
      | one => rw [map_one]; exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | neg a _ ha => rw [map_neg]; exact neg_mem ha
      | mul a b _ _ ha hb =>
        rw [map_mul]
        have := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ ha _ hb
        rwa [mul_one] at this
    simpa only [AlgEquiv.symm_apply_apply] using key _ hz

theorem exists_basis_hat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ P Q : Matrix (Fin n) (Fin n) (RA F E), P * Q = 1 ∧ Q * P = 1 ∧ ∀ z, z ∈ hat F (L : Set (Fin n → E)) ↔
      ∀ a, (Q *ᵥ z) a ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  choose y y' hyy hy hy' using fun a => exists_generator F (cI a) (hc a)
  have hD : Matrix.diagonal y * Matrix.diagonal y' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    exact hyy a
  have h1 : P * Matrix.diagonal y * (Matrix.diagonal y' * Q) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ Q, hD, Matrix.one_mul, hPQ]
  refine ⟨_, _, h1, mul_eq_one_comm.1 h1, fun z => ?_⟩
  have hz : z = P *ᵥ (Q *ᵥ z) := by rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  conv_lhs => rw [hz, hP, key]
  refine forall_congr' fun a => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  constructor
  · intro h
    have := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (hy' a) _ h
    rwa [inv_mul_cancel₀ (hc a)] at this
  · intro h
    have := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (hy a) _ h
    rwa [mul_one, ← mul_assoc, hyy, one_mul] at this

theorem exists_isFrame {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), Formalism.L2.DIV.IsFrame β L := by
  obtain ⟨P, Q, hPQ, hQP, h⟩ := exists_basis_hat F L hfg hsp
  let s := Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E
  have hm : ∀ A B : Matrix (Fin n) (Fin n) (RA F E), A * B = 1 → A.map s * B.map s = 1 := fun A B hAB => by
    rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨P.map s, Q.map s, hm _ _ hPQ, hm _ _ hQP⟩, fun x => ?_⟩
  have e : ∀ i, (Q.map s *ᵥ x) i = s ((Q *ᵥ fun j => s.symm (x j)) i) := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.apply_symm_apply, Matrix.map_apply]
  change _ ↔ ∀ i, (Q.map s *ᵥ x) i ∈ _
  simp only [e]
  constructor
  · intro hx i
    exact (mem_integral_adelic_lattice_iff F _).1 ((h _).1 (GlobalTheory.PrincInLevel.swap_symm_mem_hat L x hx) i)
  · intro hx
    have := GlobalTheory.PrincInLevel.swap_mem_hatL L _ ((h _).2 fun i => (mem_integral_adelic_lattice_iff F _).2 (hx i))
    simpa only [s, AlgEquiv.apply_symm_apply] using this

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isSDFrame : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (Λ : Set (Fin V.rank → D.host.E)) = L0c D V → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∃ β, IsSDFrame V β Λ 1 := by
  intro D V Λ hΛ hd
  have hl : Λ = GlobalTheory.Member.latC V := SetLike.coe_injective (hΛ.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V).symm)
  have hfg : Λ.FG := hl ▸ V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have h1 : (Λ : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := by
      rw [hl]; rfl
    rw [h1, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  obtain ⟨β, hβ⟩ := exists_isFrame D.host.F Λ hfg hsp
  refine ⟨β, 0, hβ, hd, one_pos, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pow_zero, Nat.cast_one, one_smul]
    rw [← hΛ] at hx
    exact hx
  · rw [pow_zero, Nat.cast_one, one_smul, ← hΛ]
    exact hx

end GlobalTheory.AdelicFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_adelic_frame_level_one : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (Λ : Set (Fin V.rank → D.host.E)) = L0c D V → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∃ β, IsSDFrame V β Λ 1 := by
  first | exact @GlobalTheory.AdelicFrame.exists_isSDFrame | exact GlobalTheory.AdelicFrame.exists_isSDFrame | (intros; apply GlobalTheory.AdelicFrame.exists_isSDFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeCoefficientWeightEqMinorWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeCoefficientWeightEqMinorWeights
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm


open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes in
theorem weights_of_minors : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), σ = D.what₂.embLL → ∀ M : DSModel (Wc D i) (parAt (Wc D i) σ), (∀ τ a, M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) → ∃ x₁ x₂ x₃ : D.what₂.Tau → ℤ, ∀ τ, (x₁ τ : ℚ) = -(D.hc τ).e i + ((Vc D i).rank : ℚ) / 2 ∧ (x₂ τ : ℚ) = -(D.hc τ).e i - ((Vc D i).rank : ℚ) / 2 ∧ (x₃ τ : ℚ) = -(((((Wc D i).sig (tauE D τ)).1 : ℚ) - ((Wc D i).sig (tauE D τ)).2) / 2 + (-(D.hc τ).e i - 1 / 2)) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK ((Wc D i).sig (tauE D τ)).1 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₁ τ) (x₂ τ) a : ℝ)) ∧ ∀ j : Fin (Vc D i).rank, wtU ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₃ τ) j = -(Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j := by
  intro D i σ hσ M _
  subst hσ
  have hnr : ∃ s : ℕ, D.R.r + D.R.t = 2 * s := by
    obtain ⟨a, ha⟩ := Formalism.L2.NTheta.odd_r D.R
    obtain ⟨b, hb⟩ := D.R.t_odd
    exact ⟨a + b + 1, by omega⟩
  obtain ⟨s, hs⟩ := hnr
  have hsq : (D.R.r : ℚ) + D.R.t = 2 * s := by exact_mod_cast hs
  choose e he using fun τ : D.what₂.Tau => (D.hc τ).e_int i
  choose d hd using fun τ : D.what₂.Tau => (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).d_int
  refine ⟨fun τ => -e τ + s, fun τ => -e τ - s, fun τ => -d τ, fun τ => ?_⟩
  have A := GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ
  obtain ⟨hpq, hV⟩ := A.rank
  have hVq : ((Vc D i).rank : ℚ) = 2 * s := by rw [hV, hs]; push_cast; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [he, hVq]; push_cast; ring
  · rw [he, hVq]; push_cast; ring
  · have := hd τ
    unfold dShift at this
    push_cast
    rw [← this]
    ring
  · have hen := M.enum τ
    rw [GlobalTheory.ThetaFiresProbe.parAt_fixed] at hen
    obtain ⟨hn, hx⟩ := GlobalTheory.HolDS.lowK_holPar (Formalism.L2.NTheta.holOK_kapW (D.hc τ) _ _ hpq) hen
    intro a
    obtain ⟨x, rfl⟩ : ∃ x, a = Fin.cast hn (finSumFinEquiv x) :=
      ⟨finSumFinEquiv.symm (Fin.cast hn.symm a), by simp⟩
    rw [hx x]
    congr 1
    rcases x with c | c
    · have h1 := A.kap_plus c
      rw [hsq, eS, he] at h1
      have h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) = (aP D i τ c : ℤ) + (-e τ + s) := by
        have : ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) : ℤ) : ℚ) =
            (((aP D i τ c : ℤ) + (-e τ + s) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
        exact_mod_cast this
      rw [h2]
      unfold wtK
      rw [if_pos (by simp)]
      simp
    · have h1 := A.kap_minus c
      rw [hsq, eS, he] at h1
      have h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) =
          -(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e τ - s) := by
        have : ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) : ℤ) : ℚ) =
            ((-(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e τ - s) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
        exact_mod_cast this
      rw [h2]
      unfold wtK
      rw [if_neg (by simp)]
      have h3 : (Wc D i).rank - 1 - ((Fin.cast hn (finSumFinEquiv (Sum.inr c)) : Fin (Wc D i).rank) : ℕ) =
          qS D i τ - 1 - c := by
        simp only [finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd]
        rw [← hn]
        simp only [qS]
        omega
      rw [h3]
  · intro j
    have h1 := A.coef_eq j
    rw [hd] at h1
    have h2 : (Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j = thetaWt D i τ j + d τ := by
      exact_mod_cast h1
    rw [h2]
    have hj := j.2
    unfold wtU thetaWt
    simp only [pS, qS] at hpq ⊢
    by_cases c1 : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1
    · have ht := D.R.three_m_lt_t
      rw [if_pos c1, if_pos c1, if_neg (by omega)]
      ring
    · rw [if_neg c1, if_neg c1]
      by_cases c2 : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1 + D.R.t
      · rw [if_pos c2, if_neg (by omega)]
        ring
      · rw [if_neg c2, if_pos (by omega)]
        have h3 : (Vc D i).rank - 1 - (j : ℕ) = ((Wc D i).sig (tauE D τ)).2 - 1 - (j - (((Wc D i).sig (tauE D τ)).1 + D.R.t)) := by
          omega
        rw [h3]
        ring

end GlobalTheory.JointHarm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeCoefficientWeightEqMinorWeightsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), σ = D.what₂.embLL → ∀ M : DSModel (Wc D i) (parAt (Wc D i) σ), (∀ τ a, M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) → ∃ x₁ x₂ x₃ : D.what₂.Tau → ℤ, ∀ τ, (x₁ τ : ℚ) = -(D.hc τ).e i + ((Vc D i).rank : ℚ) / 2 ∧ (x₂ τ : ℚ) = -(D.hc τ).e i - ((Vc D i).rank : ℚ) / 2 ∧ (x₃ τ : ℚ) = -(((((Wc D i).sig (tauE D τ)).1 : ℚ) - ((Wc D i).sig (tauE D τ)).2) / 2 + (-(D.hc τ).e i - 1 / 2)) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK ((Wc D i).sig (tauE D τ)).1 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₁ τ) (x₂ τ) a : ℝ)) ∧ ∀ j : Fin (Vc D i).rank, wtU ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₃ τ) j = -(Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j := by
  first | exact @GlobalTheory.JointHarm.weights_of_minors | exact GlobalTheory.JointHarm.weights_of_minors | (intros; apply GlobalTheory.JointHarm.weights_of_minors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivedActionSmoothVectorRealLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivedActionSmoothVectorRealLinear
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecLinear

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem lieG_add {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) (hY : Y ∈ lieG G) : X + Y ∈ lieG G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  have h2 : Yᴴ * G + G * Y = 0 := hY
  show (X + Y)ᴴ * G + G * (X + Y) = 0
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, h1, h2, add_zero]

theorem lieG_smul (a : ℝ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieG G) : a • X ∈ lieG G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  show (a • X)ᴴ * G + G * (a • X) = 0
  rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]

theorem gard_add (hσ : IsURepOn (UJset ε) σ) {φ ψ : Matrix (Fin n) (Fin n) ℂ → ℝ} (hφ : IsTest φ) (hψ : IsTest ψ)
    (w : H) : gard ε σ (φ + ψ) w = gard ε σ φ w + gard ε σ ψ w := by
  unfold gard
  rw [← integral_add (hφ.integrable (continuous_orbit hσ w)) (hψ.integrable (continuous_orbit hσ w))]
  simp only [Pi.add_apply, add_smul]

theorem gard_smul (a : ℝ) (φ : Matrix (Fin n) (Fin n) ℂ → ℝ) (w : H) :
    gard ε σ (a • φ) w = (a : ℂ) • gard ε σ φ w := by
  unfold gard
  rw [← integral_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Complex.coe_smul]

theorem dRep_linear : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ w ∈ smSub G (trRep σ P), (∀ X ∈ lieG G, ∀ Y ∈ lieG G, dRep (trRep σ P) (X + Y) w = dRep (trRep σ P) X w + dRep (trRep σ P) Y w) ∧ ∀ (a : ℝ), ∀ X ∈ lieG G, dRep (trRep σ P) (a • X) w = (a : ℂ) • dRep (trRep σ P) X w := by
  intro n ε H _ _ _ σ P G hP h hσ w hw
  have hG := gram_unit hP h
  have hπ := isURepOn_trRep hP h hσ
  refine ⟨fun X hX Y hY => ?_, fun a X hX => ?_⟩
  · refine sub_eq_zero.1 (eq_zero_of_inner_gard hσ fun φ hφ v => ?_)
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.gardingVector_derivative_eq_gardingVector n ε H σ P G hP h hσ φ hφ
    have hu := gard_mem hP h hσ hφ v
    rw [inner_sub_right, inner_add_right, inner_dRep hG hπ hu hw hX, inner_dRep hG hπ hu hw hY,
      inner_dRep hG hπ hu hw (lieG_add hX hY), (hψ X).2 hX, (hψ Y).2 hY, (hψ _).2 (lieG_add hX hY), map_add,
      gard_add hσ (hψ X).1 (hψ Y).1, inner_add_left]
    ring
  · refine sub_eq_zero.1 (eq_zero_of_inner_gard hσ fun φ hφ v => ?_)
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.gardingVector_derivative_eq_gardingVector n ε H σ P G hP h hσ φ hφ
    have hu := gard_mem hP h hσ hφ v
    rw [inner_sub_right, inner_smul_right, inner_dRep hG hπ hu hw hX,
      inner_dRep hG hπ hu hw (lieG_smul a hX), (hψ X).2 hX, (hψ _).2 (lieG_smul a hX), map_smul,
      gard_smul, inner_smul_left, Complex.conj_ofReal]
    ring

end GlobalTheory.SmVecLinear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivedActionSmoothVectorRealLinearStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derived_action_smooth_vector_real_linear : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ w ∈ smSub G (trRep σ P), (∀ X ∈ lieG G, ∀ Y ∈ lieG G, dRep (trRep σ P) (X + Y) w = dRep (trRep σ P) X w + dRep (trRep σ P) Y w) ∧ ∀ (a : ℝ), ∀ X ∈ lieG G, dRep (trRep σ P) (a • X) w = (a : ℂ) • dRep (trRep σ P) X w := by
  first | exact @GlobalTheory.SmVecLinear.dRep_linear | exact GlobalTheory.SmVecLinear.dRep_linear | (intros; apply GlobalTheory.SmVecLinear.dRep_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorProductDefiniteUnitaryLocalModelsIrreducib
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorProductDefiniteUnitaryLocalModelsIrreducib
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift

theorem subalgebra_eq_top_of_irreducible {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (A : Subalgebra ℂ (Module.End ℂ X))
    (h : ∀ U : Submodule ℂ X, (∀ a ∈ A, ∀ x ∈ U, a x ∈ U) → U = ⊥ ∨ U = ⊤) : A = ⊤ := by
  classical
  rcases subsingleton_or_nontrivial X with hX | hX
  · refine eq_top_iff.2 fun f _ => ?_
    rw [Subsingleton.elim f 0]
    exact A.zero_mem
  haveI : IsSimpleModule A X := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun U => ?_ }
    rcases h (U.restrictScalars ℂ) (fun a ha x hx => U.smul_mem (⟨a, ha⟩ : A) hx) with h1 | h1
    · left
      exact (Submodule.restrictScalars_eq_bot_iff ℂ A X).1 h1
    · right
      exact (Submodule.restrictScalars_eq_top_iff ℂ A X).1 h1
  have hscal : ∀ φ : Module.End A X, ∃ c : ℂ, ∀ m, φ m = c • m := by
    intro φ
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := X) ℂ).2 φ
    exact ⟨c, fun m => by rw [← hc]; rfl⟩
  refine eq_top_iff.2 fun f _ => ?_
  let F : Module.End (Module.End A X) X :=
    { toFun := fun m => f m
      map_add' := fun x y => by simp
      map_smul' := fun φ m => by
        obtain ⟨c, hc⟩ := hscal φ
        simp only [Module.End.smul_def, RingHom.id_apply, hc, map_smul] }
  let b := Module.finBasis ℂ X
  obtain ⟨r, hr⟩ := jacobson_density F (Finset.univ.image b)
  have : f = (r : Module.End ℂ X) :=
    b.ext fun i => hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]
  exact r.2

theorem piTensor_irreducible {ι κ : Type} [Finite ι] [DecidableEq ι] {H : ι → Type} [∀ i, AddCommGroup (H i)]
    [∀ i, Module ℂ (H i)] [∀ i, FiniteDimensional ℂ (H i)] (σ : ∀ i, κ → Module.End ℂ (H i))
    (h : ∀ i, ∀ U : Submodule ℂ (H i), (∀ u, ∀ x ∈ U, σ i u x ∈ U) → U = ⊥ ∨ U = ⊤)
    (U : Submodule ℂ (⨂[ℂ] i, H i))
    (hU : ∀ i u, ∀ x ∈ U,
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i (σ i u)) x ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  cases nonempty_fintype ι
  have hcomp : ∀ (f g : ∀ i, H i →ₗ[ℂ] H i) (x : ⨂[ℂ] i, H i),
      PiTensorProduct.map (fun i => f i ∘ₗ g i) x = PiTensorProduct.map f (PiTensorProduct.map g x) := by
    intro f g x
    rw [PiTensorProduct.map_comp]; rfl
  have h1 : ∀ i (a : Module.End ℂ (H i)), ∀ x ∈ U,
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i a) x ∈ U := by
    intro i
    let A : Subalgebra ℂ (Module.End ℂ (H i)) :=
      { carrier := {a | ∀ x ∈ U,
          PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i a) x ∈ U}
        mul_mem' := fun {a b} ha hb x hx => by
          have := ha _ (hb x hx)
          rw [← hcomp] at this
          convert this using 3
          funext ρ
          by_cases hρ : ρ = i
          · subst hρ; simp [Module.End.mul_eq_comp]
          · simp [Function.update_of_ne hρ]
        add_mem' := fun {a b} ha hb x hx => by
          rw [PiTensorProduct.map_update_add]
          exact U.add_mem (ha x hx) (hb x hx)
        algebraMap_mem' := fun c x hx => by
          rw [Algebra.algebraMap_eq_smul_one, PiTensorProduct.map_update_smul]
          have : Function.update (fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ)) i (1 : Module.End ℂ (H i)) =
              fun ρ => (LinearMap.id : H ρ →ₗ[ℂ] H ρ) := Function.update_eq_self i _
          rw [this, PiTensorProduct.map_id]
          exact U.smul_mem c hx }
    have hA : A = ⊤ := subalgebra_eq_top_of_irreducible A fun W hW =>
      h i W fun u x hx => hW (σ i u) (hU i u) x hx
    intro a
    have : a ∈ A := hA ▸ Algebra.mem_top
    exact this
  have h2 : ∀ (f : ∀ i, H i →ₗ[ℂ] H i) (s : Finset ι), ∀ x ∈ U,
      PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) x ∈ U := by
    intro f s
    induction s using Finset.induction_on with
    | empty => intro x hx; simpa using hx
    | insert j s hj ih =>
      intro x hx
      have := h1 j (f j) _ (ih x hx)
      rw [← hcomp] at this
      convert this using 3
      funext ρ
      by_cases hρ : ρ = j
      · subst hρ; simp [hj]
      · simp [hρ]
  have h3 : ∀ (f : ∀ i, H i →ₗ[ℂ] H i), ∀ x ∈ U, PiTensorProduct.map f x ∈ U := by
    intro f x hx
    simpa using h2 f Finset.univ x hx
  rw [or_iff_not_imp_left]
  intro hne
  obtain ⟨x, hxU, hx⟩ := (Submodule.ne_bot_iff U).1 hne
  let b := fun i => Module.finBasis ℂ (H i)
  let B := Basis.piTensorProduct b
  obtain ⟨p, hp⟩ : ∃ p, B.repr x p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (B.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have e : PiTensorProduct.map (fun i => ((b i).coord (p i)).smulRight (v i)) =
      (B.coord p).smulRight (PiTensorProduct.tprod ℂ v) := by
    ext w
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.smulRight_apply,
      Module.Basis.coord_apply, B, Basis.piTensorProduct_repr_tprod_apply]
    exact (PiTensorProduct.tprod ℂ).map_smul_univ _ v
  have h4 := h3 (fun i => ((b i).coord (p i)).smulRight (v i)) x hxU
  rw [e] at h4
  exact (U.smul_mem_iff hp).1 h4

theorem tensor_irreducible : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ ∀ U : Submodule ℂ (M.H τ), (∀ u : Matrix.unitaryGroup (Fin V.rank) ℂ, ∀ x ∈ U, M.σ τ u x ∈ U) → U = ⊥ ∨ U = ⊤) → AllPlus M → FiniteDimensional ℂ (SmT M) ∧ Function.Injective (inclT M) ∧ ∃ π, IsTensAct M π ∧ IrrFam π := by
  intro D V S M h _
  classical
  haveI := fun τ => (h τ).1
  let e : SmT M ≃ₗ[ℂ] ⨂[ℂ] τ, M.H τ := PiTensorProduct.congr fun τ => LinearEquiv.ofTop (M.sm τ) (h τ).2.1
  have he : ∀ x, e x = inclT M x := fun x => rfl
  refine ⟨inferInstance, fun x y hxy => e.injective hxy,
    fun τ u => e.symm.toLinearMap ∘ₗ actT M τ (unfr M τ u) ∘ₗ e.toLinearMap, fun τ u x => ?_, fun U hU => ?_⟩
  · rw [← he, ← he]
    simp
  · have := piTensor_irreducible (fun τ (u : Matrix.unitaryGroup (Fin V.rank) ℂ) => (M.σ τ u : M.H τ →ₗ[ℂ] M.H τ))
      (fun τ => (h τ).2.2) (U.map e.toLinearMap) (by
        rintro τ u _ ⟨x, hx, rfl⟩
        refine ⟨_, hU τ u x hx, ?_⟩
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, actT, rep_unfr])
    rcases this with h1 | h1
    · exact Or.inl ((Submodule.map_eq_bot_iff).1 h1)
    · exact Or.inr ((Submodule.map_eq_top_iff).1 h1)

end GlobalTheory.DefLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorProductDefiniteUnitaryLocalModelsIrreducibStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorProduct_definiteUnitary_localModels_irreducible : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), (∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤ ∧ ∀ U : Submodule ℂ (M.H τ), (∀ u : Matrix.unitaryGroup (Fin V.rank) ℂ, ∀ x ∈ U, M.σ τ u x ∈ U) → U = ⊥ ∨ U = ⊤) → AllPlus M → FiniteDimensional ℂ (SmT M) ∧ Function.Injective (inclT M) ∧ ∃ π, IsTensAct M π ∧ IrrFam π := by
  first | exact @GlobalTheory.DefLift.tensor_irreducible | exact GlobalTheory.DefLift.tensor_irreducible | (intros; apply GlobalTheory.DefLift.tensor_irreducible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomia
noncomputable section

open MvPolynomial

namespace GlobalTheory.DefLift.BilFischer

variable {σ : Type} [Fintype σ]

def wt (α : σ →₀ ℕ) : ℂ := ∏ v, ((α v).factorial : ℂ)

theorem wt_ne_zero (α : σ →₀ ℕ) : wt α ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

theorem wt_add_single (α : σ →₀ ℕ) (v : σ) : wt (α + Finsupp.single v 1) = wt α * ((α v : ℂ) + 1) := by
  classical
  unfold wt
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v),
    ← Finset.mul_prod_erase _ (fun x => ((α x).factorial : ℂ)) (Finset.mem_univ v)]
  have h3 : ∏ x ∈ Finset.univ.erase v, (((α + Finsupp.single v 1 : σ →₀ ℕ) x).factorial : ℂ) =
      ∏ x ∈ Finset.univ.erase v, ((α x).factorial : ℂ) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxv : x ≠ v := Finset.ne_of_mem_erase hx
    simp [Finsupp.single_apply, Ne.symm hxv]
  rw [h3]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

def pair : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  (basisMonomials σ ℂ).constr ℂ fun α => wt α • lcoeff ℂ α

theorem pair_monomial_one (α : σ →₀ ℕ) (Q : MvPolynomial σ ℂ) :
    pair (monomial α 1) Q = wt α * AddMonoidAlgebra.coeff Q α := by
  have := (basisMonomials σ ℂ).constr_basis ℂ (fun α => wt α • lcoeff ℂ α) α
  rw [coe_basisMonomials] at this
  unfold pair
  rw [this]
  simp

theorem pair_monomial (α : σ →₀ ℕ) (c : ℂ) (Q : MvPolynomial σ ℂ) :
    pair (monomial α c) Q = c * (wt α * AddMonoidAlgebra.coeff Q α) := by
  have : (monomial α c : MvPolynomial σ ℂ) = c • monomial α 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply, pair_monomial_one, smul_eq_mul]

theorem pair_mul_X (P Q : MvPolynomial σ ℂ) (v : σ) : pair (P * X v) Q = pair P (pderiv v Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [X, monomial_mul, mul_one, pair_monomial, pair_monomial, coeff_pderiv, wt_add_single]
    ring
  | add P P' h h' => simp only [add_mul, map_add (f := _), LinearMap.add_apply, h, h']

def lin (A : σ → σ → ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun v => ∑ w, A v w • X w

theorem lin_X (A : σ → σ → ℂ) (v : σ) : lin A (X v) = ∑ w, A v w • X w := by
  simp [lin]

theorem pderiv_lin_X (A : σ → σ → ℂ) (v u : σ) : pderiv v (lin A (X u)) = C (A u v) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lin_X, map_sum, Finset.sum_eq_single v]
  · simp [smul_eq_C_mul]
  · intro w _ hw
    simp [pderiv_X, Pi.single_apply, hw]
  · simp

theorem pderiv_lin (A : σ → σ → ℂ) (v : σ) (Q : MvPolynomial σ ℂ) :
    pderiv v (lin A Q) = ∑ w, A w v • lin A (pderiv w Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp [lin]
  | add P P' h h' => simp only [map_add (f := _), h, h', smul_add, Finset.sum_add_distrib]
  | mul_X P u h =>
    rw [map_mul, Derivation.leibniz, h, pderiv_lin_X]
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, smul_add, Finset.sum_add_distrib,
      Finset.mul_sum, mul_smul_comm]
    congr 1
    rw [Finset.sum_eq_single u]
    · simp [smul_eq_C_mul, mul_comm]
    · intro w _ hw
      simp [pderiv_X, Pi.single_apply, hw, Ne.symm hw]
    · simp

theorem coeff_zero_lin (A : σ → σ → ℂ) (Q : MvPolynomial σ ℂ) : AddMonoidAlgebra.coeff (lin A Q) 0 = AddMonoidAlgebra.coeff Q 0 := by
  change constantCoeff (lin A Q) = constantCoeff Q
  induction Q using MvPolynomial.induction_on with
  | C c => simp [lin]
  | add P P' h h' => simp only [map_add (f := _), h, h']
  | mul_X P u h => simp [lin_X, map_sum, smul_eq_C_mul]

theorem pair_lin (A : σ → σ → ℂ) (P Q : MvPolynomial σ ℂ) :
    pair (lin A P) Q = pair P (lin (fun v w => A w v) Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    have : lin A (C c) = C c := by simp [lin]
    rw [this, C_apply, pair_monomial, pair_monomial, coeff_zero_lin]
  | add P P' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']
  | mul_X P u h =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [pair_mul_X, pderiv_lin, map_mul, lin_X, Finset.mul_sum, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mul_smul_comm, map_smul, map_smul, LinearMap.smul_apply, pair_mul_X, h]

theorem pair_nondeg (Q : MvPolynomial σ ℂ) (h : ∀ P, pair P Q = 0) : Q = 0 := by
  ext α
  have := h (monomial α 1)
  rw [pair_monomial_one] at this
  simpa [wt_ne_zero] using this

theorem pair_rep (ℓ : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (d : ℕ)
    (h : ∀ α : σ →₀ ℕ, d < α.degree → ℓ (monomial α 1) = 0) : ∃ Q, ∀ P, pair P Q = ℓ P := by
  classical
  have hfin : {α : σ →₀ ℕ | α.degree ≤ d}.Finite := Finsupp.finite_of_degree_le d
  refine ⟨∑ α ∈ hfin.toFinset, monomial α (ℓ (monomial α 1) / wt α), fun P => ?_⟩
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    have : (monomial α c : MvPolynomial σ ℂ) = c • monomial α 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [pair_monomial, this, map_smul, smul_eq_mul, coeff_sum]
    congr 1
    simp only [coeff_monomial, Finset.sum_ite_eq', Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    split_ifs with hd
    · exact mul_div_cancel₀ _ (wt_ne_zero α)
    · rw [h α (not_le.1 hd), mul_zero]
  | add P P' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h']

open Classical in
theorem subst_eq_lin {ι : Type} [Fintype ι] {m n : ℕ} (a : ι → Matrix (Fin n) (Fin n) ℂ)
    (b : ι → Matrix (Fin m) (Fin m) ℂ) :
    subst a b = lin fun v w => if v.1 = w.1 then b v.1 w.2.1 v.2.1 * a v.1 v.2.2 w.2.2 else 0 := by
  unfold subst lin
  congr 1
  funext v
  rw [Fintype.sum_prod_type, Finset.sum_eq_single v.1, Fintype.sum_prod_type]
  · simp
  · intro τ _ hτ
    simp [Ne.symm hτ]
  · simp

theorem exists_pair (ι : Type) [Fintype ι] (m n : ℕ) :
    ∃ B : Pol ι m n →ₗ[ℂ] Pol ι m n →ₗ[ℂ] ℂ, (∀ Q, (∀ P, B P Q = 0) → Q = 0) ∧
      (∀ a b P Q, B (subst a b P) Q =
        B P (subst (fun τ => (a τ).transpose) (fun τ => (b τ).transpose) Q)) ∧
      ∀ (ℓ : Pol ι m n →ₗ[ℂ] ℂ) (d : ℕ),
        (∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → ℓ (MvPolynomial.monomial α 1) = 0) →
          ∃ Q, ∀ P, B P Q = ℓ P := by
  refine ⟨pair, pair_nondeg, fun a b P Q => ?_, pair_rep⟩
  rw [subst_eq_lin, subst_eq_lin, pair_lin]
  congr 3
  funext v w
  by_cases h : v.1 = w.1
  · simp [h]
  · simp [h, Ne.symm h]

end GlobalTheory.DefLift.BilFischer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBilinearFischerPairingMatrixEntryPolynomiaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bilinearFischerPairing_matrixEntryPolynomialRing : ∀ (ι : Type) [Fintype ι] (m n : ℕ), ∃ B : Pol ι m n →ₗ[ℂ] Pol ι m n →ₗ[ℂ] ℂ, (∀ Q, (∀ P, B P Q = 0) → Q = 0) ∧ (∀ a b P Q, B (subst a b P) Q = B P (subst (fun τ => (a τ).transpose) (fun τ => (b τ).transpose) Q)) ∧ ∀ (ℓ : Pol ι m n →ₗ[ℂ] ℂ) (d : ℕ), (∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → ℓ (MvPolynomial.monomial α 1) = 0) → ∃ Q, ∀ P, B P Q = ℓ P := by
  first | exact @GlobalTheory.DefLift.BilFischer.exists_pair | exact GlobalTheory.DefLift.BilFischer.exists_pair | (intros; apply GlobalTheory.DefLift.BilFischer.exists_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfRangeEq
noncomputable section

open Module NumberField IsDedekindDomain Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef Formalism.BasicNotions
open scoped Matrix InnerProductSpace ComplexOrder

namespace GlobalTheory.Mem.RowSides

section Semi

variable {K : Type} [Field K] {σ : K →+* ℂ} {U V W : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module ℂ W]

theorem semi_injective_of_basis {ι : Type} [Fintype ι] (b : Basis ι K U) (g : U →ₛₗ[σ] W)
    (h : LinearIndependent ℂ fun i => g (b i)) : Function.Injective g := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b.sum_repr x, map_sum] at hx
  simp only [map_smulₛₗ] at hx
  have := Fintype.linearIndependent_iff.1 h (fun i => σ (b.repr x i)) hx
  refine b.repr.injective (Finsupp.ext fun i => σ.injective ?_)
  simpa using this i

end Semi

section Polar

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem majAt_expand {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (x + a • y) ^ 2 = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 + Formalism.HermitianLatticesTheory.normAt b X v (a • y) ^ 2 +
      2 * (v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y).re := by
  have hs : Formalism.HermitianLatticesTheory.fcoord b X v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v y := by
    have : Formalism.HermitianLatticesTheory.vecAt b v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v y := by
      funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
    rw [Formalism.HermitianLatticesTheory.fcoord, this, Matrix.mulVec_smul]; rfl
  simp only [normAt_sq_eq_majAt, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, hs, Finset.mul_sum, Complex.re_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul', Complex.star_def, Complex.mul_re, Complex.add_re,
    Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem majAt_eq_of_normAt [_root_.NumberField.IsTotallyComplex K] {V ι W κ : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (v : InfinitePlace K) (e : V →ₗ[K] W)
    (h : ∀ x, Formalism.HermitianLatticesTheory.normAt b' X' v (e x) ^ 2 = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b' X' v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt b X v x y := by
  have key : ∀ a : K, (v.embedding a * Formalism.HermitianLatticesTheory.majAt b' X' v (e x) (e y)).re =
      (v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y).re := fun a => by
    have h1 := majAt_expand b X v a x y
    have h2 := majAt_expand b' X' v a (e x) (e y)
    rw [← map_smul, ← map_add (f := _), h, h, h] at h2
    linarith
  obtain ⟨a, ha⟩ : ∃ a : K, (v.embedding a).im ≠ 0 := by
    by_contra hn
    push Not at hn
    have hc := IsTotallyComplex.isComplex v
    rw [InfinitePlace.isComplex_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.2 (hn x)
  have h1 := key 1
  have h2 := key a
  simp only [map_one, one_mul] at h1
  simp only [Complex.mul_re, h1] at h2
  refine Complex.ext h1 (mul_left_cancel₀ ha ?_)
  linarith

end Polar

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0) (ℓ : Lvl K G)

variable {B ℓ} {v0 : InfinitePlace K} (hv0 : IsConjAt v0) {s : ℕ} (h : B.Ok s) (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ)




end Block

end GlobalTheory.Mem.RowSides

end
end
