module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.ThetaSumAdd
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.FourierZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.TThetaSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GamQFEqOneIffK
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.Imports
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IwaRedOfC

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIsTransportFK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.TransportF
open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E} {ξ : AF F ⊗[F] E}
variable {κ : Type} [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
theorem exists_isTransportF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∃ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT _ _ _ _ ω hω JA JB ξ hA hB' κ _ co hrat
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hω.std.1
  let τ := Fintype.equivFin κ
  have he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (numCoordF co τ w) (numCoordF co τ w') := fun w w' => by
    rw [symplOF_eq_symp hA hB', co.form]
    simp only [symV, numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card κ) → F,
      numCoordF co τ (ratWF x) = (rat y, rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [numCoordF_apply]; erw [h]; rfl⟩
  have hadd : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (Φ + Φ') =
        GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ + GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ' := fun Φ hΦ Φ' hΦ' => by
    simp only [thetaTr_eqF co τ]
    exact congrArg (· ∘ numCoordF co τ) (thV_add hR hψ
      (GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (comp_mem_schA τ hΦ))
      (GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (comp_mem_schA τ hΦ')))
  have hinj : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ' → Φ = Φ' :=
    fun Φ hΦ Φ' hΦ' h => by
    simp only [thetaTr_eqF co τ] at h
    have h2 := thV_injOn hR hψ (comp_mem_schA τ hΦ) (comp_mem_schA τ hΦ')
      ((numCoordF co τ).surjective.injective_comp_right h)
    funext x
    simpa [Function.comp_def] using congrFun h2 (x ∘ τ.symm)
  have hon : ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f ↔
      ∃ Φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ = f := fun f => by
    constructor
    · intro hf
      obtain ⟨Φ, hΦ, h⟩ := _root_.GlobalTheory.T.schrodinger_model_intertwining F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _ (numCoordF co τ) he hr f hf
      refine ⟨_, comp_mem_schA τ.symm hΦ, ?_⟩
      rw [thetaTr_eqF co τ, ← h]
      congr 2
      funext x
      simp [Function.comp_def]
    · rintro ⟨Φ, hΦ, rfl⟩
      rw [thetaTr_eqF co τ]
      exact _root_.GlobalTheory.T.schrodinger_model_isomorphism F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _ (numCoordF co τ) he hr _
        (comp_mem_schA τ hΦ)
  obtain ⟨om, hom⟩ := exists_transport' _ _ _ hadd (thetaTr_smulF co) hinj hon
    (ω.comp (pairHomF hS hξ0 hA hB')) fun p f hf => hω.om_pres _ f hf
  refine ⟨om, ?_⟩
  intro a b g h hh hg Φ hΦ
  have e : (ω.comp (pairHomF hS hξ0 hA hB')) (a, b) = ω (g, h) :=
    congrArg ω (pairHomF_eq hS hξ0 hA hB' a b g h hh hg)
  have h2 := hom (a, b) Φ hΦ
  exact ⟨h2.1, h2.2.trans (LinearMap.congr_fun e _)⟩
end GlobalTheory.TransportF
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKmainLin
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem rho_add_k (w) (Φ Φ' : d.Fn) : d.dd.rho d.B.ψ w (Φ + Φ') = d.dd.rho d.B.ψ w Φ + d.dd.rho d.B.ψ w Φ' := by
  funext y
  simp [Darboux.rho, schr, mul_add]
theorem rho_smul_k (w) (a : ℂ) (Φ : d.Fn) : d.dd.rho d.B.ψ w (a • Φ) = a • d.dd.rho d.B.ψ w Φ := by
  funext y
  simp [Darboux.rho, schr, mul_left_comm]
def Tl_k : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Φ' := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.add_apply, _root_.PositivityTheory.SiegelWeilFormula.KMain.rho_add_k, map_add (f := _)]
  map_smul' a Φ := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.smul_apply, _root_.PositivityTheory.SiegelWeilFormula.KMain.rho_smul_k, map_smul, RingHom.id_apply]
theorem Tl_apply_k (Φ : d.Fn) : _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_k d Φ = d.T Φ := rfl
def secl_k : d.Fn →ₗ[ℂ] (d.G → ℂ) where
  toFun := d.sec0
  map_add' Φ Φ' := by
    funext x
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, Pi.add_apply, map_add (f := _)]
  map_smul' a Φ := by
    funext x
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, Pi.smul_apply, map_smul, RingHom.id_apply]
theorem secl_apply_k (Φ : d.Fn) : _root_.PositivityTheory.SiegelWeilFormula.KMain.secl_k d Φ = d.sec0 Φ := rfl
theorem om_mem_k (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ h
theorem S_mem_k (g) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.S g Φ ∈ d.sch :=
  d.ok.dbl.lin.pres g Φ h
theorem thetaSum_add_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) :
    thetaSum F (Φ + Φ') = thetaSum F Φ + thetaSum F Φ' := by
  have h1 := (hT F E σ d Φ h).1
  have h2 := (hT F E σ d Φ' h').1
  have h3 := (hT F E σ d (Φ + Φ') (d.sch.add_mem h h')).1
  have h4 := h1.add h2
  rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  simp only [map_add (f := _), Pi.add_apply, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  exact h3.unique h4
theorem thetaSum_smul_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (a : ℂ) {Φ : d.Fn} (h : Φ ∈ d.sch) : thetaSum F (a • Φ) = a * thetaSum F Φ := by
  have h1 := (hT F E σ d Φ h).1
  have h3 := (hT F E σ d (a • Φ) (d.sch.smul_mem a h)).1
  have h4 := h1.mul_left a
  rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k] at h3
  exact h3.unique h4
theorem I_add_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) :
    d.I (Φ + Φ') = d.I Φ + d.I Φ' := by
  funext x
  have i1 := ((hA F E σ d).2.2 Φ h).1 x
  have i2 := ((hA F E σ d).2.2 Φ' h').1 x
  have e : ∀ g, thetaSum F (d.om x (d.S g (Φ + Φ'))) = thetaSum F (d.om x (d.S g Φ)) + thetaSum F (d.om x (d.S g Φ')) :=
    fun g => by
      rw [map_add (f := _), map_add (f := _)]
      exact _root_.PositivityTheory.SiegelWeilFormula.KMain.thetaSum_add_k d hT (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KMain.S_mem_k d g h)) (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KMain.S_mem_k d g h'))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.I, thetaMean, Pi.add_apply, e]
  rw [average_eq, average_eq, average_eq, integral_add i1 i2, smul_add]
theorem I_smul_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (a : ℂ) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.I (a • Φ) = a • d.I Φ := by
  funext x
  have e : ∀ g, thetaSum F (d.om x (d.S g (a • Φ))) = a * thetaSum F (d.om x (d.S g Φ)) :=
    fun g => by
      rw [map_smul, map_smul]
      exact _root_.PositivityTheory.SiegelWeilFormula.KMain.thetaSum_smul_k d hT a (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KMain.S_mem_k d g h))
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.I, thetaMean, Pi.smul_apply, e, smul_eq_mul]
  rw [average_eq, average_eq, integral_const_mul, mul_smul_comm]
theorem I_sum_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k) {ι : Type} (s : Finset ι) (f : ι → d.Fn) (h : ∀ i ∈ s, f i ∈ d.sch) :
    d.I (∑ i ∈ s, f i) = ∑ i ∈ s, d.I (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := _root_.PositivityTheory.SiegelWeilFormula.KMain.I_smul_k d hT 0 (d.sch.zero_mem)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      _root_.PositivityTheory.SiegelWeilFormula.KMain.I_add_k d hT hA (h a (Finset.mem_insert_self _ _)) (d.sch.sum_mem fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]
end PositivityTheory.SiegelWeilFormula.KMain
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourFZ
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FirstTermPLZfcCore
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.FTA.ZFC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
variable {Y : Spc F E n}
theorem chr_ker_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b)
    (β : nA σ Y b) : (∀ T : nF σ Y b, chr B.ψ b T β = 1) ↔ β ∈ nF σ Y b := by
  have hσ : ∀ a, σ (σ a) = a := GlobalTheory.LeviLine.sigma_invol hB.cm
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hB.cm.2.2.1]; norm_num)
  obtain ⟨ε, hε⟩ := hb.1
  have hβ : β.1 ∈ PositivityTheory.SiegelWeilFormula.kfour.nCond σ n ε := (PositivityTheory.SiegelWeilFormula.kfour.mem_nA_iff hσ hε β.1).1 β.2
  constructor
  · intro h
    refine (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff β).2 (rat_of_ker hB.cm hB.std ε β.1 ?_ fun T hT => ?_)
    · have e := hβ
      simp only [PositivityTheory.SiegelWeilFormula.kfour.nCond, AddSubgroup.mem_mk, ] at e
      rw [e, Int.cast_smul_eq_zsmul]
    · have hm : incM F T ∈ nA σ Y b := by
        refine (PositivityTheory.SiegelWeilFormula.kfour.mem_nA_iff hσ hε _).2 ?_
        show (incM F T)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F T).map (cA σ))
        rw [Int.cast_smul_eq_zsmul, ← incM_map_cA]
        ext i j
        have := congrFun (congrFun hT i) j
        simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] at this ⊢
        simp only [incM, Matrix.map_apply, this, map_neg, map_zsmul]
      have hT' : (⟨incM F T, hm⟩ : nA σ Y b) ∈ nF σ Y b := (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff _).2 ⟨T, rfl⟩
      exact h ⟨⟨incM F T, hm⟩, hT'⟩
  · intro hβF T
    obtain ⟨T₀, hT₀⟩ := (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff β).1 hβF
    obtain ⟨T₁, hT₁⟩ := (PositivityTheory.SiegelWeilFormula.kfour.mem_nF_iff T.1).1 T.2
    unfold chr
    rw [hT₀, hT₁, ← incM_mul, trace_incM_rat, ← map_neg]
    exact hB.std.2.1 _
theorem fc_inj_pt_per_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (b : GL (Fin n ⊕ Fin n) E) (nb : nA σ Y b → G2 σ Y)
    (lam : Measure (nA σ Y b)) (𝓖 : Set (nA σ Y b)) (hb : IsFrame2 σ Y b) (hc : CoefData (σ := σ) (Y := Y) b nb lam 𝓖)
    (f : G2 σ Y → ℂ) (hf : Continuous f) (hper : ∀ β ∈ nF σ Y b, ∀ g, f (nb β * g) = f g) (x : G2 σ Y)
    (hx : ∀ T : nF σ Y b, fc B.ψ b nb lam 𝓖 f T x = 0) : f x = 0 := by
  obtain ⟨hnb, hlam, hFD, -⟩ := hc
  have hσ : ∀ a, σ (σ a) = a := GlobalTheory.LeviLine.sigma_invol hB.cm
  obtain ⟨i1, i2, i3, i4⟩ := PositivityTheory.SiegelWeilFormula.kfour.nA_top hσ hb
  obtain ⟨K, hK, hcov⟩ := PositivityTheory.SiegelWeilFormula.kfour.nF_cocompact hσ hb
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  have htr : Continuous (Algebra.trace (AF F) (AE F E)) := IsModuleTopology.continuous_of_linearMap _
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (nA σ Y b) (nF σ Y b) K hK hcov
    (nF σ Y b) (chr B.ψ b)
    (fun T => hψ.1.comp (htr.comp ((continuous_const.matrix_mul continuous_subtype_val).matrix_trace)).neg)
    (fun T β β' => by
      unfold chr
      rw [AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul])
    (fun T T' β => by
      unfold chr
      rw [AddSubgroup.coe_add, AddSubgroup.coe_add, Matrix.add_mul, Matrix.trace_add, map_add (f := _), neg_add,
        AddChar.map_add_eq_mul])
    (fun β => by
      unfold chr
      rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, Matrix.zero_mul, Matrix.trace_zero, map_zero, neg_zero,
        AddChar.map_zero_eq_one])
    (fun T β => hψ.2.1 _)
    (_root_.PositivityTheory.FTA.ZFC.chr_ker_k hB hb)
    lam 𝓖 hlam hFD (fun β => f (nb β * x))
    (hf.comp ((PositivityTheory.SiegelWeilFormula.kfour.nb_continuous hσ hb hnb).mul continuous_const))
    (fun γ hγ β => by
      show f (nb (γ + β) * x) = f (nb β * x)
      rw [PositivityTheory.SiegelWeilFormula.kfour.nb_add hnb, mul_assoc]
      exact hper γ hγ _)
    (fun T => (integral_congr_ae (.of_forall fun β => mul_comm _ _)).trans (hx T))
  have h0 := congrFun key 0
  simpa [PositivityTheory.SiegelWeilFormula.kfour.nb_zero hnb] using h0
end PositivityTheory.FTA.ZFC
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem fourierZero_k : _root_.PositivityTheory.SiegelWeilFormula.FourierZero_k := by
  intro F E _ _ _ _ _ σ d nb lam 𝓖 hc f hf hper hfc
  funext g
  exact _root_.PositivityTheory.FTA.ZFC.fc_inj_pt_per_k d.ok.good d.b nb lam 𝓖 d.ok.frame hc f hf hper g fun T => hfc T g
end PositivityTheory.SiegelWeilFormula.kfour
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTparMain
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem frameData_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ t0 : GL (Fin d.n) E,
    incM F d.b.1 = Matrix.fromCols (incM F d.b.1.toCols₁) (incM F d.b.1.toCols₂) ∧
    incM F d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1 ∧
    ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1)ᵀ * dbl (incM F d.Y.J) *
      (incM F d.b.1.toCols₂).map (cA σ) = 1 ∧
    incM F t0.1 * incM F (t0⁻¹).1 = 1 := by
  obtain ⟨t0, ht0'⟩ := d.ok.frame.2
  have ht0 : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * t0.1 := ht0'
  have hBx : incM F d.b.1.toCols₁ =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1 := by
    rw [ht0, incM_mul, incM_diagCols]
  refine ⟨t0, incM_fromCols _, hBx, ?_, ?_⟩
  · rw [← hBx]; exact frame_xy_A d.ok.frame
  · rw [← incM_mul, Units.mul_inv, incM_one]
set_option backward.isDefEq.respectTransparency false in
theorem tPar_k : _root_.PositivityTheory.SiegelWeilFormula.TPar_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, hB, hBx, hf, hT⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  have mem : ∀ w, d.dd.rho d.B.ψ w Φ ∈ schA F d.κ := fun w => GlobalTheory.HeisSchA.schr_mem_schA _ hψ _ Φ hΦ
  refine ⟨fun x β hx X => ?_, fun x t u hx X => ?_, fun g X => ?_⟩
  · have h1 := inFrame_mul hx
    have h2 := inv_mul_frame h1 (N' := Matrix.fromBlocks 1 (-β) 0 1)
      (by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one])
    rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
    replace h1 := Matrix.fromCols_inj h1
    replace h2 := Matrix.fromCols_inj h2
    rw [hBx] at h1 h2
    have hpar : IsPar x 1 := by
      have e := par_of hT (show mat2 x * ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) *
          incM F t0.1) = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1 * 1 by
        rw [h1.1]; simp)
      rw [Matrix.mul_one, hT] at e
      unfold IsPar
      rw [Units.val_one]
      exact e
    have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 x⁻¹)ᵀ = -(X * βᵀ * (incM F t0.1)ᵀ) *
        (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ + X * (incM F d.b.1.toCols₂)ᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, h2.2]
      simp [Matrix.transpose_mul, Matrix.transpose_add, Matrix.mul_add, Matrix.mul_assoc, Matrix.transpose_neg]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
    rw [l_rho_om h x _ hΦ, l_om_par h hpar (mem _), key, l_shift h hψ _ _ hΦ]
    have he := symp_N X β (incM F t0.1) (incM F d.b.1.toCols₂) (incM F d.A.J) (dbl (incM F d.Y.J)) hf
    dsimp only [incM, cA] at he
    dsimp only [incM, cA]
    rw [he]
    simp
  · have h1 := inFrame_mul hx
    have h2 := inv_mul_frame h1 (N' := Matrix.fromBlocks (t⁻¹ : GL (Fin d.n) (AE F E)).1 0 0 (u⁻¹ : GL (Fin d.n) (AE F E)).1)
      (by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one])
    rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
    replace h1 := Matrix.fromCols_inj h1
    replace h2 := Matrix.fromCols_inj h2
    rw [hBx] at h1 h2
    obtain ⟨G0, hG0⟩ : ∃ G0 : GL (Fin d.n) (AE F E), G0 = Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) t0 :=
      ⟨_, rfl⟩
    have g1 : (G0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) = incM F t0.1 := by
      rw [hG0]; rfl
    have g2 : ((G0⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = incM F (t0⁻¹).1 := by
      rw [hG0, ← map_inv]; rfl
    have hpar : IsPar x (G0 * t * G0⁻¹) := by
      have e := par_of hT (show mat2 x * ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) *
          incM F t0.1) = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1 * t.1 by
        rw [h1.1]; simp)
      unfold IsPar
      rw [Units.val_mul, Units.val_mul, g1, g2]
      exact e
    have hdet : Matrix.GeneralLinearGroup.det (G0 * t * G0⁻¹) = Matrix.GeneralLinearGroup.det t := by
      rw [map_mul, map_mul, map_inv]
      exact mul_inv_cancel_comm _ _
    have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 x⁻¹)ᵀ = X * (u⁻¹).1ᵀ * (incM F d.b.1.toCols₂)ᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, h2.2]
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
    rw [l_rho_om h x _ hΦ, l_om_par h hpar (mem _), hdet, key]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
    rw [l_rho_S h hψ g _ hΦ, Matrix.mul_assoc]
def TThetaSum_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch, HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => d.T Φ (incM F X)) (thetaSum F Φ)
set_option backward.isDefEq.respectTransparency false in
theorem tThetaSum_k : _root_.PositivityTheory.SiegelWeilFormula.Tpar.TThetaSum_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, ht0'⟩ := d.ok.frame.2
  have ht0 : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * t0.1 := ht0'
  obtain ⟨Am, hAm⟩ : ∃ Am : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E, Am = Matrix.fromRows 1 (-1) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = (d.b⁻¹).1 * Am := ⟨_, rfl⟩
  have hA : Am = d.b.1.toCols₁ * M.toRows₁ + d.b.1.toCols₂ * M.toRows₂ := by
    rw [← Matrix.fromCols_mul_fromRows, Matrix.fromCols_toCols, Matrix.fromRows_toRows, hM, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]
  have hinj : ∀ v, M.toRows₂ *ᵥ v = 0 → v = 0 := by
    intro v hv
    have e1 : Am *ᵥ v = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) *ᵥ (t0.1 *ᵥ (M.toRows₁ *ᵥ v)) := by
      rw [hA, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero, ht0,
        ← Matrix.mulVec_mulVec]
    funext i
    have a1 := congrFun e1 (Sum.inl i)
    have a2 := congrFun e1 (Sum.inr i)
    simp [hAm, diagCols, Matrix.fromRows_mulVec, Matrix.neg_mulVec] at a1 a2
    have : (2 : E) * v i = 0 := by linear_combination a1 - a2
    simpa using this
  have hu : IsUnit M.toRows₂.det := (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.mulVec_injective_iff_isUnit.1 fun v w e => sub_eq_zero.1 (hinj _ (by rw [Matrix.mulVec_sub, e, sub_self])))
  let e : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E :=
    { toFun := fun y => y * M.toRows₂ᵀ
      invFun := fun X => X * (M.toRows₂)⁻¹ᵀ
      left_inv := fun y => by
        simp only
        rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hu, Matrix.transpose_one, Matrix.mul_one]
      right_inv := fun X => by
        simp only
        rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one, Matrix.mul_one] }
  have hterm : ∀ y : Matrix (Fin d.m) (Fin d.n) E,
      d.l (d.dd.rho d.B.ψ (incM F (Matrix.fromCols y (-y))) Φ) = d.T Φ (incM F (e y)) := by
    intro y
    have hy : Matrix.fromCols y (-y) = y * M.toRows₁ᵀ * t0.1ᵀ * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E)ᵀ + y * M.toRows₂ᵀ * d.b.1.toCols₂ᵀ := by
      have : Matrix.fromCols y (-y) = y * Amᵀ := by simp [hAm, Matrix.transpose_fromRows, Matrix.mul_fromCols]
      rw [this, hA, ht0]
      simp [Matrix.transpose_add, Matrix.transpose_mul, Matrix.mul_add, Matrix.mul_assoc]
    have ea : incM F (y * M.toRows₁ᵀ * t0.1ᵀ * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E)ᵀ) = incM F (y * M.toRows₁ᵀ * t0.1ᵀ) *
        (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ := by
      simp only [incM_mul, incM_transpose, incM_diagCols]
    have ec : incM F (y * M.toRows₂ᵀ * d.b.1.toCols₂ᵀ) = incM F (y * M.toRows₂ᵀ) * (incM F d.b.1.toCols₂)ᵀ := by
      simp only [incM_mul, incM_transpose]
    have hr := psi_rat h hψ (y * M.toRows₁ᵀ * t0.1ᵀ * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E)ᵀ) (y * M.toRows₂ᵀ * d.b.1.toCols₂ᵀ)
    have ea' := ea
    have ec' := ec
    dsimp only [incM] at ea' ec'
    dsimp only [] at hr
    rw [ea', ec'] at hr
    rw [hy, incM_add, ea, ec, l_shift h hψ _ _ hΦ]
    dsimp only [incM, cA]
    rw [hr, one_mul]
    rfl
  have hs := h.theta Φ hΦ
  rw [show (fun y : Matrix (Fin d.m) (Fin d.n) E => d.l (d.dd.rho d.B.ψ (incM F (Matrix.fromCols y (-y))) Φ)) =
      (fun X => d.T Φ (incM F X)) ∘ e from funext hterm] at hs
  exact (Equiv.hasSum_iff e).1 hs
theorem tTheta_of_k
    (h2 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
      ∀ Φ ∈ d.sch, ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ)) : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k :=
  fun F E _ _ _ _ _ σ d Φ hΦ => ⟨_root_.PositivityTheory.SiegelWeilFormula.Tpar.tThetaSum_k F E σ d Φ hΦ, h2 F E σ d Φ hΦ⟩
end PositivityTheory.SiegelWeilFormula.Tpar
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutLat
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutLatA
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
namespace AutLatA
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
theorem sgsg_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
theorem mem_iff_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (y : Matrix (Fin nT) (Fin nS) E) :
    finRatF F y ∈ latF F E nS nT Λ ↔ y ∈ Λ :=
  ⟨fun h => (hR y).2 fun M' hM' => (_root_.PositivityTheory.ThKW.gamQF_eq_one_iff'_k C y M').1 ((hA _).1 h _ (finRatF_mem_of hM')),
    finRatF_mem_of⟩
theorem sdQ_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hR : RatSD σ JS JT ξ₀ Λ) : SelfDual (gamQF σ JS JT ξ₀ B.ψ) Λ := fun x =>
  (hR x).trans (forall₂_congr fun y _ => (_root_.PositivityTheory.ThKW.gamQF_eq_one_iff'_k C x y).symm)
theorem norm_emb_eq_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (φ : E →+* ℂ) (x : E) :
    ∃ v : InfinitePlace F, ‖φ x‖ = ‖tauB B v x‖ := by
  have hcm := hB.cm
  let ρ : F →+* ℂ := φ.comp (algebraMap F E)
  refine ⟨InfinitePlace.mk ρ, ?_⟩
  have hρ : ComplexEmbedding.IsReal ρ := by
    have := hcm.1.isReal (InfinitePlace.mk ρ)
    rwa [InfinitePlace.isReal_mk_iff] at this
  have he : (InfinitePlace.mk ρ).embedding = ρ := by
    rcases InfinitePlace.embedding_mk_eq ρ with h | h
    · exact h
    · rw [h]; exact hρ
  have hτ : (tauB B (InfinitePlace.mk ρ)).comp (algebraMap F E) = ρ := by
    exact (B.emb (InfinitePlace.mk ρ)).2.trans he
  obtain ⟨c, hc⟩ := PI.OmLocU.Red.fix_range σ hcm (y := x * σ x) (by rw [map_mul, _root_.PositivityTheory.ThKW.AutLatA.sgsg_k hB, mul_comm])
  have key : ∀ τ : E →+* ℂ, τ.comp (algebraMap F E) = ρ → Complex.normSq (τ x) = ρ c := fun τ hτ => by
    rw [← hτ, RingHom.comp_apply, hc, map_mul, hcm.2.2.2 τ]
    exact (Complex.mul_conj (τ x)).symm
  have h2 := (key φ rfl).trans (key _ hτ).symm
  rw [Complex.ofReal_inj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
theorem finLat_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hG : GoodLat Λ) (R : ℝ) : {y | y ∈ Λ ∧ ‖infRatF (tauB B) y‖ ≤ R}.Finite := by
  obtain ⟨d, hd, hdi⟩ := exists_denomM hG.fg
  have hS := GlobalTheory.CompletedLatticeFinite.finite_of_denom d hd R
  refine (Set.Finite.pi fun _ : Fin nT => Set.Finite.pi fun _ : Fin nS => hS).subset ?_
  rintro y ⟨hy, hR⟩ i - j -
  refine ⟨hdi y hy i j, fun φ => ?_⟩
  obtain ⟨v, hv⟩ := _root_.PositivityTheory.ThKW.AutLatA.norm_emb_eq_k hB φ (y i j)
  rw [hv]
  exact (norm_le_pi_norm (infRatF (tauB B) y) ((i, j), v)).trans hR
theorem isHeisQ_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (hw : w + sgOF σ w = 1) :
    IsHeis (sgOF σ) w (gamQF σ JS JT ξ₀ B.ψ) fun x => opFF hc w (finRatF F x) := by
  have H := isHeis_opFF (_root_.PositivityTheory.ThKW.AutLatA.sgsg_k C.good) C.hS C.hT C.hξ hc hw
  have e : ∀ x y, gamQF σ JS JT ξ₀ B.ψ x y = gamFF σ JS JT ξ₀ B.ψ (finRatF F x) (finRatF F y) := fun _ _ => rfl
  exact ⟨H.sg_sg, H.w_add, fun x y z => by rw [e, e, e, map_add (f := _), H.add_left],
    fun x y z => by rw [e, e, e, map_add (f := _), H.add_right], fun x => by rw [e, H.alt],
    fun r x y => by rw [e, e, map_smul, map_smul, H.adj], fun v => by rw [map_zero, H.zero],
    fun x y v => by rw [H.comp, e, map_smul, map_add (f := _)]⟩
theorem idx_eq_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) =
      Λ.toAddSubgroup.relIndex (Λ.toAddSubgroup.comap (GlobalTheory.RatAut.sandw b a).toAddMonoidHom) := by
  have hmem := _root_.PositivityTheory.ThKW.AutLatA.mem_iff_k C hR hO.sd
  have hfin := hO.fin (g⁻¹, h⁻¹)
  have hmov : ∀ u ∈ latF F E nS nT Λ,
      idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • u ∈
        (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) := fun u hu => by
    rw [mem_map_rho, map_nsmul]
    exact AddSubgroup.nsmul_relIndex_mem (latF F E nS nT Λ).toAddSubgroup (Submodule.mem_map_of_mem hu)
  rw [GlobalTheory.FinWeil.idx, ← GlobalTheory.RatLattice.relIndex_comap_comap (finRatF F (E := E) (nS := nS) (nT := nT)).toAddMonoidHom]
  · congr 1
    · ext x; exact hmem x
    · ext x
      show finRatF F x ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) ↔ b * x * a ∈ Λ
      rw [mem_map_rho, rhoFF_finRatF ha hb, hmem]
  · intro z hz
    have hN := Nat.pos_of_ne_zero hfin
    obtain ⟨γ, hγ⟩ := lat_approx hG _ (incAF F E ((idx (latF F E nS nT Λ)
      ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) : ℕ) : E)⁻¹ • z).fin
    obtain ⟨u, hu, e⟩ : ∃ u ∈ latF F E nS nT Λ, z = finRatF F (idx (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • γ) +
        idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • u :=
      ⟨_, hγ, by rw [map_nsmul, ← nsmul_add, add_sub_cancel, nsmul_inv_smul' (F := F) (E := E) hN]⟩
    refine ⟨idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • γ, ?_, ?_⟩
    · show finRatF F _ ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))
      rw [eq_sub_of_add_eq e.symm]
      exact sub_mem hz (hmov u hu)
    · show z - finRatF F _ ∈ latF F E nS nT Λ
      rw [sub_eq_of_eq_add' e]
      exact nsmul_mem hu _
open GlobalTheory.RatAut in
theorem data_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x) ∧
    ∃ (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (c N M : ℕ), n ≠ 0 ∧ c ≠ 0 ∧ N ≠ 0 ∧
      (∀ k, b * t k * a - t k ∈ Λ) ∧ (∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) ∧
      ∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k) = lam n ∧ lam n ^ 2 = n ∧
      ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ - 1).det)| ∧
      ((c * idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) : ℕ) : ℚ) =
        |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ).det)| := by
  have sd := _root_.PositivityTheory.ThKW.AutLatA.sdQ_k C hR
  obtain ⟨d, hd0, hdi⟩ := exists_denomM hG.fg
  have fg : Λ.toAddSubgroup.FG := GlobalTheory.RatLattice.fg_of_denom _ d hd0 hdi
  have full := hG.den
  rw [_root_.PositivityTheory.ThKW.AutLatA.idx_eq_k C hG hR hO ha hb]
  rw [← det_sandw] at hΔ ⊢
  rw [← det_sandw_sub_one] at hd ⊢
  have hbij : Function.Bijective ⇑(sandw b a - 1) :=
    (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 hd.isUnit)
  refine ⟨hbij, ?_⟩
  set A := Λ.toAddSubgroup with hA
  obtain ⟨N, hN, hNA⟩ : ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ A, N • sandw b a x ∈ A := by
    obtain ⟨s, hs⟩ := fg
    choose k hk hk' using full
    refine ⟨∏ y ∈ s, k (sandw b a y), Finset.prod_ne_zero_iff.2 fun y _ => (hk _).ne', fun x hx => ?_⟩
    suffices h : ∀ z : A, (∏ y ∈ s, k (sandw b a y)) • sandw b a z.1 ∈ A by
      exact h ⟨x, hx⟩
    intro z
    have hz : z ∈ AddSubsemigroup.closure (s : Set A) := by rw [hs]; trivial
    induction hz using AddSubsemigroup.closure_induction with
    | mem z hz =>
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun y : A => k (sandw b a y)) (show z ∈ s from hz)
      rw [hm, mul_comm, mul_smul]
      exact nsmul_mem (hk' _) m
    | add x y _ _ hx hy =>
      change (∏ y ∈ s, k (sandw b a y)) • sandw b a (x.1 + y.1) ∈ A
      rw [map_add, smul_add]
      exact add_mem hx hy
  have i1 := GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det _ _ A fg full (sandw b a - 1) N hN hd fun x hx => by
    rw [LinearMap.sub_apply, smul_sub]
    exact sub_mem (hNA x hx) (nsmul_mem hx N)
  have i2 := GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det _ _ A fg full (sandw b a) N hN hΔ hNA
  set B₁ := A.comap (sandw b a - 1).toAddMonoidHom with hB₁
  set B₂ := A.comap (sandw b a).toAddMonoidHom with hB₂
  set NA := A.map (N • AddMonoidHom.id _) with hNA'
  have e12 : A ⊓ B₁ = A ⊓ B₂ := by
    ext x
    refine and_congr_right fun hx => ?_
    show sandw b a x - x ∈ A ↔ sandw b a x ∈ A
    exact ⟨fun h => by simpa using add_mem h hx, fun h => sub_mem h hx⟩
  have hle : NA ≤ A ⊓ B₂ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨nsmul_mem hx N, ?_⟩
    show sandw b a (N • x) ∈ A
    rw [map_nsmul]
    exact hNA x hx
  have m1 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₁) B₁ (e12 ▸ hle) inf_le_right
  have m2 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₂) B₂ hle inf_le_right
  rw [AddSubgroup.inf_relIndex_right] at m1 m2
  rw [e12] at m1
  have h0 : NA.relIndex (A ⊓ B₂) * A.relIndex B₁ ≠ 0 := by
    rw [m1, ← Nat.cast_ne_zero (R := ℚ), i1, abs_ne_zero, Algebra.norm_ne_zero_iff]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hN)) hd
  obtain ⟨t, t1, t2⟩ := exists_transversal A B₁ (right_ne_zero_of_mul h0)
  obtain ⟨g1, g2⟩ := gauss_isometry (_root_.PositivityTheory.ThKW.AutLatA.isHeisQ_k C hc hO.hw) hO.good sd ((sandw b a).restrictScalars (𝓞 E))
    (fun x y => by
      show gamFF σ JS JT ξ₀ B.ψ (finRatF F (b * x * a)) (finRatF F (b * y * a)) =
        gamFF σ JS JT ξ₀ B.ψ (finRatF F x) (finRatF F y)
      rw [← rhoFF_finRatF ha hb, ← rhoFF_finRatF ha hb]
      unfold gamFF
      rw [coe_rhoFF, coe_rhoFF, _root_.PositivityTheory.ThKW.symplOF_actOF_k C]) hbij.2 _ t t1 t2
  exact ⟨_, t, _, N, _, right_ne_zero_of_mul h0, left_ne_zero_of_mul h0, hN, t1, t2, g1, g2, m1 ▸ i1, m2 ▸ i2⟩
end AutLatA
end PositivityTheory.ThKW
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
theorem finRatF_mem_iff_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (y : Matrix (Fin nT) (Fin nS) E) :
    finRatF F y ∈ latF F E nS nT Λ ↔ y ∈ Λ := _root_.PositivityTheory.ThKW.AutLatA.mem_iff_k C hR hA y
theorem finite_lat_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hG : GoodLat Λ) (R : ℝ) : {y | y ∈ Λ ∧ ‖infRatF (tauB B) y‖ ≤ R}.Finite :=
  _root_.PositivityTheory.ThKW.AutLatA.finLat_k hB hG R
theorem finite_data_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x) ∧
    ∃ (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (c N M : ℕ), n ≠ 0 ∧ c ≠ 0 ∧ N ≠ 0 ∧
      (∀ k, b * t k * a - t k ∈ Λ) ∧ (∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) ∧
      ∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k) = lam n ∧ lam n ^ 2 = n ∧
      ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ - 1).det)| ∧
      ((c * idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) : ℕ) : ℚ) =
        |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ).det)| :=
  _root_.PositivityTheory.ThKW.AutLatA.data_k C hG hR hO ha hb hΔ hd
end PositivityTheory.ThKW
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTweylBase
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem std_k : IsStd d.B.ψ := d.ok.good.std
include d in
theorem cm_k : IsCMExt F E σ := d.ok.good.1
theorem hS_k : IsUSplitting (adeleClass F) d.B.ψ d.dd (fun (g : UA σ d.A.J) x => mat g * x) d.S := d.ok.dbl.lin
theorem hO_k : IsUSplitting (adeleClass F) d.B.ψ d.dd (actB (cA σ)) d.om := d.ok.dbl.weil.2.1
theorem hR_k : SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) d.dd d.χ
    (diagCols (Fin d.n)) d.om := d.ok.dbl.weil.2.2
theorem mat_mul_inv_k (g : UA σ d.A.J) : mat g * mat g⁻¹ = 1 := by
  show g.1.1 * (g⁻¹).1.1 = 1
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
end PositivityTheory.SiegelWeilFormula.tweyl
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitLin
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section SDl
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def linRhoL_k (v : Mx F E d.m d.n) : d.Fn →ₗ[ℂ] d.Fn where
  toFun := d.dd.rho d.B.ψ (v * (incM F d.b.1.toCols₂)ᵀ)
  map_add' Φ Ψ := by
    funext y
    simp only [Darboux.rho, schr, Pi.add_apply]
    ring
  map_smul' a Φ := by
    funext y
    simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem lin_T_sum_k {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (X : Mx F E d.m d.n) :
    d.T (∑ i ∈ s, c i • Φs i) X = ∑ i ∈ s, c i * d.T (Φs i) X := by
  set_option synthInstance.maxHeartbeats 100000 in
    change d.l (linRhoL_k d X (∑ i ∈ s, c i • Φs i)) = ∑ i ∈ s, c i * d.l (linRhoL_k d X (Φs i))
    simp only [map_sum, map_smul, smul_eq_mul]
theorem constantTerm_finsetSum {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (x : d.G) :
    d.sec0 (∑ i ∈ s, c i • Φs i) x = ∑ i ∈ s, c i * d.sec0 (Φs i) x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, map_sum, map_smul, smul_eq_mul]
theorem lin_om_mem_k (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ h
theorem lin_S_mem_k (g : UA σ d.A.J) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.S g Φ ∈ d.sch := d.ok.dbl.lin.pres g Φ h
theorem lin_sum_mem_k {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (h : ∀ i ∈ s, Φs i ∈ d.sch) :
    ∑ i ∈ s, c i • Φs i ∈ d.sch :=
  Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (h i hi)
theorem lin_thetaSum_sum_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (h : ∀ i ∈ s, Φs i ∈ d.sch) :
    thetaSum F (∑ i ∈ s, c i • Φs i) = ∑ i ∈ s, c i * thetaSum F (Φs i) := by
  have h1 := (hT F E σ d _ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_sum_mem_k d s c Φs h)).1
  have h2 : HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => ∑ i ∈ s, c i * d.T (Φs i) (incM F X))
      (∑ i ∈ s, c i * thetaSum F (Φs i)) :=
    hasSum_sum fun i hi => ((hT F E σ d _ (h i hi)).1).mul_left (c i)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_T_sum_k] at h1
  exact h1.unique h2
theorem lin_I_sum_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k) {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn)
    (h : ∀ i ∈ s, Φs i ∈ d.sch) (x : d.G) : d.I (∑ i ∈ s, c i • Φs i) x = ∑ i ∈ s, c i * d.I (Φs i) x := by
  have e : ∀ g : UA σ d.A.J, thetaSum F (d.om x (d.S g (∑ i ∈ s, c i • Φs i))) =
      ∑ i ∈ s, c i * thetaSum F (d.om x (d.S g (Φs i))) := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    simp only [map_smul]
    exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_thetaSum_sum_k d hT s c (fun i => d.om x (d.S g (Φs i))) fun i hi => _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_S_mem_k d g (h i hi))
  have hint : ∀ i ∈ s, IntegrableOn (fun g => thetaSum F (d.om x (d.S g (Φs i)))) d.D d.μ :=
    fun i hi => ((hA F E σ d).2.2 _ (h i hi)).1 x
  show ⨍ g in d.D, thetaSum F (d.om x (d.S g (∑ i ∈ s, c i • Φs i))) ∂d.μ =
    ∑ i ∈ s, c i * ⨍ g in d.D, thetaSum F (d.om x (d.S g (Φs i))) ∂d.μ
  simp only [e, setAverage_eq]
  rw [integral_finsetSum s fun i hi => (hint i hi).const_mul (c i), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, mul_smul_comm]
end SDl
theorem lin_psi_meas_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (M : Mx F E d.n d.n) :
    Measurable (fun β : nA σ d.Y d.b => d.B.ψ (-d.tt (M * β.1))) := by
  have key : ∀ β : nA σ d.Y d.b, d.B.ψ (-d.tt (M * β.1)) =
      ∏ i, ∏ k, d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * β.1 k i))) := by
    intro β
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, ← Finset.sum_neg_distrib, lin_addChar_sum]
  rw [show (fun β : nA σ d.Y d.b => d.B.ψ (-d.tt (M * β.1))) = fun β =>
      ∏ i, ∏ k, d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * β.1 k i))) from funext key]
  have : OpensMeasurableSpace (AE F E) := ⟨le_rfl⟩
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun k _ => ?_
  have hc : Continuous fun y : AE F E => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * y))) :=
    d.ok.good.std.1.comp (IsModuleTopology.continuous_of_linearMap
      ((Algebra.trace (AF F) (AE F E)).comp (LinearMap.mulLeft (AF F) (M i k)))).neg
  exact hc.measurable.comp ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_subtype_coe))
theorem lin_fc_sum_k (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb lam 𝓖} (hcd : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖)
    (T : nF σ d.Y d.b) (hND : IsND T) (x : d.G) {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → d.G → ℂ)
    (hc : ∀ i, Continuous (f i)) (hi : ∀ i, ∀ γ ∈ rat2 σ d.Y, ∀ g, f i (γ * g) = f i g) :
    fc d.B.ψ d.b nb lam 𝓖 (∑ i ∈ s, c i • f i) T x = ∑ i ∈ s, c i * fc d.B.ψ d.b nb lam 𝓖 (f i) T x := by
  classical
  obtain ⟨hlin, -⟩ := hLB F E σ d (fun f => fc d.B.ψ d.b nb lam 𝓖 f T x) ⟨nb, lam, 𝓖, T, x, hcd, hND, rfl⟩
  have hfun : ∀ s : Finset ι, (∑ i ∈ s, c i • f i) = fun a => ∑ i ∈ s, c i * f i a := by
    intro s; funext a; simp [Finset.sum_apply]
  have hcs : ∀ s : Finset ι, Continuous (∑ i ∈ s, c i • f i) := by
    intro s; rw [hfun s]; exact continuous_finsetSum s fun i _ => continuous_const.mul (hc i)
  have his : ∀ s : Finset ι, ∀ γ ∈ rat2 σ d.Y, ∀ g, (∑ i ∈ s, c i • f i) (γ * g) = (∑ i ∈ s, c i • f i) g := by
    intro s γ hγ g; rw [hfun s]; exact Finset.sum_congr rfl fun i _ => by rw [hi i γ hγ g]
  induction s using Finset.induction_on with
  | empty =>
    have h0 := hlin 1 0 0 continuous_const continuous_const (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    simp only [one_smul, add_zero, one_mul] at h0
    simpa using h0
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, hlin (c j) (f j) _ (hc j) (hcs s) (hi j) (his s), ih]
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
