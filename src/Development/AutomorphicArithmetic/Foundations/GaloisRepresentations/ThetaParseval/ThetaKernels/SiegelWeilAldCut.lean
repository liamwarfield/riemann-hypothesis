module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOfLeaves
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfSec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainLe
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ThetaSumRationalInvariant
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.AesmOfContinuous
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FcCont

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldCut
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
def YFrame_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ), n + 1 = d.n → 1 ≤ n →
  ∃ (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ), _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y ∧ IsFrame2 σ Y b ∧
    d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε ∧ b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε
def JEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ),
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∃ j : G2 σ Y →* d.G, _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j
def KStd_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G), IsFrame2 σ Y b → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j → IsStdK (σ := σ) (Y := Y) d.B b (d.K.comap j)
def HgtPull_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j → IsHgt (d.K.comap j) (d.a ∘ j)
def ModelEx_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (j : G2 σ Y →* d.G), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b →
  (∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε ∧ b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε) → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j →
  ∃ (κ : Type) (_ : Fintype κ) (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) κ)
    (om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)) (S : UA σ d.A.J →* Module.End ℂ ((κ → AF F) → ℂ))
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ), IsDbl (σ := σ) (A := d.A) (Y := Y) d.B.ψ dd d.χ om S l ∧ _root_.PositivityTheory.SiegelWeilFormula.Ald.Res_k d h b j dd om l
theorem ldEx_of_leaves_k (h1 : _root_.PositivityTheory.SiegelWeilFormula.Ald.YFrame_k) (h2 : _root_.PositivityTheory.SiegelWeilFormula.Ald.JEx_k) (h3 : _root_.PositivityTheory.SiegelWeilFormula.Ald.KStd_k) (h4 : _root_.PositivityTheory.SiegelWeilFormula.Ald.HgtPull_k) (h5 : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k) : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.LDEx_k := by
  intro hT hA F E _ _ _ _ _ σ d hn
  have h : (d.n - 1) + 1 = d.n := by omega
  have hn1 : 1 ≤ d.n - 1 := by omega
  obtain ⟨Y, b, ε, hs, hb, e1, e2⟩ := h1 F E σ d (d.n - 1) h hn1
  obtain ⟨j, hj⟩ := h2 F E σ d (d.n - 1) h Y b ε e1 e2
  obtain ⟨κ, _, dd, om, S, l, hd, hr⟩ := h5 hT hA F E σ d (d.n - 1) h Y b j hn1 hs hb ⟨ε, e1, e2⟩ hj
  let L0 : _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum d :=
    { n := d.n - 1, Y := Y, κ := κ, dd := dd, om := om, S := S, l := l, b := b, K := d.K.comap j, a := fun x => d.a (j x),
      ok := ⟨d.ok.good, d.ok.hm, hn1, d.ok.aniso, hs, d.ok.hecke, d.ok.res, hd, hb, h3 F E σ d _ h Y b j hb hj,
        h4 F E σ d _ h Y b j hn1 hs hb hj, d.ok.haar, d.ok.dom⟩ }
  exact ⟨{ toLiftedSchrodingerDatum := L0, i₀ := i0 h, em := em0 h, inj := em0_injective h, rng := ne_last_iff_mem_range h, j := j, cont := hj.1,
             j_in := hj.2.1, j_out := hj.2.2, res := hr }⟩
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopMainLe
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Atop
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem LD.n_succ_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : L.n + 1 = d.n := by
  have h1 : Finset.univ.image L.em = Finset.univ.erase L.i₀ := by
    ext i
    rw [Finset.mem_image, Finset.mem_erase]
    simp only [Finset.mem_univ, true_and, and_true]
    exact ((L.rng i).trans Set.mem_range).symm
  have h2 := congrArg Finset.card h1
  rw [Finset.card_image_of_injective _ L.inj, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at h2
  have := L.i₀.pos
  omega
theorem mainInequality_by_corank (hRD : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hLD : _root_.PositivityTheory.SiegelWeilFormula.LDEx_k) (hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hEq : _root_.PositivityTheory.SiegelWeilFormula.MainEq_k) (hStep : _root_.PositivityTheory.SiegelWeilFormula.Step_k)
    (hVA : _root_.PositivityTheory.SiegelWeilFormula.VacAll_k) (k : ℕ) : ∀ d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ, d.m ≤ d.n → d.n - d.m = k → _root_.PositivityTheory.SiegelWeilFormula.MainC_k 2 d := by
  induction k with
  | zero =>
    intro d h hk
    exact hEq F E σ d (by omega)
  | succ k ih =>
    intro d h hk
    have hm := d.ok.hm
    obtain ⟨L⟩ := hLD F E σ d (by omega)
    have hL := _root_.PositivityTheory.SiegelWeilFormula.Atop.LD.n_succ_k L
    obtain ⟨R⟩ := hRD F E σ d
    obtain ⟨R'⟩ := hRD F E σ L.sd
    have hC' : _root_.PositivityTheory.SiegelWeilFormula.MainC_k 2 L.sd := ih L.sd (by show d.m ≤ L.n; omega) (by show L.n - d.m = k; omega)
    have hV' : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R' := fun Φ hΦ hv x => hC' Φ (hPK F E σ L.sd R' Φ hΦ ((hVK F E σ L.sd R').2.1 hv)) x
    exact hVA F E σ d R 2 (hStep F E σ d R L R' (by omega) hV')
end PositivityTheory.SiegelWeilFormula.Atop
namespace PositivityTheory.SiegelWeilFormula
theorem Atop.mainLeOf_k : _root_.PositivityTheory.SiegelWeilFormula.MainLeOf_k := by
  intro hRD hLD hVK hPK hEq hStep hVA F E _ _ _ _ _ σ d h
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.mainInequality_by_corank hRD hLD hVK hPK hEq hStep hVA _ d h rfl
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourLB
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem lamBd_k : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k := by
  intro F E _ _ _ _ _ σ d L hL
  obtain ⟨nb, lam, 𝓖, T, x, ⟨hnb, hlam, hfd, hvol⟩, -, rfl⟩ := hL
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB
  have hb := d.ok.frame
  obtain ⟨iLC, iSC, iT2, iBo⟩ := nA_top hσ hb
  have hcont := nb_continuous hσ hb hnb
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := nF_cocompact hσ hb
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  have hχc : Continuous χ := continuous_chr hψ.1 T.1.1
  have hχn : ∀ β, ‖χ β‖ = 1 := fun β => hψ.2.1 _
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hcm : Continuous fun β : nA σ d.Y d.b => nb β * x := hcont.mul continuous_const
  have hper : ∀ f : d.G → ℂ, (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → ∀ β, ∃ k ∈ K,
      f (nb β * x) = f (nb k * x) := by
    intro f hf β
    obtain ⟨γ, hγ, hk⟩ := hKc β
    refine ⟨γ + β, hk, ?_⟩
    rw [nb_add hnb, mul_assoc, hf _ (nb_rat hnb γ hγ)]
  have hbd : ∀ (f : d.G → ℂ) (M : ℝ), (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ y ∈ (fun β => nb β * x) '' K, ‖f y‖ ≤ M) → ∀ β, ‖f (nb β * x) * χ β‖ ≤ M := by
    intro f M hf hM β
    obtain ⟨k, hk, e⟩ := hper f hf β
    rw [norm_mul, hχn β, mul_one, e]
    exact hM _ ⟨k, hk, rfl⟩
  have hint : ∀ f : d.G → ℂ, Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      IntegrableOn (fun β => f (nb β * x) * χ β) 𝓖 lam := by
    intro f hfc hf
    obtain ⟨M, hM⟩ := (hK.image hcm).exists_bound_of_continuousOn hfc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne ?_ ?_
    · exact ((hfc.comp hcm).mul hχc).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun β => hbd f M hf hM β
  refine ⟨fun a f f' hfc hf'c hf hf' => ?_, ⟨(fun β => nb β * x) '' K, hK.image hcm, fun f M hfc hf hM => ?_⟩⟩
  · simp only [fc]
    have e : (fun β : nA σ d.Y d.b => (a • f + f') (nb β * x) *
        d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))) =
        fun β => a * (f (nb β * x) * χ β) + f' (nb β * x) * χ β := by
      funext β; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hχ]; ring
    rw [e, integral_add ((hint f hfc hf).const_mul a) (hint f' hf'c hf'), integral_const_mul]
  · show ‖∫ β in 𝓖, f (nb β * x) * χ β ∂lam‖ ≤ M
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun β _ => hbd f M hf hM β)
    have hr : lam.real 𝓖 = 1 := by simp [Measure.real, hvol]
    rwa [hr, mul_one] at h1
end PositivityTheory.SiegelWeilFormula.kfour
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoRat
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.ThKF0.Resc in
set_option maxHeartbeats 1000000 in
theorem thetaSum_rational_invariant (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (γ : d.G) (hγ : γ ∈ rat2 σ d.Y) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) :
    thetaSum F (d.om γ Ψ) = thetaSum F Ψ := by
  have hσ : IsCMExt F E σ := d.cm
  have hψ : IsStd d.B.ψ := d.std
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  obtain ⟨-, hS, hR⟩ := d.ok.dbl.weil
  have hYd : d.Y.J.det ≠ 0 := by
    obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
    intro hz
    have hee : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have hM : (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
        Matrix.fromBlocks 0 (((ε : ℤ) : E) • 1) 1 0 = 1 := by
      rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [smul_smul, hee]
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_mul, ← hε, Matrix.det_mul, Matrix.det_mul, dbl, Matrix.det_fromBlocks_zero₂₁, hz] at h1
    simp at h1
  have hκ : Fintype.card d.κ = Fintype.card (Fin d.m) * Fintype.card (Fin d.n ⊕ Fin d.n) := by
    have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    let bE : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
    let bA := Algebra.TensorProduct.basis (AF F) bE
    haveI : Module.Free (AF F) (AE F E) := Module.Free.of_basis bA
    haveI : Module.Finite (AF F) (AE F E) := Module.Finite.of_basis bA
    have e := d.dd.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_eq_card_basis bA, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e ⊢
    omega
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord h2 hκ d.dd.e d.ok.dbl.rat
  obtain ⟨a, b, hab, hA, hB⟩ : ∃ a b : E, -1 = δ * a * b ∧ IsHerm σ (a • d.A.J) ∧ IsHerm σ (b • d.Y.J) := by
    rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, -δ⁻¹, by field_simp, ?_, ?_⟩
      · rw [one_smul]; exact ⟨hA.herm, (herm_det hA).isUnit⟩
      · refine ⟨fun i j => by simp [hY i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hYd
    · refine ⟨-δ⁻¹, 1, by field_simp, ?_, ?_⟩
      · refine ⟨fun i j => by simp [hA.skew i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) (skew_det hA)
      · rw [one_smul]; exact ⟨hY, hYd.isUnit⟩
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hξ : (-1 : AE F E) = inclR (F := F) (AF F) δ * inclR (F := F) (AF F) a * inclR (F := F) (AF F) b := by
    rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]
  have hJA : incM F (a • d.A.J) = inclR (F := F) (AF F) a • incM F d.A.J := by
    ext i j; simp [incM]
  have hJB : incM F (dbl (b • d.Y.J)) = inclR (F := F) (AF F) b • dbl (incM F d.Y.J) := by
    ext (i | i) (j | j) <;> simp [incM, dbl]
  obtain ⟨d', om', he, hS', hR', hgg⟩ := split_resc (c := cA σ) (C := adeleClass F) (ψ := d.B.ψ) (κ := d.κ) hξ
    (hb.isUnit.map (inclR (F := F) (AF F))) hJA hJB hS.toIsSplitting hR
  have hd' : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)) :=
    fun x => by rw [he]; exact hd₀ x
  obtain ⟨g', hg'1, hg'2⟩ := hgg γ
  have hg : ∃ γ₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E,
      ((g' : GL (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F γ₀ := by
    obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
    refine ⟨g₀, ?_⟩
    rw [hg'1, ← hg₀]
    rfl
  rw [← hg'2]
  exact split_core hψ hq (a • d.A.J) (b • d.Y.J) hA hB d' d₀ hd' d.χ d.ok.hecke om' hS' hR' g' hg Ψ hΨ
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingNStr
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem nilpotentMap_add (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
theorem nb_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb) (β β' : nA σ d.Y d.b) :
    nb (β + β') = nb β * nb β' :=
  kfour.nb_add h β β'
theorem nb_rat_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb) {β : nA σ d.Y d.b} (hβ : β ∈ nF σ d.Y d.b) :
    nb β ∈ rat2 σ d.Y :=
  kfour.nb_rat h β hβ
theorem continuous_nb_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb) : Continuous nb :=
  kfour.nb_continuous (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame h
theorem nCocompact_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ K : Set (nA σ d.Y d.b), IsCompact K ∧ ∀ β, ∃ l ∈ nF σ d.Y d.b, β - l ∈ K := by
  obtain ⟨K, hK, hKx⟩ := kfour.nF_cocompact (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame
  refine ⟨K, hK, fun β => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hKx β
  exact ⟨-γ, neg_mem hγ, by rwa [sub_neg_eq_add, add_comm]⟩
theorem aesm_of_continuous_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {u : nA σ d.Y d.b × (Fin d.n → Fin d.n → ℝ) → ℂ} (hu : Continuous u) :
    AEStronglyMeasurable u ((lam.restrict 𝓖).prod volume) :=
  kfour.aesm_of_continuous (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame lam 𝓖 hu
theorem chi_cont_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) :
    Continuous fun β : nA σ d.Y d.b => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) := by
  have htr : Continuous (Algebra.trace (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (Algebra.trace (AF F) (AE F E))
  exact d.ok.good.std.1.comp ((htr.comp (continuous_const.matrix_mul continuous_subtype_val).matrix_trace).neg)
theorem chi_per_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) {l : nA σ d.Y d.b} (hl : l ∈ nF σ d.Y d.b) :
    d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * l.1)))) = 1 := by
  obtain ⟨T₀, hT₀⟩ := (kfour.mem_nF_iff T.1).1 T.2
  obtain ⟨l₀, hl₀⟩ := (kfour.mem_nF_iff l).1 hl
  rw [hT₀, hl₀, ← kfour.incM_mul']
  exact psi_rat d.ok.good.std.2.1 (T₀ * l₀)
theorem chi_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) (β β' : nA σ d.Y d.b) :
    d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * (β + β').1)))) =
      d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) *
        d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β'.1)))) := by
  rw [AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add, AddChar.map_add_eq_mul]
set_option maxHeartbeats 800000 in
theorem fc_shift_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hCD : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (f : d.G → ℂ) (hinv : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g)
    (T : nF σ d.Y d.b) (β₁ : nA σ d.Y d.b) (z : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 f T (nb β₁ * z) = d.B.ψ (d.tt (T.1.1 * β₁.1)) * fc d.B.ψ d.b nb lam 𝓖 f T z := by
  obtain ⟨hN, hH, hD, -⟩ := hCD
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  set u : nA σ d.Y d.b → ℂ := fun β => f (nb β * z) * χ β with hu
  have hca : ∀ a b, χ (a + b) = χ a * χ b := fun a b => _root_.PositivityTheory.SiegelWeilFormula.KSing.chi_add_k d T a b
  have hcp : ∀ l ∈ nF σ d.Y d.b, χ l = 1 := fun l hl => _root_.PositivityTheory.SiegelWeilFormula.KSing.chi_per_k d T hl
  have hper : ∀ (γ : nF σ d.Y d.b) (x : nA σ d.Y d.b), u (γ +ᵥ x) = u x := by
    intro γ x
    show f (nb (γ.1 + x) * z) * χ (γ.1 + x) = f (nb x * z) * χ x
    rw [hca, hcp _ γ.2, one_mul, _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hN, mul_assoc, hinv _ (_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_rat_k d hN γ.2)]
  have hc : d.B.ψ (d.tt (T.1.1 * β₁.1)) * χ β₁ = 1 := by
    simp only [hχ, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt]
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have e1 : ∀ β, f (nb β * (nb β₁ * z)) * χ β = d.B.ψ (d.tt (T.1.1 * β₁.1)) * u (β₁ + β) := by
    intro β
    simp only [hu]
    rw [← mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hN, add_comm β₁ β, hca β β₁]
    linear_combination (-(f (nb (β + β₁) * z) * χ β)) * hc
  have eL : fc d.B.ψ d.b nb lam 𝓖 f T (nb β₁ * z) = d.B.ψ (d.tt (T.1.1 * β₁.1)) * ∫ β in 𝓖, u (β₁ + β) ∂lam := by
    unfold fc
    rw [← integral_const_mul]
    congr 1
    funext β
    exact e1 β
  rw [eL]
  congr 1
  have hmp := measurePreserving_add_left lam β₁
  have hme : MeasurableEmbedding fun β : nA σ d.Y d.b => β₁ + β := measurableEmbedding_addLeft β₁
  have hs : (fun β : nA σ d.Y d.b => β₁ + β) ⁻¹' ((fun β => -β₁ + β) ⁻¹' 𝓖) = 𝓖 := by
    ext β
    simp
  have h2 : IsAddFundamentalDomain (nF σ d.Y d.b) ((fun β => -β₁ + β) ⁻¹' 𝓖) lam := by
    refine hD.preimage_of_equiv (measurePreserving_add_left lam (-β₁)).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => ?_
    show -β₁ + (γ.1 + x) = γ.1 + (-β₁ + x)
    abel
  calc ∫ β in 𝓖, u (β₁ + β) ∂lam
      = ∫ β in (fun β : nA σ d.Y d.b => β₁ + β) ⁻¹' ((fun β => -β₁ + β) ⁻¹' 𝓖), u (β₁ + β) ∂lam := by rw [hs]
    _ = ∫ β in (fun β => -β₁ + β) ⁻¹' 𝓖, u β ∂lam := hmp.setIntegral_preimage_emb hme u _
    _ = ∫ β in 𝓖, u β ∂lam := h2.setIntegral_eq hD hper
end PositivityTheory.SiegelWeilFormula.KSing
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitP
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KSplitP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem siegel_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {p : d.G} {t : GL (Fin d.n) (AE F E)} (hp : IsPar p t) :
    ∃ C : ℂ, ∀ Φ ∈ d.sch, d.l (d.om p Φ) = C * d.l Φ :=
  ⟨_, fun Φ hΦ => d.ok.dbl.weil.2.2 d.l d.ok.dbl.adm (fun z φ hφ => d.ok.dbl.kill z φ hφ) p t hp Φ hΦ⟩
theorem T_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) : d.T Φ 0 = d.l Φ := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.T
  congr 1
  funext x
  simp [Darboux.rho, schr, Matrix.zero_mul]
theorem loc_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : R.loc w 0 = 0 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
  ext i j
  simp
theorem iota_isPar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (q : GR d.n) (hq : (mR q).toBlocks₂₁ = 0) :
    ∃ t, IsPar (R.ι w q) t ∧ (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖(mR q).toBlocks₁₁.det‖ ^ 2 := by
  have hn : 0 < d.n := d.ok.hn
  obtain ⟨t0, ht0⟩ := d.ok.frame.2
  set M := inFrame d.b (R.ι w q) with hM
  have hζ : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have hw : dZ d.n R.ζ * d.cw w M = mR q * dZ d.n R.ζ := R.at_w w q
  set C := d.cw w M with hC
  have e1 : dZ d.n R.ζ * C = Matrix.fromBlocks C.toBlocks₁₁ C.toBlocks₁₂ (R.ζ • C.toBlocks₂₁) (R.ζ • C.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks C]
    simp [dZ, Matrix.fromBlocks_multiply]
  have e2 : mR q * dZ d.n R.ζ = Matrix.fromBlocks (mR q).toBlocks₁₁ (R.ζ • (mR q).toBlocks₁₂) (mR q).toBlocks₂₁
      (R.ζ • (mR q).toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR q)]
    simp [dZ, Matrix.fromBlocks_multiply]
  rw [e1, e2] at hw
  obtain ⟨h11, -, h21, -⟩ := Matrix.fromBlocks_inj.1 hw
  rw [hq] at h21
  have hC21 : C.toBlocks₂₁ = 0 := (smul_eq_zero.1 h21).resolve_left hζ
  have hoff := R.off_f w q
  have hmem : R.ι w q ∈ SiegelEisensteinSeries.Grp.parS σ d.Y d.b (SiegelEisensteinSeries.Grp.siegelS hn) := by
    refine (SiegelEisensteinSeries.Grp.mem_parS_siegelS hn).2 fun i j => ?_
    refine Place.ad_ext d.cm d.B.emb (fun w' => ?_) ?_
    · by_cases hw' : w' = w
      · subst hw'
        have := congrFun (congrFun hC21 i) j
        simpa [Matrix.toBlocks₂₁, hC, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw] using this
      · have := congrFun (congrFun (R.off_w w w' q hw') (Sum.inr i)) (Sum.inl j)
        simpa [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, hM] using this
    · have := congrFun (congrFun hoff (Sum.inr i)) (Sum.inl j)
      simpa [hM] using this
  obtain ⟨t, hPt, hdet⟩ := SiegelEisensteinSeries.Grp.isPar_of_mem_siegelS ht0 hn hmem
  refine ⟨t, hPt, ?_⟩
  set N := M.toBlocks₁₁ with hN
  have hfinN : finOne F • N = finOne F • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    ext i j
    have := congrFun (congrFun hoff (Sum.inl i)) (Sum.inl j)
    simpa [hN, Matrix.toBlocks₁₁, Matrix.one_apply] using this
  set e := algebraMap (AF F) (AE F E) (finOne F) with he
  have hidem : e * e = e := by rw [he, ← map_mul, Krd.fin_idem]
  have hpow' : ∀ k : ℕ, e ^ (k + 1) = e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, hidem]
  have hpow : e ^ d.n = e := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hk]; exact hpow' k
  have hdetN : e * (N.det - 1) = 0 := by
    have h1 : (e • N).det = (e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))).det := by
      rw [he, algebraMap_smul, algebraMap_smul, hfinN]
    rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, hpow, Matrix.det_one, mul_one] at h1
    rw [mul_sub, h1, mul_one, sub_self]
  have hat : ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) - 1 ∈ PositivityTheory.ThKG.CayleyTransformDarboux.atI F E := by
    rw [PositivityTheory.ThKG.CayleyTransformDarboux.mem_atI, hdet]
    intro u hu
    have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    have eu : u = u * finOne F :=
      Prod.ext (by change u.1 = u.1 * 0; rw [hu1, mul_zero]) (by change u.2 = u.2 * 1; rw [mul_one])
    rw [Algebra.smul_def, eu, map_mul, mul_assoc, ← he, hdetN, mul_zero]
  rw [PositivityTheory.ThKG.CayleyTransformDarboux.absE_inf d.cm d.B.emb hat]
  rw [Finset.prod_eq_single w (fun w' _ hne => ?_) (fun h => absurd (Finset.mem_univ w) h)]
  · rw [hdet, RingHom.map_det]
    have : (N.map (piInf (d.B.emb w))) = C.toBlocks₁₁ := by ext i j; rfl
    rw [RingHom.mapMatrix_apply, this, h11]
  · rw [hdet, RingHom.map_det]
    have : (N.map (piInf (d.B.emb w'))) = (d.cw w' M).toBlocks₁₁ := by ext i j; rfl
    rw [RingHom.mapMatrix_apply, this, R.off_w w w' q hne]
    have h1 : (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ).toBlocks₁₁ = 1 := by
      ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
    rw [h1, Matrix.det_one, norm_one, one_pow]
end PositivityTheory.SiegelWeilFormula.KSplitP
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepFc
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fcAll_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (x : d.G) :
    (∀ (a : ℂ) (f f' : d.G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ γ ∈ rat2 σ d.Y, ∀ g, f' (γ * g) = f' g) →
      fc d.B.ψ d.b nb lam 𝓖 (a • f + f') T x = a * fc d.B.ψ d.b nb lam 𝓖 f T x + fc d.B.ψ d.b nb lam 𝓖 f' T x) ∧
    ∃ C : Set d.G, IsCompact C ∧ ∀ (f : d.G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ y ∈ C, ‖f y‖ ≤ M) → ‖fc d.B.ψ d.b nb lam 𝓖 f T x‖ ≤ M := by
  obtain ⟨hnb, hlam, hfd, hvol⟩ := hc
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB
  have hb := d.ok.frame
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ hb
  have hcont := kfour.nb_continuous hσ hb hnb
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ hb
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  have hχc : Continuous χ := kfour.continuous_chr hψ.1 T.1.1
  have hχn : ∀ β, ‖χ β‖ = 1 := fun β => hψ.2.1 _
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hcm : Continuous fun β : nA σ d.Y d.b => nb β * x := hcont.mul continuous_const
  have hper : ∀ f : d.G → ℂ, (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → ∀ β, ∃ k ∈ K,
      f (nb β * x) = f (nb k * x) := by
    intro f hf β
    obtain ⟨γ, hγ, hk⟩ := hKc β
    refine ⟨γ + β, hk, ?_⟩
    rw [kfour.nb_add hnb, mul_assoc, hf _ (kfour.nb_rat hnb γ hγ)]
  have hbd : ∀ (f : d.G → ℂ) (M : ℝ), (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ y ∈ (fun β => nb β * x) '' K, ‖f y‖ ≤ M) → ∀ β, ‖f (nb β * x) * χ β‖ ≤ M := by
    intro f M hf hM β
    obtain ⟨k, hk, e⟩ := hper f hf β
    rw [norm_mul, hχn β, mul_one, e]
    exact hM _ ⟨k, hk, rfl⟩
  have hint : ∀ f : d.G → ℂ, Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      IntegrableOn (fun β => f (nb β * x) * χ β) 𝓖 lam := by
    intro f hfc hf
    obtain ⟨M, hM⟩ := (hK.image hcm).exists_bound_of_continuousOn hfc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne ?_ ?_
    · exact ((hfc.comp hcm).mul hχc).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun β => hbd f M hf hM β
  refine ⟨fun a f f' hfc hf'c hf hf' => ?_, ⟨(fun β => nb β * x) '' K, hK.image hcm, fun f M hfc hf hM => ?_⟩⟩
  · simp only [fc]
    have e : (fun β : nA σ d.Y d.b => (a • f + f') (nb β * x) *
        d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))) =
        fun β => a * (f (nb β * x) * χ β) + f' (nb β * x) * χ β := by
      funext β; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hχ]; ring
    rw [e, integral_add ((hint f hfc hf).const_mul a) (hint f' hf'c hf'), integral_const_mul]
  · show ‖∫ β in 𝓖, f (nb β * x) * χ β ∂lam‖ ≤ M
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun β _ => hbd f M hf hM β)
    have hr : lam.real 𝓖 = 1 := by simp [Measure.real, hvol]
    rwa [hr, mul_one] at h1
theorem fcCont_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (f : d.G → ℂ)
    (hf : Continuous f) (hi : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) : Continuous fun x => fc d.B.ψ d.b nb lam 𝓖 f T x := by
  obtain ⟨hnb, hlam, hfd, hvol⟩ := hc
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB
  have hb := d.ok.frame
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ hb
  obtain ⟨iTG, iLCG, -, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  have hcont := kfour.nb_continuous hσ hb hnb
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ hb
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  have hχc : Continuous χ := kfour.continuous_chr hψ.1 T.1.1
  have hχn : ∀ β, ‖χ β‖ = 1 := fun β => hψ.2.1 _
  have hfin : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  have hmul : Continuous fun q : nA σ d.Y d.b × d.G => nb q.1 * q.2 := (hcont.comp continuous_fst).mul continuous_snd
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨N, hN, hNx⟩ := exists_compact_mem_nhds x₀
  have hKN : IsCompact ((fun q : nA σ d.Y d.b × d.G => nb q.1 * q.2) '' (K ×ˢ N)) := (hK.prod hN).image hmul
  obtain ⟨M, hM⟩ := hKN.exists_bound_of_continuousOn hf.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((hf.comp (hcont.mul continuous_const)).mul hχc).aestronglyMeasurable
  · filter_upwards [hNx] with x hx
    refine Filter.Eventually.of_forall fun β => ?_
    obtain ⟨γ, hγ, hk⟩ := hKc β
    rw [norm_mul, hχn β, mul_one]
    have : f (nb β * x) = f (nb (γ + β) * x) := by
      rw [kfour.nb_add hnb, mul_assoc, hi _ (kfour.nb_rat hnb γ hγ)]
    rw [this]
    exact hM _ ⟨(γ + β, x), ⟨hk, hx⟩, rfl⟩
  · exact Filter.Eventually.of_forall fun β =>
      ((hf.comp (continuous_const.mul continuous_id)).mul continuous_const).continuousAt
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilTbBdd
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil.Tb
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
abbrev bA_k : Module.Basis (Fin 2) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) d.bs
abbrev Ix_k : Type := Fin d.m × Fin d.n × Fin 2
theorem tmul_eq_k (c : AF F) (k : Fin 2) : c ⊗ₜ[F] d.bs k = c • _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d k := by
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem cmb_eq_k (c : _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d → AF F) (i : Fin d.m) (j : Fin d.n) : d.cmb c i j = ∑ k, c (i, j, k) • _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.tmul_eq_k]
theorem cmb_crd_k (Y : Mx F E d.m d.n) : d.cmb (d.crd Y) = Y := by
  funext i j
  rw [_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.cmb_eq_k]
  exact (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).sum_repr (Y i j)
theorem crd_cmb_k (c : _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d → AF F) : d.crd (d.cmb c) = c := by
  funext p
  obtain ⟨i, j, k⟩ := p
  show ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).repr (d.cmb c i j)) k = c (i, j, k)
  rw [_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.cmb_eq_k]
  exact congrFun ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).repr_sum_self fun k => c (i, j, k)) k
def mh_k (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) : Matrix (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (AF F) :=
  fun p q => if p.2.1 = q.2.1 then (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).repr (M p.1 q.1 * _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d q.2.2) p.2.2 else 0
theorem crd_mul_k (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) (Y : Mx F E d.m d.n) :
    d.crd (M * Y) = _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d M *ᵥ d.crd Y := by
  funext p
  obtain ⟨i, j, k⟩ := p
  have hY : ∀ i', Y i' j = ∑ k', d.crd Y (i', j, k') • _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d k' := fun i' => ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).sum_repr (Y i' j)).symm
  show ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).repr ((M * Y) i j)) k = _
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun i' _ => by rw [hY i']]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (fun h => absurd (Finset.mem_univ j) h)]
  simp only [if_true]
  exact Finset.sum_congr rfl fun k' _ => mul_comm _ _
theorem mulVec_ext_k {A B : Matrix (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (AF F)} (h : ∀ c, A *ᵥ c = B *ᵥ c) : A = B := by
  ext p q
  have := congrFun (h (Pi.single q 1)) p
  simpa [Matrix.mulVec_single_one] using this
theorem mh_mul_k (M N : Matrix (Fin d.m) (Fin d.m) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d (M * N) = _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d M * _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d N :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mulVec_ext_k d fun c => by
    conv_lhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_cmb_k d c]
    conv_rhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_cmb_k d c]
    rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k, ← Matrix.mulVec_mulVec, ← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k, Matrix.mul_assoc]
theorem mh_one_k : _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d 1 = 1 :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mulVec_ext_k d fun c => by
    conv_lhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_cmb_k d c]
    rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k, Matrix.one_mul, _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_cmb_k, Matrix.one_mulVec]
theorem continuous_mh_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k]
  split_ifs
  · have hc := (IsModuleTopology.continuous_of_linearMap ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).coord p.2.2)).comp
      ((continuous_id.matrix_elem p.1 q.1).mul (continuous_const (y := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d q.2.2)))
    exact hc
  · exact continuous_const
def mhU_k : GL (Fin d.m) (AE F E) →* GL (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (AF F) :=
  Units.map { toFun := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_k d, map_one' := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_one_k d, map_mul' := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mh_mul_k d }
theorem continuous_mhU_inv_k : Continuous fun h : UA σ d.A.J => _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mhU_k d ((h : GL (Fin d.m) (AE F E))⁻¹) := by
  rw [Units.continuous_iff]
  have h1 : Continuous fun h : UA σ d.A.J => ((h : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have h2 : Continuous fun h : UA σ d.A.J =>
      (((h : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  refine ⟨(_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.continuous_mh_k d).comp h2, ?_⟩
  simp only [← map_inv, inv_inv]
  exact (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.continuous_mh_k d).comp h1
def xi_k : Matrix (Fin d.m) (Fin d.n) E ≃ (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d → F) where
  toFun X p := d.bs.repr (X p.1 p.2.1) p.2.2
  invFun c i j := ∑ k, c (i, j, k) • d.bs k
  left_inv X := by
    funext i j
    exact d.bs.sum_repr (X i j)
  right_inv c := by
    funext p
    obtain ⟨i, j, k⟩ := p
    exact congrFun (d.bs.repr_sum_self fun k => c (i, j, k)) k
theorem crd_incM_k (X : Matrix (Fin d.m) (Fin d.n) E) : d.crd (incM F X) = PositivityTheory.RgEis.ratV (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d X) := by
  funext p
  obtain ⟨i, j, k⟩ := p
  show ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bA_k d).repr ((1 : AF F) ⊗ₜ[F] X i j)) k = algebraMap F (AF F) (d.bs.repr (X i j) k)
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp
theorem bound_cpt_k (Fn : Mx F E d.m d.n → ℂ) (hF : Fn ∈ d.schM) (Ω : Set (UA σ d.A.J)) (hΩ : IsCompact Ω) :
    ∃ u : (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d → F) → ℝ, Summable u ∧ ∀ h ∈ Ω, ∀ X, ‖Fn (mat h⁻¹ * incM F X)‖ ≤ u (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d X) := by
  have hG : (fun c => Fn (d.cmb c)) ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := F) (ι := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) := hF
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hG (hΩ.image (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.continuous_mhU_inv_k d))
  refine ⟨u, hu, fun h hh X => ?_⟩
  have e : Fn (mat h⁻¹ * incM F X) =
      Fn (d.cmb (((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.mhU_k d ((h : GL (Fin d.m) (AE F E))⁻¹) : GL (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (AF F)) : Matrix (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.Ix_k d) (AF F)) *ᵥ
        PositivityTheory.RgEis.ratV (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d X))) := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_incM_k, ← _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.cmb_crd_k d (mat h⁻¹ * incM F X), _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k]
    rfl
  rw [e]
  exact hb _ ⟨h, hh, rfl⟩ _
theorem reindex_k (Fn : Mx F E d.m d.n → ℂ) (γ : UA σ d.A.J) (hγ : γ ∈ ratU σ d.A.J) :
    ∃ e : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E, ∀ h X,
      Fn (mat (γ * h)⁻¹ * incM F (e X)) = Fn (mat h⁻¹ * incM F X) := by
  obtain ⟨G, hG⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hγ)
  have hinc : ∀ A B : Matrix (Fin d.m) (Fin d.m) E, incM F (A * B) = incM F A * incM F B := fun A B => by
    simp only [incM]; exact Matrix.map_mul
  have hinc' : ∀ (A : Matrix (Fin d.m) (Fin d.m) E) (B : Matrix (Fin d.m) (Fin d.n) E), incM F (A * B) = incM F A * incM F B :=
    fun A B => by simp only [incM]; exact Matrix.map_mul
  have l1 : ∀ X : Matrix (Fin d.m) (Fin d.n) E, ((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) * ((G : Matrix (Fin d.m) (Fin d.m) E) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have l2 : ∀ X : Matrix (Fin d.m) (Fin d.n) E, (G : Matrix (Fin d.m) (Fin d.m) E) * (((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  refine ⟨⟨fun X => (G : Matrix (Fin d.m) (Fin d.m) E) * X, fun X => ((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) * X, l1, l2⟩,
    fun h X => ?_⟩
  congr 1
  have hm : mat (γ * h)⁻¹ = mat h⁻¹ * incM F ((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) := by
    have : (((γ : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) =
        incM F ((G⁻¹ : GL (Fin d.m) E) : Matrix (Fin d.m) (Fin d.m) E) := by
      rw [← hG, ← map_inv]; rfl
    simp only [mat, mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
    rw [this]
  simp only [Equiv.coe_fn_mk, hm]
  rw [Matrix.mul_assoc, ← hinc', l1]
theorem cpt_k (hS : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.ThK.Dbl.Cpt σ d.A.J := by
  have hC := _root_.GlobalTheory.ThK.Dbl.cptAll_of_k PositivityTheory.ThKEst.grpTop_of _root_.PositivityTheory.ThKEst.epsOf_of_k (PositivityTheory.ThKEst.siegelAll_of hS)
    PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
  rcases d.ok.sign with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hC F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inl h1) d.ok.aniso
  · exact hC F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inr h1) d.ok.aniso
end PositivityTheory.SiegelWeilFormula.Kdil.Tb
namespace PositivityTheory.SiegelWeilFormula.Kdil
open Tb in
theorem thetaBdd_of_k (hS : GlobalTheory.Published.SiegelSetUnitary) : _root_.PositivityTheory.SiegelWeilFormula.Kdil.ThetaBdd_k := by
  intro F E _ _ _ _ _ σ d Fn hF
  obtain ⟨Ω, hΩ, cov⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.cpt_k d hS).cov
  obtain ⟨u, hu, hb⟩ := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.bound_cpt_k d Fn hF Ω hΩ
  refine ⟨∑' ξ, u ξ, fun h => ?_⟩
  obtain ⟨γ, hγ, hγΩ⟩ := cov h
  obtain ⟨e, he⟩ := _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.reindex_k d Fn γ hγ
  have key : (fun X => ‖Fn (mat h⁻¹ * incM F X)‖) = (fun Y => ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖) ∘ e := by
    funext X
    exact congrArg norm (he h X).symm
  have hs : Summable (fun Y => ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun Y => hb _ hγΩ Y) ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d).summable_iff.2 hu)
  refine ⟨?_, ?_⟩
  · rw [key]; exact e.summable_iff.2 hs
  · rw [key]
    show ∑' X, ‖Fn (mat (γ * h)⁻¹ * incM F (e X))‖ ≤ _
    rw [e.tsum_eq (fun Y => ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖)]
    calc ∑' Y, ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖ ≤ ∑' Y, u (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d Y) :=
          hs.tsum_le_tsum (fun Y => hb _ hγΩ Y) ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d).summable_iff.2 hu)
      _ = ∑' ξ, u ξ := (_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.xi_k d).tsum_eq u
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitPure
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem T_eq_lin_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) (X : Mx F E d.m d.n) :
    d.T Φ X = (d.l ∘ₗ schrL d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ))) Φ := rfl
theorem T_sum_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {k : ℕ} (c : Fin k → ℂ) (Φs : Fin k → d.Fn) :
    d.T (∑ i, c i • Φs i) = ∑ i, c i • d.T (Φs i) := by
  funext X
  set_option synthInstance.maxHeartbeats 100000 in
    rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k]
theorem T_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Ψ : d.Fn) : d.T (Φ - Ψ) = d.T Φ - d.T Ψ := by
  funext X
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k, map_sub, Pi.sub_apply, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k]
def genF_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
    (X : Mx F E d.m d.n) : ℂ :=
  (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2
def genL_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n) :
    ((Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R P
  map_add' f g := by funext X; simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k, Pi.add_apply]; ring
  map_smul' c f := by funext X; simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
def pureGen_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ P φ, Dense.Good φ ∧ f = _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R P (Dense.pf φ)}
theorem pureGen_sub_fock_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_k R ⊆ R.fock := by
  rintro _ ⟨P, φ, hφ, rfl⟩
  exact Submodule.subset_span ⟨P, Dense.pf φ, Dense.pf_mem hφ, rfl⟩
theorem fock_le_span_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_k R) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have := Dense.mem_span_pf hg
  clear hg
  have key : _root_.PositivityTheory.SiegelWeilFormula.KWhit.genL_k R P g ∈ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_k R) := by
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨φ, hφ, rfl⟩ := hx; exact Submodule.subset_span ⟨P, φ, hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  exact key
theorem isPureT_of_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n)
    (φ : ∀ u : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → Fv F u) → ℂ) (hφ : Dense.Good φ) (Φ : d.Fn)
    (h : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R P (Dense.pf φ)) : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureT_k R Φ := by
  refine ⟨P, φ, fun v => hφ.1 v, hφ.2.mono fun v hv => hv, ?_⟩
  rw [h]
  rfl
theorem pureSpan_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k := by
  intro hT hF hPK F E _ _ _ _ _ σ d R Φ hΦ hTΦ
  have hB := hT.1 F E σ d
  have h1 : d.T Φ ∈ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_k R) := _root_.PositivityTheory.SiegelWeilFormula.KWhit.fock_le_span_k R hTΦ
  obtain ⟨k, c, gs, hsum⟩ := Submodule.mem_span_set'.1 h1
  have hpre : ∀ i : Fin k, ∃ Ψ ∈ d.sch, d.T Ψ = (gs i : Mx F E d.m d.n → ℂ) := fun i =>
    hB.2.1 _ ((hF F E σ d R).1 (_root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_sub_fock_k R (gs i).2))
  choose Φs hΦs hTs using hpre
  refine ⟨k, c, Φs, fun i => ⟨hPK F E σ d R (Φs i) (hΦs i) (hTs i ▸ _root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_sub_fock_k R (gs i).2), ?_⟩, ?_⟩
  · obtain ⟨P, φ, hφ, e⟩ := (gs i).2
    exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.isPureT_of_k R P φ hφ (Φs i) ((hTs i).trans e)
  · have hmem : Φ - ∑ i, c i • Φs i ∈ d.sch :=
      sub_mem hΦ.1 (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΦs i))
    have h0 : d.T (Φ - ∑ i, c i • Φs i) = 0 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.T_sub_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_sum_k, ← hsum]
      simp only [hTs, sub_self]
    exact (sub_eq_zero.1 (hB.2.2 _ hmem h0))
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
