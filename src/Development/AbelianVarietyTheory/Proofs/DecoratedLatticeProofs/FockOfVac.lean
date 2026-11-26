module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOperatorActsByNoncompactQuadraticOps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroAtZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOfVac
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOfVac
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockVecOfVac

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis

theorem coeff_sum_pderiv_eq_zero {ι : Type} [Fintype ι] (c : ι → ℂ) (Q : MvPolynomial ι ℂ) (n : ℕ)
    (hQ : ∀ m : ι →₀ ℕ, n < m.degree → Q.coeff m = 0) (m : ι →₀ ℕ) (hm : n < m.degree + 1) :
    (∑ i, c i • MvPolynomial.pderiv i Q).coeff m = 0 := by
  classical
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_pderiv,
    hQ _ (by rw [map_add (f := _), Finsupp.degree_single]; omega), zero_mul, smul_zero]

theorem fock_of_vac : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsVacVec ψ θ M M' f → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec ψ θ V W (cart M) (cart M') (ptOf ψ θ M M' f P) := by
  intro D V W S S' M M' θ ψ hψ hθ f hf P
  have hS : ∀ τ, IsCartanInv (gramAt D V τ) (cart M τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model M
  have hT : ∀ τ, IsCartanInv (gramAt D W τ) (cart M' τ) := GlobalTheory.FrameEquiv.isCartanInv_cart_model M'
  set A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M') with hAdef
  have hadd : ∀ g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → IsThetaFunO ψ V W (g + g') := by
    intro g g' hg hg'
    refine { quasi := ?_, level := ?_, cont := hg.cont.add hg'.cont, smooth := ?_ }
    · intro γ w
      simp only [Pi.add_apply, hg.quasi, hg'.quasi, mul_add]
    · obtain ⟨U, hU, hUg⟩ := hg.level
      obtain ⟨U', hU', hUg'⟩ := hg'.level
      refine ⟨U ⊓ U', by rw [AddSubgroup.coe_inf]; exact hU.inter hU', fun u hu hinf => ?_⟩
      have he : heisO ψ V W u (g + g') = heisO ψ V W u g + heisO ψ V W u g' := by
        funext w
        simp only [heisO, Pi.add_apply, mul_add]
      rw [he, hUg u hu.1 hinf, hUg' u hu.2 hinf]
    · intro k L hL hfin w
      simpa [Pi.add_apply] using (hg.smooth k L hL hfin w).add (hg'.smooth k L hL hfin w)
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (a • g) := by
    intro a g hg
    refine { quasi := ?_, level := ?_, cont := hg.cont.const_smul a, smooth := ?_ }
    · intro γ w
      simp only [Pi.smul_apply, smul_eq_mul, hg.quasi]
      ring
    · obtain ⟨U, hU, hUg⟩ := hg.level
      refine ⟨U, hU, fun u hu hinf => ?_⟩
      have he : heisO ψ V W u (a • g) = a • heisO ψ V W u g := by
        funext w
        simp only [heisO, Pi.smul_apply, smul_eq_mul]
        ring
      rw [he, hUg u hu hinf]
    · intro k L hL hfin w
      simpa [Pi.smul_apply] using (hg.smooth k L hL hfin w).const_smul a
  have hA : ∀ k g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (A k g) := fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  have hc : ∀ i j g, IsThetaFunO ψ V W g → A i (A j g) = A j (A i g) :=
    fun i j _ h => aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
  have Aadd : ∀ i g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → A i (g + g') = A i g + A i g' :=
    fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h'
  have Asm : ∀ i (a : ℂ) g, IsThetaFunO ψ V W g → A i (a • g) = a • A i g :=
    fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h
  have hpt : ∀ Q, ptOf ψ θ M M' f Q = pureTensorL A f Q := fun _ => rfl
  have hm : ∀ Q, IsThetaFunO ψ V W (pureTensorL A f Q) := pure_mem hadd hsm hA hf.theta

  have hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ), ∃ c : FVar D W.rank V.rank → ℂ, ∀ Q,
      annih (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) z (pureTensorL A f Q) =
        pureTensorL A f (∑ i, c i • MvPolynomial.pderiv i Q) := by
    intro τ z
    refine ⟨fun k => (fockScale D k.1 : ℂ)⁻¹ * (-(4 * Real.pi * Complex.I) *
      ((omDir V W τ z k.1 (unitMap (onb M k.1) (onb M' k.1) k.2.1 k.2.2) : ℝ) +
        Complex.I * (omDir V W τ (cplxO (cart M τ) (cart M' τ) z) k.1
          (unitMap (onb M k.1) (onb M' k.1) k.2.1 k.2.2) : ℝ))), fun Q => ?_⟩
    exact GlobalTheory.ArchRec.DerFock.pure_deriv hadd hsm hA hc Aadd Asm
      (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h)
      (fun j _ h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ z hS hT j.1 _ h) hf.theta (hf.vac τ z) Q
  refine ⟨by rw [hpt]; exact hm P, P.totalDegree + 1, fun l hl => ?_⟩

  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ), ∃ Q : MvPolynomial (FVar D W.rank V.rank) ℂ,
      l.foldr (fun p g => annih (heisO ψ V W) θ p.1 (cplxO (cart M p.1) (cart M' p.1)) p.2 g) (pureTensorL A f P) =
        pureTensorL A f Q ∧ ∀ m : FVar D W.rank V.rank →₀ ℕ, P.totalDegree < m.degree + l.length → Q.coeff m = 0 := by
    intro l
    induction l with
    | nil =>
      refine ⟨P, rfl, fun m hm' => MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_⟩
      have h' : P.totalDegree < m.degree := by simpa using hm'
      exact h'
    | cons p l ih =>
      obtain ⟨Q, hQ, hQc⟩ := ih
      obtain ⟨c, hc'⟩ := hder p.1 p.2
      refine ⟨∑ i, c i • MvPolynomial.pderiv i Q, ?_, fun m hm' => ?_⟩
      · rw [List.foldr_cons, hQ, hc']
      · refine coeff_sum_pderiv_eq_zero c Q (P.totalDegree - l.length) (fun m' hm'' => hQc m' (by omega)) m ?_
        simp only [List.length_cons] at hm'
        omega
  obtain ⟨Q, hQ, hQc⟩ := key l
  have hQ0 : Q = 0 := MvPolynomial.ext _ _ fun m => by
    simpa using hQc m (by rw [hl]; omega)
  rw [hpt, hQ, hQ0, map_zero]

end GlobalTheory.FockVecOfVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOfVacStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFockVec_ptOf_of_isVacVec : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsVacVec ψ θ M M' f → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec ψ θ V W (cart M) (cart M') (ptOf ψ θ M M' f P) := by
  first | exact @GlobalTheory.FockVecOfVac.fock_of_vac | exact GlobalTheory.FockVecOfVac.fock_of_vac | (intros; apply GlobalTheory.FockVecOfVac.fock_of_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLine
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLine
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ConjLine

open GlobalTheory.Mem.Isom

variable {D : D7}

theorem entries_fix {A : Type} [CommRing A] {m n : ℕ} (c : A) {M : Matrix (Fin n) (Fin n) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (Q : Matrix (Fin n) (Fin m) A) (i j : Fin m) : c * (P * M * Q) i j = (P * M * Q) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l k]
  ring

theorem entries_fix' {A : Type} [CommRing A] {m n k : ℕ} (c : A) {M : Matrix (Fin n) (Fin k) A} (hM : ∀ i j, c * M i j = M i j)
    (P : Matrix (Fin m) (Fin n) A) (i : Fin m) (j : Fin k) : c * (P * M) i j = (P * M) i j := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_rhs => rw [← hM l j]
  ring

theorem sub_one_conj {A : Type} [CommRing A] {m n : ℕ} {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A} (PQ : P * Q = 1)
    (M : Matrix (Fin n) (Fin n) A) : P * M * Q - 1 = P * (M - 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, PQ]

theorem det_conj_rect {A : Type} [CommRing A] {m n : ℕ} (h : n = m) {P : Matrix (Fin m) (Fin n) A} {Q : Matrix (Fin n) (Fin m) A}
    (QP : Q * P = 1) (M : Matrix (Fin n) (Fin n) A) : (P * M * Q).det = M.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P.det), mul_assoc, ← Matrix.det_mul, mul_eq_one_comm.1 QP, Matrix.det_one, mul_one]

variable {V V' : HSp D} (I : IsoMat V V')

theorem isThetaFunO_tr (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {f : WO S V → ℂ} (hf : IsThetaFunO ψ S V f) :
    IsThetaFunO ψ S V' (I.trW S f) := by
  have hinf : ∀ w : WO S V', w.map (infPart D) = 0 → ((I.phi S).symm w).map (infPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (infPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  have hfin : ∀ w : WO S V', w.map (finPart D) = 0 → ((I.phi S).symm w).map (finPart D) = 0 := fun w h => by
    show (HMul.hMul I.aQ w).map (finPart D) = 0
    rw [Matrix.map_mul, h, Matrix.mul_zero]
  refine ⟨fun γ w => ?_, ?_, hf.cont.comp (I.continuous_phi_symm S), fun k L hL h0 w => ?_⟩
  · obtain ⟨w, rfl⟩ := (I.phi S).surjective w
    have e : ratW V' S γ = I.phi S (ratW V S (I.Q * γ)) := by
      rw [IsoMat.phi_ratW, ← Matrix.mul_assoc, I.PQ, Matrix.one_mul]
    rw [e, ← map_add (f := _), I.symplOH_phi]
    simp only [IsoMat.trW, AddEquiv.symm_apply_apply]
    exact hf.quasi _ _
  · obtain ⟨U, hU, e⟩ := hf.level
    refine ⟨U.map (I.phi S).toAddMonoidHom, ?_, ?_⟩
    · have e : ((U.map (I.phi S).toAddMonoidHom : AddSubgroup (WO S V')) : Set (WO S V')) = (I.phi S).symm ⁻¹' U := by
        ext w
        simp only [AddSubgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · rintro ⟨u, hu, rfl⟩
          simpa using hu
        · intro hw
          exact ⟨_, hw, by simp⟩
      rw [e]
      exact hU.preimage (I.continuous_phi_symm S)
    · rintro _ ⟨u, hu, rfl⟩ h0
      have h1 : u.map (infPart D) = 0 := by
        have := hinf _ h0
        simpa using this
      show heisO ψ S V' (I.phi S u) (I.trW S f) = I.trW S f
      rw [I.heisO_trW, e u hu h1]
  · have := hf.smooth k ((I.phi S).symm.toAddMonoidHom.comp L) ((I.continuous_phi_symm S).comp hL) (fun t => hfin _ (h0 t))
      ((I.phi S).symm w)
    simpa [IsoMat.trW] using this

theorem isWeilDatumO_tr (S : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {χ χ' : (AE D)ˣ →* Circle}
    {om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)}
    (h : IsWeilDatumO ψ S V χ χ' om) : IsWeilDatumO ψ S V' χ χ' (I.omT S om) := by
  have hT : ∀ f, IsThetaFunO ψ S V' f → IsThetaFunO ψ S V (I.symm.trW S f) := fun f hf => isThetaFunO_tr I.symm S hf
  refine ⟨h.std, h.hecS, h.hecT, h.resS, I.rank_eq ▸ h.resT, fun p f hf => ?_, fun g k w₀ f hf => ?_, fun γ hγ γ' hγ' f hf => ?_,
    fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩
  · exact isThetaFunO_tr I S (h.om_pres _ _ (hT f hf))
  · rw [IsoMat.omT_apply, IsoMat.omT_apply, ← I.symm.heisO_trW S ψ w₀ f, h.om_heis _ _ _ _ (hT f hf), ← I.heisO_trW, I.actO_phi]
    congr 2
    · exact I.kap.apply_symm_apply k
    · exact (I.phi S).apply_symm_apply w₀
  · rw [IsoMat.omT_apply]
    show om (γ, I.kap.symm γ') (I.symm.trW S f) ((I.phi S).symm 0) = f 0
    have := h.om_aut γ hγ (I.kap.symm γ') (I.symm.kap_mem_GQ hγ') _ (hT f hf)
    rw [map_zero, this]
    show f ((I.phi S) 0) = f 0
    rw [map_zero]
  · exact (h.om_cont _ (hT f hf) ((I.phi S).symm w)).comp
      (continuous_fst.prodMk ((I.continuous_kap_symm).comp continuous_snd))
  · obtain ⟨ν, 𝓖, hν, h𝓖, hu⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_isometryTransport D V V' I S μ 𝓕 hμ h𝓕
    have e1 := hu fun x => ‖om (p.1, I.kap.symm p.2) (I.symm.trW S f) x‖ₑ ^ 2
    have e2 := hu fun x => ‖I.symm.trW S f x‖ₑ ^ 2
    have e3 : ∀ w, I.symm.trW S f ((I.phi S).symm w) = f w := fun w => congrArg f ((I.phi S).apply_symm_apply w)
    simp only [e3] at e2
    rw [IsoMat.omT_apply]
    exact e1.trans ((h.om_unit ν 𝓖 hν h𝓖 _ _ (hT f hf)).trans e2.symm)
  · have e0 : mt V (I.kap.symm k) - 1 = _ := sub_one_conj I.aQ_aP (mt V' k)
    have hsupp : SuppAt e V (I.kap.symm k) := fun i j => by
      unfold SuppAt at hk
      rw [e0]
      exact entries_fix _ hk _ _ i j
    have e1 : (mt V (I.kap.symm k)).det = (mt V' k).det := det_conj_rect I.rank_eq.symm I.aP_aQ (mt V' k)
    have hdet : IsDetAt e V (I.kap.symm k) y := by
      unfold IsDetAt at hy ⊢
      rw [e1]
      exact hy
    obtain ⟨r, hr, H⟩ := h.om_split e he g (I.kap.symm k) hg hsupp x y hx hdet
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    have hinv : ∀ u : WO S V, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S V f →
        (ℓ ∘ₗ I.trL S) (heisO ψ S V u f) = (ℓ ∘ₗ I.trL S) f := by
      intro u hu f hf
      show ℓ (I.trW S (heisO ψ S V u f)) = ℓ (I.trW S f)
      rw [← I.heisO_trW]
      exact hℓ _ (fun i j => entries_fix' _ hu I.aP i j) _ (isThetaFunO_tr I S hf)
    have := H (ℓ ∘ₗ I.trL S) hinv _ (hT f hf)
    have e1 : (ℓ ∘ₗ I.trL S) (I.symm.trW S f) = ℓ f := congrArg ℓ (I.symm.trW_symm_trW S f)
    rw [e1] at this
    exact this

end GlobalTheory.ConjLine

noncomputable section
namespace GlobalTheory.ConjLine
open GlobalTheory.Mem.Isom GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger
variable {D : D7}

theorem cT_eq_conjTranspose {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := Matrix.ext fun _ _ => rfl

theorem cmHost_imaginaryGenerator_ne_zero : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero (D := D)

def sc (D : D7) : D.host.E := star (-D.host.xi0⁻¹)

theorem sc_mul : star (sc D) * sc D * (D.host.xi0 * star D.host.xi0) = 1 := by
  have h := cmHost_imaginaryGenerator_ne_zero (D := D)
  have h' : star D.host.xi0 ≠ 0 := star_ne_zero.2 h
  simp only [sc, star_star, star_neg, star_inv₀]
  field_simp

theorem gram_sc (L L' : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E)
    (hg : τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (sc D • τ) * L.gram * (sc D • τ) = L'.gram := by
  rw [cT_eq_conjTranspose, Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [hg, smul_smul]
  convert one_smul D.host.E L'.gram using 2
  have := sc_mul (D := D)
  simp only [Int.cast_one, one_mul]
  linear_combination this

def isoOf (L L' : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (hr : L.rank = L'.rank)
    (hg : τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram) : IsoMat L' L where
  P := sc D • τ
  Q := L'.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (sc D • τ) * L.gram
  QP := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ L.gram, gram_sc L L' τ hg,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det L')]
  PQ := by
    refine (Matrix.mul_eq_one_comm_of_equiv (finCongr hr)).2 ?_
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ L.gram, gram_sc L L' τ hg,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det L')]
  gram := gram_sc L L' τ hg

theorem dagger_sc (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (w : WO S L') :
    dagger S L (HMul.hMul ((sc D • τ).map (incA D)) w) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w) := by
  have e : (sc D • τ).map (incA D) = incA D (sc D) • (rat τ : Mx D L.rank L'.rank) := by
    ext i j; simp [rat]
  rw [e, Matrix.smul_mul, dagger, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj, adj_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  show incA D (star (sc D)) = _
  simp [sc]

end GlobalTheory.ConjLine

noncomputable section
namespace GlobalTheory.ConjLine
open GlobalTheory.Mem.Isom GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger
variable {D : D7}

theorem trW_cj (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (hr : L.rank = L'.rank)
    (hg : τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram) (f : WO L S → ℂ) :
    (isoOf L L' τ hr hg).symm.trW S (cj (dagger S L) f) =
      fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) := by
  funext w
  show starRingEnd ℂ (f (dagger S L (HMul.hMul ((sc D • τ).map (incA D)) w))) = _
  rw [dagger_sc]
  rfl

theorem trivOnF_of_resEta {χ χ' : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (h' : ResEta D χ' n) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.TrivOnF D (χ⁻¹ * χ') := by
  intro a
  obtain ⟨η, hη⟩ := h.1
  have e1 := h.2 η hη a
  have e2 := h'.2 η hη a
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, e1, e2, inv_mul_cancel]

theorem conj_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E), L.rank = L'.rank → τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ (χz χ χ' : ((AE D)ˣ →* Circle)) (om : Om L S) (om' : Om S L'), IsWeilDatumO ψ L S χz χ om → IsWeilDatumO ψ S L' χ' χz om' → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L' (fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) ∧ ∀ h, om' (h, 1) (fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) = fun w => star (om (1, h) f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) := by
  intro D ψ L L' S τ hr hg χz χ χ' om om' hom hom' f hf
  have CA := GlobalTheory.T.weilConjugationAdjointRule_standard_char D ψ hom.std L S
  have hW : IsWeilDatumO ψ S L χ χz (conjAdjoint om) := (CA.conj_adjoint χz χ om hom).1
  have hF₁ : IsThetaFunO ψ S L (cj (dagger S L) f) := (CA.theta_dagger f).2 hf
  set I := (isoOf L L' τ hr hg).symm with hI
  have hG : IsThetaFunO ψ S L' (I.trW S (cj (dagger S L) f)) := isThetaFunO_tr I S hF₁
  rw [hI, trW_cj] at hG
  refine ⟨hG, fun h => ?_⟩
  have hW₀ : IsWeilDatumO ψ S L' χ χz (I.omT S (conjAdjoint om)) := isWeilDatumO_tr I S hW
  have hom'' : IsWeilDatumO ψ S L' (χ * (χ⁻¹ * χ')) (χz * 1) om' := by
    rw [mul_inv_cancel_left, mul_one]; exact hom'
  obtain ⟨a, b, ha, hb, e⟩ := (GlobalTheory.WeilDetermined.weilDatumDetermined D).2 ψ S L' χ χz (χ⁻¹ * χ') 1
    (I.omT S (conjAdjoint om)) om' (trivOnF_of_resEta hom.resT hom'.resS) (fun _ => rfl) hW₀ hom'' h 1
  have ha1 : a = 1 := by
    obtain ⟨x, hx⟩ := ha.1
    exact (ha.2 x hx).symm
  have hb1 : b = 1 := hb.at_one
  refine (e _ hG).trans ?_
  rw [ha1, hb1, inv_one, one_mul]
  simp only [Circle.coe_one, one_smul]
  rw [← trW_cj L L' S τ hr hg, ← hI, IsoMat.omT_apply, map_one, I.trW_symm_trW, ← trW_cj L L' S τ hr hg, ← hI]
  congr 1
  exact cjEnd_cj (daggerEquiv L S) (om (1, h)) f

end GlobalTheory.ConjLine
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLineStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_conj_sourceLine_eq_targetLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E), L.rank = L'.rank → τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ (χz χ χ' : ((AE D)ˣ →* Circle)) (om : Om L S) (om' : Om S L'), IsWeilDatumO ψ L S χz χ om → IsWeilDatumO ψ S L' χ' χz om' → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L' (fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) ∧ ∀ h, om' (h, 1) (fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) = fun w => star (om (1, h) f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) := by
  first | exact @GlobalTheory.ConjLine.conj_line | exact GlobalTheory.ConjLine.conj_line | (intros; apply GlobalTheory.ConjLine.conj_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HostFieldsPrimesTies
open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Core.Ht2

theorem host_fields_primes_ties : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)), (I.rec7 l Z).host.ccK = ⊤ ∧ GL3Theta.InducedCMType (I.rec7 l Z) ∧ GL3Theta.HostFieldConditions (I.rec7 l Z) ∧ B.fields.AbelianUnramifiedExtensionConditions ∧ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G).Ok ∧ (∀ x : B.fields.K, B.embLL (star x) = starRingEnd ℂ (B.embLL x)) ∧ (B.primes X).Ok ∧ (B.primes X).PiGCong ∧ (B.primes X).cond = B.host.QS * B.host.q * B.host.d ∧ (∀ i, (B.primes X).g i = B.host.g i) ∧ B.wts.Ok := by
  intro B X I _ _ l Z
  exact ⟨B.toPre.ccK_top, GlobalTheory.InducedType.restrict_K _, Formalism.MainNotions.GL3Theta.cm_field_facts_hold _, (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1,
    seamOf_ok B (I.cols l) Z.W Z.V Z.S Z.N Z.G, B.starLL_cx, (GlobalTheory.BasePrimes.primes_ok B X).1, (GlobalTheory.BasePrimes.primes_ok B X).2,
    rfl, fun _ => rfl, B.wts_isOk⟩

end GlobalTheory.Core.Ht2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaOfHeisenbergIntertwinerBoundedAtZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaOfHeisenbergIntertwinerBoundedAtZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.ThetaMap

variable {D : D7}

theorem heisO_apply_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (g : WO S T → ℂ) :
    heisO ψ S T w g 0 = g w := by
  have h0 : hO S T 0 w = 0 := by simp [hO]
  simp [heisO, symplOH, symplO, h0]

theorem thetaMap : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T S₀ T₀ : HSp D) (ι : WO S₀ T₀ →+ WO S T), Continuous ι → (∀ w, w.map (finPart D) = 0 → (ι w).map (finPart D) = 0) → (∀ w, w.map (infPart D) = 0 → (ι w).map (infPart D) = 0) → ∀ A : (WO S T → ℂ) → WO S₀ T₀ → ℂ, IsSobForm ψ θ S T (fun f => A f 0) → (∀ f w, IsThetaFunO ψ S T f → A (heisO ψ S T (ι w) f) = heisO ψ S₀ T₀ w (A f)) → (∀ f γ, IsThetaFunO ψ S T f → A f (ratW T₀ S₀ γ) = A f 0) → ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S₀ T₀ (A f) := by
  intro D ψ hψ θ hθ S T S₀ T₀ ι hιc hιf hιi A hA hint hrat f hf

  have key : ∀ w, A f w = A (heisO ψ S T (ι w) f) 0 := by
    intro w
    rw [hint f w hf, heisO_apply_zero]
  have hfun : A f = fun w => (fun g => A g 0) (heisO ψ S T (ι w) f) := funext key
  obtain ⟨hc, hs⟩ := GlobalTheory.T.sobolevBoundedThetaForm_matrixCoeff_smooth D ψ hψ θ hθ S T (fun g => A g 0) hA f hf
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro γ w
    have h1 := hrat (heisO ψ S T (ι w) f) γ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (ι w))
    rw [hint f w hf, heisO_apply_zero] at h1
    simp only [heisO] at h1
    rw [← h1, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  ·
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap ι, hUo.preimage hιc, fun u hu hui => ?_⟩
    rw [← hint f u hf, hU (ι u) hu (hιi u hui)]
  ·
    rw [hfun]
    exact hc.comp hιc
  ·
    intro k L hL hLf w
    have h2 := hs k (ι.comp L) (hιc.comp hL) (fun t => hιf (L t) (hLf t)) (ι w)
    rw [hfun]
    simpa [map_add (f := _)] using h2

end GlobalTheory.ThetaMap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaOfHeisenbergIntertwinerBoundedAtZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_of_heisenberg_intertwiner_bounded_at_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T S₀ T₀ : HSp D) (ι : WO S₀ T₀ →+ WO S T), Continuous ι → (∀ w, w.map (finPart D) = 0 → (ι w).map (finPart D) = 0) → (∀ w, w.map (infPart D) = 0 → (ι w).map (infPart D) = 0) → ∀ A : (WO S T → ℂ) → WO S₀ T₀ → ℂ, IsSobForm ψ θ S T (fun f => A f 0) → (∀ f w, IsThetaFunO ψ S T f → A (heisO ψ S T (ι w) f) = heisO ψ S₀ T₀ w (A f)) → (∀ f γ, IsThetaFunO ψ S T f → A f (ratW T₀ S₀ γ) = A f 0) → ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S₀ T₀ (A f) := by
  first | exact @GlobalTheory.ThetaMap.thetaMap | exact GlobalTheory.ThetaMap.thetaMap | (intros; apply GlobalTheory.ThetaMap.thetaMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DerivativeClosedFunctionClassSmoothAndSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DerivativeClosedFunctionClassSmoothAndSchwartz
open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

namespace GlobalTheory.Unf.PartialClass

theorem smooth_schwartz : ∀ (k : ℕ) (V : Set ((Fin k → ℝ) → ℂ)), (∀ φ ∈ V, Continuous φ) → (∀ φ ∈ V, ∀ i : Fin k, ∃ φ' ∈ V, ∀ x : Fin k → ℝ, HasDerivAt (fun t : ℝ => φ (x + t • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' x) 0) → (∀ φ ∈ V, ContDiff ℝ ∞ φ) ∧ ((∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ N * ‖φ x‖ ≤ C) → ∀ φ ∈ V, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ x, g x = φ x) := by
  intro k V hc hd
  have hsm : ∀ φ ∈ V, ContDiff ℝ ∞ φ := by
    refine GlobalTheory.Unf.MatCoef.contDiff_of_partials (fun F => F ∈ V) hc ?_
    intro F hF i
    obtain ⟨φ', hφ', hD⟩ := hd F hF i
    refine ⟨1, fun _ => fun _ => 1, fun _ => φ', fun _ => contDiff_const, fun _ => hφ', ?_⟩
    intro t
    simpa using hD t
  refine ⟨hsm, fun hdec => ?_⟩
  choose φ' hφ' hD using hd

  have hfd : ∀ φ (hφ : φ ∈ V), fderiv ℝ φ = fun x => ∑ i, φ' φ hφ i x •
      (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (1 : ℂ) := by
    intro φ hφ
    funext x
    have h := GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_partials k φ (fun i => φ' φ hφ i) (fun i => hc _ (hφ' φ hφ i)) (fun i t => hD φ hφ i t) x
    rw [h.fderiv]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext v
    simp [mul_comm]
  have key : ∀ j : ℕ, ∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ N * ‖iteratedFDeriv ℝ j φ x‖ ≤ C := by
    intro j
    induction j with
    | zero =>
      intro φ hφ N
      obtain ⟨C, hC⟩ := hdec φ hφ N
      exact ⟨C, fun x => by simpa [norm_iteratedFDeriv_zero] using hC x⟩
    | succ j ih =>
      intro φ hφ N
      choose C hC using fun i => ih (φ' φ hφ i) (hφ' φ hφ i) N
      set L : Fin k → ((Fin k → ℝ) →L[ℝ] ℂ) := fun i =>
        (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (1 : ℂ)
      refine ⟨∑ i, ‖(ContinuousLinearMap.id ℝ ℂ).smulRight (L i)‖ * C i, fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv, hfd φ hφ]
      have hsum : iteratedFDeriv ℝ j (fun x => ∑ i, φ' φ hφ i x • L i) x =
          ∑ i, ((ContinuousLinearMap.id ℝ ℂ).smulRight (L i)).compContinuousMultilinearMap
            (iteratedFDeriv ℝ j (φ' φ hφ i) x) := by
        rw [iteratedFDeriv_fun_sum_apply]
        · refine Finset.sum_congr rfl fun i _ => ?_
          exact iteratedFDeriv_smul_const_apply
            (((hsm _ (hφ' φ hφ i)).of_le (mod_cast le_top)).contDiffAt)
        · intro i _
          exact (((hsm _ (hφ' φ hφ i)).of_le (mod_cast le_top)).smul contDiff_const).contDiffAt
      rw [hsum]
      refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)) ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      refine le_trans (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _)
        (by positivity)) ?_
      have := hC i x
      nlinarith [norm_nonneg ((ContinuousLinearMap.id ℝ ℂ).smulRight (L i)),
        norm_nonneg (iteratedFDeriv ℝ j (φ' φ hφ i) x), pow_nonneg (norm_nonneg x) N]
  intro φ hφ
  refine ⟨{ toFun := φ, smooth' := hsm φ hφ, decay' := fun N j => ?_ }, fun x => rfl⟩
  obtain ⟨C, hC⟩ := key j φ hφ N
  exact ⟨C, hC⟩

end GlobalTheory.Unf.PartialClass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DerivativeClosedFunctionClassSmoothAndSchwartzStatement
open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivativeClosedFunctionClass_smooth_and_schwartz : ∀ (k : ℕ) (V : Set ((Fin k → ℝ) → ℂ)), (∀ φ ∈ V, Continuous φ) → (∀ φ ∈ V, ∀ i : Fin k, ∃ φ' ∈ V, ∀ x : Fin k → ℝ, HasDerivAt (fun t : ℝ => φ (x + t • (Pi.single i (1 : ℝ) : Fin k → ℝ))) (φ' x) 0) → (∀ φ ∈ V, ContDiff ℝ ∞ φ) ∧ ((∀ φ ∈ V, ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ N * ‖φ x‖ ≤ C) → ∀ φ ∈ V, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ x, g x = φ x) := by
  first | exact @GlobalTheory.Unf.PartialClass.smooth_schwartz | exact GlobalTheory.Unf.PartialClass.smooth_schwartz | (intros; apply GlobalTheory.Unf.PartialClass.smooth_schwartz <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentUnfoldingBesselFourierJacobiEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentUnfoldingBesselFourierJacobiEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.Unf.StepFour

variable {D : D7}

theorem zEll_mem_ratMx (T : HSp D) (ρ : ℕ) (z : Fin T.rank → D.host.E) : zEll T ρ z ∈ ratMx D T.rank ρ := by
  refine ⟨Matrix.vecMulVec z (fun i : Fin ρ => if i.1 + 1 = ρ then (1 : D.host.E) else 0), ?_⟩
  funext i j
  change incA D (z i * (if j.1 + 1 = ρ then (1 : D.host.E) else 0)) = ratV z i * ell D ρ j
  simp only [ratV, ell]
  split_ifs <;> simp

theorem incAdj_yZero_mem {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Fin S.rank → D.host.E) :
    d.incAdj S (yZero S ρ z) ∈ ratMx D T.rank S.rank := by
  have hy : yZero S ρ z ∈ ratMx D S.rank ρ := by
    rw [yZero]; exact neg_mem (zEll_mem_ratMx S ρ z)
  rw [HypDec.incAdj_apply, HypDec.incY_apply]
  exact ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (x : AF D.host.F) :
    star (ψ x) = ψ (-x) := by
  change (starRingEnd ℂ) (ψ x) = _
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.1.2.1 x)]

end GlobalTheory.Unf.StepFour
end

noncomputable section
namespace GlobalTheory.Unf.StepFour

variable {D : D7}

theorem integrand_eq {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {ρ : ℕ}
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) (f : WO V₀ W → ℂ)
    (hf : IsThetaFunO ψ V₀ W f) (b : Mx D ρ V₀.rank) :
    star (psiBes ψ dV 1 z (dV.nB b)) * f (xZero dW ⬝ b) =
      heisO ψ V₀ W (dW.incX V₀ b) (heisO ψ V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (heisO ψ V₀ W (dW.inc0 V₀ 0) f)) 0 := by
  rw [HypDec.integrandT_eq, ← psi_yZero ψ dV dW z b, star_psi hψ, map_zero, add_zero]
  obtain ⟨γ, hγ⟩ := incAdj_yZero_mem dW V₀ z
  have hx : dW.incX V₀ b = xZero dW ⬝ b := rfl
  have hq := hf.quasi γ (xZero dW ⬝ b)
  rw [show ratW W V₀ γ = dW.incAdj V₀ (yZero V₀ ρ z) from hγ] at hq
  rw [hx, add_comm (xZero dW ⬝ b), hq, ← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hc : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add (f := _), add_halves, map_one]
  have hs : symplO V₀ W (xZero dW ⬝ b) (dW.incAdj V₀ (yZero V₀ ρ z)) =
      -symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (xZero dW ⬝ b) := GlobalTheory.OrientedHeis.symplO_skew _ _
  rw [symplOH, symplOH]
  linear_combination (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (xZero dW ⬝ b)) * hc -
    algebraMap D.host.F (AF D.host.F) (1 / 2) * hs

end GlobalTheory.Unf.StepFour
end

noncomputable section
namespace GlobalTheory.Unf.StepFour

theorem fl_eq_flatBF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J)
    (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ →
      fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flatBF s Ψ 0 := by
  intro D ψ ρ B J s Ψ hΨ
  have hψ : IsStdChar D ψ (-1) := s.weil.std
  have hf : ∀ x, IsThetaFunO ψ B.V₀ J.W (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x) := fun x =>
    (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  unfold fl flatBF flat flatAt
  congr 1
  funext u
  have hu : ∀ b, star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b * B.d.levi u.1)) =
      star (psiUni ψ u.1) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b)) := by
    intro b
    rw [psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.levi_mem_NFlag (mem_UX.1 u.2)), psiBes_levi, star_mul',
      mul_comm]
  unfold flFun flatFun evalAt
  simp_rw [hu, mul_assoc]
  rw [integral_const_mul]
  congr 1
  congr 1
  funext b
  exact integrand_eq hψ B.d J.d _ _ (hf _) b

end GlobalTheory.Unf.StepFour
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentUnfoldingBesselFourierJacobiEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotentUnfolding_besselFourierJacobi_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → fl ψ B.d J.W s.vS s.vT s.vU (fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n)) (xZero J.d) Ψ = flatBF s Ψ 0 := by
  first | exact @GlobalTheory.Unf.StepFour.fl_eq_flatBF | exact GlobalTheory.Unf.StepFour.fl_eq_flatBF | (intros; apply GlobalTheory.Unf.StepFour.fl_eq_flatBF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NrmStepZeroEq
noncomputable section

namespace GlobalTheory.Core.ColNorm

open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.StepZero

section Forget

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
  (pref : DecoF X.E n ST SG Q → Prop) (lam : X.Tau → DomWeight n) {Λ₀ : LevFam X.E X.K n SG}
  (pf : ∀ b, (stepY ST y β Λ Θ pref).D b → Prop)

def secR [Unique β] (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) :
    (base ST lam Λ₀).Sec where
  rep c := (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c)).1.1.deco
  spec c := by
    obtain ⟨⟨b, q⟩, rfl⟩ := (clEquiv pref lam hy hΛ hΘ).surjective c
    rw [Equiv.symm_apply_apply]
    refine (clMap_cl (Θ := Θ) pref lam hΛ b _).symm.trans ?_
    exact congrArg (fun q => clMap (y := y) (Λ := Λ) (Θ := Θ) (Λ₀ := Λ₀) pref lam ⟨b, q⟩) (((stepY ST y β Λ Θ pref).reRep pf).rp_spec b q)

theorem majAt_eq_ipAt [Unique β] (hX : X.Ok) (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (hS : ((stepY ST y β Λ Θ pref).reRep pf).Ok)
    (h : (((stepY ST y β Λ Θ pref).reRep pf).fam X.emb lam).Ok) (h₀ : (base ST lam Λ₀).Ok) (hr : (base ST lam Λ₀).Rat)
    (v : InfinitePlace X.K) (x : ((stepY ST y β Λ Θ pref).reRep pf).FormsK X.emb lam h) (φ : (base ST lam Λ₀).EqFun)
    (hx : ∀ c, x.1 c = φ.1 (((stepY ST y β Λ Θ pref).reRep pf).rep c).1.1.deco) :
    Formalism.HermitianLatticesTheory.majAt (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).b
      (((stepY ST y β Λ Θ pref).reRep pf).hlat X.emb lam h).X v x x = (base ST lam Λ₀).ipAt h₀ v φ φ := by
  obtain ⟨σ, hσ⟩ := hX.conjK
  have hF : FOk X.emb σ := ⟨hX.conjE, hX.emb_star, hσ⟩
  refine (majAt_eq_classSum (((stepY ST y β Λ Θ pref).reRep pf).csd X.emb lam h) (GlobalTheory.Mem.LatGood.hasRatBasis _ _ σ lam hF hS h)
    (fun v => GlobalTheory.Mem.LatGood.step_gram_posDef _ _ σ lam hF hS h v.embedding) v _ _).trans ?_
  rw [hr.ipAt_indep h₀ (secR pref lam pf hy hΛ hΘ)]
  refine (@Fintype.sum_equiv _ _ _ (_) (_) _ (clEquiv pref lam hy hΛ hΘ).symm _ _ fun c => ?_).symm
  rw [hx]
  congr 3
  refine (card_stab pref hy hΛ hΘ ((clEquiv pref lam hy hΛ hΘ).symm c).1 (((stepY ST y β Λ Θ pref).reRep pf).rep ((clEquiv pref lam hy hΛ hΘ).symm c))).symm.trans ?_
  exact @Nat.card_eq_fintype_card _ (_)

end Forget

end GlobalTheory.Core.ColNorm

namespace GlobalTheory.Core.ColNorm

open NumberField IsDedekindDomain _root_.Formalism.BasicNotions _root_.Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem nrm_stepZero_eq : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (hX : B.fields.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (x : ((I.fm l u a).lat 0).V) (φ : ColsK I u), IsCol I u a l x φ → ∀ v, nrm ((I.fm l u a).lat 0) v x = nrm (Mu0H (Pr := B.primes X) B.wts I.Ch hX u) v φ := by
  intro B X I h hX l u a x φ hc v
  have hL := h.idx_ok a
  letI := StepZero.idxUnique hL
  have key := majAt_eq_ipAt ((I.Tp a).pref u 0) (lamT (B.hcW u) 0) (I.pref u a 0) hX
    (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a)) (StepZero.levGAt_zero (I.Tp a) hL) (StepZero.levQAt_zero (I.Tp a) hL)
    ((l.ch u a).step 0) ((l.fmL u a).fam 0) (colOk (Pr := B.primes X) B.wts I.Ch hX u 0) (colRat (Pr := B.primes X) B.wts I.Ch hX u 0) v x φ hc
  have key2 := key.trans (latH_maj (Pr := B.primes X) B.wts I.Ch hX u 0 v φ φ).symm
  have h1 := normAt_sq_eq_majAt ((I.fm l u a).lat 0).b ((I.fm l u a).lat 0).X v x
  have h2 := normAt_sq_eq_majAt (Mu0H (Pr := B.primes X) B.wts I.Ch hX u).b (Mu0H (Pr := B.primes X) B.wts I.Ch hX u).X v φ
  exact (pow_left_inj₀ (normAt_nonneg _ _ _ _) (normAt_nonneg _ _ _ _) two_ne_zero).1
    (h1.trans ((congrArg Complex.re key2).trans h2.symm))

end GlobalTheory.Core.ColNorm

end
end
