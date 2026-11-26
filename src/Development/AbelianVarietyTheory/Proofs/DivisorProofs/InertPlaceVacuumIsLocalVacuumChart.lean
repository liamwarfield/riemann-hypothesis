module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralShiftExists

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceVacuumIsLocalVacuumChart
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridgeVac

theorem acts_eq {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ}
    {r : (κ → AF F) → ℂ} (hr : Rest (evFin F v) φ r) {x₀ : κ → AF F} (hx₀ : r x₀ ≠ 0)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h1 : Acts (evFin F v) T φ φ₁) (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i)) with hz
  have hza : At (evFin F v) z := fun u hu => funext fun i => by
    simpa only [hz, Pi.smul_apply, Pi.zero_apply] using
      GlobalTheory.LatVac.at_liftV v (y i - evFin F v (x₀ i)) u hu
  have hrx : r (x₀ + z) = r x₀ := hr.1 x₀ z hza
  have hy : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [hz, Pi.add_apply, map_add (f := _), GlobalTheory.LatVac.evFin_liftV, add_sub_cancel]
  have e := congrFun ((h1 r hr).symm.trans (h2 r hr)) (x₀ + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hx₀ e

theorem evFin_half_mem {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (h : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have e : evFin F v (⅟(2 : AF F)) = algebraMap F (Fv F v) (2 : F)⁻¹ := by
    have h1 : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
      have := congrArg (evFin F v) (invOf_mul_self (2 : AF F))
      rwa [map_mul, map_ofNat, map_one] at this
    have h2 : algebraMap F (Fv F v) (2 : F)⁻¹ * 2 = 1 := by
      rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
    have h20 : (2 : Fv F v) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
    exact mul_right_cancel₀ h20 (h1.trans h2.symm)
  rw [e]
  exact GlobalTheory.LatVac.half_mem_adicCompletionIntegers F v h

theorem vac_locVac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∃ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v ∧ s ≠ 0 ∧
      GlobalTheory.Hk3.LocVac ρ s := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hLat, _⟩ := hC
  obtain ⟨hSB, hne, θ, _, hfix⟩ := hTr.geo.hM'.vac v
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hTr.base.inert v w hin).1
  have hb := evFin_half_mem v h2
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v (G.M'.vac v) hSB
  refine ⟨⟨G.M'.vac v, hSB⟩, rfl, fun h => hne (congrArg Subtype.val h), fun u hu => ?_⟩
  have hγ : κ u ∈ latAtV G.V' G.W v := (hLat u).1 hu
  have hone := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hTr.base hTr.geo.hV' hTr.geo.hW v θ
    (⅟(2 : AF F)) hb (κ u) hγ (κ u) hγ
  have h1 := hfix (κ u) hγ
  rw [hone, one_smul] at h1
  apply Subtype.ext
  exact acts_eq v hr hx₀ _ _ _ (hρ u ⟨G.M'.vac v, hSB⟩) h1

end GlobalTheory.InertBridgeVac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaSpanFiniteDimensionalDualPair
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaSpanFiniteDimensionalDualPair
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
open scoped Matrix

noncomputable section

namespace GlobalTheory.FockKFin.VacFin

open GlobalTheory.ThK.EvAt0.PolD Formalism.BasicNotions.TH

theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem Jm_transpose (p q : ℕ) : (Jm p q)ᵀ = Jm p q := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]

theorem vac_mem_line {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (h : GlobalTheory.ThK.IsPair B M χX χW om r s r' s') :
    ∃ v : SInf F (Fin n × Fin d), ∀ g, GaussD M B.emb g → ∃ z : ℂ, g = z • v := by
  have hb := h.base
  choose A hA hAθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (h.herm.sig w) (h.herm.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.RealLift.frameEx_holds _ _ _ _ _ (h.skew.sig w) (h.skew.cartan w)
  have hA1 : ∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.FockMapEx.fockEx_of_derEx GlobalTheory.HeisDer.derEx F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I
    A C hb.cm hb.std fr
  obtain ⟨D, hD⟩ := GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hb.std
  have hDd : ∀ u, At (evI F) u → ∀ f : SInf F (Fin n × Fin d), D u f = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
    intro u hu f
    refine DFunLike.ext _ _ fun x => ?_
    rw [(hD u hu f).2 x, dOp_apply]
    try rfl
  have tw : ∀ w (c : Matrix (Ix r s) (Ix r' s') ℂ) (e : ℂ),
      A w * (e • (Jm r s * c * Jm r' s')) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm r' s' * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hCθ w, Matrix.transpose_mul, Jm_transpose]
    calc A w * (e • (Jm r s * c * Jm r' s')) * (C w)ᵀ = e • ((A w * Jm r s) * c * (Jm r' s' * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hAθ w, ← h2]; simp only [Matrix.mul_assoc]
  refine ⟨Φ (PiTensorProduct.tprod ℂ fun _ => 1), fun g ⟨ε, hε⟩ => ?_⟩
  refine GlobalTheory.VacLn.vacLine_of_derEx GlobalTheory.HeisDer.derEx F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ
    hb.cm hb.std fr hΦ g ε ?_
  intro u u' hu hu' c hc hc' f f' hf hf'
  have e1 : f = D u g := (GlobalTheory.RealLift.actsLaws F _ g f (D u g)).2.2.2.2 _ hf (hD u hu g).1
  have e2 : f' = D u' g := (GlobalTheory.RealLift.actsLaws F _ g f' (D u' g)).2.2.2.2 _ hf' (hD u' hu' g).1
  rw [e1, e2, hDd u hu, hDd u' hu']
  exact hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w])

end GlobalTheory.FockKFin.VacFin

theorem GlobalTheory.FockKFin.vacSp_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → FiniteDimensional ℂ (GlobalTheory.FockKFin.vacSp M B.emb) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  obtain ⟨v, hv⟩ := GlobalTheory.FockKFin.VacFin.vac_mem_line σ B n d X W M χX χW om r s r' s' h
  have hle : GlobalTheory.FockKFin.vacSp M B.emb ≤ Submodule.span ℂ {v} := by
    refine Submodule.span_le.2 fun g hg => ?_
    obtain ⟨z, rfl⟩ := hv g hg
    exact Submodule.smul_mem _ z (Submodule.subset_span rfl)
  exact Submodule.finiteDimensional_of_le hle

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaSpanFiniteDimensionalDualPairStatement
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacua_span_finiteDimensional_dualPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → FiniteDimensional ℂ (GlobalTheory.FockKFin.vacSp M B.emb) := by
  first | exact @GlobalTheory.FockKFin.vacSp_finiteDimensional | exact GlobalTheory.FockKFin.vacSp_finiteDimensional | (intros; apply GlobalTheory.FockKFin.vacSp_finiteDimensional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsFramesMajorantNormEqPetersson
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsFramesMajorantNormEqPetersson
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.FrameRead

theorem normAt_eq_sqrt {K : Type} [Field K] [NumberField K] {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.cnorm
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show star (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v x i) = (starRingEnd ℂ) (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v x i) from rfl,
    Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem frames_read : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)
    (i : Fin D.R.m), (R.toCx3 F).KForm b →
    (∀ v, IsUnit ((R.toCx3 F).XW b i v).det) ∧
      ∀ v (c : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)) → D.what₂.LL),
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).XW b i) v c =
          (Real.sqrt (RealDat.nP F.lv2 b))⁻¹ * nrmR R.toRealDat i v.embedding (∑ k, c k • R.toRealDat.bL F.lv2 b i k) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F b i hK
  refine ⟨fun v => frame_gram_unit _ (hK i v).1, fun v c => ?_⟩
  have h1 := normAt_eq_sqrt (n := (R.toCx3 F).dW b i) ((R.toCx3 F).XW b i) v c
  have h2 := majAt_gram ((R.toCx3 F).XW b i) v ((R.toCx3 F).bW b i v) (hK i v).1 rfl c c
  refine h1.trans ?_
  have h3 : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (z : E), Real.sqrt (inner ℂ z z).re = ‖z‖ := by
    intro E _ _ z
    rw [show (inner ℂ z z).re = ‖z‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) z, Real.sqrt_sq (norm_nonneg _)]
  rw [h2, h3]
  set s := twAt D.what₂.embLL v
  set σ := sgAt D.what₂.embLL v
  have hl : lin ((R.toCx3 F).bW b i v) (cpt v.embedding c) =
      Tw.mk s (∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ)) := by
    rw [lin_apply]
    have e : ∀ x : ↥(R.toRealDat.WS F.lv2 b i σ), Tw.mk s x = Tw.mkL s ↥(R.toRealDat.WS F.lv2 b i σ) x := fun _ => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ]
    show v.embedding (c k) • _ = _
    rw [emb_eq D.what₂.embLL v (c k)]
    rfl
  rw [hl]
  have hc : (((∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ)) : R.toRealDat.WS F.lv2 b i σ) : (R.HW i σ).H) =
      (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) • (R.FW i).j σ (∑ k, c k • R.toRealDat.bL F.lv2 b i k) := by
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, RealDat.bC]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, smul_comm]
  calc ‖Tw.mk s (∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ))‖
      = ‖(((∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ)) : R.toRealDat.WS F.lv2 b i σ) : (R.HW i σ).H)‖ := rfl
    _ = _ := by
      rw [hc, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
      unfold nrmR
      rw [InfinitePlace.mk_embedding]

end GlobalTheory.FrameRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFormsFramesMajorantNormEqPeterssonStatement
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftForms_frames_majorantNorm_eq_petersson : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)
    (i : Fin D.R.m), (R.toCx3 F).KForm b →
    (∀ v, IsUnit ((R.toCx3 F).XW b i v).det) ∧
      ∀ v (c : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)) → D.what₂.LL),
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).XW b i) v c =
          (Real.sqrt (RealDat.nP F.lv2 b))⁻¹ * nrmR R.toRealDat i v.embedding (∑ k, c k • R.toRealDat.bL F.lv2 b i k) := by
  first | exact @GlobalTheory.FrameRead.frames_read | exact GlobalTheory.FrameRead.frames_read | (intros; apply GlobalTheory.FrameRead.frames_read <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPairPartnerCmExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPairPartnerCmExtension
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilPairPartnerF

theorem pair_partnerF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (a : UG (cA σ) (incM F JA)) (b : UG (cA σ) (incM F JB)),
          ∃ (g : GAF σ JS) (h : GAF σ JT), mtF σ JT h = a.1.1 ∧ mtF σ JS g = (b⁻¹).1.1ᵀ := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT hS _ ξ₀ hξ₀ _ JA JB ξ hA hB a b
  have hmap : ∀ {m n : Type} (X : Matrix m n (AF F ⊗[F] E)),
      X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) :=
    fun X => Matrix.ext fun i j => rfl

  have ha : (a.1.val)ᵀ * incM F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = incM F JA := a.2
  set A : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E) := a.1.val with hAdef
  have hJA : incM F JA = (incM F JT)ᵀ := by
    rw [hA]; rfl
  rw [hJA] at ha
  have ha' := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'
  have hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JT := by
    show Formalism.UG.cT _ a.1.val * _ * a.1.val = _
    simp only [Formalism.UG.cT, hmap]
    rw [Matrix.mul_assoc]
    exact ha'

  obtain ⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ = f := ⟨_, rfl⟩
  have hb : (b.1.val)ᵀ * incM F JB * (b.1.val).map cR = incM F JB := by
    rw [← hcR, hmap]; exact b.2
  have hBB : b.1.val * (b⁻¹).1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).mul_inv
  have hBB' : (b⁻¹).1.val * b.1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).inv_mul
  obtain ⟨Bm, hBdef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), b.1.val = M := ⟨_, rfl⟩
  obtain ⟨Bi, hBidef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), (b⁻¹).1.val = M := ⟨_, rfl⟩
  rw [hBdef] at hb hBB hBB'
  rw [hBidef] at hBB hBB'
  have hdet : JS.det ≠ 0 := hS.2
  have hGN := GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := F) (E := E) (AF F)) JS hdet
  have hNG := GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := F) (E := E) (AF F)) JS hdet
  have hsm : incM F (ξ₀ • JS⁻¹) = inclR (F := F) (AF F) ξ₀ • incM F JS⁻¹ :=
    GlobalTheory.WeilPairPartner.map_smul_eq _ _ _
  have hu : IsUnit (inclR (F := F) (E := E) (AF F) ξ₀) :=
    (isUnit_iff_ne_zero.mpr hξ₀).map _
  have hcore := GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu Bm Bi (incM F JB) (incM F JS)
    (incM F JS⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG
  have hTT : Biᵀ * Bmᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  let gU : GL (Fin nS) (AF F ⊗[F] E) :=
    ⟨Biᵀ, Bmᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩
  have hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JS := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) Biᵀ * incM F JS * Biᵀ = incM F JS
    rw [hcR]
    simp only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]
    exact hcore
  refine ⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩
  show Biᵀ = ((b⁻¹).1.val)ᵀ
  rw [hBidef]

end GlobalTheory.WeilPairPartnerF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPairPartnerCmExtensionStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryPair_partner_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (a : UG (cA σ) (incM F JA)) (b : UG (cA σ) (incM F JB)),
          ∃ (g : GAF σ JS) (h : GAF σ JT), mtF σ JT h = a.1.1 ∧ mtF σ JS g = (b⁻¹).1.1ᵀ := by
  first | exact @GlobalTheory.WeilPairPartnerF.pair_partnerF | exact GlobalTheory.WeilPairPartnerF.pair_partnerF | (intros; apply GlobalTheory.WeilPairPartnerF.pair_partnerF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxChangeIntertwine
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU

noncomputable section

namespace GlobalTheory.TowU

section Dbl

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
  {κ κ' : Type} [Fintype κ] [Fintype κ']

end Dbl

section Adelic

variable {F : Type} [Field F] [NumberField F]

theorem adm_of_eqOn_schA {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ φ ∈ schA F κ, l φ = l' φ) (hl : l ∈ (adeleClass F).adm κ) : l' ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl g hg
  exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩

variable {ψ : AddChar (AF F) ℂ} {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
  {κ κ' : Type} [Fintype κ] [Fintype κ'] {d : Darboux B κ} {d' : Darboux B κ'}
  {s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)}
  {S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}

theorem IsOp.rho_eq (hs : ∀ w, s (d.e w) = d'.e w) (hS : IsOp ψ s S S') (w : W) {φ : (κ → AF F) → ℂ}
    (hφ : φ ∈ schA F κ) : S (d.rho ψ w φ) = d'.rho ψ w (S φ) := by
  simp only [Darboux.rho]
  rw [hS.Heisenberg₂ _ _ hφ, hs]

theorem isUSplitting_of_isOp (hψ : IsStd ψ) (hs : ∀ w, s (d.e w) = d'.e w) (hS : IsOp ψ s S S')
    {G : Type} [Group G] [TopologicalSpace G] {act : G → W → W}
    {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} {om' : G →* Module.End ℂ ((κ' → AF F) → ℂ)}
    (hom : ∀ g, ∀ φ ∈ schA F κ', om' g φ = S (om g (S' φ)))
    (h : IsUSplitting (adeleClass F) ψ d act om) : IsUSplitting (adeleClass F) ψ d' act om' := by
  have hmem : ∀ (κ₀ : Type) [Fintype κ₀] (p : (κ₀ → AF F) × (κ₀ → AF F)) (φ : (κ₀ → AF F) → ℂ),
      φ ∈ schA F κ₀ → schr ψ p φ ∈ schA F κ₀ := fun κ₀ _ p φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ₀ p φ hφ
  have hrho' : ∀ w, ∀ φ ∈ schA F κ', S' (d'.rho ψ w φ) = d.rho ψ w (S' φ) := fun w φ hφ => by
    have h1 := IsOp.rho_eq hs hS w (hS.pres' φ hφ)
    rw [hS.right φ hφ] at h1
    have hm : d.rho ψ w (S' φ) ∈ schA F κ := hmem _ _ _ (hS.pres' φ hφ)
    rw [← h1, hS.left _ hm]
  refine ⟨⟨fun g φ hφ => ?_, fun g w φ hφ => ?_, fun g l hl => ?_⟩, fun μ' hμ' g φ hφ => ?_, fun l hl φ hφ => ?_⟩
  · rw [hom g φ hφ]
    exact hS.pres _ (h.pres g _ (hS.pres' φ hφ))
  · have hw : d'.rho ψ w φ ∈ schA F κ' := hmem _ _ _ hφ
    rw [hom g _ hw, hrho' w φ hφ, h.impl g w _ (hS.pres' φ hφ),
      IsOp.rho_eq hs hS _ (h.pres g _ (hS.pres' φ hφ)), hom g φ hφ]
  · have h2 := hS.adm' _ (h.adm g _ (hS.adm l hl))
    refine adm_of_eqOn_schA (fun φ hφ => ?_) h2
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hom g φ hφ]
  · letI : MeasurableSpace (κ → AF F) := borel _
    haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
    obtain ⟨c, -, -, hc⟩ := hS.norm Measure.addHaar μ' inferInstance hμ'
    rw [hom g φ hφ, hc _ (h.pres g _ (hS.pres' φ hφ)), h.unit Measure.addHaar inferInstance g _ (hS.pres' φ hφ),
      ← hc _ (hS.pres' φ hφ), hS.right φ hφ]
  · refine (h.cont (l ∘ₗ S) (hS.adm l hl) (S' φ) (hS.pres' φ hφ)).congr fun g => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hom g φ hφ]

theorem siegelRule_of_isOp {E' : Type} [CommRing E'] [Algebra (AF F) E'] {c : E' →ₐ[AF F] E'} {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {ξ : E'} {JA : Matrix α α E'} {JB : Matrix β β E'}
    {d : Darboux (symp c ξ JA JB) κ} {d' : Darboux (symp c ξ JA JB) κ'} (hs : ∀ w, s (d.e w) = d'.e w)
    (hS : IsOp ψ s S S') {χ : E'ˣ →* Circle} {ν : Type} [Fintype ν] [DecidableEq ν] {Cy : Matrix β ν E'}
    {om : UG c JB →* Module.End ℂ ((κ → AF F) → ℂ)} {om' : UG c JB →* Module.End ℂ ((κ' → AF F) → ℂ)}
    (hom : ∀ g, ∀ φ ∈ schA F κ', om' g φ = S (om g (S' φ)))
    (h : SiegelRule c (adeleClass F) ψ ξ JA JB d χ Cy om) : SiegelRule c (adeleClass F) ψ ξ JA JB d' χ Cy om' := by
  intro l hl hinv p t hpt φ hφ
  have key := h (l ∘ₗ S) (hS.adm l hl) (fun z φ' hφ' => by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [IsOp.rho_eq hs hS _ hφ']
    exact hinv z _ (hS.pres _ hφ')) p t hpt (S' φ) (hS.pres' φ hφ)
  simp only [LinearMap.coe_comp, Function.comp_apply, hS.right φ hφ] at key
  rw [hom p φ hφ]
  exact key

end Adelic

end GlobalTheory.TowU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalHeisenbergOperatorsLaw
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertRhoLaw

theorem darboux_rho_rho {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w w' : W) (Φ : (κ → R) → ℂ) :
    d.rho ψ w (d.rho ψ w' Φ) = ψ (⅟(2 : R) * B w w') • d.rho ψ (w + w') Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, map_add (f := _), Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  rw [d.form]
  simp only [add_dotProduct, dotProduct_add]
  have h2 : ⅟(2 : R) + ⅟(2 : R) = 1 := invOf_two_add_invOf_two
  linear_combination (-((d.e w).1 ⬝ᵥ (d.e w').2)) * h2

theorem darboux_rho_zero {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (Φ : (κ → R) → ℂ) :
    d.rho ψ 0 Φ = Φ := by
  funext x
  simp [Darboux.rho, schr]

theorem eq_of_tens_eq {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ] {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) (h0 : r 0 ≠ 0) {φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h : tens (evFin F v) φ₁ r = tens (evFin F v) φ₂ r) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i) with hz
  have hza : At (evFin F v) z := by
    intro u hu
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hrx : r (0 + z) = r 0 := hr 0 z hza
  have hy : (fun i => evFin F v ((0 + z) i)) = y := by
    funext i
    simp only [hz, zero_add, GlobalTheory.LatVac.evFin_liftV]
  have e := congrFun h (0 + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ h0 e

end GlobalTheory.InertRhoLaw

namespace GlobalTheory.InertRhoLaw

theorem rho_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ρ 0 = 1 ∧ ∀ x y, ρ x * ρ y = ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) • ρ (x + y) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' _ v w _ _ L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ρ hρ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hEq, -, -, -, -, -⟩ := hC
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a' × Fin (a + a')) v
  have hA : ∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)),
      G.M'.co.rho B.ψ (κ x) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R) =
        tens (evFin F v) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R :=
    fun x m => hρ x m R (hR _ m.2)
  have hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x := (hR 0 (Submodule.zero_mem _)).1
  refine ⟨?_, fun x y => ?_⟩
  · refine LinearMap.ext fun m => Subtype.ext ?_
    refine eq_of_tens_eq v hRi hR0 ?_
    rw [← hA 0 m, map_zero, darboux_rho_zero]
    rfl
  · refine LinearMap.ext fun m => Subtype.ext ?_
    refine eq_of_tens_eq v hRi hR0 ?_
    have e1 := hA x (ρ y m)
    have e2 := hA y m
    have e3 := hA (x + y) m
    have hl := darboux_rho_rho G.M'.co B.ψ (κ x) (κ y) (tens (evFin F v) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) R)
    rw [e2, e1, ← map_add (f := _), e3] at hl
    dsimp only [cA, incM] at hl
    rw [← hEq x y] at hl
    rw [Module.End.mul_apply, hl, LinearMap.smul_apply, Submodule.coe_smul]
    funext z
    simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.InertRhoLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctional
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

noncomputable section
namespace GlobalTheory.HaarSB

section General

variable (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
  [LocallyCompactSpace G]

def measG : MeasurableSpace G := borel G

attribute [local instance] measG

instance borelG : BorelSpace G := ⟨rfl⟩

def intSub : Submodule ℂ (G → ℂ) where
  carrier := {h | Integrable h (Measure.addHaar : Measure G)}
  zero_mem' := integrable_zero _ _ _
  add_mem' := Integrable.add
  smul_mem' c _ h := h.smul c

def I0 : intSub G →ₗ[ℂ] ℂ where
  toFun h := ∫ x, (h : G → ℂ) x ∂(Measure.addHaar : Measure G)
  map_add' h h' := integral_add h.2 h'.2
  map_smul' c h := integral_smul c (h : G → ℂ)

def Lext : (G → ℂ) →ₗ[ℂ] ℂ := (LinearMap.exists_extend (I0 G)).choose

variable {G}

theorem Lext_apply (h : G → ℂ) (hh : Integrable h (Measure.addHaar : Measure G)) :
    Lext G h = ∫ x, h x ∂(Measure.addHaar : Measure G) :=
  LinearMap.congr_fun (LinearMap.exists_extend (I0 G)).choose_spec ⟨h, hh⟩

theorem integrable_of_SB {f : G → ℂ} (hf : f ∈ SB G) : Integrable f (Measure.addHaar : Measure G) :=
  hf.1.continuous.integrable_of_hasCompactSupport hf.2

theorem Lext_translate {f : G → ℂ} (hf : f ∈ SB G) (a : G) :
    Lext G (fun x => f (x + a)) = Lext G f := by
  have hi := integrable_of_SB hf
  rw [Lext_apply _ (hi.comp_add_right a), Lext_apply _ hi]
  exact integral_add_right_eq_self _ _

end General

theorem exists_invariant_form (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] (K : Set G) (hKc : IsCompact K) (hKo : IsOpen K) (h0 : (0 : G) ∈ K) :
    ∃ Λ : (G → ℂ) →ₗ[ℂ] ℂ, (∀ f ∈ SB G, ∀ a, Λ (fun Y => f (Y + a)) = Λ f) ∧ ∃ f ∈ SB G, Λ f ≠ 0 := by
  haveI : LocallyCompactSpace G := hKc.locallyCompactSpace_of_mem_nhds_of_addGroup (hKo.mem_nhds h0)
  letI := measG G
  refine ⟨Lext G, fun f hf a => Lext_translate hf a, K.indicator fun _ => 1, ?_, ?_⟩
  · exact ⟨(LocallyConstant.indicator (1 : LocallyConstant G ℂ) ⟨hKc.isClosed, hKo⟩).isLocallyConstant,
      HasCompactSupport.intro hKc fun z hz => Set.indicator_of_notMem hz _⟩
  · have hi : Integrable (K.indicator fun _ => (1 : ℂ)) (Measure.addHaar : Measure G) :=
      (integrable_indicator_iff hKo.measurableSet).2 (integrableOn_const hKc.measure_lt_top.ne)
    rw [Lext_apply _ hi, integral_indicator_const _ hKo.measurableSet]
    have hpos : 0 < (Measure.addHaar : Measure G) K := hKo.measure_pos _ ⟨0, h0⟩
    have : 0 < (Measure.addHaar : Measure G).real K := ENNReal.toReal_pos hpos.ne' hKc.measure_lt_top.ne
    simpa using this.ne'

theorem exists_invariant_form_matrix : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (n d : ℕ), ∃ Λ : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), ∀ a, Λ (fun Y => f (Y + a)) = Λ f) ∧
      ∃ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), Λ f ≠ 0 := by
  intro F _ _ v n d
  set O : Set (Fv F v) := (v.adicCompletionIntegers F : Set (Fv F v))
  have hO : IsOpen O := Valued.isOpen_valuationSubring _
  have hOc : IsCompact O := PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers v
  have h0 : (0 : Fv F v) ∈ O := (v.adicCompletionIntegers F).zero_mem
  set K : Set (Matrix (Fin n) (Fin d) (Fv F v)) := Set.univ.pi fun _ => Set.univ.pi fun _ => O
  exact exists_invariant_form _ K
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc)
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hO)
    (fun _ _ _ _ => h0)

end GlobalTheory.HaarSB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctionalStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translation_invariant_functional : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (n d : ℕ), ∃ Λ : (Matrix (Fin n) (Fin d) (Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), ∀ a, Λ (fun Y => f (Y + a)) = Λ f) ∧
      ∃ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), Λ f ≠ 0 := by
  first | exact @GlobalTheory.HaarSB.exists_invariant_form_matrix | exact GlobalTheory.HaarSB.exists_invariant_form_matrix | (intros; apply GlobalTheory.HaarSB.exists_invariant_form_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemAndComm
noncomputable section

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSchComm

def lmul {R : Type} [CommRing R] {m : ℕ} (n : ℕ) (A : Matrix (Fin m) (Fin m) R) (z : Fin m → Fin n → R) :
    Fin m → Fin n → R := fun i j => ∑ c, A i c * z c j

theorem lmul_lmul {R : Type} [CommRing R] {m n : ℕ} {A B : Matrix (Fin m) (Fin m) R} (h : A * B = 1)
    (z : Fin m → Fin n → R) : lmul n A (lmul n B z) = z := by
  change (A * (B * Matrix.of z) : Matrix (Fin m) (Fin n) R) = Matrix.of z
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]

theorem continuous_lmul {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m : ℕ} (n : ℕ)
    (A : Matrix (Fin m) (Fin m) R) : Continuous (lmul n A) := by
  unfold lmul
  fun_prop

def lmulHomeo {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m : ℕ} (n : ℕ)
    {A B : Matrix (Fin m) (Fin m) R} (h : A * B = 1) : (Fin m → Fin n → R) ≃ₜ (Fin m → Fin n → R) where
  toFun := lmul n A
  invFun := lmul n B
  left_inv := lmul_lmul (mul_eq_one_comm.1 h)
  right_inv := lmul_lmul h
  continuous_toFun := continuous_lmul n A
  continuous_invFun := continuous_lmul n B

def lmulFam {T : Type} {m : ℕ} (n : ℕ) {A B : T → Matrix (Fin m) (Fin m) ℂ} (h : ∀ τ, A τ * B τ = 1) :
    (T → Fin m → Fin n → ℂ) ≃ₗ[ℝ] (T → Fin m → Fin n → ℂ) where
  toFun z τ := lmul n (A τ) (z τ)
  invFun z τ := lmul n (B τ) (z τ)
  map_add' z z' := by
    funext τ i j
    simp [lmul, mul_add, Finset.sum_add_distrib]
  map_smul' c z := by
    funext τ i j
    simp [lmul, Finset.mul_sum, mul_left_comm]
  left_inv z := funext fun τ => lmul_lmul (mul_eq_one_comm.1 (h τ)) (z τ)
  right_inv z := funext fun τ => lmul_lmul (h τ) (z τ)

theorem map_mul_entry {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {m n : ℕ} (M : Matrix (Fin m) (Fin m) R)
    (x : Matrix (Fin m) (Fin n) R) : (fun i j => φ ((M * x) i j)) = lmul n (M.map φ) fun i j => φ (x i j) := by
  funext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lmul, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply]

variable {D : D7} {n : ℕ}

theorem map_cancel {R : Type} [CommRing R] (φ : AE D →+* R) (V : HSp D) (g : GA D V) :
    (mt V g).map φ * (mt V g⁻¹).map φ = 1 := by
  have h : mt V g * mt V g⁻¹ = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_inv]
    exact Units.mul_inv _
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem comp_mem (θ : InfFam D) (V : HSp D) (h : GA D V) {Φ : Mx D V.rank n → ℂ} (hΦ : Φ ∈ schwartzA θ V.rank n) :
    (fun x : Mx D V.rank n => Φ (mt V h ⬝ x)) ∈ schwartzA θ V.rank n := by
  induction hΦ using Submodule.span_induction with
  | zero => exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
  | smul c Φ _ h1 => exact Submodule.smul_mem _ c h1
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (lmulFam n fun τ => map_cancel ((θ τ).comp (infPart D)) V h).toContinuousLinearEquiv f,
      g ∘ lmulHomeo n (map_cancel (finPart D) V h), ⟨hg.1.comp_continuous (lmulHomeo n _).continuous, hg.2.comp_homeomorph _⟩, funext fun x => ?_⟩
    have e1 := fun τ => map_mul_entry ((θ τ).comp (infPart D)) (mt V h) x
    have e2 := map_mul_entry (finPart D) (mt V h) x
    exact congrArg₂ (· * ·) (congrArg f (funext e1)) (congrArg g e2)

theorem inner_mul (V : HSp D) (h : GA D V) (x y : Mx D V.rank n) :
    StdUnn.inner V (mt V h ⬝ x) (mt V h ⬝ y) = StdUnn.inner V x y := by
  unfold StdUnn.inner
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA V), ← Matrix.mul_assoc (adj (mt V h)), mt_unitary]

def subst (θ : InfFam D) (V : HSp D) (n : ℕ) (h : GA D V) : Module.End ℂ (schwartzA θ V.rank n) where
  toFun Φ := ⟨fun x => Φ.1 (mt V h ⬝ x), comp_mem θ V h Φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem subst_mem_and_comm : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n), StdUnn.IsWeilSch ψ χ θ V μ ω → ∀ h : GA D V, (∀ Φ ∈ schwartzA θ V.rank n, (fun x : Mx D V.rank n => Φ (mt V h ⬝ x)) ∈ schwartzA θ V.rank n) ∧ ∀ (g : StdUnn.G D n) (Φ Ψ : schwartzA θ V.rank n), (∀ x, Ψ.1 x = Φ.1 (mt V h ⬝ x)) → ∀ x, (ω g Ψ).1 x = (ω g Φ).1 (mt V h ⬝ x) := by
  intro D n V ψ χ θ _ μ 𝓕 hμ ω hω h
  refine ⟨fun Φ hΦ => comp_mem θ V h hΦ, fun g Φ Ψ hΨ x => ?_⟩
  let S : Subgroup (StdUnn.G D n) :=
    { carrier := {g | Commute (ω g) (subst θ V n h)}
      one_mem' := by
        change Commute (ω 1) _
        rw [map_one]
        exact Commute.one_left _
      mul_mem' := fun {a b} ha hb => by
        change Commute (ω (a * b)) _
        rw [map_mul]
        exact Commute.mul_left ha hb
      inv_mem' := fun {a} ha => Commute.units_inv_left (u := ω.toHomUnits a) ha }
  have hS : S = ⊤ := by
    refine StdUnn.eq_top_of_levi_unip_weyl D n S (fun g a hg => ?_) (fun g b hg => ?_) (fun g hg => ?_) <;>
      refine LinearMap.ext fun Φ => Subtype.ext (funext fun x => ?_) <;>
      change (ω g (subst θ V n h Φ)).1 x = (ω g Φ).1 (mt V h ⬝ x)
    · rw [hω.levi g a hg, hω.levi g a hg, Matrix.mul_assoc]
      rfl
    · rw [hω.unip g b hg, hω.unip g b hg, inner_mul]
      rfl
    · rw [hω.weyl g hg, hω.weyl g hg, ← GlobalTheory.Twist.LeftHaar.integral_left_unitary D V n h μ hμ.1
        (fun y => Φ.1 y * ψ (StdUnn.trA (Matrix.trace (StdUnn.inner V (mt V h ⬝ x) y))))]
      refine congrArg (integral μ) (funext fun y => ?_)
      exact congrArg (fun t => Φ.1 (mt V h ⬝ y) * ψ (StdUnn.trA (Matrix.trace t))) (inner_mul V h x y).symm
  have hg : g ∈ S := hS ▸ Subgroup.mem_top g
  obtain rfl : Ψ = subst θ V n h Φ := Subtype.ext (funext hΨ)
  exact congrFun (congrArg Subtype.val (LinearMap.congr_fun (show Commute (ω g) (subst θ V n h) from hg).eq Φ)) x

end GlobalTheory.WeilSchComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverValueCore
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.CoverVal

theorem cover_value_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ c0 : ℂ, ‖c0‖ = 1 ∧ ∀ (t : Tp) (X : Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → IsSympl X bas → IdxIs O.c' (inC O.c') X idx e → latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → IsMark (O.dδ t).l₂ X.Λ mk → MarkAd (O.dδ t).l₂ (Wc D i) (rank_Wc i) (iotaW T i) k mk → letI : Algebra (O.dδ t).c₂.F ℂ := ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)).toAlgebra; ∀ (y₂ : FrPt (O.dδ t).Xo₂ (O.dδ t).c₂ ℂ) (A₂ : AnFib X bas idx e (frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.x₀ ((i : ℕ) + 1) O.s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (O.dδ t).Xo₂ (O.dδ t).c₂ (O.dδ t).cδ y₂ = c0 * ((R.xi (tup t) xk : Circle) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT i Tp tup O hO
  obtain ⟨c0, ⟨m, hm0, hm⟩, hc⟩ := hO.cxi
  refine ⟨c0, Complex.norm_eq_one_of_pow_eq_one hm hm0.ne', ?_⟩
  intro t X g bas idx e k xk mk hX hp hs hi hL hxk hmk hk y₂ A₂ hA₂
  obtain ⟨hU, hW, g', e', F', ik, φ, th, hth, hD, hval⟩ := hc t
  obtain ⟨hlev, hA, -⟩ := hO.cov t
  obtain ⟨hX₀, hon₀, -, hp₀, -, -, h1, -, hΨ₀, -⟩ := GlobalTheory.AdTh.models_at_record_core D G Pl0 T0 A T R F κ v₀ hR hT i O.s0
    (sOv_eq _ _ _) (T.dict _ O.s0 1).1
  have hσ : GoodEmb (O.dδ t).c₂ ((inC O.c').comp ((O.dδ t).eF.symm : (O.dδ t).c₂.F →+* O.c'.F)) := rfl
  have hmod : ∀ j, IsMod (Wc D i) (rank_Wc i) ((O.U₂ t).X j) := fun j =>
    isMod_of _ _ _ (hW j) fun ρ => ((hU.2.1 j).2 _).2 ((hΨ₀ _).1 ((hX₀.psi _).2 ⟨ρ, rfl⟩))
  have hor : ∀ j, IsOrthogonalFrame ((O.U₂ t).X j) (T.x₀ ((i : ℕ) + 1) O.s0) := fun j τ hτ => by
    have hsp := sameSp_of (hmod j) hX₀ ((hU.2.1 j).1.trans hp₀.symm)
    rw [hsp.gm, hsp.p0]
    exact hon₀ ⟨τ, hsp.psi ▸ hτ⟩
  obtain ⟨Wt⟩ := nonempty_uw ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU)
  obtain ⟨hon, γ, ⟨hγ, hl, hf⟩, hma, -⟩ := GlobalTheory.AdTh.dict_atComp_markAd D _ _ _ _ _ _ _ (O.U₂ t) hσ hU h1 hA R.θ (Wc D i) (rank_Wc i)
    (O.dict₂ t) (iotaW T i) g' e' F' ik φ th _ hR.models.inf hmod hor hth hD Wt k
  obtain ⟨hd, hpt⟩ := point_eq (Formalism.L2.PjFree.Unf.ofPj (O.U₂ t)) hσ hU h1 hA hR.models.inf (Wc D i) (rank_Wc i) (iotaW T i)
    _ Wt (O.dict₂ t k).1 (O.dict₂ t k).2 γ k hγ (hmod _) hl hf hon hma X g bas idx e mk hX hp hs hi hL hmk hk y₂ A₂ hA₂
  obtain ⟨γ', hγ', h2, h3, -⟩ := hD.2 k
  obtain ⟨-, -, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D (Wc D i)
  obtain ⟨a, ha⟩ := hrat γ' hγ'
  have hv := hval k γ' ⟨hγ', h2, h3⟩
  rw [(hO.tuple t).xi _ _ (hmul _ _ _ _ ha hxk), map_mul, (hR.lev.xi (tup t)).1.2 a, _root_.one_mul] at hv
  exact (evR_eq_of_point _ hlev.2.2.2.2.2.2.2.1 _ y₂ hpt).trans ((dif_pos hd).symm.trans hv)

end GlobalTheory.AdTh.CoverVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharDotMulMemAdelicSchwartzSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharDotMulMemAdelicSchwartzSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CharMulSchA

theorem charMul_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ b : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    (fun x => ψ (x ⬝ᵥ b) * Φ x) ∈ GlobalTheory.WeilM.schA F κ := by
  intro F _ _ κ _ ψ hψ b Φ hΦ
  have h := GlobalTheory.SchrKeepsSchA.schr_mem_schA F ψ hψ κ (0, b) Φ hΦ
  convert h using 1
  funext x
  simp [GlobalTheory.WeilM.schr]

end GlobalTheory.CharMulSchA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharDotMulMemAdelicSchwartzSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addCharDotMul_mem_adelicSchwartzSpace : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ b : κ → AF F, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    (fun x => ψ (x ⬝ᵥ b) * Φ x) ∈ GlobalTheory.WeilM.schA F κ := by
  first | exact @GlobalTheory.CharMulSchA.charMul_mem_schA | exact GlobalTheory.CharMulSchA.charMul_mem_schA | (intros; apply GlobalTheory.CharMulSchA.charMul_mem_schA <;> assumption)
end
end
