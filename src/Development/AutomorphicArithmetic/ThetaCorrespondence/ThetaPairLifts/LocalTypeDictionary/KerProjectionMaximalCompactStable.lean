module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AlgDAndPreimageStableUnderKInf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift
namespace GlobalTheory.KStableSums
open scoped Classical in
theorem kStable_subspace_sums : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) {r s r' s' : ℕ},
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ {Pi : Type} [AddCommGroup Pi] [Module ℂ Pi] (Q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] Pi) (N : Submodule ℂ Pi),
    (∀ (w : InfinitePlace F) (Z : Matrix (Fin d) (Fin d) ℂ) (γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W →
      (∀ t : ℝ, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w)) =
        NormedSpace.exp (t • Z)) →
      (∀ (t : ℝ) (w' : InfinitePlace F), w' ≠ w →
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w')) = 1) →
      ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
      (∀ i, f i ∈ M.Pol B.ψ B.emb ∧ f₁ i ∈ M.Pol B.ψ B.emb) →
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
      Q (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ N → Q (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) ∈ N) →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb, ∀ Ψ ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb,
      om (1, k) Ψ ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb ∧ (Q Ψ ∈ N → Q (om (1, k) Ψ) ∈ N) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hb hX hW hM hw Pv _ _ Q N hlie k hk Ψ hΨ
  have hAL : ActsLaws := GlobalTheory.RealLift.actsLaws
  have hfr : FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl : VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  have hfe : FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hls : LieScalar := _root_.GlobalTheory.T.weil_lie_algebra_scalar_action hP hder hvl
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws hAL hder hvl
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.PolCompact.incM_map_piInf', one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.PolCompact.incM_map_piInf']; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hw
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _ hb.cm hb.std fr hΦ hwp.1.1
  have hadm := fun g => (hwp.isUSplitting).adm g
  obtain ⟨γ, hγ, Yg, hgen, hYu, hKC, hγ1⟩ :=
    exists_line_upq σ r' s' B.emb (incM F W.J) Complex.I C W.θ hb.cm hC1 hCθ k hk.1 hk.2
  have hloc := GlobalTheory.RealLift.locFin_sumPl _ _ _
    (fun w => GlobalTheory.PolCompact.locFin_second r s r' s' (Yg w) (hKC w) (c w * (Yg w).trace))
  obtain ⟨U, hU, hSA⟩ := GlobalTheory.T.weakExponential_action_on_fockVectors F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  obtain ⟨m, f, φ, hf, hφ, rfl⟩ := exists_sum_pure M B.ψ B.emb hΨ
  have hf' : ∀ i, ∃ y, Φ y = f i := fun i => LinearMap.mem_range.1 (by rw [hr]; exact hf i)
  choose T hT using hf'
  obtain rfl : f = fun i => Φ (T i) := funext fun i => (hT i).symm
  let G : (Fin m → Tens F r s r' s') →ₗ[ℂ] ((Fin n × Fin d → AF F) → ℂ) :=
    ∑ i, (pureL (φ i)) ∘ₗ Φ ∘ₗ LinearMap.proj i
  have hG : ∀ y, G y = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ (y i)) (φ i) := fun y => by
    simp only [G, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]; rfl
  have hplace : ∀ (w : InfinitePlace F) (y : Fin m → Tens F r s r' s'), Q (G y) ∈ N →
      Q (G (piEnd m (atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol r s r' s') w
        (fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1)) y)) ∈ N := by
    intro w y hy
    rw [hG] at hy ⊢
    obtain ⟨A', hCA, hAC⟩ := GlobalTheory.RealLift.KLineProof.frame_inv (hC1 w)
    have hsu : ∀ w', (Pi.single w (Yg w) : InfinitePlace F → Matrix (Ix r' s') (Ix r' s') ℂ) w' ∈ upq r' s' := by
      intro w'
      by_cases h : w' = w
      · subst h; simpa using hYu w'
      · rw [Pi.single_eq_of_ne h]
        show (0 : Matrix (Ix r' s') (Ix r' s') ℂ)ᴴ * Jm r' s' + Jm r' s' * 0 = 0
        simp
    obtain ⟨γw, hγw, hgw⟩ := GlobalTheory.T.unitaryLieElements_generate_oneParamLines F E σ (Fin d) r' s' B.emb (incM F W.J) Complex.I C hb.cm hC1 _ hsu
    refine hlie w (C w * Yg w * A') γw hγw ?_ ?_ m (fun i => Φ (y i)) _ φ hφ
      (fun i => ⟨by rw [← hr]; exact LinearMap.mem_range_self Φ _, by rw [← hr]; exact LinearMap.mem_range_self Φ _⟩)
      ?_ hy
    · intro t
      have h1 := hgw t w
      simp only [Pi.single_eq_same] at h1
      calc (mat (γw (Multiplicative.ofAdd t))).map (piInf (B.emb w))
          = ((γw (Multiplicative.ofAdd t)).1 : Matrix (Fin d) (Fin d) (AE F E)).map (piInf (B.emb w)) * C w * A' := by
            rw [Matrix.mul_assoc, hCA, Matrix.mul_one]; rfl
        _ = C w * NormedSpace.exp (t • Yg w) * A' := by rw [h1]
        _ = NormedSpace.exp (t • (C w * Yg w * A')) := by
            rw [show t • (C w * Yg w * A') = C w * (t • Yg w) * A' by rw [Matrix.mul_smul, Matrix.smul_mul],
              exp_conj_rect _ _ hCA hAC]
    · intro t w' hw'
      have h1 := hgw t w'
      rw [Pi.single_eq_of_ne hw', smul_zero, NormedSpace.exp_zero, Matrix.mul_one] at h1
      obtain ⟨A'', hCA', -⟩ := GlobalTheory.RealLift.KLineProof.frame_inv (hC1 w')
      calc (mat (γw (Multiplicative.ofAdd t))).map (piInf (B.emb w'))
          = ((γw (Multiplicative.ofAdd t)).1 : Matrix (Fin d) (Fin d) (AE F E)).map (piInf (B.emb w')) * C w' * A'' := by
            rw [Matrix.mul_assoc, hCA', Matrix.mul_one]; rfl
        _ = 1 := by rw [h1, hCA']
    · intro i
      have hsd := hact γw hγw _ hgw (y i)
      rw [sumPl_single] at hsd
      exact (hAL F (Fin n × Fin d) _ _ (Φ (y i))).1 _ (fun t => map_zero _) hsd
  let N' : Submodule ℂ (Fin m → Tens F r s r' s') := N.comap (Q ∘ₗ G)
  have hstab : ∀ y ∈ N', piEnd m (sumPl fun w => fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1) y ∈ N' := by
    intro y hy
    have e : piEnd m (sumPl fun w => fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1) y =
        ∑ w, piEnd m (atPl (V := fun _ : InfinitePlace F => Formalism.BasicNotions.TH.Pol r s r' s') w
          (fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1)) y := by
      funext i
      simp only [piEnd_apply, sumPl, LinearMap.sum_apply, Finset.sum_apply]
    rw [e]
    exact N'.sum_mem fun w _ => hplace w y hy
  have hk1 : ∀ i, om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ (T i)) (φ i)) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ (U (T i))) (φ i) := by
    intro i
    have h1 := hSA (T i)
    change SA (om (1, γ (Multiplicative.ofAdd 1))) (Φ (T i)) (Φ (U (T i))) at h1
    rw [hγ1] at h1
    have hg := GlobalTheory.AdelicCoordSB.finprod_mem_SB F (Fin n × Fin d) (φ i) (hφ i).1
      (((hφ i).2.and hM.std).mono fun v hv => hv.1.trans hv.2)
    exact h1 _ hg
  have hsum : om (1, k) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ (T i)) (φ i)) =
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ (U (T i))) (φ i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hk1 i
  refine ⟨?_, fun hQ => ?_⟩
  · rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span
      ⟨Φ (U (T i)), φ i, by rw [← hr]; exact LinearMap.mem_range_self Φ _, (hφ i).1, (hφ i).2, rfl⟩
  · have h0 : T ∈ N' := by
      show Q (G T) ∈ N
      rw [hG]; exact hQ
    have h2 := GlobalTheory.KStableLie.mem_of_isExp (isExp_piEnd hU m) N' hstab h0
    have e := hG (piEnd m U T)
    simp only [piEnd_apply] at e
    rw [hsum, ← e]
    exact h2
end GlobalTheory.KStableSums
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algD_and_preimage_stable_under_KInf : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) {r s r' s' : ℕ},
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ {Pi : Type} [AddCommGroup Pi] [Module ℂ Pi] (Q : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] Pi) (N : Submodule ℂ Pi),
    (∀ (w : InfinitePlace F) (Z : Matrix (Fin d) (Fin d) ℂ) (γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J),
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W →
      (∀ t : ℝ, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w)) =
        NormedSpace.exp (t • Z)) →
      (∀ (t : ℝ) (w' : InfinitePlace F), w' ≠ w →
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (B.emb w')) = 1) →
      ∀ (m : ℕ) (f f₁ : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ),
      (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = M.vac v) →
      (∀ i, f i ∈ M.Pol B.ψ B.emb ∧ f₁ i ∈ M.Pol B.ψ B.emb) →
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
      Q (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ N → Q (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) ∈ N) →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb, ∀ Ψ ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb,
      om (1, k) Ψ ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb ∧ (Q Ψ ∈ N → Q (om (1, k) Ψ) ∈ N) := by
  first | exact @_root_.GlobalTheory.KStableSums.kStable_subspace_sums | exact _root_.GlobalTheory.KStableSums.kStable_subspace_sums | (intros; apply _root_.GlobalTheory.KStableSums.kStable_subspace_sums <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
namespace GlobalTheory.SquareAgree.KerCptW
theorem ker_projection_maximalCompact_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ Φ₁,
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA (om (1, k) ΦD) Φ₁ → p Φ = 0 → p Φ₁ = 0 := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _ hO hTr Pi rf rl p p' hm k hk ΦD hΦD Φ Φ₁
    hD hD1 hp
  have hψ := hO.psi
  subst hψ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd Bs.ψ := hTr.base.std
  let Fn : ((Fin W.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) → WO W X → ℂ :=
    fun Ψ z => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ (cA.symm z) Ψ)
  have hFn : ∀ Ψ f, IsDatum Γ.M Bs.ψ cA Ψ f → f = Fn Ψ := by
    intro Ψ f h
    funext z
    have h1 := h.2 (cA.symm z)
    rw [AddEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hex : ∀ Ψ ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M Bs.ψ cA Ψ (Fn Ψ) ∧ Fn Ψ ∈ algF Bs.ψ θ true A B := by
    intro Ψ hΨ
    obtain ⟨f, hf, hd⟩ := hO.algA' Ψ hΨ
    obtain rfl := hFn _ _ hd
    exact ⟨hd, hf⟩
  let q₀ : (algD Γ.M Bs.ψ Bs.emb) →ₗ[ℂ] Pi :=
    { toFun := fun Ψ => p (Fn Ψ.1)
      map_add' := fun Ψ₁ Ψ₂ => by
        have h := CoinvPass.isDatum_add hstd (hex _ Ψ₁.2).1 (hex _ Ψ₂.2).1
        show p (Fn (Ψ₁.1 + Ψ₂.1)) = _
        rw [← hFn _ _ h, map_add (f := _)]
      map_smul' := fun c Ψ => by
        have h := CoinvPass.isDatum_smul c (hex _ Ψ.2).1
        show p (Fn (c • Ψ.1)) = _
        rw [← hFn _ _ h, map_smul]
        rfl }
  obtain ⟨Q, hQ⟩ := q₀.exists_extend
  have hQv : ∀ Ψ (h : Ψ ∈ algD Γ.M Bs.ψ Bs.emb), Q Ψ = p (Fn Ψ) := fun Ψ h => LinearMap.congr_fun hQ ⟨Ψ, h⟩
  have key := _root_.GlobalTheory.T.algD_and_preimage_stable_under_KInf hP Bs Γ.M Xc.β (Xc.β / Xc.α) om hTr.base hTr.geo.hV hTr.geo.hW hTr.geo.hM hTr.weil Q ⊥ ?hyp k hk ΦD hΦD
  · obtain ⟨hmem, hker⟩ := key
    have h0 : Q ΦD ∈ (⊥ : Submodule ℂ Pi) := by
      rw [Submodule.mem_bot, hQv _ hΦD, ← hFn _ _ hD, hp]
    have h2 := hker h0
    rw [Submodule.mem_bot, hQv _ hmem, ← hFn _ _ hD1] at h2
    exact h2
  case hyp =>
    intro w Z γ hγ hw hw' m f f₁ φ hφ hf hact hN
    have hmemS : ∀ g : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F _, (∀ i, g i ∈ Γ.M.Pol Bs.ψ Bs.emb) →
        ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (φ i) ∈ algD Γ.M Bs.ψ Bs.emb := fun g hg =>
      Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨g i, φ i, hg i, (hφ i).1, (hφ i).2, rfl⟩
    have hΨ := hmemS f fun i => (hf i).1
    have hΨ' := hmemS f₁ fun i => (hf i).2
    obtain ⟨τ, Y, hY, hγY⟩ := GlobalTheory.T.exists_lieGenerator_of_oneParameterSubgroup_realPlace D θ X hθ e Γ.W hO.JX Bs.emb w Z γ hγ hw hw'
    have hder : IsDer θ X (fun h => ωA (1, h)) τ Y (Fn (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))
        (Fn (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i))) := by
      intro z
      have hd := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP Γ.M Bs.ψ _ _ om hTr.base.cm hstd hTr.geo.hM hTr.weil γ hγ m f f₁ φ hφ hact (cA.symm z)
      refine hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      have hw1 := hO.weilA _ _ (hex _ hΨ).1 1 (oneP θ X τ Y t)
      rw [GlobalTheory.LocWeilAct.conjU_one' W 1 hO.JW, ← hγY t] at hw1
      have := hFn _ _ hw1
      show ωA (1, oneP θ X τ Y t) (Fn _) z = _
      rw [this]
    have hpe := hm.mapA.eql τ Y hY _ (hex _ hΨ).2 _ (hex _ hΨ').2 hder
    rw [Submodule.mem_bot] at hN ⊢
    rw [hQv _ hΨ'] at ⊢
    rw [hQv _ hΨ] at hN
    rw [hpe, hN, map_zero]
end GlobalTheory.SquareAgree.KerCptW
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_agree_kernel_compact_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ Φ₁,
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA (om (1, k) ΦD) Φ₁ → p Φ = 0 → p Φ₁ = 0 := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerCptW.ker_projection_maximalCompact_stable | exact _root_.GlobalTheory.SquareAgree.KerCptW.ker_projection_maximalCompact_stable | (intros; apply _root_.GlobalTheory.SquareAgree.KerCptW.ker_projection_maximalCompact_stable <;> assumption)
end
