module

public import Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseMain
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemPolarizationStabilizerOfDualPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.HoweDualityUnramifiedAllPlaces

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DvReBaseReal
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace GlobalTheory.ReBase
section First
open scoped Matrix Classical
open Formalism.BasicNotions.TH
open GlobalTheory.RealLift GlobalTheory.RealLift.LieFirstPf GlobalTheory.RealLift.FirstLine
theorem exists_rebase_splitting_datum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ : SInf F (Fin n × Fin d),
      GlobalTheory.RealLift.SD (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil γ hγ f hf
  choose A hA hAθ using fun w => frameEx_holds _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => frameEx_holds _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf', one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf']; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have fr' : Framed B.emb (incM F W.J) (incM F X.J) Complex.I 1 C A := ⟨mul_one _, hC1, hA1⟩
  have hvl := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives GlobalTheory.T.archHeisenbergDerivatives_exist
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hB.cm hB.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws actsLaws GlobalTheory.T.archHeisenbergDerivatives_exist hvl F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hB.cm hB.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hWeil
  obtain ⟨d', hdd, hB1'⟩ := hwp.2.1
  have hΦ' := fockMap_swap hΦ hdd
  obtain ⟨c, hact⟩ := _root_.GlobalTheory.T.weil_lie_algebra_scalar_action hKP GlobalTheory.T.archHeisenbergDerivatives_exist hvl F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ d' Complex.I 1 C A _
    (om.comp (MonoidHom.inl _ _)) hB.cm hB.std fr' hΦ' hB1'.1
  obtain ⟨Y, -, hY⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin n) r s B.emb (incM F X.J) 1 A hB.cm hA1 γ hγ
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  have hT : Φ T = (Φ ∘ₗ (swapT (InfinitePlace F) r s r' s').toLinearMap) ((swapT (InfinitePlace F) r s r' s').symm T) := by
    simp
  have key := hact γ hγ Y hY ((swapT (InfinitePlace F) r s r' s').symm T)
  rw [← hT] at key
  exact ⟨_, key⟩
end First
theorem deriv_conjugate_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
      ActsD (evI F) (fun t => om (g * γ (Multiplicative.ofAdd t) * g⁻¹, 1)) (T f) (T f₁) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil g hg h hh T hT hTi γ hγ f hf f₁ hf₁
  obtain ⟨f₂, hsd⟩ := _root_.GlobalTheory.ReBase.exists_rebase_splitting_datum hKP F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hWeil γ hγ f hf
  have e := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₂ f₁).2.2.1 _
    ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f f₂ f₁).1 _ (fun t => map_zero _) hsd) hf₁
  subst e
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hWeil
  refine (GlobalTheory.RealLift.actsLaws F _ (T f) (T f₂) (T f₂)).1 _ (fun t => map_zero _) ?_
  intro g' hg' l hl
  have key : ∀ φ : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) φ (T φ) →
      om (g, h) (GlobalTheory.WeilM.pureA F φ g') = GlobalTheory.WeilM.pureA F (T φ) g' := by
    intro φ hφ
    have hr : ∀ x z, At (evI F) z → (fun x : Fin n × Fin d → AF F => g' (fun i => (x i).2)) (x + z) =
        (fun x : Fin n × Fin d → AF F => g' (fun i => (x i).2)) x := by
      intro x z hz
      change g' (fun i => (x i + z i).2) = g' (fun i => (x i).2)
      congr 1
      funext i
      change (x i).2 + (z i).2 = (x i).2
      rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
    exact hφ _ ⟨hr, Submodule.subset_span ⟨φ, g', hg', rfl⟩⟩
  have hfun : (fun t : ℝ => l (om (g * γ (Multiplicative.ofAdd t) * g⁻¹, 1) (GlobalTheory.WeilM.pureA F (T f) g'))) =
      fun t => (l ∘ₗ om (g, h)) (om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.WeilM.pureA F f g')) := by
    funext t
    rw [← key f (hT f), LinearMap.comp_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 3
    exact Prod.ext (by simp only [Prod.fst_mul, inv_mul_cancel_right]) (by simp)
  rw [hfun, ← key f₂ (hT f₂)]
  exact hsd g' hg' _ (hS.adm (g, h) l hl)
section Second
open GlobalTheory.RealLift
theorem conjugation_acts_on_derivation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
      ActsD (evI F) (fun t => om (1, h * γ (Multiplicative.ofAdd t) * h⁻¹)) (T f) (T f₁) := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hb hX hW _hM hw g _hg h _hh T hT hTs γ hγ f hf f₁ hf₁
  have hder := GlobalTheory.RealLift.Main.i_derex
  have hvl := GlobalTheory.RealLift.Main.i_vacline hder
  have hfe := GlobalTheory.RealLift.Main.i_fockex hder
  choose A hA hAθ using fun w => GlobalTheory.RealLift.Main.i_frameex _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.RealLift.Main.i_frameex _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.RealLift.Main.incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.RealLift.Main.incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.RealLift.Main.i_polrange GlobalTheory.RealLift.actsLaws hder hvl F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm
    hb.std fr hAθ hCθ hΦ
  have hsp : IsUSplitting (adeleClass F) B.ψ M.co (actAB (cA σ)) om := IsUWeilPair.isUSplitting hw
  have hsp2 := GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.RealLift.Main.i_liescalar_alt hK hder hvl F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _
    hb.cm hb.std fr hΦ hsp2
  obtain ⟨Yg, -, hY⟩ := GlobalTheory.RealLift.Main.i_genex F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C hb.cm hC1 γ hγ
  obtain ⟨T0, rfl⟩ := GlobalTheory.RealLift.Main.pol_eq B M Φ hr hf
  obtain ⟨D, hSD⟩ : ∃ D, SD (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T0) D := ⟨_, hc γ hγ Yg hY T0⟩
  have hAD : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T0) D :=
    (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T0) D D).1 _ (fun t => map_zero _) hSD
  have e0 : f₁ = D := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T0) f₁ D).2.2.1 _ hf₁ hAD
  subst e0
  have hSD2 : SD (fun t => om (1, h * γ (Multiplicative.ofAdd t) * h⁻¹)) (T (Φ T0)) (T f₁) := by
    intro g' hg' l hl
    have hl' : l ∘ₗ om (g, h) ∈ (adeleClass F).adm (Fin n × Fin d) := hsp.adm (g, h) l hl
    have hrest : ∀ f0 : SInf F (Fin n × Fin d), Rest (evI F) (⇑f0) (fun x => g' fun i => (x i).2) := fun f0 =>
      ⟨fun x z hz => by
        show g' (fun i => (x i + z i).2) = g' (fun i => (x i).2)
        congr 1
        funext i
        show (x i).2 + (z i).2 = (x i).2
        rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz i, add_zero], Submodule.subset_span ⟨f0, g', hg', rfl⟩⟩
    have hpure : ∀ f0 : SInf F (Fin n × Fin d), pureA F (⇑f0) g' = tens (evI F) (⇑f0) (fun x => g' fun i => (x i).2) :=
      fun _ => rfl
    have e1 : om (g⁻¹, h⁻¹) (pureA F (⇑(T (Φ T0))) g') = pureA F (⇑(Φ T0)) g' := by
      rw [hpure, hTs _ _ (hrest _), LinearEquiv.symm_apply_apply]
      rfl
    have e2 : om (g, h) (pureA F (⇑f₁) g') = pureA F (⇑(T f₁)) g' := by
      rw [hpure, hT _ _ (hrest _)]
      rfl
    have e3 : ∀ t : ℝ, om (1, h * γ (Multiplicative.ofAdd t) * h⁻¹) (pureA F (⇑(T (Φ T0))) g') =
        om (g, h) (om (1, γ (Multiplicative.ofAdd t)) (pureA F (⇑(Φ T0)) g')) := by
      intro t
      have hp : ((1 : UA σ X.J), h * γ (Multiplicative.ofAdd t) * h⁻¹) = (g, h) * (1, γ (Multiplicative.ofAdd t)) * (g⁻¹, h⁻¹) :=
        Prod.ext (by simp) (by simp)
      rw [hp, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e1]
    simp only [e3]
    have := hSD g' hg' _ hl'
    simpa only [LinearMap.comp_apply, e2] using this
  exact (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (T (Φ T0)) (T f₁) (T f₁)).1 _ (fun t => map_zero _) hSD2
end Second
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Pair
open GlobalTheory.MajTransport
variable {n d : ℕ} {X Y : Spc F E n} {W Z : Spc F E d}
theorem pair_quotient_projection (hKP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ}
    (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ)
    (hw : M.IsWeil B.ψ χX χW om) {g : UA σ X.J} {h : UA σ W.J} (hg : g ∈ UAt σ X (evI F))
    (hh : h ∈ UAt σ W (evI F)) {T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d)}
    (hT1 : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f))
    (hT2 : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f))
    (hθX : ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)))
    (hθW : ∀ w, (mat h).map (piInf (B.emb w)) * W.θ w = Z.θ w * (mat h).map (piInf (B.emb w)))
    {P : Type} [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    (hq : RealQuot B (reM M Y Z) om p) :
    RealQuot B M om (p ∘ₗ (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))) := by
  have hpol := pair_pol hB hX hW hM hw hg hh hT1 hT2 hθX hθW
  have memT : ∀ f ∈ M.Pol B.ψ B.emb, T f ∈ (reM M Y Z).Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d))) hf
    rw [hpol] at this; exact this
  refine ⟨?_, fun γ hγ f hf f₁ hD => ?_, fun k hk f hf f₁ hA => ?_⟩
  · rw [Submodule.map_comp, hpol]; exact hq.onto
  · exact hq.lie _ (lines_conj hσ hγ hg) (T f) (memT f hf) (T f₁)
      (_root_.GlobalTheory.ReBase.deriv_conjugate_line hKP F E σ B n d X W M χX χW om r s r' s' hB hX hW hM hw g hg h hh T hT1 hT2 γ hγ f hf f₁ hD)
  · have hA' := acts_conj (pres_of hw) hT1 hT2 hA
    have e : ((g, h) * (k, 1) * (g, h)⁻¹ : UA σ X.J × UA σ W.J) = (g * k * g⁻¹, 1) := Prod.ext rfl (by simp)
    rw [e] at hA'
    exact hq.cpt (g * k * g⁻¹) (kinf_conj B.emb hg hθX hk) (T f) (memT f hf) (T f₁) hA'
end Pair
open GlobalTheory.MajTransport in
theorem real_maps_transport (hKP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') {V : Spc F E a} {V' : Spc F E a'} {W : Spc F E (a + a')} (R₂ : RealMaps F a a')
    {g : UA σ G.V.J} (hg : g ∈ UAt σ G.V (evI F)) {g' : UA σ G.V'.J} (hg' : g' ∈ UAt σ G.V' (evI F))
    {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evI F))
    (hθ : ∀ w, (mat g).map (piInf (B.emb w)) * G.V.θ w = V.θ w * (mat g).map (piInf (B.emb w)))
    (hθ' : ∀ w, (mat g').map (piInf (B.emb w)) * G.V'.θ w = V'.θ w * (mat g').map (piInf (B.emb w)))
    (hθW : ∀ w, (mat h).map (piInf (B.emb w)) * G.W.θ w = W.θ w * (mat h).map (piInf (B.emb w)))
    {T : SInf F (Fin a × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a × Fin (a + a'))}
    {T' : SInf F (Fin a' × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a' × Fin (a + a'))}
    (hT1 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g, h)) f (T f))
    (hT2 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f))
    (hT1' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g', h)) f (T' f))
    (hT2' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g'⁻¹, h⁻¹)) f (T'.symm f))
    (hT₂ : IsTriple B (reG G V V' W) X om om') (hR₂ : IsRealMaps B (reG G V V' W) om om' R₂) :
    IsRealMaps B G om om' (reR R₂ T T') := by
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hT.base.cm
  have hT1s : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g⁻¹⁻¹, h⁻¹⁻¹)) f (T.symm.symm f) :=
    fun f => by simpa only [inv_inv, LinearEquiv.symm_symm] using hT1 f
  have hpol := pair_pol (Y := V) (Z := W) hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hg hh hT1 hT2 hθ hθW
  have hpol' := pair_pol (Y := V') (Z := W) hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' hg' hh hT1' hT2' hθ' hθW
  have memT : ∀ f ∈ G.M.Pol B.ψ B.emb, T f ∈ (reG G V V' W).M.Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')))) hf
    rw [hpol] at this; exact this
  have memT' : ∀ f ∈ G.M'.Pol B.ψ B.emb, T' f ∈ (reG G V V' W).M'.Pol B.ψ B.emb := fun f hf => by
    have := Submodule.mem_map_of_mem (f := (T' : SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')))) hf
    rw [hpol'] at this; exact this
  have memTs : ∀ f' ∈ (reG G V V' W).M.Pol B.ψ B.emb, T.symm f' ∈ G.M.Pol B.ψ B.emb := fun f' hf' => by
    have hf'' : f' ∈ (G.M.Pol B.ψ B.emb).map (T : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a'))) := by
      rw [hpol]; exact hf'
    obtain ⟨f, hf, rfl⟩ := hf''
    simpa using hf
  have hW' : ∀ w, (mat h⁻¹).map (piInf (B.emb w)) * W.θ w = G.W.θ w * (mat h⁻¹).map (piInf (B.emb w)) :=
    fun w => rev_conj (map_mul_inv _ h) (map_inv_mul _ h) (hθW w)
  refine ⟨?_, ?_, ?_, ?_, hR₂.nontriv, ?_⟩
  · exact _root_.GlobalTheory.ReBase.pair_quotient_projection (Y := V) (Z := W) hKP hσ hT.base hT.geo.hV hT.geo.hW hT.geo.hM hT.weil hg hh hT1 hT2 hθ hθW
      R₂.p hR₂.quot
  · exact _root_.GlobalTheory.ReBase.pair_quotient_projection (Y := V') (Z := W) hKP hσ hT.base hT.geo.hV' hT.geo.hW hT.geo.hM' hT.weil' hg' hh hT1' hT2' hθ'
      hθW R₂.p' hR₂.quot'
  · intro γ hγ f hf f' hf' f₁ f₁' hD hD' hpp
    exact hR₂.lie _ (lines_conj hσ hγ hh) (T f) (memT f hf) (T' f') (memT' f' hf') (T f₁) (T' f₁')
      (_root_.GlobalTheory.ReBase.conjugation_acts_on_derivation hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hT.base hT.geo.hV hT.geo.hW hT.geo.hM
        hT.weil g hg h hh T hT1 hT2 γ hγ f hf f₁ hD)
      (_root_.GlobalTheory.ReBase.conjugation_acts_on_derivation hKP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hT.base hT.geo.hV' hT.geo.hW
        hT.geo.hM' hT.weil' g' hg' h hh T' hT1' hT2' γ hγ f' hf' f₁' hD') hpp
  · intro k hk f hf f' hf' f₁ f₁' hA hA' hpp
    have e : ((g, h) * (1, k) * (g, h)⁻¹ : UA σ G.V.J × UA σ G.W.J) = (1, h * k * h⁻¹) := Prod.ext (by simp) rfl
    have e' : ((g', h) * (1, k) * (g', h)⁻¹ : UA σ G.V'.J × UA σ G.W.J) = (1, h * k * h⁻¹) := Prod.ext (by simp) rfl
    have hB := acts_conj (pres_of hT.weil) hT1 hT2 hA
    have hB' := acts_conj (pres_of hT.weil') hT1' hT2' hA'
    rw [e] at hB
    rw [e'] at hB'
    exact hR₂.cpt (h * k * h⁻¹) (kinf_conj B.emb hh hθW hk) (T f) (memT f hf) (T' f') (memT' f' hf') (T f₁) (T' f₁')
      hB hB' hpp
  · intro N hL hK
    refine hR₂.irred N (fun γ' hγ' f' hf' f₁' hD hN => ?_) (fun k' hk' f' hf' f₁' hA hN => ?_)
    · have hD' := _root_.GlobalTheory.ReBase.conjugation_acts_on_derivation hKP F E σ B a (a + a') (reS G.V V) (reS G.W W) (reG G V V' W).M X.β (X.β / X.α) om _ _ _ _
        hT₂.base hT₂.geo.hV hT₂.geo.hW hT₂.geo.hM hT₂.weil g⁻¹ (uat_inv hg) h⁻¹ (uat_inv hh) T.symm hT2 hT1s γ' hγ'
        f' hf' f₁' hD
      have hN' : R₂.p (T (T.symm f')) ∈ N := by rwa [LinearEquiv.apply_symm_apply]
      have := hL _ (lines_conj hσ hγ' (uat_inv hh)) (T.symm f') (memTs f' hf') (T.symm f₁') hD' hN'
      have this' : R₂.p (T (T.symm f₁')) ∈ N := this
      rwa [LinearEquiv.apply_symm_apply] at this'
    · have hB := acts_conj (pres_of hT.weil) hT2 hT1s hA
      have hB' : Acts (evI F) (om (1, h⁻¹ * (id k' : UA σ G.W.J) * h⁻¹⁻¹)) (T.symm f') (T.symm f₁') := by
        convert hB using 3
        exact Prod.ext (by show (1 : UA σ G.V.J) = g⁻¹ * 1 * g⁻¹⁻¹; simp) rfl
      have hN' : R₂.p (T (T.symm f')) ∈ N := by rwa [LinearEquiv.apply_symm_apply]
      have := hK _ (kinf_conj (X := reS G.W W) (Y := G.W) B.emb (uat_inv hh) hW' hk') (T.symm f') (memTs f' hf')
        (T.symm f₁') hB' hN'
      have this' : R₂.p (T (T.symm f₁')) ∈ N := this
      rwa [LinearEquiv.apply_symm_apply] at this'
end GlobalTheory.ReBase
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DvReBaseUniq
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace GlobalTheory.ReBase
section Real
open scoped Matrix
open GlobalTheory.RealActs GlobalTheory.ThK.RealUniq
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
theorem howe_supremum_projection (hKP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {n d r s r' s' : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χY χW : Chr F E}
    {o : Rep σ Y W} (h : IsPair B M χY χW o r s r' s') :
    ∀ N N', GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o N → GlobalTheory.Published.ThetaSubInf M B.ψ B.emb o N' → N ≠ M.Pol B.ψ B.emb →
      N' ≠ M.Pol B.ψ B.emb → N ⊔ N' ≠ M.Pol B.ψ B.emb := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hY : Y.J.det ≠ 0 := fun h0 => det_ne_zero_of_sig (h.herm.sig w) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
  have hW : W.J.det ≠ 0 := fun h0 => det_ne_zero_of_sig (h.skew.sig w) (by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero])
  exact (hKP.howeDualityReal F E σ h.base.cm n d Y W M B.ψ χY χW o h.base.std h.herm.herm hY h.skew.skew hW h.resX h.resW
    h.hX h.hW h.weil B.emb h.herm.cartan h.skew.cartan).2
theorem real_maps_unique : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ R₃ : RealMaps F a a', IsRealMaps B G om om' R₃ → ∃ (ψ : R.Pi ≃ₗ[ℂ] R₃.Pi) (l : ℂ), l ≠ 0 ∧
      (∀ f ∈ G.M.Pol B.ψ B.emb, R₃.p f = ψ (R.p f)) ∧ ∀ f ∈ G.M'.Pol B.ψ B.emb, R₃.p' f = l • ψ (R.p' f) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM R₃ hR₃
  have hR := hM.real
  have hPV := isPair_V hM.triple
  have hPV' := isPair_V' hM.triple
  have actV := _root_.GlobalTheory.T.dualPair_preserves_polarization hKP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV
  have actV' := _root_.GlobalTheory.T.dualPair_preserves_polarization hKP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV'
  have ks_p : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → KerStab B G.M om R'.p := fun R' h =>
    ⟨fun γ hγ f hf f₁ h1 h0 => by
      have := h.lie γ hγ f hf 0 (zero_mem _) f₁ 0 h1 (actsD_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this,
     fun k hk f hf f₁ h1 h0 => by
      have := h.cpt k hk f hf 0 (zero_mem _) f₁ 0 h1 (acts_zero _) (by rw [h0, map_zero])
      rwa [map_zero] at this⟩
  have ks_p' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → KerStab B G.M' om' R'.p' := fun R' h =>
    ⟨fun γ hγ f hf f₁ h1 h0 => by
      have := h.lie γ hγ 0 (zero_mem _) f hf 0 f₁ (actsD_zero _) h1 (by rw [h0, map_zero])
      rw [map_zero] at this; exact this.symm,
     fun k hk f hf f₁ h1 h0 => by
      have := h.cpt k hk 0 (zero_mem _) f hf 0 f₁ (acts_zero _) h1 (by rw [h0, map_zero])
      rw [map_zero] at this; exact this.symm⟩
  have onto' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ y, ∃ f' ∈ G.M'.Pol B.ψ B.emb, R'.p' f' = y :=
    fun R' h y => by
      have : y ∈ (G.M'.Pol B.ψ B.emb).map R'.p' := h.quot'.onto ▸ Submodule.mem_top
      exact Submodule.mem_map.1 this
  have onto : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ y, ∃ f ∈ G.M.Pol B.ψ B.emb, R'.p f = y :=
    fun R' h y => by
      have : y ∈ (G.M.Pol B.ψ B.emb).map R'.p := h.quot.onto ▸ Submodule.mem_top
      exact Submodule.mem_map.1 this
  have irr_p' : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → Irred B G.M' om' R'.p' := fun R' h N h1 h2 => by
    apply h.irred N
    · intro γ hγ f hf f₁ hf₁ hN
      obtain ⟨f', hf', e⟩ := onto' R' h (R'.p f)
      obtain ⟨D, -, hDi⟩ := actV'.2.2.1 γ hγ
      have h1' := (hDi f' hf' (D f')).2 rfl
      rw [h.lie γ hγ f hf f' hf' f₁ (D f') hf₁ h1' e.symm]
      exact h1 γ hγ f' hf' (D f') h1' (e ▸ hN)
    · intro k hk f hf f₁ hf₁ hN
      obtain ⟨f', hf', e⟩ := onto' R' h (R'.p f)
      obtain ⟨D, -, hDi⟩ := actV'.2.2.2 k hk
      have h1' := (hDi f' hf' (D f')).2 rfl
      rw [h.cpt k hk f hf f' hf' f₁ (D f') hf₁ h1' e.symm]
      exact h2 k hk f' hf' (D f') h1' (e ▸ hN)
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_equiv_howeDuality_realPlaces F E σ B _ _ _ _ G.M om _ _ R.p R₃.p actV (_root_.GlobalTheory.ReBase.howe_supremum_projection hKP hPV) hR.quot hR₃.quot hR.nontriv
    hR₃.nontriv (ks_p R hR) (ks_p R₃ hR₃) hR.irred hR₃.irred
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.T.exists_equiv_howeDuality_realPlaces F E σ B _ _ _ _ G.M' om' _ _ R.p' R₃.p' actV' (_root_.GlobalTheory.ReBase.howe_supremum_projection hKP hPV') hR.quot' hR₃.quot'
    hR.nontriv hR₃.nontriv (ks_p' R hR) (ks_p' R₃ hR₃) (irr_p' R hR) (irr_p' R₃ hR₃)
  choose DL hDLm hDLi using actV.2.2.1
  choose DK hDKm hDKi using actV.2.2.2
  choose DL' hDLm' hDLi' using actV'.2.2.1
  choose DK' hDKm' hDKi' using actV'.2.2.2
  let ι : Type := {γ // γ ∈ Lines σ G.W} ⊕ {k // k ∈ KInf σ G.W B.emb}
  let D : ι → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')) :=
    Sum.elim (fun γ => DL γ.1 γ.2) (fun k => DK k.1 k.2)
  let D' : ι → SInf F (Fin a' × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a' × Fin (a + a')) :=
    Sum.elim (fun γ => DL' γ.1 γ.2) (fun k => DK' k.1 k.2)
  have Dm : ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb, D i f ∈ G.M.Pol B.ψ B.emb := by
    rintro (γ | k) f hf
    exacts [hDLm _ _ f hf, hDKm _ _ f hf]
  have Dm' : ∀ i, ∀ f ∈ G.M'.Pol B.ψ B.emb, D' i f ∈ G.M'.Pol B.ψ B.emb := by
    rintro (γ | k) f hf
    exacts [hDLm' _ _ f hf, hDKm' _ _ f hf]
  have joint : ∀ R' : RealMaps F a a', IsRealMaps B G om om' R' → ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb,
      ∀ f' ∈ G.M'.Pol B.ψ B.emb, R'.p f = R'.p' f' → R'.p (D i f) = R'.p' (D' i f') := by
    rintro R' h (γ | k) f hf f' hf' e
    · exact h.lie γ.1 γ.2 f hf f' hf' _ _ ((hDLi _ _ f hf _).2 rfl) ((hDLi' _ _ f' hf' _).2 rfl) e
    · exact h.cpt k.1 k.2 f hf f' hf' _ _ ((hDKi _ _ f hf _).2 rfl) ((hDKi' _ _ f' hf' _).2 rfl) e
  have ker0 : ∀ i, ∀ f ∈ G.M.Pol B.ψ B.emb, R.p f = 0 → R.p (D i f) = 0 := by
    rintro (γ | k) f hf h0
    · exact (ks_p R hR).1 γ.1 γ.2 f hf _ ((hDLi _ _ f hf _).2 rfl) h0
    · exact (ks_p R hR).2 k.1 k.2 f hf _ ((hDKi _ _ f hf _).2 rfl) h0
  let π : G.M.Pol B.ψ B.emb →ₗ[ℂ] R.Pi := R.p ∘ₗ (G.M.Pol B.ψ B.emb).subtype
  have hπ : Function.Surjective π := fun y => by
    obtain ⟨f, hf, e⟩ := onto R hR y
    exact ⟨⟨f, hf⟩, e⟩
  let ρ : ι → Module.End ℂ R.Pi := fun i =>
    induced π hπ ((D i).restrict (Dm i)) (fun u hu => ker0 i u.1 u.2 hu)
  have hρ : ∀ i, ∀ f (hf : f ∈ G.M.Pol B.ψ B.emb), ρ i (R.p f) = R.p (D i f) := fun i f hf =>
    induced_apply π hπ _ _ ⟨f, hf⟩
  have irrρ : ∀ N : Submodule ℂ R.Pi, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN => by
    apply hR.irred N
    · intro γ hγ f hf f₁ h1 hx
      rw [(hDLi γ hγ f hf f₁).1 h1]
      have := hN (Sum.inl ⟨γ, hγ⟩) _ hx
      rwa [hρ _ f hf] at this
    · intro k hk f hf f₁ h1 hx
      rw [(hDKi k hk f hf f₁).1 h1]
      have := hN (Sum.inr ⟨k, hk⟩) _ hx
      rwa [hρ _ f hf] at this
  let T : Module.End ℂ R.Pi := ψ.symm.toLinearMap ∘ₗ ψ₁.toLinearMap
  have comm : ∀ i, T * ρ i = ρ i * T := fun i => by
    refine LinearMap.ext fun x => ?_
    obtain ⟨f', hf', rfl⟩ := onto' R hR x
    obtain ⟨f, hf, e⟩ := onto R hR (R.p' f')
    obtain ⟨g, hg, eg⟩ := onto R₃ hR₃ (R₃.p' f')
    have j1 := joint R hR i f hf f' hf' e
    have j3 := joint R₃ hR₃ i g hg f' hf' eg
    have lhs : T (ρ i (R.p' f')) = R.p (D i g) := by
      calc T (ρ i (R.p' f')) = ψ.symm (ψ₁ (R.p' (D' i f'))) := by rw [← e, hρ i f hf, j1]; rfl
      _ = ψ.symm (R₃.p' (D' i f')) := by rw [← hψ₁ _ (Dm' i f' hf')]
      _ = R.p (D i g) := by rw [← j3, hψ _ (Dm i g hg), LinearEquiv.symm_apply_apply]
    have rhs : ρ i (T (R.p' f')) = R.p (D i g) := by
      calc ρ i (T (R.p' f')) = ρ i (ψ.symm (R₃.p' f')) := by
            show ρ i (ψ.symm (ψ₁ (R.p' f'))) = _
            rw [← hψ₁ f' hf']
      _ = ρ i (R.p g) := by rw [← eg, hψ g hg, LinearEquiv.symm_apply_apply]
      _ = R.p (D i g) := hρ i g hg
    rw [Module.End.mul_apply, Module.End.mul_apply, lhs, rhs]
  have hrank : Module.rank ℂ R.Pi ≤ Cardinal.aleph0 :=
    (LinearMap.rank_le_of_surjective π hπ).trans (_root_.GlobalTheory.T.polarization_rank_le_dim hKP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hPV)
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_one_of_commute_irreducible_of_countable_rank R.Pi ι ρ T hR.nontriv hrank irrρ comm
  have hT : ∀ x, T x = c • x := fun x => by rw [hc]; rfl
  refine ⟨ψ, c, ?_, hψ, fun f hf => ?_⟩
  · rintro rfl
    haveI := hR.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : R.Pi)
    have h0 : ψ.symm (ψ₁ x) = 0 := by rw [← zero_smul ℂ x, ← hT x]; rfl
    exact hx (ψ₁.injective (ψ.symm.injective (h0.trans (map_zero _).symm) |>.trans (map_zero _).symm))
  · rw [hψ₁ f hf]
    calc ψ₁ (R.p' f) = ψ (T (R.p' f)) := by
          show _ = ψ (ψ.symm (ψ₁ (R.p' f)))
          rw [LinearEquiv.apply_symm_apply]
    _ = c • ψ (R.p' f) := by rw [hT, map_smul]
end Real
section Fin
open GlobalTheory.FinUniq
end Fin
end GlobalTheory.ReBase
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralCompRightTranslate
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace GlobalTheory.ThetaRightTranslate
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem thetaIntegral_rightTranslate_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ g ∈ UAt σ X (evI F), ∀ (h : UA σ W.J) (Φ : (Fin n × Fin d → AF F) → ℂ),
      Φ ∈ schA F (Fin n × Fin d) → ∀ y, M.I om (om (g, h) Φ) y = M.I om Φ (y * h) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp g _ h Φ hΦ y
  have hTB := _root_.GlobalTheory.T.theta_kernel_fundamental_properties hP F E σ B n d X W M χX χW om r s r' s' hp
  have hinv : ∀ γ ∈ ratU σ X.J, ∀ x, theta om Φ (γ * x) (y * h) = theta om Φ x (y * h) := by
    intro γ hγ x
    have := (hTB.1 Φ hΦ).2.1 γ hγ 1 (one_mem _) x (y * h)
    rwa [one_mul] at this
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := hp.good.haar
  haveI : M.μ.IsMulRightInvariant := isMulRightInvariant σ hp.base.cm X.J hp.herm.herm
    (GlobalTheory.isUnit_det_of_isHerm F E σ B n X r s hp.herm) M.μ
  haveI := countable_ratU σ X.J
  haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩
  haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ :=
    ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩
  have hL : M.I om (om (g, h) Φ) y = ∫ x in M.dom, theta om Φ (x * g) (y * h) ∂M.μ := by
    unfold Model.I theta
    congr 1
    funext x
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  have hmp := measurePreserving_mul_right M.μ g
  have h1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight g) (fun x => theta om Φ x (y * h))
    ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom)
  have hpre : (fun x : UA σ X.J => x * g) ⁻¹' ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) = M.dom := by
    ext x; simp
  rw [hpre] at h1
  have hfd' : IsFundamentalDomain (ratU σ X.J) ((fun x : UA σ X.J => x * g⁻¹) ⁻¹' M.dom) M.μ :=
    hp.good.dom.preimage_of_equiv (measurePreserving_mul_right M.μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id (fun γ x => by
        show (γ.1 * x) * g⁻¹ = γ.1 * (x * g⁻¹)
        exact mul_assoc _ _ _)
  have h2 := hfd'.setIntegral_eq hp.good.dom (f := fun x => theta om Φ x (y * h)) (fun γ x => hinv γ.1 γ.2 x)
  rw [hL, h1, h2]
  rfl
end GlobalTheory.ThetaRightTranslate
end
end

section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntegral_comp_rightTranslate : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ g ∈ UAt σ X (evI F), ∀ (h : UA σ W.J) (Φ : (Fin n × Fin d → AF F) → ℂ),
      Φ ∈ schA F (Fin n × Fin d) → ∀ y, M.I om (om (g, h) Φ) y = M.I om Φ (y * h) := by
  first | exact @_root_.GlobalTheory.ThetaRightTranslate.thetaIntegral_rightTranslate_eq | exact _root_.GlobalTheory.ThetaRightTranslate.thetaIntegral_rightTranslate_eq | (intros; apply _root_.GlobalTheory.ThetaRightTranslate.thetaIntegral_rightTranslate_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoweReBase
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace UpperTheory.Lit.HoweDuality
open GlobalTheory GlobalTheory.FinUniq
theorem exists_local_iso_scalar_of_reG : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    ∀ (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (Rf₃ : FinMaps F a a'), IsFinMaps B (reG G V V' W) X om om' Rf₃ →
    ∀ v : Pl F, ∃ (ψ : Rf.Pi v ≃ₗ[ℂ] Rf₃.Pi v) (l : ℂ), l ≠ 0 ∧ (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf₃.p v φ = ψ (Rf.p v φ)) ∧
      (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf₃.p' v φ = l • ψ (Rf.p' v φ)) ∧ (v ∉ X.T → l = 1) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM V V' W Rf₃ h₃ v
  have hT := hM.triple
  have hf := hM.fin
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hP' := GlobalTheory.ThK.Inhab.pairV' hT
  have hAE := _root_.GlobalTheory.ThK.LocalOps.theta_kernel_local_operators_act hK
  have h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := fun u _ => by
    show u • ((1 : UA σ G.V.J).1.1 - 1) = 0
    rw [show (1 : UA σ G.V.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have h1V' : (1 : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := fun u _ => by
    show u • ((1 : UA σ G.V'.J).1.1 - 1) = 0
    rw [show (1 : UA σ G.V'.J).1.1 = 1 from rfl, sub_self, smul_zero]
  have exV : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om _ _ _ _ hP v).1 1 h1V h hh φ hφ
    exact ⟨φ₁, h1, h2⟩
  have exV' : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) φ φ₁ := fun h hh φ hφ => by
    obtain ⟨φ₁, ⟨h1, h2⟩, -⟩ := (hAE F E σ B _ _ _ _ _ _ _ om' _ _ _ _ hP' v).1 1 h1V' h hh φ hφ
    exact ⟨φ₁, h1, h2⟩
  have props : ∀ Q : FinMaps F a a',
      (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) = ⊤ →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁' ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' → Q.p v φ = Q.p' v φ' →
          Q.p v φ₁ = Q.p' v φ₁') →
      (∀ N : Submodule ℂ (Q.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Q.p v φ ∈ N → Q.p v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, h)) φ φ₁ → Q.p v φ = 0 → Q.p v φ₁ = 0) ∧
      (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ → Q.p' v φ = 0 → Q.p' v φ₁ = 0) ∧
      (∀ N : Submodule ℂ (Q.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (1, h)) φ φ₁ → Q.p' v φ ∈ N → Q.p' v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) := by
    intro Q onto' eqv irr
    refine ⟨fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun h hh φ hφ φ₁ hφ₁ hact e => ?_, fun N hN => irr N ?_⟩
    · rw [eqv h hh φ hφ 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero_zero v _) (by rw [e, map_zero]), map_zero]
    · rw [← eqv h hh 0 (zero_mem _) φ hφ 0 (zero_mem _) φ₁ hφ₁ (acts_zero_zero v _) hact (by rw [e, map_zero]), map_zero]
    · intro h hh φ hφ φ₁ hφ₁ hact hmem
      obtain ⟨φ', hφ', e⟩ : ∃ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Q.p' v φ' = Q.p v φ := by
        have : Q.p v φ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Q.p' v) := by rw [onto']; trivial
        exact this
      obtain ⟨φ₁', hφ₁', hact'⟩ := exV' h hh φ' hφ'
      rw [eqv h hh φ hφ φ' hφ' φ₁ hφ₁ φ₁' hφ₁' hact hact' e.symm]
      exact hN h hh φ' hφ' φ₁' hφ₁' hact' (e ▸ hmem)
  obtain ⟨sV, sV', iV'⟩ := props Rf (hf.onto' v) (hf.equiv v) (hf.irred v)
  obtain ⟨tV, tV', jV'⟩ := props Rf₃ (h₃.onto' v) (h₃.equiv v) (h₃.irred v)
  haveI := hf.nontriv v
  haveI := h₃.nontriv v
  have mV := ker_maximal om v (Rf.p v) (hf.onto v) (hf.inv v) sV (hf.irred v)
  have mV₃ := ker_maximal (Y := G.V) (Z := G.W) om v (Rf₃.p v) (h₃.onto v) (h₃.inv v) tV (h₃.irred v)
  have mV' := ker_maximal om' v (Rf.p' v) (hf.onto' v) (hf.inv' v) sV' iV'
  have mV₃' := ker_maximal (Y := G.V') (Z := G.W) om' v (Rf₃.p' v) (h₃.onto' v) (h₃.inv' v) tV' jV'
  have howe := PositivityTheory.Sph.maxFinT_of sphTri F E σ B a a' G X om om' hT v trivial
  have eV := howe.1 _ _ mV mV₃
  have eV' := howe.2 _ _ mV' mV₃'
  obtain ⟨ψ, hψ⟩ := equiv_of_ker_eq' (Rf.p v) (Rf₃.p v) (hf.onto v) (h₃.onto v) eV
  obtain ⟨ψ', hψ'⟩ := equiv_of_ker_eq' (Rf.p' v) (Rf₃.p' v) (hf.onto' v) (h₃.onto' v) eV'
  set T : Module.End ℂ (Rf.Pi v) := ψ.symm.toLinearMap ∘ₗ ψ'.toLinearMap with hTdef
  have hTapp : ∀ x, T x = ψ.symm (ψ' x) := fun x => rfl
  have comm : ∀ h ∈ UAt σ G.W (evFin F v), ∀ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ χ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) χ χ₁ → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ = T (Rf.p v χ) → Rf.p v φ₁ = T (Rf.p v χ₁) := by
    intro h hh χ hχ χ₁ hχ₁ hc φ hφ φ₁ hφ₁ ha e
    obtain ⟨χ', hχ', e1⟩ : ∃ χ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf.p' v χ' = Rf.p v χ := by
      have : Rf.p v χ ∈ (SB (Fin a' × Fin (a + a') → Fv F v)).map (Rf.p' v) := by rw [hf.onto' v]; trivial
      exact this
    obtain ⟨χ₁', hχ₁', hc'⟩ := exV' h hh χ' hχ'
    have e2 : Rf.p v χ₁ = Rf.p' v χ₁' := hf.equiv v h hh χ hχ χ' hχ' χ₁ hχ₁ χ₁' hχ₁' hc hc' e1.symm
    have e3 : Rf₃.p v φ = Rf₃.p' v χ' := by
      rw [hψ φ hφ, e, hTapp, ← e1, LinearEquiv.apply_symm_apply, ← hψ' χ' hχ']
    have e4 : Rf₃.p v φ₁ = Rf₃.p' v χ₁' := h₃.equiv v h hh φ hφ χ' hχ' φ₁ hφ₁ χ₁' hχ₁' ha hc' e3
    rw [hTapp, e2, ← hψ' χ₁' hχ₁', ← e4, hψ φ₁ hφ₁, LinearEquiv.symm_apply_apply]
  have hrank : Module.rank ℂ (Rf.Pi v) ≤ Cardinal.aleph0 := by
    haveI := sc_Fv v
    have sp : Function.Surjective ((Rf.p v).comp (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := fun y => by
      have : y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by rw [hf.onto v]; trivial
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨⟨x, hx⟩, rfl⟩
    exact (LinearMap.rank_le_of_surjective _ sp).trans (rank_SB_le _)
  have hker : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.ker (T - c • 1) →
        Rf.p v φ₁ ∈ LinearMap.ker (T - c • 1) := by
    intro c h hh φ hφ φ₁ hφ₁ hact hmem
    rw [LinearMap.mem_ker] at hmem ⊢
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hmem ⊢
    have hsc := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hφ hact hact c 0
    rw [zero_smul, zero_smul, add_zero, add_zero] at hsc
    have e : Rf.p v (c • φ) = T (Rf.p v φ) := by rw [map_smul, hmem]
    have := comm h hh φ hφ φ₁ hφ₁ hact (c • φ) ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ) (c • φ₁)
      ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hφ₁) hsc e
    rw [← this, map_smul]
  have hran : ∀ c : ℂ, ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ LinearMap.range (T - c • 1) →
        Rf.p v φ₁ ∈ LinearMap.range (T - c • 1) := by
    intro c h hh φ hφ φ₁ hφ₁ hact hmem
    obtain ⟨y, hy⟩ := hmem
    obtain ⟨χ, hχ, rfl⟩ : ∃ χ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf.p v χ = y := by
      have : y ∈ (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) := by rw [hf.onto v]; trivial
      exact this
    obtain ⟨χ₁, hχ₁, hc⟩ := exV h hh χ hχ
    have hsum := GlobalTheory.ThK.LocalOps.acts_lin v (om (1, h)) (exV h hh) hφ hχ hact hc 1 c
    rw [one_smul, one_smul] at hsum
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hy
    have e : Rf.p v (φ + c • χ) = T (Rf.p v χ) := by
      rw [map_add (f := _), map_smul, ← hy]; abel
    have := comm h hh χ hχ χ₁ hχ₁ hc (φ + c • χ) (add_mem hφ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ)) (φ₁ + c • χ₁)
      (add_mem hφ₁ ((SB (Fin a × Fin (a + a') → Fv F v)).smul_mem c hχ₁)) hsum e
    refine ⟨Rf.p v χ₁, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [← this, map_add (f := _), map_smul]; abel
  obtain ⟨l, hl⟩ := scalar_of_irred (fun N => ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ → Rf.p v φ ∈ N → Rf.p v φ₁ ∈ N)
    hrank (hf.irred v) T hker hran
  have hTl : ∀ x, ψ' x = l • ψ x := fun x => by
    have := congrArg (fun f : Module.End ℂ (Rf.Pi v) => f x) hl
    simp only [hTapp, LinearMap.smul_apply, Module.End.one_apply] at this
    rw [← map_smul, ← this, LinearEquiv.apply_symm_apply]
  have hl0 : l ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := exists_ne (0 : Rf.Pi v)
    have := hTl x
    rw [zero_smul, LinearEquiv.map_eq_zero_iff] at this
    exact hx this
  refine ⟨ψ, l, hl0, hψ, fun φ hφ => by rw [hψ' φ hφ, hTl], fun hv => ?_⟩
  obtain ⟨s1, s2⟩ := hf.sph v hv
  obtain ⟨s3, -⟩ := h₃.sph v hv
  have hvac := (hT.geo.hM.vac v).1
  have hvac' := (hT.geo.hM'.vac v).1
  change Rf₃.p v (G.M.vac v) = Rf₃.p' v (G.M'.vac v) at s3
  have e1 : Rf₃.p' v (G.M'.vac v) = l • Rf₃.p v (G.M.vac v) := by
    rw [hψ' _ hvac', hTl, ← s1, ← hψ _ hvac]
  have hne : Rf₃.p v (G.M.vac v) ≠ 0 := by
    rw [hψ _ hvac]; exact (LinearEquiv.map_ne_zero_iff ψ).2 s2
  rw [← s3] at e1
  have : (l - 1) • Rf₃.p v (G.M.vac v) = 0 := by rw [sub_smul, one_smul, ← e1, sub_self]
  rcases smul_eq_zero.1 this with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hne
end UpperTheory.Lit.HoweDuality
end
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
noncomputable section
namespace GlobalTheory.ReBase
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')}
variable {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem rebase_finite_scalar (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {R R₂ : RealMaps F a a'} {Rf S : FinMaps F a a'}
    (hM : IsMatched B G X om om' R Rf) (hM₂ : IsMatched B (reG G V V' Z) X om om' R₂ S) :
    ∃ (ψ : ∀ v, Rf.Pi v ≃ₗ[ℂ] S.Pi v) (l : Pl F → ℂ), (∀ v ∉ X.T, l v = 1) ∧
      (∀ v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), S.p v φ = ψ v (Rf.p v φ)) ∧
      (∀ v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S.p' v φ = l v • ψ v (Rf.p' v φ)) ∧
      ∏ v ∈ X.T, l v = X.ν (kapId B G V V' Z) := by
  choose ψ l hl h3 h4 h5 using _root_.UpperTheory.Lit.HoweDuality.exists_local_iso_scalar_of_reG hP F E σ B a a' G X om om' R Rf hM V V' Z S hM₂.fin
  refine ⟨ψ, l, h5, h3, h4, ?_⟩
  have hc := hM.triple.chars
  have key : ∀ v : B.P, l v.1 = (chrW X.ν (B.τ v) (kap G V V' Z v.1) : ℂ) := by
    intro v
    by_cases hv : v.1 ∈ X.T
    · haveI := hM.fin.nontriv v.1
      obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v.1)
      obtain ⟨φ, hφ, e⟩ : y ∈ (SB _).map (Rf.p v.1) := by rw [hM.fin.onto]; trivial
      obtain ⟨φ', hφ', e'⟩ : y ∈ (SB _).map (Rf.p' v.1) := by rw [hM.fin.onto']; trivial
      have h := zeta_rel hM.triple.base hM.triple.geo hM₂.triple.geo (hM.fin.zeta v hv) (hM₂.fin.zeta v hv) hφ hφ'
        (e.trans e'.symm)
      rw [map_smul, h3 _ _ hφ, h4 _ _ hφ', e, e'] at h
      exact (smul_left_injective ℂ ((LinearEquiv.map_ne_zero_iff (ψ v.1)).2 hy) h).symm
    · have hw : splitPrime (B.τ v) ∉ above E (X.T : Set (Pl F)) := fun h => hv (by
        have h' : (splitPrime (B.τ v)).under (𝓞 F) ∈ (X.T : Set (Pl F)) := h
        rwa [splitPrime_under] at h')
      have hk := valuation_kap hM.triple.geo hM₂.triple.geo v
      have h1 := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.α hc.heckeα v.1 (B.τ v)).2.2.2 (hc.unrα _ hw) _ hk
      have h2 := (GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.β hc.heckeβ v.1 (B.τ v)).2.2.2 (hc.unrβ _ hw) _ hk
      have h0 : chrW X.ν (B.τ v) (kap G V V' Z v.1) =
          chrW X.α (B.τ v) (kap G V V' Z v.1) / chrW X.β (B.τ v) (kap G V V' Z v.1) := by
        simp only [Chars.ν, chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply, map_div]
      rw [h5 _ hv, h0, h1, h2, div_one, Units.val_one]
  rw [chr_kapId, Finset.prod_subset hc.sub (fun v _ hv => h5 v hv), ← Finset.prod_coe_sort B.P l]
  exact Finset.prod_congr rfl fun v _ => key v
theorem rebase_constants_agree (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) {R R₂ : RealMaps F a a'} {Rf S : FinMaps F a a'}
    (hM : IsMatched B G X om om' R Rf) (hM₂ : IsMatched B (reG G V V' Z) X om om' R₂ S)
    {g : UA σ G.V.J} (hg : g ∈ UAt σ G.V (evI F)) {g' : UA σ G.V'.J} (hg' : g' ∈ UAt σ G.V' (evI F))
    {h : UA σ G.W.J} (hh : h ∈ UAt σ G.W (evI F))
    (hθ : ∀ w, (mat g).map (piInf (B.emb w)) * G.V.θ w = V.θ w * (mat g).map (piInf (B.emb w)))
    (hθ' : ∀ w, (mat g').map (piInf (B.emb w)) * G.V'.θ w = V'.θ w * (mat g').map (piInf (B.emb w)))
    (hθW : ∀ w, (mat h).map (piInf (B.emb w)) * G.W.θ w = Z.θ w * (mat h).map (piInf (B.emb w)))
    {T : SInf F (Fin a × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a × Fin (a + a'))}
    {T' : SInf F (Fin a' × Fin (a + a')) ≃ₗ[ℂ] SInf F (Fin a' × Fin (a + a'))} (hTc : Continuous T) (hTc' : Continuous T')
    (hT1 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g, h)) f (T f))
    (hT2 : ∀ f : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f))
    (hT1' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g', h)) f (T' f))
    (hT2' : ∀ f : SInf F (Fin a' × Fin (a + a')), Acts (evI F) (om' (g'⁻¹, h⁻¹)) f (T'.symm f))
    {ψ₀ : R.Pi ≃ₗ[ℂ] (reR R₂ T T').Pi} {l₀ : ℂ} (hl₀ : l₀ ≠ 0)
    (hR : ∀ f ∈ G.M.Pol B.ψ B.emb, (reR R₂ T T').p f = ψ₀ (R.p f))
    (hR' : ∀ f ∈ G.M'.Pol B.ψ B.emb, (reR R₂ T T').p' f = l₀ • ψ₀ (R.p' f))
    {c d : ℂ} (hc : IsConst B G X om om' R Rf c) (hd : IsConst B (reG G V V' Z) X om om' R₂ S d) :
    d = l₀ * X.ν (kapId B G V V' Z) * c := by
  obtain ⟨ψ, l, hl1, h3, h4, hl⟩ := _root_.GlobalTheory.ReBase.rebase_finite_scalar hP hM hM₂
  obtain ⟨⟨-, hu, -⟩, -, hso⟩ := (hK.1 F E σ B a a' G X om om' hM.triple).2 R Rf hM
  have hT := hM.triple
  set Λ : ℂ := l₀ * X.ν (kapId B G V V' Z) with hΛ
  have hΛ0 : Λ ≠ 0 := mul_ne_zero hl₀ (Circle.coe_ne_zero _)
  have pm : ∀ Φ Φ', PolMatch B G X R Rf Φ Φ' →
      PolMatch B (reG G V V' Z) X R₂ S (om (g, h) (Λ • Φ)) (om' (g', h) Φ') := fun Φ Φ' hm => by
    have := polMatch_iso hl1 hR hR' h3 h4 hm
    rw [hl] at this
    exact polMatch_transport hT R₂ hg hg' hh hθ hθ' hθW hT1 hT2 hT1' hT2' S this
  have so : ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, om' (g', h) Φ' ∈ (reG G V V' Z).M'.So B.ψ B.τ₁ := fun Φ' hΦ' =>
    (GlobalTheory.ThKRealConj.so_reG' G V V' Z B.ψ B.τ₁).symm ▸ hso (g', h) Φ' hΦ'
  have hc' : IsConst B G X om om' R Rf (d / Λ) := by
    rintro Φ Φ' ⟨hSo, m, m', r, f, s, r', f', s', hr, hr', hΦ, hΦ', hk⟩ y
    have e1 : ∀ u : Fin m → SInf F (Fin a × Fin (a + a')),
        om (g, h) (Λ • ∑ i, pureA F (u i) (r i)) = ∑ i, pureA F (⇑(Λ • T (u i))) (r i) := fun u => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [acts_pureA (hT1 (u i)) (hr i).1, pureA_smul]
    have e2 : ∀ u : Fin m' → SInf F (Fin a' × Fin (a + a')),
        om' (g', h) (∑ i, pureA F (u i) (r' i)) = ∑ i, pureA F (T' (u i)) (r' i) := fun u => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => acts_pureA (hT1' (u i)) (hr' i).1
    have hm : Match B (reG G V V' Z) X R₂ S (om (g, h) (Λ • Φ)) (om' (g', h) Φ') := by
      refine ⟨so _ hSo, m, m', r, fun i => Λ • T (f i), fun k i => Λ • T (s k i), r', fun i => T' (f' i),
        fun k i => T' (s' k i), fun i => ⟨(hr i).1, ((hTc.tendsto _).comp (hr i).2).const_smul Λ⟩,
        fun i => ⟨(hr' i).1, (hTc'.tendsto _).comp (hr' i).2⟩, by rw [hΦ, e1], by rw [hΦ', e2], fun k => ?_⟩
      have h1 := so _ (hk k).1
      have h2 := pm _ _ (hk k).2
      rw [e2] at h1
      rw [e1, e2] at h2
      exact ⟨h1, h2⟩
    have sΦ : Λ • Φ ∈ schA F (Fin a × Fin (a + a')) := by
      rw [hΦ]
      exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, r i, (hr i).1, rfl⟩)
    have sΦ' : Φ' ∈ schA F (Fin a' × Fin (a + a')) := by
      rw [hΦ']
      exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, r' i, (hr' i).1, rfl⟩
    have key := hd _ _ hm (y * h⁻¹)
    have i1 := _root_.GlobalTheory.T.thetaIntegral_comp_rightTranslate hP F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ (GlobalTheory.ThK.RealUniq.isPair_V hT) g hg h _ sΦ
      (y * h⁻¹)
    have i2 := _root_.GlobalTheory.T.thetaIntegral_comp_rightTranslate hP F E σ B a' (a + a') G.V' G.W G.M' _ _ om' _ _ _ _ (GlobalTheory.ThK.RealUniq.isPair_V' hT) g' hg' h _
      sΦ' (y * h⁻¹)
    rw [inv_mul_cancel_right] at i1 i2
    change G.M.I om (om (g, h) (Λ • Φ)) (y * h⁻¹) = d * G.M'.I om' (om' (g', h) Φ') (y * h⁻¹) at key
    rw [i1, i2, GlobalTheory.PolIso.modelI_smul] at key
    rw [div_mul_eq_mul_div, eq_div_iff hΛ0, ← key, mul_comm]
  rw [hu.unique hc hc']
  field_simp
theorem rebase_ratio_real_part (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hK : ThetaIntegralsAgree) {Xa Xb : Chars F E} {R R₂ : RealMaps F a a'}
    {oa ob : Rep σ G.V G.W} {oa' ob' : Rep σ G.V' G.W} {Ra Rb Sa Sb : FinMaps F a a'} {ca cb da db : ℂ}
    (m1 : IsMatched B G Xa oa oa' R Ra) (m2 : IsMatched B G Xb ob ob' R Rb)
    (n1 : IsMatched B (reG G V V' Z) Xa oa oa' R₂ Sa) (n2 : IsMatched B (reG G V V' Z) Xb ob ob' R₂ Sb)
    (k1 : IsConst B G Xa oa oa' R Ra ca) (k2 : IsConst B G Xb ob ob' R Rb cb)
    (l1 : IsConst B (reG G V V' Z) Xa oa oa' R₂ Sa da) (l2 : IsConst B (reG G V V' Z) Xb ob ob' R₂ Sb db) :
    ∃ k : (AE F E)ˣ, da * cb = ((Xa.ν k / Xb.ν k : Circle) : ℂ) * (db * ca) := by
  have ta := m1.triple
  have tb := m2.triple
  have hB := ta.base
  obtain ⟨g, hg, eg⟩ := GlobalTheory.T.cartan_involution_systems_conj_archimedean_unitary F E σ B a _ _ G.V V hB ta.geo.hV n1.triple.geo.hV
  obtain ⟨g', hg', eg'⟩ := GlobalTheory.T.cartan_involution_systems_conj_archimedean_unitary F E σ B a' _ _ G.V' V' hB ta.geo.hV' n1.triple.geo.hV'
  obtain ⟨h, hh, eh⟩ := GlobalTheory.T.skewHermitian_cartanInvolutionSystems_conjugate_archimedean F E σ B (a + a') _ _ G.W Z hB ta.geo.hW n1.triple.geo.hW
  obtain ⟨T, hTc, hT1, hT2⟩ := exists_op hB.std ta.weil hg hh
  obtain ⟨T', hTc', hT1', hT2'⟩ := exists_op hB.std ta.weil' hg' hh
  have hR₃ := _root_.GlobalTheory.ReBase.real_maps_transport hP ta R₂ hg hg' hh eg eg' eh hT1 hT2 hT1' hT2' n1.triple n1.real
  obtain ⟨ψ₀, l₀, hl₀, hR, hR'⟩ := _root_.GlobalTheory.ReBase.real_maps_unique hP F E σ B a a' G Xa oa oa' R Ra m1 _ hR₃
  have eα : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → Xa.α z = Xb.α z := fun z hz =>
    Circle.ext ((ta.chars.expα z hz).trans (tb.chars.expα z hz).symm)
  have eβ : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → Xa.β z = Xb.β z := fun z hz =>
    Circle.ext ((ta.chars.expβ z hz).trans (tb.chars.expβ z hz).symm)
  have eV := fun g hg h hh => weil_arch_eq (g := g) (k := h) hB.cm hB.std ta.geo.hV.herm
    (GlobalTheory.FinUniq.det_ne_zero_herm ta.geo.hV) ta.geo.hW.skew (GlobalTheory.FinUniq.det_ne_zero_skew ta.geo.hW) eβ
    (fun z hz => by rw [MonoidHom.div_apply, MonoidHom.div_apply, eα z hz, eβ z hz]) ta.weil tb.weil hg hh
  have eV' := fun g hg h hh => weil_arch_eq (g := g) (k := h) hB.cm hB.std ta.geo.hV'.herm
    (GlobalTheory.FinUniq.det_ne_zero_herm ta.geo.hV') ta.geo.hW.skew (GlobalTheory.FinUniq.det_ne_zero_skew ta.geo.hW) eα
    (fun z hz => by rw [MonoidHom.div_apply, MonoidHom.div_apply, eα z hz, eβ z hz]) ta.weil' tb.weil' hg hh
  have hhi := GlobalTheory.MajTransport.uat_inv hh
  have ha := _root_.GlobalTheory.ReBase.rebase_constants_agree hP hK m1 n1 hg hg' hh eg eg' eh hTc hTc' hT1 hT2 hT1' hT2' hl₀ hR hR' k1 l1
  have hb := _root_.GlobalTheory.ReBase.rebase_constants_agree hP hK m2 n2 hg hg' hh eg eg' eh hTc hTc' (fun f => acts_congr (eV g hg h hh) (hT1 f))
    (fun f => acts_congr (eV _ (GlobalTheory.MajTransport.uat_inv hg) _ hhi) (hT2 f))
    (fun f => acts_congr (eV' g' hg' h hh) (hT1' f))
    (fun f => acts_congr (eV' _ (GlobalTheory.MajTransport.uat_inv hg') _ hhi) (hT2' f)) hl₀ hR hR' k2 l2
  refine ⟨kapId B G V V' Z, ?_⟩
  have h0 : (Xb.ν (kapId B G V V' Z) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  rw [ha, hb, Circle.coe_div]
  field_simp
end GlobalTheory.ReBase
end
end
