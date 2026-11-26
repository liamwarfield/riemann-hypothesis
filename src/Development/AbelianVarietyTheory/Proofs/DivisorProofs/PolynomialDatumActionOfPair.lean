module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankDiffLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecondStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPair
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolActsPf

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.RealActs

section Swap

variable {P Q R S : ℕ}

def flipE (P Q R S : ℕ) : Formalism.BasicNotions.TH.Pol R S P Q ≃ₗ[ℂ] Formalism.BasicNotions.TH.Pol P Q R S :=
  (MvPolynomial.renameEquiv ℂ (Equiv.prodComm (Ix R S) (Ix P Q))).toLinearEquiv

theorem flipE_apply (f : Formalism.BasicNotions.TH.Pol R S P Q) : flipE P Q R S f = MvPolynomial.rename Prod.swap f := rfl

theorem lineSign_flip (a : Ix P Q) (b : Ix R S) :
    lineSign (p := R) (q := S) (r := P) (s := Q) b a = lineSign (p := P) (q := Q) (r := R) (s := S) a b := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem flipE_heisOp (c : Matrix (Ix R S) (Ix P Q) ℂ) (f : Formalism.BasicNotions.TH.Pol R S P Q) :
    flipE P Q R S (heisOp c f) = heisOp cᵀ (flipE P Q R S f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [heisOp, flipE_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    map_smul, map_sum, map_sub, GlobalTheory.FockSwap.rename_raiB, GlobalTheory.FockSwap.rename_lowB]
  congr 1
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_
  simp [lineSign_flip]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def flipT (ι : Type) (P Q R S : ℕ) :
    (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) ≃ₗ[ℂ] ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S :=
  PiTensorProduct.congr fun _ => flipE P Q R S

theorem flipT_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ f, flipE P Q R S (L' f) = L (flipE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    flipT ι P Q R S (atPl w L' T) = atPl w L (flipT ι P Q R S T) := by
  have e : (flipT ι P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (flipT ι P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, flipT,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

theorem flipT_sumPl (L' : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ w f, flipE P Q R S (L' w f) = L w (flipE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    flipT ι P Q R S (sumPl L' T) = sumPl L (flipT ι P Q R S T) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => flipT_atPl w (L' w) (L w) (h w) T

end Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isFockMap_flip {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    {P Q R S : ℕ} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w} {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ} {A : InfinitePlace F → Matrix α (Ix P Q) ℂ}
    {C : InfinitePlace F → Matrix β (Ix R S) ℂ} {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} (hΦ : IsFockMap ψ τ d A C Φ)
    (hdd : ∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) :
    IsFockMap ψ τ d' C A (Φ ∘ₗ (flipT (InfinitePlace F) P Q R S).toLinearMap) := by
  refine ⟨hΦ.1.comp (flipT (InfinitePlace F) P Q R S).injective, fun u hu c hc T => ?_⟩
  have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
  have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
    rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (flipT (InfinitePlace F) P Q R S T)
  have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
    show schr ψ (d'.e _) = schr ψ (d.e _)
    rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [flipT_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ) (fun w f => flipE_heisOp (c w) f)]
  set_option backward.isDefEq.respectTransparency false in
   rw [show (fun t : ℝ => d'.rho ψ (realAd F t • u)) =
    (fun t : ℝ => d.rho ψ (realAd F t • uᵀ)) from funext hr]
  exact key

theorem incM_map_real {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem locFin_compact (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

section Graph

variable {κ V : Type} [Fintype κ] [AddCommGroup V] [Module ℂ V] {Φ : V →ₗ[ℂ] SInf F κ}

theorem graph_of_inj (hΦ : Function.Injective Φ) (L : Module.End ℂ V) (Rel : SInf F κ → SInf F κ → Prop)
    (huniq : ∀ f f₁ f₂, Rel f f₁ → Rel f f₂ → f₁ = f₂) (h : ∀ v, Rel (Φ v) (Φ (L v))) :
    ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ LinearMap.range Φ, D f ∈ LinearMap.range Φ) ∧
      ∀ f ∈ LinearMap.range Φ, ∀ f₁ : SInf F κ, Rel f f₁ ↔ f₁ = D f := by
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hΦ)
  refine ⟨Φ ∘ₗ L ∘ₗ Ψ, fun f _ => LinearMap.mem_range_self Φ _, ?_⟩
  rintro _ ⟨v, rfl⟩ f₁
  have e : (Φ ∘ₗ L ∘ₗ Ψ) (Φ v) = Φ (L v) := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]
  rw [e]
  exact ⟨fun h1 => huniq _ _ _ h1 (h v), fun h1 => h1 ▸ h v⟩

theorem derOn_of_sd (hΦ : Function.Injective Φ) (L : Module.End ℂ V) (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (h0 : ∀ t, T t 0 = 0) (h : ∀ v, SD T (Φ v) (Φ (L v))) : DerOn (LinearMap.range Φ) T :=
  graph_of_inj hΦ L (fun f f₁ => ActsD (evI F) T f f₁) (fun f f₁ f₂ => (actsLaws F κ f f₁ f₂).2.2.1 T)
    fun v => (actsLaws F κ _ _ (Φ v)).1 T h0 (h v)

theorem opOn_of_sa (hΦ : Function.Injective Φ) (L : Module.End ℂ V) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (h0 : T 0 = 0) (h : ∀ v, SA T (Φ v) (Φ (L v))) : OpOn (LinearMap.range Φ) T :=
  graph_of_inj hΦ L (fun f f₁ => Acts (evI F) T f f₁) (fun f f₁ f₂ => (actsLaws F κ f f₁ f₂).2.2.2.1 T)
    fun v => (actsLaws F κ _ _ (Φ v)).2.1 T h0 (h v)

end Graph

theorem member (hP : GlobalTheory.FunPr.Hypotheses₂) {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype κ] {P Q R S : ℕ} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w}
    {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ} {a b : ℂ}
    {A : InfinitePlace F → Matrix α (Ix P Q) ℂ} {C : InfinitePlace F → Matrix β (Ix R S) ℂ}
    {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)}
    {θ : InfinitePlace F → Matrix β β ℂ} (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (fr : Framed τ JA JB a b A C)
    (hΦ : IsFockMap ψ τ d A C Φ) (hs : IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om)
    (hθ : ∀ w, θ w * C w = C w * Jm R S) :
    (∀ γ ∈ RLines (σ := σ) JB, DerOn (LinearMap.range Φ) (fun t => om (γ (Multiplicative.ofAdd t)))) ∧
    ∀ k : UG (cA σ) JB, At (evI F) ((k.1 : Matrix β β (AE F E)) - 1) →
      (∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) → OpOn (LinearMap.range Φ) (om k) := by
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hls : LieScalar := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hP hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)
  have hgen : GenEx := GlobalTheory.T.oneParamSubgroup_generators_exist
  have hkl : KLine := kLine_of_lineEx exists_line_of_upq
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ ψ τ _ _ d a b A C Φ om hcm hψ fr hΦ hs
  refine ⟨fun γ hγ => ?_, fun k hk hc => ?_⟩
  · obtain ⟨Y, -, hY⟩ := hgen F E σ β R S τ JB b C hcm fr.2.2 γ hγ
    exact derOn_of_sd hΦ.1 _ _ (fun t => map_zero _) (hact γ hγ Y hY)
  · obtain ⟨γ, hγ, Y, hY, hKC, hγ1⟩ := hkl F E σ β R S τ JB b C θ hcm fr.2.2 hθ k hk hc
    have hloc := locFin_sumPl _ _ _ (fun w => locFin_compact P Q R S (Y w) (hKC w) (c w * (Y w).trace))
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F κ _ Φ _ (om.comp γ) hloc
      (fun t l hl => hs.adm _ l hl) (fun T => hact γ hγ Y hY T)
    change ∀ T, SA (om (γ (Multiplicative.ofAdd 1))) (Φ T) (Φ (U T)) at hSA
    rw [hγ1] at hSA
    exact opOn_of_sa hΦ.1 U _ (map_zero _) hSA

theorem polActs_of_isPair : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → GlobalTheory.RealActs.PolActs B M om := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' h
  have hb := h.base
  have hfr : FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hfe : FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws actsLaws hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder)
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (h.herm.sig w) (h.herm.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (h.skew.sig w) (h.skew.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_real, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_real]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have fr' : Framed B.emb (incM F W.J) (incM F X.J) Complex.I 1 C A := ⟨mul_one _, hC1, hA1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := h.weil
  obtain ⟨d', hd', hB⟩ := hwp.2.1
  have hr' : LinearMap.range (Φ ∘ₗ (flipT (InfinitePlace F) r s r' s').toLinearMap) = M.Pol B.ψ B.emb := by
    rw [LinearEquiv.range_comp, hr]
  obtain ⟨h1, h2⟩ := member hP hb.cm hb.std fr' (isFockMap_flip hΦ hd') hB.1 hAθ
  obtain ⟨h3, h4⟩ := member hP hb.cm hb.std fr hΦ hwp.1.1 hCθ
  rw [hr'] at h1 h2
  rw [hr] at h3 h4
  exact ⟨fun γ hγ => h1 γ hγ, fun k hk => h2 k hk.1 hk.2, fun γ hγ => h3 γ hγ, fun k hk => h4 k hk.1 hk.2⟩

end GlobalTheory.PolActsPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantSmulIntegralOfFourthPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantSmulIntegralOfFourthPower
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.RuleIntegral

theorem vLa_int_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K}
    (hr : (r : K) ≠ 0) : 0 ≤ vLa w (r : K) := by
  unfold vLa
  have h1 := w.valuation_le_one (K := K) r
  have h2 : (w.valuation K) (r : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  omega

theorem nonneg_of_four {x : EReal} (hx : x ≠ ⊥) (h : 0 ≤ x + x + x + x) : 0 ≤ x := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => exact le_top
  | coe r =>
    have : (0 : EReal) ≤ ((r + r + r + r : ℝ) : EReal) := by simpa [EReal.coe_add] using h
    have h' : (0 : ℝ) ≤ r + r + r + r := EReal.coe_nonneg.1 this
    exact EReal.coe_nonneg.2 (by linarith)

theorem eq_zero_or_top_of_double {x : EReal} (hx : x ≠ ⊥) (h : x = x + x) : x = 0 ∨ x = ⊤ := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => exact Or.inr rfl
  | coe r =>
    left
    have h' : r = r + r := by exact_mod_cast h
    have : r = 0 := by linarith
    simp [this]

theorem exists_common_denom {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (a : ι → K) :
    ∃ s : 𝓞 K, (s : K) ≠ 0 ∧ ∀ i, ∃ r : 𝓞 K, (r : K) = (s : K) * a i := by
  classical
  have h := fun i => IsLocalization.exists_integer_multiple (nonZeroDivisors (𝓞 K)) (a i)
  choose d hd using h
  refine ⟨∏ i, (d i : 𝓞 K), ?_, fun i => ?_⟩
  · have hm : (∏ i, (d i : 𝓞 K)) ∈ nonZeroDivisors (𝓞 K) :=
      Submonoid.prod_mem _ fun i _ => (d i).2
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
  · obtain ⟨r, hr⟩ := hd i
    refine ⟨(∏ j ∈ Finset.univ.erase i, (d j : 𝓞 K)) * r, ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (d j : 𝓞 K)) (Finset.mem_univ i)]
    have e1 : ∀ x : 𝓞 K, (x : K) = algebraMap (𝓞 K) K x := fun _ => rfl
    rw [e1, e1, map_mul, map_mul, hr, Algebra.smul_def]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_idem_zero {w : HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal}
    (hv : v ∈ valSet Xo c (algCls Xo c) w) : ∃ Z, v (GlobalTheory.FlatLine.idem Z) = 0 := by
  obtain ⟨y, rfl⟩ := hv
  have h1 : vAtV y 1 = 0 := by
    rcases y with ⟨q, T, io, e, ho, y, hy, eta, heta, rfl⟩
    show nval T.V e (evI y 1) = 0
    have h1 : evI y 1 = 1 := by
      letI := io.toAlgebra
      exact evalAt_one _ _ y.1 y.2.1
    rw [h1, nval_of_ne one_ne_zero]
    simp [vV]
  by_contra hne
  push_neg at hne
  have htop : ∀ Z, vAtV y (GlobalTheory.FlatLine.idem Z) = ⊤ := fun Z => by
    have hd := vAtV_mul y (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z)
    rw [GlobalTheory.FlatLine.idem_mul_idem] at hd
    exact (eq_zero_or_top_of_double (vAtV_ne_bot y _) hd).resolve_left (hne Z)
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  classical
  have hs : ∀ s : Finset (Comp Xo c), vAtV y (∑ Z ∈ s, GlobalTheory.FlatLine.idem Z) = ⊤ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using vAtV_zero y
    | insert Z s hZ ih =>
      rw [Finset.sum_insert hZ]
      have := vAtV_add y (GlobalTheory.FlatLine.idem Z) (∑ Z ∈ s, GlobalTheory.FlatLine.idem Z)
      rw [htop Z, ih, min_self] at this
      exact top_le_iff.1 this
  have h2 := hs Finset.univ
  rw [GlobalTheory.FlatLine.sum_idem] at h2
  rw [h2] at h1
  exact EReal.top_ne_zero h1

theorem exists_smul_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K ρ : Rul Xo c) (a : Comp Xo c → c.F), (∀ Z, a Z ≠ 0) → (∀ Z, GlobalTheory.FlatLine.idem Z * ρ ^ 4 = a Z • (GlobalTheory.FlatLine.idem Z * K)) → (∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v K) → ∃ t : c.F, t ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (t • ρ) := by
  intro E _ _ _ H Dw l Xo c K ρ a ha hρ hK
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  obtain ⟨s, hs0, hsa⟩ := exists_common_denom a
  refine ⟨(s : c.F), hs0, fun w v hv => ?_⟩
  have hKv := hK w v hv
  obtain ⟨Z, hZ⟩ := exists_idem_zero hv
  obtain ⟨y, rfl⟩ := hv
  obtain ⟨r, hr⟩ := hsa Z
  have hb : (((s ^ 3 * r : 𝓞 c.F)) : c.F) = (s : c.F) ^ 4 * a Z := by
    have hr' : algebraMap (𝓞 c.F) c.F r = algebraMap (𝓞 c.F) c.F s * a Z := hr
    show algebraMap (𝓞 c.F) c.F (s ^ 3 * r) = (algebraMap (𝓞 c.F) c.F s) ^ 4 * a Z
    rw [map_mul, map_pow, hr']; ring
  have hb0 : (((s ^ 3 * r : 𝓞 c.F)) : c.F) ≠ 0 := by
    rw [hb]; exact mul_ne_zero (pow_ne_zero _ hs0) (ha Z)
  have hid : GlobalTheory.FlatLine.idem Z * ((s : c.F) • ρ) ^ 4 =
      (((s ^ 3 * r : 𝓞 c.F)) : c.F) • (GlobalTheory.FlatLine.idem Z * K) := by
    rw [smul_pow, mul_smul_comm, hρ Z, smul_smul, hb]
  have h4 : ∀ x : Rul Xo c, x ^ 4 = x * x * x * x := fun x => by ring
  have e := congrArg (vAtV y) hid
  rw [h4, vAtV_mul, vAtV_mul, vAtV_mul, vAtV_mul, vAtV_smul _ _ _ hb0, vAtV_mul, hZ, zero_add, zero_add] at e
  refine nonneg_of_four (vAtV_ne_bot _ _) ?_
  rw [e]
  refine add_nonneg ?_ hKv
  exact EReal.coe_nonneg.2 (by exact_mod_cast vLa_int_nonneg w hb0)

end GlobalTheory.RuleIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantSmulIntegralOfFourthPowerStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_smul_integral_of_fourth_power : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K ρ : Rul Xo c) (a : Comp Xo c → c.F), (∀ Z, a Z ≠ 0) → (∀ Z, GlobalTheory.FlatLine.idem Z * ρ ^ 4 = a Z • (GlobalTheory.FlatLine.idem Z * K)) → (∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v K) → ∃ t : c.F, t ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (t • ρ) := by
  first | exact @GlobalTheory.RuleIntegral.exists_smul_nonneg | exact GlobalTheory.RuleIntegral.exists_smul_nonneg | (intros; apply GlobalTheory.RuleIntegral.exists_smul_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LocWeilAct

theorem conjU_mul' {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (hc : J = c • V.gram) (a b : GA D V) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hc (a * b) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hc a * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hc b :=
  Subtype.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_mul])

theorem conjU_one' {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E)
    (hc : J = c • V.gram) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU V c hc 1 = 1 :=
  Subtype.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one])

theorem linear_of_acts {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (T : Module.End ℂ ((κ → AF F) → ℂ)) (S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ)
    (hS : ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), S φ ∈ GlobalTheory.WeilM.SB _ ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) T φ (S φ)) :
    ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _, ∀ c : ℂ, S (c • φ + φ') = c • S φ + S φ' := by
  intro φ hφ φ' hφ' c
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) κ v
  have hs := Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
  have tl : ∀ f f' : (κ → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (c • f + f') R =
      c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) f R + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) f' R := by
    intro f f'; funext x; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (S (c • φ + φ')) R =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (c • S φ + S φ') R := by
    rw [← (hS _ hs).2 R (hR _ hs), tl, tl, map_add (f := _), map_smul, (hS φ hφ).2 R (hR φ hφ), (hS φ' hφ').2 R (hR φ' hφ')]
  funext y
  have hx := congrFun e (fun k => GlobalTheory.LatVac.liftV v (y k))
  have hRx : R (fun k => GlobalTheory.LatVac.liftV v (y k)) = R 0 := by
    have := (hR φ hφ).1 0 (fun k => GlobalTheory.LatVac.liftV v (y k))
      (fun u hu => funext fun k => GlobalTheory.LatVac.at_liftV v (y k) u hu)
    rwa [zero_add] at this
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.LatVac.evFin_liftV, hRx] at hx
  exact mul_right_cancel₀ hR0 hx

theorem act_omB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om'),
    ∃ ν α : (Fv D.host.F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι : ((Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ]
              (Matrix (Fin (G.V (.grid i j)).rank) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)) (Fv D.host.F Bs.v₁) → ℂ),
      Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      ∀ g : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁), ∃ k : GA D (G.V (.grid i j)),
        ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁) φ r → ∃ φ₁ ∈ GlobalTheory.WeilM.SB _,
          om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) φ r) =
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) φ₁ r ∧ ι φ₁ = omB ν α g 1 (ι φ) := by
  intro D T L sc G W t i j M e Bs Γ X om om' h hTr
  obtain ⟨K, hK⟩ := GlobalTheory.SplitGLLift.exists_hom_supp_split W t i j M e Bs Γ X om om' h hTr
  let K' : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J :=
    { toFun := fun g => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ (K g)
      map_one' := by simp only [map_one]; exact conjU_one' _ _ _
      map_mul' := fun g g' => by simp only [map_mul]; exact conjU_mul' _ _ _ _ _ }
  have hK' : ∀ g, K' g = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ (K g) := fun _ => rfl
  have hB := fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' Bs Γ X om om' hTr Bs.v₁ (K' g) (hK g).1
  choose S hS using hB
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have pres : ∀ p Φ, Φ ∈ GlobalTheory.WeilM.schA D.host.F _ → om' p Φ ∈ GlobalTheory.WeilM.schA D.host.F _ :=
    fun p Φ hΦ => hSplit.pres p Φ hΦ
  have restS : ∀ g φ r, φ ∈ GlobalTheory.WeilM.SB _ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁) φ r →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁) (S g φ) r := fun g φ r hφ hr =>
    ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact pres _ _ hr.2⟩
  have h1 : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _ := fun g φ hφ => (hS g φ hφ).1
  have h2 : ∀ g g', ∀ φ ∈ GlobalTheory.WeilM.SB _, S (g * g') φ = S g (S g' φ) := by
    intro g g' φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ _ _ hφ fun r hr => ?_
    have e1 : ((K' (g * g'), (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J))) =
        (K' g, 1) * (K' g', 1) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    rw [← (hS (g * g') φ hφ).2 r hr, e1, map_mul, Module.End.mul_apply, (hS g' φ hφ).2 r hr,
      (hS g (S g' φ) (h1 g' φ hφ)).2 r (restS g' φ r hφ hr)]
  have h3 : ∀ φ ∈ GlobalTheory.WeilM.SB _, S 1 φ = φ := by
    intro φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ _ _ hφ fun r hr => ?_
    have e1 : ((K' 1, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J))) = 1 := by rw [map_one]; rfl
    rw [← (hS 1 φ hφ).2 r hr, e1, map_one, Module.End.one_apply]
  have hψ : Continuous Bs.ψ := hTr.base.std.1
  have atAct : ∀ g (γ : Matrix _ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) γ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁)
        (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (K' g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have h4 : ∀ g (γ : Matrix _ _ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) γ → ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
              (K' g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.SchrSB.schr_mem_SB Bs.ψ hψ Bs.v₁ (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq Bs.v₁ φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ r hr
    have hRw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁)
        (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.HeisSchA.rho_mem_schA Γ.M' Bs.ψ hTr.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  have h5 : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat Bs Γ X om om' hTr Bs.v₁ (K' g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ
  obtain ⟨ν, α, hν, hC⟩ := GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator Bs Γ X om om' hTr K' (fun g => hK g) S h1
    (fun g => linear_of_acts Bs.v₁ (om' (K' g, 1)) (S g) (hS g)) h2 h3 h4 h5
  exact ⟨ν, α, hν, fun ι hι g => ⟨K g, fun φ hφ r hr =>
    ⟨S g φ, h1 g φ hφ, (hS g φ hφ).2 r hr, hC ι hι g φ hφ⟩⟩⟩

end GlobalTheory.LocWeilAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeilStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodSplitPlace_translation_acts_through_weil : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G)
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om'),
    ∃ ν α : (Fv D.host.F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι : ((Fin (G.V (.grid i j)).rank × Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank) → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ]
              (Matrix (Fin (G.V (.grid i j)).rank) (Fin ((G.V (.grid (i + 1) (j + 1))).rank + (G.V (.grid i j)).rank)) (Fv D.host.F Bs.v₁) → ℂ),
      Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      ∀ g : GL (Fin (G.V (.grid i j)).rank) (Fv D.host.F Bs.v₁), ∃ k : GA D (G.V (.grid i j)),
        ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ r, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin D.host.F Bs.v₁) φ r → ∃ φ₁ ∈ GlobalTheory.WeilM.SB _,
          om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) φ r) =
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin D.host.F Bs.v₁) φ₁ r ∧ ι φ₁ = omB ν α g 1 (ι φ) := by
  first | exact @GlobalTheory.LocWeilAct.act_omB | exact GlobalTheory.LocWeilAct.act_omB | (intros; apply GlobalTheory.LocWeilAct.act_omB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EqCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsLevGrp {H : Host E} (l : Level H) {r : ℕ} (Y : Data E r) : Prop :=
  ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧
    (∀ x ∈ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • Y.Λ, ∃ y ∈ Y.Λ,
      (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.M • y) ∧
    (∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ, (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.A • y)

def IsSelfDualTr {r : ℕ} (Y : Data E r) : Prop :=
  ∀ x : Fin r → E, x ∈ Y.Λ ↔ ∀ y ∈ Y.Λ, ∃ n : ℤ, Algebra.trace ℚ E (-Y.ξ0 * herm Y.Gm x y) = n

end GlobalTheory.EqCovol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BigDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}


variable (G i j) in
abbrev Pt : Type := Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)


variable (G i j) in
abbrev Ix : Type := Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank)


variable (G i j) in
abbrev HomV : Type := WO (negSp (spW G i j)) (spV G i j)


variable (G i j) in
abbrev HomW : Type := WO (spV₁ G i j) (spW G i j)

abbrev mapV (e : Num G i j) (u : Pt G i j) : HomV G i j := mulG (negSp (spW G i j)) (colV e u)ᵀ

abbrev mapW (e : Num G i j) (u : Pt G i j) : HomW G i j := adjV₁ e u

theorem mulG_eq (S : HSp D) {n : ℕ} (y : Matrix (Fin n) (Fin S.rank) (AE D)) :
    mulG S y = HMul.hMul y (S.gram.map (incA D)) := rfl

def divG (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : Matrix (Fin n) (Fin S.rank) (AE D) :=
  HMul.hMul x ((S.gram⁻¹).map (incA D))

theorem divG_mulG (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : divG S (mulG S x) = x := by
  rw [divG, mulG_eq, Matrix.mul_assoc, mul_eq_one_comm.1 (GlobalTheory.RouteCoords.inv_mul_gram S), Matrix.mul_one]

theorem mulG_divG (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : mulG S (divG S x) = x := by
  rw [divG, mulG_eq, Matrix.mul_assoc, GlobalTheory.RouteCoords.inv_mul_gram S, Matrix.mul_one]

theorem mulG_add (S : HSp D) {n : ℕ} (x y : Matrix (Fin n) (Fin S.rank) (AE D)) : mulG S (x + y) = mulG S x + mulG S y :=
  Matrix.add_mul _ _ _

theorem mulG_smul (S : HSp D) {n : ℕ} (c : AF D.host.F) (x : Matrix (Fin n) (Fin S.rank) (AE D)) :
    mulG S (c • x) = c • mulG S x := Matrix.smul_mul _ _ _

def ofMaps (e : Num G i j) (x : HomV G i j × HomW G i j) : Pt G i j :=
  (fromCols (divG (negSp (spW G i j)) x.1)ᵀ ((divG (spV₁ G i j) (-x.2)).map (cA D))).submatrix id e.symm

theorem mapV_ofMaps (e : Num G i j) (x : HomV G i j × HomW G i j) : mapV e (ofMaps e x) = x.1 := by
  have h1 : (colV e (ofMaps e x))ᵀ = divG (negSp (spW G i j)) x.1 := Matrix.ext fun a b => by
    simp only [colV, ofMaps, transpose_apply, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl]
  exact (congrArg (mulG (negSp (spW G i j))) h1).trans (mulG_divG _ _)

theorem mapW_ofMaps (e : Num G i j) (x : HomV G i j × HomW G i j) : mapW e (ofMaps e x) = x.2 := by
  have h2 : ((ofMaps e x).submatrix id fun k => e (.inr k)).map (cA D) = divG (spV₁ G i j) (-x.2) := Matrix.ext fun a b => by
    simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply,
      GlobalTheory.DualPairCheck.cA_cA]
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h2).trans ((congrArg Neg.neg (mulG_divG _ _)).trans (neg_neg _))

theorem ofMaps_maps (e : Num G i j) (u : Pt G i j) : ofMaps e (mapV e u, mapW e u) = u := by
  have h1 : divG (negSp (spW G i j)) (mapV e u) = (colV e u)ᵀ := divG_mulG _ _
  have h2 : divG (spV₁ G i j) (-mapW e u) = (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    (congrArg (divG (spV₁ G i j)) (neg_neg _)).trans (divG_mulG _ _)
  ext a b
  obtain ⟨k | k, rfl⟩ := e.surjective b
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]
    exact congrFun (congrFun h1 k) a
  · simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]
    exact (congrArg (cA D) (congrFun (congrFun h2 a) k)).trans (GlobalTheory.DualPairCheck.cA_cA _)

theorem mapV_add (e : Num G i j) (u u' : Pt G i j) : mapV e (u + u') = mapV e u + mapV e u' :=
  mulG_add (negSp (spW G i j)) (colV e u)ᵀ (colV e u')ᵀ

theorem mapW_add (e : Num G i j) (u u' : Pt G i j) : mapW e (u + u') = mapW e u + mapW e u' := by
  have h : ((u + u').submatrix id fun k => e (.inr k)).map (cA D) =
      (u.submatrix id fun k => e (.inr k)).map (cA D) + (u'.submatrix id fun k => e (.inr k)).map (cA D) :=
    Matrix.ext fun a b => map_add (cA D) _ _
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h).trans ((congrArg Neg.neg (mulG_add _ _ _)).trans (neg_add _ _))

theorem mapV_smul (e : Num G i j) (c : AF D.host.F) (u : Pt G i j) : mapV e (c • u) = c • mapV e u :=
  mulG_smul (negSp (spW G i j)) c (colV e u)ᵀ

theorem mapW_smul (e : Num G i j) (c : AF D.host.F) (u : Pt G i j) : mapW e (c • u) = c • mapW e u := by
  have h : ((c • u).submatrix id fun k => e (.inr k)).map (cA D) = c • (u.submatrix id fun k => e (.inr k)).map (cA D) :=
    Matrix.ext fun a b => map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c _
  exact (congrArg (fun y => -mulG (spV₁ G i j) y) h).trans ((congrArg Neg.neg (mulG_smul _ _ _)).trans (smul_neg _ _).symm)

def maps (e : Num G i j) : Pt G i j ≃ₗ[AF D.host.F] HomV G i j × HomW G i j where
  toFun u := (mapV e u, mapW e u)
  invFun := ofMaps e
  map_add' u u' := Prod.ext (mapV_add e u u') (mapW_add e u u')
  map_smul' c u := Prod.ext (mapV_smul e c u) (mapW_smul e c u)
  left_inv := ofMaps_maps e
  right_inv x := Prod.ext (mapV_ofMaps e x) (mapW_ofMaps e x)

theorem maps_apply (e : Num G i j) (u : Pt G i j) : maps e u = (mapV e u, mapW e u) := rfl

abbrev sympPt (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (u u' : Pt G i j) : AF D.host.F :=
  symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) u u'


set_option maxHeartbeats 1000000 in
theorem symp_eq (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) (x x' : Pt G i j) :
    sympPt Γ x x' = symplO _ _ (mapV e x) (mapV e x') + symplO _ _ (mapW e x) (mapW e x') := by
  have hJW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      incA D D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map (incA D))ᵀ ((spV₁ G i j).gram.map (incA D))ᵀ := by
    have k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM Γ.W.J = incA D D.host.xi0 •
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (spV G i j).gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (spV₁ G i j).gramᵀ) := by
      rw [hWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul]
      congr 1
      exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_map _ _ _ (map_zero _)
    exact k
  have hJV : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J = (spW G i j).gram.map (incA D) := by
    rw [hW, one_smul]; rfl
  have hN : (negSp (spW G i j)).gram.map (incA D) = -(spW G i j).gram.map (incA D) := by
    rw [negSp_gram]; exact Matrix.map_neg _ (map_neg _) _
  have hA : hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x x' = _ :=
    GlobalTheory.RouteCoords.quadruple_sum_eq_trace_transpose_mul (cA D : AE D → AE D) _ _ _ _
  have hB1 : hO _ _ (mapV e x) (mapV e x') = _ :=
    GlobalTheory.RouteCoords.orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((negSp (spW G i j)).gram⁻¹).map (incA D))
      ((spV G i j).gram.map (incA D)) _ _
  have hB2 : hO _ _ (mapW e x) (mapW e x') = _ :=
    GlobalTheory.RouteCoords.orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((spV₁ G i j).gram⁻¹).map (incA D))
      ((spW G i j).gram.map (incA D)) _ _
  have h1 := GlobalTheory.RouteCoords.trace_first (cA D) ((negSp (spW G i j)).gram.map (incA D))
    (((negSp (spW G i j)).gram⁻¹).map (incA D)) ((spV G i j).gram.map (incA D)) (GlobalTheory.RouteCoords.gram_conj_transpose _)
    (GlobalTheory.RouteCoords.inv_mul_gram _) (colV e x) (colV e x')
  have h2 := GlobalTheory.RouteCoords.trace_second (cA D) GlobalTheory.DualPairCheck.cA_cA (incA D D.host.xi0) GlobalTheory.RouteCoords.adeleConj_incl_skewElement_eq_neg
    ((spW G i j).gram.map (incA D)) ((spV₁ G i j).gram.map (incA D)) (((spV₁ G i j).gram⁻¹).map (incA D))
    (GlobalTheory.RouteCoords.gram_conj_transpose _) (GlobalTheory.RouteCoords.gram_conj_transpose _) (GlobalTheory.RouteCoords.inv_mul_gram _)
    (x.submatrix id fun k => e (.inr k)) (x'.submatrix id fun k => e (.inr k))
  rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.neg_mul, trace_neg, mul_neg, map_neg, neg_eq_iff_eq_neg] at h2
  unfold sympPt symp symplO
  rw [hA, hB1, hB2]
  conv_rhs => arg 2; rw [← GlobalTheory.DualPairCheck.trace_cA]
  rw [← map_add (f := _)]
  congr 1
  erw [h2, h1]
  rw [hN, hJW, hJV, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    GlobalTheory.RouteCoords.mul_blk_mul_transpose, transpose_neg, Matrix.mul_neg, trace_smul, trace_neg, Matrix.add_mul, trace_add,
    submatrix_map, submatrix_map, smul_eq_mul]
  unfold colV
  ring

def box (e : Num G i j) (f₁ : HomV G i j → ℂ) (f₂ : HomW G i j → ℂ) (u : Pt G i j) : ℂ := f₁ (mapV e u) * f₂ (mapW e u)

def heisPt (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (u₀ : Pt G i j) (f : Pt G i j → ℂ) (u : Pt G i j) : ℂ :=
  ψ (⅟(2 : AF D.host.F) * sympPt Γ u u₀) * f (u + u₀)

theorem invOf_two : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one]

theorem heisPt_box (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) (ψ : AddChar (AF D.host.F) ℂ) (u₀ : Pt G i j)
    (f₁ : HomV G i j → ℂ) (f₂ : HomW G i j → ℂ) :
    heisPt Γ ψ u₀ (box e f₁ f₂) = box e (heisO ψ _ _ (mapV e u₀) f₁) (heisO ψ _ _ (mapW e u₀) f₂) := by
  funext u
  unfold heisPt box heisO symplOH
  rw [symp_eq e Γ hW hWW, mul_add, AddChar.map_add_eq_mul, mapV_add, mapW_add, invOf_two]
  ring

abbrev thetaPt (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (Ix G i j → AF D.host.F) → ℂ)
    (u : Pt G i j) : ℂ := thetaSum D.host.F (Γ.M.co.rho ψ u Φ)

theorem rho_rho {R W κ : Type} [CommRing R] [Invertible (2 : R)] [AddCommGroup W] [Module R W] {B : W → W → R} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar R ℂ) (u u₀ : W) (Φ : (κ → R) → ℂ) :
    co.rho ψ u (co.rho ψ u₀ Φ) = ψ (⅟(2 : R) * B u u₀) • co.rho ψ (u + u₀) Φ := by
  funext x
  simp only [Darboux.rho, schr, co.form, map_add (f := _), Prod.fst_add, Prod.snd_add, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-((co.e u).1 ⬝ᵥ (co.e u₀).2)) * invOf_two_add_invOf_two (R := R)

theorem thetaPt_rho (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (ψ : AddChar (AF D.host.F) ℂ) (Φ : (Ix G i j → AF D.host.F) → ℂ)
    (u₀ : Pt G i j) : thetaPt Γ ψ (Γ.M.co.rho ψ u₀ Φ) = heisPt Γ ψ u₀ (thetaPt Γ ψ Φ) :=
  funext fun u => (congrArg (thetaSum D.host.F) (rho_rho Γ.M.co ψ u u₀ Φ)).trans tsum_mul_left


variable (G i j) in
abbrev latV : AddSubgroup (HomV G i j) :=
  latO (negSp (spW G i j)) (spV G i j) (G.Λ (.grid (i + 1) (j + 1)) : Set _) (G.Λ (.grid i (j + 1)) : Set _) fun _ => True


variable (G i j) in
abbrev latW : AddSubgroup (HomW G i j) :=
  latO (spV₁ G i j) (spW G i j) (G.Λ (.grid (i + 1) j) : Set _) (G.Λ (.grid (i + 1) (j + 1)) : Set _) fun _ => True

def latPt (e : Num G i j) (v : Pl D.host.F) : AddSubgroup (Pt G i j) where
  carrier := {u | At (evFin D.host.F v) u ∧ mapV e u ∈ latV G i j ∧ mapW e u ∈ latW G i j}
  zero_mem' := ⟨fun u _ => smul_zero u, by
    rw [show mapV e 0 = 0 from congrArg Prod.fst (map_zero (maps e))]; exact zero_mem _, by
    rw [show mapW e 0 = 0 from congrArg Prod.snd (map_zero (maps e))]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨fun u hu => by rw [smul_add, ha.1 u hu, hb.1 u hu, add_zero],
    by rw [mapV_add]; exact add_mem ha.2.1 hb.2.1, by rw [mapW_add]; exact add_mem ha.2.2 hb.2.2⟩
  neg_mem' := fun {a} ha => ⟨fun u hu => by rw [smul_neg, ha.1 u hu, neg_zero], by
    rw [show mapV e (-a) = -mapV e a from congrArg Prod.fst (map_neg (maps e) a)]; exact neg_mem ha.2.1, by
    rw [show mapW e (-a) = -mapW e a from congrArg Prod.snd (map_neg (maps e) a)]; exact neg_mem ha.2.2⟩

def genPt (e : Num G i j) (v : Pl D.host.F) : Set (Pt G i j) :=
  {γ | (∃ γ' ∈ latPt e v, γ = 2 • γ') ∨ γ ∈ latPt e v ∧ ∃ ε, IsSplitIdem D ε ∧ γ ∈ mixHalf e ε}

theorem genPt_subset (e : Num G i j) (v : Pl D.host.F) : genPt e v ⊆ latPt e v := by
  rintro _ (⟨γ, h, rfl⟩ | h)
  exacts [nsmul_mem h 2, h.1]

def boxGraph (e : Num G i j) (ε : AE D) (T₁ : (HomV G i j → ℂ) →ₗ[ℂ] (HomV G i j → ℂ))
    (T₂ : (HomW G i j → ℂ) →ₗ[ℂ] (HomW G i j → ℂ)) : Submodule ℂ ((Pt G i j → ℂ) × (Pt G i j → ℂ)) :=
  Submodule.span ℂ {p | ∃ φ₁ φ₂, IsSBHalf ε (latV G i j) φ₁ ∧ IsSBHalf ε (latW G i j) φ₂ ∧
    p = (box e φ₁ φ₂, box e (T₁ φ₁) (T₂ φ₂))}

end GlobalTheory.BigDat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivariance
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolStabInf

open Formalism.BasicNotions.TH GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : piInf (τ w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) / (‖piInf (τ w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))‖ : ℂ) ≠ 0 := by
    have h0 : piInf (τ w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ≠ 0 := by
      intro e
      have := congrArg (piInf (τ w)) z.mul_inv
      rw [map_mul, e, zero_mul, map_one] at this
      exact zero_ne_one this
    exact div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0)
  rw [zpow_sub₀ this]

theorem locFin_fock1 (P Q R S : ℕ) (X : Mat P Q) (hX : IsKC X) (c : ℂ) :
    LocFin (fockAct1 P Q R S X + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs X hX y hy) (W.smul_mem c hy)⟩

theorem locFin_fock2 (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩


open scoped Classical in
theorem polStab : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    (∀ γ ∈ Lines σ G.V, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb) ∧
    (∀ k ∈ KInf σ G.V B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      Acts (evI F) (om (k, 1)) f f₁ → f₁ ∈ G.M.Pol B.ψ B.emb) ∧
    (∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ f₂ : SInf F (Fin a × Fin (a + a')),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₂ → f₂ = f₁) ∧
    (∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      Acts (evI F) (om (1, k)) f f₁ ∧ ∀ f₂ : SInf F (Fin a × Fin (a + a')), Acts (evI F) (om (1, k)) f f₂ → f₂ = f₁) := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' h
  obtain ⟨hb, hg, hc, hw, -⟩ := h
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hD := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hD
  have hfe := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hD
  have hsec := GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar hK.base hD hfe hvl (GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hK.base hD hvl)
  have hfst := GlobalTheory.T.lieFirst_of_lieSecond' hsec
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hD hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr
    hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1
    hc.expβ
  obtain ⟨d, hd, hB1⟩ := hwp.2.1
  have hW1 := hfst F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co d 1 Complex.I A C Φ _ _ _ hb.cm hb.std fr hΦ hd hB1
    (hasExp_div B.emb hc.expβ hc.expα)
  have hadm := fun g => (hwp.isUSplitting).adm g
  have hL := GlobalTheory.RealLift.actsLaws
  have mem : ∀ T, Φ T ∈ G.M.Pol B.ψ B.emb := fun T => hr ▸ LinearMap.mem_range_self Φ T
  have pol : ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ T, f = Φ T := fun f hf => by
    rw [← hr] at hf
    obtain ⟨T, rfl⟩ := hf
    exact ⟨T, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ hγ f hf f₁ h1
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨Yg, -, hY⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin a) _ _ B.emb (incM F G.V.J) 1 A hb.cm hA1 γ hγ
    have h2 := (hL F _ (Φ T) _ f₁).1 _ (fun t => map_zero _) (hW1 γ hγ Yg hY T)
    have e := (hL F _ (Φ T) _ f₁).2.2.1 _ h2 h1
    rw [← e]
    exact mem _
  · intro k hk f hf f₁ h1
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin a) _ _
      B.emb (incM F G.V.J) 1 A G.V.θ hb.cm hA1 hAθ k hk.1 hk.2
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F _ _ Φ _ ((om.comp (MonoidHom.inl _ _)).comp γ)
      (GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w => locFin_fock1 _ _ _ _ (Yg w) (hKC w) _) (fun t l hl => hadm _ l hl)
      (fun T => hW1 γ hγ Yg hgen T)
    have h2 := (hL F _ (Φ T) (Φ (U T)) f₁).2.1 _ (map_zero _) (hSA T)
    change Acts _ (om (MonoidHom.inl _ _ (γ (Multiplicative.ofAdd 1)))) _ _ at h2
    rw [hγ1] at h2
    have e := (hL F _ (Φ T) _ f₁).2.2.2.1 _ h2 h1
    rw [← e]
    exact mem _
  · intro γ hγ f hf
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨Yg, -, hY⟩ := GlobalTheory.T.oneParamSubgroup_generators_exist F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ
    have h2 := (hL F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) (hW2 γ hγ Yg hY T)
    exact ⟨_, mem _, h2, fun f₂ h3 => (hL F _ (Φ T) _ _).2.2.1 _ h3 h2⟩
  · intro k hk f hf
    obtain ⟨T, rfl⟩ := pol f hf
    obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.RealLift.exists_line_of_upq F E σ
      (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C G.W.θ hb.cm hC1 hCθ k hk.1 hk.2
    obtain ⟨U, -, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F _ _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ)
      (GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w => locFin_fock2 _ _ _ _ (Yg w) (hKC w) _) (fun t l hl => hadm _ l hl)
      (fun T => hW2 γ hγ Yg hgen T)
    have h2 := (hL F _ (Φ T) (Φ (U T)) (Φ (U T))).2.1 _ (map_zero _) (hSA T)
    change Acts _ (om (MonoidHom.inr _ _ (γ (Multiplicative.ofAdd 1)))) _ _ at h2
    rw [hγ1] at h2
    exact ⟨_, mem _, h2, fun f₂ h3 => (hL F _ (Φ T) _ _).2.2.2.1 _ h3 h2⟩

end GlobalTheory.PolStabInf

end
end
