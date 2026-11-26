module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentGroupPullbackEpsilonLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepApplyEqSmulOfHalfIndicatorBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLiftKodairaSpencerZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLiftKodairaSpencerZero
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSFull

theorem eq_lieComb {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ} {cf : Fin n → R}
    {v : Fin n → (epsR R ⟶ A)} {w : epsR R ⟶ A} (h : IsLieComb cf v w) : w = GlobalTheory.FlagTan.lieComb cf v := by
  obtain ⟨u, hu, rfl⟩ := h
  unfold GlobalTheory.FlagTan.lieComb
  congr 2
  funext i
  exact Over.OverMorphism.ext (hu i)

theorem eq_one_of_isLieComb_zero {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {n : ℕ}
    {v : Fin n → (epsR R ⟶ A)} (hv : ∀ i, IsTangent (v i)) {w : epsR R ⟶ A}
    (h : IsLieComb (fun _ => (0 : R)) v w) : w = 1 := by
  rw [eq_lieComb h]
  unfold GlobalTheory.FlagTan.lieComb
  simp [GlobalTheory.GrpTangent.epsScale_zero_comp (hv _)]

theorem isKSValue_one_sum {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    [GrpObj A'] {i : A.left ⟶ A'.left} {h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i} {J : Type} (s : Finset J)
    (c : J → K) (F : J → HdR A) (hF : ∀ k, IsKSValue h (F k) 1) : IsKSValue h (∑ k ∈ s, c k • F k) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, ⟨0, zero_mem _, fun _ => (LinearMap.zero_apply _).trans (by simp)⟩, isLieImage_one_iff.2 (zero_mem _)⟩
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    have := ((hF k).smul (c k)).add ih
    rwa [MonObj.comp_one, _root_.mul_one] at this

theorem isKSValue_one_of_rows {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))}
    [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (HdR A))
    (hiso : ∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) (hlag : ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A)
    (hperf : LinearMap.IsPerfPair ψ) (halt : ψ.IsAlt)
    (hsym : ∀ f g k k', IsFilLift h f k → IsFilLift h g k' → ψ f k' + ψ k g = 0)
    {Ι : Type} [Fintype Ι] {m : Ι → ℕ} (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A)
    (hl : ∀ k, IsLieImage (hb k) (ub k.1 k.2)) (hspan : Submodule.span K (Set.range hb) ⊔ Fil A = ⊤)
    (P : Ι → Prop) (cj : Ι → Ι) (hcj : ∀ σ, P σ → ¬ P (cj σ))
    (h0 : ∀ k : (Σ σ, Fin (m σ)), ¬ P k.1 → GlobalTheory.FlagTan.IsKSRow h ψ hb k 1)
    (h1 : ∀ k : (Σ σ, Fin (m σ)), P k.1 → ∃ cf w, IsLieComb cf (ub (cj k.1)) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb k w) :
    ∀ f ∈ Fil A, IsKSValue h f 1 := by
  classical

  have what₂ : ∀ k : (Σ σ, Fin (m σ)), ∃ f ∈ Fil A, (∀ k', ψ f (hb k') = if k' = k then 1 else 0) ∧
      ∃ kf, IsFilLift h f kf ∧ (¬ P k.1 → kf ∈ Fil A) ∧
        (P k.1 → ∃ cf : Fin (m (cj k.1)) → K, kf - ∑ b, cf b • hb ⟨cj k.1, b⟩ ∈ Fil A) := fun k => by
    by_cases hk : P k.1
    · obtain ⟨cf, w, hc, f, hf, hd, kf, hkf, hw⟩ := h1 k hk
      refine ⟨f, hf, fun k' => (hd k').trans (ite_congr rfl (fun _ => rfl) (fun _ => rfl)), kf, hkf,
        fun h' => absurd hk h', fun _ => ⟨cf, ?_⟩⟩
      have e := GlobalTheory.FlagTan.isLieImage_lieComb cf (fun b => hl ⟨cj k.1, b⟩)
      rw [← eq_lieComb hc] at e
      exact hw.sub_mem e
    · obtain ⟨f, hf, hd, kf, hkf, hw⟩ := h0 k hk
      exact ⟨f, hf, fun k' => (hd k').trans (ite_congr rfl (fun _ => rfl) (fun _ => rfl)), kf, hkf,
        fun _ => isLieImage_one_iff.1 hw, fun h' => absurd h' hk⟩
  choose F hF hδ kf hkf hk0 hk1 using what₂

  have zero : ∀ d ∈ Fil A, (∀ k, ψ d (hb k) = 0) → d = 0 := fun d hd h0 => by
    have hker : Submodule.span K (Set.range hb) ⊔ Fil A ≤ LinearMap.ker (ψ d) := by
      refine sup_le ((Submodule.span_le).2 ?_) fun g hg => hiso d hd g hg
      rintro _ ⟨k, rfl⟩
      exact h0 k
    have e : ψ d = 0 := LinearMap.ext fun x => hker (hspan ▸ Submodule.mem_top)
    exact hperf.bijective_left.1 (e.trans (map_zero ψ).symm)

  have span : ∀ g ∈ Fil A, g = ∑ k, ψ g (hb k) • F k := fun g hg => by
    refine (sub_eq_zero.1 (zero _ (sub_mem hg (sum_mem fun k _ => Submodule.smul_mem _ _ (hF k))) fun k' => ?_))
    have e : ∑ k, (ψ (ψ g (hb k) • F k)) (hb k') = ψ g (hb k') := by
      rw [Finset.sum_eq_single k' (fun b _ hb' => by
        rw [map_smul, LinearMap.smul_apply, hδ, if_neg (Ne.symm hb'), smul_zero]) (by simp)]
      rw [map_smul, LinearMap.smul_apply, hδ, if_pos rfl, smul_eq_mul, _root_.mul_one]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, e, sub_self]

  have key : ∀ k k', ψ (kf k) (F k') = 0 := fun k k' => by
    by_cases hk : P k.1
    · by_cases hk' : P k'.1
      · obtain ⟨cf, hcf⟩ := hk1 k hk
        have e1 := hiso _ hcf _ (hF k')
        rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e1
        set_option synthInstance.maxHeartbeats 100000 in
          rw [e1, map_sum, LinearMap.sum_apply]
        refine Finset.sum_eq_zero fun b _ => ?_
        have hne : (⟨cj k.1, b⟩ : Σ σ, Fin (m σ)) ≠ k' := fun e => hcj _ hk (by subst e; exact hk')
        rw [map_smul, LinearMap.smul_apply, ← LinearMap.IsAlt.neg halt (F k') _, hδ, if_neg hne, neg_zero,
          smul_zero]
      · have e1 := hsym _ _ _ _ (hkf k) (hkf k')
        rw [hiso _ (hF k) _ (hk0 k' hk'), zero_add] at e1
        exact e1
    · exact hiso _ (hk0 k hk) _ (hF k')
  have hone : ∀ k, IsKSValue h (F k) 1 := fun k =>
    ⟨kf k, hkf k, isLieImage_one_iff.2 (hlag _ fun g hg => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [span g hg, map_sum]
      exact Finset.sum_eq_zero fun k' _ => by rw [map_smul, key, smul_zero])⟩
  intro f hf
  rw [span f hf]
  exact isKSValue_one_sum _ _ _ hone

end GlobalTheory.KSFull

namespace GlobalTheory.KSFull

theorem conj_embK' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  show conjEmb τ ((H.bar z : 𝓞 E) : E) = τ (z : E)
  rw [H.bar_eq]
  simp [conjEmb, IsCMField.complexEmbedding_complexConj]

theorem ksFull : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧ ∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1 := by
  intro PP E _ _ _ H Dw l Xo c K _ _ y x' _ _ hKS
  obtain ⟨A, _, A', _, π, π', i, h, ψ, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hKS
  refine ⟨A, inferInstance, A', inferInstance, π, π', i, h, hπ, hπ', e, ?_⟩
  have P := PP.p5
  have hU := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  haveI : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc i π', e, ha z]
    · rw [Category.assoc, Category.assoc, Over.w, h.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ₀, hpol₀, hiso, hperf, hlag⟩ := GlobalTheory.PolExists.polForm_exists P Xo hπ
  obtain rfl : ψ = ψ₀ := IsPolForm.unique P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hpol hpol₀
  have hadj := GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action P Xo hπ a ha hpol
  have hK := GlobalTheory.DeRham.ksRegular_of_isAbelianScheme P h hA' gA'
  obtain ⟨ub₀, hu₀, ht₀, he₀, hbasis₀⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha
  obtain rfl : ub = ub₀ := by
    funext σ k
    apply ReciprocityTheory.ChartRestriction.G.PullbackSections.push_inj hπ
    apply Over.OverMorphism.ext
    change (ub σ k).left ≫ π = (ub₀ σ k).left ≫ π
    rw [hu, hu₀]
  have hl' : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), IsLieImage (hb k) (ub k.1 k.2) := fun k => hl k.1 k.2
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration P y hπ ub hu hb hl'
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hl' k).push (a.act z)
    rw [he₀] at h1
    exact h1.sub_mem ((hl' k).smul _)
  have hsym := GlobalTheory.T.tangent_group_pullback_epsilon_lift PP E H Dw l Xo K y.x x' A A' π π' i h ψ hπ hπ' e hpol
  refine isKSValue_one_of_rows h ψ hiso hlag hperf hpol.isAlt hsym ub hb hl' hspan
    (fun σ => σ ∈ GlobalTheory.FlagTan.psiSet H) conjEmb
    (fun σ hσ => ((GlobalTheory.FlagTan.isHalf_psiSet H) σ).1 hσ) ?_ ?_
  ·
    have key : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (j : Fin (Dw.mult (conjEmb τ.1))),
        GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, j⟩ 1 := fun τ j => by
      obtain ⟨w, hw, hr⟩ := hM τ j
      rwa [eq_one_of_isLieComb_zero (fun b => ht₀ τ.1 b) hw] at hr
    rintro ⟨σ, j⟩ hσ
    have hτ : conjEmb σ ∈ GlobalTheory.FlagTan.psiSet H := by
      rw [(GlobalTheory.FlagTan.isHalf_psiSet H) (conjEmb σ), GlobalTheory.AllWt.conjEmb_conjEmb]
      exact hσ
    suffices ∀ σ' (_ : conjEmb (conjEmb σ) = σ') (j' : Fin (Dw.mult σ')),
        GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨σ', j'⟩ 1 from this σ (GlobalTheory.AllWt.conjEmb_conjEmb σ) j
    intro σ' e'
    subst e'
    exact key ⟨conjEmb σ, hτ⟩
  ·
    rintro ⟨σ, j⟩ -
    exact GlobalTheory.KSExist.ksRow_exists_lieComb h a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift h a a' hc z hw)
      χ ub hb hspan hind heig hbasis₀ (conjEmb σ) σ
      (fun z => by
        simp only [χ, RingHom.comp_apply]
        rw [← conj_embK' c (conjEmb σ) z, GlobalTheory.AllWt.conjEmb_conjEmb]) j

end GlobalTheory.KSFull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLiftKodairaSpencerZeroStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_group_lift_kodaira_spencer_zero : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧ ∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1 := by
  first | exact @GlobalTheory.KSFull.ksFull | exact GlobalTheory.KSFull.ksFull | (intros; apply GlobalTheory.KSFull.ksFull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxGe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxGe
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem eq_zero_of_skew_of_I_smul_skew {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    (M : Matrix (Fin r) (Fin r) ℂ)
    (h1 : ∀ u w, hermC τ G (M *ᵥ u) w + hermC τ G u (M *ᵥ w) = 0)
    (h2 : ∀ u w, hermC τ G ((Complex.I • M) *ᵥ u) w + hermC τ G u ((Complex.I • M) *ᵥ w) = 0) :
    M = 0 := by
  have hl : ∀ (c : ℂ) v w, hermC τ G (c • v) w = c * hermC τ G v w := by
    intro c v w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hr : ∀ (c : ℂ) v w, hermC τ G v (c • w) = starRingEnd ℂ c * hermC τ G v w := by
    intro c v w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hA : ∀ u w, hermC τ G (M *ᵥ u) w = 0 := by
    intro u w
    have e1 := h1 u w
    have e2 := h2 u w
    rw [smul_mulVec, smul_mulVec, hl, hr, Complex.conj_I] at e2
    have : Complex.I * (2 * hermC τ G (M *ᵥ u) w) = 0 := by linear_combination e2 + Complex.I * e1
    simpa [Complex.I_ne_zero] using this
  have hGt : (G.map τ).det ≠ 0 := by
    have e := RingHom.map_det τ G
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]; exact (map_ne_zero τ).2 hG
  have hv : ∀ u, M *ᵥ u = 0 := by
    intro u
    refine Matrix.eq_zero_of_vecMul_eq_zero hGt ?_
    funext b
    have := hA u (Pi.single b 1)
    simpa [hermC, Matrix.vecMul, dotProduct, Pi.single_apply] using this
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem finrank_comap_realLie_le (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hr : 1 ≤ r) (hG : G.det ≠ 0) (hx : ∀ τ, (mat x τ).det ≠ 0) :
    Module.finrank ℝ ((realLie Ψ G).comap (fromFrame x)) ≤ Ψ.card * (r ^ 2 - 1) := by
  set W := (realLie Ψ G).comap (fromFrame x) with hW
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hsm : ∀ (c : ℂ) (V : EuclideanSpace ℂ (Ψ × Fin r × Fin r)),
      fromFrame x (c • V) = c • fromFrame x V := by
    intro c V
    funext τ
    have e : Matrix.of (fun a b => (c • V) (τ, a, b)) = c • Matrix.of (fun a b => V (τ, a, b)) := rfl
    show (mat x τ * Matrix.of (fun a b => (c • V) (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) =
      c • (mat x τ * Matrix.of (fun a b => V (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
    rw [e, Matrix.mul_smul, Matrix.smul_mul]
  have hIW : ∀ V, V ∈ W → Complex.I • V ∈ W → V = 0 := by
    intro V h1 h2
    have h1' : fromFrame x V ∈ realLie Ψ G := h1
    have h2' : fromFrame x (Complex.I • V) ∈ realLie Ψ G := h2
    rw [hsm] at h2'
    have hM : ∀ τ, Matrix.of (fromFrame x V τ) = 0 := fun τ =>
      eq_zero_of_skew_of_I_smul_skew hG _ (h1' τ).2 (h2' τ).2
    refine PiLp.ext fun p => ?_
    obtain ⟨τ, a, b⟩ := p
    have e : (mat x τ * Matrix.of (fun a b => V (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = 0 := hM τ
    have := key1 τ (Matrix.of (fun a b => V (τ, a, b)))
    rw [e, Matrix.mul_zero, Matrix.zero_mul] at this
    have := congrFun (congrFun this a) b
    simpa using this.symm
  let L : (W × W) →ₗ[ℝ] EuclideanSpace ℂ (Ψ × Fin r × Fin r) :=
    { toFun := fun p => (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) + Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r))
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
        rw [smul_comm] }
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have hp' : (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) + Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = 0 := hp
    have e1 : (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = Complex.I • ((-p.2 : W) : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) := by
      rw [Submodule.coe_neg, smul_neg]; exact eq_neg_of_add_eq_zero_left hp'
    have h3 : Complex.I • ((-p.2 : W) : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) ∈ W := e1 ▸ p.1.2
    have h4 := hIW _ (-p.2).2 h3
    have h5 : p.2 = 0 := by
      have : -p.2 = 0 := Subtype.ext h4
      simpa using this
    have h6 : p.1 = 0 := by
      apply Subtype.ext
      rw [e1, h4, smul_zero]; rfl
    exact Prod.ext h6 h5
  let tr : EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] (Ψ → ℂ) :=
    { toFun := fun Y τ => ∑ a, Y (τ, a, a)
      map_add' := by
        intro Y Z; funext τ; simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c Y; funext τ; simp [Finset.smul_sum] }
  have htrW : ∀ Y ∈ W, tr Y = 0 := by
    intro Y hY
    have hY' : fromFrame x Y ∈ realLie Ψ G := hY
    funext τ
    have ht := (hY' τ).1
    have e : Matrix.of (fromFrame x Y τ) = mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ := rfl
    rw [e, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ (hx τ).isUnit, Matrix.one_mul] at ht
    show ∑ a, Y (τ, a, a) = (0 : Ψ → ℂ) τ
    simpa [Matrix.trace] using ht
  have hrange : L.range ≤ LinearMap.ker tr := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.mem_ker]
    have e : L p = (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) + Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) := rfl
    rw [e, map_add (f := _)]
    have h2 : tr (Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r))) = Complex.I • tr p.2 := by
      funext τ; simp [tr, Finset.mul_sum]
    rw [h2, htrW _ p.1.2, htrW _ p.2.2, smul_zero, add_zero]
  have hsurj : LinearMap.range tr = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      if p.2.1 = ⟨0, hr⟩ ∧ p.2.2 = ⟨0, hr⟩ then c p.1 else 0), ?_⟩
    funext τ
    simp [tr]
  have hdimE : Module.finrank ℝ (EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = 2 * (Ψ.card * (r * r)) := by
    rw [(WithLp.linearEquiv 2 ℝ (Ψ × Fin r × Fin r → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Fintype.card_prod, Fintype.card_coe, mul_comm]
  have hdimP : Module.finrank ℝ (Ψ → ℂ) = 2 * Ψ.card := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Fintype.card_coe, mul_comm]
  have h1 := LinearMap.finrank_range_add_finrank_ker tr
  rw [hsurj, finrank_top, hdimE, hdimP] at h1
  have h2 := Submodule.finrank_mono hrange
  rw [LinearMap.finrank_range_of_inj hLinj, Module.finrank_prod] at h2
  have h3 : Ψ.card * (r ^ 2 - 1) = Ψ.card * (r * r) - Ψ.card := by
    rw [Nat.mul_sub_one, sq]
  rw [h3]
  omega

end GlobalTheory.CovTop.VolUp

namespace GlobalTheory.CovTop.VolUp

theorem riemLie_frameBox_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ((ε / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε} := by
  intro E _ _ _ r Ψ G x hr hG hx ε hε hε1
  set W := (realLie Ψ G).comap (fromFrame x) with hW
  unfold riemLie
  have hf : Measurable (fun Y : W => fromFrame x Y.1) :=
    ((fromFrame x).comp W.subtype).continuous_of_finiteDimensional.measurable
  refine le_trans ?_ (Measure.le_map_apply hf.aemeasurable _)
  rw [OrthonormalBasis.addHaar_eq_volume]
  have hdim := finrank_comap_realLie_le Ψ G x hr hG hx
  set N := Module.finrank ℝ W with hN
  obtain ⟨b⟩ : Nonempty (OrthonormalBasis (Fin N) ℝ W) := ⟨stdOrthonormalBasis ℝ W⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  set η : ℝ := ε / ((Ψ.card : ℝ) * (r : ℝ) ^ 2) with hη
  have hη0 : 0 ≤ η := by positivity
  have hcr : (N : ℝ) ≤ (Ψ.card : ℝ) * (r : ℝ) ^ 2 := by
    have : N ≤ Ψ.card * r ^ 2 := hdim.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    exact_mod_cast this
  have hη1 : η ≤ 1 := by
    rcases Nat.eq_zero_or_pos Ψ.card with h0 | h0
    · simp [hη, h0]
    · have : (1 : ℝ) ≤ (Ψ.card : ℝ) * (r : ℝ) ^ 2 := by
        have : 1 ≤ Ψ.card * r ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
        exact_mod_cast this
      exact div_le_one_of_le₀ (hε1.trans this) (by positivity)
  have hNη : (N : ℝ) * η ≤ ε := by
    calc (N : ℝ) * η ≤ ((Ψ.card : ℝ) * (r : ℝ) ^ 2) * η := mul_le_mul_of_nonneg_right hcr hη0
      _ ≤ ε := by
        rcases eq_or_ne ((Ψ.card : ℝ) * (r : ℝ) ^ 2) 0 with h0 | h0
        · rw [h0, zero_mul]; exact hε.le
        · rw [hη, mul_div_cancel₀ _ h0]
  let C : Set (Fin N → ℝ) := Set.univ.pi fun _ => Set.Ioo (-(η / 2)) (η / 2)
  have hmp : MeasurePreserving (fun Y : W => (b.repr Y).ofLp) volume volume :=
    (PiLp.volume_preserving_ofLp _).comp b.measurePreserving_repr
  have hC : volume ((fun Y : W => (b.repr Y).ofLp) ⁻¹' C) = ENNReal.ofReal η ^ N := by
    rw [hmp.measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo]
    simp [Finset.prod_const]
  calc ENNReal.ofReal (η ^ (Ψ.card * (r ^ 2 - 1))) = ENNReal.ofReal η ^ (Ψ.card * (r ^ 2 - 1)) :=
        ENNReal.ofReal_pow hη0 _
    _ ≤ ENNReal.ofReal η ^ N := pow_le_pow_right_of_le_one' (ENNReal.ofReal_le_one.2 hη1) hdim
    _ = volume ((fun Y : W => (b.repr Y).ofLp) ⁻¹' C) := hC.symm
    _ ≤ _ := by
      refine measure_mono fun Y hY => ?_
      simp only [Set.mem_preimage, C, Set.mem_pi, Set.mem_univ, Set.mem_Ioo, true_implies] at hY
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      intro τ a c
      have e : Matrix.of (fromFrame x Y.1 τ) =
          mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ := rfl
      rw [e, key1]
      have h1 : ‖(Y.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, c)‖ ≤ ‖Y‖ := PiLp.norm_apply_le _ _
      have h2 : ‖Y‖ ≤ ∑ i, |(b.repr Y).ofLp i| := by
        calc ‖Y‖ = ‖∑ i, (b.repr Y).ofLp i • b i‖ := by rw [b.sum_repr]
          _ ≤ ∑ i, ‖(b.repr Y).ofLp i • b i‖ := norm_sum_le _ _
          _ = ∑ i, |(b.repr Y).ofLp i| := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs]
      have h3 : ∑ i, |(b.repr Y).ofLp i| ≤ (N : ℝ) * (η / 2) := by
        calc ∑ i, |(b.repr Y).ofLp i| ≤ ∑ _i : Fin N, η / 2 :=
              Finset.sum_le_sum fun i _ => (abs_lt.2 (hY i)).le
          _ = (N : ℝ) * (η / 2) := by simp
      simp only [Matrix.of_apply]
      linarith

end GlobalTheory.CovTop.VolUp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxGeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianLieMeasure_frameBox_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ((ε / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε} := by
  first | exact @GlobalTheory.CovTop.VolUp.riemLie_frameBox_ge | exact GlobalTheory.CovTop.VolUp.riemLie_frameBox_ge | (intros; apply GlobalTheory.CovTop.VolUp.riemLie_frameBox_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellsFramesTriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellsFramesTriangular
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem tri_of_cols {L : Type} [CommRing L] {n m : ℕ} (U : Matrix (Fin n) (Fin m) L) (Wm : Matrix (Fin m) (Fin n) L)
    (hWU : Wm * U = 1) (V : Matrix (Fin n) (Fin m) L)
    (h : ∀ j, ∃ a : Fin m → L, (∀ i, j < i → a i = 0) ∧ (fun r => V r j) = U.mulVec a) :
    V = U * (Wm * V) ∧ ∀ i j, j < i → (Wm * V) i j = 0 := by
  choose a ha hV using h
  have hc : ∀ j, (fun i => (Wm * V) i j) = a j := fun j => by
    have e : (fun i => (Wm * V) i j) = Wm.mulVec (fun r => V r j) := by
      funext i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e, hV j, Matrix.mulVec_mulVec, hWU, Matrix.one_mulVec]
  refine ⟨?_, fun i j hij => ?_⟩
  · ext r j
    have e1 := congrFun (hV j) r
    have e2 : (U * (Wm * V)) r j = U.mulVec (fun i => (Wm * V) i j) r := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [e2, hc j]
    exact e1
  · exact (congrFun (hc j) i).trans (ha j i hij)

theorem spMap_comp_spMap {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} {A : Atlas Y p}
  {Z : Scheme.{0}} {π : Z ⟶ Y.X} {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)]

theorem comp_base (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) {L : Type} [CommRing L] (z : Sp L ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) :
    z ≫ π = spMap (((ev z _ hz).comp (cellθ κ k).toRingHom).comp (cC A k.1)) ≫ tau (A.V k.1).2 := by
  conv_lhs => rw [← eq_spMap_ev k z hz]
  rw [Category.assoc, hZ.plk.base, cbase, ← Category.assoc, spMap_comp_spMap]
  rfl

theorem le_comp_base (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) {L : Type} [CommRing L] (z : Sp L ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (A.V k.1).1 := by
  rw [comp_base hZ k z hz]
  exact le_preimage_comp _ (tau_le _ le_rfl)

theorem ev_comp_base (hZ : Cells A π g κ) (k : A.B × Pm Dw.mult) {L : Type} [CommRing L] (z : Sp L ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) (h : ⊤ ≤ (z ≫ π) ⁻¹ᵁ (A.V k.1).1) :
    ev (z ≫ π) _ h = ((ev z _ hz).comp (cellθ κ k).toRingHom).comp (cC A k.1) := by
  rw [ev_congr (comp_base hZ k z hz) _ h (by rw [← comp_base hZ k z hz]; exact h)]
  exact ev_spMap_tau _ _ _

theorem ne_zero_of_span_eq_top {L ι : Type} [Field L] [Fintype ι] {v : ι → L} (h : Ideal.span (Set.range v) = ⊤) :
    v ≠ 0 := by
  rintro rfl
  have h2 : (1 : L) ∈ Ideal.span (Set.range (0 : ι → L)) := h ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h2
  simp at hc

theorem col_tri (hZ : Cells A π g κ) (k k' : A.B × Pm Dw.mult) (σ : E →+* ℂ) {L : Type} [Field L] (z : Sp L ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ (κ k.1 k.2).opensRange) (hz' : ⊤ ≤ z ⁻¹ᵁ (κ k'.1 k'.2).opensRange)
    (hM : ⊤ ≤ (z ≫ π) ⁻¹ᵁ ((A.k k.1).M.U ⊓ (A.k k'.1).M.U)) (j : Fin (Dw.mult σ)) :
    ∃ a : Fin (Dw.mult σ) → L, (∀ i, j < i → a i = 0) ∧
      ((chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev (z ≫ π) _ hM)).mulVec
        (fun s => ((ev z _ hz').comp (cellθ κ k').toRingHom) (uC A k'.1 k'.2 σ s j)) =
      ((uC A k.1 k.2 σ).map ((ev z _ hz).comp (cellθ κ k).toRingHom)).mulVec a := by
  classical
  have span_range_comp_eq_top : ∀ {A B : Type} [CommRing A] [CommRing B] {n : ℕ}
      (v : Fin (n + 1) → A), Ideal.span (Set.range v) = ⊤ → (ψ : A →+* B) →
      Ideal.span (Set.range (ψ ∘ v)) = ⊤ := by
    intro A B _ _ n v hv ψ
    rw [Set.range_comp, ← Ideal.map_span, hv, Ideal.map_top]
  have spMap_pt : ∀ {O A B : Type} [CommRing O] [CommRing A] [CommRing B] {n : ℕ}
      (c : O →+* A) (v : Fin (n + 1) → A) (hv : Ideal.span (Set.range v) = ⊤) (ψ : A →+* B),
      spMap ψ ≫ pt c v hv = pt (ψ.comp c) (ψ ∘ v) (span_range_comp_eq_top v hv ψ) := by
    intro O A B _ _ _ n c v hv ψ
    letI := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := O)
    refine (ProjPoint.SpecMap_ofHom _ _ _ ψ).trans ?_
    unfold pt
    congr 1
    exact MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  have pt_str : ∀ {O A : Type} [CommRing O] [CommRing A] {N : ℕ}
      (c : O →+* A) (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤),
      pt c v hv ≫ PSpace.str O N = spMap c := by
    intro O A _ _ N c v hv
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r
  have hx := le_comp_base hZ k z hz
  have hx' := le_comp_base hZ k' z hz'
  have ex := ev_comp_base hZ k z hz hx
  have ex' := ev_comp_base hZ k' z hz' hx'
  have ez := eq_spMap_ev k z hz
  have ez' := eq_spMap_ev k' z hz'
  obtain ⟨a0, ha0⟩ := A.tw L (z ≫ π) k'.1 k.1 hx' hx hM
  rw [ex, ex'] at ha0
  generalize (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev (z ≫ π) _ hM) = Chx at ha0 ⊢
  generalize (ev z _ hz).comp (cellθ κ k).toRingHom = ψ at ez ha0 ⊢
  generalize (ev z _ hz').comp (cellθ κ k').toRingHom = ψ' at ez' ha0 ⊢
  have hj : j.1 + 1 ≤ Dw.mult σ := j.2
  obtain ⟨hu, hp⟩ := hZ.plk.plk k.1 k.2 (stdEn σ (j.1 + 1) hj)
  obtain ⟨hu', hp'⟩ := hZ.plk.plk k'.1 k'.2 (stdEn σ (j.1 + 1) hj)
  have e1 : z ≫ g (stdEn σ (j.1 + 1) hj) = pt (ψ.comp ((MvPolynomial.C).comp ((A.alpha k.1).comp (RingHom.id c.F))))
      (ψ ∘ plk (uvec (A.cv k.1) k.2) (std σ (j.1 + 1) hj)) (span_range_comp_eq_top _ hu ψ) := by
    rw [← ez, Category.assoc, hp, spMap_pt]
  have e2 : z ≫ g (stdEn σ (j.1 + 1) hj) = pt (ψ'.comp ((MvPolynomial.C).comp ((A.alpha k'.1).comp (RingHom.id c.F))))
      (ψ' ∘ plk (uvec (A.cv k'.1) k'.2) (std σ (j.1 + 1) hj)) (span_range_comp_eq_top _ hu' ψ') := by
    rw [← ez', Category.assoc, hp', spMap_pt]
  have ec : ψ.comp ((MvPolynomial.C).comp ((A.alpha k.1).comp (RingHom.id c.F))) =
      ψ'.comp ((MvPolynomial.C).comp ((A.alpha k'.1).comp (RingHom.id c.F))) := by
    have := congrArg (· ≫ PSpace.str c.F _) (e1.symm.trans e2)
    simp only [pt_str] at this
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  obtain ⟨u, hu2⟩ := (pt_eq_pt_iff _ (span_range_comp_eq_top _ hu ψ) (span_range_comp_eq_top _ hu' ψ')).1
    (e1.symm.trans (e2.trans (congrArg (fun c => pt c _ _) ec.symm)))
  let cv : Fin (j.1 + 1) → Fin (A.N + 1) → L := fun l => ψ ∘ uvec (A.cv k.1) k.2 (std σ (j.1 + 1) hj l)
  let cv' : Fin (j.1 + 1) → Fin (A.N + 1) → L := fun l => ψ' ∘ uvec (A.cv k'.1) k'.2 (std σ (j.1 + 1) hj l)
  have hpl : plk cv' id = (u : L) • plk cv id := by
    have := hu2
    rw [map_plk, map_plk, Units.smul_def] at this
    exact this
  have h0 : plk cv' id ≠ 0 := fun h =>
    ne_zero_of_span_eq_top (span_range_comp_eq_top _ hu' ψ') (by rw [map_plk]; exact h)
  have hmem := mem_span_of_plk_eq_smul L A.N (j.1 + 1) cv cv' u h0 hpl (Fin.last j.1)
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hmem
  have hcol : ∀ (b : A.B) (w : Pm Dw.mult) (φ : CR Dw.mult (A.V b) →+* L) (i : Fin (Dw.mult σ)),
      (fun r => φ (uvec (A.cv b) w ⟨σ, i⟩ r)) =
        ((A.A b).map (φ.comp (cC A b))).mulVec (((uC A b w σ).map φ).mulVec (Pi.single i 1)) := by
    intro b w φ i
    funext r
    rw [uvec_cv, Matrix.mulVec_single_one]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum]
  let av : Fin (Dw.mult σ) → L := ∑ l, f l • Pi.single (Fin.castLE hj l) 1
  have hq : (fun s => ψ' (uC A k'.1 k'.2 σ s j)) = ((uC A k'.1 k'.2 σ).map ψ').mulVec (Pi.single j 1) := by
    funext s
    rw [Matrix.mulVec_single_one]
    rfl
  have hL : ∑ l, f l • cv l = ((A.A k.1).map (ψ.comp (cC A k.1))).mulVec (((uC A k.1 k.2 σ).map ψ).mulVec av) := by
    simp only [cv, av, Matrix.mulVec_sum, Matrix.mulVec_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact congrArg _ (hcol k.1 k.2 ψ (Fin.castLE hj l))
  have hR : cv' (Fin.last j.1) = (a0 : L) • ((A.A k.1).map (ψ.comp (cC A k.1))).mulVec
      (Chx.mulVec (fun s => ψ' (uC A k'.1 k'.2 σ s j))) := by
    have e : Fin.castLE hj (Fin.last j.1) = j := Fin.ext rfl
    have := hcol k'.1 k'.2 ψ' j
    rw [← hq, ha0, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec] at this
    simp only [cv', std, e]
    exact this
  have hCA : (A.C k.1).map (ψ.comp (cC A k.1)) * (A.A k.1).map (ψ.comp (cC A k.1)) = 1 := by
    rw [← Matrix.map_mul, A.CA, Matrix.map_one _ (map_zero _) (map_one _)]
  have hC : ∀ v, ((A.C k.1).map (ψ.comp (cC A k.1))).mulVec (((A.A k.1).map (ψ.comp (cC A k.1))).mulVec v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, hCA, Matrix.one_mulVec]
  have key := congrArg ((A.C k.1).map (ψ.comp (cC A k.1))).mulVec (hf.trans hR)
  rw [hL, Matrix.mulVec_smul, hC, hC] at key
  refine ⟨((a0⁻¹ : Lˣ) : L) • av, fun i hi => ?_, ?_⟩
  · simp only [av, Pi.smul_apply, Finset.sum_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_zero fun l _ => ?_, mul_zero]
    rw [if_neg, mul_zero]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.coe_castLE] at this
    have := l.2
    omega
  · rw [Matrix.mulVec_smul, key, smul_smul, Units.inv_mul, one_smul]

theorem isReduced_of_cells (hZ : Cells A π g κ) : IsReduced Z := by
  have : ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) := fun x => by
    have := (hZ.normal x).1
    infer_instance
  exact isReduced_of_isReduced_stalk _

theorem flagCells_frames_triangular_common (hZ : Cells A π g κ) : FlagCellFrameChangeTriangular hZ := by
  haveI := isReduced_of_cells hZ
  intro k k' σ
  have hle : (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ π ⁻¹ᵁ ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) :=
    inf_le_inf (cell_le hZ k) (cell_le hZ k')
  let Cm := (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map
    (π.appLE ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) ((κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange) hle).hom
  let U' := ((uC A k'.1 k'.2 σ).map (cellθ κ k')).map (resG Z (inf_le_right :
    (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ _))
  let U := ((uC A k.1 k.2 σ).map (cellθ κ k)).map (resG Z (inf_le_left :
    (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ _))
  let Wm := ((wC A k.1 k.2 σ).map (cellθ κ k)).map (resG Z (inf_le_left :
    (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange ≤ _))
  have hWU : Wm * U = 1 := by
    simp only [Wm, U]
    rw [← Matrix.map_mul, ← Matrix.map_mul, wC_mul_uC, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have key : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z)
      (hz : ⊤ ≤ z ⁻¹ᵁ ((κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange)),
      (Cm * U').map (ev z _ hz) = U.map (ev z _ hz) * (Wm * (Cm * U')).map (ev z _ hz) ∧
        ∀ i j, j < i → (Wm * (Cm * U')).map (ev z _ hz) i j = 0 := by
    intro L _ z hz
    have hz1 := le_preimage_mono inf_le_left hz
    have hz2 := le_preimage_mono inf_le_right hz
    have hM := le_preimage_map π hle hz
    have eC : Cm.map (ev z _ hz) = (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map (ev (z ≫ π) _ hM) := by
      ext r s
      exact ev_appLE z π hle hz hM _
    have eU : U.map (ev z _ hz) = (uC A k.1 k.2 σ).map ((ev z _ hz1).comp (cellθ κ k).toRingHom) := by
      ext r s
      exact ev_res z _ hz hz1 _
    have eU' : U'.map (ev z _ hz) = (uC A k'.1 k'.2 σ).map ((ev z _ hz2).comp (cellθ κ k').toRingHom) := by
      ext r s
      exact ev_res z _ hz hz2 _
    have h := tri_of_cols (U.map (ev z _ hz)) (Wm.map (ev z _ hz))
      (by rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero _) (map_one _)]) ((Cm * U').map (ev z _ hz))
      (fun j => by
        obtain ⟨a, ha, e⟩ := col_tri hZ k k' σ z hz1 hz2 hM j
        refine ⟨a, ha, ?_⟩
        rw [eU, ← e, Matrix.map_mul, eC, eU']
        funext r
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct])
    rw [show (Wm * (Cm * U')).map (ev z _ hz) = Wm.map (ev z _ hz) * (Cm * U').map (ev z _ hz) from Matrix.map_mul]
    exact h
  refine ⟨Wm * (Cm * U'), fun i j hij => ext_ev_field fun L _ z hz => ?_, ?_⟩
  · rw [map_zero]
    exact (key L z hz).2 i j hij
  · ext r s
    refine ext_ev_field fun L _ z hz => ?_
    have := congrFun (congrFun (key L z hz).1 r) s
    rw [← Matrix.map_mul] at this
    exact this

end GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), FlagCellFrameChangeTriangular hZ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hZ => GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular_common hZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellsFramesTriangularStatement
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagCellFrameChangeTriangular_of_cells : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ), FlagCellFrameChangeTriangular hZ := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular | exact GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular | (intros; apply GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIntZNonnegAway
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat GlobalTheory.ShortBound
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace GlobalTheory.CovInt


set_option maxHeartbeats 1000000 in
theorem smul_intZ_nonneg_away : ∀ (D : D7) (H : Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ)
    (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ →
    (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ = 1) →
    (∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) → d.l₂.M ≠ 0 →
    ∀ (Λ : GenLat D.host.E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M →
    ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w →
    ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g →
    ∀ la : HeightOneSpectrum (𝓞 c.F), (∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → ¬ ℓ ^ 2 ∣ d.l₂.M) →
    ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v ((betaH (Dw := Dw) c Λ * (intZ D Dw d.l₂ n w : c.F)) • g) := by
  intro D H Dw l Xo c n d _ hlev hnab hroot hwi hM0 Λ N hU hTM hN w P hP x0 g hsec hR la hla v hv
  have hroot1 : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k),
      evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1 := fun k _ _ y₂ => by rw [pow_one]; exact hroot k y₂
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    exacts [h.choose_spec.1, one_ne_zero]
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℕ, P₀ = (NumberField.discr D.host.E).natAbs := ⟨_, rfl⟩
  have hP0 : P₀ ≠ 0 := hP₀ ▸ Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = P₀ ^ Formalism.L2.Pj.DF Dw w * d.l₂.M ^ Formalism.L2.Pj.DF Dw w *
    Nat.card (Fin n → LevQ Dw d.l₂) := ⟨_, rfl⟩
  have hK0 : K ≠ 0 := hK ▸ mul_ne_zero (mul_ne_zero (pow_ne_zero _ hP0) (pow_ne_zero _ hM0)) hc0
  have hKZ : intZ D Dw d.l₂ n w = K := by rw [intZ, hK, hP₀]; ring
  rw [hKZ, mul_comm]
  obtain ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩ := hv
  show 0 ≤ nval Tc.V e (evI yI _)
  rw [evI_smul]
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot1 Λ N hU hTM hN w P hP x0 g hsec hR
      Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have heR : (0 : ℝ) < ((r * e : ℕ) : ℝ) := by exact_mod_cast he'
  rw [← nval_bc iT hr hiT e, map_mul, hval, ← hio]
  obtain ⟨ℓ, hℓ, hu⟩ := GlobalTheory.ShortBound.exists_resChar T' hfr
  have hmem : (ℓ : 𝓞 c.F) ∈ la.asIdeal := by
    by_contra hnm
    have h2 := ho'.2 (ℓ : c.F)
    have hv1 : la.valuation c.F (ℓ : c.F) = 1 := by
      rw [← map_natCast (algebraMap (𝓞 c.F) c.F)]
      exact la.valuation_eq_one_iff_notMem.2 hnm
    have hv0 : vLa la (ℓ : c.F) = 0 := by simp [vLa, hv1]
    rw [map_natCast, hv0, mul_zero] at h2
    have h0 : (ℓ : T'.V) ≠ 0 := fun h0 => by
      have : algebraMap T'.V T'.Fr (ℓ : T'.V) = 0 := by rw [h0, map_zero]
      rw [map_natCast] at this
      exact hℓ.ne_zero (by exact_mod_cast this)
    have h3 := GlobalTheory.PlaceExtField.vV_pos (K' := T'.Fr) h0 hu
    rw [map_natCast] at h3
    omega
  have hsq : ¬ ℓ ^ 2 ∣ d.l₂.M := hla ℓ hℓ hmem
  obtain ⟨α, hαM, hα⟩ : ∃ α : ℕ, α ∣ d.l₂.M ∧ ((¬ ℓ ∣ d.l₂.M ∧ (α : 𝓞 D.host.E) = 1) ∨
      (ℓ ∣ d.l₂.M ∧ (α : 𝓞 D.host.E) * H.bar α = (ℓ : 𝓞 D.host.E) ∧ d.l₂.Mb ≤ Ideal.span {H.bar α}) ∨
      (ℓ ∣ d.l₂.M ∧ (α : 𝓞 D.host.E) = (ℓ : 𝓞 D.host.E))) := by
    by_cases hd : ℓ ∣ d.l₂.M
    · exact ⟨ℓ, hd, Or.inr (Or.inr ⟨hd, rfl⟩)⟩
    · exact ⟨1, one_dvd _, Or.inl ⟨hd, Nat.cast_one⟩⟩
  obtain ⟨α', hα'⟩ := hαM
  have ha0 : α ≠ 0 := left_ne_zero_of_mul (hα' ▸ hM0)
  have ha0' : α' ≠ 0 := right_ne_zero_of_mul (hα' ▸ hM0)
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  haveI := Nat.finite_of_card_ne_zero hc0
  have hu0 : io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E)) ≠ 0 :=
    (map_ne_zero io₂).2 (nrm_ne_zero _ _ (Nat.cast_ne_zero.2 ha0))
  have key := le_nval_avg (V := T'.V) (r * e) (fun q => io₂ (d.w x0 q)) _ ζ _
    ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) _ 1 one_pos hζ hu0 (by exact_mod_cast hc0)
    (fun q => map_isIntegral_int io₂ (hwi x0 q)) _
    (fun q => GlobalTheory.SupFull.class_bound d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he' hch ℓ hℓ
      hu Λ N hU hTM hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi
      (fun b => levRep (q b)) (htp q) (hF q) hrat hsq α hα)
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hKv := add_le_add (le_refl (nval T'.V (r * e) (K : T'.Fr))) key
  rw [← nval_mul, nval_of_ne (Nat.cast_ne_zero.2 hK0), ← EReal.coe_add] at hKv
  refine le_trans (EReal.coe_nonneg.2 ?_) (hKv.trans (le_of_eq ?_))
  · have b0 : ∀ p : ℕ, (0 : ℝ) ≤ vV T'.V (p : T'.Fr) := fun p => by
      exact_mod_cast GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T' p
    have b1 : (vV T'.V (K : T'.Fr) : ℝ) = (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (P₀ : T'.Fr) : ℝ) +
        (Formalism.L2.Pj.DF Dw w : ℕ) * ((vV T'.V (α : T'.Fr) : ℝ) + vV T'.V (α' : T'.Fr)) +
        vV T'.V ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) := by
      rw [hK, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
        vV_mul (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hP0)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hM0)))
          (Nat.cast_ne_zero.2 hc0),
        vV_mul (pow_ne_zero _ (Nat.cast_ne_zero.2 hP0)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hM0)),
        vV_pow (Nat.cast_ne_zero.2 hP0), vV_pow (Nat.cast_ne_zero.2 hM0)]
      conv_lhs => rw [show ((d.l₂.M : ℕ) : T'.Fr) = (α : T'.Fr) * (α' : T'.Fr) by rw [hα', Nat.cast_mul],
        vV_mul (Nat.cast_ne_zero.2 ha0) (Nat.cast_ne_zero.2 ha0')]
      push_cast
      ring
    have b2 : (vV T'.V (io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E))) : ℝ) = (Formalism.L2.Pj.DF Dw w : ℕ) * vV T'.V (α : T'.Fr) := by
      rw [nrm_nat, map_pow, map_natCast, vV_pow (Nat.cast_ne_zero.2 ha0)]
      push_cast
      ring
    have b3 : ∑ p ∈ D.host.condN.primeFactors, (vV T'.V (p : T'.Fr) : ℝ) / (r * e : ℕ) *
        D.host.vdH p * (Formalism.L2.Pj.DF Dw w : ℝ) / 2 ≤ (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (P₀ : T'.Fr) : ℝ) / (r * e : ℕ) := by
      have h := ram_sum_le_vV_discr D.host.E T' _ (fun p (hp : p ∈ D.host.condN.primeFactors) => Nat.prime_of_mem_primeFactors hp)
        (r * e) (Formalism.L2.Pj.DF Dw w)
      rw [← hP₀, Nat.cast_pow, vV_pow (Nat.cast_ne_zero.2 hP0), Int.cast_mul, Int.cast_natCast] at h
      rw [hP₀] at h ⊢
      exact h
    have b4 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (α' : T'.Fr) : ℝ) / (r * e : ℕ) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (b0 _)) heR.le
    rw [b1, b2, add_div, add_div, mul_add, add_div]
    linarith
  · congr 1
    simp only [map_mul, map_inv₀, map_natCast]
    field_simp

end GlobalTheory.CovInt
end
end
