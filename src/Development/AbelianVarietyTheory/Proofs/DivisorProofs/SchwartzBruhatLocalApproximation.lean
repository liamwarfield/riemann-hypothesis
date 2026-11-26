module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorEighth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedCharacterGood
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterLocalGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingIntegral
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblDiag

section Groups

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {β : Type} [Fintype β] [DecidableEq β]
  {J : Matrix β β E}

theorem fromBlocks_unit_left (k : UG c J) : (Matrix.fromBlocks ((k : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J *
    (Matrix.fromBlocks ((k : GL β E) : Matrix β β E) 0 0 1).map c = dbl J := by
  have hk : ((k : GL β E) : Matrix β β E)ᵀ * J * ((k : GL β E) : Matrix β β E).map c = J := k.2
  have h1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.map_zero _ (map_zero c), h1, Matrix.one_mul, Matrix.mul_one, hk]

theorem fromBlocks_unit_right (k : UG c J) : (Matrix.fromBlocks 1 0 0 ((k : GL β E) : Matrix β β E))ᵀ * dbl J *
    (Matrix.fromBlocks 1 0 0 ((k : GL β E) : Matrix β β E)).map c = dbl J := by
  have hk : ((k : GL β E) : Matrix β β E)ᵀ * J * ((k : GL β E) : Matrix β β E).map c = J := k.2
  have hn : ((k : GL β E) : Matrix β β E)ᵀ * (-J) * ((k : GL β E) : Matrix β β E).map c = -J := by
    rw [Matrix.mul_neg, Matrix.neg_mul, hk]
  have h1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.map_zero _ (map_zero c), h1, Matrix.one_mul, Matrix.mul_one, hn]

def diagL (k : UG c J) : UG c (dbl J) :=
  ⟨⟨Matrix.fromBlocks ((k : GL β E) : Matrix β β E) 0 0 1, Matrix.fromBlocks (((k : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1,
    by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one],
    by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]⟩, fromBlocks_unit_left c k⟩

def diagR (k : UG c J) : UG c (dbl J) :=
  ⟨⟨Matrix.fromBlocks 1 0 0 ((k : GL β E) : Matrix β β E), Matrix.fromBlocks 1 0 0 (((k : GL β E)⁻¹ : GL β E) : Matrix β β E),
    by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one],
    by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]⟩, fromBlocks_unit_right c k⟩

end Groups

section Local

variable {F : Type} [Field F] [NumberField F]

theorem boxFun_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem conj_mem_SB {Y : Type} [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => starRingEnd ℂ (φ y)) ∈ SB Y :=
  ⟨h.1.comp _, h.2.comp_left (map_zero _)⟩

theorem tens_boxFun (v : Pl (F := F)) {κ κ' : Type} (φ₁ : (κ → Fv F v) → ℂ) (φ₂ : (κ' → Fv F v) → ℂ)
    (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens (evFin F v) φ₁ r₁) (tens (evFin F v) φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

theorem rest_boxFun (v : Pl (F := F)) {κ κ' : Type} [Fintype κ] [Fintype κ'] {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ}
    {r₁ : (κ → AF F) → ℂ} {r₂ : (κ' → AF F) → ℂ} (h₁ : Rest (evFin F v) φ₁ r₁) (h₂ : Rest (evFin F v) φ₂ r₂) :
    Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) := by
  refine ⟨fun x z hz => ?_, ?_⟩
  · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inl i)
    have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inr i)
    show r₁ ((x + z) ∘ Sum.inl) * r₂ ((x + z) ∘ Sum.inr) = r₁ (x ∘ Sum.inl) * r₂ (x ∘ Sum.inr)
    rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
      show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, h₁.1 _ _ hz1, h₂.1 _ _ hz2]
  · rw [tens_boxFun]
    exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ h₁.2 _ h₂.2

theorem eq_of_tens_eq_of_ne (v : Pl (F := F)) {κ : Type} {ψ₁ ψ₂ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) {x₀ : κ → AF F} (h0 : r x₀ ≠ 0)
    (h : tens (evFin F v) ψ₁ r = tens (evFin F v) ψ₂ r) : ψ₁ = ψ₂ := by
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i))
  have hz : At (evFin F v) z := by
    intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [Pi.add_apply, z, map_add (f := _), GlobalTheory.LatVac.evFin_liftV]
    abel
  have e := congrFun h (x₀ + z)
  simp only [tens, hev, hr x₀ z hz] at e
  exact mul_right_cancel₀ h0 e

theorem acts_comp (v : Pl (F := F)) {κ : Type} [Fintype κ] {T₁ T₂ : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (hT₂ : ∀ f ∈ schA F κ, T₂ f ∈ schA F κ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h₂ : Acts (evFin F v) T₂ φ φ₁) (h₁ : Acts (evFin F v) T₁ φ₁ φ₂) :
    Acts (evFin F v) (fun f => T₁ (T₂ f)) φ φ₂ := by
  intro r hr
  have e := h₂ r hr
  have hr₁ : Rest (evFin F v) φ₁ r := ⟨hr.1, e ▸ hT₂ _ hr.2⟩
  show T₁ (T₂ _) = _
  rw [e, h₁ r hr₁]

end Local

end GlobalTheory.DblDiag

namespace GlobalTheory.DblDiag

open Matrix

theorem diag_integral : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) → ((Fin a' × Fin (a + a')) → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd →
    ∀ (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    (∀ (g : UA σ G.V'.J) (gd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin a' × Fin (a + a')), ∀ φ₂ ∈ schA F (Fin a' × Fin (a + a')), omd gd (boxFun φ₁ φ₂) = boxFun (om' (g, 1) φ₁) φ₂) →
    ∀ (g : GL (Fin a') (Fv F v)) (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks (mat (K g)) 0 0 (mat (K g)) →
    ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ'' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd p) (boxFun φ₁ φ₂) φ'' →
    ∀ μ : @MeasureTheory.Measure ((Fin a' × Fin (a + a')) → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫ x, φ'' (Sum.elim x x) ∂μ =
        ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ)) * ∫ x, φ₁ x * φ₂ x ∂μ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv t K hK S hS ν α ι hι hint d' hd' dd hdd omd hspl hres g p hp
    φ₁ h₁ φ₂ h₂ φ'' h'' hact μ hμ
  change UG _ (dbl (incM F G.V'.J)) →* _ at omd
  set k := K g with hk
  let gd := diagL (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) k
  let gd' := diagR (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) k
  have hgd : ((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
      Matrix.fromBlocks (mat k) 0 0 1 := rfl
  have hgd' : ((gd' : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
      Matrix.fromBlocks 1 0 0 (mat k) := rfl
  have hpq : p = gd * gd' := by
    apply Subtype.ext; apply Units.ext
    rw [hp]
    show _ = Matrix.fromBlocks (mat k) 0 0 1 * Matrix.fromBlocks 1 0 0 (mat k)
    rw [Matrix.fromBlocks_multiply]; simp
  have hAt : At (evFin F v) (((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) := by
    intro u hu
    have hk1 : u • (mat k - 1) = 0 := (hK g).1 u hu
    have e : Matrix.fromBlocks (mat k) 0 0 (1 : Matrix (Fin a') (Fin a') (AE F E)) - 1 =
        Matrix.fromBlocks (mat k - 1) 0 0 0 := by
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]; simp [sub_eq_add_neg]
    rw [hgd, e, Matrix.fromBlocks_smul]
    simp [hk1]

  have hSsb : ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), S g φ ∈ SB _ := fun φ hφ => (hS g φ hφ).1
  have hSlin : ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ' ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ c : ℂ,
      S g (c • φ + φ') = c • S g φ + S g φ' := by
    intro φ hφ φ' hφ' c
    have hm : c • φ + φ' ∈ SB ((Fin a' × Fin (a + a')) → Fv F v) := (SB _).add_mem ((SB _).smul_mem c hφ) hφ'
    refine hι.bij.injOn (hSsb _ hm) ((SB _).add_mem ((SB _).smul_mem c (hSsb φ hφ)) (hSsb φ' hφ')) ?_
    rw [hint g _ hm, map_add (f := _), map_smul, map_add (f := _), map_smul, hint g φ hφ, hint g φ' hφ']
    funext Y
    simp only [GlobalTheory.SplitFlip.omB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hSnorm : ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun φ hφ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat B G X om om' hT v k (hK g).1 φ (S g φ) hφ (hS g φ hφ).1 (hS g φ hφ).2 μ hμ

  have hL : ∀ ψ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd gd) (boxFun ψ₁ ψ₂) (boxFun (S g ψ₁) ψ₂) := by
    intro ψ₁ hψ₁ ψ₂ hψ₂
    obtain ⟨φ', -, hA⟩ := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v gd hAt _ (boxFun_mem_SB hψ₁ hψ₂)
    obtain ⟨r₁, hr₁, x₁, hx₁⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v ψ₁ hψ₁
    obtain ⟨r₂, hr₂, x₂, hx₂⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v ψ₂ hψ₂
    have hR := rest_boxFun v hr₁ hr₂
    have e := hA _ hR
    rw [tens_boxFun, hres k gd hgd _ hr₁.2 _ hr₂.2, (hS g ψ₁ hψ₁).2 r₁ hr₁, ← tens_boxFun] at e
    have h0 : boxFun r₁ r₂ (Sum.elim x₁ x₂) ≠ 0 := by
      simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr]; exact mul_ne_zero hx₁ hx₂
    have e2 : φ' = boxFun (S g ψ₁) ψ₂ := eq_of_tens_eq_of_ne v hR.1 h0 e.symm
    rw [e2] at hA; exact hA

  set c : ℂ := (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) with hc
  set T₂ : ((Fin a' × Fin (a + a')) → Fv F v) → ℂ := fun x => c * starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x)
    with hT₂
  have hR' : Acts (evFin F v) (omd gd') (boxFun φ₁ φ₂) (boxFun φ₁ T₂) :=
    GlobalTheory.T.triple_local_gl_embedding_theta hP F E σ B a a' G X om om' hT v hv t K hK S hS ν α ι hι hint d' hd' dd hdd omd hspl hres g gd' hgd' φ₁ h₁ φ₂ h₂
  have hT₂sb : T₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v) :=
    (SB _).smul_mem c (conj_mem_SB (hSsb _ (conj_mem_SB h₂)))
  have hcomp : Acts (evFin F v) (fun f => omd gd (omd gd' f)) (boxFun φ₁ φ₂) (boxFun (S g φ₁) T₂) :=
    acts_comp v (fun f hf => hspl.pres gd' f hf) hR' (hL φ₁ h₁ T₂ hT₂sb)
  have hφ'' : φ'' = boxFun (S g φ₁) T₂ := by
    refine GlobalTheory.TensUniq.eq_of_tens_eq v (boxFun φ₁ φ₂) _ _ (boxFun_mem_SB h₁ h₂) fun r hr => ?_
    have heq : omd p = omd gd * omd gd' := by
      calc
        omd p = omd (gd * gd') := congrArg omd hpq
        _ = omd gd * omd gd' := map_mul omd gd gd'
    exact (hact r hr).symm.trans ((congrArg (fun f : Module.End ℂ _ =>
      f (tens (evFin F v) (boxFun φ₁ φ₂) r)) heq).trans (hcomp r hr))
  subst hφ''
  have e : (fun x => boxFun (S g φ₁) T₂ (Sum.elim x x)) =
      fun x => c * (S g φ₁ x * starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x)) := by
    funext x
    simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, hT₂]
    ring
  rw [show (∫ x, boxFun (S g φ₁) T₂ (Sum.elim x x) ∂μ) =
      ∫ x, c * (S g φ₁ x * starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x)) ∂μ from congrArg (fun f => ∫ x, f x ∂μ) e,
    MeasureTheory.integral_const_mul]
  rw [GlobalTheory.T.local_linear_operator_l2_isometry v (S g) hSsb hSlin μ hμ hSnorm φ₁ h₁ φ₂ h₂]

end GlobalTheory.DblDiag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingIntegralStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_local_gl_embedding_integral : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) → ((Fin a' × Fin (a + a')) → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd →
    ∀ (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    (∀ (g : UA σ G.V'.J) (gd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((gd : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin a' × Fin (a + a')), ∀ φ₂ ∈ schA F (Fin a' × Fin (a + a')), omd gd (boxFun φ₁ φ₂) = boxFun (om' (g, 1) φ₁) φ₂) →
    ∀ (g : GL (Fin a') (Fv F v)) (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((p : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks (mat (K g)) 0 0 (mat (K g)) →
    ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ'' ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd p) (boxFun φ₁ φ₂) φ'' →
    ∀ μ : @MeasureTheory.Measure ((Fin a' × Fin (a + a')) → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫ x, φ'' (Sum.elim x x) ∂μ =
        ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ)) * ∫ x, φ₁ x * φ₂ x ∂μ := by
  first | exact @GlobalTheory.DblDiag.diag_integral | exact GlobalTheory.DblDiag.diag_integral | (intros; apply GlobalTheory.DblDiag.diag_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterLocalGL
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LinBarChar

open Matrix

theorem boxFun_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem fromBlocks_diag_sub_one {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    Matrix.fromBlocks A 0 0 A - 1 = Matrix.fromBlocks (A - 1) 0 0 (A - 1) := by
  rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  simp [sub_eq_add_neg]

theorem fromBlocks_diag_mul_diagCols {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    Matrix.fromBlocks A 0 0 A * (diagCols n : Matrix (n ⊕ n) n R) = (diagCols n : Matrix (n ⊕ n) n R) * A := by
  ext (i | i) j <;> simp [diagCols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply]

theorem unif_pow_ne_real : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν (unifAt v) : ℂ)) ^ m ≠ (r : ℂ) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hχ t K hK S hS ν α ι hι hint m hm r hr
  obtain ⟨-, ⟨d', hd', hBw⟩, -⟩ := hT.weil'
  obtain ⟨-, dd, omd, hdd, ⟨-, hspl, hsieg⟩, hres⟩ := hBw

  haveI : Nonempty (Fin a') := ⟨⟨0, by have := hT.geo.aBig; omega⟩⟩
  obtain ⟨g₀, hg₀⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin a') (R := Fv F v) (unifAt v)

  set k := K g₀ with hk
  have hkU : (mat k)ᵀ * incM F G.V'.J * (mat k).map (cA σ) = incM F G.V'.J := k.2
  set mi : Matrix (Fin a') (Fin a') (AE F E) := ((k : GL (Fin a') (AE F E))⁻¹).1
  have h1 : mat k * mi = 1 := Units.mul_inv (k : GL (Fin a') (AE F E))
  have h2 : mi * mat k = 1 := Units.inv_mul (k : GL (Fin a') (AE F E))
  let P₀ : GL (Fin a' ⊕ Fin a') (AE F E) := ⟨Matrix.fromBlocks (mat k) 0 0 (mat k), Matrix.fromBlocks mi 0 0 mi,
    by rw [Matrix.fromBlocks_multiply, h1]; simp [Matrix.fromBlocks_one],
    by rw [Matrix.fromBlocks_multiply, h2]; simp [Matrix.fromBlocks_one]⟩
  have hP₀ : P₀ ∈ UG (cA σ) (dbl (incM F G.V'.J)) := by
    show (Matrix.fromBlocks (mat k) 0 0 (mat k))ᵀ * dbl (incM F G.V'.J) * (Matrix.fromBlocks (mat k) 0 0 (mat k)).map (cA σ) = _
    have hn : (mat k)ᵀ * (-incM F G.V'.J) * (mat k).map (cA σ) = -incM F G.V'.J := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hkU]
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.map_zero _ (map_zero (cA σ))]
    rw [hkU, hn]
  let p : UG (cA σ) (dbl (incM F G.V'.J)) := ⟨P₀, hP₀⟩
  have hpm : ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
      Matrix.fromBlocks (mat k) 0 0 (mat k) := rfl
  have hAt : At (evFin F v) (((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) := by
    intro u hu
    have hk1 : u • (mat k - 1) = 0 := (hK g₀).1 u hu
    rw [hpm, fromBlocks_diag_sub_one, Matrix.fromBlocks_smul]
    simp [hk1]
  have hpt : ((p : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) *
      (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E)) =
      (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E)) *
        (((k : UA σ G.V'.J) : GL (Fin a') (AE F E)) : Matrix (Fin a') (Fin a') (AE F E)) := by
    rw [hpm]
    exact fromBlocks_diag_mul_diagCols _

  obtain ⟨l, hl, hinv, r₀, hr₀, c₀, hc₀, μ, hμ, hlφ, φ₀, hφ₀, hI⟩ := GlobalTheory.T.exists_admitted_diagonal_integral_linearForm F E σ a a' G B.ψ d' dd hdd v
  have hbox := boxFun_mem_SB hφ₀ hφ₀
  obtain ⟨φ'', hφ'', hact⟩ := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v p hAt _ hbox
  have h4 := GlobalTheory.T.triple_local_gl_embedding_integral hP F E σ B a a' G X om om' hT v hv t K hK S hS ν α ι hι hint d' hd' dd hdd omd hspl
    (fun g gd hgd φ₁ h₁ φ₂ h₂ => hres g gd hgd φ₁ h₁ φ₂ h₂) g₀ p hpm φ₀ hφ₀ φ₀ hφ₀ φ'' hφ'' hact μ hμ
  have hs := hsieg l hl hinv p _ hpt _ (hr₀ _ hbox).2
  have hs' := (congrArg l (hact r₀ (hr₀ _ hbox))).symm.trans hs
  rw [hlφ _ hφ'', hlφ _ hbox, h4] at hs'
  have hbd : (∫ x, boxFun φ₀ φ₀ (Sum.elim x x) ∂μ) = ∫ x, φ₀ x * φ₀ x ∂μ := rfl
  rw [hbd] at hs'
  set I := ∫ x, φ₀ x * φ₀ x ∂μ
  set val := ((X.α / X.β) (Matrix.GeneralLinearGroup.det ((k : UA σ G.V'.J) : GL (Fin a') (AE F E))) : ℂ) *
        ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F)
          (Matrix.GeneralLinearGroup.det ((k : UA σ G.V'.J) : GL (Fin a') (AE F E)))) : ℝ) ^
            ((Fintype.card (Fin (a + a')) : ℝ) / 2) : ℝ) : ℂ) with hval
  set u : ℂ := (ν (GlobalTheory.SplitFlip.gdet g₀) : ℂ) with hu
  have hratio : u / starRingEnd ℂ u = val := by
    have : c₀ * I * (u / starRingEnd ℂ u) = c₀ * I * val := by linear_combination hs'
    exact mul_left_cancel₀ (mul_ne_zero hc₀ hI) this
  have h6 := GlobalTheory.T.triple_local_gl_embedding_equivariant F E σ B a a' G X om om' hT v hv t K hK g₀

  have hgd : GlobalTheory.SplitFlip.gdet g₀ = unifAt v := hg₀
  rw [hgd] at hu h6
  have hu0 : u ≠ 0 := by rw [hu]; exact Units.ne_zero _
  have hr' : u ^ m = (r : ℂ) := by rw [hu]; exact hr
  have hrc : starRingEnd ℂ u ^ m = (r : ℂ) := by rw [← map_pow, hr', Complex.conj_ofReal]
  have hr0 : (r : ℂ) ≠ 0 := by rw [← hr']; exact pow_ne_zero _ hu0
  have hone : val ^ m = 1 := by
    rw [← hratio, div_pow, hr', hrc, div_self hr0]
  set z := chrW X.ν t (unifAt v) with hz
  rcases h6 with h | h
  · have e1 : ((z ^ (2 * m) : ℂˣ) : ℂ) = 1 := by
      rw [Units.val_pow_eq_pow_val, pow_mul, ← h, hone]
    apply hχ t (((2 * m : ℕ) : ℤ)) (by omega)
    rw [zpow_natCast]
    exact Units.ext e1
  · have e1 : (((z⁻¹) ^ (2 * m) : ℂˣ) : ℂ) = 1 := by
      rw [Units.val_pow_eq_pow_val, pow_mul, ← h, hone]
    apply hχ t (-((2 * m : ℕ) : ℤ)) (by omega)
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
    exact Units.ext e1

end GlobalTheory.LinBarChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterLocalGLStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_local_GL : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν (unifAt v) : ℂ)) ^ m ≠ (r : ℂ) := by
  first | exact @GlobalTheory.LinBarChar.unif_pow_ne_real | exact GlobalTheory.LinBarChar.unif_pow_ne_real | (intros; apply GlobalTheory.LinBarChar.unif_pow_ne_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedCharacterGood
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GoodPlaceAct

theorem chrW_pow_not_real {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (χ : Chr F E) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (h : ∀ k : ℤ, k ≠ 0 → chrW χ t (unifAt v) ^ k ≠ 1) :
    ∀ m : ℕ, 0 < m → ∀ r : ℝ, ((chrW χ t (unifAt v) : ℂ)) ^ m ≠ (r : ℂ) := by
  intro m hm r hr
  have hn : ‖((chrW χ t (unifAt v) : ℂˣ) : ℂ)‖ = 1 := by
    simp only [chrW, locChar, MonoidHom.coe_comp, Function.comp_apply]
    first | exact Circle.norm_coe _ | exact Circle.abs_coe _ | simp
  have hr1 : |r| = 1 := by
    have e := congrArg norm hr
    rw [norm_pow, hn, one_pow, Complex.norm_real, Real.norm_eq_abs] at e
    exact e.symm
  have hsq : r ^ 2 = 1 := by rw [← sq_abs, hr1, one_pow]
  apply h ((2 * m : ℕ) : ℤ) (by exact_mod_cast (by omega : 2 * m ≠ 0))
  apply Units.ext
  rw [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_one, pow_mul', hr]
  exact_mod_cast hsq

theorem act_omB : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) → ∀ t : E →ₐ[F] Fv F v,
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν₀ (unifAt v) : ℂ)) ^ m ≠ (r : ℂ)) ∧
      ∀ ι, G.M'.IsLinBar B.ψ t 1 1 ι → ∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v),
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧ ι φ₁ = GlobalTheory.SplitFlip.omB ν₀ ν₀ g₀ 1 (ι φ) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hTr v hv hnr t
  obtain ⟨K, hK⟩ := GlobalTheory.T.exists_local_GL_embedding_unitary F E σ B a a' G X om om' hTr v hv t
  let Bs : Base F E := { B with v₁ := v, τ₁ := t }
  have hTr' : IsTriple Bs G X om om' := ⟨{ hTr.base with }, { hTr.geo with hV := { hTr.geo.hV with }, hV' := { hTr.geo.hV' with }, hW := { hTr.geo.hW with } },
    { hTr.chars with good := hv }, hTr.weil, hTr.weil'⟩
  have hB := fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hTr v (K g) (hK g).1
  choose S hS using hB
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  have pres : ∀ p Φ, Φ ∈ GlobalTheory.WeilM.schA F _ → om' p Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun p Φ hΦ => hSplit.pres p Φ hΦ
  have restS : ∀ g φ r, φ ∈ SB _ → Rest (evFin F v) φ r → Rest (evFin F v) (S g φ) r := fun g φ r hφ hr =>
    ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact pres _ _ hr.2⟩
  have h1 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ := fun g φ hφ => (hS g φ hφ).1
  have hvac := hTr.geo.hM'.vac v
  have hlin : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ c : ℂ,
      S g (c • φ + φ') = c • S g φ + S g φ' := by
    intro g φ hφ φ' hφ' c
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v (G.M'.vac v) _ _ hvac.1 fun r hr => ?_
    have hsum : c • φ + φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v) := Submodule.add_mem _ (Submodule.smul_mem _ c hφ) hφ'
    have r0 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hsum hr
    have r1 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ hr
    have r2 := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v _ _ r hvac.2.1 hφ' hr
    have et : ∀ (ψ₁ ψ₂ : (Fin a' × Fin (a + a') → Fv F v) → ℂ), tens (evFin F v) (c • ψ₁ + ψ₂) r =
        c • tens (evFin F v) ψ₁ r + tens (evFin F v) ψ₂ r := fun ψ₁ ψ₂ => by
      funext x; simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [← (hS g _ hsum).2 r r0, et, map_add (f := _), map_smul, (hS g φ hφ).2 r r1, (hS g φ' hφ').2 r r2, et]
  have h2 : ∀ g g', ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S (g * g') φ = S g (S g' φ) := by
    intro g g' φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have e1 : ((K (g * g'), (1 : UA σ G.W.J))) = (K g, 1) * (K g', 1) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    rw [← (hS (g * g') φ hφ).2 r hr, e1, map_mul, Module.End.mul_apply, (hS g' φ hφ).2 r hr,
      (hS g (S g' φ) (h1 g' φ hφ)).2 r (restS g' φ r hφ hr)]
  have h3 : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S 1 φ = φ := by
    intro φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have e1 : ((K 1, (1 : UA σ G.W.J))) = 1 := by rw [map_one]; rfl
    rw [← (hS 1 φ hφ).2 r hr, e1, map_one, Module.End.one_apply]
  have hψ : Continuous B.ψ := hTr.base.std.1
  have atAct : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) γ →
      At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have h4 : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v)
            (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hψ v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hTr.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  have h5 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → Fv F v) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ :=
    fun g φ hφ μ hμ => GlobalTheory.T.localWeilOperator_isometry_schwartzBruhat B G X om om' hTr v (K g) (hK g).1 φ (S g φ) hφ (h1 g φ hφ) (hS g φ hφ).2 μ hμ
  by_cases hex : ∃ ι, G.M'.IsLinBar B.ψ t 1 1 ι
  · obtain ⟨ν, α, -, hC⟩ := GlobalTheory.T.heisenbergIntertwiner_eq_twisted_weilOperator Bs G X om om' hTr' K hK S h1 hlin h2 h3 h4 h5
    obtain ⟨ι₀, hι₀⟩ := hex
    refine ⟨ν, GlobalTheory.T.unramified_character_local_GL hP F E σ B a a' G X om om' hTr v hv hnr t K hK S hS ν α ι₀ hι₀ (hC ι₀ hι₀),
      fun ι hι g₀ => ⟨K g₀, (hK g₀).1, fun φ hφ => ⟨S g₀ φ, h1 g₀ φ hφ, (hS g₀ φ hφ).2, ?_⟩⟩⟩
    rw [hC ι hι g₀ φ hφ]
    funext Y
    simp only [GlobalTheory.SplitFlip.omB, map_one, Units.val_one]
  · exact ⟨chrW X.ν t, chrW_pow_not_real _ t (fun k hk => hnr t k hk), fun ι hι => absurd ⟨ι, hι⟩ hex⟩

end GlobalTheory.GoodPlaceAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedCharacterGoodStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_character_good : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v →
    (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) → ∀ t : E →ₐ[F] Fv F v,
    ∃ ν₀ : (Fv F v)ˣ →* ℂˣ, (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν₀ (unifAt v) : ℂ)) ^ m ≠ (r : ℂ)) ∧
      ∀ ι, G.M'.IsLinBar B.ψ t 1 1 ι → ∀ g₀ : GL (Fin a') (Fv F v), ∃ g ∈ UAt σ G.V' (evFin F v),
        ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (g, 1)) φ φ₁ ∧ ι φ₁ = GlobalTheory.SplitFlip.omB ν₀ ν₀ g₀ 1 (ι φ) := by
  first | exact @GlobalTheory.GoodPlaceAct.act_omB | exact GlobalTheory.GoodPlaceAct.act_omB | (intros; apply GlobalTheory.GoodPlaceAct.act_omB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximation
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RankCoinv


open GlobalTheory.SplitFlip in
theorem exists_soLoc_sub_mem_augAt : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v,
    X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ t : E →ₐ[F] Fv F v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₀ ∈ G.M'.SoLoc B.ψ t, φ - φ₀ ∈ augAt om' v := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv hν t φ hφ
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_bar_good_place hP F E σ B a a' G X om om' hT v hv t
  obtain ⟨ν₀, hν₀, hf⟩ := GlobalTheory.T.exists_unramified_character_good hP F E σ B a a' G X om om' hT v hv hν t
  have hspan : Submodule.span ℂ {Z | ∃ g : GL (Fin a') (Fv F v), ∃ Ψ' ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)),
      Z = omB ν₀ ν₀ g 1 Ψ' - Ψ'} ≤ (augAt om' v ⊓ SB _).map ι := by
    rw [Submodule.span_le]
    rintro Z ⟨g₀, Ψ', hΨ', rfl⟩
    obtain ⟨φ', hφ', rfl⟩ := hι.bij.surjOn hΨ'
    obtain ⟨g, hg, hact⟩ := hf ι hι g₀
    obtain ⟨φ₁, hφ₁, hA, hE⟩ := hact φ' hφ'
    refine ⟨φ₁ - φ', ⟨Submodule.subset_span ⟨g, hg, φ', hφ', φ₁, hφ₁, hA, rfl⟩, Submodule.sub_mem _ hφ₁ hφ'⟩, ?_⟩
    simp [map_sub, hE]
  obtain ⟨Ψ₀, -, hrk, hmem⟩ := GlobalTheory.T.schwartzBruhat_full_rank_modulo_translates (Fv F v) a' (a + a') ν₀ (unifAt v)
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec hν₀ (ι φ) (hι.bij.mapsTo hφ)
  obtain ⟨n, ⟨hnA, hnSB⟩, hn⟩ := hspan hmem
  refine ⟨φ - n, ⟨Submodule.sub_mem _ hφ hnSB, ι, hι, fun Y hY => ?_⟩, by simpa using hnA⟩
  have : ι (φ - n) = Ψ₀ := by rw [map_sub, hn]; abel
  rw [this]; exact hrk Y hY

end GlobalTheory.RankCoinv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_local_approximation : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) →
    ∀ t : E →ₐ[F] Fv F v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∃ φ₀ ∈ G.M'.SoLoc B.ψ t, φ - φ₀ ∈ augAt om' v := by
  first | exact @GlobalTheory.RankCoinv.exists_soLoc_sub_mem_augAt | exact GlobalTheory.RankCoinv.exists_soLoc_sub_mem_augAt | (intros; apply GlobalTheory.RankCoinv.exists_soLoc_sub_mem_augAt <;> assumption)
end
