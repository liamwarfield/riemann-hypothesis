module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocalLowerBoundCmPointFramePolynomialEveryPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmMulRightOfIsCMExt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertSph

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def latAt {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : AddSubgroup (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
    ∃ y ∈ W.L, z = a • fun i => inclR (F := F) (AF F) (y i)}

def KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UA σ W.J) :=
  {h | h ∈ UAt σ W (evFin F v) ∧ ∀ z ∈ latAt W v, mat h *ᵥ z ∈ latAt W v ∧ mat h⁻¹ *ᵥ z ∈ latAt W v}

theorem one_mem_KAt (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : (1 : UA σ W.J) ∈ KAt σ W v := by
  refine ⟨?_, fun z hz => ?_⟩
  · intro u _
    show u • (mat (1 : UA σ W.J) - 1) = 0
    simp [mat]
  · simp [mat, hz]

end GlobalTheory.InertSph
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

section Laws

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


variable (F κ) in
def intPts : Set (κ → Af F) :=
  Set.univ.pi fun _ => {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}

theorem indicator_intPts_mem_SB : (intPts F κ).indicator (1 : (κ → Af F) → ℂ) ∈ SB (κ → Af F) := by
  haveI := GlobalTheory.IntegralFinAdele.t2Space_finiteAdeleRing' F
  have hO : IsOpen {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have hC : IsCompact {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1
  have hU : IsOpen (intPts F κ) := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hK : IsCompact (intPts F κ) := isCompact_univ_pi fun _ => hC
  refine ⟨?_, HasCompactSupport.intro' hK hK.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ intPts F κ
  · filter_upwards [hU.mem_nhds hx] with y hy
    simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem zero_mem_intPts : (0 : κ → Af F) ∈ intPts F κ := fun _ _ v => zero_mem _

def ptAt (a : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), y i)

theorem pureA_ptAt (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (a : κ → mixedEmbedding.mixedSpace F)
    (y : κ → Af F) : pureA F f g (ptAt a y) = f a * g y := by
  change f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i))) * g y = f a * g y
  congr 1
  congr 1
  funext i
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (a i)

theorem fin_eq_zero_of_at {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h := congrFun (hz ((0, 1) : AF F) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))) i
  have h2 : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
  rwa [one_mul] at h2

theorem at_of_fin_eq_zero {z : κ → AF F} (hz : ∀ i, (z i).2 = 0) : At (evI F) z := by
  intro u hu
  have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  funext i
  refine Prod.ext ?_ ?_
  · change u.1 * (z i).1 = 0
    rw [hu1, zero_mul]
  · change u.2 * (z i).2 = 0
    rw [hz i, mul_zero]

theorem tens_eq_pureA (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evI F) z → r (x + z) = r x) :
    tens (evI F) f r = pureA F f (fun y => r (fun i => ((0 : Ainf F), y i))) := by
  funext x
  simp only [tens, pureA, evI]
  congr 1
  have h := hr (fun i => ((0 : Ainf F), (x i).2)) (fun i => ((x i).1, (0 : Af F)))
    (at_of_fin_eq_zero fun i => rfl)
  rw [← h]
  congr 1
  funext i
  exact Prod.ext (zero_add _).symm (add_zero _).symm

theorem mem_SB_of_pureA_mem {f : SInf F κ} (hf : f ≠ 0) {g : (κ → Af F) → ℂ} (h : pureA F f g ∈ schA F κ) :
    g ∈ SB (κ → Af F) := by
  obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hf (SchwartzMap.ext h0)
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → Af F) → ℂ) := LinearMap.funLeft ℂ ℂ (ptAt a)
  have hle : schA F κ ≤ (SB (κ → Af F)).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f', g', hg', rfl⟩
    change (fun y => pureA F f' g' (ptAt a y)) ∈ SB (κ → Af F)
    simp_rw [pureA_ptAt]
    exact (SB (κ → Af F)).smul_mem (f' a) hg'
  have h1 : L (pureA F f g) ∈ SB (κ → Af F) := hle h
  have h2 : L (pureA F f g) = f a • g := by
    funext y
    change pureA F f g (ptAt a y) = _
    rw [pureA_ptAt]
    rfl
  rw [h2] at h1
  have h3 := (SB (κ → Af F)).smul_mem (f a)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h3

theorem eval_mem_adm (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
    (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

end Laws

section Main

open scoped Classical

theorem actsLaws : ActsLaws := by
  intro F _ _ κ _ f f₁ f₂
  set g₀ : (κ → Af F) → ℂ := (intPts F κ).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (κ → Af F) := indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem zero_mem_intPts]; rfl

  set r₀ : (κ → AF F) → ℂ := fun x => g₀ (fun i => (x i).2) with hr₀def
  have hr₀inv : ∀ x z, At (evI F) z → r₀ (x + z) = r₀ x := by
    intro x z hz
    change g₀ (fun i => (x i + z i).2) = g₀ (fun i => (x i).2)
    congr 1
    funext i
    change (x i).2 + (z i).2 = (x i).2
    rw [fin_eq_zero_of_at hz, add_zero]
  have htens₀ : ∀ φ : (κ → mixedEmbedding.mixedSpace F) → ℂ, tens (evI F) φ r₀ = pureA F φ g₀ := fun φ => rfl
  have hrest₀ : Rest (evI F) (⇑f) r₀ := ⟨hr₀inv, by rw [htens₀]; exact Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩⟩

  have hext : ∀ h₁ h₂ : SInf F κ, (∀ a, pureA F h₁ g₀ (ptAt a 0) = pureA F h₂ g₀ (ptAt a 0)) → h₁ = h₂ := by
    intro h₁ h₂ h
    ext a
    simpa [pureA_ptAt, hg₀0] using h a

  have hzero : ∀ g : (κ → Af F) → ℂ, pureA F ⇑(0 : SInf F κ) g = 0 := by
    intro g; funext x; simp [pureA]
  have hzeroT : ∀ r : (κ → AF F) → ℂ, tens (evI F) ⇑(0 : SInf F κ) r = 0 := by
    intro r; funext x; simp [tens]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T hT0 hSD r hr x
    by_cases hf : f = 0
    · subst hf
      have hf₁ : f₁ = 0 := hext _ _ fun a => by
        have h := hSD g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
        simp only [LinearMap.proj_apply, hzero, hT0] at h
        rw [hzero]
        exact (h.unique (hasDerivAt_const 0 (0 : ℂ)))
      subst hf₁
      rw [hzeroT]
      simp only [hT0, Pi.zero_apply]
      exact hasDerivAt_const 0 (0 : ℂ)
    · have hg : (fun y => r (fun i => ((0 : Ainf F), y i))) ∈ SB (κ → Af F) :=
        mem_SB_of_pureA_mem hf (tens_eq_pureA (⇑f) hr.1 ▸ hr.2)
      have h := hSD _ hg _ (eval_mem_adm x)
      rw [tens_eq_pureA (⇑f) hr.1, tens_eq_pureA (⇑f₁) hr.1]
      exact h
  · intro T hT0 hSA r hr
    by_cases hf : f = 0
    · subst hf
      have hf₁ : f₁ = 0 := hext _ _ fun a => by
        have h := hSA g₀ hg₀
        rw [hzero, hT0] at h
        rw [← h, hzero]
      subst hf₁
      rw [hzeroT, hT0]
    · have hg : (fun y => r (fun i => ((0 : Ainf F), y i))) ∈ SB (κ → Af F) :=
        mem_SB_of_pureA_mem hf (tens_eq_pureA (⇑f) hr.1 ▸ hr.2)
      rw [tens_eq_pureA (⇑f) hr.1, tens_eq_pureA (⇑f₁) hr.1]
      exact hSA _ hg
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e₁ := h₁ r₀ hrest₀ (ptAt a 0)
    have e₂ := h₂ r₀ hrest₀ (ptAt a 0)
    rw [htens₀] at e₁ e₂
    exact e₁.unique e₂
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e := (h₁ r₀ hrest₀).symm.trans (h₂ r₀ hrest₀)
    rw [htens₀, htens₀] at e
    exact congrFun e (ptAt a 0)
  · intro T h₁ h₂
    refine hext _ _ fun a => ?_
    have e₁ := h₁ g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
    have e₂ := h₂ g₀ hg₀ _ (eval_mem_adm (ptAt a 0))
    exact e₁.unique e₂

end Main

end GlobalTheory.RealLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archActionReadings_compatible : GlobalTheory.RealLift.ActsLaws := by
  first | exact @GlobalTheory.RealLift.actsLaws | exact GlobalTheory.RealLift.actsLaws | (intros; apply GlobalTheory.RealLift.actsLaws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
open scoped NNReal Pointwise
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.UnitaryVol

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h1 := h.2.2 (star v) (by simpa using hv)
  rw [star_star, hMv, dotProduct_zero] at h1
  simp at h1

theorem isHermND_map {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ}
    (hσ : ∀ x, σ (σ x) = x) (h : X.IsHerm σ B r s) : IsHermND σ (X.J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.map_apply, hσ]
    exact (h.herm j i).symm
  · have hJ : X.J.det ≠ 0 := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      intro hz
      apply det_ne_zero_of_isCartan (h.cartan w)
      rw [show X.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix X.J from rfl, ← RingHom.map_det, hz, map_zero]
    rw [show X.J.map σ = (σ : E →+* E).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 hJ

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  haveI := (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).to_subtype
  exact Function.Injective.countable
    (f := fun γ : ratU σ J => (⟨γ.1.1, Subgroup.mem_subgroupOf.1 γ.2⟩ :
      Set.range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))))
    fun γ γ' h => Subtype.val_injective (Subtype.val_injective (congrArg Subtype.val h :))

end GlobalTheory.UnitaryVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory TopologicalSpace Opposite
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.VB
open GlobalTheory.Twist (resM resM_self app_resM)
open GlobalTheory.QCoh (appLinear freeModule)

namespace GlobalTheory.OmegaGlobal

theorem map_bijective_of_isIso_counit {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) (X Y : D) [IsIso (adj.counit.app X)] :
    Function.Bijective (R.map : (X ⟶ Y) → _) := by
  have h : (R.map : (X ⟶ Y) → _) = adj.homEquiv _ _ ∘ fun φ => adj.counit.app X ≫ φ := by
    funext φ
    simp [Adjunction.homEquiv_unit]
  rw [h]
  exact (adj.homEquiv _ _).bijective.comp
    ((asIso (adj.counit.app X)).homFromEquiv (Z := Y)).symm.bijective

section Frames

variable {X : Scheme.{0}} {F : X.Modules}

theorem isQuasicoherent_of_frames (h : ∀ x : X, ∃ (U : X.Opens) (n : ℕ) (e : Fin n → Γ(F, U)),
    x ∈ U ∧ IsFrame e) : F.IsQuasicoherent := by
  choose U n e hx he using h
  refine QCoh.isQuasicoherent_of_restrict F (fun x => (U x).ι)
    (fun x => ⟨x, by simpa using hx x⟩) fun x => ?_
  have := (isVB_freeModule (U x).toScheme (Fin (n x))).isQuasicoherent
  exact QCoh.isQuasicoherent_of_iso ((isFrame_freeFrame _ _).iso
      ((isFrame_restrict_iff (U x).ι _).2 ((he x).res ((U x).ι_image_le ⊤))))

end Frames

variable {O : Type} [CommRing O] {G : Over (Sp O)} [GrpObj G]

theorem fst_mul (x y : LieG G) : ptMap (TrivSqZeroExt.fstHom O O O) ≫ (x.1 * y.1) =
    toUnit (specO O O) ≫ η[G] := by
  rw [comp_mul, x.2, y.2]
  exact _root_.mul_one (1 : specO O O ⟶ G)

theorem fst_scale (a : O) (x : LieG G) : ptMap (TrivSqZeroExt.fstHom O O O) ≫
    (ptMap (dualScale a) ≫ x.1) = toUnit (specO O O) ≫ η[G] := by
  refine Eq.trans ?_ x.2
  rw [← Category.assoc]
  congr 1
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext y <;> simp [dualScale]

end GlobalTheory.OmegaGlobal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroEvalFrNeZero
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj GlobalTheory.LamT

namespace GlobalTheory.LatFull.CMInt

theorem exists_denom {K : Type} [Field K] [NumberField K] (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (c : K) :
    ∃ N : 𝓞 K, N ≠ 0 ∧ ∀ x ∈ J, IsIntegral ℤ ((N : K) * (x * c)) := by
  obtain ⟨a, ha, h⟩ := (J * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c).isFractional
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun x hx => ?_⟩
  obtain ⟨w, hw⟩ := h (x * c) (FractionalIdeal.mul_mem_mul hx (FractionalIdeal.mem_spanSingleton_self _ _))
  rw [Algebra.smul_def] at hw
  have : (a : K) * (x * c) = (w : K) := hw.symm
  rw [this]
  exact w.isIntegral_coe

theorem exists_denom_eval {K σ : Type} [Field K] [NumberField K] [Finite σ]
    (J : (σ →₀ ℕ) → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (x : σ → K) (d : ℕ) :
    ∃ N : K, N ≠ 0 ∧ ∀ G : MvPolynomial σ K, G.IsHomogeneous d → (∀ μ, AddMonoidAlgebra.coeff G μ ∈ J μ) →
      IsIntegral ℤ (N * MvPolynomial.eval x G) := by
  classical
  choose M hM0 hM using fun μ : σ →₀ ℕ => exists_denom (J μ) (∏ i ∈ μ.support, x i ^ μ i)
  let S := (Finsupp.finite_of_degree_le (σ := σ) d).toFinset
  refine ⟨((∏ μ ∈ S, M μ : 𝓞 K) : K), ?_, fun G hG hJ => ?_⟩
  · have : (∏ μ ∈ S, M μ : 𝓞 K) ≠ 0 := Finset.prod_ne_zero_iff.2 fun μ _ => hM0 μ
    exact fun h => this (RingOfIntegers.coe_eq_zero_iff.1 h)
  · rw [MvPolynomial.eval_eq, Finset.mul_sum]
    refine IsIntegral.sum _ fun μ hμ => ?_
    have hS : μ ∈ S := by
      simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      have := hG (MvPolynomial.mem_support_iff.1 hμ)
      rw [Finsupp.degree_eq_weight_one]
      exact this.le
    rw [← Finset.prod_erase_mul _ _ hS]
    have e : (((∏ ν ∈ S.erase μ, M ν) * M μ : 𝓞 K) : K) = ((∏ ν ∈ S.erase μ, M ν : 𝓞 K) : K) * (M μ : K) :=
      map_mul (algebraMap (𝓞 K) K) _ _
    rw [e, mul_assoc]
    exact (RingOfIntegers.isIntegral_coe _).mul (hM μ _ (hJ μ))

theorem coeff_mem_of_loc {K : Type} [Field K] [NumberField K] {g : ℕ} {B : Type} [Fintype B] {m : B → ℕ}
    (e : (Σ b, Fin (m b)) ≃ Fin g) (T abelian₂ : MLine K) (ℓ : Fin g → MLine K) (U : Matrix (Fin g) (Fin g) K)
    (G : MvPolynomial (FrVar m) K) (n : ℕ) (hT : T.Good) (hℓ : ∀ j, (ℓ j).Good)
    (hloc : ∀ p, Step5Loc e T abelian₂ ℓ U G n p) (μ : FrVar m →₀ ℕ) :
    AddMonoidAlgebra.coeff G μ ∈ (lineNN T ℓ (fun v : FrVar m => e ⟨v.1, v.2.2⟩) μ n).I := by
  classical
  refine coeff_mem_of_local K g ℓ T (FrVar m) _ μ n _ hT hℓ fun p => ?_
  obtain ⟨t, cd, cl, ht, hcd, hcl, hv, V, K', _, _, _, _, _, _, f, Ub, hVc, hfin, hind, hUb, hclUb, hW⟩ := hloc p
  refine ⟨t, cl, ht, hcl, ?_⟩
  have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.1
  have hftn : f (t ^ n) ≠ 0 := (map_ne_zero f).mpr htn
  obtain ⟨w, hw⟩ := coeff_integral_local V K' B m (MvPolynomial.map f G) Ub (fun b j => f (cl (e ⟨b, j⟩)))
    (f (t ^ n)) hVc hfin hftn hUb hclUb hW μ
  have hrange : f (AddMonoidAlgebra.coeff G μ * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) ∈
      Set.range (algebraMap V K') := by
    refine ⟨w, ?_⟩
    rw [map_div₀, map_mul, map_prod]
    simp only [map_pow]
    rw [← map_pow f t n, ← MvPolynomial.coeff_map, hw, mul_div_cancel_left₀ _ hftn]
  have h1 := (hind _).mp hrange
  calc p.valuation K (AddMonoidAlgebra.coeff G μ * ∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v)
      = p.valuation K (AddMonoidAlgebra.coeff G μ * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) *
          p.valuation K (t ^ n) := by
        rw [← map_mul, div_mul_cancel₀ _ htn]
    _ ≤ p.valuation K (t ^ n) := mul_le_of_le_one_left' h1

theorem exists_det_ne_zero_evalFr_ne_zero {K : Type} [Field K] [Infinite K] {B : Type} [Fintype B] {m : B → ℕ}
    (G : MvPolynomial (FrVar m) K) (hG : G ≠ 0) :
    ∃ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K, (∀ b, (Y b).det ≠ 0) ∧ evalFr G Y ≠ 0 := by
  classical
  have hev : ∀ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K,
      evalFr (∏ b, FieldPoly.blockDetPoly K m b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← FieldPoly.evalFr_blockDetPoly m _ Y]
    simp only [evalFr, map_prod]
  have hD : (∏ b, FieldPoly.blockDetPoly K m b) ≠ 0 := fun h0 => by
    have h1 := hev fun _ => 1
    rw [h0] at h1
    simp [evalFr] at h1
  have hP := mul_ne_zero hD hG
  obtain ⟨x, hx⟩ : ∃ x : FrVar m → K, MvPolynomial.eval x ((∏ b, FieldPoly.blockDetPoly K m b) * G) ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (MvPolynomial.funext fun x => by rw [h x, map_zero])
  rw [map_mul] at hx
  let X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
  refine ⟨X, fun b => ?_, right_ne_zero_of_mul hx⟩
  have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hev X]; exact left_ne_zero_of_mul hx
  exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)

theorem exists_frame_bounded_denom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F₀ ∈ sec Xo c a n, (∀ G, IsFrPoly F₀ z.y G → G ≠ 0) → ∃ (y : FrPt Xo c z.K) (N : z.K), N * evR Xo c F₀ y ≠ 0 ∧ ∀ F ∈ sec Xo c a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → IsIntegral ℤ (N * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz a n F₀ hF₀ hne
  classical
  obtain ⟨G₀, hG₀, -⟩ := FieldPoly.exists_isFrPoly_isHomogeneous E H Dw l Xo c z.K z.y a n F₀ hF₀
  obtain ⟨Y, hY, hY0⟩ := exists_det_ne_zero_evalFr_ne_zero G₀ (hne G₀ hG₀)
  obtain ⟨y, hy, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c z.K z.y (fun b => (Y b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact (hY b).isUnit)
  rw [Units.val_one] at hy
  have hval : ∀ (F : Rul Xo c) (G : MvPolynomial (FrVar Dw.mult) z.K), IsFrPoly F z.y G →
      evR Xo c F y = evalFr G Y := fun F G hG => by
    have h1 := hG z.K (AlgHom.id c.F z.K) z.y y Y (fun b => (hY b).isUnit) (GlobalTheory.Frames.frMapUniq_refl z.y) hy
    have h2 : MvPolynomial.map (AlgHom.id c.F z.K).toRingHom G = G := MvPolynomial.map_id G
    rwa [h2] at h1
  have hgood : z.Tl.dual.Good ∧ ∀ k, (z.ℓ k).Good := by
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvΨ, hv', hT, -⟩, ⟨-, -, -, hℓ⟩, -⟩ := hz
    refine ⟨(degree_algebraic z.K z.Tl z.Tl hT hT).2.2.1, fun k => ?_⟩
    have h := hℓ k
    change (z.letters.ℓ k).Good
    generalize z.letters = L at h
    revert h
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact (hvΨ q.2).1
    | inr q => intro h1; rw [h1]; exact (hv' q.2).1
  obtain ⟨N, hN, hint⟩ := exists_denom_eval
    (fun μ : FrVar Dw.mult →₀ ℕ => (lineNN z.Tl.dual z.ℓ (fun v : FrVar Dw.mult => z.e ⟨v.1, v.2.2⟩) μ n).I)
    (fun v : FrVar Dw.mult => Y v.1 v.2.2 v.2.1) (∑ τ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ)))
  refine ⟨y, N, by rw [hval F₀ G₀ hG₀]; exact mul_ne_zero hN hY0, fun F hF hv => ?_⟩
  obtain ⟨G, hG, hh⟩ := FieldPoly.exists_isFrPoly_isHomogeneous E H Dw l Xo c z.K z.y a n F hF
  rw [hval F G hG]
  exact hint G hh (coeff_mem_of_loc z.e z.Tl.dual z.LamL z.ℓ z.U G n hgood.1 hgood.2
    (LocClause.step5Loc_cmPt E H Dw l Xo c z f La hz a n F hF hv G hG))

end GlobalTheory.LatFull.CMInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.LieVB GlobalTheory.Conormal

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

section Op

variable (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]

abbrev opModule : Module Oᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id O).fromOpposite fun x y => Commute.all x y)

theorem opModule_central : @IsCentralScalar O M _ (opModule O M).toSMul :=
  @IsCentralScalar.mk O M _ (opModule O M).toSMul fun _ _ => rfl

end Op

section Defs

variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

abbrev TM : Over (Sp O) := Over.mk (spMap (algebraMap O (TrivSqZeroExt O M)))

def zeroSec : 𝟙_ (Over (Sp O)) ⟶ TM O M :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom O O M).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

theorem isChart : IsChart (TM O M).hom (sec (zeroSec O M)) ⊤ ⊤ :=
  ⟨isAffineOpen_top (Sp O), isAffineOpen_top (Spec (CommRingCat.of (TrivSqZeroExt O M))), le_top, le_top⟩

abbrev topModule : Module Γ(Sp O, ⊤) M :=
  Module.compHom M (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom

abbrev toTsze : Γ((TM O M).left, ⊤) →+* TrivSqZeroExt O M :=
  (Scheme.ΓSpecIso (CommRingCat.of (TrivSqZeroExt O M))).hom.hom

abbrev toO : Γ(Sp O, ⊤) →+* O := (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom

theorem toTsze_base (r : Γ(Sp O, ⊤)) :
    toTsze O M ((TM O M).hom.appLE ⊤ ⊤ le_top r) = algebraMap O _ (toO O r) := by
  rw [appLE_top]
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O (TrivSqZeroExt O M)))) r)

theorem toO_sec (b : Γ((TM O M).left, ⊤)) :
    toO O ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top b) = (toTsze O M b).fst := by
  rw [appLE_top]
  exact congr($(Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O M).toRingHom)) b)

end Defs

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

section Kappa

variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
  [IsCentralScalar O M]

def sndFn : letI := (isChart O M).algebra; letI := topModule O M
    Γ((TM O M).left, ⊤) →ₗ[Γ(Sp O, ⊤)] M :=
  letI := (isChart O M).algebra
  letI := topModule O M
  { toFun := fun b => (toTsze O M b).snd
    map_add' := fun a b => by simp
    map_smul' := fun r b => by
      change (toTsze O M ((TM O M).hom.appLE ⊤ ⊤ le_top r * b)).snd = toO O r • (toTsze O M b).snd
      rw [map_mul, toTsze_base, TrivSqZeroExt.snd_mul]
      simp [TrivSqZeroExt.algebraMap_eq_inl] }

theorem sndFn_apply (b : Γ((TM O M).left, ⊤)) :
    letI := (isChart O M).algebra; letI := topModule O M
    sndFn O M b = (toTsze O M b).snd := rfl

theorem sndFn_der (a b : Γ((TM O M).left, ⊤)) :
    letI := (isChart O M).algebra; letI := topModule O M
    sndFn O M (a * b) = (isChart O M).aug (sec_hom _) a • sndFn O M b +
      (isChart O M).aug (sec_hom _) b • sndFn O M a := by
  letI := (isChart O M).algebra
  letI := topModule O M
  rw [sndFn_apply, sndFn_apply, sndFn_apply, map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]
  change _ = (toO O ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top a) • (toTsze O M b).snd : M) +
    toO O ((sec (zeroSec O M)).appLE ⊤ ⊤ le_top b) • (toTsze O M a).snd
  rw [toO_sec, toO_sec]

instance quasiCompact_zeroSec : QuasiCompact (sec (zeroSec O M)) := by
  have : QuasiSeparated (TM O M).hom := show QuasiSeparated (Spec.map _) from inferInstance
  infer_instance

def kappa : Γ(conormal (sec (zeroSec O M)), ⊤) →+ M :=
  letI := (isChart O M).algebra
  letI := topModule O M
  ((AugCot.lift ((isChart O M).aug (sec_hom _)) (sndFn O M) (sndFn_der O M)).toAddMonoidHom).comp
    ((isChart O M).augCotEquiv (sec_hom _)).symm.toLinearMap.toAddMonoidHom

theorem kappa_d (b : Γ((TM O M).left, ⊤)) :
    kappa O M (d (sec_hom (zeroSec O M)) le_top b) = (toTsze O M b).snd := by
  letI := (isChart O M).algebra
  letI := topModule O M
  change (AugCot.lift ((isChart O M).aug (sec_hom _)) (sndFn O M) (sndFn_der O M))
    (((isChart O M).augCotEquiv (sec_hom _)).symm (d (sec_hom (zeroSec O M)) le_top b)) = _
  rw [← (isChart O M).augCotEquiv_d (sec_hom _) b, LinearEquiv.symm_apply_apply, AugCot.lift_d]
  rfl

end Kappa

section Phi

variable {O : Type} [CommRing O]


variable (A : Over (Sp O)) [GrpObj A] in
def Wmod : Type := Γ(omega A, ⊤)

instance (A : Over (Sp O)) [GrpObj A] : AddCommGroup (Wmod A) :=
  inferInstanceAs (AddCommGroup Γ(omega A, ⊤))

instance (A : Over (Sp O)) [GrpObj A] : Module O (Wmod A) :=
  Module.compHom Γ(omega A, ⊤) (cst O)

variable {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]
  {A : Over (Sp O)} [GrpObj A]

def Phi (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) : Wmod A →+ M :=
  (kappa O M).comp (QCoh.appLinear (cotMap z h) ⊤).toAddMonoidHom

theorem Phi_apply (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (w : Wmod A) :
    Phi z h w = kappa O M ((cotMap z h).app ⊤ w) := rfl

end Phi

end GlobalTheory.SqZeroPt

namespace GlobalTheory.SqZeroPt

section Tower

open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {A : Over (Sp O)} [GrpObj A]
  {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]


end Tower

end GlobalTheory.SqZeroPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
def spanK (φ : Sm E a) : Submodule ℂ (Sm E a) := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)

theorem spanK_stable (φ : Sm E a) : ∀ k, ∀ w ∈ spanK E a φ, cptRep E a k w ∈ spanK E a φ := by
  intro k w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k', rfl⟩ := hx
    exact Submodule.subset_span ⟨k * k', by simp only [map_mul, mul_apply_eq_comp]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem self_mem_spanK (φ : Sm E a) : φ ∈ spanK E a φ :=
  Submodule.subset_span ⟨1, by simp only [map_one, one_apply_eq_self]⟩

def mapsJ (φ : Sm E a) (L : Subgroup (GL (Fin a) (Af E))) : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a) where
  carrier := {T | T ∈ maps L (spanK E a φ) (spanK_stable φ) ∧ ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T w) = 0}
  zero_mem' := ⟨zero_mem _, fun z _ _ w => by simp⟩
  add_mem' {T T'} h h' := ⟨add_mem h.1 h'.1, fun z hz h0 w => by
    simp [h.2 z hz h0 w, h'.2 z hz h0 w]⟩
  smul_mem' c T h := ⟨Submodule.smul_mem _ c h.1, fun z hz h0 w => by simp [h.2 z hz h0 w]⟩

end GlobalTheory.AutGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open GlobalTheory.VB GlobalTheory.Conormal
open GlobalTheory.KS.DerMorK (deformHom hom_ext_appLE)

namespace GlobalTheory.LieVB.TangentSurj

section General

variable {S X T : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (p : T ⟶ S) (ε : Γ(T, ⊤)) (hε : ε * ε = 0)
  (D : Der π e (structureModule S))

def val {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) : Γ(X, W) →+ Γ(S, V) := D.app h

theorem val_mul {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (f g : Γ(X, W)) :
    val D h (f * g) = e.appLE W V h f * val D h g + e.appLE W V h g * val D h f :=
  D.app_mul h f g

theorem val_base {W : X.Opens} {V U : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (k : W ≤ π ⁻¹ᵁ U) (a : Γ(S, U)) :
    val D h (π.appLE U W k a) = 0 := D.app_base h k a

theorem val_one {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) : val D h 1 = 0 := by
  simpa using val_base D (U := ⊤) h le_top 1

theorem val_res {W W' : X.Opens} (k : W' ≤ W) (f : Γ(X, W)) :
    val D (le_refl (e ⁻¹ᵁ W')) (resG X k f) = resG S (e.preimage_mono k) (val D le_rfl f) :=
  (D.app_res _ k f).trans (D.res_app le_rfl (e.preimage_mono k) f).symm


include hε in
theorem res_sq (U : T.Opens) : resG T (le_top : U ≤ ⊤) ε * resG T (le_top : U ≤ ⊤) ε = 0 := by
  rw [← map_mul, hε, map_zero]

def psi (W : X.Opens) : Γ(X, W) →+* Γ(T, p ⁻¹ᵁ e ⁻¹ᵁ W) where
  toFun f := p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) +
    p.appLE _ _ le_rfl (val D le_rfl f) * resG T le_top ε
  map_one' := by simp only [val_one, map_one, map_zero, zero_mul, add_zero]
  map_mul' f g := by
    simp only [val_mul, map_mul, map_add (f := _)]
    linear_combination -(p.appLE _ _ le_rfl (val D le_rfl f) * p.appLE _ _ le_rfl (val D le_rfl g)) *
      res_sq ε hε (p ⁻¹ᵁ e ⁻¹ᵁ W)
  map_zero' := by simp only [map_zero, zero_mul, add_zero]
  map_add' f g := by
    simp only [map_add (f := _)]
    ring

theorem psi_apply (W : X.Opens) (f : Γ(X, W)) : psi p ε hε D W f =
    p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) +
      p.appLE _ _ le_rfl (val D le_rfl f) * resG T le_top ε := rfl

theorem psi_nat (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)) :
    psi p ε hε D W' (resG X h f) =
      resG T (p.preimage_mono (e.preimage_mono h)) (psi p ε hε D W f) := by
  rw [psi_apply, psi_apply, val_res, map_add (f := _), map_mul, resG_resG, resG_appLE, resG_appLE,
    appLE_resG e, appLE_resG p, ← resG_appLE e (e.preimage_mono h) le_rfl, appLE_resG p]

theorem psi_nil (W : X.Opens) (f : Γ(X, W)) :
    IsNilpotent (psi p ε hε D W f - p.appLE _ _ le_rfl (e.appLE W _ le_rfl f)) := by
  refine ⟨2, ?_⟩
  rw [psi_apply]
  linear_combination (p.appLE _ _ le_rfl (val D le_rfl f)) ^ 2 * res_sq ε hε (p ⁻¹ᵁ e ⁻¹ᵁ W)

def deform : T ⟶ X :=
  deformHom (p ≫ e) (psi p ε hε D) (psi_nat p ε hε D) fun W f => by
    have h : ((p ≫ e).app W).hom f = p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) := by
      rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app]; rfl
    rw [h]
    exact psi_nil p ε hε D W f

theorem deform_appLE (W : X.Opens) {U : T.Opens} (k : U ≤ p ⁻¹ᵁ e ⁻¹ᵁ W) (f : Γ(X, W)) :
    (deform p ε hε D).appLE W U k f = resG T k (psi p ε hε D W f) := rfl

theorem deform_comp (he : e ≫ π = 𝟙 S) : deform p ε hε D ≫ π = p := by
  have h₀ : p ≫ e ≫ π = p := by rw [he, Category.comp_id]
  refine hom_ext_appLE (congr(($h₀).base)) fun U k => ?_
  ext a
  have k' : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ e ⁻¹ᵁ π ⁻¹ᵁ U := k
  refine (appLE_appLE (f := deform p ε hε D) rfl le_rfl k' k a).symm.trans ?_
  rw [deform_appLE, psi_apply, val_base, map_zero, zero_mul, add_zero,
    appLE_base he _ _ ((le_preimage_iff he).1 le_rfl), appLE_resG, resG_appLE,
    Scheme.Hom.appLE_eq_app]

theorem comp_deform {z : S ⟶ T} (hz : z ≫ p = 𝟙 S) (h0 : z.appLE ⊤ ⊤ le_top ε = 0) :
    z ≫ deform p ε hε D = e := by
  have h₀ : z ≫ p ≫ e = e := by rw [reassoc_of% hz]
  refine hom_ext_appLE (congr(($h₀).base)) fun W k => ?_
  ext f
  have k' : e ⁻¹ᵁ W ≤ z ⁻¹ᵁ p ⁻¹ᵁ e ⁻¹ᵁ W := k
  refine (appLE_appLE (f := z) (g := deform p ε hε D) (V := p ⁻¹ᵁ e ⁻¹ᵁ W)
    rfl le_rfl k' k f).symm.trans ?_
  rw [deform_appLE, resG_self, psi_apply, map_add (f := _), map_mul, appLE_resG,
    ← resG_appLE z le_top le_top ε, h0, map_zero, mul_zero, add_zero,
    appLE_base hz _ _ le_rfl, resG_self, Scheme.Hom.appLE_eq_app]

end General

variable (O : Type) [CommRing O]

theorem epsFn_sq : epsFn O * epsFn O = 0 := by
  have h := map_mul (Scheme.ΓSpecIso (.of (DualNumber O))).inv.hom DualNumber.eps DualNumber.eps
  rw [DualNumber.eps_mul_eps, map_zero] at h
  exact h.symm

theorem epsZero_epsFn : (sec (epsZero O)).appLE ⊤ ⊤ le_top (epsFn O) = 0 := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O O).toRingHom)) DualNumber.eps).symm.trans ?_
  exact (congrArg (Scheme.ΓSpecIso (.of O)).inv.hom (DualNumber.fst_eps (R := O))).trans
    (map_zero _)

theorem tangent_surjective (O : Type) [CommRing O] (G : Over (Sp O)) [GrpObj G] :
    Function.Surjective (tangent : LieG G → Γ(Lie G, ⊤)) := by
  intro l
  let D := lieEquivDer G l
  let x : specO O (DualNumber O) ⟶ G :=
    Over.homMk (deform (specO O (DualNumber O)).hom (epsFn O) (epsFn_sq O) D)
      (deform_comp _ _ _ D (sec_hom η[G]))
  have hx : ptMap (TrivSqZeroExt.fstHom O O O) ≫ x = toUnit (specO O O) ≫ η[G] := by
    have h : (toUnit (specO O O)).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    ext1
    simp only [Over.comp_left, h]
    exact (comp_deform _ _ (epsFn_sq O) D (sec_hom (epsZero O)) (epsZero_epsFn O)).trans
      (Category.id_comp _).symm
  refine ⟨⟨x, hx⟩, (homGlobalEquiv _ _).injective (omega_hom_ext fun W f => ?_)⟩
  refine dualApp_tangent_dUnit ⟨x, hx⟩ le_rfl f
    ((le_preimage_iff (sec_hom (epsZero O))).2 le_rfl) le_rfl le_rfl
    ((unitSec G).appLE W _ le_rfl f) (val D le_rfl f) ?_
  exact (deform_appLE _ _ (epsFn_sq O) D W le_rfl f).trans (resG_self _ _)

end GlobalTheory.LieVB.TangentSurj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
noncomputable section

open ValuativeRel
open scoped Matrix

namespace GlobalTheory.FullRankCoinv.UnitMinor

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def unitMinorSet (n d : ℕ) : Set (Matrix (Fin n) (Fin d) k) :=
  {Y | (∀ i j, Y i j ∈ 𝒪[k]) ∧ ∃ f : Fin n ↪ Fin d, valuation k (Y.submatrix id f).det = 1}

def lastCols (n d : ℕ) (h : n ≤ d) : Fin n ↪ Fin d :=
  ⟨fun i => ⟨d - n + i, by omega⟩, fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)⟩

theorem lastCols_val (n d : ℕ) (h : n ≤ d) (i : Fin n) : (lastCols n d h i : ℕ) = d - n + i := rfl

section
open MeasureTheory GlobalTheory.SplitFlip

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [-instance] CompanionTheory.QL.instMeasGL

variable {k}

theorem smallF_lact [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ) (h : GL (Fin n) k)
    (Φ : Matrix (Fin n) (Fin d) k → ℂ) (Y : Matrix (Fin n) (Fin d) k) :
    smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν (GlobalTheory.FullRankCoinv.lact ν h Φ) Y =
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y := by
  unfold smallF GlobalTheory.FullRankCoinv.lact
  have hI := integral_mul_left_eq_self (μ := haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))
    (fun g : GL (Fin n) k => Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
    (invT h)⁻¹
  rw [← hI]
  congr 1; funext g
  have e1 : gdet ((invT h)⁻¹ * g) = gdet h * gdet g := by
    rw [gdet_mul, show gdet (invT h)⁻¹ = (gdet (invT h))⁻¹ from map_inv _ _, gdet_invT, inv_inv]
  simp only [e1, Units.val_mul, invT_inv_val, map_mul, apow_mul, Matrix.mul_assoc, Fintype.card_fin]
  ring

end

end GlobalTheory.FullRankCoinv.UnitMinor
end
end
