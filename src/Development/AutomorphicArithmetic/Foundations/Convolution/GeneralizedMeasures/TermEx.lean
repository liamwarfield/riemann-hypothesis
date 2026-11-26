module

public import Development.AutomorphicArithmetic.AdelicGluing.OfinDoubleCosetIndicatorEqHop
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.InfAtFinEmb
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LocHeckeSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchOfScale
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.G1St

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AdelicGluing.ProdFnIsLocallyConstantHasCompactSupport
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open UpperTheory.ConvolutionTheory.GM.TE

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}

private theorem cmp_val (w : PlacesOver E v) (g : GL (Fin n) (CompletionsOver E v)) (i j : Fin n) :
    (UpperTheory.ConvolutionTheory.GM.cmp w g).val i j = g.val i j w := rfl

private theorem cmp_continuous (w : PlacesOver E v) :
    Continuous (UpperTheory.ConvolutionTheory.GM.cmp (n := n) w) := by
  have hv : Continuous fun g : GL (Fin n) (CompletionsOver E v) => (UpperTheory.ConvolutionTheory.GM.cmp w g).val := by
    refine continuous_matrix fun i j => ?_
    simp only [cmp_val]
    exact (continuous_apply w).comp (Units.continuous_val.matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hv, ?_⟩
  have : (fun g : GL (Fin n) (CompletionsOver E v) => ((UpperTheory.ConvolutionTheory.GM.cmp w g)⁻¹ : GL (Fin n) (w.1.adicCompletion E)).val)
      = (fun g => (UpperTheory.ConvolutionTheory.GM.cmp w g).val) ∘ fun g => g⁻¹ := by
    funext g
    simp [map_inv]
  exact this ▸ hv.comp continuous_inv

private theorem one_apply_pi (i j : Fin n) (w : PlacesOver E v) :
    (1 : Matrix (Fin n) (Fin n) (CompletionsOver E v)) i j w =
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j := by
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.one_apply_ne hij]

private noncomputable def glGlue (x : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E)) :
    GL (Fin n) (CompletionsOver E v) where
  val := Matrix.of fun i j w => (x w).val i j
  inv := Matrix.of fun i j w => ((x w)⁻¹ : GL (Fin n) (w.1.adicCompletion E)).val i j
  val_inv := by
    refine Matrix.ext fun i j => funext fun w => ?_
    have h1 := congrFun (congrFun (x w).val_inv i) j
    rw [Matrix.mul_apply] at h1
    rw [Matrix.mul_apply, Finset.sum_apply, one_apply_pi]
    exact h1
  inv_val := by
    refine Matrix.ext fun i j => funext fun w => ?_
    have h1 := congrFun (congrFun (x w).inv_val i) j
    rw [Matrix.mul_apply] at h1
    rw [Matrix.mul_apply, Finset.sum_apply, one_apply_pi]
    exact h1

private theorem glGlue_continuous :
    Continuous (glGlue (E := E) (n := n) (v := v)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => continuous_pi fun w => ?_
    exact (Units.continuous_val.matrix_elem i j).comp (continuous_apply w)
  · refine continuous_matrix fun i j => continuous_pi fun w => ?_
    exact (Units.continuous_val.matrix_elem i j).comp (continuous_inv.comp (continuous_apply w))

private theorem glGlue_cmp (g : GL (Fin n) (CompletionsOver E v)) :
    glGlue (fun w => UpperTheory.ConvolutionTheory.GM.cmp w g) = g := by
  ext i j w
  rfl

end

theorem UpperTheory.prodFn_isLocallyConstant_hasCompactSupport :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ),
        (∀ w, IsLocallyConstant (h w) ∧ HasCompactSupport (h w)) →
        IsLocallyConstant (prodFn h) ∧ HasCompactSupport (prodFn h) := by
  intro F E _ _ _ _ _ n v h hh
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  have hp : prodFn h = fun g => ∏ w, h w (UpperTheory.ConvolutionTheory.GM.cmp w g) := by
    funext g
    exact finprod_eq_prod_of_fintype _
  constructor
  · have key : ∀ s : Finset (PlacesOver E v),
        IsLocallyConstant fun g : GL (Fin n) (CompletionsOver E v) => ∏ w ∈ s, h w (UpperTheory.ConvolutionTheory.GM.cmp w g) := by
      classical
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        exact IsLocallyConstant.const (1 : ℂ)
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ((hh a).1.comp_continuous (cmp_continuous a)).mul ih
    rw [hp]
    exact key Finset.univ
  · have hK : IsCompact (glGlue '' Set.pi Set.univ fun w : PlacesOver E v => tsupport (h w)) :=
      (isCompact_univ_pi fun w => (hh w).2).image glGlue_continuous
    set_option synthInstance.maxHeartbeats 200000 in
      refine HasCompactSupport.of_support_subset_isCompact hK fun g hg => ?_
    refine ⟨fun w => UpperTheory.ConvolutionTheory.GM.cmp w g, fun w _ => subset_tsupport _ ?_, glGlue_cmp g⟩
    rw [Function.mem_support, hp] at hg
    intro h0
    exact hg (Finset.prod_eq_zero (Finset.mem_univ w) h0)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ClopenTest
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped Pointwise
open UpperTheory.ConvolutionTheory.GM.TE

namespace UpperTheory.ConvolutionTheory.GM.TE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem clopen_test {G : Type*} [TopologicalSpace G] [T2Space G] (A : Set G) (ho : IsOpen A) (hc : IsCompact A) :
    IsLocallyConstant (A.indicator (1 : G → ℂ)) ∧ HasCompactSupport (A.indicator (1 : G → ℂ)) := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ A
  · exact ⟨A, ho, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨Aᶜ, hc.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

private theorem test_int (w : Pl E) :
    IsLocallyConstant ((GLnLocal.integralGL (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))).indicator (1 : GL (Fin n) (w.adicCompletion E) → ℂ)) ∧
      HasCompactSupport ((GLnLocal.integralGL (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))).indicator (1 : GL (Fin n) (w.adicCompletion E) → ℂ)) :=
  clopen_test _ (GLnLocal.isOpen_integralGL _ n) (GLnLocal.isCompact_integralGL _ n)

private theorem iwCoset_eq (w : Pl E) (m : Fin n → ℤ) :
    iwCoset w m = ((GLnLocal.iwahori (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))) *
      ({Cartan.diagPow (w.adicCompletion E) n m} : Set (GL (Fin n) (w.adicCompletion E)))) * (GLnLocal.iwahori (w.adicCompletion E) n : Set (GL (Fin n) (w.adicCompletion E))) := by
  ext g
  simp only [iwCoset, Set.mem_setOf_eq, Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
  · rintro ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

private theorem test_iw (w : Pl E) (m : Fin n → ℤ) :
    IsLocallyConstant ((iwCoset w m).indicator (1 : GL (Fin n) (w.adicCompletion E) → ℂ)) ∧ HasCompactSupport ((iwCoset w m).indicator (1 : GL (Fin n) (w.adicCompletion E) → ℂ)) := by
  refine clopen_test _ ?_ ?_
  · rw [iwCoset_eq]
    exact (GLnLocal.isOpen_iwahori _ n).mul_left
  · rw [iwCoset_eq]
    exact ((GLnLocal.isCompact_iwahori _ n).mul isCompact_singleton).mul (GLnLocal.isCompact_iwahori _ n)

private theorem unit_prod (v : Pl F) :
    (prodFn fun w : PlacesOver E v => (GLnLocal.integralGL (w.1.adicCompletion E) n : Set (GL (Fin n) (w.1.adicCompletion E))).indicator (1 : GL (Fin n) (w.1.adicCompletion E) → ℂ)) =
      (unitSet E n v).indicator 1 := by
  funext g
  unfold prodFn
  by_cases hg : g ∈ unitSet E n v
  · rw [Set.indicator_of_mem hg]
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    have hm : cmp w g ∈ (GLnLocal.integralGL (w.1.adicCompletion E) n : Set (GL (Fin n) (w.1.adicCompletion E))) := hg w
    exact (Set.indicator_of_mem hm _).trans rfl
  · rw [Set.indicator_of_notMem hg]
    have : ∃ w : PlacesOver E v, cmp w g ∉ (GLnLocal.integralGL (w.1.adicCompletion E) n : Set _) := by
      by_contra hc
      push_neg at hc
      exact hg hc
    obtain ⟨w, hw⟩ := this
    exact finprod_eq_zero _ w (Set.indicator_of_notMem hw _) (Set.toFinite _)

private theorem det_int (w : Pl E) (a : GL (Fin n) (w.adicCompletion E)) (ha : a ∈ GLnLocal.integralGL (w.adicCompletion E) n) :
    Valued.v (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det = 1 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff _ _).1 ha
  have key : ∀ b : Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ i j, b i j ∈ (ValuativeRel.valuation (w.adicCompletion E)).integer) →
      Valued.v b.det ≤ 1 := fun b hb => by
    have hb' : ∀ i j, b i j ∈ w.adicCompletionIntegers E := fun i j => (mem_valuationInteger_iff w _).1 (hb i j)
    have : b.det ∈ w.adicCompletionIntegers E := by
      rw [Matrix.det_apply']
      exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hb' _ _)
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 this
  have k1 := key _ h1
  have k2 := key _ h2
  have hm : Valued.v (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det *
      Valued.v ((a⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm k1 ?_
  calc (1 : _) = _ := hm.symm
    _ ≤ _ * 1 := mul_le_mul_right k2 _
    _ = _ := mul_one _

private theorem det_one (w : Pl E) (m : Fin n → ℤ) (hs : ∑ i, m i = 0) (g : GL (Fin n) (w.adicCompletion E)) (hg : g ∈ iwCoset w m) :
    Valued.v (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  have hI := GLnLocal.iwahori_le_integralGL (w.adicCompletion E) n
  have hd : (Cartan.diagPow (w.adicCompletion E) n m : Matrix (Fin n) (Fin n) (w.adicCompletion E)).det = 1 := by
    rw [Cartan.coe_diagPow, Matrix.det_diagonal]
    have ht := Cartan.uniformizer_ne_zero (w.adicCompletion E)
    have : ∀ s : Finset (Fin n), ∏ i ∈ s, ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) ^ m i =
        ((GLnLocal.uniformizer (w.adicCompletion E) : _) : w.adicCompletion E) ^ (∑ i ∈ s, m i) := fun s => by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ht]
    rw [this, hs, zpow_zero]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hd, mul_one, map_mul, det_int w a (hI ha), det_int w b (hI hb), one_mul]

private theorem iw_zero (w : Pl E) (g : GL (Fin n) (w.adicCompletion E)) (hg : g ∈ iwCoset w (0 : Fin n → ℤ)) :
    g ∈ GLnLocal.iwahori (w.adicCompletion E) n := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  have hd : Cartan.diagPow (w.adicCompletion E) n (0 : Fin n → ℤ) = 1 := by
    apply Units.ext
    rw [Cartan.coe_diagPow]
    simp
  rw [hd, mul_one]
  exact mul_mem ha hb

private theorem iw_left (w : Pl E) (m : Fin n → ℤ) (a g : GL (Fin n) (w.adicCompletion E))
    (ha : a ∈ GLnLocal.iwahori (w.adicCompletion E) n) : a * g ∈ iwCoset w m ↔ g ∈ iwCoset w m := by
  constructor
  · rintro ⟨c, hc, b, hb, e⟩
    refine ⟨a⁻¹ * c, mul_mem (inv_mem ha) hc, b, hb, ?_⟩
    calc g = a⁻¹ * (a * g) := (inv_mul_cancel_left a g).symm
      _ = _ := by rw [e]; simp only [mul_assoc]
  · rintro ⟨c, hc, b, hb, rfl⟩
    exact ⟨a * c, mul_mem ha hc, b, hb, by simp only [mul_assoc]⟩

private theorem over_eq {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem at_eq {v : Pl F} (a b : AdelicGLn.FiniteAdelicGL E n) (h : ∀ w : PlacesOver E v, cf w.1 a = cf w.1 b) :
    mapGL n (atFin v) (finEmb E n a) = mapGL n (atFin v) (finEmb E n b) := by
  refine Units.ext (Matrix.ext fun i j => funext fun w => ?_)
  exact congrArg (fun g : GL (Fin n) (w.1.adicCompletion E) => (g : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) i j) (h w)

private theorem cf_mul (w : Pl E) (a b : AdelicGLn.FiniteAdelicGL E n) : cf w (a * b) = cf w a * cf w b := by
  simp only [cf, map_mul, finAt_mul]

private theorem cf_loc (w w' : Pl E) (hne : w ≠ w') (y : GL (Fin n) (w'.adicCompletion E)) (x : AdelicGLn.FiniteAdelicGL E n) :
    cf w (AdelicGLn.localEmbedding w' y * x) = cf w x := by
  rw [cf_mul]
  have : cf w (AdelicGLn.localEmbedding w' y) = 1 := (UpperTheory.ConvolutionTheory.Tf.locEmb E n w').2.2.1 w hne y
  rw [this, one_mul]

open Classical in
private theorem rF_congr (S : Finset (Pl F)) {q : Pl F} (w₀ : PlacesOver E q)
    (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (κ : Finset (Pl E)) (a b : AdelicGLn.FiniteAdelicGL E n)
    (h1 : ∀ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n a)) = ψ v (mapGL n (atFin v) (finEmb E n b)))
    (h2 : ∀ w : PlacesOver E q, w ≠ w₀ → (cf w.1 a ∈ iwCoset w.1 (0 : Fin n → ℤ) ↔ cf w.1 b ∈ iwCoset w.1 (0 : Fin n → ℤ)))
    (h3 : a ∈ Cnd S q κ ↔ b ∈ Cnd S q κ) : rF S w₀ ψ κ a = rF S w₀ ψ κ b := by
  unfold rF
  congr 1
  · congr 1
    · exact Finset.prod_congr rfl h1
    · refine finprod_congr fun w => ?_
      by_cases hw : w = w₀
      · rw [if_pos hw, if_pos hw]
      · rw [if_neg hw, if_neg hw]
        by_cases hb : cf w.1 b ∈ iwCoset w.1 (0 : Fin n → ℤ)
        · rw [Set.indicator_of_mem hb, Set.indicator_of_mem ((h2 w hw).2 hb)]; rfl
        · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (mt (h2 w hw).1 hb)]
  · by_cases hb : b ∈ Cnd S q κ
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (h3.2 hb)]; rfl
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (mt h3.1 hb)]

private theorem rF_free₀ (S : Finset (Pl F)) {q : Pl F} (hq : q ∉ S) (w₀ : PlacesOver E q)
    (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (κ : Finset (Pl E)) :
    Free w₀.1 (rF S w₀ ψ κ) := by
  intro y x
  refine rF_congr S w₀ ψ κ _ _ (fun v hv => ?_) (fun w hw => ?_) ?_
  · rw [at_eq _ x fun w => cf_loc w.1 w₀.1 (fun e => hq ?_) y x]
    rw [← over_eq w₀, ← e, over_eq w]
    exact hv
  · rw [cf_loc w.1 w₀.1 (fun e => hw (Subtype.ext e)) y x]
  · have : ∀ w : Pl E, w.under (𝓞 F) ≠ q → cf w (AdelicGLn.localEmbedding w₀.1 y * x) = cf w x := fun w hw =>
      cf_loc w w₀.1 (fun e => hw (e ▸ over_eq w₀)) y x
    constructor
    · intro h w a b c
      rw [← this w c]
      exact h w a b c
    · intro h w a b c
      rw [this w c]
      exact h w a b c

private theorem rF_free (S : Finset (Pl F)) {q : Pl F} (w₀ : PlacesOver E q)
    (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (κ : Finset (Pl E)) (w : Pl E) (hw : w ∈ κ)
    (hS : w.under (𝓞 F) ∉ S) (hq : w.under (𝓞 F) ≠ q) : Free w (rF S w₀ ψ κ) := by
  intro y x
  refine rF_congr S w₀ ψ κ _ _ (fun v hv => ?_) (fun w' _ => ?_) ?_
  · rw [at_eq _ x fun w' => cf_loc w'.1 w (fun e => hS ?_) y x]
    rw [← e, over_eq w']
    exact hv
  · rw [cf_loc w'.1 w (fun e => hq (by rw [← e, over_eq w'])) y x]
  · have : ∀ w' : Pl E, w' ∉ κ → cf w' (AdelicGLn.localEmbedding w y * x) = cf w' x := fun w' hw' =>
      cf_loc w' w (fun e => hw' (e ▸ hw)) y x
    constructor
    · intro h w' a b c
      rw [← this w' a]
      exact h w' a b c
    · intro h w' a b c
      rw [this w' a]
      exact h w' a b c

private theorem rF_inv (S : Finset (Pl F)) {q : Pl F} (w₀ : PlacesOver E q)
    (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (κ : Finset (Pl E)) (u : AdelicGLn.FiniteAdelicGL E n)
    (h1 : ∀ v ∈ S, ∀ g, ψ v (mapGL n (atFin v) (finEmb E n u) * g) = ψ v g)
    (h2 : ∀ w : PlacesOver E q, cf w.1 u ∈ GLnLocal.iwahori (w.1.adicCompletion E) n)
    (h3 : ∀ w : Pl E, w.under (𝓞 F) ∉ S → w.under (𝓞 F) ≠ q → cf w u ∈ GLnLocal.integralGL (w.adicCompletion E) n)
    (x : AdelicGLn.FiniteAdelicGL E n) : rF S w₀ ψ κ (u * x) = rF S w₀ ψ κ x := by
  refine rF_congr S w₀ ψ κ _ _ (fun v hv => ?_) (fun w _ => ?_) ?_
  · rw [map_mul, map_mul]
    exact h1 v hv _
  · rw [cf_mul]
    exact iw_left w.1 0 _ _ (h2 w)
  · constructor
    · intro h w a b c
      have := h w a b c
      rw [cf_mul] at this
      exact (Subgroup.mul_mem_cancel_left _ (h3 w b c)).1 this
    · intro h w a b c
      rw [cf_mul]
      exact mul_mem (h3 w b c) (h w a b c)

open Classical in
private theorem supp (S : Finset (Pl F)) {q : Pl F} (w₀ : PlacesOver E q)
    (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (κ : Finset (Pl E))
    (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ) (m : Fin n → ℤ) (x : AdelicGLn.FiniteAdelicGL E n)
    (hne : rF S w₀ ψ κ x * (iwCoset w₀.1 m).indicator 1 (cf w₀.1 x) * ∏ w ∈ κ, h w (cf w x) ≠ 0) :
    (∀ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n x)) ≠ 0) ∧ cf w₀.1 x ∈ iwCoset w₀.1 m ∧
      (∀ w : PlacesOver E q, w ≠ w₀ → cf w.1 x ∈ iwCoset w.1 (0 : Fin n → ℤ)) ∧ (∀ w ∈ κ, h w (cf w x) ≠ 0) ∧ x ∈ Cnd S q κ := by
  obtain ⟨hne1, hκ⟩ := mul_ne_zero_iff.1 hne
  obtain ⟨hr, hi⟩ := mul_ne_zero_iff.1 hne1
  unfold rF at hr
  obtain ⟨hr1, hc⟩ := mul_ne_zero_iff.1 hr
  obtain ⟨hs, hw⟩ := mul_ne_zero_iff.1 hr1
  refine ⟨Finset.prod_ne_zero_iff.1 hs, Set.mem_of_indicator_ne_zero hi, fun w hw' => ?_, Finset.prod_ne_zero_iff.1 hκ,
    Set.mem_of_indicator_ne_zero hc⟩
  haveI := Fintype.ofFinite (PlacesOver E q)
  rw [finprod_eq_prod_of_fintype] at hw
  have := Finset.prod_ne_zero_iff.1 hw w (Finset.mem_univ _)
  rw [if_neg hw'] at this
  exact Set.mem_of_indicator_ne_zero this

private theorem regroup (S : Finset (Pl F)) {q : Pl F} (hq : q ∉ S) (w₀ : PlacesOver E q)
    (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (κ : Finset (Pl E))
    (hκ : ∀ w ∈ κ, w.under (𝓞 F) ∉ S ∧ w.under (𝓞 F) ≠ q)
    (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ)
    (hh : ∀ w ∉ κ, h w = (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1)
    (m : Fin n → ℤ) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ)
    (h1 : ∀ v ∈ S, φ v = ψ v) (h2 : φ q = iwFn w₀ m)
    (h3 : ∀ v ∉ S, v ≠ q → φ v = prodFn fun w : PlacesOver E v => h w.1) (x : AdelicGLn.FiniteAdelicGL E n) :
    ∏ᶠ v, φ v (mapGL n (atFin v) (finEmb E n x)) =
      rF S w₀ ψ κ x * (iwCoset w₀.1 m).indicator 1 (cf w₀.1 x) * ∏ w ∈ κ, h w (cf w x) :=
  UpperTheory.finprod_local_factors_with_iwahori_at_place F E n S q hq w₀ ψ κ hκ h hh m φ h1 h2 h3 x

private theorem test_prod {v : Pl F} (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ)
    (hh : ∀ w, IsLocallyConstant (h w) ∧ HasCompactSupport (h w)) :
    IsLocallyConstant (prodFn h) ∧ HasCompactSupport (prodFn h) :=
  UpperTheory.prodFn_isLocallyConstant_hasCompactSupport F E n v h hh

private theorem ht_bound (S : Finset (Pl F)) (q : Pl F) (κ : Finset (Pl E))
    (ψ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ) (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ)
    (h1 : ∀ v ∈ S, HasCompactSupport (ψ v)) (h2 : ∀ w ∈ κ, HasCompactSupport (h w)) :
    ∃ Yf : ℝ, 1 ≤ Yf ∧ ∀ x : AdelicGLn.FiniteAdelicGL E n, (∀ v ∈ S, ψ v (mapGL n (atFin v) (finEmb E n x)) ≠ 0) →
      (∀ w ∈ κ, h w (cf w x) ≠ 0) → x ∈ Cnd S q κ → heightOff q (finEmb E n x) ≤ Yf :=
  UpperTheory.height_bounded_on_support_of_compact_test_functions F E n S q κ ψ h h1 h2

end UpperTheory.ConvolutionTheory.GM.TE

theorem UpperTheory.ConvolutionTheory.GM.termE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ) (q : Pl F) (w₀ : PlacesOver E q)
      (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (aE : TI E n) (L : Loc σ n q w₀) (ν : Fin n → ℤ), Good ν →
    ∀ 𝔢 : Side θ (Module.finrank F E), IsSideE L νE aE ν 𝔢 → ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ κ : Finset (Pl E), (∀ w ∈ κ, w ∉ 𝔢.S) →
    ∀ (p : Pl E → MvPolynomial (Fin n) ℂ) (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ), (∀ w ∈ κ, IsSph w (p w) (h w)) →
      (∀ w ∉ κ, h w = (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1) → ∃ Y₁ : ℝ, 1 ≤ Y₁ ∧
    ∀ ev, 𝔢.toAmp.IsEv ev → ∀ (j : ℕ) (wd : List (Option (Ix E n))) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ),
      (∀ v ∈ L.S, φ v = L.φ v) → φ q = iwFn w₀ (fun i => (j : ℤ) * ν i) →
      (∀ v ∉ L.S, v ≠ q → φ v = prodFn fun w : PlacesOver E v => h w.1) →
      ∃ f : TG E n, (∀ x, f x = avg (tensE (onInf (word νE aE (none :: wd))) φ) x) ∧
        Rop μ f = 𝔢.toAmp.A ∘L (ev (C (mono wd) * map C (∏ w ∈ κ, atPl w (p w))) ∘L 𝔢.Uq 0 ^ j) ∘L Rop μ 𝔢.g ∧
        Sup w₀ ν j (Y₁ * Y₀ ^ wd.length) f := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ θ q w₀ νE _ aE L ν hν 𝔢 hside
  obtain ⟨rfl, rfl, hS, hU, hg, hUq⟩ := hside
  obtain ⟨c, hc⟩ := tensHt F E n hn q
  obtain ⟨Y, hY1, hY⟩ := wordHt E n hn 𝔢.ν 𝔢.a₀ 𝔢.smooth
  have hq : q ∉ L.S := L.q_not
  have hsum : ∑ i, ν i = 0 := hν.2.1
  refine ⟨Y ^ c, one_le_pow₀ hY1, ?_⟩
  intro κ hκ p h hsph hoff
  have hκ' : ∀ w ∈ κ, w.under (𝓞 F) ∉ L.S ∧ w.under (𝓞 F) ≠ q := fun w hw => by
    have := hκ w hw
    rw [hS] at this
    push_neg at this
    exact this
  have ht : ∀ w, IsLocallyConstant (h w) ∧ HasCompactSupport (h w) := fun w => by
    by_cases hw : w ∈ κ
    · exact ⟨((sphEx E n hn w).2.2 _ _ (hsph w hw)).1, ((sphEx E n hn w).2.2 _ _ (hsph w hw)).2.1⟩
    · rw [hoff w hw]
      exact TE.test_int w
  obtain ⟨Yf, hYf1, hYf⟩ := TE.ht_bound L.S q κ L.φ h (fun v hv => (L.test v hv).2.1) (fun w _ => (ht w).2)
  obtain ⟨C₁, hC1, hC⟩ := hc Yf hYf1
  refine ⟨C₁ * Y ^ (2 * c), one_le_mul_of_one_le_of_one_le hC1 (one_le_pow₀ hY1), ?_⟩
  intro ev hev j wd φ h1 h2 h3
  have hφq : IsLocallyConstant (iwFn w₀ fun i => (j : ℤ) * ν i) ∧ HasCompactSupport (iwFn w₀ fun i => (j : ℤ) * ν i) :=
    TE.test_prod _ fun w => TE.test_iw w.1 _
  have hLq : IsLocallyConstant (iwFn w₀ (0 : Fin n → ℤ)) ∧ HasCompactSupport (iwFn w₀ (0 : Fin n → ℤ)) :=
    TE.test_prod _ fun w => TE.test_iw w.1 _
  obtain ⟨e₀, -, he₀, ht₀⟩ := avgE F E n hn (insert q L.S) 𝔢.a₀ L.φ (fun v hv => by
      rcases Finset.mem_insert.1 hv with hvq | hv
      · rw [hvq, L.at_q.1]; exact hLq
      · exact ⟨(L.test v hv).1, (L.test v hv).2.1⟩)
    (fun v hv => (L.off v (fun h => hv (Finset.mem_insert_of_mem h)) (fun h => hv (by rw [h]; exact Finset.mem_insert_self _ _))).1)
  obtain ⟨e₁, -, he₁, ht₁⟩ := avgE F E n hn (insert q (L.S ∪ κ.image fun w => w.under (𝓞 F))) (word 𝔢.ν 𝔢.a₀ (none :: wd)) φ
    (fun v hv => by
      by_cases hvq : v = q
      · rw [hvq, h2]; exact hφq
      by_cases hvS : v ∈ L.S
      · rw [h1 v hvS]; exact ⟨(L.test v hvS).1, (L.test v hvS).2.1⟩
      · rw [h3 v hvS hvq]; exact TE.test_prod _ fun w => ht w.1)
    (fun v hv => by
      have hvq : v ≠ q := fun h => hv (by rw [h]; exact Finset.mem_insert_self _ _)
      have hvS : v ∉ L.S := fun h => hv (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
      rw [h3 v hvS hvq, ← TE.unit_prod]
      congr 1
      funext w
      refine hoff w.1 fun hw => hv (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.2 ⟨w.1, hw, ?_⟩)))
      exact HeightOneSpectrum.ext w.2.over.symm)
  have hr₀ : ∀ x, e₀ x = TE.rF L.S w₀ L.φ κ x * (iwCoset w₀.1 0).indicator 1 (cf w₀.1 x) *
      ∏ w ∈ κ, (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1 (cf w x) := fun x => by
    rw [he₀, TE.regroup L.S hq w₀ L.φ κ hκ' (fun w => (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1)
      (fun _ _ => rfl) 0 L.φ (fun _ _ => rfl) L.at_q.1 (fun v hv hvq => by rw [(L.off v hv hvq).1, TE.unit_prod])]
  have hr₁ : ∀ x, e₁ x = TE.rF L.S w₀ L.φ κ x * (iwCoset w₀.1 fun i => (j : ℤ) * ν i).indicator 1 (cf w₀.1 x) *
      ∏ w ∈ κ, h w (cf w x) := fun x => by
    rw [he₁, TE.regroup L.S hq w₀ L.φ κ hκ' h hoff _ φ h1 h2 h3]
  have hinv : ∀ u ∈ 𝔢.U, cf w₀.1 u ∈ GLnLocal.iwahori (w₀.1.adicCompletion E) n ∧
      ∀ x, TE.rF L.S w₀ L.φ κ (u * x) = TE.rF L.S w₀ L.φ κ x := fun u hu => by
    rw [hU] at hu
    have hv : ∀ v, mapGL n (atFin v) (finEmb E n u) ∈ L.UE v := fun v => by
      have := (Subgroup.mem_iInf.1 hu) v
      exact this
    have hI : ∀ w : PlacesOver E q, cf w.1 u ∈ GLnLocal.iwahori (w.1.adicCompletion E) n := fun w =>
      (L.at_q.2.2.1 _).1 (hv q) w
    refine ⟨hI w₀, fun x => TE.rF_inv L.S w₀ L.φ κ u (fun v hS' g => (L.inv v hS').1 _ (hv v) g) hI (fun w hwS hwq => ?_) x⟩
    have := hv (w.under (𝓞 F))
    have h4 : mapGL n (atFin (w.under (𝓞 F))) (finEmb E n u) ∈ unitSet E n (w.under (𝓞 F)) := by
      rw [← (L.off _ hwS hwq).2.2.1]
      exact this
    exact h4 ⟨w, ⟨rfl⟩⟩
  have hg₀ : tens 𝔢.a₀ e₀ = 𝔢.g := by
    ext x
    rw [ht₀, hg]
  have hrep := repOne E n hn μ 𝔢.toAmp ev hev w₀.1 ((hS _).2 (Or.inr (HeightOneSpectrum.ext w₀.2.over.symm))) ν hν.1.antitone κ hκ p h hsph
    (TE.rF L.S w₀ L.φ κ) (TE.rF_free₀ L.S hq w₀ L.φ κ) (fun w hw => TE.rF_free L.S w₀ L.φ κ w hw (hκ' w hw).1 (hκ' w hw).2) hinv j wd e₀ e₁ hr₀ hr₁
  refine ⟨tens (word 𝔢.ν 𝔢.a₀ (none :: wd)) e₁, ht₁, ?_, ?_⟩
  · rw [hUq, ← hg₀]
    exact hrep
  · intro g hgne
    have hword : ∀ g', word 𝔢.ν 𝔢.a₀ (none :: wd) g' ≠ 0 → AutomorphicForm.height (infEmb E n g') ≤ Y ^ (wd.length + 2) :=
      fun g' hg' => hY _ g' hg'
    have hne : ∀ x, e₁ x ≠ 0 → heightOff q (finEmb E n x) ≤ Yf ∧
        ∀ w : PlacesOver E q, Valued.v (cf w.1 x : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)).det = 1 := fun x hx => by
      rw [hr₁] at hx
      obtain ⟨s1, s2, s3, s4, s5⟩ := TE.supp L.S w₀ L.φ κ h _ x hx
      refine ⟨hYf x s1 s4 s5, fun w => ?_⟩
      by_cases hw : w = w₀
      · subst hw
        exact TE.det_one w.1 _ (by rw [← Finset.mul_sum, hsum, mul_zero]) _ s2
      · exact TE.det_one w.1 0 (by simp) _ (s3 w hw)
    obtain ⟨b1, b2⟩ := hC _ e₁ (Y ^ (wd.length + 2)) (one_le_pow₀ hY1) hword hne _ hgne
    rw [hr₁] at b2
    obtain ⟨s1, s2, s3, s4, s5⟩ := TE.supp L.S w₀ L.φ κ h _ _ b2
    refine ⟨b1.trans (le_of_eq (by ring)), s2, fun w hw => TE.iw_zero w.1 _ (s3 w hw)⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocAll
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

namespace UpperTheory.ConvolutionTheory.GM.LocalAllPlaces

private theorem sph_unique {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (p : MvPolynomial (Fin n) ℂ)
    (h h' : GL (Fin n) (w.adicCompletion K) → ℂ) (a : IsSph w p h) (b : IsSph w p h') : h = h' := by
  obtain ⟨m1, b1, μ1, h1, hμ1, H1, e1, s1⟩ := a
  obtain ⟨m2, b2, μ2, h2, hμ2, H2, e2, s2⟩ := b
  obtain rfl : m1 = m2 := b1.measurable_eq.trans b2.measurable_eq.symm
  obtain rfl : μ1 = μ2 := by
    have h := Measure.isMulLeftInvariant_eq_smul μ1 μ2
    have h3 := congrArg (fun m : Measure _ => m (GLnLocal.integralGL (w.adicCompletion K) n)) h
    simp only [Measure.smul_apply, hμ1, hμ2] at h3
    have h4 : Measure.haarScalarFactor μ1 μ2 = 1 := by
      have : ((Measure.haarScalarFactor μ1 μ2 : NNReal) : ENNReal) = 1 := by
        rw [h3]; simp [ENNReal.smul_def]
      exact_mod_cast this
    rw [h4, one_smul] at h
    exact h
  obtain rfl : H1 = H2 := satakeTransform_injective (s1.trans s2.symm)
  funext x
  rw [← e1, ← e2]

private theorem powE_one {n : ℕ} (i : Fin n) : powE 1 i = X i := by
  unfold powE
  rw [AlgEquiv.symm_apply_eq]
  apply Subtype.ext
  simp [esymmAlgEquiv_apply, esymmAlgHom_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem over_iff (v : Pl F) (w : Pl E) : w.asIdeal.LiesOver v.asIdeal ↔ w.under (𝓞 F) = v := by
  constructor
  · intro h
    exact HeightOneSpectrum.ext h.over.symm
  · rintro rfl
    exact ⟨rfl⟩

private theorem resDeg_split (v : Pl F) (hs : Split E v) (w : PlacesOver E v) : resDeg F w.1 = 1 := by
  have h := finrank_eq_ramificationIdx_mul_inertiaDeg E v w.1
  have h1 : Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = 1 :=
    Module.finrank_of_bijective_algebraMap ⟨(completionMap v w.1).injective, hs w⟩
  rw [h1] at h
  exact Nat.eq_one_of_mul_eq_one_left h.symm

private theorem resDeg_inert (v : Pl F) (hu : Unr E v) (w : PlacesOver E v) (hw : ∀ w' : PlacesOver E v, w' = w) :
    resDeg F w.1 = Module.finrank F E := by
  have he : w.1.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_iff.2 (hu w)
  rw [← sum_ramificationIdx_mul_inertiaDeg E v, Finset.sum_eq_single w (fun b _ hb => absurd (hw b) hb) (by simp), he, one_mul]
  rfl

open Classical in
private theorem prod_filter {M : Type} [CommMonoid M] (κ : Finset (Pl E)) (v : Pl F) (a : Pl E → M) :
    ∏ w ∈ κ.filter (fun w => w.under (𝓞 F) = v), a w = ∏ w : PlacesOver E v, if w.1 ∈ κ then a w.1 else 1 := by
  rw [← Finset.prod_filter]
  symm
  refine Finset.prod_bij (fun w _ => w.1) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact ⟨hw, (over_iff v w.1).1 w.2⟩
  · intro w _ w' _ h
    exact Subtype.ext h
  · intro w hw
    simp only [Finset.mem_filter] at hw
    exact ⟨⟨w, (over_iff v w).2 hw.2⟩, by simp [hw.1], rfl⟩
  · intro w _
    rfl

end UpperTheory.ConvolutionTheory.GM.LocalAllPlaces

open UpperTheory.ConvolutionTheory.GM.LocalAllPlaces in
theorem UpperTheory.ConvolutionTheory.GM.locAll :
    LocUnit → LocAll := by
  classical
  intro hU F E _ _ _ _ _ _ _ _ σ hσ hp n hn κ hκ t₀ ht D
  have key : ∀ w : Pl E, ∃ γ : MvPolynomial (Fin n) ℂ,
      (w ∈ κ → eval (fun i : Fin n => (t₀ w).esymm (i + 1)) γ ≠ 0) ∧
      (w ∈ κ → ∀ (v : Pl F) (hw : w.asIdeal.LiesOver v.asIdeal), ¬ Split E v →
        ∀ p : MvPolynomial (Fin n) ℂ, p.totalDegree ≤ D → ∀ h f, IsSph w (γ * p) h →
          IsSph v (aeval (powE (Module.finrank F E)) (γ * p)) f →
          MatchAt σ v 1 (fun g => h (cmp (⟨w, hw⟩ : PlacesOver E v) g)) f) := by
    intro w
    by_cases hw : w ∈ κ
    · by_cases hs : Split E (w.under (𝓞 F))
      · refine ⟨1, fun _ => by simp, fun _ v hv hns => ?_⟩
        obtain rfl := (over_iff v w).1 hv
        exact absurd hs hns
      · obtain ⟨γ, h1, h2⟩ := UpperTheory.ConvolutionTheory.H.locHeckeInert F E σ hσ hp n hn _ (hκ w hw) hs ⟨w, ⟨rfl⟩⟩ (t₀ w)
          (ht w hw).1 (ht w hw).2 D
        refine ⟨γ, fun _ => h1, fun _ v hv _ => ?_⟩
        obtain rfl := (over_iff v w).1 hv
        exact h2
    · exact ⟨1, fun h => absurd h hw, fun h => absurd h hw⟩
  choose γ hγ1 hγ2 using key
  refine ⟨γ, hγ1, fun p hpD v hv h f hh hh' hf => ?_⟩
  rw [prod_filter] at hf
  by_cases hs : Split E v
  · refine UpperTheory.ConvolutionTheory.L1.locHeckeSplit F E σ hσ hp n hn v hs (fun w => if w.1 ∈ κ then γ w.1 * p w.1 else 1)
      (fun w => h w.1) f (fun w => ?_) ?_
    · by_cases hw : w.1 ∈ κ
      · simpa only [if_pos hw] using hh _ hw
      · simp only [if_neg hw, hh' _ hw]
        exact (sphEx E n hn w.1).2.1
    · rw [finprod_eq_prod_of_fintype]
      convert hf using 2 with w
      have : (powE 1 : Fin n → MvPolynomial (Fin n) ℂ) = X := funext powE_one
      rw [resDeg_split v hs w, this, aeval_X_left_apply]
  · obtain ⟨w, hw⟩ := UpperTheory.V.Z.Tf.Orb.placeUniq_holds F E hp v hs
    rw [Finset.prod_eq_single w (fun b _ hb => absurd (hw b) hb) (by simp)] at hf
    have e : (prodFn fun w : PlacesOver E v => h w.1) = fun g => h w.1 (cmp w g) := by
      funext g
      exact finprod_eq_single _ w fun b hb => absurd (hw b) hb
    rw [e]
    by_cases hk : w.1 ∈ κ
    · rw [if_pos hk, resDeg_inert v hv w hw] at hf
      exact hγ2 w.1 hk v w.2 hs (p w.1) (hpD _ hk) _ f (hh _ hk) hf
    · rw [if_neg hk] at hf
      rw [sph_unique v 1 _ _ hf (sphEx F n hn v).2.1, hh' _ hk]
      have e2 : (fun g => (GLnLocal.integralGL (w.1.adicCompletion E) n : Set _).indicator
          (1 : GL (Fin n) (w.1.adicCompletion E) → ℂ) (cmp w g)) =
          (unitSet E n v).indicator 1 := by
        funext g
        have : g ∈ unitSet E n v ↔ cmp w g ∈ (GLnLocal.integralGL (w.1.adicCompletion E) n : Set _) :=
          ⟨fun hg => hg w, fun hg w' => by rw [hw w']; exact hg⟩
        by_cases hg : g ∈ unitSet E n v
        · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (this.1 hg)]; rfl
        · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt this.2 hg)]
      rw [e2]
      exact hU F E σ hσ hp n hn v hv
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.BcPoly
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem bc_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (w : Pl E) (p : MvPolynomial (Fin n) ℂ) :
    bcPR F (map C (atPl w p) : PR E n) = map C (atPl (w.under (𝓞 F)) (aeval (powE (resDeg F w)) p)) := by
  unfold atPl
  induction p using MvPolynomial.induction_on with
  | C a => simp [bcPR]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    simp [bcPR]

private theorem bc_mono {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (wd : List (Option (Ix E n))) : bcPR F (C (mono wd) : PR E n) = C (mono (wd.map (resIx F))) := by
  unfold mono
  induction wd with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih]
    simp [bcPR, resIx]

theorem UpperTheory.ConvolutionTheory.GM.bcPoly :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (κ : Finset (Pl E)) (κF : Finset (Pl F)), (∀ w ∈ κ, w.under (𝓞 F) ∈ κF) →
    ∀ (p : Pl E → MvPolynomial (Fin n) ℂ) (wd : List (Option (Ix E n))) [DecidableEq (Pl F)],
      bcPR F (C (mono wd) * map C (∏ w ∈ κ, atPl w (p w))) = C (mono (wd.map (resIx F))) *
        map C (∏ v ∈ κF, atPl v (∏ w ∈ κ.filter fun w => w.under (𝓞 F) = v, aeval (powE (resDeg F w)) (p w))) := by
  intro F E _ _ _ _ _ n κ κF hκ p wd _
  rw [map_mul, bc_mono, map_prod, map_prod]
  congr 1
  simp only [bc_at]
  rw [← map_prod, ← Finset.prod_fiberwise_of_maps_to hκ]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  unfold atPl
  rw [map_prod]
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [(Finset.mem_filter.1 hw).2]
end

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private def glue {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] {n : ℕ} (g : ∀ i, GL (Fin n) (R i)) :
    GL (Fin n) (∀ i, R i) where
  val := Matrix.of fun a b i => (g i : Matrix (Fin n) (Fin n) (R i)) a b
  inv := Matrix.of fun a b i => ((g i)⁻¹ : GL (Fin n) (R i)) a b
  val_inv := by
    ext a b i
    have := congrFun (congrFun (g i).mul_inv a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Matrix.one_apply] at this ⊢
    rw [this]; split_ifs <;> rfl
  inv_val := by
    ext a b i
    have := congrFun (congrFun (g i).inv_mul a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply, Matrix.one_apply] at this ⊢
    rw [this]; split_ifs <;> rfl

private theorem glue_cont {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] [∀ i, TopologicalSpace (R i)] {n : ℕ} :
    Continuous (glue : (∀ i, GL (Fin n) (R i)) → GL (Fin n) (∀ i, R i)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun a => continuous_pi fun b => continuous_pi fun i => ?_
    exact (Units.continuous_val.comp (continuous_apply i)).matrix_elem a b
  · refine continuous_pi fun a => continuous_pi fun b => continuous_pi fun i => ?_
    exact (Units.continuous_coe_inv.comp (continuous_apply i)).matrix_elem a b

private theorem cmp_cont {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}
    (w : PlacesOver E v) : Continuous (cmp (n := n) w) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply w).comp (Units.continuous_val.matrix_elem a b)
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply w).comp (Units.continuous_coe_inv.matrix_elem a b)

private theorem prodFn_test {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}
    (h : ∀ w : PlacesOver E v, GL (Fin n) (w.1.adicCompletion E) → ℂ) (hc : ∀ w, Continuous (h w) ∧ HasCompactSupport (h w)) :
    Continuous (prodFn h) ∧ HasCompactSupport (prodFn h) := by
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  have e : prodFn h = fun g => ∏ w, h w (cmp w g) := funext fun g => finprod_eq_prod_of_fintype _
  rw [e]
  refine ⟨continuous_finsetProd _ fun w _ => (hc w).1.comp (cmp_cont w), ?_⟩
  haveI : T2Space (CompletionsOver E v) := Pi.t2Space
  haveI : T2Space (GL (Fin n) (CompletionsOver E v)) := Units.instT2Space
  haveI : R1Space (GL (Fin n) (CompletionsOver E v)) := T2Space.r1Space
  refine HasCompactSupport.intro ((isCompact_univ_pi fun w => (hc w).2.isCompact).image glue_cont) fun g hg => ?_
  by_contra hne
  refine hg ⟨fun w => cmp w g, fun w _ => subset_tsupport _ ?_, ?_⟩
  · exact fun h0 => hne (Finset.prod_eq_zero (Finset.mem_univ w) h0)
  · exact Units.ext (Matrix.ext fun a b => rfl)

private theorem prodFn_unit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F} :
    (prodFn fun w : PlacesOver E v => (GLnLocal.integralGL (w.1.adicCompletion E) n : Set _).indicator 1) =
      (unitSet E n v).indicator 1 := by
  haveI : Fintype (PlacesOver E v) := Fintype.ofFinite _
  funext g
  rw [prodFn, finprod_eq_prod_of_fintype]
  by_cases hg : g ∈ unitSet E n v
  · rw [Set.indicator_of_mem hg]
    exact Finset.prod_eq_one fun w _ => Set.indicator_of_mem (hg w) _
  · rw [Set.indicator_of_notMem hg]
    obtain ⟨w, hw⟩ := not_forall.1 hg
    exact Finset.prod_eq_zero (Finset.mem_univ w) (Set.indicator_of_notMem hw _)

open scoped Pointwise in
private theorem iwCoset_test {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (ν : Fin n → ℤ) :
    Continuous ((iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ)) ∧ HasCompactSupport ((iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ)) := by
  have e : iwCoset w ν = (GLnLocal.iwahori (w.adicCompletion K) n : Set _) * {Cartan.diagPow (w.adicCompletion K) n ν} *
      (GLnLocal.iwahori (w.adicCompletion K) n : Set _) := by
    ext g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact Set.mul_mem_mul (Set.mul_mem_mul ha rfl) hb
    · rintro ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hc : IsCompact (iwCoset w ν) := by
    rw [e]; exact ((GLnLocal.isCompact_iwahori _ _).mul isCompact_singleton).mul (GLnLocal.isCompact_iwahori _ _)
  have ho : IsOpen (iwCoset w ν) := by
    rw [e]; exact (GLnLocal.isOpen_iwahori _ _).mul_left
  exact ⟨IsClopen.continuous_indicator ⟨hc.isClosed, ho⟩ continuous_const,
    HasCompactSupport.intro hc fun g hg => Set.indicator_of_notMem hg _⟩

open Classical in
private theorem mono_split {E : Type} [Field E] [NumberField E] {n : ℕ} (κ : Finset (Pl E)) (β : Pl E × Fin n →₀ ℕ)
    (hβ : ∀ x ∈ β.support, x.1 ∈ κ) : ∃ p : Pl E → MvPolynomial (Fin n) ℂ, (∀ w ∈ κ, (p w).totalDegree ≤ β.degree) ∧
      ∏ w ∈ κ, atPl w (p w) = monomial β 1 := by
  refine ⟨fun w => ∏ i, X i ^ β (w, i), fun w _ => ?_, ?_⟩
  · refine (totalDegree_finsetProd _ _).trans ?_
    simp only [totalDegree_X_pow]
    have h1 : ∑ i, β (w, i) = ∑ x ∈ Finset.univ.image (fun i : Fin n => (w, i)), β x := by
      rw [Finset.sum_image]; intro a _ b _ h; exact (Prod.ext_iff.1 h).2
    rw [h1, Finsupp.degree_apply]
    exact Finset.sum_le_sum_of_ne_zero fun x _ hx => Finsupp.mem_support_iff.2 hx
  · simp only [atPl, map_prod, map_pow, rename_X]
    rw [← Finset.prod_product' κ Finset.univ (fun w i => (X (w, i) : MvPolynomial (Pl E × Fin n) ℂ) ^ β (w, i)), monomial_eq, C_1, one_mul,
      Finsupp.prod_of_support_subset β (s := κ ×ˢ Finset.univ) (fun x hx => Finset.mem_product.2 ⟨hβ x hx, Finset.mem_univ _⟩) _
        (fun _ _ => pow_zero _)]

private theorem sup_mono {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {n : ℕ} {q : Pl F}
    {w₀ : PlacesOver K q} {ν : Fin n → ℤ} {j : ℕ} {Y Y' : ℝ} {f : normOneGL (K := K) (n := n) → ℂ} (h : Sup w₀ ν j Y f) (hY : Y ≤ Y') :
    Sup w₀ ν j Y' f := fun g hg => ⟨(h g hg).1.trans hY, (h g hg).2⟩

private theorem under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem onInf_test {K : Type} [Field K] [NumberField K] {n : ℕ} (β : TI K n) :
    Continuous (onInf β) ∧ HasCompactSupport (onInf β) :=
  ⟨β.continuous.comp (archEquiv K n).continuous, β.hasCompactSupport.comp_homeomorph (archEquiv K n).toHomeomorph⟩

set_option maxHeartbeats 1000000 in
theorem UpperTheory.ConvolutionTheory.GM.termEx :
    LocUnit → TermEx := by
  intro hU F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE iμE μF iμF θ q w₀ q₀ hq νE _ νF _ aE aF ci hci hA
  classical
  letI : MeasurableSpace (GL (Fin n) (InfiniteAdeleRing E)) := borel _
  haveI : BorelSpace (GL (Fin n) (InfiniteAdeleRing E)) := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin n) (InfiniteAdeleRing F)) := borel _
  haveI : BorelSpace (GL (Fin n) (InfiniteAdeleRing F)) := ⟨rfl⟩
  choose s1 b1 s2 b2 mE mF hm using fun v => (matchOne F E σ n v).1
  obtain ⟨k, hk, H4⟩ := UpperTheory.ConvolutionTheory.G.g4 F E σ hσ n hn hp μE μF (νE.map (archEquiv E n).symm) (νF.map (archEquiv F n).symm) mE mF
    iμE iμF ((archEquiv E n).symm.isHaarMeasure_map νE) ((archEquiv F n).symm.isHaarMeasure_map νF)
    (fun v => ⟨(hm v).1, (hm v).2.2.1⟩) (fun v => ⟨(hm v).2.1, (hm v).2.2.2⟩)
  obtain ⟨cq, hcq, HQ⟩ := UpperTheory.ConvolutionTheory.L1.locQ F E σ hσ hp n hn q hq
  refine ⟨k * ci * cq, by positivity, fun L ν hν 𝔢 𝔣 he hf => ?_⟩
  obtain ⟨YE, hYE, TE⟩ := termE F E σ hσ hp n hn μE θ q w₀ νE aE L ν hν 𝔢 he
  obtain ⟨YF, hYF, TF⟩ := termF F E σ hσ hp n hn μF q w₀ q₀ νF aF L ν hν 𝔣 hf
  refine ⟨max YE YF, le_max_of_le_left hYE, fun κ hκ t₀ ht D => ?_⟩
  have hκ' : ∀ w ∈ κ, w.under (𝓞 F) ∉ L.S ∧ w.under (𝓞 F) ≠ q := fun w hw => not_or.1 (mt (he.2.2.1 w).2 (hκ w hw))
  obtain ⟨γ, hγ, LA⟩ := locAll hU F E σ hσ hp n hn κ (fun w hw => L.unr _ (hκ' w hw).1) t₀ ht D
  refine ⟨∏ w ∈ κ, atPl w (γ w), fun x hx => ?_, ?_, fun β hβ hD => ?_⟩
  · obtain ⟨w, hw, hx⟩ := Finset.mem_biUnion.1 (vars_prod _ hx)
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (vars_rename _ _ hx)
    exact hw
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun w hw => ?_
    rw [atPl, eval_rename]
    exact hγ w hw
  obtain ⟨p, hp1, hp2⟩ := mono_split κ β hβ
  have hhE : ∀ w : Pl E, ∃ h : GL (Fin n) (w.adicCompletion E) → ℂ, (w ∈ κ → IsSph w (γ w * p w) h) ∧
      (w ∉ κ → h = (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1) ∧ Continuous h ∧ HasCompactSupport h := by
    intro w
    obtain ⟨a, b, c⟩ := sphEx E n hn w
    by_cases hw : w ∈ κ
    · obtain ⟨h, hh⟩ := a (γ w * p w)
      exact ⟨h, fun _ => hh, fun h' => absurd hw h', (c _ _ hh).1.continuous, (c _ _ hh).2.1⟩
    · exact ⟨_, fun h' => absurd h' hw, fun _ => rfl, (c _ _ b).1.continuous, (c _ _ b).2.1⟩
  choose h h1 h2 h3 using hhE
  obtain ⟨κF, hκF⟩ : ∃ κF : Finset (Pl F), ∀ v, v ∈ κF ↔ ∃ w ∈ κ, w.under (𝓞 F) = v :=
    ⟨κ.image fun w => w.under (𝓞 F), fun v => Finset.mem_image⟩
  have hhF : ∀ v : Pl F, ∃ f : GL (Fin n) (v.adicCompletion F) → ℂ,
      IsSph v (∏ w ∈ κ.filter fun w => w.under (𝓞 F) = v, aeval (powE (resDeg F w)) (γ w * p w)) f ∧
      (v ∉ κF → f = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1) ∧ Continuous f ∧ HasCompactSupport f := by
    intro v
    obtain ⟨a, b, c⟩ := sphEx F n hn v
    by_cases hv : v ∈ κF
    · obtain ⟨f, hh⟩ := a (∏ w ∈ κ.filter fun w => w.under (𝓞 F) = v, aeval (powE (resDeg F w)) (γ w * p w))
      exact ⟨f, hh, fun h' => absurd hv h', (c _ _ hh).1.continuous, (c _ _ hh).2.1⟩
    · refine ⟨_, ?_, fun _ => rfl, (c _ _ b).1.continuous, (c _ _ b).2.1⟩
      rw [Finset.filter_eq_empty_iff.2 fun w hw e => hv ((hκF v).2 ⟨w, hw, e⟩), Finset.prod_empty]
      exact b
  choose f f1 f2 f3 using hhF
  have hκF' : ∀ v ∈ κF, v ∉ L.S ∧ v ≠ q := fun v hv => by
    obtain ⟨w, hw, rfl⟩ := (hκF v).1 hv
    exact hκ' w hw
  obtain ⟨Y1, hY1, TE⟩ := TE κ hκ (fun w => γ w * p w) h h1 h2
  obtain ⟨Y2, hY2, TF⟩ := TF κF (fun v hv => mt (hf.2.2.1 v).1 (not_or.2 (hκF' v hv))) _ f (fun v _ => f1 v) f2
  refine ⟨max Y1 Y2, le_max_of_le_left hY1, fun evE evF hE hF j wd => ?_⟩
  obtain ⟨φ, φS, φq, φo⟩ : ∃ φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ, (∀ v ∈ L.S, φ v = L.φ v) ∧
      φ q = iwFn w₀ (fun i => (j : ℤ) * ν i) ∧ ∀ v ∉ L.S, v ≠ q → φ v = prodFn fun w : PlacesOver E v => h w.1 :=
    ⟨Function.update (fun v => if v ∈ L.S then L.φ v else prodFn fun w : PlacesOver E v => h w.1) q (iwFn w₀ fun i => (j : ℤ) * ν i),
      fun v hv => by rw [Function.update_of_ne (fun e : v = q => L.q_not (e ▸ hv)), if_pos hv], Function.update_self ..,
      fun v hv hvq => by rw [Function.update_of_ne hvq, if_neg hv]⟩
  obtain ⟨ψ, ψS, ψq, ψo⟩ : ∃ ψ : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ, (∀ v ∈ L.S, ψ v = L.f v) ∧
      ψ q = (iwCoset q fun i => (j : ℤ) * ν i).indicator 1 ∧ ∀ v ∉ L.S, v ≠ q → ψ v = f v :=
    ⟨Function.update (fun v => if v ∈ L.S then L.f v else f v) q ((iwCoset q fun i => (j : ℤ) * ν i).indicator 1),
      fun v hv => by rw [Function.update_of_ne (fun e : v = q => L.q_not (e ▸ hv)), if_pos hv], Function.update_self ..,
      fun v hv hvq => by rw [Function.update_of_ne hvq, if_neg hv]⟩
  obtain ⟨c, cS, cq', co⟩ : ∃ c : Pl F → ℂ, (∀ v ∈ L.S, c v = L.c v) ∧ c q = cq ∧ ∀ v ∉ L.S, v ≠ q → c v = 1 :=
    ⟨Function.update (fun v => if v ∈ L.S then L.c v else 1) q cq,
      fun v hv => by rw [Function.update_of_ne (fun e : v = q => L.q_not (e ▸ hv)), if_pos hv], Function.update_self ..,
      fun v hv hvq => by rw [Function.update_of_ne hvq, if_neg hv]⟩
  obtain ⟨fE, e1, e2, e3⟩ := TE evE hE j wd φ φS φq φo
  obtain ⟨fF, g1, g2, g3⟩ := TF evF hF j (wd.map (resIx F)) ψ ψS ψq ψo
  have hpoly : (map C (∏ w ∈ κ, atPl w (γ w)) * monomial β (mono wd) : PR E n) =
      C (mono wd) * map C (∏ w ∈ κ, atPl w (γ w * p w)) := by
    have : ∏ w ∈ κ, atPl w (γ w * p w) = (∏ w ∈ κ, atPl w (γ w)) * monomial β 1 := by
      rw [← hp2, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun w _ => map_mul (rename _) _ _
    rw [this, map_mul, map_monomial, C_1, mul_left_comm, C_mul_monomial, mul_one]
  rw [List.length_map] at g3
  have h0 : (0 : ℝ) ≤ max Y1 Y2 := le_max_of_le_left (zero_le_one.trans hY1)
  refine ⟨fE, fF, by rw [hpoly]; exact e2, ?_, sup_mono e3 ?_, sup_mono g3 ?_, ?_⟩
  · rw [hpoly, bcPoly F E n κ κF (fun w hw => (hκF _).2 ⟨w, hw, rfl⟩)]
    exact g2
  · exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (zero_le_one.trans hYE) (le_max_left _ _) _) (by positivity) h0
  · exact mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (zero_le_one.trans hYF) (le_max_right _ _) _) (by positivity) h0
  have key := H4 (insert q (L.S ∪ κF)) (onInf (word νE aE (none :: wd))) (onInf (word νF aF (none :: wd.map (resIx F)))) φ ψ ci c
    (onInf_test _).1 (onInf_test _).2 (onInf_test _).1 (onInf_test _).2 (fun v => ?_) (fun v hv => ?_) (hA (none :: wd)) (fun v => ?_)
  · have hc : (k : ℂ) * ci * ∏ v ∈ insert q (L.S ∪ κF), c v = ((k * ci * cq : ℝ) : ℂ) * ∏ v ∈ L.S, L.c v := by
      rw [Finset.prod_insert (by
          rw [Finset.mem_union, not_or]; exact ⟨L.q_not, fun h => (hκF' q h).2 rfl⟩),
        Finset.prod_union (Finset.disjoint_right.2 fun v hv => (hκF' v hv).1),
        Finset.prod_eq_one fun v hv => co v (hκF' v hv).1 (hκF' v hv).2, Finset.prod_congr rfl cS, cq']
      push_cast
      ring
    rw [hc, ← funext e1, ← funext g1] at key
    exact key
  · by_cases hv : v ∈ L.S
    · rw [φS v hv, ψS v hv]
      obtain ⟨a1, a2, a3, a4⟩ := L.test v hv
      exact ⟨a1.continuous, a2, a3.continuous, a4⟩
    by_cases hvq : v = q
    · subst hvq
      rw [φq, ψq]
      have := prodFn_test (fun w : PlacesOver E v => (iwCoset w.1 (if w = w₀ then (fun i => (j : ℤ) * ν i) else 0)).indicator 1)
        fun w => iwCoset_test _ _
      exact ⟨this.1, this.2, iwCoset_test _ _⟩
    · rw [φo v hv hvq, ψo v hv hvq]
      have := prodFn_test (fun w : PlacesOver E v => h w.1) fun w => h3 w.1
      exact ⟨this.1, this.2, f3 v⟩
  · rw [Finset.mem_insert, Finset.mem_union, not_or, not_or] at hv
    rw [φo v hv.2.1 hv.1, ψo v hv.2.1 hv.1]
    refine ⟨?_, f2 v hv.2.2, co v hv.2.1 hv.1⟩
    rw [← prodFn_unit]
    congr 1
    funext w
    exact h2 w.1 fun hw => hv.2.2 ((hκF v).2 ⟨w.1, hw, under_eq w⟩)
  · refine (?_ : MatchAt σ v (c v) (φ v) (ψ v)) (mE v) (mF v) (hm v).1 (hm v).2.1 (hm v).2.2.1 (hm v).2.2.2
    by_cases hv : v ∈ L.S
    · rw [φS v hv, ψS v hv, cS v hv]
      exact L.mat v hv
    by_cases hvq : v = q
    · subst hvq
      rw [φq, ψq, cq']
      exact HQ w₀ _
    · rw [φo v hv hvq, ψo v hv hvq, co v hv hvq]
      exact LA p (fun w hw => (hp1 w hw).trans hD) v (L.unr v hv) h (f v) h1 h2 (f1 v)
