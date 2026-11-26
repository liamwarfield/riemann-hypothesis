module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CharIndep
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.AtInj
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ListProdStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.BumpEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.AmpSlot
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PairPosition
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.TyEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SideTrace

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HasFinTraceSmul
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

private theorem hasFinTrace_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c : ℂ} (b : ℂ) (hb : b ≠ 0)
    (h : HasFinTrace A c) : HasFinTrace (b • A) (b * c) := by
  obtain ⟨hf, rfl⟩ := h
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (b • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((b • A).restrict h1) = b * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    intro R hR h1 h2
    subst hR
    have e : (b • A).restrict h1 = b • A.restrict h2 := rfl
    rw [e, map_smul, smul_eq_mul]
  have hr : LinearMap.range (b • A) = LinearMap.range A := LinearMap.range_smul _ _ hb
  exact ⟨by rw [hr]; exact hf, key _ hr _ _⟩

private theorem hasTrace_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {s : ℂ} (d : ENNReal) (hd0 : d ≠ 0) (hdt : d ≠ ⊤)
    (h : HasTrace m ρ f s) : HasTrace (d • m) ρ f ((d.toReal : ℂ) * s) := by
  obtain ⟨A, hA, hF⟩ := h
  have hb : (d.toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hd0, hdt⟩)
  refine ⟨(d.toReal : ℂ) • A, fun v l => ⟨(hA v l).1.smul_measure hdt, ?_⟩, hasFinTrace_smul A _ hb hF⟩
  rw [integral_smul_measure, LinearMap.smul_apply, map_smul, (hA v l).2, Complex.real_smul, smul_eq_mul]

private theorem exists_ext {ι α : Type} {P : α → Type} (f : ι → α) (hf : Function.Injective f) (d : ∀ a, P a)
    (g : ∀ i, P (f i)) : ∃ G : ∀ a, P a, ∀ i, G (f i) = g i := by
  classical
  refine ⟨fun a => if h : ∃ i, f i = a then h.choose_spec ▸ g h.choose else d a, fun i => ?_⟩
  have aux : ∀ (j : ι) (e : f j = f i), (e ▸ g j : P (f i)) = g i := by
    intro j e
    obtain rfl := hf e
    rfl
  have h : ∃ j, f j = f i := ⟨i, rfl⟩
  simp only [dif_pos h]
  exact aux _ _

private theorem prod_mem_of {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    (l : List (H →L[ℂ] H)) (h : ∀ B ∈ l, ∀ v ∈ W, B v ∈ W) : ∀ v ∈ W, l.prod v ∈ W := by
  induction l with
  | nil => intro v hv; simpa using hv
  | cons B l ih =>
    intro v hv
    rw [List.prod_cons]
    exact h B (by simp) _ (ih (fun B' hB' => h B' (by simp [hB'])) v hv)

section Loc
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

private theorem rhoL_comm' {w w' : Pl K} (h : w ≠ w') (g : Gw n w) (g' : Gw n w') :
    Commute (rhoL μ w g) (rhoL μ w' g') := by
  have hm := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'
  change rhoF μ _ ∘L rhoF μ _ = rhoF μ _ ∘L rhoF μ _
  rw [← hm, ← hm]
  unfold rhoL at *
  rw [hc]

private theorem oloc_fix {w w' : Pl K} (h : w ≠ w') [MeasurableSpace (Gw n w)] (m : Measure (Gw n w)) (ψ : Gw n w → ℂ)
    (B : LL μ →L[ℂ] LL μ) (hB : IsOloc μ w m ψ B) (J : Subgroup (Gw n w')) {v : LL μ} (hv : v ∈ fixL μ w' J) :
    B v ∈ fixL μ w' J := by
  have hc : ∀ x : Gw n w', ∀ b, B (rhoL μ w' x b) = rhoL μ w' x (B b) := by
    intro x b
    refine ext_inner_left ℂ fun a => ?_
    rw [hB, ← ContinuousLinearMap.adjoint_inner_left, hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have h1 := congrArg (· b) (rhoL_comm' μ h g x)
    simp only [ContinuousLinearMap.mul_apply] at h1
    simp only
    rw [ContinuousLinearMap.adjoint_inner_left, h1]
  simp only [fixL, fixF, Submodule.mem_iInf] at hv ⊢
  rintro u ⟨k, hk, rfl⟩
  have hv' : rhoL μ w' k v = v := hv _ ⟨k, hk, rfl⟩
  show rhoL μ w' k (B v) = B v
  rw [← hc, hv']

private theorem isClosed_fixL (w : Pl K) (J : Subgroup (Gw n w)) : IsClosed (fixL μ w J : Set (LL μ)) := by
  simp only [fixL, fixF, Submodule.coe_iInf]
  exact isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_eq (rhoF μ u).continuous continuous_id

private theorem prj_of_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) {x : H} (hx : x ∈ W) : prj W x = x :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure W hx)

private theorem prj_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Y W : Submodule ℂ H} (hW : IsClosed (W : Set H)) (h : Y ≤ W) (x : H) : prj Y x ∈ W :=
  Submodule.topologicalClosure_minimal Y h hW (Submodule.starProjection_apply_mem _ x)

private theorem trOn_bot {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) :
    trOn (⊥ : Submodule ℂ H) T = 0 := by
  have : prj (⊥ : Submodule ℂ H) = 0 := by
    ext x
    simp [prj]
  simp [trOn, this, GroundTheory.Automorphic.trace]

end Loc

private theorem under_over' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

theorem UpperTheory.ConvolutionTheory.C.termE :
    UpperTheory.ConvolutionTheory.C.TermE := by
  classical
  intro F E _ _ _ _ _ _ σ hgen k n hk hn μ _ θ hθ D s hs hposition νE _ νF _ b a aE aF harch _ _ m hm q w₀ hq T V hV hVθ
    hrank τ₀ τ hocc₀ hocc y hy
  obtain ⟨hZc, hZs, hZa, hY⟩ := UpperTheory.ConvolutionTheory.L1.zBasic F E σ k n hn μ D s hs hposition νF a q w₀ hq T V hV y hy
  obtain ⟨c₁, hc₁, hside⟩ := UpperTheory.ConvolutionTheory.L1.sideTrace F E σ hgen k n hk hn μ θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq
    T V hV hVθ hrank y hy
  obtain ⟨r, p, hpinj, hpr⟩ : ∃ (r : ℕ) (p : Fin r → Pl F), Function.Injective p ∧ ∀ v, v ∈ T.sp ↔ v ∈ Set.range p := by
    refine ⟨T.sp.card, fun i => (T.sp.equivFin.symm i).1, ?_, fun v => ⟨fun hv => ⟨T.sp.equivFin ⟨v, hv⟩, by simp⟩, ?_⟩⟩
    · exact Subtype.val_injective.comp T.sp.equivFin.symm.injective
    · rintro ⟨i, rfl⟩
      exact (T.sp.equivFin.symm i).2
  have hpm : ∀ i, p i ∈ T.sp := fun i => (hpr _).2 ⟨i, rfl⟩
  have hprod : ∀ t : Pl F → ℂ, ∏ v ∈ T.sp, t v = ∏ i, t (p i) := by
    intro t
    have e : T.sp = Finset.univ.image p := by
      ext v
      simp [hpr]
    rw [e, Finset.prod_image (fun _ _ _ _ h => hpinj h)]
  obtain ⟨mm, hmm, hmm1, bb, hbb, htr⟩ : ∃ mm : ∀ u : Pl E, Measure (Gw n u), (∀ u, (mm u).IsHaarMeasure) ∧
      (∀ u, mm u (T.J u) = 1) ∧ ∃ bb : Pl E → ℂ, (∀ u, bb u ≠ 0) ∧
        ∀ (u : Pl E) (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Gw n u) X) (f : Gw n u → ℂ) (z : ℂ),
          HasTrace (m u) ρ f z → HasTrace (mm u) ρ f (bb u * z) := by
    have h0 : ∀ u, m u (T.J u) ≠ 0 := fun u => by
      haveI := hm u
      exact ((T.co u).2.measure_pos (m u) ⟨1, Subgroup.one_mem _⟩).ne'
    have ht : ∀ u, m u (T.J u) ≠ ⊤ := fun u => by
      haveI := hm u
      exact (T.co u).1.measure_lt_top.ne
    have hd0 : ∀ u, (m u (T.J u))⁻¹ ≠ 0 := fun u => ENNReal.inv_ne_zero.2 (ht u)
    have hdt : ∀ u, (m u (T.J u))⁻¹ ≠ ⊤ := fun u => ENNReal.inv_ne_top.2 (h0 u)
    refine ⟨fun u => (m u (T.J u))⁻¹ • m u, fun u => ?_, fun u => ?_, fun u => (((m u (T.J u))⁻¹.toReal : ℝ) : ℂ),
      fun u => ?_, fun u X _ _ ρ f z h => hasTrace_smul _ (hd0 u) (hdt u) h⟩
    · haveI := hm u
      exact Measure.IsHaarMeasure.smul _ (hd0 u) (hdt u)
    · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (h0 u) (ht u)]
    · exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hd0 u, hdt u⟩)
  have hJq : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n := T.at_q w₀
  have hne : ∀ i, (T.mk' (p i)).1 ≠ w₀.1 := by
    intro i h
    have h1 : p i = q := calc
      p i = (T.mk' (p i)).1.under (𝓞 F) := (under_over' _).symm
      _ = w₀.1.under (𝓞 F) := by rw [h]
      _ = q := under_over' _
    exact T.q_not (h1 ▸ (Finset.mem_filter.1 (hpm i)).1)
  have hover : ∀ i j, (T.mk' (p i)).1 = (T.mk' (p j)).1 → p i = p j := by
    intro i j h
    calc
      p i = (T.mk' (p i)).1.under (𝓞 F) := (under_over' _).symm
      _ = (T.mk' (p j)).1.under (𝓞 F) := by rw [h]
      _ = p j := under_over' _
  set O : Fin (k + 1) → LL μ →L[ℂ] LL μ := fun i => OComponent μ (s i) (hs i) νF a with hO
  have hYfix : T.Y μ V O y ≤ fixL μ w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n) := by
    rw [hY, ← hJq]
    exact inf_le_right.trans (iInf₂_le w₀.1 (Or.inl rfl))
  have step : ∀ (L : GM.Loc σ n q w₀) (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), T.Fits L ψ →
      ∀ (e : Fin n → ℤ) (l : ℕ) (𝔢 : Side θ l), Antitone e → GM.IsSideE L νE aE e 𝔢 → ∀ j : ℕ,
      ∃ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (B i)) ∧
        trOn (eigIn V 𝔢.toAmp.A (y ^ (k + 1))) ((𝔢.Uq 0 ^ j) ∘L Rop μ 𝔢.g ∘L θ.U) =
          c₁ * trOn (T.Y μ V O y) (Uiw μ w₀.1 (j • e) ∘L (List.ofFn B).prod) := by
    intro L ψ hfit e l 𝔢 he hsd j
    have hB : ∀ i, ∃ B, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) B := fun i => by
      haveI := hmm (T.mk' (p i)).1
      exact (UpperTheory.ConvolutionTheory.C.olocEx E n μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (hfit.test _ (hpm i)).1).exists
    choose B hB using hB
    refine ⟨B, hB, ?_⟩
    rw [hside L ψ hfit e l 𝔢 hsd r p hpinj hpr (fun i => mm (T.mk' (p i)).1) (fun i => ⟨hmm _, hmm1 _⟩) B hB j]
    congr 1
    have hP : ∀ x, (List.ofFn B).prod (prj (T.Y μ V O y) x) ∈
        fixL μ w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n) := fun x => by
      refine prod_mem_of _ _ ?_ _ (prj_mem (isClosed_fixL μ _ _) hYfix x)
      intro C hC v hv
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hC
      exact oloc_fix μ (hne i) _ _ _ (hB i) _ hv
    have hU := UpperTheory.ConvolutionTheory.C.uiwPow E n μ w₀.1 e he j
    simp only [trOn]
    congr 1
    ext1 x
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hU, ContinuousLinearMap.comp_apply, prj_of_mem _ (hP x)]
  by_cases hZ : T.Z μ V O y = ⊥
  · refine ⟨0, fun h => absurd hZ h, ?_⟩
    intro L ψ hfit e l 𝔢 he hsd j sq t _ _
    obtain ⟨B, -, h⟩ := step L ψ hfit e l 𝔢 he hsd j
    have hYb : T.Y μ V O y = ⊥ := by rw [hY, hZ, bot_inf_eq]
    rw [h, hYb, trOn_bot]
    simp
  let w : Fin (r + 1) → Pl E := Fin.cons w₀.1 fun i => (T.mk' (p i)).1
  have hw : Function.Injective w := by
    refine Fin.cons_injective_iff.2 ⟨?_, ?_⟩
    · rintro ⟨i, h⟩
      exact hne i h
    · intro i j h
      exact hpinj (hover i j h)
  have hmk : ∀ u, u ∈ T.marked ↔ ∃ i, w i = u := by
    intro u
    constructor
    · rintro (rfl | ⟨v, hv, rfl⟩)
      · exact ⟨0, rfl⟩
      · obtain ⟨i, rfl⟩ := (hpr v).1 hv
        exact ⟨i.succ, rfl⟩
    · rintro ⟨i, rfl⟩
      refine Fin.cases (Or.inl rfl) (fun i => Or.inr ⟨p i, hpm i, rfl⟩) i
  have hinf : ∀ G : ∀ u : Pl E, Subgroup (Gw n u),
      ⨅ u ∈ T.marked, fixL μ u (G u) = ⨅ i, fixL μ (w i) (G (w i)) := by
    intro G
    refine le_antisymm (le_iInf fun i => iInf₂_le (w i) ((hmk _).2 ⟨i, rfl⟩)) (le_iInf₂ fun u hu => ?_)
    obtain ⟨i, rfl⟩ := (hmk u).1 hu
    exact iInf_le _ i
  have hYZ : T.Y μ V O y = T.Z μ V O y ⊓ ⨅ i, fixL μ (w i) (T.J (w i)) := by rw [hY, hinf T.J]
  let σ' : ∀ i, SmIrr (Gw n (w i)) := Fin.cons (α := fun i => SmIrr (Gw n (w i))) τ₀ fun i => τ (p i)
  have hoccs : ∀ i, Occurs μ V (w i) (σ' i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hocc₀
    · exact hocc _ (hpm i)
  have hadm : ∀ U : ∀ i, Subgroup (Gw n (w i)), (∀ i, CO (U i)) →
      FiniteDimensional ℂ ↥(T.Z μ V O y ⊓ ⨅ i, fixL μ (w i) (U i)) := by
    intro U hU
    obtain ⟨G, hG⟩ := exists_ext (P := fun u : Pl E => Subgroup (Gw n u)) w hw (fun _ => ⊥) U
    have h := hZa G (fun u hu => by
      obtain ⟨i, rfl⟩ := (hmk u).1 hu
      rw [hG]
      exact hU i)
    have e : (⨅ i, fixL μ (w i) (G (w i))) = ⨅ i, fixL μ (w i) (U i) := iInf_congr fun i => by rw [hG i]
    rw [hinf G, e] at h
    exact h
  obtain ⟨N, hN, hfac⟩ := UpperTheory.ConvolutionTheory.C.summandFactor E n μ V (T.Z μ V O y) (r + 1) w σ' hV hw hoccs
    (fun v hv => hv.1.1) hZ hZc (fun i g v hv => hZs (w i) ((hmk _).2 ⟨i, rfl⟩) g v hv) hadm
  refine ⟨c₁ * N * ∏ i, bb (w i), fun _ => ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero hc₁ (Nat.cast_ne_zero.2 hN.ne')) (Finset.prod_ne_zero_iff.2 fun i _ => hbb _)
  intro L ψ hfit e l 𝔢 he hsd j sq t hsq ht
  obtain ⟨B, hB, h⟩ := step L ψ hfit e l 𝔢 he hsd j
  obtain ⟨hCO, -, hI⟩ := UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test E n w₀.1
  obtain ⟨htest, hinv⟩ := hI (j • e)
  let φ : ∀ i, Gw n (w i) → ℂ :=
    Fin.cons (α := fun i => Gw n (w i) → ℂ) ((GM.iwCoset w₀.1 (j • e)).indicator 1) fun i => ψ (p i)
  let T' : Fin (r + 1) → LL μ →L[ℂ] LL μ := Fin.cons (α := fun _ => LL μ →L[ℂ] LL μ) (Uiw μ w₀.1 (j • e)) B
  let s' : Fin (r + 1) → ℂ := Fin.cons (α := fun _ => ℂ) (bb w₀.1 * sq) fun i => bb (T.mk' (p i)).1 * t (p i)
  have h1 : ∀ i, Test (φ i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact htest
    · exact (hfit.test _ (hpm i)).1
  have h2 : ∀ i, ∀ u ∈ T.J (w i), ∀ g, φ i (u * g) = φ i g := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro u hu g
      exact hinv u (hJq ▸ hu) g
    · intro u hu g
      exact ((hfit.test _ (hpm i)).2 u hu g).1
  have h3 : ∀ i, IsOloc μ (w i) (mm (w i)) (φ i) (T' i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · haveI := hmm w₀.1
      exact UpperTheory.ConvolutionTheory.C.hopOloc E n μ w₀.1 (mm w₀.1) (GLnLocal.iwahori (w₀.1.adicCompletion E) n)
        (Cartan.diagPow (w₀.1.adicCompletion E) n (j • e)) hCO (by rw [← hJq]; exact hmm1 _)
    · exact hB i
  have h4 : ∀ i, HasTrace (mm (w i)) (σ' i).ρ (φ i) (s' i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact htr w₀.1 τ₀.V τ₀.ρ _ sq hsq
    · exact htr _ (τ (p i)).V (τ (p i)).ρ _ _ (ht _ (hpm i))
  have hf : trOn (T.Z μ V O y ⊓ ⨅ i, fixL μ (w i) (T.J (w i))) (List.ofFn T').prod = N * ∏ i, s' i :=
    hfac (fun i => T.J (w i)) (fun i => mm (w i)) φ T' s' (fun i => T.co _) (fun i => hmm _) h1 h2 h3 h4
  have hlist : (List.ofFn T').prod = Uiw μ w₀.1 (j • e) ∘L (List.ofFn B).prod := by
    rw [List.ofFn_succ, List.prod_cons]
    rfl
  rw [h, hYZ, ← hlist, hf, hprod t]
  have hw0 : w 0 = w₀.1 := rfl
  have hws : ∀ i : Fin r, w i.succ = (T.mk' (p i)).1 := fun _ => rfl
  have hs0 : s' 0 = bb w₀.1 * sq := rfl
  have hss : ∀ i : Fin r, s' i.succ = bb (T.mk' (p i)).1 * t (p i) := fun _ => rfl
  simp only [Fin.prod_univ_succ, hw0, hws, hs0, hss, Finset.prod_mul_distrib]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PickS
open NumberField IsDedekindDomain Filter

theorem UpperTheory.ConvolutionTheory.T.pickS :
    UpperTheory.ConvolutionTheory.T.PickS := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V Λ t hV hAt v
  obtain ⟨hInf, hUnr, hNe, -, -, -⟩ := UpperTheory.ConvolutionTheory.T.places F E hp
  obtain ⟨S₀, hS₀, hA⟩ := hAt
  obtain ⟨-, -, h0⟩ := UpperTheory.ConvolutionTheory.Dp.parEx E n hn μ V hV
  have hU := Filter.eventually_cofinite.1 hUnr
  have hfin := ((hS₀.image (fun w => w.under (𝓞 F))).union hU).union (Set.finite_singleton v)
  obtain ⟨q, hq, hqS⟩ := (hInf.diff hfin).nonempty
  have hsub : ∀ w, w.under (𝓞 F) ∉ hfin.toFinset → w ∉ S₀ := fun w hw hw0 =>
    hw (hfin.mem_toFinset.2 (Or.inl (Or.inl ⟨w, hw0, rfl⟩)))
  refine ⟨hfin.toFinset, q, (hNe q).some, hfin.mem_toFinset.2 (Or.inr rfl),
    fun h => hqS (hfin.mem_toFinset.1 h), hq, fun u hu => ?_, fun w hw => ?_, fun S' hS' => ?_⟩
  · by_contra h
    exact hu (hfin.mem_toFinset.2 (Or.inl (Or.inr h)))
  · exact (hA.2 w (hsub w hw)).2.1
  · have hS : ∀ w, w ∉ S' → w ∉ S₀ := fun w hw => hsub w fun h => hw ((hS' w).2 (Or.inl h))
    exact ⟨⟨hA.1, fun w hw => hA.2 w (hS w hw)⟩, fun τ => (hA.1 τ).1,
      fun w hw => ⟨(hA.2 w (hS w hw)).1, h0 w _ (hA.2 w (hS w hw))⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FdFixed
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical

private theorem fd_fixed {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    (m : Measure G) (ρ : Representation ℂ G V) (J : Subgroup G) (hJ : MeasurableSet (J : Set G))
    (h1 : m (J : Set G) = 1) (A : V →ₗ[ℂ] V) (hA : IsIntegralOp m ρ ((J : Set G).indicator 1) A)
    (hf : FiniteDimensional ℂ (LinearMap.range A)) : FiniteDimensional ℂ (fixedVectors ρ J) := by
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range A) fun x hx => ?_
  have hAx : A x = x := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, (hA x l).2, sub_eq_zero]
    have e : (fun g => ((J : Set G).indicator (1 : G → ℂ)) g * l (ρ g x)) =
        (J : Set G).indicator fun _ => l x := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · have hgx : ρ g x = x := hx g hg
        simp [Set.indicator_of_mem hg, hgx]
      · simp [Set.indicator_of_notMem hg]
    rw [e, integral_indicator hJ]
    simp [Measure.real, h1]
  exact ⟨x, hAx⟩

private theorem under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

theorem UpperTheory.ConvolutionTheory.T.termE :
    UpperTheory.ConvolutionTheory.T.TermE := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn m hm μ _ θ hθ D s hs hsl νE _ νF _ b a aE aF hAS q w₀ hq T V hV hVθ hR hne _ _ mm hmm
    τ hocc ν hν
  obtain ⟨y, hy, hY⟩ := (UpperTheory.ConvolutionTheory.L1.twistY F E σ hσ m n hm hn μ θ hθ D s hs hsl νE νF b a aE aF hAS q w₀ hq T V hV hVθ hR).1 hne
  have hJ : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n := T.at_q w₀
  have hcoI : CO (GLnLocal.iwahori (w₀.1.adicCompletion E) n) := hJ ▸ T.co w₀.1
  haveI := hmm w₀.1
  have h0 : mm w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) ≠ 0 :=
    hcoI.2.measure_ne_zero _ ⟨1, one_mem _⟩
  have hT : mm w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) ≠ ⊤ :=
    hcoI.1.measure_lt_top.ne
  obtain ⟨m₀, hm₀, hm₀1⟩ : ∃ m₀ : Measure (Gw n w₀.1), m₀.IsHaarMeasure ∧
      m₀ (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) = 1 := by
    refine ⟨(mm w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)))⁻¹ • mm w₀.1,
      Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hT) (ENNReal.inv_ne_top.2 h0), ?_⟩
    simp [ENNReal.inv_mul_cancel h0 hT]
  haveI := hm₀
  have hmm' : ∀ u, (Function.update mm w₀.1 m₀ u).IsHaarMeasure := by
    intro u
    by_cases h : u = w₀.1
    · subst h
      simpa using hm₀
    · simpa [Function.update_of_ne h] using hmm u
  obtain ⟨c, hc, hmain⟩ := UpperTheory.ConvolutionTheory.C.termE F E σ hσ m n hm hn μ θ hθ D s hs hsl νE νF b a aE aF hAS
    (Function.update mm w₀.1 m₀) hmm' q w₀ hq T V hV hVθ hR (τ w₀.1) (fun v => τ (T.mk' v).1) (hocc _) (fun v _ => hocc _) y hy
  have hYZ : T.Y μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≤ T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y := by
    unfold Ty.Y Ty.Z Ty.typed
    exact inf_le_inf_left _ (le_iInf₂ fun w _ => iInf_le _ w)
  have hZne : T.Z μ V (fun i => OComponent μ (s i) (hs i) νF a) y ≠ ⊥ := fun h => hY (le_bot_iff.1 (h ▸ hYZ))
  have hfix : V ⊓ fixL μ w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n) ≠ ⊥ := by
    intro h
    refine hY (le_bot_iff.1 (h ▸ le_inf ?_ ?_))
    · exact inf_le_left.trans inf_le_left
    · have heig := (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w₀.1 (T.J w₀.1) (T.χ w₀.1) (T.co _) (T.chr _)).2.1
      have hχ : T.χ w₀.1 = 1 := T.triv q hq w₀
      rw [← hJ, ← heig, ← hχ]
      exact inf_le_right.trans (iInf_le _ w₀.1)
  obtain ⟨hfx, -, -, s₀, -, A, hA, hfin, -⟩ :=
    UpperTheory.ConvolutionTheory.T.unitTrace E n μ V hV w₀.1 m₀ hm₀ (τ w₀.1) _ (hocc _) hcoI hfix
  have fd := fd_fixed m₀ (τ w₀.1).ρ _ hcoI.2.measurableSet hm₀1 A hA hfin
  obtain ⟨Z, hZ0, hcard, hZ⟩ := UpperTheory.ConvolutionTheory.C.iwPow E n w₀.1 m₀ hm₀1 (τ w₀.1) ν hν fd
  refine ⟨y ^ (m + 1), c, Z, pow_pos hy _, hc hZne, ?_, hZ0, ?_⟩
  · rintro rfl
    exact hfx (Submodule.finrank_eq_zero.1 (by simpa using hcard.symm))
  · intro L ψ hF l 𝔢 hS sv hsv j
    refine hmain L ψ hF ν l 𝔢 hν hS j _ sv ?_ ?_
    · rw [Function.update_self]
      exact hZ j
    · intro v hv
      have hne' : (T.mk' v).1 ≠ w₀.1 := by
        intro h
        have hvq : v = q := by rw [← under_eq (T.mk' v), h, under_eq w₀]
        exact T.q_not (hvq ▸ (Finset.mem_filter.1 hv).1)
      rw [Function.update_of_ne hne']
      exact hsv v hv
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.AbsLast
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped Classical

namespace UpperTheory.ConvolutionTheory.T.AbsoluteValueFixed

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {v : Pl K}

private theorem fixed_fd (U : Subgroup (Gw n v)) (hU : CO U) (σ : SmIrr (Gw n v)) :
    FiniteDimensional ℂ (fixedVectors σ.ρ U) := by
  have h := PositivityTheory.Exh.irreducibleAdmissibleGL (v.adicCompletion K) n σ.V σ.ρ σ.smooth σ.irred
  have h2 := h.2 U hU.2 hU.1
  have e : GlobalTheory.PRep.fixed σ.ρ U = fixedVectors σ.ρ U := by
    ext x
    constructor
    · intro hx g hg
      simpa using hx ⟨g, hg⟩
    · intro hx g
      simpa using hx g g.2
  rw [← e]
  exact h2

private theorem td : TotallyDisconnectedSpace (Gw n v) := by
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) (v.adicCompletion K)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → v.adicCompletion K))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

end UpperTheory.ConvolutionTheory.T.AbsoluteValueFixed

open UpperTheory.ConvolutionTheory.T.AbsoluteValueFixed in
theorem UpperTheory.ConvolutionTheory.T.absLast :
    UpperTheory.ConvolutionTheory.T.AbsLast := by
  intro K _ _ n v _ _ m _ U hU ι _ τ a Z τ₀ c Z₀ hc hZ₀ h0 hZ hfix hid
  by_contra hno
  obtain ⟨ζ, hζ⟩ := Multiset.exists_mem_of_ne_zero hZ₀
  have hk : ((Multiset.filter (· = ζ) Z₀).card : ℂ) ≠ 0 := by
    have : 0 < (Multiset.filter (· = ζ) Z₀).card :=
      Multiset.card_pos_iff_exists_mem.2 ⟨ζ, Multiset.mem_filter.2 ⟨hζ, rfl⟩⟩
    exact_mod_cast this.ne'
  let σ : Option ι → SmIrr (Gw n v) := fun o => o.elim τ₀ τ
  let C : Option ι → ℂ := fun o => o.elim (c * ((Multiset.filter (· = ζ) Z₀).card : ℂ))
    (fun i => -(a i * ((Multiset.filter (· = ζ) (Z i)).card : ℂ)))
  haveI : m.IsMulRightInvariant := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL (v.adicCompletion K) n m
  haveI : LocallyCompactSpace (Gw n v) :=
    hU.1.locallyCompactSpace_of_mem_nhds_of_group (hU.2.mem_nhds U.one_mem)
  haveI : T2Space (Gw n v) := Units.isEmbedding_embedProduct.t2Space
  haveI : TotallyDisconnectedSpace (Gw n v) := td
  have key := UpperTheory.ConvolutionTheory.C.charIndep (Gw n v) m U hU (Option ι) σ C (fun o => fixed_fd U hU (σ o)) ?_ none hfix
  · have hset : {o : Option ι | Nonempty ((σ o).ρ.Equiv (σ none).ρ)} = {none} := by
      ext o
      cases o with
      | none => exact ⟨fun _ => rfl, fun _ => ⟨Representation.Equiv.refl (σ none).ρ⟩⟩
      | some i =>
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, reduceCtorEq, iff_false]
        exact fun h => hno ⟨i, h⟩
    rw [hset, finsum_mem_singleton] at key
    exact (mul_ne_zero hc hk) key
  · intro φ s hφ hinv hs
    have e := hid φ (s none) (fun i => s (some i)) hφ hinv (hs none) (fun i => hs (some i))
    have p := UpperTheory.ConvolutionTheory.C.powIndep (Option ι)
      (fun o => o.elim (c * s none) (fun i => -(a i * s (some i))))
      (fun o => o.elim Z₀ Z)
      (fun o => by cases o with
        | none => exact h0
        | some i => exact hZ i)
      (by
        filter_upwards [e] with j hj
        rw [Fintype.sum_option]
        simp only [Option.elim]
        have : ∑ i, -(a i * s (some i)) * ((Z i).map (· ^ j)).sum
            = -∑ i, a i * ((Z i).map (· ^ j)).sum * s (some i) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [this, ← hj]
        ring) ζ
    rw [Fintype.sum_option] at p ⊢
    simp only [Option.elim] at p
    have : ∑ i, C (some i) * s (some i)
        = ∑ i, -(a i * s (some i)) * ((Multiset.filter (· = ζ) (Z i)).card : ℂ) :=
      Finset.sum_congr rfl (fun i _ => by simp only [C, Option.elim]; ring)
    rw [this]
    have h1 : C none = c * ((Multiset.filter (· = ζ) Z₀).card : ℂ) := rfl
    rw [h1]
    linear_combination p
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PullBack
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep GlobalTheory.CuspRep

namespace UpperTheory.ConvolutionTheory.T

section Rep
variable {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

private def pull (e : G ≃ₜ* H) (τ : SmIrr H) : SmIrr G where
  V := τ.V
  ρ := τ.ρ.comp (e : G →* H)
  smooth := fun x => (τ.smooth x).preimage e.continuous
  irred := by
    refine (OrderIso.isSimpleOrder_iff (β := Subrepresentation τ.ρ)
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => ?_⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (e g) hv⟩
        left_inv := fun S => rfl
        right_inv := fun S => rfl
        map_rel_iff' := Iff.rfl }).2 τ.irred
    have := S.apply_mem_toSubmodule (e.symm g) hv
    simpa using this

end Rep

section Trace
variable {G H V : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H] [AddCommGroup V] [Module ℂ V]

private theorem hasFinTrace_smul {A : V →ₗ[ℂ] V} {c s : ℂ} (hc : c ≠ 0) (h : HasFinTrace A s) :
    HasFinTrace (c • A) (c * s) := by
  obtain ⟨hf, rfl⟩ := h
  have hR : LinearMap.range (c • A) = LinearMap.range A := LinearMap.range_smul A c hc
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (c • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((c • A).restrict h1) =
        c * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    rintro _ rfl h1 h2
    have : (c • A).restrict h1 = c • A.restrict h2 := by
      ext x
      simp
    rw [this, map_smul, smul_eq_mul]
  exact ⟨hR ▸ hf, key _ hR _ _⟩

private theorem hasTrace_map (e : G ≃ₜ* H) (mF : Measure G) (mE : Measure H) (c : NNReal) (hc : c ≠ 0)
    (h : mE = c • mF.map e) (π : Representation ℂ H V) (ψ : H → ℂ) (s : ℂ)
    (hs : HasTrace mF (π.comp (e : G →* H)) (fun g => ψ (e g)) s) : HasTrace mE π ψ ((c : ℂ) * s) := by
  obtain ⟨A, hA, hf⟩ := hs
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  refine ⟨(c : ℂ) • A, fun x l => ?_, hasFinTrace_smul hc' hf⟩
  obtain ⟨hi, hl⟩ := hA x l
  have hi' : Integrable (fun y => ψ y * l (π y x)) (mF.map e) := hme.integrable_map_iff.2 hi
  subst h
  refine ⟨hi'.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure, hme.integral_map, LinearMap.smul_apply, map_smul, hl]
  simp [NNReal.smul_def]

end Trace

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.pullBack :
    UpperTheory.ConvolutionTheory.T.PullBack := by
  intro F E _ _ _ _ _ n v w hs _ _ _ _ mF mE hF hE τ'
  obtain ⟨⟨e, he⟩, -⟩ := UpperTheory.ConvolutionTheory.L1.splitLoc F E v w hs n
  have hmap : (mF.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map mF e
  have hscal := Measure.isMulLeftInvariant_eq_smul mE (mF.map e)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure mE (mF.map e)
  have hc0 : mE.haarScalarFactor (mF.map e) ≠ 0 := hpos.ne'
  refine ⟨pull e τ', ((mE.haarScalarFactor (mF.map e) : NNReal) : ℂ), by exact_mod_cast hc0, ?_, ?_, ?_⟩
  · rintro τ₁ ⟨E₁⟩
    refine ⟨E₁.toLinearEquiv, fun g x => ?_⟩
    rw [← he g]
    exact LinearMap.congr_fun (E₁.toIntertwiningMap.isIntertwining' g) x
  · intro ψ s h
    refine hasTrace_map e mF mE _ hc0 hscal τ'.ρ ψ s ?_
    have hfun : (fun g => ψ (e g)) = fun g => ψ (mapGL n (completionMap v w.1) g) :=
      funext fun g => by rw [he g]
    rw [hfun]
    exact h
  · intro J U hJ hU
    have hU' : ∀ g, g ∈ U ↔ e g ∈ J := fun g => by rw [he g]; exact hU g
    have hset : (U : Set (Gw n v)) = e ⁻¹' (J : Set (Gw n w.1)) := Set.ext hU'
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hset]
      exact e.toHomeomorph.isCompact_preimage.2 hJ.1
    · rw [hset]
      exact hJ.2.preimage e.continuous
    · intro h h0
      refine h (eq_bot_iff.2 fun x hx => ?_)
      have hx' : x ∈ fixedVectors (pull e τ').ρ U := fun u hu => hx _ ((hU' u).1 hu)
      rw [h0] at hx'
      exact hx'
    · intro φ hφ hinv
      refine ⟨fun y => φ (e.symm y), ⟨hφ.1.comp_continuous e.symm.continuous,
        hφ.2.comp_homeomorph e.symm.toHomeomorph⟩, fun u hu g => ?_, ?_⟩
      · have hu' : e.symm u ∈ U := (hU' _).2 (by simpa using hu)
        simpa [map_mul] using hinv _ hu' (e.symm g)
      · funext g
        rw [← he g]
        simp
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SideSum
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical

private theorem trace_range_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c s : ℂ} (hc : c ≠ 0)
    (h : HasFinTrace A s) : HasFinTrace (c • A) (c * s) := by
  obtain ⟨hfd, rfl⟩ := h
  have hr : LinearMap.range (c • A) = LinearMap.range A := LinearMap.range_smul _ _ hc
  have key : ∀ W : Submodule ℂ V, W = LinearMap.range A → ∀ h' : ∀ v ∈ W, (c • A) v ∈ W,
      LinearMap.trace ℂ W ((c • A).restrict h') = c * LinearMap.trace ℂ (LinearMap.range A)
        (A.restrict (p := LinearMap.range A) (q := LinearMap.range A) fun v _ => LinearMap.mem_range_self A v) := by
    rintro W rfl h'
    have : (c • A).restrict h' = c • A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
        (fun v _ => LinearMap.mem_range_self A v) := by
      ext v
      rfl
    rw [this, map_smul, smul_eq_mul]
  exact ⟨hr ▸ hfd, key _ hr _⟩

private theorem hasTrace_of_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {s : ℂ} {d : ENNReal} (h0 : d ≠ 0) (ht : d ≠ ⊤)
    (h : HasTrace (d • m) ρ f s) : HasTrace m ρ f (((d.toReal : ℂ))⁻¹ * s) := by
  obtain ⟨A, hA, hT⟩ := h
  have hr : (d.toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
  refine ⟨((d.toReal : ℂ))⁻¹ • A, fun v l => ?_, trace_range_smul A (inv_ne_zero hr) hT⟩
  obtain ⟨h1, h2⟩ := hA v l
  refine ⟨(integrable_smul_measure h0 ht).1 h1, ?_⟩
  rw [LinearMap.smul_apply, map_smul, h2, integral_smul_measure, smul_eq_mul, Complex.real_smul, inv_mul_cancel_left₀ hr]

private theorem fd_of_trace {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {I : Subgroup G} {s : ℂ} (hIm : MeasurableSet (I : Set G))
    (h0 : m I ≠ 0) (ht : m I ≠ ⊤) (h : HasTrace m ρ ((I : Set G).indicator 1) s) :
    FiniteDimensional ℂ (fixedVectors ρ I) := by
  obtain ⟨A, hA, hfd, -⟩ := h
  have hr : ((m (I : Set G)).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
  have hfix : ∀ v ∈ fixedVectors ρ I, A v = ((m (I : Set G)).toReal : ℂ) • v := by
    intro v hv
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2, map_smul, smul_eq_mul]
    have e : (fun g => (I : Set G).indicator (1 : G → ℂ) g * l (ρ g v)) = (I : Set G).indicator fun _ => l v := by
      funext g
      by_cases hg : g ∈ (I : Set G)
      · have : ρ g v = v := hv g hg
        simp [hg, this]
      · simp [hg]
    rw [e, integral_indicator hIm, setIntegral_const, measureReal_def, Complex.real_smul]
  have hle : fixedVectors ρ I ≤ LinearMap.range A := by
    intro v hv
    refine ⟨((m (I : Set G)).toReal : ℂ)⁻¹ • v, ?_⟩
    rw [map_smul, hfix v hv, smul_smul, inv_mul_cancel₀ hr, one_smul]
  exact Submodule.finiteDimensional_of_le hle

private theorem test_ind {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) :
    Test (((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)).indicator (1 : Gw n w → ℂ)) := by
  obtain ⟨hc, ho⟩ := (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test K n w).1
  have hcl : IsClosed ((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)) :=
    Subgroup.isClosed_of_isOpen _ ho
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ ((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w))
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    rfl
  · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

private theorem iw_pow_at {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) [MeasurableSpace (Gw n w)]
    [BorelSpace (Gw n w)] (m : Measure (Gw n w)) [m.IsHaarMeasure] (σ : SmIrr (Gw n w)) (ν : Fin n → ℤ) (hν : Antitone ν)
    {s₀ : ℂ} (h₀ : HasTrace m σ.ρ (((GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) : Set (Gw n w)).indicator 1) s₀) :
    ∃ (c : ℂ) (Z : Multiset ℂ), 0 ∉ Z ∧ ∀ j : ℕ, HasTrace m σ.ρ ((GM.iwCoset w (j • ν)).indicator 1) (c * (Z.map (· ^ j)).sum) := by
  obtain ⟨hc, ho⟩ := (UpperTheory.iwahori_compactOpen_and_iwCoset_indicator_test K n w).1
  have hpos : m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) ≠ 0 :=
    (ho.measure_pos m ⟨1, one_mem _⟩).ne'
  have htop : m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) ≠ ⊤ := hc.measure_lt_top.ne
  have hfd := fd_of_trace ho.measurableSet hpos htop h₀
  set d : ENNReal := (m (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)))⁻¹ with hd
  have hd0 : d ≠ 0 := ENNReal.inv_ne_zero.2 htop
  have hdt : d ≠ ⊤ := ENNReal.inv_ne_top.2 hpos
  haveI : (d • m).IsHaarMeasure := Measure.IsHaarMeasure.smul m hd0 hdt
  have h1 : (d • m) (GLnLocal.iwahori (w.adicCompletion K) n : Subgroup (Gw n w)) = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, hd, ENNReal.inv_mul_cancel hpos htop]
  obtain ⟨Z, hZ0, -, hZ⟩ := UpperTheory.ConvolutionTheory.C.iwPow K n w (d • m) h1 σ ν hν hfd
  exact ⟨_, Z, hZ0, fun j => hasTrace_of_smul hd0 hdt (hZ j)⟩

private theorem amp_A_eq {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a : TI K n)
    (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) (h1 : 𝔞.ν = ν) (h2 : 𝔞.a₀ = a) (h3 : 𝔞.U = U) :
    𝔞.A = Oinf μ ν a ∘L prj (fixF μ U) := by
  subst h2 h3
  have : ∀ (ν' : Measure (archGroup K n)) (_ : ν'.IsHaarMeasure) (_ : ν' = ν) , Oinf μ ν' 𝔞.a₀ = Oinf μ ν 𝔞.a₀ := by
    intro ν' _ h; subst h; rfl
  exact congrArg (· ∘L prj (fixF μ 𝔞.U)) (this 𝔞.ν 𝔞.haar h1)

private theorem trOn_bot' {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (B : H →L[ℂ] H) :
    trOn (⊥ : Submodule ℂ H) B = 0 := by
  have := UpperTheory.trOn_eq_mul_of_eq_smul_on_subspace H ⊥ B B 0 inferInstance (fun v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv]; simp)
  simpa using this

theorem UpperTheory.ConvolutionTheory.T.sideSum :
    UpperTheory.ConvolutionTheory.T.SideSum := by
  intro F E _ _ _ _ _ _ σ n l hn μ _ ν _ _ _ m hm a q w₀ S UF e he p x hx
  haveI hmH : ∀ v, (m v).IsHaarMeasure := fun v => (hm v).1
  by_cases hex : ∃ (L : GM.Loc σ n q w₀) (𝔣 : Side (Twist.id μ) l), L.S = S ∧ (∀ v ∈ S, L.UF v = UF v) ∧ GM.IsSideF L ν a e 𝔣
  swap
  · refine ⟨Empty, inferInstance, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, ?_⟩
    intro L 𝔣 h1 h2 h3
    exact absurd ⟨L, 𝔣, h1, h2, h3⟩ hex
  obtain ⟨L₀, 𝔣₀, hS₀, hU₀, hF₀⟩ := hex
  obtain ⟨κ, -, hT⟩ := UpperTheory.ConvolutionTheory.C.termF F E σ n l hn μ ν m hm
  have hfin := (UpperTheory.ConvolutionTheory.T.ampFin F n hn μ 𝔣₀.toAmp).1 x hx
  set P : Set (Submodule ℂ (LL μ)) := {V | IsSummand μ V ∧ eigIn V 𝔣₀.toAmp.A x ≠ ⊥ ∧ p V} with hP
  have hPfin : P.Finite := hfin.subset fun V h => ⟨h.1, h.2.1⟩
  have hτ : ∀ V : P, ∃ τ : ∀ v : Pl F, SmIrr (Gw n v), ∀ v, Occurs μ V.1 v (τ v) := fun V => by
    have := fun v => (UpperTheory.ConvolutionTheory.C.occursBasics F n μ V.1 v (m v) V.2.1).1
    choose τ hτ using this
    exact ⟨τ, hτ⟩
  choose τ hτ using hτ
  have hZ : ∀ V : P, ∃ (c : ℂ) (Z : Multiset ℂ), 0 ∉ Z ∧ ∀ j : ℕ,
      HasTrace (m q) (τ V q).ρ ((GM.iwCoset q (j • e)).indicator 1) (c * (Z.map (· ^ j)).sum) := fun V => by
    obtain ⟨s₀, hs₀⟩ := (UpperTheory.ConvolutionTheory.C.occursBasics F n μ V.1 q (m q) V.2.1).2.2 (τ V q) (hτ V q) _ (test_ind q)
    exact iw_pow_at q (m q) (τ V q) e he hs₀
  choose c Z hZ0 hZ using hZ
  have hN := fun V : P => hT a q w₀ S V.1 (τ V) x V.2.1 hx (fun v _ => hτ V v)
  choose N hN using hN
  letI : Fintype P := hPfin.fintype
  refine ⟨P, inferInstance, fun V => V.1, τ, fun V => κ * x * N V * c V, Z, fun V => ⟨V.2.1, V.2.2.2, hZ0 V, hτ V⟩, ?_⟩
  intro L 𝔣 hS hU hF s hs j
  have hUF : L.UF = L₀.UF := by
    funext v
    by_cases hv : v ∈ S
    · rw [hU v hv, hU₀ v hv]
    by_cases hq : v = q
    · subst hq
      rw [L.at_q.2.2.2, L₀.at_q.2.2.2]
    · rw [(L.off v (hS ▸ hv) hq).2.2.2, (L₀.off v (hS₀ ▸ hv) hq).2.2.2]
  have hA : 𝔣.toAmp.A = 𝔣₀.toAmp.A := by
    obtain ⟨h1, h2, -, h3, -, -⟩ := hF
    obtain ⟨h1', h2', -, h3', -, -⟩ := hF₀
    rw [amp_A_eq 𝔣.toAmp ν a _ h1 h2 h3, amp_A_eq 𝔣₀.toAmp ν a _ h1' h2' h3', hUF]
  have hid : ∀ V : Submodule ℂ (LL μ), V.map ((Twist.id μ).U : LL μ →ₗ[ℂ] LL μ) = V := fun V => by
    have : ((Twist.id μ).U : LL μ →ₗ[ℂ] LL μ) = LinearMap.id := LinearMap.ext fun _ => rfl
    rw [this, Submodule.map_id]
  have hsum : 𝔣.tr p x j = ∑ᶠ V ∈ P, trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) := by
    unfold Side.tr
    refine finsum_mem_inter_support_eq _ _ _ ?_
    ext V
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, hP]
    constructor
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      refine ⟨⟨h1, fun h => h4 ?_, h3⟩, h4⟩
      rw [hA, h, trOn_bot']
    · rintro ⟨⟨h1, -, h3⟩, h4⟩
      exact ⟨⟨h1, hid V, h3⟩, h4⟩
  rw [hsum, ← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun V _ => ?_
  rw [(hN V).2 L e 𝔣 hS he hF j _ (s V) (hZ V j) (hs V)]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PickInf
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1
open scoped ComplexConjugate

theorem UpperTheory.ConvolutionTheory.T.Port.adj_ne {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (u : H) (hu : star T u ≠ 0) : (T * star T) u ≠ 0 := by
  intro h0
  apply hu
  rw [ContinuousLinearMap.star_eq_adjoint] at h0 ⊢
  have h1 : T (ContinuousLinearMap.adjoint T u) = 0 := h0
  rw [← inner_self_eq_zero (𝕜 := ℂ), ContinuousLinearMap.adjoint_inner_left, h1, inner_zero_right]

theorem UpperTheory.ConvolutionTheory.T.Port.pickInf_of (hInf : UpperTheory.ConvolutionTheory.L1.InfSplit) (hAB : UpperTheory.ConvolutionTheory.L1.ArchBasic)
    (hBump : UpperTheory.ConvolutionTheory.L1.BumpEx) (hPosition : UpperTheory.ConvolutionTheory.L1.ArchSlotEx) (hSq : UpperTheory.ConvolutionTheory.L1.SqOp)
    (hAmp : UpperTheory.ConvolutionTheory.L1.AmpSlot) (hPair : UpperTheory.ConvolutionTheory.L1.PairPosition) : UpperTheory.ConvolutionTheory.T.PickInf := by
  set_option synthInstance.maxHeartbeats 100000 in
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ u hu
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 :=
    ⟨Module.finrank F E - 1, by have := hp.two_le; omega⟩
  obtain ⟨p⟩ := (hInf F E σ hσ m hm).1 inferInstance
  obtain ⟨D, -⟩ := (hInf F E σ hσ m hm).2 p
  obtain ⟨-, -, -, -, -, ⟨s, hsl, hs⟩, -, -⟩ := hAB F E σ m D n
  obtain ⟨νF, hνF⟩ : ∃ νF : Measure (archGroup F n), νF.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨b, hbs, hbf, hbn, hbu⟩ := hBump F n νF (LL μE)
    (((rightRegularRep (rationalGLOne (K := E) (n := n)) μE).compHom (archP E n) continuous_archP).compHom (s 0) (hs 0)) u hu
  obtain ⟨νE, hνE, a, aE, aF, hA⟩ := hPosition F E σ m D n νF b hbs hbf hbn
  obtain ⟨hsq, -, -, -⟩ := hSq F n νF b a aF m hA.sq hA.pow hA.norm (LL μE)
    (((rightRegularRep (rationalGLOne (K := E) (n := n)) μE).compHom (archP E n) continuous_archP).compHom (s 0) (hs 0))
  obtain ⟨hAE, hAF⟩ := hAmp F E σ m D n νE νF b a aE aF hA
  refine ⟨m, hm, D, s, hs, νE, hνE, νF, hνF, b, a, aE, aF, hsl, hA, hAE μE, hAF μF,
    hPair F E σ m hm D n νE νF b a aE aF hA, ?_⟩
  have key := UpperTheory.ConvolutionTheory.T.Port.adj_ne _ u hbu
  rw [← hsq] at key
  exact key

theorem UpperTheory.ConvolutionTheory.T.pickInf :
    UpperTheory.ConvolutionTheory.T.PickInf := UpperTheory.ConvolutionTheory.T.Port.pickInf_of infSplit archBasic bumpEx archPositionEx sqOp ampPosition pairPosition
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.OneTerm
theorem UpperTheory.ConvolutionTheory.T.oneTerm :
    UpperTheory.ConvolutionTheory.T.OneTerm := by
  intro K _ _ _ n l _ μ _ θ 𝔰 V Λ t hV hθ hAt x j
  have hset : {V' : Submodule ℂ (UpperTheory.ConvolutionTheory.C.LL μ) | UpperTheory.ConvolutionTheory.C.IsSummand μ V' ∧
      V'.map (θ.U : UpperTheory.ConvolutionTheory.C.LL μ →ₗ[ℂ] UpperTheory.ConvolutionTheory.C.LL μ) = V' ∧
      UpperTheory.ConvolutionTheory.At μ 𝔰.S V' Λ t} = {V} := by
    ext V'
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact UpperTheory.ConvolutionTheory.Dp.atInj K n μ V' V h1 hV 𝔰.S 𝔰.finS t h3.2 hAt.2
    · rintro rfl
      exact ⟨hV, hθ, hAt⟩
  unfold UpperTheory.ConvolutionTheory.Side.tr
  rw [hset, finsum_mem_singleton]
end

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T in
theorem UpperTheory.ConvolutionTheory.T.coreDesc :
    UpperTheory.ConvolutionTheory.CI → UpperTheory.ConvolutionTheory.GM.GM → UpperTheory.ConvolutionTheory.T.CoreDesc :=
  coreDesc_of absLast pullBack unitTrace oneTerm sideSum pickS pickInf tyEx termE goodEx places C.occursBasics L1.eigBasic
