module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PositionOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

def WordTens : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E]
    (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ) (νE : Measure (archGroup E n)) [νE.IsHaarMeasure]
    (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n) (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    ∀ w : List (Option (Ix E n)), ∃ φ : Fin (m + 1) → TI F n, IsTens D φ (GM.word νE aE w) ∧
      ∀ g, GM.word νF aF (w.map (GM.resIx F)) g = cvAll νF m (fun i => φ i) g

def AmpSlot : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E]
    (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ) (νE : Measure (archGroup E n)) [νE.IsHaarMeasure]
    (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n) (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    (∀ (μE : Measure (normOneGL (K := E) (n := n))) [μE.IsHaarMeasure], GM.AmpFn μE νE aE) ∧
      ∀ (μF : Measure (normOneGL (K := F) (n := n))) [μF.IsHaarMeasure], GM.AmpFn μF νF aF

def PairPosition : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E]
    (σ : E ≃ₐ[F] E) (m : ℕ), Module.finrank F E = m + 1 → ∀ (D : InfD σ m) (n : ℕ) (νE : Measure (archGroup E n)) [νE.IsHaarMeasure]
    (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n) (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    GM.ArchPair σ νE νF aE aF 1

def SplitLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (w : PlacesOver E v),
    Function.Surjective (completionMap v w.1) → ∀ n : ℕ,
    (∃ e : GL (Fin n) (v.adicCompletion F) ≃ₜ* GL (Fin n) (w.1.adicCompletion E), ∀ g, e g = mapGL n (completionMap v w.1) g) ∧
    (∀ g, mapGL n (completionMap v w.1) g ∈ GLnLocal.integralGL (w.1.adicCompletion E) n ↔
      g ∈ GLnLocal.integralGL (v.adicCompletion F) n) ∧
    (∀ g, mapGL n (completionMap v w.1) g ∈ GLnLocal.iwahori (w.1.adicCompletion E) n ↔
      g ∈ GLnLocal.iwahori (v.adicCompletion F) n) ∧
    (∀ ν g, mapGL n (completionMap v w.1) g ∈ GM.iwCoset w.1 ν ↔ g ∈ GM.iwCoset v ν) ∧
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal

def MatchProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ m : ℕ, Module.finrank F E = m + 1 → ∀ (n : ℕ) (v : Pl F) (w₀ : PlacesOver E v),
    GM.Split E v → ∃ w : Fin (m + 1) ≃ PlacesOver E v, w 0 = w₀ ∧
      ∀ h : ∀ u : PlacesOver E v, GL (Fin n) (u.1.adicCompletion E) → ℂ, (∀ u, Continuous (h u) ∧ HasCompactSupport (h u)) →
      ∀ [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
        (mF : Measure (GL (Fin n) (v.adicCompletion F))), mF.IsHaarMeasure →
        mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1 →
        GM.MatchAt σ v 1 (GM.prodFn h) (cvAll mF m fun i g => h (w i) (mapGL n (completionMap v (w i).1) g))

def UnitSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) (v : Pl F), GM.Split E v →
    GM.MatchAt σ v 1 ((unitSet E n v).indicator 1) ((GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1)

def SphLaws : Prop :=
  (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (w : PlacesOver E v),
    Function.Surjective (completionMap v w.1) → ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℂ) (h : GL (Fin n) (w.1.adicCompletion E) → ℂ),
    GM.IsSph w.1 p h → GM.IsSph v p fun g => h (mapGL n (completionMap v w.1) g)) ∧
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (v : Pl K),
    (∀ p h, GM.IsSph (n := n) v p h → Continuous h ∧ HasCompactSupport h) ∧
    (∀ p h h', GM.IsSph (n := n) v p h → GM.IsSph v p h' → h = h') ∧
    ∀ [MeasurableSpace (GL (Fin n) (v.adicCompletion K))] [BorelSpace (GL (Fin n) (v.adicCompletion K))]
      (m : Measure (GL (Fin n) (v.adicCompletion K))), m.IsHaarMeasure → m (GLnLocal.integralGL (v.adicCompletion K) n) = 1 →
      ∀ p p' h h', GM.IsSph (n := n) v p h → GM.IsSph v p' h' → GM.IsSph v (p * p') (cv m h h')

end UpperTheory.ConvolutionTheory.L1
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensOp
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.L1

section General

variable {G Γ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [MeasurableSpace Γ] [BorelSpace Γ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem ofFn_prod_single {M : Type} [Monoid M] :
    ∀ (k : ℕ) (a : Fin k → M) (j : Fin k), (∀ i, i ≠ j → a i = 1) → (List.ofFn a).prod = a j := by
  intro k
  induction k with
  | zero => intro a j; exact j.elim0
  | succ k ih =>
    intro a j h
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun j' => ?_) j (motive := fun j => (∀ i, i ≠ j → a i = 1) → a 0 * (List.ofFn fun i => a i.succ).prod = a j) h
    · intro h
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact h _ (Fin.succ_ne_zero i)
    · intro h
      rw [h 0 (Fin.succ_ne_zero j').symm, one_mul]
      exact ih (fun i => a i.succ) j' fun i hi => h _ (fun e => hi (Fin.succ_injective _ e))

private theorem ofFn_mulSingle {k : ℕ} (g : Fin k → G) :
    (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin k → G)).prod = g := by
  funext j
  have e := map_list_prod (Pi.evalMonoidHom (fun _ : Fin k => G) j)
    (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin k → G))
  simp only [Pi.evalMonoidHom_apply] at e
  rw [e, List.map_ofFn]
  refine (ofFn_prod_single k _ j fun i hi => ?_).trans ?_
  · simp [Pi.mulSingle_eq_of_ne hi.symm]
  · simp

private theorem continuous_ofFn_prod : ∀ (k : ℕ) (s : Fin k → G →* Γ), (∀ i, Continuous (s i)) →
    Continuous fun g : Fin k → G => (List.ofFn fun i => s i (g i)).prod := by
  intro k
  induction k with
  | zero => intro s _; simpa using continuous_const
  | succ k ih =>
    intro s hs
    simp only [List.ofFn_succ, List.prod_cons]
    exact ((hs 0).comp (continuous_apply 0)).mul
      ((ih (fun i => s i.succ) fun i => hs _).comp
        (continuous_pi fun i => continuous_apply i.succ))

private theorem inner_cc (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (π : UnitaryRep G H)
    (f : CompactlySupportedContinuousMap G ℂ) (w v : H) :
    ⟪w, π.integrated μ (UnitaryRep.ccToL1 μ f) v⟫_ℂ = ∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ := by
  have hint : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  rw [UnitaryRep.integrated_ccToL1_apply, ← integral_inner hint]
  simp only [inner_smul_right]

private theorem inner_ofFn_prod (μ : Measure G) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (π : UnitaryRep Γ H) : ∀ (k : ℕ) (s : Fin k → G →* Γ) (hs : ∀ i, Continuous (s i))
    (φ : Fin k → CompactlySupportedContinuousMap G ℂ) (w v : H),
    ⟪w, (List.ofFn fun i => (π.compHom (s i) (hs i)).integrated μ (UnitaryRep.ccToL1 μ (φ i))).prod v⟫_ℂ =
      ∫ g : Fin k → G, (∏ i, φ i (g i)) * ⟪w, π (List.ofFn fun i => s i (g i)).prod v⟫_ℂ
        ∂(Measure.pi fun _ => μ) := by
  intro k
  induction k with
  | zero =>
    intro s hs φ w v
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ) (fun i => i.elim0), integral_dirac]
    simp
  | succ k ih =>
    intro s hs φ w v
    have hint : ∀ i, Integrable (φ i) μ := fun i =>
      (φ i).continuous.integrable_of_hasCompactSupport (φ i).hasCompactSupport
    have hF : Integrable (fun g : Fin (k + 1) → G =>
        (∏ i, φ i (g i)) * ⟪w, π (List.ofFn fun i => s i (g i)).prod v⟫_ℂ)
        (Measure.pi fun _ => μ) := by
      refine (Integrable.fintype_prod (f := fun i => (φ i : G → ℂ)) hint).mul_bdd
        (c := ‖w‖ * ‖v‖) ?_ (Filter.Eventually.of_forall fun g => π.norm_inner_orbit_le w v _)
      exact (continuous_const.inner ((π.continuous_orbit v).comp
        (continuous_ofFn_prod _ s hs))).aestronglyMeasurable
    have mp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0).symm
    rw [← mp.integral_comp' _]
    refine Eq.trans ?_ (integral_prod _ (mp.integrable_comp_of_integrable hF)).symm
    rw [List.ofFn_succ, List.prod_cons, ContinuousLinearMap.mul_apply, inner_cc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [UnitaryRep.compHom_apply]
    rw [UnitaryRep.inner_map_right, ih (fun i => s i.succ) (fun i => hs _) (fun i => φ i.succ),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.prod_univ_succ, List.ofFn_succ,
      List.prod_cons, Fin.insertNthEquiv_zero, Fin.cons_zero, Fin.cons_succ]
    show _ = (φ 0 x * ∏ i, φ i.succ (g i)) *
      ⟪w, π (s 0 x * (List.ofFn fun i => s i.succ (g i)).prod) v⟫_ℂ
    rw [UnitaryRep.map_mul_apply, UnitaryRep.inner_map_right π (s 0 x) w]
    ring

end General

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.tensOp :
    UpperTheory.ConvolutionTheory.L1.TensOp := by
  intro F E _ _ _ _ _ σ m D n νE _ νF _ hν s hs hposition H _ _ _ π φ β hβ
  obtain ⟨hcg, -, hmul, hcont, -⟩ := UpperTheory.ConvolutionTheory.L1.archBasic F E σ m D n
  have hglue : ∀ g : Fin (m + 1) → archGroup F n,
      UpperTheory.ConvolutionTheory.L1.glueA D n g = (List.ofFn fun i => s i (g i)).prod := by
    intro g
    have e := map_list_prod (MonoidHom.mk' (UpperTheory.ConvolutionTheory.L1.glueA D n) hmul)
      (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin (m + 1) → archGroup F n))
    rw [UpperTheory.ConvolutionTheory.L1.ofFn_mulSingle, List.map_ofFn] at e
    refine e.trans ?_
    congr 1
    congr 1
    funext i
    exact (hposition i (g i)).symm
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [UpperTheory.ConvolutionTheory.L1.inner_ofFn_prod, UpperTheory.ConvolutionTheory.L1.inner_cc]
  have hm : Continuous fun x : archGroup E n => β x * ⟪w, π x v⟫_ℂ :=
    β.continuous.mul (continuous_const.inner (π.continuous_orbit v))
  have e1 : ∫ x, β x * ⟪w, π x v⟫_ℂ ∂νE = ∫ x, β x * ⟪w, π x v⟫_ℂ
      ∂(Measure.map (UpperTheory.ConvolutionTheory.L1.glueA D n) (Measure.pi fun _ => νF)) := by
    rw [← hν]
  rw [e1, integral_map hcont.aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [hβ, hglue g]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hglue g, hcg]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchSlotEx
open MeasureTheory
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

private theorem asx_cvPow {a : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (k : ℕ) :
    Continuous (cvPow μ a k) ∧ HasCompactSupport (cvPow μ a k) := by
  induction k with
  | zero => exact ⟨ha, ha'⟩
  | succ k ih =>
    have h := cvBasic G μ a (cvPow μ a k) a ha ha' ih.1 ih.2 ha ha'
    exact ⟨h.1, h.2.1⟩

private theorem asx_star {b : G → ℂ} (hb : Continuous b) (hb' : HasCompactSupport b) :
    Continuous (fun x => conj (b x⁻¹)) ∧ HasCompactSupport (fun x => conj (b x⁻¹)) := by
  refine ⟨by fun_prop, ?_⟩
  have h : HasCompactSupport (fun x => b x⁻¹) := hb'.comp_homeomorph (Homeomorph.inv G)
  exact h.comp_left (g := fun z : ℂ => conj z) (map_zero _)

end

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.archPositionEx :
    UpperTheory.ConvolutionTheory.L1.ArchSlotEx := by
  intro F E _ _ _ _ _ σ m D n νF _ b hs hf hn
  obtain ⟨-, -, -, -, -, -, hHaar, hTens⟩ := archBasic F E σ m D n
  have hb : Continuous (fun g => b g) := map_continuous b
  have hb' : HasCompactSupport (fun g => b g) := b.hasCompactSupport
  obtain ⟨h1, h2⟩ := asx_star hb hb'
  have hc := cvBasic _ νF (fun g => b g) (fun x => conj (b x⁻¹)) (fun g => b g) hb hb' h1 h2 hb hb'
  let a : TI F n := ⟨⟨cv νF (fun g => b g) (fun x => conj (b x⁻¹)), hc.1⟩, hc.2.1⟩
  obtain ⟨aE, haE⟩ := hTens fun _ => a
  obtain ⟨h3, h4⟩ := asx_cvPow νF (a := fun g => a g) (map_continuous a) a.hasCompactSupport m
  let aF : TI F n := ⟨⟨cvPow νF (fun g => a g) m, h3⟩, h4⟩
  exact ⟨_, hHaar νF, a, aE, aF,
    { meas := rfl, smooth := hs, fin := hf, norm := hn, sq := fun _ => rfl, tens := haE, pow := fun _ => rfl }⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmoothAlt
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory
open scoped ContDiff

namespace UpperTheory.ConvolutionTheory.L1

private theorem fin_prod {ι X : Type} [Fintype ι] {Y : ι → Type} (p : ∀ i, X → Y i) (S : ∀ i, Set (Y i → ℂ))
    (hS : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ (S i))) :
    FiniteDimensional ℂ (Submodule.span ℂ
      {f : X → ℂ | ∃ s : ∀ i, Y i → ℂ, (∀ i, s i ∈ S i) ∧ f = fun x => ∏ i, s i (p i x)}) := by
  classical
  let T : (∀ i, Y i → ℂ) →ₘₗ[ℂ] (X → ℂ) :=
    (MultilinearMap.mkPiAlgebra ℂ ι (X → ℂ)).compLinearMap (fun i => LinearMap.funLeft ℂ ℂ (p i))
  have hT : ∀ s x, T s x = ∏ i, s i (p i x) := by
    intro s x
    simp [T, MultilinearMap.compLinearMap_apply, Finset.prod_apply, LinearMap.funLeft_apply]
  let d : ι → ℕ := fun i => Module.finrank ℂ (Submodule.span ℂ (S i))
  let b : ∀ i, Module.Basis (Fin (d i)) ℂ (Submodule.span ℂ (S i)) := fun i => Module.finBasis ℂ _
  let R : Set (X → ℂ) := Set.range fun r : ∀ i, Fin (d i) => T fun i => ((b i (r i) : Submodule.span ℂ (S i)) : Y i → ℂ)
  have hR : R.Finite := Set.finite_range _
  have hle : Submodule.span ℂ {f : X → ℂ | ∃ s : ∀ i, Y i → ℂ, (∀ i, s i ∈ S i) ∧ f = fun x => ∏ i, s i (p i x)} ≤
      Submodule.span ℂ R := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨s, hs, rfl⟩
    have hs' : ∀ i, s i ∈ Submodule.span ℂ (S i) := fun i => Submodule.subset_span (hs i)
    let c : ∀ i, Fin (d i) → ℂ := fun i j => (b i).repr ⟨s i, hs' i⟩ j
    have hsum : ∀ i, s i = ∑ j, c i j • ((b i j : Submodule.span ℂ (S i)) : Y i → ℂ) := by
      intro i
      have h := (b i).sum_repr ⟨s i, hs' i⟩
      calc s i = ((⟨s i, hs' i⟩ : Submodule.span ℂ (S i)) : Y i → ℂ) := rfl
        _ = ((∑ j, c i j • b i j : Submodule.span ℂ (S i)) : Y i → ℂ) := by rw [h]
        _ = _ := by rw [AddSubmonoidClass.coe_finsetSum]; rfl
    have e : (fun x => ∏ i, s i (p i x)) = T s := funext fun x => (hT s x).symm
    have e2 : T s = T fun i => ∑ j, c i j • ((b i j : Submodule.span ℂ (S i)) : Y i → ℂ) :=
      congrArg T (funext hsum)
    show (fun x => ∏ i, s i (p i x)) ∈ (Submodule.span ℂ R : Set (X → ℂ))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, e2, MultilinearMap.map_sum]
    refine Submodule.sum_mem _ fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ R) := FiniteDimensional.span_of_finite ℂ hR
  exact Submodule.finiteDimensional_of_le hle

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E ≃ₐ[F] E} {m : ℕ}

private def cR (D : InfD σ m) (i : Fin (m + 1)) : InfiniteAdeleRing E →+* InfiniteAdeleRing F :=
  (Pi.evalRingHom (fun _ : Fin (m + 1) => InfiniteAdeleRing F) i).comp D.e.toRingHom

private theorem continuous_cR (D : InfD σ m) (i : Fin (m + 1)) : Continuous (cR D i) :=
  (continuous_apply i).comp D.cont

private def thetaR (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : ArchMatrix E n →+* ArchMatrix F n :=
  (archMatrixEquiv F n).toRingHom.comp ((RingHom.mapMatrix (cR D i)).comp (archMatrixEquiv E n).symm.toRingHom)

private theorem continuous_thetaR (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : Continuous (thetaR D n i) := by
  have h1 : Continuous fun M : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E) => M.map (cR D i) :=
    continuous_id.matrix_map (continuous_cR D i)
  exact (continuous_archMatrixEquiv F n).comp (h1.comp (continuous_archMatrixEquiv_symm E n))

private theorem compA_val (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (g : archGroup E n) :
    (((compA D n i g : archGroup F n) : (ArchMatrix F n)ˣ) : ArchMatrix F n) =
      thetaR D n i ((g : (ArchMatrix E n)ˣ) : ArchMatrix E n) := rfl

private theorem thetaR_exp (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (X : ArchMatrix E n) :
    thetaR D n i (NormedSpace.exp X) = NormedSpace.exp (thetaR D n i X) := by
  letI : NormedAlgebra ℚ (ArchMatrix E n) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℚ (ArchMatrix F n) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact NormedSpace.map_exp (thetaR D n i) (continuous_thetaR D n i) X

private def thetaL (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : archLie E n →L[ℝ] archLie F n where
  toFun Y := ⟨thetaR D n i (Y : ArchMatrix E n), Submodule.mem_top⟩
  map_add' X Y := Subtype.ext (map_add (thetaR D n i) _ _)
  map_smul' c X := Subtype.ext (map_real_smul (thetaR D n i) (continuous_thetaR D n i) c _)
  cont := ((continuous_thetaR D n i).comp continuous_subtype_val).subtype_mk _

private theorem compA_expG (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (Y : archLie E n) :
    compA D n i ((isExpLieAlgebra E n).expG Y) = (isExpLieAlgebra F n).expG (thetaL D n i Y) := by
  apply Subtype.ext
  apply Units.ext
  rw [compA_val, IsExpLieAlgebra.coe_expG, IsExpLieAlgebra.coe_expG]
  exact thetaR_exp D n i _

private theorem tens_smooth (D : InfD σ m) (n : ℕ) (φ : Fin (m + 1) → TI F n) (β : TI E n) (hβ : IsTens D φ β)
    (hφ : ∀ i, SmoothT (φ i)) : SmoothT β := by
  refine (IsExpLieAlgebra.isSmoothFun_iff (isExpLieAlgebra E n)).2 fun g => ?_
  have e : (fun Y : archLie E n => β (g * (isExpLieAlgebra E n).expG Y)) = fun Y => ∏ i,
      (fun Z : archLie F n => φ i (compA D n i g * (isExpLieAlgebra F n).expG Z)) (thetaL D n i Y) := by
    funext Y
    rw [hβ]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, compA_expG]
  rw [e]
  refine contDiff_prod fun i _ => ?_
  exact ((IsExpLieAlgebra.isSmoothFun_iff (isExpLieAlgebra F n)).1 (hφ i) _).comp (thetaL D n i).contDiff

private theorem tens_fin [_root_.NumberField.IsTotallyComplex F] (D : InfD σ m) (n : ℕ) (φ : Fin (m + 1) → TI F n) (β : TI E n)
    (hβ : IsTens D φ β) (hφ : ∀ i, LeftFin (φ i)) : LeftFin β := by
  haveI := fin_prod (ι := Fin (m + 1)) (X := archGroup E n) (Y := fun _ => archGroup F n) (fun i => compA D n i)
    (fun i => Set.range fun k : archCompact F n => fun g : archGroup F n => φ i ((k : archGroup F n) * g)) hφ
  have hsub : (Set.range fun k : archCompact E n => fun g : archGroup E n => β ((k : archGroup E n) * g)) ⊆
      {f | ∃ s : Fin (m + 1) → archGroup F n → ℂ, (∀ i, s i ∈ Set.range fun k : archCompact F n =>
        fun g : archGroup F n => φ i ((k : archGroup F n) * g)) ∧ f = fun x => ∏ i, s i (compA D n i x)} := by
    rintro f ⟨k, rfl⟩
    have hk := ((positionOf F E σ m D).2 n (k : archGroup E n)).1 k.2
    refine ⟨fun i g => φ i (compA D n i k * g), fun i => ⟨⟨_, hk i⟩, rfl⟩, ?_⟩
    funext x
    show β ((k : archGroup E n) * x) = _
    rw [hβ]
    exact Finset.prod_congr rfl fun i _ => by rw [map_mul]
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.tensSmooth :
    UpperTheory.ConvolutionTheory.L1.TensSmooth := by
  intro F E _ _ _ _ _ _ σ m D n φ β hβ
  exact ⟨UpperTheory.ConvolutionTheory.L1.tens_smooth D n φ β hβ, UpperTheory.ConvolutionTheory.L1.tens_fin D n φ β hβ⟩
end
end
