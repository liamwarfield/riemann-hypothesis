module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchBasic
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo

theorem UpperTheory.ConvolutionTheory.L1.archBasic :
    UpperTheory.ConvolutionTheory.L1.ArchBasic := by
  intro F E _ _ _ _ _ σ m D n
  obtain ⟨h1, h2, h3, h4, h5, -⟩ :=
    UpperTheory.ConvolutionTheory.L1.glueBasic (InfiniteAdeleRing F) (InfiniteAdeleRing E) _ _ m D n
  have compA_apply : ∀ i x, UpperTheory.ConvolutionTheory.L1.compA D n i x =
      archEquiv F n (D.comp n i ((archEquiv E n).symm x)) := fun _ _ => rfl
  have glueA_apply : ∀ g, UpperTheory.ConvolutionTheory.L1.glueA D n g =
      archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i)) := fun _ => rfl
  have c1 : ∀ g i, UpperTheory.ConvolutionTheory.L1.compA D n i (UpperTheory.ConvolutionTheory.L1.glueA D n g) = g i := by
    intro g i
    rw [compA_apply, glueA_apply, ContinuousMulEquiv.symm_apply_apply, h1,
      ContinuousMulEquiv.apply_symm_apply]
  have c2 : ∀ x, UpperTheory.ConvolutionTheory.L1.glueA D n (fun i => UpperTheory.ConvolutionTheory.L1.compA D n i x) = x := by
    intro x
    rw [glueA_apply]
    simp only [compA_apply, ContinuousMulEquiv.symm_apply_apply]
    rw [h2, ContinuousMulEquiv.apply_symm_apply]
  have c3 : ∀ g h, UpperTheory.ConvolutionTheory.L1.glueA D n (g * h) =
      UpperTheory.ConvolutionTheory.L1.glueA D n g * UpperTheory.ConvolutionTheory.L1.glueA D n h := by
    intro g h
    simp only [glueA_apply]
    rw [← map_mul, ← h3]
    congr 2
    funext i
    exact map_mul (archEquiv F n).symm (g i) (h i)
  have c4 : Continuous (UpperTheory.ConvolutionTheory.L1.glueA D n) := by
    have : Continuous fun g : Fin (m + 1) → archGroup F n =>
        archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i)) :=
      (archEquiv E n).continuous.comp
        (h4.comp (continuous_pi fun i => (archEquiv F n).symm.continuous.comp (continuous_apply i)))
    exact this
  have c5 : ∀ i, Continuous (UpperTheory.ConvolutionTheory.L1.compA D n i) := by
    intro i
    have : Continuous fun x : archGroup E n =>
        archEquiv F n (D.comp n i ((archEquiv E n).symm x)) :=
      (archEquiv F n).continuous.comp ((h5 i).comp (archEquiv E n).symm.continuous)
    exact this
  let e : (Fin (m + 1) → archGroup F n) ≃ₜ* archGroup E n :=
    { toFun := UpperTheory.ConvolutionTheory.L1.glueA D n
      invFun := fun x i => UpperTheory.ConvolutionTheory.L1.compA D n i x
      left_inv := fun g => funext (c1 g)
      right_inv := c2
      map_mul' := c3
      continuous_toFun := c4
      continuous_invFun := continuous_pi c5 }
  refine ⟨c1, c2, c3, c4, c5, ?_, ?_, ?_⟩
  · refine ⟨fun i => (e.toMulEquiv.toMonoidHom).comp (MonoidHom.mulSingle (fun _ : Fin (m + 1) => archGroup F n) i), ?_, ?_⟩
    · intro i g
      rfl
    · intro i
      have hm : Continuous fun g : archGroup F n => (Pi.mulSingle i g : Fin (m + 1) → archGroup F n) :=
        by
          refine continuous_pi fun j => ?_
          by_cases hj : j = i
          · subst hj
            simpa using (continuous_id' : Continuous fun a : archGroup F n => a)
          · simpa [Pi.mulSingle_eq_of_ne hj] using continuous_const
      exact c4.comp hm
  · intro νF _
    exact e.isHaarMeasure_map (Measure.pi fun _ => νF)
  · intro φ
    have hc : Continuous fun g : archGroup E n => ∏ i, φ i (UpperTheory.ConvolutionTheory.L1.compA D n i g) :=
      continuous_finsetProd _ fun i _ => (φ i).continuous.comp (c5 i)
    have hK : IsCompact (UpperTheory.ConvolutionTheory.L1.glueA D n '' Set.pi Set.univ fun i => tsupport (φ i)) :=
      (isCompact_univ_pi fun i => (φ i).hasCompactSupport).image c4
    have hs : HasCompactSupport fun g : archGroup E n => ∏ i, φ i (UpperTheory.ConvolutionTheory.L1.compA D n i g) := by
      refine HasCompactSupport.of_support_subset_isCompact hK ?_
      intro x hx
      refine ⟨fun i => UpperTheory.ConvolutionTheory.L1.compA D n i x, ?_, c2 x⟩
      intro i _
      apply subset_tsupport
      intro h0
      exact hx (Finset.prod_eq_zero (Finset.mem_univ i) h0)
    exact ⟨⟨⟨_, hc⟩, hs⟩, fun g => rfl⟩
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.FinSplit
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.L1

private theorem pi_factor {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ι → Type*} [∀ i, Field (k i)]
    {K : Type*} [Field K] (φ : (∀ i, k i) →+* K) : ∃ w, ∀ b : ∀ i, k i, b w = 0 → φ b = 0 := by
  have h1 : ∑ i, φ (Pi.single i 1) = 1 := by
    have h : (∑ x, Pi.single x 1 : ∀ i, k i) = 1 := Finset.univ_sum_single (1 : ∀ i, k i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, h, map_one]
  obtain ⟨w, hw⟩ : ∃ w, φ (Pi.single w 1) ≠ 0 := by
    by_contra! h
    simp [h] at h1
  refine ⟨w, fun b hb => ?_⟩
  have h0 : b * Pi.single w 1 = 0 := by
    ext i
    by_cases h : i = w
    · subst h
      simp [hb]
    · simp [Pi.single_eq_of_ne h]
  have h2 := congrArg φ h0
  rw [map_mul, map_zero] at h2
  exact (mul_eq_zero.1 h2).resolve_right hw

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem comp_eq (v : HeightOneSpectrum (𝓞 F)) (φ : CompletionsOver E v →+* v.adicCompletion F)
    (hφ : ∀ a, φ (incFin E v a) = a)
    (hs : ∀ w : PlacesOver E v, Function.Surjective (completionMap v w.1)) :
    ∃ w : PlacesOver E v, ∀ b, completionMap v w.1 (φ b) = b w := by
  classical
  obtain ⟨w, hw⟩ := pi_factor φ
  refine ⟨w, fun b => ?_⟩
  obtain ⟨a, ha⟩ := hs w (b w)
  have h : φ (b - incFin E v a) = 0 := hw _ (by
    change b w - completionMap v w.1 a = 0
    rw [ha, sub_self])
  rw [map_sub, hφ, sub_eq_zero] at h
  rw [h, ha]

private noncomputable def pt (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v)
    (hs : Function.Surjective (completionMap v w.1)) : E →ₐ[F] v.adicCompletion F where
  toRingHom := (RingEquiv.ofBijective (completionMap v w.1)
    ⟨(completionMap v w.1).injective, hs⟩).symm.toRingHom.comp (algebraMap E (w.1.adicCompletion E))
  commutes' r := by
    change (RingEquiv.ofBijective (completionMap v w.1) _).symm _ = _
    rw [RingEquiv.symm_apply_eq]
    change _ = completionMap v w.1 _
    rw [completionMap_algebraMap, ← IsScalarTower.algebraMap_apply]

private theorem completionMap_pt (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v)
    (hs : Function.Surjective (completionMap v w.1)) (x : E) :
    completionMap v w.1 (pt v w hs x) = algebraMap E (w.1.adicCompletion E) x :=
  (RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs⟩).apply_symm_apply _

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.finSplit :
    UpperTheory.ConvolutionTheory.L1.FinSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm v w₀ hs
  classical
  obtain ⟨e, he, hshift⟩ := UpperTheory.ConvolutionTheory.L1.galSplit F E σ hσ m hm (v.adicCompletion F)
    (CompletionsOver E v) (tensorEquiv' E v) (pt v w₀ (hs w₀))
  have hinc : ∀ r, incFin E v r = tensorEquiv' E v (1 ⊗ₜ r) := fun r => by
    rw [tensorEquiv'_tmul, map_one, one_mul]
    rfl
  have hdiag : ∀ r i, e (incFin E v r) i = r := fun r i => by
    rw [hinc, he, map_one, map_one, one_mul]
  have hsmul : ∀ (a : v.adicCompletion F) (b : CompletionsOver E v), e (a • b) = a • e b := by
    intro a b
    funext i
    rw [Algebra.smul_def, map_mul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg (· * e b i) (hdiag a i)
  let L : CompletionsOver E v ≃ₗ[v.adicCompletion F] (Fin (m + 1) → v.adicCompletion F) :=
    { e.toAddEquiv with map_smul' := hsmul }
  let D : Split (incFin E v) (galFin σ v) m :=
    { e := e
      cont := IsModuleTopology.continuous_of_linearMap L.toLinearMap
      cont_symm := IsModuleTopology.continuous_of_linearMap L.symm.toLinearMap
      map_diag := hdiag
      map_shift := hshift }
  have hcomp : ∀ i, ∃ w : PlacesOver E v, ∀ b, completionMap v w.1 (e b i) = b w := fun i =>
    comp_eq v ((Pi.evalRingHom _ i).comp e.toRingHom) (fun a => hdiag a i) hs
  choose w hw using hcomp
  have hne : ∀ i u, e (Pi.single u 1) i ≠ 0 → w i = u := by
    intro i u h
    by_contra hu
    apply h
    apply (completionMap v (w i).1).injective
    rw [hw, map_zero, Pi.single_eq_of_ne hu]
  have hinj : Function.Injective w := by
    intro i j h
    by_contra hij
    have key : ∀ u, u = w j → ∀ b, completionMap v u.1 (e b i) = b u → e b i = e b j := by
      intro u hu b h3
      subst hu
      exact (completionMap v (w j).1).injective (h3.trans (hw j b).symm)
    have h4 := key _ h (e.symm (Pi.single i 1)) (hw i _)
    rw [RingEquiv.apply_symm_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at h4
    exact one_ne_zero h4
  have hsurj : Function.Surjective w := by
    intro u
    have h1 : e (Pi.single u 1) ≠ 0 := fun h => by
      have h2 := congrFun ((map_eq_zero_iff e e.injective).1 h) u
      rw [Pi.single_eq_same] at h2
      exact one_ne_zero h2
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h1
    exact ⟨i, hne i u hi⟩
  have h0 : ∀ b : CompletionsOver E v, completionMap v w₀.1 (e b 0) = b w₀ := by
    intro b
    obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective b
    induction t with
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), Pi.add_apply, map_add (f := _), hx, hy, Pi.add_apply]
    | tmul x a =>
      rw [he, map_mul]
      simp only [Fin.val_zero, pow_zero]
      rw [show ((1 : E ≃ₐ[F] E) x) = x from rfl, completionMap_pt, tensorEquiv'_tmul]
      rfl
  have hw0 : w 0 = w₀ := by
    refine hne 0 w₀ fun h => ?_
    have h1 := h0 (Pi.single w₀ 1)
    rw [h, map_zero, Pi.single_eq_same] at h1
    exact zero_ne_one h1
  exact ⟨D, Equiv.ofBijective w ⟨hinj, hsurj⟩, hw0, fun b i => hw i b⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.IntPow
open MeasureTheory NumberField
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup K n) H)

private theorem int_cv (f e g : TI K n) (hg : ∀ x, g x = cv ν f e x) :
    π.integrated ν (UnitaryRep.ccToL1 ν g) =
      π.integrated ν (UnitaryRep.ccToL1 ν f) * π.integrated ν (UnitaryRep.ccToL1 ν e) := by
  obtain ⟨g', h1, -, h2⟩ := UpperTheory.ConvolutionTheory.Tf.homConv (archGroup K n) (archGroup K n) (MonoidHom.id _)
    continuous_id ν ν f e
  have hgg : g = g' := by
    ext x
    rw [hg, h1]
    rfl
  subst hgg
  rw [h2 H π]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply,
    UnitaryRep.integrated_ccToL1_apply, UnitaryRep.compHom_apply]
  rfl

private theorem int_pow (a : TI K n) (k : ℕ) :
    ∃ c : TI K n, (∀ g, c g = cvPow ν a k g) ∧
      π.integrated ν (UnitaryRep.ccToL1 ν c) = π.integrated ν (UnitaryRep.ccToL1 ν a) ^ (k + 1) := by
  induction k with
  | zero => exact ⟨a, fun _ => rfl, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc, hT⟩ := ih
    obtain ⟨h1, h2, -⟩ := UpperTheory.ConvolutionTheory.L1.cvBasic (archGroup K n) ν a c a a.continuous a.hasCompactSupport
      c.continuous c.hasCompactSupport a.continuous a.hasCompactSupport
    have hfun : (c : archGroup K n → ℂ) = cvPow ν a k := funext hc
    refine ⟨⟨⟨cv ν a c, h1⟩, h2⟩, fun g => ?_, ?_⟩
    · change cv ν a c g = cv ν a (cvPow ν a k) g
      rw [hfun]
    · rw [int_cv ν π a c _ (fun _ => rfl), hT, pow_succ' _ (k + 1)]

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.sqOp :
    UpperTheory.ConvolutionTheory.L1.SqOp := by
  intro K _ _ n ν _ b a aF m ha haF hb H _ _ _ π
  obtain ⟨-, hinv⟩ := (UpperTheory.ConvolutionTheory.Tf.unimod K n).1 ν
  let bs : TI K n := ⟨⟨fun x => conj (b x⁻¹),
      Complex.continuous_conj.comp (b.continuous.comp continuous_inv)⟩,
    (b.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := fun z => conj z) (map_zero _)⟩
  obtain ⟨hadj, hnorm, -⟩ := UpperTheory.ConvolutionTheory.Tf.adjInt (archGroup K n) H π ν b bs (fun _ => rfl)
  have hT : π.integrated ν (UnitaryRep.ccToL1 ν a) =
      π.integrated ν (UnitaryRep.ccToL1 ν b) * star (π.integrated ν (UnitaryRep.ccToL1 ν b)) := by
    rw [ContinuousLinearMap.star_eq_adjoint, hadj]
    exact int_cv ν π b bs a ha
  have hb1 : ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ ≤ 1 := hnorm.trans hb
  obtain ⟨c, hc, hcT⟩ := int_pow ν π a m
  have hcF : c = aF := by
    ext g
    rw [hc, haF]
  refine ⟨hT, ?_, ?_, hcF ▸ hcT⟩
  · rw [hT]
    exact mul_star_self_nonneg _
  · rw [hT]
    calc _ ≤ ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ * ‖star (π.integrated ν (UnitaryRep.ccToL1 ν b))‖ := norm_mul_le _ _
      _ = ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ * ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ := by rw [norm_star]
      _ ≤ 1 := mul_le_one₀ hb1 (norm_nonneg _) hb1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.InfSplit
open NumberField GroundTheory.Global.InfinitePlace
open scoped TensorProduct

theorem UpperTheory.ConvolutionTheory.L1.infSplit :
    UpperTheory.ConvolutionTheory.L1.InfSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm
  refine ⟨fun hF => ?_, fun p => ?_⟩
  · have h : ∀ v : InfinitePlace F, Nonempty (E →ₐ[F] v.Completion) := fun v => by
      haveI : IsAlgClosed v.Completion :=
        IsAlgClosed.of_ringEquiv ℂ _
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex (hF.isComplex v)).symm
      exact ⟨IsAlgClosed.lift⟩
    exact ⟨Pi.algHom F (fun v : InfinitePlace F => v.Completion) fun v => (h v).some⟩
  · obtain ⟨e, he, hs⟩ := UpperTheory.ConvolutionTheory.L1.galSplit F E σ hσ m hm (InfiniteAdeleRing F) (InfiniteAdeleRing E)
      (tensorInfiniteAdeleRingEquiv (K := F) (L := E)) p
    have hd : ∀ r i, e (infiniteAdeleRingMap (K := F) (L := E) r) i = r := fun r i => by
      have := he 1 r i
      rwa [tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul, map_one, map_one, one_mul] at this
    have hx : ∀ (x : E) i, e (algebraMap E (InfiniteAdeleRing E) x) i = p ((σ ^ (i : ℕ)) x) := fun x i => by
      have := he x 1 i
      rwa [tensorInfiniteAdeleRingEquiv_tmul', map_one, mul_one, mul_one] at this
    refine ⟨⟨e, ?_, ?_, hd, hs⟩, hx⟩
    · let b := Module.finBasis F E
      have h : ∀ y i, e y i = ∑ j, p ((σ ^ (i : ℕ)) (b j)) * adeleCoord b j y := fun y i => by
        conv_lhs => rw [← tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum, Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ => he _ _ _
      refine continuous_pi fun i => ?_
      simp_rw [h]
      exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_adeleCoord b j)
    · have h : ∀ a, e.symm a =
          ∑ i, infiniteAdeleRingMap (K := F) (L := E) (a i) * e.symm (Pi.single i 1) := fun a => by
        apply e.injective
        funext k
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_apply, RingEquiv.apply_symm_apply]
        simp_rw [map_mul, RingEquiv.apply_symm_apply, Pi.mul_apply, hd]
        rw [Finset.sum_eq_single k]
        · simp
        · intro j _ hj
          rw [Pi.single_eq_of_ne hj.symm, mul_zero]
        · simp
      have h' : (e.symm : _ → _) = fun a => ∑ i, infiniteAdeleRingMap (K := F) (L := E) (a i) * e.symm (Pi.single i 1) :=
        funext h
      rw [h']
      exact continuous_finsetSum _ fun i _ =>
        (continuous_infiniteAdeleRingMap.comp (continuous_apply i)).mul continuous_const
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactLaws
theorem UpperTheory.ConvolutionTheory.L1.lactLaws :
    UpperTheory.ConvolutionTheory.L1.LactLaws := by
  intro K _ _ n β hβ
  obtain ⟨_, _, hs, h1, hm, hc, _, _⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  exact ⟨fun u => (hs u).1, h1, fun u v => (hm u v).1, fun u v => (hm u v).2, fun c u => (hc c u).1⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PushTens
open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private lemma fib_cons {m : ℕ} (a : G) (y : Fin m → G) (x : G) :
    fib (Fin.cons (α := fun _ => G) a y) x = Fin.cons (α := fun _ => G) a (fib y (a⁻¹ * x)) := by
  unfold fib
  rw [← Fin.cons_snoc_eq_snoc_cons]
  congr 2
  simp [List.ofFn_succ, mul_assoc]

private lemma continuous_fib {m : ℕ} (x : G) : Continuous fun y : Fin m → G => fib y x := by
  have hp : Continuous fun y : Fin m → G => (List.ofFn y).prod := by
    simp only [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i _ => continuous_apply i
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [fib, Fin.snoc_last]
    exact (hp.inv).mul continuous_const
  · simp only [fib, Fin.snoc_castSucc]
    exact continuous_apply j

private lemma integrable_fib (μ : Measure G) [μ.IsHaarMeasure] (m : ℕ) (φ : Fin (m + 1) → G → ℂ)
    (hc : ∀ i, Continuous (φ i)) (hs : ∀ i, HasCompactSupport (φ i)) (x : G) :
    Integrable (fun y : Fin m → G => ∏ i, φ i (fib y x i)) (Measure.pi fun _ => μ) := by
  have hcont : Continuous fun y : Fin m → G => ∏ i, φ i (fib y x i) :=
    continuous_finsetProd _ fun i _ =>
      (hc i).comp ((continuous_apply i).comp (continuous_fib x))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro
    (K := Set.pi Set.univ fun i : Fin m => tsupport (φ i.castSucc))
    (isCompact_univ_pi fun i => hs _) fun y hy => ?_
  simp only [Set.mem_pi, Set.mem_univ, forall_const, not_forall] at hy
  obtain ⟨i, hi⟩ := hy
  refine Finset.prod_eq_zero (Finset.mem_univ i.castSucc) ?_
  simp only [fib, Fin.snoc_castSucc]
  exact image_eq_zero_of_notMem_tsupport hi

private lemma push_tens (μ : Measure G) [μ.IsHaarMeasure] : ∀ (m : ℕ) (φ : Fin (m + 1) → G → ℂ),
    (∀ i, Continuous (φ i)) → (∀ i, HasCompactSupport (φ i)) →
    push μ m (fun g => ∏ i, φ i (g i)) = cvAll μ m φ := by
  intro m
  induction m with
  | zero =>
    intro φ _ _
    funext x
    simp [push, cvAll, fib, Measure.real, Measure.pi_empty_univ, Fin.snoc]
  | succ m ih =>
    intro φ hc hs
    funext x
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
    have hint := integrable_fib μ (m + 1) φ hc hs x
    set F : (Fin (m + 1) → G) → ℂ := fun y => ∏ i, φ i (fib y x i) with hF
    have hsymm := hmp.symm
    have hint' : Integrable (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0).symm)
        (μ.prod (Measure.pi fun _ => μ)) :=
      (hsymm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hint
    have hval : ∀ (a : G) (y : Fin m → G),
        (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0).symm) (a, y) =
          φ 0 a * ∏ i, Fin.tail φ i (fib y (a⁻¹ * x) i) := by
      intro a y
      have : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => G) 0).symm (a, y) =
          Fin.cons (α := fun _ => G) a y := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove]
      simp only [Function.comp, this, hF, fib_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    show ∫ y, F y ∂(Measure.pi fun _ => μ) = _
    refine (hsymm.integral_comp' F).symm.trans ((integral_prod _ hint').trans ?_)
    simp only [cvAll, cv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [hval, integral_const_mul]
    have := congrFun (ih (Fin.tail φ) (fun i => hc _) (fun i => hs _)) (a⁻¹ * x)
    rw [← this]
    rfl

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.pushTens :
    UpperTheory.ConvolutionTheory.L1.PushTens := by
  intro G _ _ _ _ _ _ _ _ μ _ m φ hc hs
  exact UpperTheory.ConvolutionTheory.L1.push_tens μ m φ hc hs
end
