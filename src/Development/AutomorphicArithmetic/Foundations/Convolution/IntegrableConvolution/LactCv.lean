module

public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactConv
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchProd

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactCv
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1

private theorem cv_eq_conv {K : Type} [Field K] [NumberField K] {n : ℕ} (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] (α β : TI K n) (g : archGroup K n) : cv ν α β g = conv ν α β g := by
  rw [conv_apply]
  rfl

private theorem leftFin_cv {K : Type} [Field K] [NumberField K] {n : ℕ} (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] (α β γ : TI K n) (hγ : ∀ g, γ g = cv ν α β g) (hα : LeftFin α) : LeftFin γ := by
  unfold LeftFin at hα ⊢
  set W := Submodule.span ℂ (Set.range fun k : archCompact K n => fun g : archGroup K n => α ((k : archGroup K n) * g))
    with hW
  have hW' : ∀ f ∈ W, Continuous f ∧ HasCompactSupport f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨(map_continuous α).comp (continuous_const.mul continuous_id),
        α.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft (k : archGroup K n))⟩
    | zero => exact ⟨continuous_zero, HasCompactSupport.zero⟩
    | add x y _ _ hx hy => exact ⟨hx.1.add hy.1, hx.2.add hy.2⟩
    | smul c x _ hx => exact ⟨hx.1.const_smul c, hx.2.smul_left⟩
  have hint : ∀ f ∈ W, ∀ g : archGroup K n, Integrable (fun y => f y * β (y⁻¹ * g)) ν := by
    intro f hf g
    obtain ⟨h1, h2⟩ := hW' f hf
    exact (h1.mul ((map_continuous β).comp (continuous_inv.mul continuous_const))).integrable_of_hasCompactSupport
      h2.mul_right
  let T : W →ₗ[ℂ] (archGroup K n → ℂ) :=
    { toFun := fun f g => ∫ y, (f : archGroup K n → ℂ) y * β (y⁻¹ * g) ∂ν
      map_add' := by
        intro f f'
        funext g
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
        exact integral_add (hint f f.2 g) (hint f' f'.2 g)
      map_smul' := by
        intro c f
        funext g
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
  have hle : Submodule.span ℂ (Set.range fun k : archCompact K n => fun g : archGroup K n => γ ((k : archGroup K n) * g)) ≤
      LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨⟨fun g => α ((k : archGroup K n) * g), Submodule.subset_span ⟨k, rfl⟩⟩, ?_⟩
    funext g
    change ∫ y, α ((k : archGroup K n) * y) * β (y⁻¹ * g) ∂ν = γ ((k : archGroup K n) * g)
    rw [hγ, cv, ← integral_mul_left_eq_self (μ := ν)
      (fun y => α y * β (y⁻¹ * ((k : archGroup K n) * g))) (k : archGroup K n)]
    congr 1
    funext y
    simp [mul_assoc]
  exact Submodule.finiteDimensional_of_le hle

theorem UpperTheory.ConvolutionTheory.L1.lactCv :
    UpperTheory.ConvolutionTheory.L1.LactCv := by
  intro K _ _ _ n ν _ α β γ hα hγ
  have e : γ = conv ν α β := by
    ext g
    rw [hγ, cv_eq_conv]
  obtain ⟨hs, hu, hz⟩ := UpperTheory.ConvolutionTheory.Tf.lactConv K n ν α β hα
  refine ⟨e ▸ hs, leftFin_cv ν α β γ hγ, fun u g => ?_, fun hβ z hz' g => ?_⟩
  · rw [e, hu, ← cv_eq_conv]
  · rw [e, hu, hz inferInstance hβ z hz', ← cv_eq_conv]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.UnitSplit
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

section Group

variable {G : Type} [Group G] [MeasurableSpace G]

private theorem cv_unit (μ : Measure G) (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (h1 : μ (K : Set G) = 1) :
    cv μ ((K : Set G).indicator 1) ((K : Set G).indicator 1) = (K : Set G).indicator (1 : G → ℂ) := by
  funext x
  by_cases hx : x ∈ K
  · have e : (fun y => (K : Set G).indicator (1 : G → ℂ) y * (K : Set G).indicator (1 : G → ℂ) (y⁻¹ * x)) =
        (K : Set G).indicator (fun _ => (1 : ℂ)) := by
      funext y
      by_cases hy : y ∈ K
      · have hyx : y⁻¹ * x ∈ K := K.mul_mem (K.inv_mem hy) hx
        simp [Set.indicator_of_mem, SetLike.mem_coe, hy, hyx]
      · simp [Set.indicator_of_notMem, SetLike.mem_coe, hy]
    simp only [cv]
    rw [e, integral_indicator hK]
    simp [Measure.real, h1, SetLike.mem_coe, hx]
  · have e : (fun y => (K : Set G).indicator (1 : G → ℂ) y * (K : Set G).indicator (1 : G → ℂ) (y⁻¹ * x)) =
        fun _ => 0 := by
      funext y
      by_cases hy : y ∈ K
      · have hyx : y⁻¹ * x ∉ K := fun h => hx (by simpa using K.mul_mem hy h)
        simp [SetLike.mem_coe, hyx]
      · simp [SetLike.mem_coe, hy]
    simp only [cv]
    rw [e]
    simp [SetLike.mem_coe, hx]

private theorem cvAll_unit (μ : Measure G) (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (h1 : μ (K : Set G) = 1) (m : ℕ) (φ : Fin (m + 1) → G → ℂ)
    (hφ : ∀ i, φ i = (K : Set G).indicator 1) : cvAll μ m φ = (K : Set G).indicator 1 := by
  induction m with
  | zero => exact hφ 0
  | succ m ih =>
    simp only [cvAll]
    rw [ih (Fin.tail φ) (fun i => hφ _), hφ 0]
    exact cv_unit μ K hK h1

end Group

private theorem ind_props {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) :
    Continuous ((K : Set G).indicator (1 : G → ℂ)) ∧ HasCompactSupport ((K : Set G).indicator (1 : G → ℂ)) := by
  have hcl : IsClosed (K : Set G) := K.isClosed_of_isOpen ho
  refine ⟨(IsClopen.continuous_indicator ⟨hcl, ho⟩ continuous_const), ?_⟩
  refine hc.of_isClosed_subset (isClosed_closure) ?_
  refine closure_minimal (fun x hx => ?_) hcl
  by_contra h
  exact hx (Set.indicator_of_notMem h _)

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.unitSplit :
    UpperTheory.ConvolutionTheory.L1.UnitSplit := by
  intro F E _ _ _ _ _ _ σ hσ n v hs
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 :=
    ⟨Module.finrank F E - 1, (Nat.succ_pred_eq_of_pos Module.finrank_pos).symm⟩
  obtain ⟨w₀⟩ := nonempty_placesOver E (v := v)
  obtain ⟨w, -, hw⟩ := UpperTheory.ConvolutionTheory.L1.matchProd F E σ hσ m hm n v w₀ hs
  intro _ _ _ _ mE mF hE hF h1E h1F
  have hh : ∀ u : PlacesOver E v,
      Continuous ((GLnLocal.integralGL (u.1.adicCompletion E) n : Set (GL (Fin n) (u.1.adicCompletion E))).indicator (1 : GL (Fin n) (u.1.adicCompletion E) → ℂ)) ∧
      HasCompactSupport ((GLnLocal.integralGL (u.1.adicCompletion E) n : Set (GL (Fin n) (u.1.adicCompletion E))).indicator (1 : GL (Fin n) (u.1.adicCompletion E) → ℂ)) := fun u =>
    ind_props _ (GLnLocal.isOpen_integralGL _ n) (GLnLocal.isCompact_integralGL _ n)
  have key := hw (fun u => (GLnLocal.integralGL (u.1.adicCompletion E) n : Set (GL (Fin n) (u.1.adicCompletion E))).indicator (1 : GL (Fin n) (u.1.adicCompletion E) → ℂ))
    hh mF hF h1F mE mF hE hF h1E h1F
  have e1 : GM.prodFn (n := n) (fun u : PlacesOver E v => (GLnLocal.integralGL (u.1.adicCompletion E) n : Set (GL (Fin n) (u.1.adicCompletion E))).indicator (1 : GL (Fin n) (u.1.adicCompletion E) → ℂ)) =
      (unitSet E n v).indicator 1 := by
    funext g
    rw [GM.prodFn, finprod_eq_prod_of_fintype]
    by_cases hg : g ∈ unitSet E n v
    · rw [Set.indicator_of_mem hg]
      refine Finset.prod_eq_one fun u _ => ?_
      exact Set.indicator_of_mem (hg u) _
    · rw [Set.indicator_of_notMem hg]
      obtain ⟨u, hu⟩ : ∃ u : PlacesOver E v, GM.cmp u g ∉ GLnLocal.integralGL (u.1.adicCompletion E) n := by
        by_contra h
        push_neg at h
        exact hg h
      exact Finset.prod_eq_zero (Finset.mem_univ u) (Set.indicator_of_notMem hu _)
  have e2 : cvAll mF m (fun i g => (GLnLocal.integralGL ((w i).1.adicCompletion E) n : Set (GL (Fin n) ((w i).1.adicCompletion E))).indicator (1 : GL (Fin n) ((w i).1.adicCompletion E) → ℂ)
        (mapGL n (completionMap v (w i).1) g)) =
      (GLnLocal.integralGL (v.adicCompletion F) n : Set (GL (Fin n) (v.adicCompletion F))).indicator 1 := by
    refine cvAll_unit mF _ (GLnLocal.isOpen_integralGL _ n).measurableSet h1F m _ fun i => ?_
    funext g
    have hi := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v (w i) (hs (w i)) n).2.1 g
    by_cases hg : g ∈ GLnLocal.integralGL (v.adicCompletion F) n
    · rw [Set.indicator_of_mem (show g ∈ (_ : Set _) from hg), Set.indicator_of_mem (show _ ∈ (_ : Set _) from hi.2 hg)]
      rfl
    · rw [Set.indicator_of_notMem (show g ∉ (_ : Set _) from hg), Set.indicator_of_notMem (show _ ∉ (_ : Set _) from fun h => hg (hi.1 h))]
  rw [e1, e2] at key
  exact key
end
end
