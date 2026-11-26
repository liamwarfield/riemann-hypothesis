module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open scoped Classical

namespace GlobalTheory.RestWitness

theorem exists_rest : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ R := by
  intro F _ _ κ _ v
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  let φs : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  refine ⟨r, ?_, fun φ hφ => ⟨hr, ?_⟩⟩
  · have e := congrFun (hrt (fun _ => 1)) 0
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at e
    rw [e]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have hI : (fun i : κ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
      funext i
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : AF F).1 = 0
      exact map_zero _
    have hP : (∏ᶠ w, Function.update φs v (fun _ => 1) w fun i => evFin F w ((0 : κ → AF F) i)) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun w => ?_
      by_cases hw : w = v
      · subst hw; rw [Function.update_self]
      · rw [Function.update_of_ne hw]
        simp only [φs, Pi.zero_apply, map_zero]
        rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
        rfl
    rw [hI, hP, mul_one]
    exact hf
  · rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w

end GlobalTheory.RestWitness
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ R := by
  first | exact @GlobalTheory.RestWitness.exists_rest | exact GlobalTheory.RestWitness.exists_rest | (intros; apply GlobalTheory.RestWitness.exists_rest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvUniqInf

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evFin_eq_zero_of_at (z : κ → AF F) (hz : At (evI F) z) (v : Pl (F := F)) (i : κ) : evFin F v (z i) = 0 := by
  set u : AF F := LinearMap.inr F (Ainf F) (Af F) 1 with hu
  have h0 : evI F u = 0 := by
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : Ainf F) = 0
    exact map_zero _
  have hzi : u * z i = 0 := by
    have := congrFun (hz u h0) i
    simpa using this
  have h1 : evFin F v u = 1 := by
    show evalV F v (1 : Af F) = 1
    exact map_one _
  have := congrArg (evFin F v) hzi
  rwa [map_mul, h1, one_mul, map_zero] at this

theorem rest_pure (g : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    Rest (evI F) (⇑g) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) := by
  refine ⟨fun x z hz => ?_, GlobalTheory.TensUniq.pure_mem_schA g φ hSB hstd⟩
  refine finprod_congr fun v => ?_
  congr 1
  funext i
  rw [Pi.add_apply, map_add (f := _), evFin_eq_zero_of_at z hz v i, add_zero]

theorem eq_of_pure_std (g g' : SInf F κ)
    (h : pure g (fun v => Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      pure g' (fun v => Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)) : g = g' := by
  refine SchwartzMap.ext fun y => ?_
  let x : κ → AF F := fun i => LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i))
  have hI : (fun i => evI F (x i)) = y := by
    funext i
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) = y i
    exact RingEquiv.apply_symm_apply _ _
  have hP : (∏ᶠ v, Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
      (fun i => evFin F v (x i))) = (1 : ℂ) := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    have h0 : (fun i => evFin F v (x i)) = 0 := by
      funext i
      show evalV F v (0 : Af F) = 0
      exact map_zero _
    rw [h0, Set.indicator_of_mem (by intro i; exact zero_mem _)]
    rfl
  have e := congrFun h x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure at e
  rw [hI, hP, mul_one, mul_one] at e
  exact e

end GlobalTheory.ThK.EvUniqInf


open GlobalTheory.ThK.EvUniqInf in
theorem GlobalTheory.ThK.EvUniq.infRel_of_isEv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ → ∀ (e : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → GlobalTheory.ThK.EvUniq.InfRel B M M₁ H' ei := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ _ _ _ hM _ hM₁ e hev ei ev _ hloc0 hloc

  have hex : ∀ v : Pl (F := F), ∃ p : (Fin n × Fin d → Fv F v) → ℂ, p ∈ SB _ ∧
      ev v p = Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∧
      (M₁.vac v = Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
        p = M.vac v) := by
    intro v
    by_cases h : M₁.vac v = Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    · exact ⟨M.vac v, (hM.vac v).1, by rw [← h]; exact (hloc0 v).1, fun _ => rfl⟩
    · have hmem : Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 ∈
          (SB (Fin n × Fin d → Fv F v)).map (ev v) := by
        rw [(hloc0 v).2]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
      obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.1 hmem
      exact ⟨p, hp, hpe, fun h' => absurd h' h⟩
  choose φ hφSB hφev hφvac using hex
  have hcof : ∀ᶠ v in cofinite, φ v = M.vac v := by
    filter_upwards [hM₁.std] with v hv
    exact hφvac v hv
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hcof, hM.std] with v h1 h2
    rw [h1, h2]
  have hevφ : (fun v => ev v (φ v)) =
      fun v => Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    funext hφev
  have hRest : ∀ g : SInf F (Fin n × Fin d), Rest (evI F) (⇑g) (fun x => ∏ᶠ v, φ v fun i => evFin F v (x i)) :=
    fun g => rest_pure g φ hφSB hstd
  have hRest₁ : ∀ g : SInf F (Fin n × Fin d₁), Rest (evI F) (⇑g) (fun x => ∏ᶠ v,
      Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 fun i => evFin F v (x i)) :=
    fun g => rest_pure g _ (fun v => GlobalTheory.StdVacuum.indicator_mem_SB v) (Filter.Eventually.of_forall fun _ => rfl)
  have he : ∀ g : SInf F (Fin n × Fin d), e (pure g φ) = pure (ei g) (fun v =>
      Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) := by
    intro g; rw [hloc g φ hφSB hcof, hevφ]
  refine ⟨fun z _ f f₁ hA g₁ hA₁ => ?_, fun u hu _ f f₁ hA => ?_⟩
  · have h1 := hev.Heisenberg₂ z (pure f φ) (hRest f).2
    have h2 : M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) (pure f φ) = pure f₁ φ :=
      hA _ (hRest f)
    rw [h2, he, he] at h1
    have h3 : M₁.co.rho B.ψ z (pure (ei f) (fun v =>
        Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)) = pure g₁ (fun v =>
        Set.indicator {x : Fin n × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :=
      hA₁ _ (hRest₁ (ei f))
    exact eq_of_pure_std _ _ (h1.trans h3)
  · have h1 := hev.inv u hu (pure f φ) (hRest f).2
    have h2 : M.co.rho B.ψ u (pure f φ) = pure f₁ φ := hA _ (hRest f)
    rw [h2, he, he] at h1
    exact eq_of_pure_std _ _ h1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.EvZeroInf

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def finPart (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (x : κ → AF F) : ℂ :=
  ∏ᶠ v, φ v fun i => evFin F v (x i)

theorem pure_eq_tens (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    pure f φ = tens (evI F) (⇑f) (finPart φ) := rfl

theorem snd_eq_zero_of_at (z : κ → AF F) (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  have h0 : evI F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F 0 1) = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0
    exact map_zero _
  have h := congrArg Prod.snd (congrFun (hz _ h0) i)
  change (1 : Af F) * (z i).2 = 0 at h
  rwa [one_mul] at h

theorem finPart_add (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : At (evI F) z) :
    finPart φ (x + z) = finPart φ x := by
  unfold finPart
  refine finprod_congr fun v => ?_
  congr 1
  funext i
  have h : evFin F v (z i) = 0 := by
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i).2 = 0
    rw [snd_eq_zero_of_at z hz i, map_zero]
  rw [Pi.add_apply, map_add (f := _), h, add_zero]

theorem exists_finPart_ne_zero (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ x₀ : κ → Af F, ∀ x : κ → AF F, (∀ i, (x i).2 = x₀ i) → finPart φ x ≠ 0 := by
  classical
  have hfin := Filter.eventually_cofinite.1 hstd
  set S := hfin.toFinset with hS
  have hy : ∀ v, ∃ y, φ v y ≠ 0 := fun v => by
    by_contra h
    push_neg at h
    exact h0 v (funext h)
  choose y hy using hy
  refine ⟨fun i => ∑ v ∈ S, singleFin v (y v i), fun x hx => ?_⟩
  have hev : ∀ w, (fun i => evFin F w (x i)) = if w ∈ S then y w else 0 := by
    intro w
    funext i
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (x i).2 = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx i, map_sum]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun v _ hv => evalV_singleFin_ne (Ne.symm hv) _) (fun h => absurd hw h),
        evalV_singleFin_self, if_pos hw]
    · rw [Finset.sum_eq_zero (fun v hv => evalV_singleFin_ne (fun h => hw (by rw [h]; exact hv)) _), if_neg hw]
      rfl
  have hne : ∀ w, φ w (fun i => evFin F w (x i)) ≠ 0 := by
    intro w
    by_cases hw : w ∈ S
    · rw [hev w, if_pos hw]; exact hy w
    · rw [hev w, if_neg hw]
      have hw' : φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
        by_contra h
        exact hw (by rw [hS, Set.Finite.mem_toFinset]; exact h)
      rw [hw', Set.indicator_of_mem (show (0 : κ → Fv F w) ∈ {x : κ → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} from
        fun i => zero_mem _)]
      exact one_ne_zero
  unfold finPart
  rw [finprod_def]
  split_ifs
  · exact Finset.prod_ne_zero_iff.2 fun w _ => hne w
  · exact one_ne_zero

theorem eq_of_pure_eq (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (g g' : SInf F κ) (h : pure g φ = pure g' φ) : g = g' := by
  obtain ⟨x₀, hx₀⟩ := exists_finPart_ne_zero φ h0 hstd
  refine DFunLike.ext g g' fun y => ?_
  let x : κ → AF F := fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i)) (x₀ i)
  have hI : (fun i => evI F (x i)) = y :=
    funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (y i)
  have e := congrFun h x
  change g (fun i => evI F (x i)) * finPart φ x = g' (fun i => evI F (x i)) * finPart φ x at e
  rw [hI] at e
  exact mul_right_cancel₀ (hx₀ x fun i => rfl) e

end GlobalTheory.EvZeroInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area)

namespace GlobalTheory.NormExact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E}

theorem delta_ne_zero (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : δ ≠ 0 :=
  (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.1

theorem area_pos (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : 0 < area (lamOf D cc δ) := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [GlobalTheory.MomDict.area_lamOf D cc δ h.1.1]
  have h1 : (0 : ℝ) < Ideal.absNorm cc := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h.1.1)
  have h2 := Complex.normSq_pos.2 (delta_ne_zero h)
  have h3 : (0 : ℝ) < Real.sqrt D.host.d := by linarith
  positivity

theorem xiR_pos (D : D7) : 0 < Formalism.L2.Pj.xiR D := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  rw [hxi]
  have h1 : (0 : ℝ) < Ideal.absNorm D.host.ccK := by linarith
  have h3 : (0 : ℝ) < Real.sqrt D.host.d := by linarith
  positivity

theorem normSq_scale (hc : cc ≠ ⊥) (h : IsScale D cc r) (δ : ℂ) (τ : D.what₂.Tau) :
    Complex.normSq (δ * embT D τ r) = 2 * Formalism.L2.Pj.xiR D * area (lamOf D cc δ) := by
  obtain ⟨hxi, hN, hd⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
  have hcj : embT D τ (D.host.conj r) = starRingEnd ℂ (embT D τ r) := by
    have := D.host.isCMField_hostE
    have h : NumberField.IsCMField.complexConj D.host.E r = D.host.conj r := by
      apply D.host.φ₀.injective
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    rw [← h, NumberField.IsCMField.complexEmbedding_complexConj]
  have h1 := congrArg (embT D τ) h
  rw [map_mul, map_mul, hcj, Complex.mul_conj, map_natCast, map_natCast] at h1
  have h2 : Complex.normSq (embT D τ r) * (Ideal.absNorm D.host.ccK : ℝ) = (Ideal.absNorm cc : ℝ) := by exact_mod_cast h1
  rw [GlobalTheory.MomDict.area_lamOf D cc δ hc, hxi, map_mul, ← h2]
  have h3 : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by linarith
  have h4 : Real.sqrt D.host.d ≠ 0 := by linarith
  field_simp

theorem IsScale.ne_zero (hc : cc ≠ ⊥) (h : IsScale D cc r) : r ≠ 0 := by
  rintro rfl
  have h1 : ((Ideal.absNorm cc : ℕ) : D.host.E) = 0 := by rw [← h]; simp
  exact hc (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h1))

theorem norm_period_sq (hc : cc ≠ ⊥) (h : IsScale D cc r) (δ : ℂ) (τ : D.what₂.Tau) :
    ‖period D δ r τ‖ ^ 2 = area (lamOf D cc δ) / Real.pi := by
  have hx := xiR_pos D
  have hp := Real.pi_pos
  rw [period, norm_div, div_pow, ← Complex.normSq_eq_norm_sq, normSq_scale hc h, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  field_simp

theorem Hf_scale (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) {a d : ℕ} (Z X : VC D a d) :
    Hf D (tor0 D cc δ) (fun τ i j => δ * embT D τ r * Z τ i j) (fun τ i j => δ * embT D τ r * X τ i j) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (X τ i j) := by
  have hA : ((area (lamOf D cc δ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (area_pos hc).ne'
  have hL : (tor0 D cc δ).abelian₂ = lamOf D cc δ := rfl
  rw [Hf, hL, div_eq_iff hA]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : δ * embT D τ r * starRingEnd ℂ (δ * embT D τ r) =
      2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ((area (lamOf D cc δ) : ℝ) : ℂ) := by
    rw [Complex.mul_conj, normSq_scale hc.1.1 h]; push_cast; ring
  rw [map_mul (starRingEnd ℂ) (δ * embT D τ r)]
  linear_combination (Z τ i j * starRingEnd ℂ (X τ i j)) * h1

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem reads_iff (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) (h : IsScale D cc r) (G : VC D S.rank T.rank → ℂ) (f : WO S T → ℂ) :
    Reads ψ θ rfl rfl cc δ r G f ↔ IsThetaFunO ψ S T f ∧ ∀ w : WO S T, w.map (finPart D) = 0 →
      f w = GlobalTheory.FockPos.gaussO θ 1 1 w *
        (fun Z : VC D S.rank T.rank => G fun τ i j => δ * embT D τ r * Z τ i j) (GlobalTheory.FockPos.zCo θ 1 1 w) := by
  have hz : ∀ w : WO S T, GlobalTheory.FockPos.zCo θ 1 1 w = fun τ => compAt θ τ w := fun w => by
    funext τ
    have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
      Matrix.map_one _ (map_zero _) (map_one _)
    simp only [GlobalTheory.FockPos.zCo, e, inv_one, Matrix.one_mul, Matrix.mul_one]
    rfl
  refine and_congr_right fun _ => forall₂_congr fun w _ => ?_
  have e1 : coordY θ rfl rfl δ r w = fun τ i j => δ * embT D τ r * compAt θ τ w i j := rfl
  have e2 := Hf_scale hc h (fun τ i j => compAt θ τ w i j) (fun τ i j => compAt θ τ w i j)
  rw [e1, e2, GlobalTheory.FockPos.gaussO, hz]
  simp only [Complex.mul_conj']
  congr! 3
  push_cast
  ring

variable {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d} {G : VC D a d → ℂ} {f f' : WO S T → ℂ}

theorem Reads.smul (h : Reads ψ θ hS hT cc δ r G f) (c : ℂ) : Reads ψ θ hS hT cc δ r (c • G) (c • f) :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).smul_mem c h.1, fun w hw => by
    rw [Pi.smul_apply, Pi.smul_apply, h.2 w hw, smul_eq_mul, smul_eq_mul]; ring⟩

theorem Reads.add {G' : VC D a d → ℂ} (h : Reads ψ θ hS hT cc δ r G f) (h' : Reads ψ θ hS hT cc δ r G' f') :
    Reads ψ θ hS hT cc δ r (G + G') (f + f') :=
  ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).add_mem h.1 h'.1, fun w hw => by
    rw [Pi.add_apply, Pi.add_apply, h.2 w hw, h'.2 w hw]; ring⟩

theorem Reads.unique (h : Reads ψ θ hS hT cc δ r G f) (h' : Reads ψ θ hS hT cc δ r G f') : f = f' :=
  sub_eq_zero.1 (GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real ((GlobalTheory.FinWeilO.thetaSub ψ S T).sub_mem h.1 h'.1)
    fun w hw => by rw [Pi.sub_apply, h.2 w hw, h'.2 w hw, sub_self])

end GlobalTheory.NormExact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

namespace GlobalTheory.SchrKeepsSchA

theorem schr_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (p : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ p Φ ∈ schA F κ := by
  intro F _ _ ψ hψ κ _ p Φ hΦ
  exact GlobalTheory.HeisSchA.schr_mem_schA ψ hψ p Φ hΦ

end GlobalTheory.SchrKeepsSchA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartzStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedinger_preserves_adelic_schwartz : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (p : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ p Φ ∈ schA F κ := by
  first | exact @GlobalTheory.SchrKeepsSchA.schr_mem_schA | exact GlobalTheory.SchrKeepsSchA.schr_mem_schA | (intros; apply GlobalTheory.SchrKeepsSchA.schr_mem_schA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SplitAdeleTrace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_one_mul_comp (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]


omit [NumberField F] [NumberField E] in
theorem trace_baseChange_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem add_conj_eq_trace {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) :
    x + σ x = algebraMap F E (Algebra.trace F E x) := by
  classical
  have hc := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (by ext y; simp [GlobalTheory.AdelicU.cm_conj_conj h])
    (by ext y; simp [GlobalTheory.AdelicU.cm_conj_conj h])
  have hs : (1 : E ≃ₐ[F] E) ≠ s := by
    intro h1
    obtain ⟨y, hy⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne h
    exact hy (DFunLike.congr_fun h1 y).symm
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hs, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h.2.2.1]
  rw [trace_eq_sum_automorphisms, hu, Finset.sum_pair hs]
  rfl

theorem trace_at_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (τ : E →ₐ[F] Fv F v)
    (z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z →
    Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z =
      GlobalTheory.LatVac.liftV v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ z + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) z) := by
  intro F E _ _ _ _ _ σ hcm v τ z hz
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  set l : AF F := GlobalTheory.LatVac.liftV v 1 with hl
  have hz1 : z = l • z := by
    have h0 := hz (1 - l) (by rw [map_sub, map_one, hl, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h0
    exact h0
  have hpiW : ∀ (t : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (l • w) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t w := by
    intro t w
    rw [Algebra.smul_def, map_mul]
    have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (algebraMap (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) l) = 1 := by
      change evFin F v l * t 1 = 1
      rw [hl, GlobalTheory.LatVac.evFin_liftV, map_one, one_mul]
    rw [this, one_mul]
  have key : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (l • w) =
      GlobalTheory.LatVac.liftV v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ w + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, ← map_add (f := _)]; congr 1; simp only [map_add (f := _)]; ring
    | tmul b e =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, trace_baseChange_tmul, mul_assoc, liftV_one_mul_comp, map_mul,
        AlgHom.commutes]
      congr 1
      change evFin F v b * algebraMap F (Fv F v) (Algebra.trace F E e) = evFin F v b * τ e + evFin F v b * τ (σ e)
      rw [← mul_add, ← map_add (f := _), add_conj_eq_trace hcm, AlgHom.commutes]
  rw [hz1, key, hpiW, hpiW]

end GlobalTheory.SplitAdeleTrace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicTrace_supportedAtSplitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z = GlobalTheory.LatVac.liftV v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ z + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) z) := by
  first | exact @GlobalTheory.SplitAdeleTrace.trace_at_split | exact GlobalTheory.SplitAdeleTrace.trace_at_split | (intros; apply GlobalTheory.SplitAdeleTrace.trace_at_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
open NumberField MeasureTheory

namespace GlobalTheory.WeilM

theorem schA_memLp_two : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
    ∀ μ : MeasureTheory.Measure (κ → AdeleRing (𝓞 F) F), μ.IsAddHaarMeasure →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, MeasureTheory.MemLp Φ 2 μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  intro μ hμ Φ hΦ
  obtain ⟨n, g, f, hg, rfl⟩ := GlobalTheory.ThetaSobolevBase.exists_sumPure hΦ
  classical
  unfold GlobalTheory.ThetaSobolevBase.sumPure
  have hs : ∀ s : Finset (Fin n), MemLp (∑ i ∈ s, GlobalTheory.WeilM.pureA F (f i) (g i)) 2 μ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simpa [Finset.sum_insert, hi] using
        (GlobalTheory.ThetaSobolevBase.memLp_pureA μ hμ (f i) (hg i)).add ih
  simpa using hs Finset.univ

end GlobalTheory.WeilM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2Statement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_mem_L2 : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
    ∀ μ : MeasureTheory.Measure (κ → AdeleRing (𝓞 F) F), μ.IsAddHaarMeasure →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, MeasureTheory.MemLp Φ 2 μ := by
  first | exact @GlobalTheory.WeilM.schA_memLp_two | exact GlobalTheory.WeilM.schA_memLp_two | (intros; apply GlobalTheory.WeilM.schA_memLp_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.SplitComps

open GlobalTheory.EmbChart (atPlace tensAt compFin_tensAt tensAt_mul_right)

theorem exists_mat_comps : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (τ : E →ₐ[F] Fv F v) {m n : Type} (P₀ P₁ : Matrix m n (Fv F v)), ∃ u : Matrix m n (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) u ∧ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = P₀ ∧ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = P₁ := by
  intro F E _ _ _ _ _ σ h v τ m n P₀ P₁
  refine ⟨Matrix.of fun i j => tensAt E v ((splitAlgEquiv h τ).symm (P₀ i j, P₁ i j)), ?_, ?_, ?_⟩
  · intro a ha
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
    have : compFin F E v (algebraMap (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = 0 := by
      change evFin F v a ⊗ₜ[F] (1 : E) = 0
      rw [ha, TensorProduct.zero_tmul]
    rw [this, mul_zero, map_zero]
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.of_apply]
    change splitProj τ (compFin F E v (tensAt E v _)) = _
    rw [compFin_tensAt, splitProj_symm]
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.of_apply]
    change splitProj (τ.comp σ) (compFin F E v (tensAt E v _)) = _
    rw [compFin_tensAt, splitProj_comp_symm]

end GlobalTheory.SplitComps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (τ : E →ₐ[F] Fv F v) {m n : Type} (P₀ P₁ : Matrix m n (Fv F v)), ∃ u : Matrix m n (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) u ∧ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = P₀ ∧ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = P₁ := by
  first | exact @GlobalTheory.SplitComps.exists_mat_comps | exact GlobalTheory.SplitComps.exists_mat_comps | (intros; apply GlobalTheory.SplitComps.exists_mat_comps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorNeZero
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VecNe

theorem thPVec_ne_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)}
    {ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hr : T.rank ≤ S.rank) (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) : f ≠ 0 := by
  obtain ⟨hv, e, he, ⟨Tm, hTm⟩, hall⟩ := h
  have h0 : f₀ ≠ 0 := by
    rintro rfl
    obtain ⟨⟨p, hp⟩, h2⟩ := hv.2.norm
    have := h2 p hp
    simp [nrm2] at this
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hinf := ho.conj.infPart_eq
  rw [hall Tm hTm]
  obtain ⟨x, h1, h2, h3⟩ := GlobalTheory.AdjDatumNe.exists_datum_ne_zero D S T βS βT Pg Q _ ξ e hr he
    (fun PP h => Finset.mem_union_left _ h) fun PP h => Finset.mem_union_right _ h
  refine GlobalTheory.PlaceModelInj.placeModel_ne_zero D ψ S T ΛS ΛT _ f₀ _ Tm hv.1 hS hT ho.conj.idem
    (by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, he.2]) hinf hTm h0
    (GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS)
      (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT) hinf (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)
      (GlobalTheory.PlaceVec.frMapAdj_up S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_down S T βS βT) (Pg ∪ Q)
      (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
        rw [GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)])
    fun hz => h3 ?_
  have := congrFun hz x
  rwa [if_pos ⟨h1, h2⟩] at this

end GlobalTheory.AdTh.VecNe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminorm
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AbsThetaSemi

variable {D : D7}

theorem continuous_coord {d m n : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    Continuous (coord (D := D) (m := m) (n := n) ε) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  refine continuous_pi fun p => ?_
  let L : AE D →ₗ[AF D.host.F] AF D.host.F :=
    (Finsupp.lapply p.2.2).comp (Algebra.TensorProduct.basis (AF D.host.F) ε).repr.toLinearMap
  exact (IsModuleTopology.continuous_of_linearMap L).comp
    ((continuous_apply p.2.1).comp (continuous_apply p.1))

theorem continuous_invPt (B : HSp D) {a : ℕ} (ξ : Matrix (Fin B.rank) (Fin a) D.host.E) :
    Continuous fun h : GA D B => invPt B h ξ := by
  unfold invPt
  have hmt : Continuous (Formalism.L2.Theta.mt B) := Units.continuous_val.comp continuous_subtype_val
  exact (hmt.comp continuous_inv).matrix_mul continuous_const

theorem measurable_absTheta (B : HSp D) {a : ℕ} {φ : Mx D B.rank a → ℂ} (hφ : Continuous φ) :
    Measurable (absTheta B φ) := by
  haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  haveI : Countable (Matrix (Fin B.rank) (Fin a) D.host.E) := inferInstanceAs (Countable (Fin B.rank → Fin a → D.host.E))
  exact Measurable.tsum fun ξ => (hφ.comp (continuous_invPt B ξ)).enorm.measurable

theorem measurable_descend_absTheta (B : HSp D) {a : ℕ} {φ : Mx D B.rank a → ℂ} (hφ : Continuous φ) :
    Measurable (descend (GQ B) (absTheta B φ)) :=
  measurable_from_quotient.2 (by
    rw [show descend (GQ B) (absTheta B φ) ∘ Quotient.mk'' = absTheta B φ from (leftInv_absTheta B φ).lift_descend]
    exact measurable_absTheta B hφ)

theorem absTheta_add_le (B : HSp D) {a : ℕ} (φ ψ : Mx D B.rank a → ℂ) (h : GA D B) :
    absTheta B (φ + ψ) h ≤ absTheta B φ h + absTheta B ψ h := by
  unfold absTheta
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun ξ => enorm_add_le _ _

theorem absTheta_smul (B : HSp D) {a : ℕ} (c : ℂ) (φ : Mx D B.rank a → ℂ) (h : GA D B) :
    absTheta B (c • φ) h = ‖c‖ₑ * absTheta B φ h := by
  unfold absTheta
  rw [← ENNReal.tsum_mul_left]
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul]

theorem absThetaInt_add_le (B : HSp D) (m : Measure (GA D B)) {a : ℕ} {φ : Mx D B.rank a → ℂ} (hφ : Continuous φ)
    (ψ : Mx D B.rank a → ℂ) : absThetaInt B m (φ + ψ) ≤ absThetaInt B m φ + absThetaInt B m ψ := by
  unfold absThetaInt
  rw [← lintegral_add_left (measurable_descend_absTheta B hφ)]
  exact lintegral_mono fun q => absTheta_add_le B φ ψ q.out

theorem absThetaInt_smul (B : HSp D) (m : Measure (GA D B)) {a : ℕ} (c : ℂ) (φ : Mx D B.rank a → ℂ) :
    absThetaInt B m (c • φ) = ‖c‖ₑ * absThetaInt B m φ := by
  unfold absThetaInt
  rw [← lintegral_const_mul' _ _ enorm_ne_top]
  exact lintegral_congr fun q => absTheta_smul B c φ q.out

theorem absTheta_le_liminf (B : HSp D) {a : ℕ} {ι : Type*} {u : Filter ι} [u.NeBot] {φs : ι → Mx D B.rank a → ℂ}
    {φ : Mx D B.rank a → ℂ} (hlim : ∀ x, Filter.Tendsto (fun i => φs i x) u (nhds (φ x))) (h : GA D B) :
    absTheta B φ h ≤ Filter.liminf (fun i => absTheta B (φs i) h) u := by
  unfold absTheta
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have ht : Filter.Tendsto (fun i => ∑ ξ ∈ s, ‖φs i (invPt B h ξ)‖ₑ) u (nhds (∑ ξ ∈ s, ‖φ (invPt B h ξ)‖ₑ)) :=
    tendsto_finsetSum s fun ξ _ => (hlim _).enorm
  rw [← ht.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i => ENNReal.sum_le_tsum s)

theorem absThetaInt_le_liminf (B : HSp D) (m : Measure (GA D B)) {a : ℕ} {ι : Type*} {u : Filter ι} [u.NeBot]
    [u.IsCountablyGenerated] {φs : ι → Mx D B.rank a → ℂ} (hc : ∀ i, Continuous (φs i))
    {φ : Mx D B.rank a → ℂ} (hlim : ∀ x, Filter.Tendsto (fun i => φs i x) u (nhds (φ x))) :
    absThetaInt B m φ ≤ Filter.liminf (fun i => absThetaInt B m (φs i)) u := by
  unfold absThetaInt
  refine le_trans (lintegral_mono fun q => absTheta_le_liminf B hlim q.out) ?_
  exact lintegral_liminf_le fun i => measurable_descend_absTheta B (hc i)

end GlobalTheory.AbsThetaSemi

namespace GlobalTheory.AbsThetaSemi

private theorem repr_map_local {D : D7} {R : Type} [CommRing R] [Algebra D.host.F R] (π : AF D.host.F →ₐ[D.host.F] R) {d : ℕ}
    (ε : Module.Basis (Fin d) D.host.F D.host.E) (z : AE D) (k : Fin d) :
    π ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr z k) =
      (Algebra.TensorProduct.basis R ε).repr (Algebra.TensorProduct.map π (AlgHom.id D.host.F D.host.E) z) k := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul, Finsupp.mapRange_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

private def finCoord_local {D : D7} {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (Fin m × Fin n × Fin d → Af D.host.F) := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  let b := Algebra.TensorProduct.basis (Af D.host.F) ε
  exact
  { toFun := fun y p => b.equivFun (y p.1 p.2.1) p.2.2
    invFun := fun c i j => b.equivFun.symm fun k => c (i, j, k)
    left_inv := fun y => by
      funext i j
      simp only
      conv_rhs => rw [← b.equivFun.symm_apply_apply (y i j)]
    right_inv := fun c => by
      funext p
      simp only [LinearEquiv.apply_symm_apply]
    continuous_toFun := continuous_pi fun p =>
      ((continuous_apply p.2.2).comp (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)).comp
        ((continuous_apply p.2.1).comp (continuous_apply p.1))
    continuous_invFun := continuous_pi fun i => continuous_pi fun j =>
      (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap).comp
        (continuous_pi fun k => continuous_apply (i, j, k)) }

private theorem continuous_mixed_local (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
      fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [this]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

private def realCoord_local {D : D7} (σ : (D.what₂.Tau → ℂ) →+ AE D) {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    (D.what₂.Tau → Fin m → Fin n → ℂ) →+ (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F) where
  toFun c p := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
    (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => c τ p.1 p.2.1) p.2.2))
  map_zero' := by
    funext p
    have : (σ fun τ => (0 : D.what₂.Tau → Fin m → Fin n → ℂ) τ p.1 p.2.1) = 0 := σ.map_zero
    show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (fstA D.host.F
      ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => (0 : D.what₂.Tau → Fin m → Fin n → ℂ) τ p.1 p.2.1)
        p.2.2)) = 0
    rw [this, map_zero, Finsupp.zero_apply, map_zero, map_zero]
  map_add' c c' := by
    funext p
    have : (σ fun τ => (c + c') τ p.1 p.2.1) = σ (fun τ => c τ p.1 p.2.1) + σ (fun τ => c' τ p.1 p.2.1) :=
      σ.map_add _ _
    show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (fstA D.host.F
      ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => (c + c') τ p.1 p.2.1) p.2.2)) = _
    rw [this, map_add (f := _), Finsupp.add_apply, map_add (f := _), map_add (f := _)]
    rfl

private theorem mem_schwartzA_comp_coord_local (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (m n d : ℕ)
    (ε : Module.Basis (Fin d) D.host.F D.host.E) (φ : WeilM.schA D.host.F (Fin m × Fin n × Fin d)) :
    φ.1 ∘ coord ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ m n := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, -, hsf, hsi⟩ := GlobalTheory.SchwartzBruhatTensor.exists_finSection D
  have hcont : Continuous (realCoord_local σ (m := m) (n := n) ε) := by
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    refine continuous_pi fun p => (continuous_mixed_local D.host.F).comp (continuous_fst.comp ?_)
    exact ((continuous_apply p.2.2).comp (IsModuleTopology.continuous_of_linearMap
        (Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.toLinearMap)).comp
      (hσ.cont.comp (continuous_pi fun τ => (continuous_apply p.2.1).comp ((continuous_apply p.1).comp (continuous_apply τ))))
  obtain ⟨M, hM⟩ : ∃ M : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F),
      ⇑M = ⇑(realCoord_local σ ε) := ⟨(realCoord_local σ ε).toRealLinearMap hcont, rfl⟩
  have hMi : Function.Injective M.toLinearMap := by
    intro a b h
    have h' : M a = M b := h
    rw [hM] at h'
    have hinj : Function.Injective (realCoord_local σ (m := m) (n := n) ε) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro c hc
      funext τ i j
      have h0 : infPart D (σ fun τ => c τ i j) = 0 := by
        apply (Algebra.TensorProduct.basis (Ainf D.host.F) ε).repr.injective
        ext k
        rw [map_zero, Finsupp.zero_apply]
        have e : InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
            (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => c τ i j) k)) = 0 :=
          congrFun hc (i, j, k)
        have e2 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective).1 e
        rw [← e2, repr_map_local (fstA D.host.F) ε]
        rfl
      have h1 := hσ.comp (fun τ => c τ i j) τ
      rw [h0, map_zero] at h1
      exact h1.symm
    exact hinj h'
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz _).1 hMi
  have hbound : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖M x‖) ^ k := ⟨1, K, fun x => by
    have h := hK.le_mul_dist x 0
    rw [dist_zero_right, map_zero, dist_zero_right] at h
    have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
    calc ‖x‖ ≤ K * ‖M x‖ := h
      _ ≤ K * (1 + ‖M x‖) ^ 1 := by rw [pow_one]; exact mul_le_mul_of_nonneg_left (by linarith) hK0⟩
  obtain ⟨φ, hφ⟩ := φ
  induction hφ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let f' : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ := SchwartzMap.compCLM ℂ M.hasTemperateGrowth hbound f
    have hf' : ∀ c, f' c = f (M c) := fun c => rfl
    let g' : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := g ∘ finCoord_local ε
    have hg' : g' ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
      ⟨hg.1.comp_continuous (finCoord_local ε).continuous, hg.2.comp_homeomorph _⟩
    have heq : WeilM.pureA D.host.F f g ∘ coord ε =
        fun x => f' (fun τ i j => compAt θ τ x i j) * g' (fun i j => finPart D (x i j)) := by
      funext x
      rw [hf']
      have hrc : (fun p => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (coord ε x p).1) =
          realCoord_local σ ε (fun τ i j => compAt θ τ x i j) := by
        funext p
        have hx : x p.1 p.2.1 = s (finPart D (x p.1 p.2.1)) + σ (fun τ => compAt θ τ x p.1 p.2.1) :=
          congrFun (congrFun (GlobalTheory.SchwartzBruhatTensor.decomp hσ hsf hsi x) p.1) p.2.1
        have h0 : fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (s (finPart D (x p.1 p.2.1))) p.2.2) = 0 :=
          (repr_map_local (fstA D.host.F) ε _ _).trans (by change (Algebra.TensorProduct.basis (Ainf D.host.F) ε).repr (infPart D (s (finPart D (x p.1 p.2.1)))) p.2.2 = 0; rw [hsi, map_zero, Finsupp.zero_apply])
        show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
            (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (x p.1 p.2.1) p.2.2)) =
          InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F
            (fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (σ fun τ => compAt θ τ x p.1 p.2.1) p.2.2))
        conv_lhs => rw [hx]
        rw [map_add (f := _), Finsupp.add_apply, map_add (fstA D.host.F), h0, zero_add]
      have hfc : (fun p => (coord ε x p).2) = finCoord_local ε (fun i j => finPart D (x i j)) := by
        funext p
        change sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) ε).repr (x p.1 p.2.1) p.2.2) =
          (Algebra.TensorProduct.basis (Af D.host.F) ε).repr (finPart D (x p.1 p.2.1)) p.2.2
        exact repr_map_local (sndA D.host.F) ε (x p.1 p.2.1) p.2.2
      show f (fun p => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (coord ε x p).1) * g (fun p => (coord ε x p).2) =
        f (M (fun τ i j => compAt θ τ x i j)) * g (finCoord_local ε (fun i j => finPart D (x i j)))
      rw [hrc, hfc, ← hM]
    rw [heq]
    exact Submodule.subset_span ⟨f', g', hg', rfl⟩
  | zero =>
    have e : (0 : (Fin m × Fin n × Fin d → AdeleRing (𝓞 D.host.F) D.host.F) → ℂ) ∘ coord ε = 0 := rfl
    rw [e]
    exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    have e : (Φ + Ψ) ∘ coord ε = Φ ∘ coord ε + Ψ ∘ coord ε := rfl
    rw [e]
    exact Submodule.add_mem _ h1 h2
  | smul a Φ _ h =>
    have e : (a • Φ) ∘ coord ε = a • (Φ ∘ coord ε) := rfl
    rw [e]
    exact Submodule.smul_mem _ a h

theorem absThetaInt_le_contSeminorm : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E), ∃ ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)), IsContSeminorm ν ∧ ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) := by
  intro hP D A B m hm hA hw d ε
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hcont : ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), Continuous (φ.1 ∘ coord ε) :=
    fun φ => (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA D.host.F φ.2).comp (continuous_coord ε)
  have hfin : ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), absThetaInt B m (φ.1 ∘ coord ε) ≠ ⊤ :=
    fun φ => (hP D A.rank B hA hw θ hθ m hm ⟨_, mem_schwartzA_comp_coord_local D θ hθ B.rank A.rank d ε φ⟩).ne
  let ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)) :=
    Seminorm.of (fun φ => (absThetaInt B m (φ.1 ∘ coord ε)).toReal)
      (fun φ ψ => by
        rw [← ENNReal.toReal_add (hfin φ) (hfin ψ)]
        exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin φ, hfin ψ⟩) (absThetaInt_add_le B m (hcont φ) _))
      (fun c φ => by
        show (absThetaInt B m (c • (φ.1 ∘ coord ε))).toReal = _
        rw [absThetaInt_smul, ENNReal.toReal_mul, toReal_enorm])
  refine ⟨ν, fun g => ?_, fun φ => (ENNReal.ofReal_toReal (hfin φ)).ge⟩
  let L : SchwartzMap (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ →ₗ[ℂ]
      WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d) :=
    { toFun := pureS g
      map_add' := fun f f' => Subtype.ext (funext fun x => by simp [pureS, WeilM.pureA, add_mul])
      map_smul' := fun c f => Subtype.ext (funext fun x => by simp [pureS, WeilM.pureA, mul_assoc]) }
  haveI := GlobalTheory.schwartzMap_barrelledSpace (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F)
  have hev : ∀ y, Continuous fun f : SchwartzMap (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ => f y :=
    fun y => ((continuous_eval_const y : Continuous fun F : BoundedContinuousFunction (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ => F y)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ).continuous
  have hN : LowerSemicontinuous fun f => absThetaInt B m ((pureS g f).1 ∘ coord ε) := by
    rw [lowerSemicontinuous_iff_le_liminf]
    intro f
    exact absThetaInt_le_liminf B m (fun f' => hcont (pureS g f')) fun x => ((hev _).tendsto f).mul_const _
  refine Seminorm.continuous_of_lowerSemicontinuous (ν.comp L) fun f y hy => ?_
  by_cases hy0 : y < 0
  · exact Filter.Eventually.of_forall fun f' => hy0.trans_le ENNReal.toReal_nonneg
  · push_neg at hy0
    have h1 : ENNReal.ofReal y < absThetaInt B m ((pureS g f).1 ∘ coord ε) :=
      (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).2 hy
    filter_upwards [hN f _ h1] with f' hf'
    exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).1 hf'

end GlobalTheory.AbsThetaSemi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminormStatement
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absoluteThetaIntegral_le_continuousSeminorm : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E), ∃ ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)), IsContSeminorm ν ∧ ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) := by
  first | exact @GlobalTheory.AbsThetaSemi.absThetaInt_le_contSeminorm | exact GlobalTheory.AbsThetaSemi.absThetaInt_le_contSeminorm | (intros; apply GlobalTheory.AbsThetaSemi.absThetaInt_le_contSeminorm <;> assumption)
end
end
