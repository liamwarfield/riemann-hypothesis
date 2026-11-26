module

public import Development.WeilBound.NonsplitUniqueness.Places
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactorAlt

@[expose] public section
attribute [local instance 10000] DivisionSemiring.to_moduleIsTorsionFree Module.Free.of_divisionRing

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
theorem UpperTheory.ConvolutionTheory.T.places :
    UpperTheory.ConvolutionTheory.T.Places := PositivityTheory.tft.places_holds
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStableAlt
open NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1

private theorem cmp_continuous {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} {v : Pl F} (u : PlacesOver E v) :
    Continuous (GM.cmp (n := n) u : GL (Fin n) (CompletionsOver E v) → GL (Fin n) (u.1.adicCompletion E)) :=
  Units.continuous_iff.2
    ⟨Units.continuous_val.matrix_map (continuous_apply u),
      Units.continuous_coe_inv.matrix_map (continuous_apply u)⟩

theorem UpperTheory.ConvolutionTheory.T.splitStable :
    UpperTheory.ConvolutionTheory.T.SplitStable := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v hs U J hJ
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 :=
    ⟨Module.finrank F E - 1, (Nat.succ_pred_eq_of_pos Module.finrank_pos).symm⟩
  obtain ⟨w₀⟩ := nonempty_placesOver E (v := v)
  haveI : Nonempty (PlacesOver E v) := ⟨w₀⟩
  haveI : Nonempty (HeightOneSpectrum (𝓞 E)) := ⟨w₀.1⟩
  obtain ⟨D, w, -, hw⟩ := UpperTheory.ConvolutionTheory.L1.finSplit F E σ hσ m hm v w₀ hs
  have hc : ∀ (x : GL (Fin n) (CompletionsOver E v)) (i : Fin (m + 1)),
      GM.cmp (w i) x = mapGL n (completionMap v (w i).1) (D.comp n i x) := fun x i =>
    Units.ext (Matrix.ext fun a b => (hw _ i).symm)
  have hshift : ∀ (x : GL (Fin n) (CompletionsOver E v)) (i : Fin (m + 1)),
      D.comp n i (mapGL n (galFin σ v) x) = D.comp n (i + 1) x := fun x i =>
    Units.ext (Matrix.ext fun a b => D.map_shift _ i)
  refine ⟨fun x hx u => ?_, fun hCO hle => ?_⟩
  · obtain ⟨i, rfl⟩ := w.surjective u
    rw [hc]
    refine (hJ (w i) _).1 ?_
    rw [hshift, hJ (w (i + 1)), ← hc]
    exact hx _
  · have hJo : ∀ u, IsOpen (J u : Set (GL (Fin n) (u.1.adicCompletion E))) := fun u => by
      obtain ⟨e, he⟩ := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hs u) n).1
      have h : (J u : Set (GL (Fin n) (u.1.adicCompletion E))) = e.symm ⁻¹' (U : Set (GL (Fin n) (v.adicCompletion F))) := by
        ext y
        have h1 := hJ u (e.symm y)
        rw [← he, e.apply_symm_apply] at h1
        exact h1.symm
      rw [h]
      exact hCO.2.preimage e.symm.continuous
    refine ⟨⨅ u, (J u).comap (GM.cmp u), fun g => by simp [Subgroup.mem_iInf], ?_, ?_⟩
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun u => (hJo u).preimage (cmp_continuous u)
    · intro g hg u
      have hgu : GM.cmp u g ∈ J u := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hg u)
      obtain ⟨e, he⟩ := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hs u) n).1
      have h2 : e.symm (GM.cmp u g) ∈ U := by
        rw [hJ u, ← he, e.apply_symm_apply]
        exact hgu
      have h3 := (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hs u) n).2.1 _ |>.2 (hle h2)
      rw [← he, e.apply_symm_apply] at h3
      exact h3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitLev
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

private theorem mem_fixL' {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (Gw n w)) (x : LL μ) (h : ∀ g ∈ J, rhoL μ w g x = x) : x ∈ fixL μ w J := by
  simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus]
  rintro _ ⟨g, hg, rfl⟩
  exact h g hg

private theorem exists_fixed {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (w : Pl K) :
    ∃ (S : Subgroup (Gw n w)) (x : LL μ), IsOpen (S : Set (Gw n w)) ∧ x ∈ V ∧ x ≠ 0 ∧ ∀ g ∈ S, rhoL μ w g x = x := by
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  obtain ⟨⟨σ, f, hf0, hfV, hfe⟩, -, -⟩ := UpperTheory.ConvolutionTheory.C.occursBasics K n μ V w (Measure.haar) hV
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf0 (LinearMap.ext hc)
  refine ⟨{ carrier := {g | σ.ρ g x = x}
            mul_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq] at ha hb ⊢
              rw [map_mul, Module.End.mul_apply, hb, ha]
            one_mem' := by simp
            inv_mem' := fun {a} ha => by
              simp only [Set.mem_setOf_eq] at ha ⊢
              conv_lhs => rw [← ha]
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] },
    f x, σ.smooth x, hfV x, hx, fun g hg => ?_⟩
  rw [← hfe g x]
  exact congrArg f hg

theorem splitLev : SplitLev := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ V hV v hv
  haveI : Nonempty (PlacesOver E v) := nonempty_placesOver E (v := v)
  haveI : Nonempty (HeightOneSpectrum (𝓞 E)) := ⟨(Classical.arbitrary (PlacesOver E v)).1⟩
  choose S x hSo hxV hx0 hxS using fun u : PlacesOver E v => exists_fixed μ V hV u.1
  have hsp := fun u : PlacesOver E v => (UpperTheory.ConvolutionTheory.L1.splitLoc F E v u (hv u) n).1
  choose e he using hsp
  let U : Subgroup (Gw n v) := GLnLocal.integralGL (v.adicCompletion F) n ⊓
    ⨅ u : PlacesOver E v, (S u).comap (mapGL n (completionMap v u.1))
  have hUo : IsOpen (U : Set (Gw n v)) := by
    have h2 : IsOpen (⋂ u : PlacesOver E v, (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1))) := by
      refine isOpen_iInter_of_finite fun u => ?_
      have : (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1)) = (e u) ⁻¹' (S u : Set (Gw n u.1)) := by
        ext g; simp only [Set.mem_preimage, he]
      rw [this]
      exact (hSo u).preimage (e u).continuous
    have h3 : (U : Set (Gw n v)) = (GLnLocal.integralGL (v.adicCompletion F) n : Set (Gw n v)) ∩
        ⋂ u : PlacesOver E v, (mapGL n (completionMap v u.1)) ⁻¹' (S u : Set (Gw n u.1)) := by
      ext g
      simp [U, Subgroup.mem_inf, Subgroup.mem_iInf]
    rw [h3]
    exact (GLnLocal.isOpen_integralGL _ n).inter h2
  have hUle : U ≤ GLnLocal.integralGL (v.adicCompletion F) n := inf_le_left
  have hUc : IsCompact (U : Set (Gw n v)) :=
    (GLnLocal.isCompact_integralGL _ n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo) hUle
  have hinj : ∀ u : PlacesOver E v, Function.Injective (mapGL n (completionMap v u.1)) := fun u a b h =>
    (e u).injective (by rw [he, he, h])
  refine ⟨U, fun u => U.map (mapGL n (completionMap v u.1)), ⟨hUc, hUo⟩, hUle, fun u => ?_⟩
  have himg : ((U.map (mapGL n (completionMap v u.1)) : Subgroup (Gw n u.1)) : Set (Gw n u.1)) = (e u) '' (U : Set (Gw n v)) := by
    ext y
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, he]
  refine ⟨⟨?_, ?_⟩, fun g => ?_, ?_⟩
  · rw [himg]
    exact hUc.image (e u).continuous
  · rw [himg]
    exact (e u).toHomeomorph.isOpenMap _ hUo
  · exact (Subgroup.mem_map_iff_mem (hinj u)).symm
  · intro hbot
    have hmem : x u ∈ V ⊓ fixL μ u.1 (U.map (mapGL n (completionMap v u.1))) := by
      refine ⟨hxV u, mem_fixL' μ u.1 _ _ ?_⟩
      rintro _ ⟨g, hg, rfl⟩
      exact hxS u _ ((Subgroup.mem_iInf.1 hg.2) u)
    rw [hbot, Submodule.mem_bot] at hmem
    exact hx0 u hmem

end UpperTheory.ConvolutionTheory.T
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.OffStable
open NumberField IsDedekindDomain ValuativeRel
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.T

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem val_gal (v : HeightOneSpectrum (𝓞 F)) (σ : E ≃ₐ[F] E) (w u : HeightOneSpectrum (𝓞 E))
    [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver v.asIdeal] (h : u = σ • w) (y : w.adicCompletion E) :
    Valued.v (galEquiv v σ w u h y) = Valued.v y := by
  have hK : ∀ x : E, Valued.v (galEquiv v σ w u h (algebraMap E (w.adicCompletion E) x)) =
      Valued.v (algebraMap E (w.adicCompletion E) x) := by
    intro x
    have hx := valuation_smul σ w x
    rw [← h] at hx
    rw [galEquiv_algebraMap, HeightOneSpectrum.algebraMap_adicCompletion,
      HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa using hx
  have hclosed : IsClosed {y : w.adicCompletion E | Valued.v (galEquiv v σ w u h y) = Valued.v y} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y0 hy0
    have h0 : y0 ≠ 0 := by
      rintro rfl
      simp at hy0
    have h1 : Valued.v y0 ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : Valued.v (galEquiv v σ w u h y0) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero _).2 h0)
    filter_upwards [Valued.locally_const h1,
      (continuous_galEquiv v σ w u h).continuousAt.preimage_mem_nhds (Valued.locally_const h2)]
      with y hy hy'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff] at hy hy' hy0 ⊢
    rwa [hy, hy']
  exact (HeightOneSpectrum.denseRange_algebraMap E w).induction_on y hclosed hK

private theorem galFin_apply (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (y : CompletionsOver E v)
    (u : PlacesOver E v) :
    galFin σ v y u = galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u) (y (σ⁻¹ • u)) := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  have h1 : galFin σ v (tensorEquiv' E v t) =
      tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F (v.adicCompletion F)) t) := by
    simp [galFin, galOf]
  rw [h1]
  clear h1
  induction t with
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]
  | tmul x a =>
    rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, Pi.mul_apply, Pi.mul_apply, map_mul]
    congr 1
    · exact (galEquiv_algebraMap v σ _ _ _ x).symm
    · exact ((galEquiv v σ _ _ (eq_smul_inv_smul v σ u)).commutes a).symm

variable {w u : HeightOneSpectrum (𝓞 E)} (φ : w.adicCompletion E →+* u.adicCompletion E)

private theorem le_of_val (hφ : ∀ y, Valued.v (φ y) = Valued.v y) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y ≤ 1) : valuation (u.adicCompletion E) (φ y) ≤ 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).le_one_iff_le_one, hφ]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).le_one_iff_le_one.1 hy

private theorem lt_of_val (hφ : ∀ y, Valued.v (φ y) = Valued.v y) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y < 1) : valuation (u.adicCompletion E) (φ y) < 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).lt_one_iff_lt_one, hφ]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).lt_one_iff_lt_one.1 hy

private theorem eq_of_val (hφ : ∀ y, Valued.v (φ y) = Valued.v y) {y : w.adicCompletion E}
    (hy : valuation (w.adicCompletion E) y = 1) : valuation (u.adicCompletion E) (φ y) = 1 := by
  rw [(ValuativeRel.isEquiv (valuation (u.adicCompletion E)) Valued.v).eq_one_iff_eq_one, hφ]
  exact (ValuativeRel.isEquiv (valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one.1 hy

private theorem integral_map (n : ℕ) (hφ : ∀ y, Valued.v (φ y) = Valued.v y)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLnLocal.integralGL (w.adicCompletion E) n) :
    mapGL n φ g ∈ GLnLocal.integralGL (u.adicCompletion E) n := by
  rw [GLnLocal.mem_integralGL_iff] at hg ⊢
  rw [← map_inv]
  simp only [Valuation.mem_integer_iff] at hg ⊢
  exact ⟨fun i j => le_of_val φ hφ (hg.1 i j), fun i j => le_of_val φ hφ (hg.2 i j)⟩

private theorem iwahori_map (n : ℕ) (hφ : ∀ y, Valued.v (φ y) = Valued.v y)
    {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLnLocal.iwahori (w.adicCompletion E) n) :
    mapGL n φ g ∈ GLnLocal.iwahori (u.adicCompletion E) n := by
  rw [GLnLocal.mem_iwahori_iff] at hg ⊢
  exact ⟨fun i j => le_of_val φ hφ (hg.1 i j), fun i j h => lt_of_val φ hφ (hg.2.1 i j h),
    fun i => eq_of_val φ hφ (hg.2.2 i)⟩

end

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.offStable :
    UpperTheory.ConvolutionTheory.T.OffStable := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v
  haveI : Nonempty (PlacesOver E v) := nonempty_placesOver E (v := v)
  haveI : Nonempty (HeightOneSpectrum (𝓞 E)) := ⟨(Classical.arbitrary (PlacesOver E v)).1⟩
  have hv : ∀ (u : PlacesOver E v) y,
      Valued.v ((galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u)).toRingEquiv.toRingHom y) = Valued.v y :=
    fun u y => UpperTheory.ConvolutionTheory.T.val_gal v σ _ _ _ y
  have hc : ∀ (x : GL (Fin n) (CompletionsOver E v)) (u : PlacesOver E v),
      GM.cmp u (mapGL n (galFin σ v) x) =
        mapGL n (galEquiv v σ (σ⁻¹ • u).1 u.1 (eq_smul_inv_smul v σ u)).toRingEquiv.toRingHom (GM.cmp (σ⁻¹ • u) x) :=
    fun x u => Units.ext (Matrix.ext fun a b => UpperTheory.ConvolutionTheory.T.galFin_apply σ v _ u)
  refine ⟨fun x hx u => ?_, fun x hx u => ?_,
    ⟨⨅ u : PlacesOver E v, (GLnLocal.integralGL (u.1.adicCompletion E) n).comap (GM.cmp u), ?_⟩,
    ⟨⨅ u : PlacesOver E v, (GLnLocal.iwahori (u.1.adicCompletion E) n).comap (GM.cmp u),
      fun g => by simp [Subgroup.mem_iInf]⟩,
    fun w => ⟨And.intro (GLnLocal.isCompact_integralGL _ n) (GLnLocal.isOpen_integralGL _ n),
      And.intro (GLnLocal.isCompact_iwahori _ n) (GLnLocal.isOpen_iwahori _ n),
      GLnLocal.iwahori_le_integralGL _ n⟩⟩
  · rw [hc]
    exact UpperTheory.ConvolutionTheory.T.integral_map _ n (hv u) (hx _)
  · rw [hc]
    exact UpperTheory.ConvolutionTheory.T.iwahori_map _ n (hv u) (hx _)
  · ext g
    simp [Subgroup.mem_iInf, unitSet, GM.cmp]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDescOf
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

theorem haar_norm (K : Type) [Field K] [NumberField K] (n : ℕ) (x : Pl K) [MeasurableSpace (Gw n x)] [BorelSpace (Gw n x)] :
    ∃ mm : Measure (Gw n x), mm.IsHaarMeasure ∧ mm (GLnLocal.integralGL (x.adicCompletion K) n) = 1 := by
  have hc := GLnLocal.isCompact_integralGL (x.adicCompletion K) n
  have ho := GLnLocal.isOpen_integralGL (x.adicCompletion K) n
  let P : TopologicalSpace.PositiveCompacts (Gw n x) := ⟨⟨_, hc⟩, by
    change (interior (GLnLocal.integralGL (x.adicCompletion K) n : Set (Gw n x))).Nonempty
    rw [ho.interior_eq]; exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure P, inferInstance, Measure.haarMeasure_self⟩

theorem coreDesc_of (hAbs : AbsLast) (hPull : PullBack) (hUnit : UnitTrace) (hOne : OneTerm) (hSum : SideSum) (hPS : PickS)
    (hPI : PickInf) (hTy : TyEx) (hTE : TermE) (hGood : GoodEx) (hPl : Places) (hOcc : OccursBasics)
    (hEig : EigBasic) (hCI : CI) (hGM : GM.GM) : CoreDesc := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ θ hθ V Λ t hV hVθ hAt hOffA v w hv τ' hτ'
  obtain ⟨S, q, w₀, hvS, hqS, hq, hunr, hsph, hS'⟩ := hPS F E σ hσ hp n hn μE V Λ t hV hAt v
  have hne := (hPl F E hp).2.2.1
  obtain ⟨T, hTS, hmk, htyped, hrank, c, f₀, UF, hUF, hL⟩ := hTy F E σ hσ hp n hn μE V hV q w₀ hq S hqS hunr hsph
    (Function.update (fun u => (hne u).some) v w)
  have hw : T.mk' v = w := by rw [hmk, Function.update_self]
  clear hmk
  subst hw
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 htyped
  obtain ⟨m, hm, D, s, hs, νE, iE, νF, iF, b, a, aE, aF, hposition, harch, hAE, hAF, hpair, hua⟩ :=
    hPI F E σ hσ hp n hn μE μF u hu0
  letI : ∀ x : Pl E, MeasurableSpace (Gw n x) := fun _ => borel _
  haveI : ∀ x : Pl E, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩
  letI : ∀ x : Pl F, MeasurableSpace (Gw n x) := fun _ => borel _
  haveI : ∀ x : Pl F, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩
  have hmE : ∀ x : Pl E, ∃ mm : Measure (Gw n x), mm.IsHaarMeasure := fun x => (haar_norm E n x).imp fun _ h => h.1
  have hmF : ∀ x : Pl F, ∃ mm : Measure (Gw n x), mm.IsHaarMeasure ∧ mm (GLnLocal.integralGL (x.adicCompletion F) n) = 1 :=
    fun x => haar_norm F n x
  choose mE hmE using hmE
  choose mF hmF using hmF
  have hτ : ∀ x : Pl E, ∃ τ : SmIrr (Gw n x), Occurs μE V x τ := fun x => by
    haveI := hmE x
    exact (hOcc E n μE V x (mE x) hV).1
  choose τ₁ hτ₁ using hτ
  obtain ⟨τ, hτ, hτw⟩ : ∃ τ : ∀ x : Pl E, SmIrr (Gw n x), (∀ x, Occurs μE V x (τ x)) ∧ τ (T.mk' v).1 = τ' := by
    refine ⟨Function.update τ₁ (T.mk' v).1 τ', fun x => ?_, Function.update_self ..⟩
    by_cases h : x = (T.mk' v).1
    · subst h; rw [Function.update_self]; exact hτ'
    · rw [Function.update_of_ne h]; exact hτ₁ x
  subst hτw
  obtain ⟨ν, hν⟩ := hGood n hn
  obtain ⟨x, cE, Z₀, hx, hcE, hZ₀, hZ0, hE⟩ := hTE F E σ hσ hp n hn m hm μE θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq T V hV
    hVθ hrank ⟨u, hu, hua⟩ mE hmE τ hτ ν hν.1.antitone
  obtain ⟨κ, hκ, hG⟩ := hGM F E σ hσ hp n hn μE μF θ hθ q w₀ hq νE νF aE aF 1 one_pos hAE hAF hpair
  set SF : Set (Pl F) := {y | y ∈ S ∨ y = q} with hSF
  set SE : Set (Pl E) := {y | y.under (𝓞 F) ∈ SF} with hSE
  obtain ⟨ι, _, V₀, τ₀, bF, Z, hι, hF⟩ := hSum F E σ n (Module.finrank F E) hn μF νF mF hmF aF q w₀ S UF ν hν.1.antitone
    (fun V₀ => ∃ Λ' t', At μF SF V₀ Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ y ∉ SE, t y = bcSat t' y) x hx
  have hvsp : v ∈ T.sp := Finset.mem_filter.2 ⟨hTS ▸ hvS, hv⟩
  obtain ⟨τv, r, hr, hiso, htr, hlev⟩ := hPull F E n v (T.mk' v) (hv _) (mF v) (mE _) (hmF v).1 (hmE _) (τ _)
  obtain ⟨hCO, hfix, hφ⟩ := hlev (T.J _) (UF v) (T.co _) (hUF v hvsp)
  have hunit : ∀ y ∈ T.sp, _ := fun y hy => hUnit E n μE V hV (T.mk' y).1 (mE _) (hmE _) (τ _) (T.J _) (hτ _) (T.co _) (by
    refine (Submodule.ne_bot_iff _).2 ⟨u, ⟨hu.1, ?_⟩, hu0⟩
    have h1 : u ∈ eigL μE (T.mk' y).1 (T.J _) (T.χ _) := (Submodule.mem_iInf _).1 hu.2 _
    rw [T.triv y (Finset.mem_filter.1 hy).2 (T.mk' y)] at h1
    have h2 := T.chr (T.mk' y).1
    rw [T.triv y (Finset.mem_filter.1 hy).2 (T.mk' y)] at h2
    rwa [(hEig E n μE _ _ _ (T.co _) h2).2.1] at h1)
  have hsu : ∀ y : Pl F, ∃ z : ℂ, y ∈ T.sp → z ≠ 0 ∧ HasTrace (mE _) (τ (T.mk' y).1).ρ
      ((T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator 1) z := fun y => by
    by_cases hy : y ∈ T.sp
    · obtain ⟨z, hz⟩ := (hunit y hy).2.2.2
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose su hsu using hsu
  let ψ₁ : ∀ y : Pl F, Gw n (T.mk' y).1 → ℂ := fun y => (T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator 1
  obtain ⟨L₁, hfit₁, -, hL₁s, hL₁n⟩ := hL ψ₁ fun y hy => ⟨(hunit y hy).2.1, (hunit y hy).2.2.1⟩
  have hL₁S : L₁.S = S := hfit₁.S_eq.trans hTS
  have hs₁ : ∀ i (y : Pl F), ∃ z : ℂ, y ∈ S → HasTrace (mF y) (τ₀ i y).ρ (L₁.f y) z := fun i y => by
    by_cases hy : y ∈ S
    · haveI := (hmF y).1
      have ht := L₁.test y (hL₁S ▸ hy)
      obtain ⟨z, hz⟩ := (hOcc F n μF (V₀ i) y (mF y) (hι i).1).2.2 _ ((hι i).2.2.2 y) (L₁.f y) ⟨ht.2.2.1, ht.2.2.2⟩
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose s₁ hs₁ using hs₁
  haveI := (hmF v).1
  obtain ⟨i, hi⟩ := hAbs F n v (mF v) (UF v) hCO ι (fun i => τ₀ i v)
    (fun i => (κ * ∏ y ∈ S, c y) * bF i * ∏ y ∈ S.erase v, s₁ i y) Z τv (cE * r * ∏ y ∈ T.sp.erase v, su y) Z₀
    (mul_ne_zero (mul_ne_zero hcE hr) (Finset.prod_ne_zero_iff.2 fun y hy => (hsu y (Finset.mem_of_mem_erase hy)).1))
    hZ₀ hZ0 (fun i => (hι i).2.2.1) (hfix (hunit v hvsp).1) (by
      intro φ s₀ sF hφt hφi hs₀ hsF
      obtain ⟨ψv, hψt, hψi, rfl⟩ := hφ φ hφt hφi
      obtain ⟨L, hfit, hLc, hLs, hLn⟩ := hL (Function.update ψ₁ v ψv) fun y hy => by
        by_cases h : y = v
        · subst h; rw [Function.update_self]; exact ⟨hψt, hψi⟩
        · rw [Function.update_of_ne h]; exact ⟨(hunit y hy).2.1, (hunit y hy).2.2.1⟩
      have hLS : L.S = S := hfit.S_eq.trans hTS
      obtain ⟨𝔢, 𝔣, h𝔢, h𝔣, hgeo⟩ := hG L ν hν
      have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hLS]; rfl
      have hfS : 𝔣.S = SF := Set.ext fun y => by rw [h𝔣.2.2.1, hLS]; rfl
      obtain ⟨hAt', hc1, hc2⟩ := hS' 𝔢.S fun y => by rw [h𝔢.2.2.1, hLS]
      have hoff : OffFam F n 𝔢.S 𝔣.S Λ t := by
        rw [heS, hfS]
        exact hOffA SF ((S.finite_toSet.union (Set.finite_singleton q)).subset fun y hy => hy)
      filter_upwards [hCI F E n _ hn hp.pos μE μF θ 𝔢 𝔣 _ hgeo Λ t hc1 hc2 hoff x hx] with j hj
      rw [hOne E n _ hn μE θ 𝔢 V Λ t hV hVθ hAt' x j,
        hE L _ hfit _ 𝔢 h𝔢 (Function.update su v (r * s₀)) (fun y hy => by
          by_cases h : y = v
          · subst h; rw [Function.update_self, Function.update_self]; exact htr _ _ hs₀
          · rw [Function.update_of_ne h, Function.update_of_ne h]; exact (hsu y hy).2) j, heS, hfS,
        hF L 𝔣 hLS (fun y hy => (hLc y hy).2) h𝔣 (fun i => Function.update (s₁ i) v (sF i)) (fun i y hy => by
          by_cases h : y = v
          · subst h
            rw [Function.update_self, hLs y hvsp, Function.update_self]; exact hsF i
          · rw [Function.update_of_ne h]
            have e : L.f y = L₁.f y := by
              by_cases hy' : GM.Split E y
              · have hys : y ∈ T.sp := Finset.mem_filter.2 ⟨hTS ▸ hy, hy'⟩
                rw [hLs y hys, hL₁s y hys, Function.update_of_ne h]
              · rw [hLn y hy hy', hL₁n y hy hy']
            rw [e]; exact hs₁ i y hy) j, hLS, Finset.prod_congr rfl fun y hy => (hLc y hy).1,
        Finset.prod_update_of_mem hvsp, Finset.mul_sum] at hj
      simp only [Finset.prod_update_of_mem hvS, Finset.sdiff_singleton_eq_erase] at hj
      calc _ = cE * (Z₀.map (· ^ j)).sum * (r * s₀ * ∏ y ∈ T.sp.erase v, su y) := by ring
        _ = _ := hj
        _ = _ := Finset.sum_congr rfl fun i _ => by ring)
  obtain ⟨Λ', t', hA, hΛ, ht⟩ := (hι i).2.1
  have hSFf : SF.Finite := (S.finite_toSet.union (Set.finite_singleton q)).subset fun y hy => hy
  refine ⟨V₀ i, Λ', t', (hι i).1, ⟨SF, hSFf, hA⟩, hΛ, ?_, τ₀ i v, (hι i).2.2.2 v, hiso _ hi⟩
  obtain ⟨𝔢, -, h𝔢, -⟩ := hG L₁ ν hν
  have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hL₁S]; rfl
  exact Filter.mem_of_superset (heS ▸ 𝔢.finS : SE.Finite).compl_mem_cofinite fun y hy => ht y hy

end UpperTheory.ConvolutionTheory.T
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.UnitTrace
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf
open scoped InnerProductSpace

section Abs

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]

private theorem fixed_of_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep G H) (τ : Representation ℂ G X) (hτ : ∀ x, IsOpen {g | τ g x = x})
    (J : Subgroup G) (hJ : IsCompact (J : Set G)) (f : X →ₗ[ℂ] H) (hf : ∀ g x, f (τ g x) = π g (f x))
    (v : H) (hv : ∀ u ∈ J, π u v = v) (x : X) (h0 : ⟪v, f x⟫_ℂ ≠ 0) :
    fixedVectors τ J ≠ ⊥ := by
  haveI : Nonempty G := ⟨1⟩
  have hfin : ((fun g => τ g x) '' (J : Set G)).Finite := by
    obtain ⟨t, -, ht⟩ := hJ.elim_nhds_subcover (fun g => {h | τ h x = τ g x}) fun g _ => by
      have h1 : IsOpen ((fun h => g⁻¹ * h) ⁻¹' {g | τ g x = x}) := (hτ x).preimage (by fun_prop)
      refine Filter.mem_of_superset (h1.mem_nhds (by simp)) fun h hh => ?_
      have h2 : τ (g⁻¹ * h) x = x := hh
      show τ h x = τ g x
      conv_rhs => rw [← h2]
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    refine (t.finite_toSet.image fun g => τ g x).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact ⟨i, hi, (h : τ g x = τ i x).symm⟩
  classical
  set S := hfin.toFinset with hS
  have hm : ∀ y, y ∈ S ↔ ∃ g ∈ J, τ g x = y := fun y => by simp [hS]
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨x, (hm x).2 ⟨1, J.one_mem, by simp⟩⟩
  have hc' : (S.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  have hst : ∀ u ∈ J, ∀ y ∈ S, τ u y ∈ S := fun u hu y hy => by
    obtain ⟨g, hg, rfl⟩ := (hm y).1 hy
    exact (hm _).2 ⟨u * g, J.mul_mem hu hg, by rw [map_mul]; rfl⟩
  have hy : ∀ y ∈ S, ⟪v, f y⟫_ℂ = ⟪v, f x⟫_ℂ := fun y hy => by
    obtain ⟨g, hg, rfl⟩ := (hm y).1 hy
    rw [hf]
    have h1 := UnitaryRep.inner_map_map π g v (f x)
    rwa [hv g hg] at h1
  have hmem : (S.card : ℂ)⁻¹ • ∑ y ∈ S, y ∈ fixedVectors τ J := fun u hu => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (τ u) (τ u⁻¹) (hst u hu) (hst _ (J.inv_mem hu)) (fun y _ => ?_) (fun y _ => ?_) fun _ _ => rfl
    · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  intro hb
  rw [hb, Submodule.mem_bot] at hmem
  have h1 : ⟪v, f ((S.card : ℂ)⁻¹ • ∑ y ∈ S, y)⟫_ℂ = ⟪v, f x⟫_ℂ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, inner_smul_right, map_sum, inner_sum, Finset.sum_congr rfl hy, Finset.sum_const,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]
  rw [hmem, map_zero, inner_zero_right] at h1
  exact h0 h1.symm

private theorem trace_ne [MeasurableSpace G] [BorelSpace G] (m : Measure G) [m.IsHaarMeasure]
    (τ : Representation ℂ G X) (J : Subgroup G) (hJ : CO J) (hx : fixedVectors τ J ≠ ⊥) {s : ℂ}
    (hs : HasTrace m τ ((J : Set G).indicator 1) s) : s ≠ 0 := by
  obtain ⟨A, hA, hfd, rfl⟩ := hs
  have hmeas : MeasurableSet (J : Set G) := hJ.2.measurableSet
  set c : ℂ := (m.real (J : Set G) : ℂ) with hcdef
  have hc : c ≠ 0 := by
    have h1 : 0 < m (J : Set G) := hJ.2.measure_pos m ⟨1, J.one_mem⟩
    have h2 : m (J : Set G) < ⊤ := hJ.1.measure_lt_top
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos h1.ne' h2.ne).ne'
  have hfix : ∀ y ∈ fixedVectors τ J, A y = c • y := fun y hy => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, (hA y l).2, map_smul, smul_eq_mul, sub_eq_zero]
    have e : (fun g => (J : Set G).indicator (1 : G → ℂ) g * l (τ g y)) = (J : Set G).indicator (fun _ => l y) := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, Pi.one_apply, one_mul, hy g hg]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
    rw [e, integral_indicator hmeas, setIntegral_const]
    simp [hcdef]
  have hran : ∀ v, A v ∈ fixedVectors τ J := fun v h hh => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero]
    change (l ∘ₗ τ h) (A v) = _
    rw [(hA v (l ∘ₗ τ h)).2, (hA v l).2]
    refine Eq.trans ?_ (integral_mul_left_eq_self (μ := m) (fun g => (J : Set G).indicator (1 : G → ℂ) g * l (τ g v)) h)
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have hi : (J : Set G).indicator (1 : G → ℂ) (h * g) = (J : Set G).indicator (1 : G → ℂ) g := by
      by_cases hg : g ∈ J
      · rw [Set.indicator_of_mem (show h * g ∈ (J : Set G) from J.mul_mem hh hg),
          Set.indicator_of_mem (show g ∈ (J : Set G) from hg)]
        rfl
      · rw [Set.indicator_of_notMem (show h * g ∉ (J : Set G) from fun e => hg ((Subgroup.mul_mem_cancel_left J hh).1 e)),
          Set.indicator_of_notMem (show g ∉ (J : Set G) from hg)]
    show (J : Set G).indicator (1 : G → ℂ) g * l (τ h (τ g v)) = (J : Set G).indicator (1 : G → ℂ) (h * g) * l (τ (h * g) v)
    rw [hi, map_mul, Module.End.mul_apply]
  obtain ⟨x, hxf, hx0⟩ := (Submodule.ne_bot_iff _).1 hx
  have hxr : x ∈ LinearMap.range A :=
    ⟨c⁻¹ • x, by rw [map_smul, hfix x hxf, smul_smul, inv_mul_cancel₀ hc, one_smul]⟩
  have hres : A.restrict (p := LinearMap.range A) (q := LinearMap.range A) (fun v _ => LinearMap.mem_range_self A v) =
      c • LinearMap.id := by
    refine LinearMap.ext fun y => Subtype.ext ?_
    obtain ⟨z, hz⟩ := y.2
    exact hfix y.1 (hz ▸ hran z)
  haveI : FiniteDimensional ℂ (LinearMap.range A) := hfd
  haveI : Nontrivial (LinearMap.range A) :=
    ⟨⟨⟨x, hxr⟩, 0, fun e => hx0 (congrArg Subtype.val e)⟩⟩
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul]
  exact mul_ne_zero hc (Nat.cast_ne_zero.2 Module.finrank_pos.ne')

end Abs

theorem UpperTheory.ConvolutionTheory.T.unitTrace :
    UpperTheory.ConvolutionTheory.T.UnitTrace := by
  intro K _ _ n μ _ V hV w _ _ m hm τ J hocc hJ hne
  haveI := hm
  have hcl : IsClosed (J : Set (Gw n w)) := J.isClosed_of_isOpen hJ.2
  have hind : ∀ u ∈ J, ∀ g, (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (u * g) = (J : Set (Gw n w)).indicator 1 g ∧
      (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (g * u) = (J : Set (Gw n w)).indicator 1 g := by
    intro u hu g
    have h1 : u * g ∈ J ↔ g ∈ J := Subgroup.mul_mem_cancel_left J hu
    have h2 : g * u ∈ J ↔ g ∈ J := Subgroup.mul_mem_cancel_right J hu
    by_cases hg : g ∈ J
    · rw [Set.indicator_of_mem (show u * g ∈ (J : Set (Gw n w)) from h1.2 hg),
        Set.indicator_of_mem (show g * u ∈ (J : Set (Gw n w)) from h2.2 hg),
        Set.indicator_of_mem (show g ∈ (J : Set (Gw n w)) from hg)]
      exact ⟨rfl, rfl⟩
    · rw [Set.indicator_of_notMem (show u * g ∉ (J : Set (Gw n w)) from fun e => hg (h1.1 e)),
        Set.indicator_of_notMem (show g * u ∉ (J : Set (Gw n w)) from fun e => hg (h2.1 e)),
        Set.indicator_of_notMem (show g ∉ (J : Set (Gw n w)) from hg)]
      exact ⟨rfl, rfl⟩
  have htest : Test ((J : Set (Gw n w)).indicator (1 : Gw n w → ℂ)) := by
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hJ.1 fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ (J : Set (Gw n w))
    · exact ⟨_, hJ.2, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  have hfix : fixedVectors τ.ρ J ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
    have hvJ : ∀ u ∈ J, locU μ w u v = v := by
      have h1 : v ∈ fixU (locU μ w) J := by
        rw [fixU_locU]
        exact hv.2
      exact h1
    by_contra hbot
    have hle : spanAll τ.ρ (locU μ w) V ≤ (ℂ ∙ v)ᗮ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, hf, x, rfl⟩
      refine Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_
      by_contra h
      exact fixed_of_inner (locU μ w) τ.ρ (fun x => τ.smooth x) J hJ.1 f hf.map v hvJ x h hbot
    have h2 := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
      (UpperTheory.summand_le_closure_span_local_type_images K n μ V w τ hV hocc hv.1)
    exact hv0 (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 h2))
  obtain ⟨-, -, h3⟩ := UpperTheory.ConvolutionTheory.C.occursBasics K n μ V w m hV
  obtain ⟨s, hs⟩ := h3 τ hocc _ htest
  exact ⟨hfix, htest, hind, s, trace_ne m τ.ρ J hJ hfix hs, hs⟩
end
