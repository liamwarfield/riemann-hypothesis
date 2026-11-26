module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.MeasEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.WeilEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Cap
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfCusp
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ConjDivMul
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ThetaLiftTrivialOrbitTermsVanish
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Stable
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapAct
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LiftRel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigOfSat
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsSide
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Imports
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ZFin
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.zFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ZFin W M π := by
  intro F E _ _ _ _ _ _ _ D W M π hreg Φ hΦ
  have hcap := UpperTheory.ConvolutionTheory.R2.cap F E D W M π
  have key : ∀ z ∈ GlobalTheory.CuspRep.Zalg E 2, ∃ c : ℂ, z Φ = c • Φ := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨τ, u, rfl⟩ := hx
      obtain ⟨m, hm, -⟩ := hreg (InfinitePlace.mk (τ.comp (algebraMap F E)))
      exact ⟨_, hcap τ m hm u Φ hΦ⟩
    | algebraMap r => exact ⟨r, by simp [Module.algebraMap_end_apply]⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [LinearMap.add_apply, ha, hb, add_smul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨b * a, by rw [Module.End.mul_apply, hb, map_smul, ha, mul_smul]⟩
  have hle : Submodule.span ℂ ((fun z : Module.End ℂ (Sm E 2) => z Φ) '' GlobalTheory.CuspRep.Zalg E 2) ≤
      Submodule.span ℂ {Φ} := Submodule.span_le.2 (by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, hc⟩ := key z hz
    change z Φ ∈ Submodule.span ℂ {Φ}
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self Φ))
  exact Submodule.finiteDimensional_of_le hle
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.aut :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Aut W M π := by
  intro F E _ _ _ _ _ _ _ D W M π hr Φ hΦ
  have h : span W M π ≤ (Cm.ofAut E 2).range := by
    apply Submodule.span_le.2
    rintro Ψ ⟨f, hf, φ, hφ, e⟩
    refine Cm.mem_range_ofAut.2 ⟨fun γ g => ?_, level F E D W M π f hf φ hφ Ψ e, (kFin F E D W M π f hf φ hφ Ψ e).2,
      zFin F E D W M π hr Ψ (Submodule.subset_span ⟨f, hf, φ, hφ, e⟩), fun g => ?_⟩
    · rw [e]; exact (equiv F E D W M π f hf φ).1 γ g
    · rw [e]; exact growth F E D W M π f hf φ hφ g
  exact Cm.mem_range_ofAut.1 (h hΦ)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsFurther
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.irr :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Irr W M π := by
  intro F E _ _ _ _ _ _ _ D W M π hreg h0 hne
  have hreg' := hreg
  choose m hm _ using hreg'
  have hs : _root_.GlobalTheory.CuspRep.IsStable (span W M π) := UpperTheory.ConvolutionTheory.R2.stable F E D W M π
  have hc : ∀ Φ ∈ span W M π, IsCuspForm Φ := fun Φ hΦ =>
    ⟨UpperTheory.ConvolutionTheory.R2.aut F E D W M π hreg Φ hΦ, (UpperTheory.ConvolutionTheory.R2.cusp F E D W M π h0 Φ hΦ).1⟩
  have hle : span W M π ≤ UpperTheory.V.Cj.S.CI 2 fun τ => m (InfinitePlace.mk (τ.comp (algebraMap F E))) := fun Φ hΦ =>
    UpperTheory.V.Cj.S.mem_CI.2 ⟨hc Φ hΦ, fun τ u => UpperTheory.ConvolutionTheory.R2.cap F E D W M π τ _ (hm _) u Φ hΦ⟩
  have key := UpperTheory.V.TR.SS.le_sSup_minimal (act (E := E) (a := 2)) (span W M π) hs fun U hU hsU => by
    obtain ⟨C, -, c2, c3, c4⟩ := UpperTheory.V.Cj.S.ciCompl (UpperTheory.V.Cj.S.ciBasic UpperTheory.V.Cj.S.capAct) E 2 one_le_two _ U (hU.trans hle) hsU
    refine ⟨C ⊓ span W M π, inf_le_right, fun o x hx => ⟨c2 o x hx.1, hs o x hx.2⟩, ?_, ?_⟩
    · rw [← inf_assoc, c3, bot_inf_eq]
    · rw [← sup_inf_assoc_of_le _ hU, c4, inf_eq_right.2 hle]
  by_contra hno
  refine hne (le_bot_iff.1 (key.trans (sSup_le ?_)))
  rintro V ⟨h1, h2, h3, h4⟩
  exact (hno ⟨⟨V, fun φ hφ => hc φ (h1 hφ), h2, h3, h4⟩, h1⟩).elim
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsTail
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.UnrSplit
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

open GlobalTheory.CuspRep.LocEx GlobalTheory.LFun GlobalTheory.PRep

theorem UpperTheory.ConvolutionTheory.R2.H.unrSplit :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ThetaLiftTrivialOrbitTermsVanish W M π → ∀ Q : CuspSub E 2, Q.V ≤ span W M π →
      ∀ (v : P F) (w : P E), SplitAt v w → ∀ B, π.HasSat v B → (CG.mk Q).HasSat w B := by
  intro F E _ _ _ _ _ _ _ D W M π hN Q hQ v w hs B hB
  obtain ⟨hq, i, hc, hx, hv⟩ := hs
  have hSmooth : IsSmooth (π.locRep v) := fun x =>
    (π.isSmooth_finPart x).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL v)

  have cpt_fin (k : TR.Kinf F 2) (g : GL (Fin 2) (Af F)) (y : π.V) :
      π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
    refine Subtype.ext ?_
    change (TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k)) * TR.rt F 2 (finGL F 2 g)) y.1 =
      (TR.rt F 2 (finGL F 2 g) * TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, TR.infGL_comm]

  have fin_loc {k : GL (Fin 2) (Af F)}
      (hk : GeneralLinearGroup.map (pLoc F v) k = 1) (g : GL (Fin 2) (v.adicCompletion F)) (y : π.V) :
      π.finPart k (π.locRep v g y) = π.locRep v g (π.finPart k y) := by
    simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul,
      GlobalTheory.CuspRep.LocUniq.comm_locGL v hk]

  have bot_or_top (W : Submodule ℂ π.V)
      (h1 : ∀ g, ∀ x ∈ W, π.locRep v g x ∈ W)
      (h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep v g x) = π.locRep v g (T x)) → ∀ x ∈ W, T x ∈ W) :
      W = ⊥ ∨ W = ⊤ := by
    have hi := Submodule.map_injective_of_injective π.V.injective_subtype
    have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
      cases o with
      | fin k =>
        have h3 := h1 (GeneralLinearGroup.map (pLoc F v) k) _ (h2
          (π.finPart ((locGL F 2 v (GeneralLinearGroup.map (pLoc F v) k))⁻¹ * k))
          (fin_loc (map_pLoc_inv_mul v k)) x hx)
        rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left] at h3
      | cpt k => exact h2 _ (fun g y => cpt_fin k _ y) x hx
      | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (locGL F 2 v g)) y.1)) x hx
    rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
      rintro o _ ⟨x, hx, rfl⟩
      exact ⟨_, hop o x hx, rfl⟩) with h | h
    · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
    · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))

  let K := KGL v (n := 2)
  have hSat : HasSatGL v (π.locRep v) B := hB
  obtain ⟨φ, hφ⟩ := hSat.exists_vec
  obtain ⟨hKo, hKc⟩ := SatCompare.isOpen_isCompact_KGL v 2
  -- Every nonzero local invariant subspace has a spherical vector.
  have detects_fixed (S : Submodule ℂ π.V) (hS : ∀ g, ∀ x ∈ S, π.locRep v g x ∈ S)
      (h : S ⊓ fixed (π.locRep v) K = ⊥) : S = ⊥ := by
    rcases bot_or_top (nullPart (π.locRep v) K) (fun g x hx => nullPart_act _ K g hx)
      (fun T hT x hx => nullPart_comm _ K T hT hx) with hnull | hnull
    · exact le_bot_iff.1 (hnull ▸ le_nullPart hSmooth hKc S hS h)
    · exact (hφ.1 (eq_zero_of_mem_nullPart hSmooth hKc hφ.2.1 (hnull ▸ Submodule.mem_top))).elim

  have exists_comp : ∃ σ, π.IsLocComp v σ := by
    let orb {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
        (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V :=
      Finsupp.linearCombination ℂ fun k => κ k x

    have orb_comm {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
        (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
        (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]

    have orb_act {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
        (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
        orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add c c' h h' => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), map_add (f := _), h, h']
      | single a b => simp [orb]

    let annPart {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
        (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V := {
      carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
      add_mem' := fun {x y} hx hy c hc => by
        have : orb κ (x + y) c = orb κ x c + orb κ y c := by
          simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add (f := _), smul_add, Finset.sum_add_distrib]
        rw [this, hx c hc, hy c hc, add_zero]
      zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
      smul_mem' := fun a x hx c hc => by
        have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
        simpa [hx c hc] using this }

    -- Vectors annihilated by the relations of φ are images of its compact type.
    have exists_type {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
        (κ : Representation ℂ K V) (φ : V)
        (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
        ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
          (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c := by
      have hO : ∀ k, ∀ y ∈ LinearMap.range (orb κ φ), κ k y ∈ LinearMap.range (orb κ φ) := by
        rintro k _ ⟨c, rfl⟩
        exact ⟨_, orb_act κ φ k c⟩
      have : FiniteDimensional ℂ (LinearMap.range (orb κ φ)) := by
        change FiniteDimensional ℂ (LinearMap.range (Finsupp.linearCombination ℂ fun k => κ k φ))
        rw [Finsupp.range_linearCombination]
        exact hφ
      let b := Module.finBasis ℂ (LinearMap.range (orb κ φ))
      obtain ⟨s, hs⟩ := (orb κ φ).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
      refine ⟨_, (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO), fun x hx => ?_⟩
      have key : ∀ c, orb κ x (s ((orb κ φ).rangeRestrict c)) = orb κ x c := fun c => by
        rw [← sub_eq_zero, ← map_sub]
        refine hx _ ?_
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val (LinearMap.congr_fun hs ((orb κ φ).rangeRestrict c))
      refine ⟨orb κ x ∘ₗ s ∘ₗ b.equivFun.symm.toLinearMap, fun k v => ?_,
        ⟨b.equivFun ((orb κ φ).rangeRestrict (Finsupp.single 1 1)), ?_⟩, fun v => ⟨_, rfl⟩⟩
      · obtain ⟨y, rfl⟩ := b.equivFun.surjective v
        obtain ⟨c, rfl⟩ := (orb κ φ).surjective_rangeRestrict y
        have h1 : (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO) k *ᵥ b.equivFun ((orb κ φ).rangeRestrict c) =
            b.equivFun ((orb κ φ).rangeRestrict (c.mapDomain (k * ·))) := by
          have h2 : (orb κ φ).rangeRestrict (c.mapDomain (k * ·)) = sub κ _ hO k ((orb κ φ).rangeRestrict c) :=
            Subtype.ext (orb_act κ φ k c)
          rw [h2]
          exact LinearMap.toMatrix_mulVec_repr b b _ _
        rw [h1]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key, orb_act]
      · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key]
        simp [orb]

    let cptPart : Representation ℂ (TR.Kinf F 2) π.V :=
      sub (TR.cptRep F 2) π.V fun k => π.stable (.cpt k)

    let L := stab π.finPart φ
    have hL : IsOpen (L : Set (GL (Fin 2) (Af F))) := π.isSmooth_finPart φ
    have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart k φ)) := by
      have := (π.cusp φ.1 φ.2).1.kfin
      refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
        (Submodule.span ℂ (Set.range fun k => TR.cptRep F 2 k φ.1)) fun x => ?_)
        fun x y e => Subtype.ext (Subtype.ext (by
          have e' := congrArg Subtype.val e
          exact e'))
      refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ x.2)
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨k, rfl⟩
    obtain ⟨d, ξ, hξ⟩ := exists_type cptPart φ hfd
    have hcomm : ∀ g k x, π.finPart g (cptPart k x) = cptPart k (π.finPart g x) := fun g k x => (cpt_fin k g x).symm
    let U : Submodule ℂ π.V := annPart cptPart φ ⊓
      fixed π.finPart (L ⊓ (GeneralLinearGroup.map (n := Fin 2) (pLoc F v)).ker)
    obtain ⟨σ, hσ, -⟩ := exists_irred hSmooth hKo detects_fixed
      U (fun g x hx => ⟨fun c hc => by
          rw [TR.CuspSub.locRep, MonoidHom.comp_apply, orb_comm _ _ (hcomm _), hx.1 c hc, map_zero],
        mem_fix.2 fun k hk => by rw [fin_loc hk.2, mem_fix.1 hx.2 k hk]⟩)
      ((Submodule.ne_bot_iff _).2 ⟨φ, ⟨fun _ hc => hc, mem_fix.2 fun k hk => hk.1⟩, hφ.1⟩) (fun K' hK' => by
        obtain ⟨W, hW, hWf⟩ := UpperTheory.V.Af.admissibleReal F 2 π (L ⊓ (K' ⊓ L.comap (locGL F 2 v)).comap (GeneralLinearGroup.map (pLoc F v)))
          (hL.inter ((hK'.inter (hL.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL v))).preimage
            (continuous_map_pLoc v))) d ξ
        refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
        obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1.1
        refine hWf f hf (fun k hk z => ?_) hx1
        have h1 := mem_fix.1 hx.1.2 _ ⟨L.mul_mem (L.inv_mem hk.2.2) hk.1, map_pLoc_inv_mul v k⟩
        have h2 := mem_fix.1 hx.2 _ hk.2.1
        have h3 : π.finPart k x = x := by
          rw [← mul_inv_cancel_left (locGL F 2 v (GeneralLinearGroup.map (pLoc F v) k)) k, map_mul,
            mul_apply_eq_comp, h1]
          exact h2
        obtain ⟨c, hc⟩ := hf2 z
        rw [hc, ← orb_comm _ _ (hcomm k), h3])
    exact ⟨σ, hσ⟩

  obtain ⟨σ, hσ⟩ := exists_comp
  have h1 : HasSatGL v σ.ρ B := by
    obtain ⟨f, hf0, hf⟩ := hσ
    have hi := GlobalTheory.BcSpehCompare.injective_of_irred σ.irred
      (τ := fun g => π.locRep v g) (fun _ => map_zero _) hf0 hf
    have hfix : ∀ x ∈ fixed σ.ρ K, f x ∈ fixed (π.locRep v) K := fun x hx =>
      mem_fix.2 fun k hk => by rw [← hf, mem_fix.1 hx k hk]
    constructor
    · have hRange : LinearMap.range f ⊓ fixed (π.locRep v) K ≠ ⊥ := fun h =>
        hf0 (LinearMap.range_eq_bot.1 (detects_fixed (LinearMap.range f)
          (by rintro g _ ⟨x, rfl⟩; exact ⟨_, hf g x⟩) h))
      obtain ⟨_, ⟨⟨x, rfl⟩, hx⟩, hx0⟩ := (Submodule.ne_bot_iff _).1 hRange
      exact (Submodule.ne_bot_iff _).2 ⟨x, mem_fix.2 fun k hk => hi (by
        rw [hf, mem_fix.1 hx k hk]), fun e => hx0 (by rw [e, map_zero])⟩
    · intro x hx hx0
      exact (hSat.2 _ (hfix x hx) ((map_ne_zero_iff f hi).2 hx0)).of_map f hf hi
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL E 2 Q w
  obtain ⟨e, he⟩ := UpperTheory.ConvolutionTheory.R2.split F E D W M π hN Q hQ v w i hc hx σ σ' hσ hσ'
  have hq' : Formalism.UG.qV E w = Formalism.UG.qV F v := by
    simpa [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV] using hq
  have h2 : GlobalTheory.LFun.HasSatGL w σ'.ρ B :=
    GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i hv hq' e (fun g x => (he g x).symm) h1
  exact (GlobalTheory.BcSpehCompare.hasSat_iff hσ' B).2 h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.UnrInert
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WeLoc
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.weLoc :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (w : P E), Gd D.δ v → Inert D v w →
      ∃ χ : Kv w → ℂ, Good χ ∧ ∀ x, ∃ u t, sg w x = D.mkE u t ∧ ψ (-(2 * u)) = χ x := by
  intro F E _ _ _ _ _ D v w hG hI
  obtain ⟨e, h1, h2, h3, -⟩ := hI.coord
  obtain ⟨sa, sm, sc, -⟩ := sgLaws F v
  obtain ⟨-, tm, tc, -⟩ := sgLaws E w
  obtain ⟨ga, gi, gm⟩ := hG.psi
  have hs : ∀ u, -(2 * sg v u) = sg v (-(2 * u)) := fun u => by
    rw [← neg_mul, sm, map_neg, map_ofNat, neg_mul]
  have s0 : sg v (0 : Kv v) = 0 := by simpa using (sm 0 0).symm
  have h4 : ∀ c u t, e (0, c) * e (u, t) = e (algebraMap F (Kv v) D.δ * (c * t), c * u) := fun c u t => by
    have a1 : ∀ x y, sg v (x * y) = sg v x * sg v y := fun x y => by rw [sm, sc]
    have a2 : ∀ x, sg v (algebraMap F (Kv v) D.δ * x) = rt D.δ * sg v x := fun x => (sm (rt D.δ) x).symm
    have a3 : (rt D.θ : A E) ^ 2 = AdeleBaseChange.adeleMap F E (rt D.δ) := by
      rw [← map_pow, D.sq]
      exact (AdeleBaseChange.adeleMap_algebraMap _).symm
    have : sg w (e (0, c) * e (u, t)) = sg w (e (algebraMap F (Kv v) D.δ * (c * t), c * u)) := by
      rw [← tc (e (0, c)), ← tm, h1, h1, h1, s0, a2, a1, a1]
      simp only [Dat.mkE, map_mul, map_zero, ← a3]
      ring
    simpa only [tc] using congrArg (cp w) this
  have key : ∀ y : Kv v, (∀ c, IsInt c → ψ (sg v (-(2 * (c * y)))) = 1) → IsInt y := fun y hy => by
    have : Valued.v (-(2 * y)) ≤ 1 := gm _ fun c hc => by
      have := hy c hc
      rwa [show -(2 * (c * y)) = c * -(2 * y) by ring] at this
    rwa [Valuation.map_neg, map_mul, hG.two, one_mul] at this
  refine ⟨fun x => ψ (sg v (-(2 * (e.symm x).1))), ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩, fun x => ?_⟩
  · beta_reduce
    rw [map_add (f := _), Prod.fst_add, mul_add, neg_add]
    exact ga _ _
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have hu : Valued.v u ≤ 1 := (le_max_left _ _).trans ((h2 u t).symm.le.trans hx)
    beta_reduce
    rw [e.symm_apply_apply]
    refine gi _ ?_
    show Valued.v _ ≤ 1
    rwa [Valuation.map_neg, map_mul, hG.two, one_mul]
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have hu : IsInt u := key u fun c hc => by
      have := hx (e (c, 0)) ((h2 c 0).le.trans (max_le hc (by simp)))
      beta_reduce at this
      rwa [h3, e.symm_apply_apply] at this
    have ht : Valued.v (algebraMap F (Kv v) D.δ * t) ≤ 1 := key _ fun c hc => by
      have := hx (e (0, c)) ((h2 0 c).le.trans (max_le (by simp) hc))
      beta_reduce at this
      rwa [h4, e.symm_apply_apply, mul_left_comm _ c t] at this
    rw [map_mul, hG.del, one_mul] at ht
    exact (h2 u t).le.trans (max_le hu ht)
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    exact ⟨_, _, h1 u t, by beta_reduce; rw [hs, e.symm_apply_apply]⟩
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem below_ev {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : P F → Prop} (h : ∀ᶠ v in cofinite, p v) : ∀ᶠ w : P E in cofinite, ∀ v, Below v w → p v := by
  have hfin : ∀ v : P F, {w : P E | Below v w}.Finite := fun v => by
    haveI := v.isMaximal
    refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
      ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_) (fun _ _ _ _ h => HeightOneSpectrum.ext h)
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.isPrime, ⟨hw⟩⟩
  have hS : {v | ¬ p v}.Finite := h
  have : (⋃ v ∈ {v | ¬ p v}, {w : P E | Below v w}).Finite := hS.biUnion fun v _ => hfin v
  filter_upwards [this.eventually_cofinite_notMem] with w hw v hv
  by_contra hc
  exact hw (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hc, hv⟩⟩)

private def LRel {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
    {D : Dat F E} (W : Weil D) (π : TR.CuspSub F 2) (h₀ : GL (Fin 2) (A E)) (Φ : GL (Fin 2) (A E) → ℂ) (v : P F) : Prop :=
  W.η.UnrAt v → W.η.val v = -1 → ∀ α β : ℂˣ, π.HasSat v {α, β} → ∀ (ϖ : (Kv v)ˣ) (z : (A E)ˣ), IsU ϖ →
    (z : A E) = D.mkE (idl v ϖ : (A F)ˣ) 0 → ideleNorm F E z = idl v ϖ ^ 2 →
    WE D Φ (aE z * h₀) = (q v)⁻¹ * ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * WE D Φ h₀ ∧
      ∀ h, Φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h) = ((α : ℂ) * β) ^ 2 * Φ h

private theorem we_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E)
    (h : GL (Fin 2) (A E)) : WE D (0 : GL (Fin 2) (A E) → ℂ) h = 0 := by
  simp [WE]

private theorem span_rel {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
    (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2) (h₀ : GL (Fin 2) (A E)) (Φ : Sm E 2) (hΦ : Φ ∈ span W M π) :
    ∀ᶠ v : P F in cofinite, LRel W π h₀ Φ.1 v := by
  have hc : ∀ Ψ ∈ span W M π, Continuous Ψ.1 := fun Ψ h => (spanCont F E D W M π Ψ h).1
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hφ, e⟩ := hx
    rw [e]
    exact liftRel F E D W M π f hf φ hφ h₀
  | zero =>
    refine Filter.Eventually.of_forall fun v _ _ α β _ ϖ z _ _ _ => ⟨?_, fun h => ?_⟩
    · show WE D (0 : GL (Fin 2) (A E) → ℂ) _ = _ * WE D (0 : GL (Fin 2) (A E) → ℂ) _
      simp [we_zero]
    · show (0 : GL (Fin 2) (A E) → ℂ) _ = _ * (0 : GL (Fin 2) (A E) → ℂ) _
      simp
  | add x y hx hy ihx ihy =>
    filter_upwards [ihx, ihy] with v h1 h2 hu hv α β hB ϖ z hϖ hz hn
    obtain ⟨a1, a2⟩ := h1 hu hv α β hB ϖ z hϖ hz hn
    obtain ⟨b1, b2⟩ := h2 hu hv α β hB ϖ z hϖ hz hn
    have e : ∀ h, WE D (x + y).1 h = WE D x.1 h + WE D y.1 h := fun h => by
      have := (weEig F E D x.1 (hc x hx)).2.2 y.1 1 (hc y hy) h
      simpa using this
    refine ⟨?_, fun h => ?_⟩
    · rw [e, e, a1, b1]; ring
    · show x.1 _ + y.1 _ = _ * (x.1 _ + y.1 _)
      rw [a2, b2]; ring
  | smul c x hx ihx =>
    filter_upwards [ihx] with v h1 hu hv α β hB ϖ z hϖ hz hn
    obtain ⟨a1, a2⟩ := h1 hu hv α β hB ϖ z hϖ hz hn
    have e : ∀ h, WE D (c • x).1 h = c * WE D x.1 h := fun h => by
      have := (weEig F E D 0 continuous_const).2.2 x.1 c (hc x hx) h
      simpa [we_zero] using this
    refine ⟨?_, fun h => ?_⟩
    · rw [e, e, a1]; ring
    · show c * x.1 _ = _ * (c * x.1 _)
      rw [a2]; ring

private theorem pairs {a b c d : ℂ} (hs : c + d = a + b) (hp : c * d = a * b) : (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have h : (c - a) * (c - b) = 0 := by linear_combination c * hs - hp
  rcases mul_eq_zero.1 h with h | h
  · have e : c = a := sub_eq_zero.1 h
    exact Or.inl ⟨e, by rw [e] at hs; exact add_left_cancel hs⟩
  · have e : c = b := sub_eq_zero.1 h
    exact Or.inr ⟨e, by rw [e, add_comm a] at hs; exact add_left_cancel hs⟩

theorem UpperTheory.ConvolutionTheory.R2.H.unrInert :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ThetaLiftTrivialOrbitTermsVanish W M π → ∀ Q : CuspSub E 2, Q.V ≤ span W M π →
      ∀ᶠ w : P E in cofinite, ∀ v : P F, Below v w → Inert D v w → ∀ B, π.HasSat v B → (CG.mk Q).HasSat w (B.map (· ^ 2)) := by
  intro F E _ _ _ _ _ _ _ D W M π hN Q hQ
  obtain ⟨y, hy, h0⟩ := (Submodule.ne_bot_iff _).1 Q.ne_bot
  have hsp := hQ hy
  obtain ⟨hcont, hleft⟩ := spanCont F E D W M π y hsp
  obtain ⟨-, hwh⟩ := UpperTheory.ConvolutionTheory.R2.cusp F E D W M π hN y hsp
  obtain ⟨h₀, hh₀⟩ : ∃ h₀, WE D y.1 h₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (hwh hc)
  obtain ⟨h₁, hh₁⟩ : ∃ h₁, y.1 h₁ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (Subtype.ext (funext hc))
  have hδ : D.δ ≠ 0 := fun e => by
    have h1 : D.θ = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by rw [D.sq, e, map_zero])
    exact D.b.ne_zero 1 (D.b1.trans h1)
  have hne : (⟨y, hy⟩ : Q.V) ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  filter_upwards [below_ev (span_rel D W M π h₀ y hsp), W.quad, GlobalTheory.CuspRep.AeFix.eventually_mem_fixed E 2 Q ⟨y, hy⟩,
    (aeK E).1 h₀, GlobalTheory.CompanionTheory.SatAe.eventually_exists_hasSat Q, below_ev (gdAe F D.δ hδ)] with w hrel hq hfix hk ⟨B', hB'⟩ hgd v hv hin B hB
  obtain ⟨hu, hval⟩ := hq v hv
  have hnv : 1 < normV v := by
    have := GlobalTheory.LFun.one_lt_absNorm v
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  have hn : normV w ≠ normV v := fun e => by
    have h3 := hin.norm
    rw [e] at h3
    nlinarith
  rw [if_neg hn] at hval
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card hB)
  obtain ⟨α', β', rfl⟩ := Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card hB')
  obtain ⟨p, hp⟩ : ∃ p, Formalism.UG.IsUnifV F v p := v.valuedAdicCompletion_surjective F _
  have hp0 : p ≠ 0 := fun h0 => by simp [Formalism.UG.IsUnifV, h0] at hp
  obtain ⟨ϖ', hϖ', hz, hnz⟩ := hin.unif (Units.mk0 p hp0) hp
  obtain ⟨r1, r2⟩ := hrel v hv hu hval α β hB (Units.mk0 p hp0) (idl w ϖ') hp hz hnz
  have hfix' : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w (n := 2), y.1 (g * finGL E 2 (locGL E 2 w k)) = y.1 g := fun g k hk =>
    congrFun (congrArg (fun x : Q.V => x.1.1) (GlobalTheory.LGrp.mem_fixed.1 hfix k hk)) g
  have hEig : EigAt w {α', β'} y.1 := by
    intro g
    refine ⟨hB'.card, fun x k hk => ?_, fun ϖ hϖ j hj x => ?_⟩
    · rw [map_mul, map_mul, ← mul_assoc, hfix' _ k hk]
    · by_cases h0 : y = 0
      · subst y
        simp
      have he := (hB'.2 (⟨y, hy⟩ : Q.V)
        (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (Subtype.ext (funext fun x => hfix' x k hk))) fun h => h0 (congrArg Subtype.val h)).2.2.2 ϖ hϖ j hj
      let ev : Q.V →+ ℂ :=
        { toFun := fun ψ => ψ.1.1 (g * finGL E 2 (locGL E 2 w x))
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hs := ev.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w 2)
        (GlobalTheory.LFun.Tj_mem_hecke hϖ j) (Q.locRep w) ⟨y, hy⟩)
      refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans (congrArg ev he))
      rw [map_mul, map_mul, ← mul_assoc]
      rfl
  have hEw := (weEig F E D y.1 hcont).2.1 w _ hEig
  have hE1 : Eig w {α', β'} fun x => WE D y.1 (lc w x * h₀) := by
    have := (fixTr E w _ h₀ hk).2 _ hEw 1
    simpa [lc] using this
  obtain ⟨χ, hχ, hχe⟩ := weLoc F E D v w (hgd v hv) hin
  have hnl : ∀ b x, WE D y.1 (lc w (nL b * x) * h₀) = χ b * WE D y.1 (lc w x * h₀) := fun b x => by
    obtain ⟨u, t, e1, e2⟩ := hχe b
    rw [map_mul, (lcLaws E w).1, e1, mul_assoc, ((weEig F E D y.1 hcont).1 hleft) u t, e2]
  obtain ⟨t1, -⟩ := whTorus E w ϖ' hϖ' χ hχ α' β' _ hE1 hnl
  obtain ⟨R, -, -, hR⟩ := heckeExpl E w ϖ' hϖ'
  have hc := (hR α' β' _ (hEig h₁) 1).2
  have hc' : y.1 (h₁ * Matrix.GeneralLinearGroup.scalar (Fin 2) (idl w ϖ')) = (α' : ℂ) * β' * y.1 h₁ := by
    simp only [one_mul, map_one, mul_one] at hc
    rw [← (lcLaws E w).2.2.2.2.1]
    exact hc
  have hp' : (α' : ℂ) * β' = (α : ℂ) ^ 2 * (β : ℂ) ^ 2 := by
    have h2 := r2 h₁
    rw [GlobalTheory.CuspRep.scalar_comm, hc'] at h2
    have h3 := mul_right_cancel₀ hh₁ h2
    rw [h3]
    ring
  have e1 : WE D y.1 (lc w (dL ϖ' 1) * h₀) = WE D y.1 (aE (idl w ϖ') * h₀) := by rw [(lcLaws E w).2.2.2.1]
  have e2 : WE D y.1 (lc w 1 * h₀) = WE D y.1 h₀ := by simp
  beta_reduce at t1
  rw [e1, e2, r1] at t1
  have hcard : ∀ {K : Type} [Field K] [NumberField K] (u : P K), q u = (normV u : ℂ) := fun u => by
    simp [q, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hqw : q w = q v ^ 2 := by
    rw [hcard, hcard, hin.norm]
    push_cast
    rfl
  have hqv : q v ≠ 0 := by
    rw [hcard]
    exact Nat.cast_ne_zero.2 (by omega)
  have hsq : q w ^ (1 / 2 : ℂ) = q v := by
    rw [hqw, hcard]
    have e : ((normV v : ℂ) ^ 2) = ((((normV v : ℝ) ^ 2 : ℝ)) : ℂ) := by push_cast; rfl
    rw [e, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    simp
  have hs : (α' : ℂ) + β' = (α : ℂ) ^ 2 + (β : ℂ) ^ 2 := by
    rw [hsq, hqw] at t1
    have h3 : q v ^ 2 * ((q v)⁻¹ * ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * WE D y.1 h₀) =
        q v * ((α : ℂ) ^ 2 + (β : ℂ) ^ 2) * WE D y.1 h₀ := by
      field_simp
    rw [h3] at t1
    exact (mul_left_cancel₀ hqv (mul_right_cancel₀ hh₀ t1)).symm
  rcases pairs hs hp' with ⟨a, b⟩ | ⟨a, b⟩
  · have a' : α' = α ^ 2 := Units.ext (by simpa using a)
    have b' : β' = β ^ 2 := Units.ext (by simpa using b)
    rw [a', b'] at hB'
    simpa using hB'
  · have a' : α' = β ^ 2 := Units.ext (by simpa using a)
    have b' : β' = α ^ 2 := Units.ext (by simpa using b)
    rw [a', b', Multiset.pair_comm] at hB'
    simpa using hB'
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

open UpperTheory.ConvolutionTheory.R2.H in
theorem UpperTheory.ConvolutionTheory.R2.unr :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Unr W M π := by
  intro F E _ _ _ _ _ _ _ D W M π h0 Q hQ
  have hs : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ v : HeightOneSpectrum (𝓞 F), Below v w → ∃ B, π.HasSat v B := by
    have h1 := UpperTheory.V.Af.Gk.satAE F 2 π
    rw [Filter.eventually_cofinite] at h1 ⊢
    refine (h1.biUnion (t := fun v => {w : HeightOneSpectrum (𝓞 E) | Below v w}) fun v _ => ?_).subset fun w hw => ?_
    · have := v.isMaximal
      refine Set.Finite.of_finite_image (f := fun w => w.asIdeal) ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).subset ?_)
        fun _ _ _ _ e => HeightOneSpectrum.ext e
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨w.isPrime, ⟨hw⟩⟩
    · simp only [Set.mem_setOf_eq, not_forall] at hw
      obtain ⟨v, hv, hn⟩ := hw
      exact Set.mem_biUnion (show v ∈ {v | ¬ ∃ B, π.HasSat v B} from hn) hv
  filter_upwards [hs, placeAe F E D, unrInert F E D W M π h0 Q hQ] with w h1 h2 h3 v hv f hf
  obtain ⟨B, hB⟩ := h1 v hv
  have h4 : 1 < normV v := by
    have := GlobalTheory.LFun.one_lt_absNorm v
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  refine ⟨B, hB, ?_⟩
  rcases h2 v hv with hsp | hi
  · have : f = 1 := Nat.pow_right_injective h4 (show normV v ^ f = normV v ^ 1 by rw [← hf, hsp.1, pow_one])
    subst this
    simpa using unrSplit F E D W M π h0 Q hQ v w hsp B hB
  · have : f = 2 := Nat.pow_right_injective h4 (show normV v ^ f = normV v ^ 2 by rw [← hf, hi.norm])
    subst this
    exact h3 v hv hi B hB
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsExtra
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExIw
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.WfNe
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.InfDec
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

private theorem real_dec {ι : Type} (X : GL (Fin 2) (ι → ℝ)) :
    ∃ (s : (ι → ℝ)ˣ) (g : GL (Fin 2) (ι → ℝ)) (k : Matrix.unitaryGroup (Fin 2) (ι → ℝ)),
      Matrix.GeneralLinearGroup.det g = 1 ∧
        X = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (g * Unitary.toUnits k) := by
  classical
  set D : (ι → ℝ)ˣ := Matrix.GeneralLinearGroup.det X with hD
  have hw : ∀ w, (D : ι → ℝ) w ≠ 0 := fun w => ((Pi.isUnit_iff.1 D.isUnit) w).ne_zero
  have hpos : ∀ w, 0 < Real.sqrt |(D : ι → ℝ) w| := fun w => Real.sqrt_pos.2 (abs_pos.2 (hw w))
  let s : (ι → ℝ)ˣ :=
    ⟨fun w => Real.sqrt |(D : ι → ℝ) w|, fun w => (Real.sqrt |(D : ι → ℝ) w|)⁻¹,
      funext fun w => mul_inv_cancel₀ (hpos w).ne', funext fun w => inv_mul_cancel₀ (hpos w).ne'⟩
  let e : ι → ℝ := fun w => if 0 < (D : ι → ℝ) w then 1 else -1
  have hee : e * e = 1 := by
    funext w
    by_cases h : 0 < (D : ι → ℝ) w <;> simp [e, h]
  have hse : (s : ι → ℝ) * s * e = D := by
    funext w
    have h2 : Real.sqrt |(D : ι → ℝ) w| * Real.sqrt |(D : ι → ℝ) w| = |(D : ι → ℝ) w| :=
      Real.mul_self_sqrt (abs_nonneg _)
    change Real.sqrt |(D : ι → ℝ) w| * Real.sqrt |(D : ι → ℝ) w| * e w = _
    rw [h2]
    by_cases h : 0 < (D : ι → ℝ) w
    · simp [e, h, abs_of_pos h]
    · have h' : (D : ι → ℝ) w < 0 := lt_of_le_of_ne (not_lt.1 h) (hw w)
      simp [e, h, abs_of_neg h']
  have hstar : star e = e := by
    funext w
    simp
  let K : Matrix (Fin 2) (Fin 2) (ι → ℝ) := !![1, 0; 0, e]
  have hKK : K * K = 1 := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [K, Matrix.mul_apply, Fin.sum_univ_two, hee]
  have hKs : star K = K := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [K, Matrix.star_eq_conjTranspose, hstar]
  have hKmem : K ∈ Matrix.unitaryGroup (Fin 2) (ι → ℝ) := by
    rw [Matrix.mem_unitaryGroup_iff, hKs]
    exact hKK
  let k : Matrix.unitaryGroup (Fin 2) (ι → ℝ) := ⟨K, hKmem⟩
  have hk : (Unitary.toUnits k) * (Unitary.toUnits k) = 1 := Units.ext hKK
  have hdetk : (Matrix.GeneralLinearGroup.det (Unitary.toUnits k) : ι → ℝ) = e := by
    change K.det = e
    simp [K, Matrix.det_fin_two]
  have hdets : ∀ t : (ι → ℝ)ˣ,
      (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) t) : ι → ℝ) = t * t := by
    intro t
    change (Matrix.GeneralLinearGroup.scalar (Fin 2) t).val.det = _
    simp [Matrix.det_fin_two, sq]
  refine ⟨s, Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹ * X * Unitary.toUnits k, k, ?_, ?_⟩
  · refine Units.ext ?_
    rw [map_mul, map_mul]
    simp only [Units.val_mul, hdetk, hdets, Units.val_one]
    rw [← hD, ← hse]
    funext w
    have h1 := congrFun hee w
    have h2 : (s : ι → ℝ) w * ((s⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) w = 1 := congrFun s.mul_inv w
    simp only [Pi.mul_apply, Pi.one_apply] at h1 ⊢
    calc _ = (((s : ι → ℝ) w * ((s⁻¹ : (ι → ℝ)ˣ) : ι → ℝ) w) ^ 2) * (e w * e w) := by ring
      _ = 1 := by rw [h2, h1]; simp
  · have hsc : Matrix.GeneralLinearGroup.scalar (Fin 2) s * Matrix.GeneralLinearGroup.scalar (Fin 2) s⁻¹ = 1 := by
      rw [← map_mul]; simp
    rw [mul_assoc _ _ (Unitary.toUnits k), hk, mul_one, ← mul_assoc, hsc, one_mul]

theorem UpperTheory.ConvolutionTheory.R2.Pp.infDec :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.InfDec F := by
  intro F _ _ _ x
  obtain ⟨s, g, k, hg, hx⟩ := real_dec (GeneralLinearGroup.map (TR.pInf F) x)
  have hdet : GeneralLinearGroup.det (TR.infGL F 2 g) = 1 := by
    rw [TR.det_infGL, hg, map_one]
  have hdet' : (TR.infGL F 2 g).val.det = 1 := congrArg Units.val hdet
  let G : G1 F := ⟨(TR.infGL F 2 g).val, hdet'⟩
  have hG : gl G = TR.infGL F 2 g := Units.ext rfl
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.infId F s) =
      TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) s) := by
    have hs : ∀ y, TR.pInf F (TR.sInf F y) = y := fun y => (TR.infEq F).symm_apply_apply y
    have hi : TR.pInf F (TR.infId F s).val = s.val := by
      change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _
      simp [hs]
    have hf : pFin F (TR.infId F s).val = 1 := by
      change (1 : Af F) - 0 + 0 = 1
      simp
    refine TR.ga_ext ?_ ?_
    · rw [TR.pInf_infGL]
      ext i j
      by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, hi]
    · rw [TR.pFin_infGL]
      ext i j
      by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, hf]
  refine ⟨G, TR.infId F s, k, GeneralLinearGroup.map (pFin F) x, ?_, ?_⟩
  · intro i j
    have h := congrArg (fun h : GL (Fin 2) (Af F) => h.val i j) (TR.pFin_infGL (E := F) g)
    have h1 : ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2 = (1 : GL (Fin 2) (Af F)).val i j := by
      by_cases e : i = j
      · simp only [Matrix.one_apply, e, if_true, Units.val_one]
        rfl
      · simp [Matrix.one_apply, e]
    rw [h1]
    exact h
  · rw [hsc, hG]
    conv_lhs => rw [← TR.infGL_mul_finGL x, hx]
    simp only [map_mul, mul_assoc]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

theorem UpperTheory.ConvolutionTheory.R2.Pp.wfNe :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.WfNe F := by
  intro F _ _ _ π
  obtain ⟨f, hf, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨ω, -, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨x, hx⟩ : ∃ x, Wf f.1 x ≠ 0 := by
    by_contra hn
    push Not at hn
    obtain ⟨φ, rfl⟩ := Fb.mem_range_ofCusp.2 (π.cusp f hf)
    exact h0 (Subtype.ext (eq_zero_of_Wf φ.2 (cuspZero F π _ hf).1 hn))
  obtain ⟨g, s, k, y, hg, rfl⟩ := infDec F x
  refine ⟨TR.act (.cpt k) (TR.act (.fin y) f), π.stable _ _ (π.stable _ _ hf), g, hg, fun h => hx ?_⟩
  unfold Wf at h ⊢
  rw [← mul_zero ((ω s : ℂˣ) : ℂ), ← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  have e : ∀ z : GL (Fin 2) (A F), gl (nU b) * (Matrix.GeneralLinearGroup.scalar (Fin 2) s * z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) s * (gl (nU b) * z) := fun z => by
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact Units.ext ((Matrix.scalar_commute (s : A F) (fun _ => mul_comm _ _) _).eq.symm)
  simp only
  rw [e, hω f hf, mul_assoc, ← mul_assoc (gl (nU b)), ← mul_assoc (gl (nU b))]
  rfl
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.exIw :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (π : TR.CuspSub F 2), ∃ f ∈ π.V, ∃ a, ∃ k ∈ KK F, Wf f.1 (gl (mD a * k)) ≠ 0 := by
  intro F _ _ _ _ π
  obtain ⟨f, hf, g, -, hg⟩ := UpperTheory.ConvolutionTheory.R2.Pp.wfNe F π
  obtain ⟨b, a, k, hk, rfl⟩ := UpperTheory.ConvolutionTheory.R2.M.iwa F g
  refine ⟨f, hf, a, k, hk, fun h => hg ?_⟩
  have e : gl (nU b * mD a * k) = gl (nU b) * gl (mD a * k) := by
    rw [mul_assoc]
    exact map_mul _ _ _
  rw [e, ((UpperTheory.ConvolutionTheory.R2.Pp.wfBasic F f.1 (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1).2.1 b _), h, mul_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExPhi
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.exPhi :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (a : (A F)ˣ), ∀ k ∈ KK F, ∃ φ ∈ Fock D.δ, hat (W.Om (mD a * k) φ).1 ![0, 1, 1, 0] ≠ 0 := by
  intro F E _ _ _ _ _ _ _ D W a k hk
  have H := hatSt F E D W
  have K := fockSt F E D W
  obtain ⟨χ, hχ, hne⟩ := (fockMul F D.δ).2 ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0]
  obtain ⟨φ₁, hφ₁, hh⟩ := hatSurj F D.δ D.neg χ hχ
  have hk' : k⁻¹ ∈ KK F := by
    have hs := (M.kkCpt F).1
    rw [hs] at hk ⊢
    exact inv_mem hk
  obtain ⟨U, hU, -, hC⟩ := K.om φ₁ hφ₁ {k⁻¹} isCompact_singleton (by rintro _ rfl; exact hk'.1)
  refine ⟨W.Om k⁻¹ φ₁, hU (hC _ rfl), ?_⟩
  have e : W.Om (mD a * k) (W.Om k⁻¹ φ₁) = W.Om (mD a) φ₁ := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
  have hv : (![a * (![0, 1, 1, 0] : V4 F) 0, ((a⁻¹ : (A F)ˣ) : A F) * (![0, 1, 1, 0] : V4 F) 1,
      a * (![0, 1, 1, 0] : V4 F) 2, a * (![0, 1, 1, 0] : V4 F) 3] : V4 F) =
      ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] := by
    ext1 i
    fin_cases i <;> simp
  rw [e, H.m, hh, hv]
  have hab : ((ab a : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ab a := (IdeleGroup.ideleModule F a).2
    exact_mod_cast this.ne'
  exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) hab) hne
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.ne :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), St.Ne W M π := by
  intro F E _ _ _ _ _ _ _ D W M π
  obtain ⟨f, hf, a, k, hk, hW⟩ := G.exIw F M π
  obtain ⟨φ, hφ, hp⟩ := G.exPhi F E D W a k hk
  by_contra hn
  have h0 : ∀ φ ∈ Fock D.δ, W1 W M f.1 φ 1 = 0 := fun φ hφ => by
    by_contra h1
    exact hn ⟨f, hf, φ, hφ, 1, h1⟩
  have h := G.zeroW F E D W M π f hf h0 φ hφ a k hk
  have e : nu F (1 : GL (Fin 2) (A E)) = 1 := by simp [nu]
  simp only [w1, e, dM_one, mul_one, map_one, Module.End.one_apply] at h
  exact mul_ne_zero hW hp h
end

open NumberField IsDedekindDomain MeasureTheory
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.quadBC2 : UpperTheory.V.Z.Bc.QuadBC2 := by
  intro F E _ _ _ _ _ _ _ h2 π hreg
  obtain ⟨D⟩ := datEx F E h2
  obtain ⟨W⟩ := weilEx F E D
  obtain ⟨M⟩ := measEx F
  by_cases h0 : ThetaLiftTrivialOrbitTermsVanish W M π
  · right
    have hne : span W M π ≠ ⊥ := by
      obtain ⟨f, hf, φ, hφ, h, hW⟩ := ne F E D W M π
      obtain ⟨Φ, hΦ⟩ := smooth F E D W M π f hf φ hφ
      intro hb
      have hm : Φ ∈ span W M π := Submodule.subset_span ⟨f, hf, φ, hφ, hΦ⟩
      rw [hb, Submodule.mem_bot] at hm
      apply hW
      rw [← exp F E D W M π f hf φ hφ h, ← hΦ, hm]
      simp [WE]
    obtain ⟨P, hP⟩ := irr F E D W M π hreg h0 hne
    exact ⟨P, fun τ m hm => ⟨hm.1, fun u Φ hΦ => cap F E D W M π τ m hm u Φ (hP hΦ)⟩,
      split F E D W M π h0 P hP, unr F E D W M π h0 P hP⟩
  · exact Or.inl ⟨W.η, W.quad, dih F E D W M π hreg h0⟩
