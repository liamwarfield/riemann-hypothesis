module

public import Formalism.AdmissibleDesigns.KernelLengthHigherColumns

@[expose] public section

section -- merged from Formalism.AdmissibleDesigns.URepApply
section -- merged from Formalism.AdmissibleDesigns.URecApply
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

def CycW : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (g : Dw i dc (idx i dc w)),
    (((Br.PD D.loc D.nbr i w hw).χ (eW i dc hw g) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) =
      (((cycE i (g : GE D.nd) : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) : ℚ_[D.nd.l i])

def sE (e : ℕ) (g : GE D.nd) : D.nd.O i :=
  ((((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp (cycE i ^ (-(e : ℤ)))) g : (D.nd.O i)ˣ) : D.nd.O i)

def epsL {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (h : Br.G D.nbr i w hw) : Br.Ow (D.nbr i w hw) :=
  (D.nbr i w hw).eO (algebraMap ℤ_[D.nd.l i] (D.nd.O i) (((cycE i ((eW i dc hw).symm h : GE D.nd))⁻¹ : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]))

end Rec

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem algZ_LL {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (z : ℤ_[D.nd.l i]) :
    algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) ((D.nbr i w hw).eO (algebraMap ℤ_[D.nd.l i] (D.nd.O i) z)) =
      algebraMap ℚ_[D.nd.l i] (Br.LLw (D.nbr i w hw)) (z : ℚ_[D.nd.l i]) := by
  rw [(D.nbr i w hw).eO_alg z, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply ℤ_[D.nd.l i] ℚ_[D.nd.l i] (Br.LLw (D.nbr i w hw))]
  rfl

theorem epsL_eq (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (h : Br.G D.nbr i w hw) :
    algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h) =
      algebraMap ℚ_[D.nd.l i] (Br.LLw (D.nbr i w hw))
        ((((Br.PD D.loc D.nbr i w hw).χ h)⁻¹ : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) := by
  have hc := hcyc w hw ((eW i dc hw).symm h)
  rw [MulEquiv.apply_symm_apply] at hc
  rw [epsL, algZ_LL, Units.val_inv_eq_inv_val, hc]
  congr 1
  exact eq_inv_of_mul_eq_one_left (by rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one])

variable [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def uRec {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) :
    Mc i Dd c ≃+ ((Fin 1 → Br.LLw (D.nbr i w hw)) ⧸ Formalism.MainNotions.N.stdG (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) 1) :=
  φ.toAddEquiv.trans (koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw)) (fun c => Br.toLLK_alg (D.nbr i w hw) c))

theorem uRec_apply {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) (m : Mc i Dd c) :
    uRec i Dd hw c φ m =
      koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw)) (fun c => Br.toLLK_alg (D.nbr i w hw) c) (φ m) :=
  rfl

end Dict

section Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem yLoc_of
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (c : Fin (D.R.t + 1)) (n : ℕ) :
    YLoc (O := D.nd.O i) (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc n) := by
  intro ψ _
  let _ := Formalism.MainNotions.N.K.Topo.fracTopology (D.nd.O i)
  let _ := Formalism.MainNotions.N.K.Topo.rTopology (D.nd.O i) Dd.R'
  have := Formalism.MainNotions.N.K.Topo.fracTop_addGroup_O i
  have := Formalism.MainNotions.N.K.Topo.fracTop_smul_O i
  have := Formalism.MainNotions.N.K.Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  have := Formalism.MainNotions.N.K.Topo.rTop_constSMul_RD i Dd
  have := Formalism.MainNotions.N.K.Topo.rTop_mul_RD i r π g0 eB e₁ s Dd hD
  have htors (m : Mc i Dd c) : ∃ a : D.nd.O i, a ≠ 0 ∧ a • m = 0 := by
    have h1 : ∀ y : KO (D.nd.O i), ∃ a : D.nd.O i, a ≠ 0 ∧ a • y = 0 := by
      intro y
      induction y using Submodule.Quotient.induction_on with
      | H x =>
        obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (D.nd.O i)) x
        refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
        exact ⟨a, by rw [Algebra.smul_def, mul_comm]; exact hab.symm⟩
    choose a ha0 ha using fun j => h1 (m j)
    refine ⟨∏ j, a j, Finset.prod_ne_zero_iff.2 fun j _ => ha0 j, ?_⟩
    funext j
    change (∏ j, a j) • m j = 0
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_smul, ha j, smul_zero]
  have hA := Formalism.MainNotions.N.K.Topo.fgTop_RD i r π g0 eB e₁ s Dd hD
  have hfg : ReciprocityTheory.ChartRestriction.T2.IsFGTop (D.nd.O i) (Ymod Dd.r Dd.χ Dd.E) := by
    have := hA.fg
    have := hA.t2
    have := hA.csmul
    refine ⟨?_, inferInstance, ?_⟩
    · exact Module.Finite.of_injective ((Ymod Dd.r Dd.χ Dd.E).subtype.restrictScalars (D.nd.O i)) Subtype.val_injective
    · exact ⟨Continuous.subtype_mk (f := fun q : (D.nd.O i) × (Ymod Dd.r Dd.χ Dd.E) => q.1 • (q.2 : Dd.R'))
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  obtain ⟨a, ha, hka⟩ : ∃ a : D.nd.O i, a ≠ 0 ∧ ∀ y : Ymod Dd.r Dd.χ Dd.E, a • ψ y = 0 := by
    obtain ⟨t, ht⟩ := hfg.fg.fg_top
    choose f hf0 hf using fun y : Ymod Dd.r Dd.χ Dd.E => htors (ψ y)
    refine ⟨∏ y ∈ t, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), fun y => ?_⟩
    have hy : y ∈ Submodule.span (D.nd.O i) (t : Set (Ymod Dd.r Dd.χ Dd.E)) := ht ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem f hx
      rw [hb, mul_comm, mul_smul, hf, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]
    | smul b x _ hx => rw [map_smul, smul_comm, hx, smul_zero]
  have continuous_of_isLocalHom {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
      [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
      (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (φ : A →+* B)
      [IsLocalHom φ] : Continuous φ := by
    refine continuous_of_continuousAt_zero φ ?_
    rw [ContinuousAt, map_zero]
    intro s hs
    obtain ⟨n, hn⟩ := (isAdic_iff.1 hB).2 s hs
    have hopen := (isAdic_iff.1 hA).1 n
    rw [Filter.mem_map]
    filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with x hx
    apply hn
    have hle : (IsLocalRing.maximalIdeal A).map φ ≤ IsLocalRing.maximalIdeal B :=
      Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit φ a ha
    have h1 : φ x ∈ ((IsLocalRing.maximalIdeal A) ^ n).map φ := Ideal.mem_map_of_mem φ hx
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hle n h1
  
  have l_mem_max : ((D.nd.l i : ℕ) : D.nd.O i) ∈ IsLocalRing.maximalIdeal (D.nd.O i) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h2 := Formalism.MainNotions.SumRepresentations.norm_iotaOQ_unit D.nd D.naut i u
    have h3 := Formalism.MainNotions.SumRepresentations.norm_iotaOQ_l D.nd D.naut i
    rw [hu] at h2
    rw [h2] at h3
    exact lt_irrefl _ h3
  have l_ne_zero : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 :=
    Formalism.MainNotions.SumRepresentations.natCast_ne_zero_O D.nd i (D.nd.l i) (D.nd.lPrime i).out.ne_zero
  have isLocalHom_alg : IsLocalHom (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
    refine ⟨fun z hz => ?_⟩
    by_contra hn
    have h1 : z ∈ IsLocalRing.maximalIdeal ℤ_[D.nd.l i] := hn
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
    obtain ⟨y, rfl⟩ := h1
    rw [map_mul, map_natCast] at hz
    exact (IsLocalRing.mem_maximalIdeal _).1 (l_mem_max) (isUnit_of_mul_isUnit_left hz)
  have continuous_alg : Continuous (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
    haveI := isLocalHom_alg
    exact continuous_of_isLocalHom (ReciprocityTheory.ChartRestriction.T2.padicCoeff_padicInt (p := D.nd.l i)).adic (D.nd.O_adic i) _
  have compact_O : CompactSpace (D.nd.O i) := by
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ_[D.nd.l i] (D.nd.O i)
    have hc : Continuous f := by
      have : (f : (Fin n → ℤ_[D.nd.l i]) → D.nd.O i) = fun v =>
          ∑ k, algebraMap ℤ_[D.nd.l i] (D.nd.O i) (v k) * f (fun j => if k = j then 1 else 0) := by
        funext v
        rw [LinearMap.pi_apply_eq_sum_univ f v]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Algebra.smul_def]
      rw [this]
      fun_prop (disch := exact continuous_alg)
    exact hf.compactSpace hc
  have t2Space_nd_O : T2Space (D.nd.O i) := by
    have hopen : ∀ n : ℕ, IsOpen ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) : Set (D.nd.O i)) :=
      (isAdic_iff.1 (D.nd.O_adic i)).1
    have hclosed : ∀ n : ℕ, IsClosed ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) : Set (D.nd.O i)) :=
      fun n => AddSubgroup.isClosed_of_isOpen (Submodule.toAddSubgroup (IsLocalRing.maximalIdeal (D.nd.O i) ^ n)) (hopen n)
    have h0 : ({0} : Set (D.nd.O i)) =
        ⋂ n : ℕ, ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) : Set (D.nd.O i)) := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_iInter, SetLike.mem_coe]
      constructor
      · rintro rfl n
        exact Ideal.zero_mem _
      · intro h
        have h1 : x ∈ (⨅ n : ℕ, IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) := by
          rw [Ideal.mem_iInf]; exact h
        rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top] at h1
        exact h1
    have : IsClosed ({0} : Set (D.nd.O i)) := by
      rw [h0]; exact isClosed_iInter hclosed
    haveI : T1Space (D.nd.O i) := IsTopologicalAddGroup.t1Space _ this
    infer_instance
  have padicCoeff_O : ReciprocityTheory.ChartRestriction.T2.PadicCoeff (D.nd.l i) (D.nd.O i) :=
    ⟨D.nd.trO i, compact_O, t2Space_nd_O, D.nd.O_adic i, l_mem_max, l_ne_zero⟩
  have hopen := hfg.isOpen_mulSub padicCoeff_O ha
  have hy : Continuous fun g => yY Dd.r Dd.χ Dd.E g :=
    Continuous.subtype_mk (f := fun g => (uElt Dd.r Dd.χ g - 1) * Dd.E)
      (((Formalism.MainNotions.N.K.Topo.uElt_cont i r π g0 eB e₁ s Dd hD hc).sub continuous_const).mul continuous_const) _
  set_option synthInstance.maxHeartbeats 200000 in
  have h : IsLocallyConstant fun g => ψ (yY Dd.r Dd.χ Dd.E g) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g₀
    refine ⟨(fun g => yY Dd.r Dd.χ Dd.E g - yY Dd.r Dd.χ Dd.E g₀) ⁻¹' _, hopen.preimage (hy.sub continuous_const), ?_, ?_⟩
    · show yY Dd.r Dd.χ Dd.E g₀ - yY Dd.r Dd.χ Dd.E g₀ ∈ Formalism.RepresentationBoundsCohomology.LOC.mulSub a (Ymod Dd.r Dd.χ Dd.E)
      rw [sub_self]
      exact zero_mem _
    · rintro g ⟨z, hz⟩
      have hz' : a • z = yY Dd.r Dd.χ Dd.E g - yY Dd.r Dd.χ Dd.E g₀ := hz
      have h1 : ψ (yY Dd.r Dd.χ Dd.E g - yY Dd.r Dd.χ Dd.E g₀) = 0 := by
        rw [← hz', map_smul, hka]
      rw [map_sub, sub_eq_zero] at h1
      exact h1
  exact h.comp_continuous continuous_subtype_val

end Loc

end Formalism.MainNotions.N.K.TBb

end
end

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem uRec_smul {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) (a : D.nd.O i) (m : Mc i Dd c) :
    uRec i Dd hw c φ (a • m) = (D.nbr i w hw).eO a • uRec i Dd hw c φ m := by
  rw [uRec_apply, uRec_apply]
  exact (congrArg (koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw))
    (fun x => Br.toLLK_alg (D.nbr i w hw) x)) (φ.map_smul a m)).trans (koEquiv_smul _ _ _ _ _)

theorem uRep_apply' (c : Fin (D.R.t + 1)) (g : GE D.nd) (m : Mc i Dd c) :
    uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m = uElt Dd.r Dd.χ g • m := rfl

omit [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
theorem koE_apply' (e : ℕ) (g : GE D.nd) (x : KO (D.nd.O i)) : koE i e g x = sE i e g • x := rfl

theorem eO_sE (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (e : ℕ) (g : Dw i dc (idx i dc w)) :
    (D.nbr i w hw).eO (sE i e (g : GE D.nd)) = (epsL i dc hw (eW i dc hw g)) ^ e := by
  have hz : (cycE i ^ (-(e : ℤ))) (g : GE D.nd) = ((cycE i (g : GE D.nd))⁻¹) ^ e := by
    rw [show (cycE i ^ (-(e : ℤ))) (g : GE D.nd) = (cycE i (g : GE D.nd)) ^ (-(e : ℤ)) from rfl,
      zpow_neg, zpow_natCast, inv_pow]
  have key : sE i e (g : GE D.nd) = (algebraMap ℤ_[D.nd.l i] (D.nd.O i)
      (((cycE i (g : GE D.nd))⁻¹ : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i])) ^ e := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← hz]
    rfl
  rw [key, map_pow]
  simp [epsL]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem uRec_act (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i))
    (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m) = koE i ((c : ℕ) - 1) g (φ m))
    (g : Dw i dc (idx i dc w)) (m : Mc i Dd c) :
    uRec i Dd hw c φ (uElt Dd.r Dd.χ (g : GE D.nd) • m) =
      (epsL i dc hw (eW i dc hw g)) ^ ((c : ℕ) - 1) • uRec i Dd hw c φ m := by
  have h1 : uElt Dd.r Dd.χ (g : GE D.nd) • m = sE i ((c : ℕ) - 1) (g : GE D.nd) • m := by
    apply φ.injective
    rw [← uRep_apply' i Dd c, hφ, koE_apply', φ.map_smul]
  rw [h1, uRec_smul, eO_sE i dc hcyc hw]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
def coefDictOf (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i))
    (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m) = koE i ((c : ℕ) - 1) g (φ m))
    (hcont : Continuous fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^ ((c : ℕ) - 1)) :
    CoefDict (Br.PD D.loc D.nbr i w hw) (Br.LLw (D.nbr i w hw)) (Br.Ow (D.nbr i w hw)) (D.nbr i w hw).eO
      (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1) where
  Ce := twLat Subtype.val_injective (epsL i dc hw) (epsL_eq i dc hcyc hw) ((c : ℕ) - 1) hcont
  u := uRec i Dd hw c φ
  u_smul a m := uRec_smul i Dd hw c φ a m
  u_act g m := (uRec_act i dc Dd hcyc hw c φ hφ g m).trans
    (actD_twLat Subtype.val_injective (epsL i dc hw) (epsL_eq i dc hcyc hw) ((c : ℕ) - 1) hcont (eW i dc hw g)
      (uRec i Dd hw c φ m)).symm

end Dict

end Formalism.MainNotions.N.K.TBb

end
end

section -- merged from Formalism.AdmissibleDesigns.TrivialBoundGeneral
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB

section LenGen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {O' : Type} [CommRing O'] {σ : O' ≃+* O}
    {A T' GG : Type} [Ring A] [Algebra O' A] [CommRing T'] [Algebra T' A] [Group GG]
    {M : Type} [AddCommGroup M] [Module A M] [Module O' M] [SMulCommClass A O' M]
    {r : GG →* A} {χ : GG →* T'ˣ} {Dw : Subgroup GG} {eG : Dw ≃* G} {e : ℕ}
    (Cd : CoefDict PD LL O σ M r χ Dw eG e)

theorem trC_add (z₁ z₂ : Dw → M) : trC Cd (z₁ + z₂) = trC Cd z₁ + trC Cd z₂ := by
  funext g
  simp only [trC, Pi.add_apply, map_add (f := _)]

theorem trC_sub (z₁ z₂ : Dw → M) : trC Cd (z₁ - z₂) = trC Cd z₁ - trC Cd z₂ := by
  funext g
  simp only [trC, Pi.sub_apply, map_sub]

theorem trC_smul (a : O') (z : Dw → M) : trC Cd (a • z) = σ a • trC Cd z := by
  funext g
  simp only [trC, Pi.smul_apply, Cd.u_smul]

theorem trC_apply_eG (z : Dw → M) (g : Dw) : trC Cd z (eG g) = Cd.u (z g) := by
  simp only [trC, MulEquiv.symm_apply_apply]

variable [TopologicalSpace Dw] (heG : Continuous eG.symm)

include heG in
theorem trC_Z1D' (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : IsLocallyConstant (z : Dw → M)) :
    trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L := by
  unfold divisibleCocycles
  refine ⟨(hz.comp_continuous heG).comp Cd.u, fun g h => ?_⟩
  have hc0 := z.2
  unfold coZ1s at hc0
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hc0
  have hc : (z : Dw → M) (eG.symm g * eG.symm h) =
      (z : Dw → M) (eG.symm g) + uElt r χ ((eG.symm g : Dw) : GG) • (z : Dw → M) (eG.symm h) :=
    hc0 _ _
  show Cd.u ((z : Dw → M) (eG.symm (g * h))) =
    Cd.u ((z : Dw → M) (eG.symm g)) + actD Cd.Ce.L g (Cd.u ((z : Dw → M) (eG.symm h)))
  rw [map_mul eG.symm g h, hc, map_add (f := _), Cd.u_act, MulEquiv.apply_symm_apply]

variable (F : Submodule O' (H1z (resRep (uRep O' (M := M) r χ) Dw))) (ℓ cB : ℕ)

def rep (y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB))) :
    coZ1s (resRep (uRep O' (M := M) r χ) Dw) :=
  Classical.choose (Submodule.mem_map.1 y.2.1)

theorem rep_lc (y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB))) :
    IsLocallyConstant ((rep F ℓ cB y : coZ1s _) : Dw → M) := (Classical.choose_spec (Submodule.mem_map.1 y.2.1)).1

theorem rep_mk (y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB))) :
    (Submodule.mkQ _ (rep F ℓ cB y) : H1z (resRep (uRep O' (M := M) r χ) Dw)) = y := (Classical.choose_spec (Submodule.mem_map.1 y.2.1)).2

variable {F ℓ cB}
variable (hp : PD.p = ℓ)
  (hW : ∀ z : coZ1s (resRep (uRep O' (M := M) r χ) Dw), IsLocallyConstant (z : Dw → M) →
    (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F → trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L)
  (hB : ∀ z : coZ1s (resRep (uRep O' (M := M) r χ) Dw), IsLocallyConstant (z : Dw → M) →
    trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L → (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F)

include heG hW in
theorem diff_mem (z₁ z₂ : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (h₁ : IsLocallyConstant (z₁ : Dw → M))
    (h₂ : IsLocallyConstant (z₂ : Dw → M))
    (hF : (Submodule.mkQ _ z₁ : H1z (resRep (uRep O' (M := M) r χ) Dw)) - Submodule.mkQ _ z₂ ∈ F) :
    trC Cd (z₁ : Dw → M) - trC Cd (z₂ : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L := by
  have hlc : IsLocallyConstant (((z₁ - z₂ : coZ1s _) : Dw → M)) := h₁.sub h₂
  have hF' : (Submodule.mkQ _ (z₁ - z₂) : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F := by
    rw [map_sub]; exact hF
  have e : trC Cd ((z₁ - z₂ : coZ1s _) : Dw → M) = trC Cd (z₁ : Dw → M) - trC Cd (z₂ : Dw → M) := by
    rw [← trC_sub]; rfl
  rw [← e]
  exact Submodule.mem_inf.2 ⟨trC_Z1D' Cd heG _ hlc, hW _ hlc hF'⟩

include heG hW hp in
theorem rep_memQ (y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB))) :
    trC Cd ((rep F ℓ cB y : coZ1s _) : Dw → M) ∈ QrecS PD Cd.Ce cB := by
  refine Submodule.mem_inf.2 ⟨trC_Z1D' Cd heG _ (rep_lc F ℓ cB y), ?_⟩
  rw [Submodule.mem_comap]
  have hlc : IsLocallyConstant ((((ℓ : O') ^ cB • rep F ℓ cB y : coZ1s _)) : Dw → M) :=
    (rep_lc F ℓ cB y).comp fun m => ((ℓ : O') ^ cB) • m
  have hmem : (Submodule.mkQ _ ((ℓ : O') ^ cB • rep F ℓ cB y) : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F := by
    rw [map_smul, rep_mk]
    first
      | exact y.2.2
      | simpa [divBy] using y.2.2
  have h := hW _ hlc hmem
  have e : trC Cd ((((ℓ : O') ^ cB • rep F ℓ cB y : coZ1s _)) : Dw → M) =
      σ ((ℓ : O') ^ cB) • trC Cd ((rep F ℓ cB y : coZ1s _) : Dw → M) := by
    rw [← trC_smul]; rfl
  rw [e] at h
  simpa [hp, map_pow, map_natCast] using h

def lenPre : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)) →ₛₗ[σ.toRingHom]
    Qrec PD Cd.Ce cB where
  toFun y := Submodule.Quotient.mk ⟨trC Cd ((rep F ℓ cB y : coZ1s _) : Dw → M), rep_memQ Cd heG hp hW y⟩
  map_add' y₁ y₂ := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
    show trC Cd ((rep F ℓ cB (y₁ + y₂) : coZ1s _) : Dw → M) -
      (trC Cd ((rep F ℓ cB y₁ : coZ1s _) : Dw → M) + trC Cd ((rep F ℓ cB y₂ : coZ1s _) : Dw → M)) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L
    rw [← trC_add]
    refine diff_mem Cd heG hW (rep F ℓ cB (y₁ + y₂)) (rep F ℓ cB y₁ + rep F ℓ cB y₂) (rep_lc F ℓ cB _)
      ((rep_lc F ℓ cB y₁).add (rep_lc F ℓ cB y₂)) ?_
    rw [map_add (f := _), rep_mk, rep_mk, rep_mk, Submodule.coe_add, sub_self]
    exact F.zero_mem
  map_smul' a y := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    show trC Cd ((rep F ℓ cB (a • y) : coZ1s _) : Dw → M) -
      σ a • trC Cd ((rep F ℓ cB y : coZ1s _) : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L
    rw [← trC_smul]
    refine diff_mem Cd heG hW (rep F ℓ cB (a • y)) (a • rep F ℓ cB y) (rep_lc F ℓ cB _)
      ((rep_lc F ℓ cB y).comp fun m => a • m) ?_
    rw [map_smul, rep_mk, rep_mk, Submodule.coe_smul, sub_self]
    exact F.zero_mem


include heG hp hW hB in
theorem lenMap_gen : LenMap PD σ
    (↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)) ⧸
      F.comap (Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)).subtype) Cd.Ce cB := by
  have key : ∀ y : ↥(Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)), lenPre (F := F) (ℓ := ℓ) (cB := cB) Cd heG hp hW y = 0 ↔ (y : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ F := by
    intro y
    show Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      have h2 := hB _ (rep_lc F ℓ cB y) (Submodule.mem_inf.1 h).2
      rwa [rep_mk] at h2
    · intro h
      exact Submodule.mem_inf.2 ⟨trC_Z1D' Cd heG _ (rep_lc F ℓ cB y),
        hW _ (rep_lc F ℓ cB y) (by rw [rep_mk]; exact h)⟩
  have hle : F.comap (Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ divBy F ((ℓ : O') ^ cB)).subtype ≤
      LinearMap.ker (lenPre (F := F) (ℓ := ℓ) (cB := cB) Cd heG hp hW) := fun y hy => LinearMap.mem_ker.2 ((key y).2 hy)
  refine ⟨(Submodule.liftQ _ (lenPre (F := F) (ℓ := ℓ) (cB := cB) Cd heG hp hW) hle).toAddMonoidHom, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      rw [LinearMap.toAddMonoidHom_coe, Submodule.liftQ_apply] at hx
      exact (Submodule.Quotient.mk_eq_zero _).2 ((key y).1 hx)
  · intro a x
    rw [LinearMap.toAddMonoidHom_coe]
    exact map_smulₛₗ _ a x

theorem trivial_bound_general {t cB : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (het : e < t) (Ce : TwLat PD LL O e) :
    (0 < e → divisibleCocycles Ce.L ⊓ HfD PD Ce.L ≤ BD Ce.L) ∧
      (e = 0 → divisibleCocycles Ce.L ⊓ HfD PD Ce.L = divisibleCocycles Ce.L ⊓ (Z1urD Ce.L I ⊔ BD Ce.L)) := by
  have h := hTB.2 e het Ce.V Ce.ρ Ce.L Ce.cont Ce.mat
  exact ⟨h.1, h.2.1⟩

end LenGen

section Conds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {O' : Type} [CommRing O'] {σ : O' ≃+* O}
    {A T' GG : Type} [Ring A] [Algebra O' A] [CommRing T'] [Algebra T' A] [Group GG]
    {M : Type} [AddCommGroup M] [Module A M] [Module O' M] [SMulCommClass A O' M]
    {r : GG →* A} {χ : GG →* T'ˣ} {Dw : Subgroup GG} {eG : Dw ≃* G} {e : ℕ}
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) [TopologicalSpace Dw] (heG : Continuous eG.symm)

theorem hW_bot (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (_hz : IsLocallyConstant (z : Dw → M))
    (h : (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ (⊥ : Submodule O' _)) :
    trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L := by
  refine Submodule.mem_sup_right ?_
  rw [Submodule.mem_bot] at h
  have h2 := (Submodule.Quotient.mk_eq_zero _).1 h
  rw [Submodule.mem_comap] at h2
  unfold coB1 at h2
  obtain ⟨m, hm⟩ := LinearMap.mem_range.1 h2
  have hz : ∀ g : Dw, (z : Dw → M) g = uElt r χ (g : GG) • m - m := fun g => (congrFun hm g).symm
  unfold BD
  refine LinearMap.mem_range.2 ⟨Cd.u m, ?_⟩
  funext x
  show actD Cd.Ce.L x (Cd.u m) - Cd.u m = Cd.u ((z : Dw → M) (eG.symm x))
  rw [hz, map_sub, Cd.u_act, MulEquiv.apply_symm_apply]

include heG in
theorem hB_bot (hpos : divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L ≤ BD Cd.Ce.L)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : IsLocallyConstant (z : Dw → M))
    (h : trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L) :
    (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ (⊥ : Submodule O' _) := by
  have hZ := trC_Z1D' Cd heG z hz
  have hB := hpos (Submodule.mem_inf.2 ⟨hZ, h⟩)
  unfold BD at hB
  obtain ⟨v, hv⟩ := LinearMap.mem_range.1 hB
  rw [Submodule.mem_bot]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [Submodule.mem_comap]
  unfold coB1
  refine LinearMap.mem_range.2 ⟨Cd.u.symm v, ?_⟩
  funext g
  apply Cd.u.injective
  have hg := congrFun hv (eG g)
  rw [trC_apply_eG] at hg
  show Cd.u (uElt r χ (g : GG) • Cd.u.symm v - Cd.u.symm v) = Cd.u ((z : Dw → M) g)
  rw [← hg, map_sub, Cd.u_act, AddEquiv.apply_symm_apply]
  try rfl

theorem unr_exists (I' : Subgroup Dw) (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw))
    (h : (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈ unrH1 (resRep (uRep O' (M := M) r χ) Dw) I') :
    ∃ m : M, ∀ g : Dw, g ∈ I' → (z : Dw → M) g = uElt r χ (g : GG) • m - m := by
  unfold unrH1 at h
  rw [LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap] at h
  unfold coB1 at h
  obtain ⟨m, hm⟩ := LinearMap.mem_range.1 h
  exact ⟨m, fun g hg => (congrFun hm ⟨g, hg⟩).symm⟩

variable {I : Subgroup G} {I' : Subgroup Dw}


include heG in
theorem hW_zero (hzero : divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L = divisibleCocycles Cd.Ce.L ⊓ (Z1urD Cd.Ce.L I ⊔ BD Cd.Ce.L))
    (hI' : ∀ h ∈ I, eG.symm h ∈ I')
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : IsLocallyConstant (z : Dw → M))
    (h : (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈
      Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ unrH1 (resRep (uRep O' (M := M) r χ) Dw) I') :
    trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L := by
  obtain ⟨m, hm⟩ := unr_exists I' z (Submodule.mem_inf.1 h).2
  have hZ := trC_Z1D' Cd heG z hz
  have hU : trC Cd (z : Dw → M) ∈ Z1urD Cd.Ce.L I := by
    unfold Z1urD
    refine ⟨Cd.u m, fun g hg => ?_⟩
    show Cd.u ((z : Dw → M) (eG.symm g)) = actD Cd.Ce.L g (Cd.u m) - Cd.u m
    rw [hm _ (hI' g hg), map_sub, Cd.u_act, MulEquiv.apply_symm_apply]
  have hmem : trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ (Z1urD Cd.Ce.L I ⊔ BD Cd.Ce.L) :=
    Submodule.mem_inf.2 ⟨hZ, Submodule.mem_sup_left hU⟩
  rw [← hzero] at hmem
  exact (Submodule.mem_inf.1 hmem).2


include heG in
theorem hB_zero (hzero : divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L = divisibleCocycles Cd.Ce.L ⊓ (Z1urD Cd.Ce.L I ⊔ BD Cd.Ce.L))
    (hI : ∀ g : Dw, g ∈ I' → eG g ∈ I)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : IsLocallyConstant (z : Dw → M))
    (h : trC Cd (z : Dw → M) ∈ HfD PD Cd.Ce.L) :
    (Submodule.mkQ _ z : H1z (resRep (uRep O' (M := M) r χ) Dw)) ∈
      Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (resRep (uRep O' (M := M) r χ) Dw) ⊓ unrH1 (resRep (uRep O' (M := M) r χ) Dw) I' := by
  have hZ := trC_Z1D' Cd heG z hz
  have hmem : trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L := Submodule.mem_inf.2 ⟨hZ, h⟩
  rw [hzero] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (Submodule.mem_inf.1 hmem).2
  unfold Z1urD at ha
  obtain ⟨x, hx⟩ := ha
  unfold BD at hb
  obtain ⟨v, hv⟩ := LinearMap.mem_range.1 hb
  refine Submodule.mem_inf.2 ⟨Submodule.mem_map.2 ⟨z, hz, rfl⟩, ?_⟩
  unfold unrH1
  rw [LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap]
  unfold coB1
  refine LinearMap.mem_range.2 ⟨Cd.u.symm (x + v), ?_⟩
  funext g
  apply Cd.u.injective
  have hg := congrFun hab (eG (g : Dw))
  rw [Pi.add_apply, trC_apply_eG, hx _ (hI _ g.2), ← hv] at hg
  show Cd.u (uElt r χ ((g : Dw) : GG) • Cd.u.symm (x + v) - Cd.u.symm (x + v)) = Cd.u ((z : Dw → M) g)
  rw [← hg, map_sub, Cd.u_act, AddEquiv.apply_symm_apply]
  show actD Cd.Ce.L (eG (g : Dw)) (x + v) - (x + v) =
    (actD Cd.Ce.L (eG (g : Dw)) x - x) + (actD Cd.Ce.L (eG (g : Dw)) v - v)
  rw [map_add (f := _)]
  abel

end Conds

end Formalism.MainNotions.N.K.TBb

end
end

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Cyc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem cycW_of : CycW i dc := by
  intro w hw g
  have h1 := Formalism.MainNotions.N.KBKa.cycZ_eq_χQ (D.nbr i w hw) (D.loc (D.nd.l i)) (eW i dc hw g)
  have h2 := (D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw (eW i dc hw g)
  have h3 : ((Br.ι (D.nbr i w hw) (eW i dc hw g) : Dec (F := D.host.E) (D.nd.plOm.1 w)) : GE D.nd) = (g : GE D.nd) := by
    show (((D.nbr i w hw).e.symm ((D.nbr i w hw).e (MulEquiv.subgroupCongr (Dw_idx i dc hw) g)) :
      ↥(Dec (F := D.host.E) (D.nd.plOm.1 w))) : GE D.nd) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [h3] at h1
  show ((((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).χ (eW i dc hw g) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) = _
  rw [h2, ← h1]
  rfl

theorem eW_inert' {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (h : Br.G D.nbr i w hw) (hh : h ∈ Br.inert D.nbr i w hw) :
    (eW i dc hw).symm h ∈ (Ine (F := D.host.E) (Aw i dc (idx i dc w))).subgroupOf (Dw i dc (idx i dc w)) := by
  rw [Subgroup.mem_subgroupOf]
  have hA : Aw i dc (idx i dc w) = D.nd.plOm.1 w := by
    unfold Aw
    rw [plOf_idx i dc (mem_plSet i dc hw)]
  rw [hA]
  exact hh

end Cyc

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem sE_cont (c' : Fin D.R.t) :
    Continuous fun g : GE D.nd => sE i (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) g := by
  have := D.nd.trO i
  have hc1 : Continuous fun g : GE D.nd => (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
    have : (fun g : GE D.nd => (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := funext fun g => by rw [map_inv]
    rw [this]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  have h := hc1.mul (D.nd.chi_cont i ((c' : ℕ) + 1))
  have he : (fun g : GE D.nd => sE i (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) g) =
      fun g => (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) :=
    funext fun g => (chi_ratio (i := i) c' g).symm
  rw [he]
  exact h

theorem epsL_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c' : Fin D.R.t) :
    Continuous fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^
      (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) := by
  have he : (fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^
      (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1)) = fun h => algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))
        ((D.nbr i w hw).eO (sE i (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) (((eW i dc hw).symm h : Dw i dc (idx i dc w)) : GE D.nd))) := by
    funext h
    rw [eO_sE i dc (cycW_of i dc) hw, MulEquiv.apply_symm_apply, map_pow]
  rw [he]
  exact continuous_subtype_val.comp ((D.nbr i w hw).eO_cont.comp
    ((sE_cont i c').comp (continuous_subtype_val.comp (eW_symm_cont i dc hw))))

variable [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]


set_option maxHeartbeats 1000000 in
theorem coefDict_of
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) :
    Nonempty (CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)
      (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1)) := by
  obtain ⟨φ, hφ⟩ := blkTw_of_def hD hN c hc
  have hc0 : c ≠ 0 := by
    intro h
    subst c
    simp at hc
  obtain ⟨c', rfl⟩ : ∃ c', Fin.succ c' = c := Fin.exists_succ_eq.mpr hc0
  exact ⟨coefDictOf i dc Dd (cycW_of i dc) hw c'.succ φ hφ (epsL_cont i dc hw c')⟩

end Dict

section Len

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]


set_option maxHeartbeats 1000000 in
theorem lenMap_of (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hwrow : w ∈ dc.row) (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ))
    (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)
      (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1)) :
    LenMap (Br.PD D.loc D.nbr i w hw) (selfO i hw) (Qcore i dc Dd c (idx i dc w) cB) Cd.Ce cB := by
  have hT := hTB w hw hwrow
  have het : (c : ℕ) - 1 < D.R.t := by
    have := c.2
    omega
  have h2 := trivial_bound_general hT het Cd.Ce
  have hp : (Br.PD D.loc D.nbr i w hw).p = D.nd.l i := Br.PD_p D.loc D.nbr i w hw
  refine lenMap_gen Cd (eW_symm_cont i dc hw) hp ?_ ?_
  · intro z hz hF
    unfold Fc at hF
    split_ifs at hF with h1
    · exact hW_zero Cd (eW_symm_cont i dc hw) (h2.2 (by omega)) (fun h hh => eW_inert' i dc hw h hh) z hz hF
    · exact hW_bot Cd z hz hF
  · intro z hz hH
    unfold Fc
    split_ifs with h1
    · exact hB_zero Cd (eW_symm_cont i dc hw) (h2.2 (by omega)) (eW_inert i dc hw) z hz hH
    · exact hB_bot Cd (eW_symm_cont i dc hw) (h2.1 (by omega)) z hz hH

end Len

section Dict2

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def YtPsi : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
      ∀ Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)
          (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1),
        ∃ Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
            ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL),
          YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
          PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd


set_option maxHeartbeats 4000000 in
theorem tbDict2_of (cB : ℕ)
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hTB : TrivialBoundAtRows i dc r π cB)
    (hY : YtPsi i dc r π Dd) : TBDict2 i dc r π Dd cB := by
  intro w hw hwrow c hcc
  obtain ⟨Cd⟩ := coefDict_of i dc r ρ π g0 eB e₁ s Dd hD hN hw c hcc
  obtain ⟨Y, hY1, hY2⟩ := hY w hw hwrow c hcc Cd
  refine ⟨Y, Cd, hY1, hY2, ?_, ?_⟩
  · exact yLoc_of i dc r π g0 eB e₁ s Dd hD hc c (idx i dc w)
  · exact lenMap_of i dc r π Dd cB hTB hw hwrow c hcc Cd

theorem trivial_bound_target_of_psi (cB : ℕ)
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hTB : TrivialBoundAtRows i dc r π cB)
    (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i) (hY : YtPsi i dc r π Dd) : TBTarget i dc Dd cB :=
  trivial_bound_target_of_dict i dc r π Dd cB hTB hTie (tbDict2_of i dc r ρ π g0 eB e₁ s Dd cB hD hN hc hTB hY)

end Dict2

end Formalism.MainNotions.N.K.TBb

end
