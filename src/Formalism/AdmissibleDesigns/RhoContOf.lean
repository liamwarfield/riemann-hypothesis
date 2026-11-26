module

public import Formalism.AdmissibleDesigns.IsDROfWpIso
public import Formalism.AdmissibleDesigns.TwistedTargetOfInputs
public import Formalism.AdmissibleDesigns.FiniteClassesLocalEq

@[expose] public section

section -- merged from Formalism.AdmissibleDesigns.RhoContOf
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open Classical

namespace Formalism.MainNotions.N.K.Font

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KHf Formalism.MainNotions.N.KDim NumberField IsDedekindDomain Formalism.NG Formalism.BasicNotions

section RhoC

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem rhoCont_of (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    Continuous fun g => rhoO D.nd i ρ π g := by
  have h : (fun g => rhoO D.nd i ρ π g) = fun g => (fun a b => rO D.nd i r π g (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) := by
    funext g
    exact Matrix.ext fun a b => (hN.2.2 g a b).symm
  rw [h]
  exact continuous_pi fun a => continuous_pi fun b => (hc π).matrix_elem _ _

end RhoC

section Lat

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
  (hK : ContinuousMul (FractionRing (D.nd.O i)))
  (hε : Continuous fun g => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i))
  (hM : ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b)

def phiW (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    TrV (eK (D.nbr i _ hn)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R) n) ≃ₗ[Br.LL D.nbr i _ hn]
      (Fin D.R.r → Br.LL D.nbr i _ hn) where
  toFun v a := eK (D.nbr i _ hn) ((v : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 a))
  invFun w := (show {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i) from
    fun b => (eK (D.nbr i _ hn)).symm (w ((H0.e0 (D := D)).symm b)))
  map_add' u v := funext fun a => map_add (eK (D.nbr i _ hn)) _ _
  map_smul' c v := funext fun a => by
    show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm c * _) = c * _
    rw [map_mul, RingEquiv.apply_symm_apply]
  left_inv v := by
    funext b
    show (eK (D.nbr i _ hn)).symm (eK (D.nbr i _ hn) (_ : FractionRing (D.nd.O i))) = _
    rw [RingEquiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv w := by
    funext a
    show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm (w ((H0.e0 (D := D)).symm (H0.e0 a)))) = w a
    rw [RingEquiv.apply_symm_apply, Equiv.symm_apply_apply]

theorem wpIso_dat (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    WpIso i dc ρ π n hn (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT := by
  refine ⟨phiW i dc n hn, fun g x => funext fun a => ?_⟩
  show eK (D.nbr i _ hn) ((KLat.matK (Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)))).mulVec
      (x : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 a)) =
    ∑ b, Br.loc D.nbr i _ hn (WpO D.nd i ρ π) g a b * eK (D.nbr i _ hn) ((x : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 b))
  refine (congrArg (eK (D.nbr i _ hn)) (KLat.matK_mulVec (Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)))
    (show {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i) from x) (H0.e0 a))).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (Equiv.sum_comp (H0.e0 (D := D)) _).symm.trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [Algebra.smul_def, map_mul, loc_apply, H0.unipotent_block_zero_entry hD hN]

end Lat

section RowDR2

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
  (hK : ContinuousMul (FractionRing (D.nd.O i)))
  (hε : Continuous fun g => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i))
  (hM : ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b)

theorem isDR_dat (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn))
      (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT (Br.iota D.nbr i _ hn)) :=
  isDR_of_wpIso i dc r ρ π hF hG2 hDec hCont (rhoCont_of i r ρ π hCont hN) n hn _ (wpIso_dat i dc r ρ π g0 eB e₁ s Dd hK hε hM hD hN n hn)

end RowDR2

end Formalism.MainNotions.N.K.Font

end
end

section -- merged from Formalism.AdmissibleDesigns.MsWApply
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.StC

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf Formalism.MainNotions.N.K.TBa Formalism.MainNotions.N.KLift

section EmbRow

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))

theorem msW_apply {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i)
    (g : Br.G D.nbr i w hw) (a b : Fin D.R.nV) :
    MsW i r hw x g a b = eS i hw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (rTwO D.nd i r x ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) a b)) := by
  rw [msW_entry]
  first
  | rfl
  | simp [Matrix.map_apply]


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem embRW_of {T : Subalgebra (D.nd.O i) (D.nd.X i → D.nd.O i)} {π : D.nd.X i} {ε : GE D.nd →* (D.nd.O i)ˣ}
    {g0 : GE D.nd} {eB e₁ s : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) T (Formalism.MainNotions.N.RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) ε g0 eB e₁ s Dd)
    [Module.Finite (D.nd.O i) Dd.R']
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) : EmbRW i dc r Dd hw := by
  obtain ⟨hr', hsm, hχ⟩ := ringDef_lift i r Dd hD
  have := nzsd_R' i Dd
  have : Module.Free (D.nd.O i) Dd.R' := Module.free_of_finite_type_torsion_free'
  set ρP := resRep (lRep (D.nd.O i) Dd.r Dd.χ) (Dw i dc (idx i dc w)) with hρP
  set e := eS i hw
  let κ : Dd.R' →ₗ[D.nd.O i] (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) :=
    (Dd.R').val.toLinearMap
  have hκ : Function.Injective κ := Subtype.val_injective
  let Λ := liftK (V := Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) κ
  have hΛs : ∀ m (s : nonZeroDivisors (D.nd.O i)), (s : D.nd.O i) • Λ (LocalizedModule.mk m s) = κ m := by
    intro m s
    rw [← map_smul, smul_mk, liftK_mkK]
  have hΛi : ∀ v, Λ v = 0 → v = 0 := by
    intro v hv
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h1 := hΛs m s
      rw [hv, smul_zero] at h1
      rw [hκ (h1.symm.trans (map_zero κ).symm), LocalizedModule.zero_mk]
  have hΛe : ∀ (γ : ↥(Dw i dc (idx i dc w))) v, Λ (locRep ρP γ v) =
      ((Formalism.NG.uElt Dd.r Dd.χ (γ : GE D.nd) : Dd.R') :
        Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * Λ v := by
    intro γ v
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h0 : locRep ρP γ (LocalizedModule.mk m s) = LocalizedModule.mk (ρP γ m) s := LocalizedModule.map_mk _ _ _ _
      rw [h0]
      apply smul_cancel s
      rw [hΛs, ← mul_smul_comm, hΛs]
      rfl
  let Ψ : Dd.X' × Fin D.R.nV → TrV e (MK (O := D.nd.O i) Dd.R') →ₗ[↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1]
      (Fin D.R.nV → ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1) := fun q =>
    { toFun := fun v a => e ((Λ (untr e v)) q.1 a q.2)
      map_add' := fun v v₂ => funext fun a => by
        show e ((Λ (untr e v + untr e v₂)) q.1 a q.2) = _
        rw [map_add (f := _)]
        simp [map_add (f := _)]
      map_smul' := fun c v => funext fun a => by
        show e ((Λ (e.symm c • untr e v)) q.1 a q.2) = c * e ((Λ (untr e v)) q.1 a q.2)
        rw [smulK]
        simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul] }
  haveI : FiniteDimensional (↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1) (TrV e (MK (O := D.nd.O i) Dd.R')) :=
    finDim_of_lat (Ow := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (Qp := ℚ_[D.nd.l i])
      (latOf e (selfO i hw) mkK (eW i dc hw).symm.toMonoidHom (heS i hw) (locRep ρP) ρP mkK_inj
        (fun γ m => (locRep_mkK _ γ m).symm) mkK_span)
  have hinj : ∀ v, (∀ q, Ψ q v = 0) → v = 0 := by
    intro v hv
    have h0 : Λ (untr e v) = 0 := by
      funext x'
      ext a b
      have := congrFun (hv (x', b)) a
      simpa [Ψ] using this
    exact hΛi _ h0
  obtain ⟨m, xs, hxs⟩ := fin_sel Ψ hinj
  refine ⟨m, fun a => Dd.p (xs a).1, LinearMap.pi fun a => Ψ (xs a), fun v v' hvv => ?_, fun g v => funext fun a => ?_⟩
  · rw [← sub_eq_zero]
    refine hxs _ fun a => ?_
    rw [map_sub, sub_eq_zero]
    exact congrFun hvv a
  · have key : ∀ (q : Dd.X' × Fin D.R.nV) (γ : ↥(Dw i dc (idx i dc w))),
        (γ : GE D.nd) = ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) → ∀ b,
        e ((Λ (locRep ρP γ (untr e v))) q.1 b q.2) = (MsW i r hw (Dd.p q.1) g).mulVec (Ψ q v) b := by
      intro q γ hγ b
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΛe, Pi.mul_apply, hγ, uElt_at i r Dd hr' hsm hχ, Matrix.mul_apply, map_sum]
      simp only [Matrix.mulVec, dotProduct, msW_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [Ψ, Matrix.map_apply, map_mul]
      exact Or.inl rfl
    funext b
    exact key (xs a) ((eW i dc hw).symm g) rfl b

end EmbRow

end Formalism.MainNotions.N.K.StC

end
end
