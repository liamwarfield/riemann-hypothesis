module

public import Formalism.AdmissibleDesigns.H1MapMemLcH1
public import Formalism.AdmissibleDesigns.EKSymmCont
public import Formalism.AdmissibleDesigns.FiniteClassesRowEqGeneric
public import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous
public import Formalism.AdmissibleDesigns.TrivialBoundTargetOfDict

@[expose] public section

section -- merged from Formalism.AdmissibleDesigns.KernelLengthHigherColumns
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.H0

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.NG Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Gen
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def kogTo (k : ℕ) : KOG O k →ₗ[O] (Fin k → KO O) :=
  Submodule.liftQ _ (LinearMap.compLeft (1 : Submodule O (FractionRing O)).mkQ (Fin k)) (by
    rintro _ ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    funext a
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_one.2 ⟨u a, rfl⟩))

theorem kogTo_mk (k : ℕ) (v : Fin k → FractionRing O) :
    kogTo k (Submodule.Quotient.mk v : KOG O k) = fun a => (Submodule.Quotient.mk (v a) : KO O) := rfl

theorem kogTo_bijective (k : ℕ) : Function.Bijective (kogTo (O := O) k) := by
  constructor
  · intro x y hxy
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [kogTo_mk, kogTo_mk] at hxy
    refine (Submodule.Quotient.eq _).2 ?_
    have h : ∀ a, v a - w a ∈ (1 : Submodule O (FractionRing O)) := fun a =>
      (Submodule.Quotient.eq _).1 (congrFun hxy a)
    choose u hu using fun a => Submodule.mem_one.1 (h a)
    exact ⟨u, funext fun a => hu a⟩
  · intro f
    choose c hc using fun a => Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (f a)
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    rw [kogTo_mk]
    funext a
    exact hc a

def kogEq (k : ℕ) : KOG O k ≃ₗ[O] (Fin k → KO O) := LinearEquiv.ofBijective (kogTo k) (kogTo_bijective k)

theorem kogEq_apply (k : ℕ) (x : KOG O k) : kogEq k x = kogTo k x := rfl

theorem kogEq_WKG {Γ : Type} [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) (x : KOG O k) (a : Fin k) :
    kogEq k (WKG M g x) a = ∑ b, M g a b • kogEq k x b := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show WKG M g (Submodule.Quotient.mk v : KOG O k) = Submodule.Quotient.mk _ from rfl]
  simp only [kogEq_apply, kogTo_mk]
  rw [← Submodule.mkQ_apply]
  trans Submodule.mkQ (1 : Submodule O (FractionRing O)) (∑ b, M g a b • v b)
  · congr 1
    simp only [LinearMap.restrictScalars_apply]
    unfold matRep mapM
    simp [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Algebra.smul_def]
  · rw [map_sum]
    simp only [map_smul, Submodule.mkQ_apply]

end Gen

structure FinCore : Prop where
  w : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.admG2 i r ρ π →
    ∀ w ∈ placesOver D.host.E (D.nd.l i),
      Module.length (D.nd.O i) ↥(Representation.invariants ((Br.WKO i ρ π).comp (decS D.nd w))) < ⊤
  e : ∀ (D : D7) (i : D.nd.Loc), ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ e : ℕ, 0 < e →
    Module.length (D.nd.O i) ↥(Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw D.nd i (e : ℤ)).comp (decS D.nd w))) < ⊤

def e0 {D : D7} : Fin D.R.r ≃ {a // RepresentationBoundsCohomology.blk D.R a = 0} := RepresentationBoundsCohomology.blockZeroEquiv D.R.r D.R.t

theorem length_ker_le {O G M M' : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (S : Submodule O M) (ρ' : Representation O G M') (f : M →ₗ[O] M') (hf : Function.Injective f)
    (h : ∀ m ∈ S, ∀ g, ρ' g (f m) = f m) :
    Module.length O ↥S ≤ Module.length O ↥(Representation.invariants ρ') := by
  let φ : S →ₗ[O] ↥(Representation.invariants ρ') :=
    LinearMap.codRestrict (Representation.invariants ρ') (f ∘ₗ S.subtype)
      (fun m => (Representation.mem_invariants ρ' _).2 fun g => h m m.2 g)
  exact Module.length_le_of_injective φ
    (fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab)))

section Rec

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

def toKOG : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0 →ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r where
  toFun m := (kogEq D.R.r).symm (fun a => m (e0 a))
  map_add' a b := by rw [← map_add (f := _)]; rfl
  map_smul' c a := by rw [RingHom.id_apply, ← map_smul]; rfl

theorem toKOG_injective : Function.Injective (toKOG i Dd) := by
  intro m m' hm
  have h' : (fun a => m (e0 a)) = (fun a => m' (e0 a)) := (kogEq D.R.r).symm.injective hm
  funext j
  obtain ⟨a, rfl⟩ := (e0 (D := D)).surjective j
  exact congrFun h' a

variable {i r ρ π g0 eB e₁ s Dd} in
theorem unipotent_block_zero_entry (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (g : GE D.nd) (a b : Fin D.R.r) :
    Dd.ρk 0 (uElt Dd.r Dd.χ g) (e0 a) (e0 b) = WpO D.nd i ρ π g a b := by
  have hE := ShaT.evS_of hD
  rw [← hE.ρk_eval]
  show Dd.ρπ (uElt Dd.r Dd.χ g) (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) = _
  apply IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
  have h := congrFun (congrFun (hE.ρπ_eval (uElt Dd.r Dd.χ g)) (Fin.castAdd D.R.t a)) (Fin.castAdd D.R.t b)
  refine Eq.trans h ?_
  rw [uElt, hE.smul_eval, hE.r_eval, hE.pπ, ← map_inv, hE.chi_eval, map_inv]
  show algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) _ *
    algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (rO D.nd i r π g (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b)) = _
  rw [hN.2.2 g a b, ← map_mul]
  rfl

variable [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

variable {i r ρ π g0 eB e₁ s Dd} in
theorem toKOG_equiv (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (g : GE D.nd) (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) :
    toKOG i Dd (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ g m) = Br.WKO i ρ π g (toKOG i Dd m) := by
  apply (kogEq D.R.r).injective
  funext a
  simp only [toKOG, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]
  unfold Br.WKO
  rw [kogEq_WKG]
  simp only [LinearEquiv.apply_symm_apply, ← unipotent_block_zero_entry hD hN]
  have hs := Equiv.sum_comp (e0 (D := D)) (fun j => Dd.ρk 0 (uElt Dd.r Dd.χ g) (e0 a) j • m j)
  rw [hs]
  rfl

def h0d (w : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) (LinearMap.ker (colDO (O := D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ
    ((decs D.host.E (Aw i dc)) w)))

theorem invariants_display_match (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) : LeTwistInvariantsAtColumns i ρ π dc (h0d i dc Dd) := by
  unfold LeTwistInvariantsAtColumns
  intro n hn
  unfold twistInvariantsLength h0d
  refine length_ker_le _ _ (toKOG i Dd) (toKOG_injective i Dd) ?_
  intro m hm g
  rw [MonoidHom.comp_apply, ← toKOG_equiv hD hN]
  congr 1
  rw [LinearMap.mem_ker] at hm
  unfold colDO at hm
  simp only [LinearMap.coe_mk, AddHom.coe_mk] at hm
  exact sub_eq_zero.1 (congrFun hm g)

variable {i r ρ π g0 eB e₁ s Dd} in
theorem kernel_length_higher_columns [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (c : Fin (D.R.t + 1)) (hc : 2 ≤ (c : ℕ)) :
    ∀ w ∈ Finset.univ.image (colIdx i dc), Module.length (D.nd.O i)
      (LinearMap.ker (colDO (O := D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ ((decs D.host.E (Aw i dc)) w))) ≤
      invariantsLengthSup i dc := by
  intro w hw
  rw [cols_eq] at hw
  have hk : (c : ℕ) - 1 ∈ Finset.Ioo 0 D.R.t := Finset.mem_Ioo.2 ⟨by omega, by have := c.2; omega⟩
  refine le_H0N i dc hw hk ?_
  obtain ⟨φ, hφ⟩ := ShaT.blkTw_of_def hD hN c (by omega)
  let κ : KO (D.nd.O i) ≃ₗ[D.nd.O i] KmodO (D.nd.O i) := Submodule.quotEquivOfEq _ _ Submodule.one_eq_range
  refine length_ker_le _ _ ((φ.trans κ).toLinearMap) (φ.trans κ).injective (fun m hm g => ?_)
  have h1 : uElt Dd.r Dd.χ g.1 • m - m = 0 := congrFun (LinearMap.mem_ker.1 hm) g
  have h3 : uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ g.1 m = m := sub_eq_zero.1 h1
  have h2 := hφ g.1 m
  rw [h3] at h2
  show ((((Formalism.MainNotions.N.Glob.epsO D.nd i) ^ (-((((c : ℕ) - 1 : ℕ)) : ℤ))) g.1 : (D.nd.O i)ˣ) : D.nd.O i) • κ (φ m) = κ (φ m)
  rw [← map_smul]
  congr 1
  refine Eq.trans ?_ h2.symm
  show _ = ((((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp
    (ShaT.cycE i ^ (-((((c : ℕ) - 1 : ℕ)) : ℤ)))) g.1 : (D.nd.O i)ˣ) : D.nd.O i) • φ m
  congr 2
  simp only [MonoidHom.comp_apply, MonoidHom.zpow_apply, map_zpow]
  rfl

end Rec

theorem theorem_of_display_and_g2 [hFin : Fact FinCore] {D : D7} (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (hD : D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → Br.sFin D.loc D.nbr i ρ π →
      (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
      SelmerLengthInequality i ρ π dc lenRow e' cB)
    (g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (g5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) : TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB :=
  theorem_of_display i ρ π dc lenRow e' cB hD
    (fun w hw => hFin.out.w D i r ρ π g2 w ((dc.cover w).1 (Or.inr hw)))
    (fun w hw e he => hFin.out.e D i w ((dc.cover w).1 (Or.inr hw)) e (Finset.mem_Ioo.1 he).1) g5x

end Formalism.MainNotions.N.K.H0

end
end

section -- merged from Formalism.AdmissibleDesigns.MsContW
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem msContW (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) : K.TBa.MsContW (i := i) (r := r) hw :=
  fun x => locC_cont i r hc hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) x

end Formalism.MainNotions.N.KOrb

end
end

section -- merged from Formalism.AdmissibleDesigns.RowTopOf
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT' w)] [∀ w, TopologicalSpace (VT' w)] [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)]
  {T₁ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁]

def RowTop1 : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    ∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hn g)))) →
        Continuous c

theorem rowTop_of
    (hT : ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
      KBKa.TopMatch (eK (D.nbr i _ hn)) (VT' n))
    (h1 : RowTop1 i dc (T₁ := T₁)) : RowTop i dc VT' (T₁ := T₁) := by
  intro n hn hpl
  refine ⟨fun c hc => ?_, h1 n hn hpl⟩
  have h := hT n hn hpl
  have h2 := (KBKa.cont_iff _ h _).1 hc
  have h3 : Continuous fun g => c (Br.iota D.nbr i _ hpl g) := h2
  obtain ⟨hm, hhm⟩ := KBKa.iotaHomeo_rec (i := i) (dc := dc) hpl
  have hc' : c = (fun g => c (Br.iota D.nbr i _ hpl g)) ∘ hm.symm := by
    funext x
    simp only [Function.comp, ← hhm]
    exact congrArg c (hm.apply_symm_apply x).symm
  rw [hc']
  exact h3.comp hm.symm.continuous

end Rec

end Formalism.MainNotions.N.KRow

end
end

section -- merged from Formalism.AdmissibleDesigns.LocCont
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i)

theorem wpO_cont (hρ : Continuous fun g => rhoO D.nd i ρ π g) : Continuous (WpO D.nd i ρ π) := by
  have hχ : Continuous fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
    have he : (fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      simp [chiU, map_inv]
    rw [he]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  show Continuous fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) • rhoO D.nd i ρ π g
  exact hχ.smul hρ

theorem loc_cont {k : ℕ} {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous M) :
    Continuous ⇑(Br.loc D.nbr i w hw M) := by
  unfold Br.loc Br.locM Br.locO mapM
  simp only [MonoidHom.coe_comp]
  refine Continuous.comp ?_ (Continuous.comp (Continuous.comp ?_ (Continuous.comp hM ?_)) ?_)
  · first
      | exact continuous_id.matrix_map continuous_subtype_val
      | exact continuous_id.matrix_map continuous_induced_dom
  · exact continuous_id.matrix_map (D.nbr i w hw).eO_cont
  · exact continuous_subtype_val
  · first
      | exact (D.nbr i w hw).e_symm_cont
      | exact continuous_subtype_val.comp (D.nbr i w hw).e_symm_cont

theorem contW_of (hρ : Continuous fun g => rhoO D.nd i ρ π g) (l : K.Col i dc) :
    KDim.ContW (i := i) (dc := dc) (ρ := ρ) (π := π) l := by
  intro v
  have hL := loc_cont i (KDim.col_over i dc l) (WpO D.nd i ρ π) (wpO_cont i ρ π hρ)
  have h2 : Continuous fun g => Matrix.mulVec (Br.loc D.nbr i _ (KDim.col_over i dc l) (WpO D.nd i ρ π) g) v :=
    hL.matrix_mulVec continuous_const
  refine h2.congr fun g => ?_
  first
    | rfl
    | simp [KDim.repW, matRep, Matrix.toLinAlgEquiv'_apply]

end Formalism.MainNotions.N.KOrb

end
end

section -- merged from Formalism.AdmissibleDesigns.TrivialBoundAtRowsOfAdmTB
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)

theorem trivialBoundAtRows_of_admTB (cB : ℕ) (hG : SelfGood i) (h : Formalism.MainNotions.EmbeddingTypes.admTB i r π dc cB) : TrivialBoundAtRows i dc r π cB :=
  fun w hw hrow => h w hw hrow (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (hG w hw)

end Formalism.MainNotions.N.K.TB

end
end

section -- merged from Formalism.AdmissibleDesigns.KoEquivSmul
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB

section Eps

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

def epsHom (e : ℕ) : G →* Matrix (Fin 1) (Fin 1) LL where
  toFun := Formalism.MainNotions.N.epsTw PD (LL := LL) e
  map_one' := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp [Formalism.MainNotions.N.epsTw]
  map_mul' g h := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp [Formalism.MainNotions.N.epsTw, Matrix.mul_apply, mul_pow]
    ring

theorem matRep_eps (e : ℕ) (g : G) (v : Fin 1 → LL) :
    Formalism.MainNotions.N.matRep (epsHom PD (LL := LL) e) g v =
      fun _ => (algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp)) ^ e * v 0 := by
  funext j
  change Matrix.mulVec (Formalism.MainNotions.N.epsTw PD (LL := LL) e g) v j = _
  simp [Matrix.mulVec, dotProduct, Formalism.MainNotions.N.epsTw]

variable {PD}

@[reducible] def twLat (hinj : Function.Injective (algebraMap O LL)) (ε' : G → O)
    (hε : ∀ g, algebraMap O LL (ε' g) = algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp)) (e : ℕ)
    (hcont : Continuous fun g => (algebraMap O LL (ε' g)) ^ e) : TwLat PD LL O e where
  V := Fin 1 → LL
  ρ := Formalism.MainNotions.N.matRep (epsHom PD e)
  L :=
    { T := Formalism.MainNotions.N.stdG O LL 1
      stable := by
        intro g x hx
        obtain ⟨u, rfl⟩ := hx
        refine ⟨fun _ => (ε' g) ^ e * u 0, ?_⟩
        rw [matRep_eps]
        funext j
        simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply, map_mul, map_pow, hε]
      fg := (Formalism.MainNotions.N.stdLatG hinj (1 : G →* Matrix (Fin 1) (Fin 1) O)).fg
      free := (Formalism.MainNotions.N.stdLatG hinj (1 : G →* Matrix (Fin 1) (Fin 1) O)).free
      span := (Formalism.MainNotions.N.stdLatG hinj (1 : G →* Matrix (Fin 1) (Fin 1) O)).span }
  cont := by
    intro x
    have h : (fun g => Formalism.MainNotions.N.matRep (epsHom PD (LL := LL) e) g x) =
        fun g => fun _ : Fin 1 => (algebraMap O LL (ε' g)) ^ e * x 0 := by
      funext g
      rw [matRep_eps, hε]
    rw [h]
    exact continuous_pi fun _ => hcont.mul continuous_const
  mat := by
    refine ⟨LinearEquiv.refl LL _, fun g v => rfl, fun v => ⟨?_, ?_⟩⟩
    · rintro ⟨u, rfl⟩ j
      exact ⟨u j, rfl⟩
    · intro hv
      choose u hu using hv
      exact ⟨u, funext fun j => hu j⟩

theorem actD_twLat (hinj : Function.Injective (algebraMap O LL)) (ε' : G → O)
    (hε : ∀ g, algebraMap O LL (ε' g) = algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp)) (e : ℕ)
    (hcont : Continuous fun g => (algebraMap O LL (ε' g)) ^ e) (h : G)
    (x : (twLat hinj ε' hε e hcont).V ⧸ (twLat hinj ε' hε e hcont).L.T) :
    actD (twLat hinj ε' hε e hcont).L h x = (ε' h ^ e) • x := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    unfold actD
    refine (congrArg Submodule.Quotient.mk
      (?_ : (twLat hinj ε' hε e hcont).ρ h v = (ε' h ^ e) • v)).trans
      (Submodule.Quotient.mk_smul _ _ _)
    funext j
    show Formalism.MainNotions.N.matRep (epsHom PD (LL := LL) e) h v j = (ε' h ^ e) • v j
    rw [matRep_eps, Algebra.smul_def, map_pow, hε, Subsingleton.elim j 0]

end Eps

section KO

variable {O' : Type} [CommRing O'] [IsDomain O'] {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
  (σ : O' ≃+* O) (eK : FractionRing O' ≃+* LL)
  (heK : ∀ c : O', eK (algebraMap O' (FractionRing O') c) = algebraMap O LL (σ c))

def kVec : FractionRing O' →ₛₗ[σ.toRingHom] (Fin 1 → LL) where
  toFun x := fun _ => eK x
  map_add' x y := by
    funext j
    simp
  map_smul' c x := by
    funext j
    simp only [Algebra.smul_def, map_mul, heK, Pi.smul_apply]
    rfl

def vecK : (Fin 1 → LL) →ₛₗ[σ.symm.toRingHom] FractionRing O' where
  toFun v := eK.symm (v 0)
  map_add' u v := by simp
  map_smul' c v := by
    apply eK.injective
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, RingEquiv.apply_symm_apply, heK]
    exact congrArg (fun y => algebraMap O LL y * v 0) (σ.apply_symm_apply c).symm

theorem kVec_le : (1 : Submodule O' (FractionRing O')) ≤ (Formalism.MainNotions.N.stdG O LL 1).comap (kVec σ eK heK) := by
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hx
  rw [Submodule.mem_comap]
  refine ⟨fun _ => σ c, ?_⟩
  funext j
  show algebraMap O LL (σ c) = eK (algebraMap O' (FractionRing O') c)
  exact (heK c).symm

def koTo : KO O' →ₛₗ[σ.toRingHom] ((Fin 1 → LL) ⧸ Formalism.MainNotions.N.stdG O LL 1) :=
  Submodule.mapQ _ _ (kVec σ eK heK) (kVec_le σ eK heK)

def koEquiv : KO O' ≃+ ((Fin 1 → LL) ⧸ Formalism.MainNotions.N.stdG O LL 1) where
  toFun := koTo σ eK heK
  invFun := Submodule.mapQ _ _ (vecK σ eK heK) (by
    rintro _ ⟨u, rfl⟩
    refine Submodule.mem_one.2 ⟨σ.symm (u 0), ?_⟩
    apply eK.injective
    show eK (algebraMap O' (FractionRing O') (σ.symm (u 0))) = eK (eK.symm (algebraMap O LL (u 0)))
    rw [heK, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply])
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      show Submodule.Quotient.mk (eK.symm (eK x)) = _
      rw [RingEquiv.symm_apply_apply]
  right_inv v := by
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      show Submodule.Quotient.mk (fun _ => eK (eK.symm (v 0))) = _
      congr 1
      funext j
      rw [RingEquiv.apply_symm_apply, Subsingleton.elim j 0]
  map_add' x y := map_add _ x y

theorem koEquiv_smul (a : O') (x : KO O') : koEquiv σ eK heK (a • x) = σ a • koEquiv σ eK heK x := by
  show koTo σ eK heK (a • x) = σ a • koTo σ eK heK x
  exact (koTo σ eK heK).map_smulₛₗ a x

end KO

end Formalism.MainNotions.N.K.TBb

end
end
