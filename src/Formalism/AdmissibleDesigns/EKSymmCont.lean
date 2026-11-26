module

public import Formalism.AdmissibleDesigns.CoboundaryMemFiniteClasses
public import Formalism.AdmissibleDesigns.FgTopContinuousLinearMap
public import Formalism.AdmissibleDesigns.DisplayForms
public import Formalism.AdmissibleDesigns.MemImageOfTensorSum
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes

@[expose] public section

section -- merged from Formalism.AdmissibleDesigns.EKSymmCont
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Module Formalism.MainNotions.N.KHf Formalism.NG

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O]
  {LL : Type} [Field LL] [TopologicalSpace LL] (e : FractionRing O ≃+* LL)

abbrev modO (V : Type) [AddCommGroup V] [Module (FractionRing O) V] : Module O (TrV e V) :=
  Module.compHom (TrV e V) (e.toRingHom.comp (algebraMap O (FractionRing O)))

theorem contSMulO (hO : Continuous fun c : O => e (algebraMap O (FractionRing O) c)) (V : Type)
    [AddCommGroup V] [Module (FractionRing O) V] :
    letI := modO e V
    ContinuousSMul O (TrV e V) := by
  letI := modO e V
  exact ⟨(ModuleTopology.continuousSMul LL (TrV e V)).continuous_smul.comp
    ((hO.comp continuous_fst).prodMk continuous_snd)⟩

variable {A : Type} [Ring A] [Algebra O A]
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [Module A V]

def smulL (hP : ∀ (c : O) (v : V), (algebraMap O A c) • v = c • v) (v : V) :
    letI := modO e V
    A →ₗ[O] TrV e V :=
  letI := modO e V
  { toFun := fun a => (a • v : V)
    map_add' := fun a b => add_smul a b v
    map_smul' := fun c a => by
      show (c • a) • v = e.symm (e (algebraMap O (FractionRing O) c)) • (a • v : V)
      rw [RingEquiv.symm_apply_apply, algebraMap_smul, Algebra.smul_def, mul_smul, hP] }

theorem smul_cont [TopologicalSpace A] [IsModuleTopology O A]
    (hO : Continuous fun c : O => e (algebraMap O (FractionRing O) c))
    (hP : ∀ (c : O) (v : V), (algebraMap O A c) • v = c • v) (v : V) :
    Continuous fun a : A => (show TrV e V from (a • v : V)) := by
  letI := modO e V
  haveI := contSMulO e hO V
  haveI : ContinuousAdd (TrV e V) := ModuleTopology.continuousAdd LL (TrV e V)
  exact (IsModuleTopology.continuous_of_linearMap (R := O) (smulL e hP v) :)

theorem orbit_cont {G Γ : Type} [Group G] [TopologicalSpace G] [Group Γ] [TopologicalSpace Γ]
    (ι : G →* Γ) (hι : Continuous ι) [TopologicalSpace A] [IsModuleTopology O A]
    (u : Γ → A) (hu : Continuous u) (ρ : Representation O Γ V) (hρ : ∀ g v, ρ g v = u g • v)
    (hO : Continuous fun c : O => e (algebraMap O (FractionRing O) c))
    (hP : ∀ (c : O) (v : V), (algebraMap O A c) • v = c • v) (v : TrV e V) :
    Continuous fun g => repL e ρ ι g v := by
  refine ((smul_cont e hO hP v).comp (hu.comp hι)).congr fun g => ?_
  show u (ι g) • (show V from v) = ρ (ι g) v
  exact (hρ _ _).symm

end Gen

section Rec

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem eK_alg_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Continuous fun c : D.nd.O i => eK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c) := by
  have h : (fun c : D.nd.O i => eK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c)) =
      fun c => algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) ((D.nbr i w hw).eO c) :=
    funext fun c => by rw [eK_apply, Br.toLLK_alg]
  rw [h]
  exact continuous_subtype_val.comp (D.nbr i w hw).eO_cont

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem uElt_cont_n
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (n : ℕ) :
    letI := K.Topo.rTopology (D.nd.O i) Dd.R'
    Continuous fun g : ↥(Γn i dc n) => uElt Dd.r Dd.χ (g : GE D.nd) := by
  letI := K.Topo.rTopology (D.nd.O i) Dd.R'
  exact (K.Topo.uElt_cont (hD := hD) (hc := hc)).comp continuous_subtype_val

theorem orbC_uRep
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
    {V : Type} [AddCommGroup V] [Module Dd.R' V] [Module (D.nd.O i) V] [Module (FractionRing (D.nd.O i)) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] [SMulCommClass Dd.R' (D.nd.O i) V]
    (hP : ∀ (c : D.nd.O i) (v : V), (algebraMap (D.nd.O i) Dd.R' c) • v = c • v) (n : ℕ) :
    OrbC i dc (resRep (uRep (D.nd.O i) (M := V) Dd.r Dd.χ) (Γn i dc n)) := by
  intro hn v
  letI := K.Topo.rTopology (D.nd.O i) Dd.R'
  haveI : IsModuleTopology (D.nd.O i) Dd.R' := K.Topo.rTop_isModuleTopology (D.nd.O i) Dd.R'
  have hι : Continuous (Br.iota D.nbr i _ hn) := (D.nbr i _ hn).e_symm_cont.congr fun g => rfl
  exact orbit_cont (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) hι
    (fun g : ↥(Γn i dc n) => uElt Dd.r Dd.χ (g : GE D.nd)) (uElt_cont_n i dc r π g0 eB e₁ s Dd hD hc n)
    _ (fun g v => rfl) (eK_alg_cont i _) hP v

theorem orbC_repE
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (x' : Dd.X') (n : ℕ) :
    letI := evalModO i (R' := Dd.R') x'
    haveI := evalTower i (R' := Dd.R') x'
    OrbC i dc (repE i dc Dd.r Dd.χ x' n) := by
  letI := evalModO i (R' := Dd.R') x'
  haveI := evalTower i (R' := Dd.R') x'
  haveI := evalComm i (R' := Dd.R') x'
  haveI := smulComm_O i (A := Dd.R') (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
  exact orbC_uRep i dc r π g0 eB e₁ s Dd hD hc (fun c v => evalScalar i x' c v) n

theorem latM_alg {n : Type} [Fintype n] [DecidableEq n] (ρ : Dd.R' →ₐ[D.nd.O i] Matrix n n (D.nd.O i))
    (c : D.nd.O i) (v : Formalism.RepresentationBoundsCohomology.SF.LatM (D.nd.O i) (FractionRing (D.nd.O i)) n ρ.toRingHom) :
    (algebraMap (D.nd.O i) Dd.R' c) • v = c • v := by
  funext j
  show ∑ k, (ρ (algebraMap (D.nd.O i) Dd.R' c)) j k • v k = c • v j
  rw [AlgHom.commutes]
  simp [Matrix.algebraMap_matrix_apply, Finset.sum_ite_eq, ite_smul]

end Rec

section Homeo

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem eK_cont :
    letI := K.Topo.fracTopology (D.nd.O i)
    Continuous (eK (D.nbr i w hw)) := by
  letI := K.Topo.fracTopology (D.nd.O i)
  haveI := K.Topo.fracTop_addGroup_O (D := D) i
  have hemb := (K.Topo.fracTop_O (D := D) i).1
  refine continuous_of_continuousAt_zero (eK (D.nbr i w hw)).toAddMonoidHom ?_
  show ContinuousAt (eK (D.nbr i w hw)) 0
  rw [← map_zero (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))), ← hemb.continuousAt_iff]
  exact (eK_alg_cont i hw).continuousAt

theorem eK_symm_val (z : Br.Ow (D.nbr i w hw)) :
    (eK (D.nbr i w hw)).symm (z : Br.LLw (D.nbr i w hw)) =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((D.nbr i w hw).eO.symm z) := by
  rw [RingEquiv.symm_apply_eq, eK_apply, Br.toLLK_alg, RingEquiv.apply_symm_apply]
  rfl

theorem eK_symm_cont :
    letI := K.Topo.fracTopology (D.nd.O i)
    Continuous (eK (D.nbr i w hw)).symm := by
  letI := K.Topo.fracTopology (D.nd.O i)
  haveI := K.Topo.fracTop_addGroup_O (D := D) i
  have hemb := (K.Topo.fracTop_O (D := D) i).1
  have hOemb : Topology.IsOpenEmbedding
      (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))) :=
    ⟨Topology.IsEmbedding.subtypeVal, ReciprocityTheory.ChartRestriction.T2.GlobAlg.isOpen_range_OL (D.nbr i w hw).LL⟩
  refine continuous_of_continuousAt_zero (eK (D.nbr i w hw)).symm.toAddMonoidHom ?_
  show ContinuousAt (eK (D.nbr i w hw)).symm 0
  rw [← map_zero (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))), ← hOemb.continuousAt_iff]
  have hfun : ((eK (D.nbr i w hw)).symm ∘ algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))) =
      fun z => algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((D.nbr i w hw).eO.symm z) :=
    funext fun z => eK_symm_val i hw z
  rw [hfun]
  exact (hemb.continuous.comp (D.nbr i w hw).eO_symm_cont).continuousAt

theorem homeoK :
    letI := K.Topo.fracTopology (D.nd.O i)
    KBKa.HomeoK (eK (D.nbr i w hw)) := by
  exact ⟨eK_cont i hw, eK_symm_cont i hw⟩

theorem topMatch_pi (n : Type) [Finite n] :
    letI := K.Topo.fracTopology (D.nd.O i)
    KBKa.TopMatch (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i)) := by
  letI := K.Topo.fracTopology (D.nd.O i)
  haveI := K.Topo.fracTop_addGroup_O (D := D) i
  letI τ : TopologicalSpace (TrV (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i))) :=
    (Pi.topologicalSpace : TopologicalSpace (n → FractionRing (D.nd.O i)))
  let φ : (n → Br.LLw (D.nbr i w hw)) ≃L[Br.LLw (D.nbr i w hw)]
      TrV (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i)) :=
    { toFun := fun v j => (eK (D.nbr i w hw)).symm (v j)
      invFun := fun x j => eK (D.nbr i w hw) (x j)
      left_inv := fun v => funext fun j => (eK (D.nbr i w hw)).apply_symm_apply (v j)
      right_inv := fun x => funext fun j => (eK (D.nbr i w hw)).symm_apply_apply (x j)
      map_add' := fun v v' => funext fun j => map_add (eK (D.nbr i w hw)).symm (v j) (v' j)
      map_smul' := fun c v => funext fun j => map_mul (eK (D.nbr i w hw)).symm c (v j)
      continuous_toFun := continuous_pi fun j => (eK_symm_cont i hw).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => (eK_cont i hw).comp (continuous_apply j) }
  have hM : IsModuleTopology (Br.LLw (D.nbr i w hw)) (TrV (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i))) :=
    IsModuleTopology.iso φ
  exact hM.1.symm

end Homeo

section Cyc

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))

end Cyc

section Row

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

end Row

section RowTop

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

end RowTop

section Ms

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem rTwO_cont (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (x : D.nd.X i) : Continuous (rTwO D.nd i r x) := by
  have hχ : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((chiU D.nd i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [MonoidHom.inv_apply, map_inv]
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  exact hχ.smul (hc x)

theorem locC_cont (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    Continuous ⇑(TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x)) := by
  have hinc : Continuous (TruncatedSeriesCountingIdentities.CoefExt.inc C) :=
    continuous_induced_rng.2 (by exact continuous_subtype_val)
  have h1 : Continuous fun g : Br.G D.nbr i w hw =>
      rTwO D.nd i r x ((Br.iota D.nbr i w hw g : _) : GE D.nd) :=
    (rTwO_cont i r hc x).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  exact ((h1.matrix_map (D.nbr i w hw).eO_cont).matrix_map continuous_subtype_val).matrix_map hinc

end Ms

end Formalism.MainNotions.N.KOrb

end
end

section -- merged from Formalism.AdmissibleDesigns.YtTarget
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

section Record

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))

abbrev YtM : Type := ↥(Ymod Dd.r Dd.χ Dd.E) × D.nd.O i

instance instAddCommGroupYtM : AddCommGroup (YtM i Dd) := Prod.instAddCommGroup

abbrev ytRepW (n : ℕ) : Representation (D.nd.O i) ↥(Dw i dc n) (YtM i Dd) :=
  resRep (ytRep (D.nd.O i) Dd.r Dd.χ Dd.E) (Dw i dc n)

abbrev ιW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Br.G D.nbr i w hw →* ↥(Dw i dc (idx i dc w)) :=
  (eW i dc hw).symm.toMonoidHom

abbrev eS {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    FractionRing (D.nd.O i) ≃+* ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 :=
  eK (D.nbr i w hw)

abbrev ytV {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Representation ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (Br.G D.nbr i w hw) (TrV (eS i hw) (MK (O := D.nd.O i) (YtM i Dd))) :=
  repL (eS i hw) (locRep (ytRepW i dc Dd (idx i dc w))) (ιW i dc hw)

abbrev MsW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 :=
  TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rTwO D.nd i r x)

def MsContW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Prop :=
  ∀ x, Continuous (MsW i r hw x)

def YtEmbW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Prop :=
  ∃ (m : ℕ) (xs : Fin m → D.nd.X i)
    (φ : TrV (eS i hw) (MK (O := D.nd.O i) (YtM i Dd)) →ₗ[↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1]
      (Fin m → Fin D.R.nV → ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1)),
    Function.Injective φ ∧ ∀ g v, φ (ytV i dc Dd hw g v) = fun a => (MsW i r hw (xs a) g).mulVec (φ v a)

variable [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def YtTarget {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) : Prop :=
  ∀ Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1),
    ∃ Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL),
      YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
      PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd

end Record

end Formalism.MainNotions.N.K.TBa

end
end

section -- merged from Formalism.AdmissibleDesigns.LocRepTriv
section -- merged from Formalism.AdmissibleDesigns.ExistsUnrDec
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KUnr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N

section Gen

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem exists_unr_dec (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ χ : ↥(A.decompositionSubgroup F) → ℤ_[p], Continuous χ ∧ (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : ↥(A.decompositionSubgroup F), (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A → χ g = 0) ∧ ∃ g, χ g = 1 := by
  exact hT2Core.out.unr A hp

end Gen

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

private lemma plOf_colIdx (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) = l.1 := by
  have hmem : l.1 ∈ K.plSet i dc := by
    simp only [K.plSet, Finset.mem_union]
    exact Or.inl (Or.inr l.2)
  have hlt : ((K.plSet i dc).equivFin ⟨l.1, hmem⟩ : ℕ) < (K.plSet i dc).card := Fin.is_lt _
  unfold K.colIdx K.idx K.plOf
  rw [dite_eq_left hmem, dite_eq_left hlt]
  simp

theorem col_over (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ placesOver D.host.E (D.nd.l i) := by
  rw [plOf_colIdx]
  first
  | exact (dc.cover l.1).mp (Or.inr l.2)
  | exact ((dc.cover l.1).mp (Or.inr l.2)).1
  | (have h := (dc.cover l.1).mp (Or.inr l.2); done)

theorem col_hp (l : K.Col i dc) :
    (K.Aw i dc (K.colIdx i dc l)).valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 := by
  have hov := col_over i dc l
  rw [plOf_colIdx] at hov
  unfold K.Aw
  rw [plOf_colIdx]
  have h2 := (D.nd.plOm.2 l.1 ((D.nd.l i : ℕ) : 𝓞 D.host.E)).mpr hov
  simpa using h2

theorem unrHom (l : K.Col i dc) : KFin.UnrHom i dc l := by
  obtain ⟨χ, hc, hm, hI, g1, h1⟩ :=
    exists_unr_dec (F := D.host.E) (K.Aw i dc (K.colIdx i dc l)) (col_hp i dc l)
  refine ⟨fun g => algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g), ⟨fun g h => ?_, fun g hg => ?_, fun hn => ?_⟩, g1, ?_⟩
  · show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ (g * h)) = _ + _
    rw [hm, map_add (f := _)]
  · have hg' : ((g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om)) ∈ Ine (F := D.host.E) (K.Aw i dc (K.colIdx i dc l)) :=
      Subgroup.mem_subgroupOf.1 hg
    show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g) = 0
    rw [hI g hg', map_zero]
  · have hf : Continuous fun g : ↥(KFin.Γc i dc l) => algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g) :=
      (K.Topo.continuous_alg i).comp hc
    have e1 : ∀ c : D.nd.O i, KHf.eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c) =
        ((D.nbr i _ hn).eO c : Br.LLw (D.nbr i _ hn)) := fun c => by
      rw [KHf.eK_apply, Br.toLLK_alg]
      rfl
    simp only [e1]
    exact continuous_subtype_val.comp ((D.nbr i _ hn).eO_cont.comp (hf.comp (Br.iota_cont D.nbr i _ hn)))
  · show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g1) = 1
    rw [h1, map_one]

end Rec

end Formalism.MainNotions.N.KUnr
end
end

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KUnr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

section Loc

variable {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ] {M : Type} [AddCommGroup M] [Module O M]

theorem locRep_triv (g : Γ) (x : KHf.MK (O := O) M) :
    KHf.locRep (Representation.trivial O Γ M) g x = x := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map (nonZeroDivisors O) (Representation.trivial O Γ M g) (LocalizedModule.mk m s) =
      LocalizedModule.mk m s
    rw [LocalizedModule.map_mk]
    rfl

end Loc

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (δO : D.nd.O i)

theorem col_mem (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ dc.col := by
  have h : l.1 ∈ K.plSet i dc := by
    unfold K.plSet
    simp [l.2]
  rw [K.colIdx, K.plOf_idx i dc h]
  exact l.2

end Rec

end Formalism.MainNotions.N.KUnr
end
end

section -- merged from Formalism.AdmissibleDesigns.CycMatchRec
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Classical

namespace Formalism.MainNotions.N.KBKa

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.MainNotions.N.KHf

section Cyc

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycZ_eq_χQ (g : ↥(GK Bw.Kw)) :
    ((ReciprocityTheory.Gal.cycZ (F := E) (Ω := Ω) l ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]) : ℚ_[l]) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := by
  set x : ℚ_[l] := ((ReciprocityTheory.Gal.cycZ (F := E) (Ω := Ω) l ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]) : ℚ_[l])
    with hx
  set x' : ℚ_[l] := ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) with hx'
  have key : ∀ m : ℕ, ‖x - x'‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    haveI : NeZero ((l ^ m : ℕ) : Ω) := ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    obtain ⟨ζ', hζ'⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hζ : IsPrimitiveRoot (Bw.j ζ') (l ^ m) := hζ'.map_of_injective Bw.j.injective
    obtain ⟨a, ha, hxa⟩ := Formalism.AdicCompletionExports.isCycG_cycZ l E Ω ℤ_[l] (RingHom.id _)
      ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) m ζ' hζ'.pow_eq_one
    obtain ⟨a', hxa', ha'⟩ := P.χQ_cyc (g : GQ l) m (Bw.j ζ') hζ.pow_eq_one
    have hg : (g : GQ l) (Bw.j ζ') = Bw.j ζ' ^ a := by
      have h0 := Bw.e_comm (Br.ι Bw g) ζ'
      have he : Bw.e (Br.ι Bw g) = g := Bw.e.apply_symm_apply g
      rw [he] at h0
      rw [h0, ha, map_pow]
    have h1 : a ≡ a' [MOD l ^ m] := by
      have h0 := hg.symm.trans ha'
      have hf : IsOfFinOrder (Bw.j ζ') :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨l ^ m, pow_pos (Fact.out : l.Prime).pos m, hζ.pow_eq_one⟩
      rwa [hf.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h0
    have hxa2 : ‖x - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      change ((ReciprocityTheory.Gal.cycZ (F := E) (Ω := Ω) l ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]) - (a : ℤ_[l]))
        ∈ Ideal.span {(l : ℤ_[l]) ^ m} at hxa
      have h0 := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 hxa
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h0
      exact h0
    have h2 : ‖((a : ℚ_[l]) - (a' : ℚ_[l]))‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      have h3 : ((l ^ m : ℕ) : ℤ) ∣ (a : ℤ) - (a' : ℤ) := Nat.modEq_iff_dvd.1 h1.symm
      have h4 := (Padic.norm_int_le_pow_iff_dvd ((a : ℤ) - a') m).2 (by exact_mod_cast h3)
      simpa using h4
    have h4 : x - x' = (x - a) + ((a - a') + -(x' - a')) := by ring
    rw [h4]
    exact (Padic.nonarchimedean _ _).trans (max_le hxa2 ((Padic.nonarchimedean _ _).trans
      (max_le h2 (by rwa [norm_neg]))))
  have hlim : Filter.Tendsto (fun m : ℕ => (l : ℝ) ^ (-(m : ℤ))) Filter.atTop (nhds 0) := by
    have h5 : ∀ m : ℕ, (l : ℝ) ^ (-(m : ℤ)) = ((l : ℝ)⁻¹) ^ m := fun m => by
      rw [zpow_neg, zpow_natCast, inv_pow]
    simp only [h5]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt))
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' hlim key))

end Cyc

section TopPi

variable {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace (FractionRing O)]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)
  (n : Type) [Fintype n]

end TopPi

section RecC

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  {VT VT' : Type}
  [AddCommGroup VT] [Module (D.nd.O i) VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul (D.nd.O i) VT] [Module (FractionRing (D.nd.O i)) VT]
  [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VT]
  [AddCommGroup VT'] [Module (D.nd.O i) VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul (D.nd.O i) VT'] [Module (FractionRing (D.nd.O i)) VT']
  [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VT']

theorem cycMatch_rec {w : ℕ} (hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i))
    (Dw : Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) VT VT')
    (hε : ∀ g : ↥(Γn i dc w), Dw.ε g = epsU D.nd i (g : GE D.nd)) :
    CycMatch Dw (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) (Br.PD D.loc D.nbr i _ hn) := by
  intro g
  rw [hε]
  have hP := cycZ_eq_χQ (D.nbr i _ hn) (D.loc (D.nd.l i)) g
  have hχ := (D.loc (D.nd.l i)).PD_χ (D.nbr i _ hn).Kw g
  simp only [eK, RingEquiv.ofBijective_apply, Br.toLLK, IsFractionRing.lift_algebraMap, LocBridge.toLL,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, epsU, Glob.epsO, MonoidHom.comp_apply,
    Units.coe_map, MonoidHom.coe_coe, cycLL, Br.PD, RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    LocBridge.eO_alg]
  rw [← IsScalarTower.algebraMap_apply, hχ, ← hP]
  first
  | exact IsScalarTower.algebraMap_apply ℤ_[D.nd.l i] ℚ_[D.nd.l i] _ _
  | rfl

end RecC

section RecD

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))

theorem rowIn_of {w : ℕ} (hε : ∀ g : ↥(Γn i dc w), (Dat w).ε g = epsU D.nd i (g : GE D.nd))
    (ht : ∀ hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
      HomeoK (eK (D.nbr i _ hn)) ∧ TopMatch (eK (D.nbr i _ hn)) (VT w) ∧ TopMatch (eK (D.nbr i _ hn)) (VT' w))
    (hdr : ∀ hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
      IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn)) (Dat w).ρT (Br.iota D.nbr i _ hn))) :
    RowIn i dc VT VT' Dat w := by
  intro hn
  obtain ⟨h1, h2, h3⟩ := ht hn
  exact ⟨h1, h2, h3, cycMatch_rec i dc hn (Dat w) hε, hdr hn⟩

end RecD

end Formalism.MainNotions.N.KBKa
end
end
