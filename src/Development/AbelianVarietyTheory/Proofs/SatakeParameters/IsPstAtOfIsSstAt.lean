module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfUnr
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstAtOfIsSstAt
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSemistableAtPlaceTwistCrystallineCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSemistableAtPlaceTwistCrystallineCharacter
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.GalOfCusp
open TensorProduct Module

noncomputable section

namespace GlobalTheory.SstTwist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

theorem ineTriv_of_isSst [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK K) V) (hV : IsPst P ρ)
    (hs : IsSst P ρ) : GlobalTheory.PstLaws.IneTriv P ρ := by
  intro g hg
  have hcl := mem_closure_mulV_of_finrank_eq l P K L V ρ hV (Dst P ρ) le_rfl
    (fun c hc x hx => (mem_Dst P ρ).mpr fun h => by
      rw [← Module.End.mul_apply, stRep_mulV P ρ h c c (mem_GK.mp h.2 _ hc), Module.End.mul_apply,
        (mem_Dst P ρ).mp hx h]) hs
  refine LinearMap.ext fun x => Subtype.ext ?_
  refine AddSubgroup.closure_induction (p := fun y _ => stRep P ρ g y = y) ?_ (map_zero _) ?_ ?_ (hcl x x.2)
  · rintro _ ⟨c, s, hs', rfl⟩
    rw [← Module.End.mul_apply, stRep_mulV P ρ g c c ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ c.2),
      Module.End.mul_apply, (mem_Dst P ρ).mp hs' g]
  · intro y z _ _ hy hz; rw [map_add (f := _), hy, hz]
  · intro y _ hy; rw [map_neg, hy]

end GlobalTheory.SstTwist

namespace GlobalTheory.SstTwist

open GlobalTheory.Pst.TwistLetters GlobalTheory.Pst.TwistLetters.Invert

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) {K L : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem isSst_twist (T : LocTied l P AI) [FiniteDimensional ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V)
    (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1)
    (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)
    (hs : IsSst P ρs) (hc : Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) ρm) : IsSst P ρt := by
  haveI := L.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥L.1 V
  have hPs : IsPst P ρs := GlobalTheory.GalCut.IwaAll.isPst_of_isSst P AI T ρs hs
  have hPm : IsPst P ρm := GlobalTheory.PstOfCrys.isPst_of_isCrys T ρm hc
  have hIs := ineTriv_of_isSst P ρs hPs hs
  have hIm := GlobalTheory.PstLaws.ineTriv_of_isCrys P ρm hPm hc
  obtain ⟨y, hy, y', hyy'⟩ := GlobalTheory.Pst.UnitLetter.exists_unit_Dpst P AI ⟨T⟩ ρm χ hm hPm
  let y₀ : ↥(Dpst P ρm) := ⟨y, hy⟩
  have hsurj := GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv P ρs ρt ρm χ hm ht y₀ y' hyy'

  let Φ : DpstUr P ρs →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρt :=
    { toFun := fun x => toUr P ρt (dmul P ρs ρt ρm χ hm ht ((toUr P ρs).symm x) y₀)
      map_add' := fun x x' => by simp only [map_add (f := _), LinearMap.add_apply]
      map_smul' := fun c x => dmul_mulD_left P ρs ρt ρm χ hm ht c _ y₀ }
  have hinj : Function.Injective Φ := by
    intro x x' hxx
    have h1 : mulB (L := L) P V y' (mulB (L := L) P V y ((toUr P ρs).symm x : V ⊗[ℚ_[l]] Bst P)) =
        mulB (L := L) P V y' (mulB (L := L) P V y ((toUr P ρs).symm x' : V ⊗[ℚ_[l]] Bst P)) :=
      congrArg (fun z : ↥(Dpst P ρt) => mulB (L := L) P V y' (z : V ⊗[ℚ_[l]] Bst P)) hxx
    rw [mulB_assoc, mulB_assoc, hyy', one_mulB, one_mulB] at h1
    exact (toUr P ρs).symm.injective (Subtype.ext h1)
  have hsur : Function.Surjective Φ := by
    intro z
    obtain ⟨x, hx⟩ := hsurj ((toUr P ρt).symm z)
    exact ⟨toUr P ρs x, by
      change toUr P ρt (dmul P ρs ρt ρm χ hm ht ((toUr P ρs).symm (toUr P ρs x)) y₀) = z
      rw [AddEquiv.symm_apply_apply, hx, AddEquiv.apply_symm_apply]⟩
  have hPt : IsPst P ρt := by
    rw [IsPst, ← (LinearEquiv.ofBijective Φ ⟨hinj, hsur⟩).rank_eq]
    exact hPs
  refine GlobalTheory.PstLaws.isSst_of_ineTriv P ρt hPt fun g hg => LinearMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := hsurj z
  rw [actD_dmul, LinearMap.congr_fun (hIs g hg) x, LinearMap.congr_fun (hIm g hg) y₀]
  rfl

end GlobalTheory.SstTwist

open GlobalTheory.Pst.TwistLetters

theorem GlobalTheory.SstTwist.isSstAt_twist : GlobalTheory.Published.DeRhamPotSemistable → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)) (c : ↥Gw →* GL (Fin 1) (Om l)), (Continuous fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → (Continuous fun g => ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) → IsSstAt P Bw r → IsCrysAt P Bw c → IsSstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) := by
  intro _ l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r c _ _ hr hc
  obtain ⟨T⟩ := hT
  obtain ⟨L₁, r₁, hm₁, hs₁⟩ := hr
  obtain ⟨L₂, c₂, hm₂, hc₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  set L := supExt L₁ L₂
  set s := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁
  set m := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom c₂
  refine ⟨L, _, GlobalTheory.TwistParamAbove.isModel_twist (hm₁.enlarge l₁) (hm₂.enlarge l₂), ?_⟩
  have hsL : IsSst P (Bw.repE L s) := GlobalTheory.AboveL.RepConj.isSst_enlarge P Bw l₁ r₁ hs₁
  have hcL : Bw.IsCrysE P L m := (GlobalTheory.Pst.local_ext P Bw l₂ c₂).1.2 hc₂
  let χ : ↥(GK Bw.Kw) → ↥L.1 := fun g => ((GlobalTheory.TwistAbove.chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1)
  have hχm : ∀ g v, Bw.repE L m g v = χ g • v := fun g v => GlobalTheory.TwistAbove.repE_rank_one Bw m g v
  have hχt : ∀ g v, Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)) g v =
      χ g • Bw.repE L s g v := by
    intro g v
    rw [GlobalTheory.TwistBridgeDR.twGL_eq]
    exact GlobalTheory.TwistBridgeDR.repE_twGL' Bw _ s g v
  exact GlobalTheory.SstTwist.isSst_twist P AI T (Bw.repE L s) _ (Bw.repE L m) χ hχm hχt hsL hcL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSemistableAtPlaceTwistCrystallineCharacterStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.GalOfCusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemistableAtPlace_twist_crystallineCharacter : GlobalTheory.Published.DeRhamPotSemistable → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)) (c : ↥Gw →* GL (Fin 1) (Om l)), (Continuous fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → (Continuous fun g => ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) → IsSstAt P Bw r → IsCrysAt P Bw c → IsSstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) := by
  first | exact @GlobalTheory.SstTwist.isSstAt_twist | exact GlobalTheory.SstTwist.isSstAt_twist | (intros; apply GlobalTheory.SstTwist.isSstAt_twist <;> assumption)
end
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open UpperTheory.V UpperTheory.V.Af

noncomputable section

namespace GlobalTheory.GalCut.IwaTwist

open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PMon Module

theorem isSst_resQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsSst P (GlobalTheory.PstCoeff.resQ ρ) := by
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  rw [IsSst, e, h, ← finrank_mul_finrank ℚ_[l] LL V]
  ring

theorem isPst_of_isSst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) {K : FinExt l}
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsPst P ρ := by
  rw [← GlobalTheory.PstCoeff.isPst_resQ_iff]
  apply GlobalTheory.PMon.isPst_of_isSst_resTo l P AI T K K le_rfl V
  have hD : Dst P (resTo (GlobalTheory.PstCoeff.resQ ρ) (le_refl K.1)) = Dst P (GlobalTheory.PstCoeff.resQ ρ) := by
    ext x
    rw [mem_Dst_resTo, mem_Dst]
    exact ⟨fun H g => H g g.2, fun H g _ => H g⟩
  have := isSst_resQ P ρ h
  rw [IsSst] at this ⊢
  rw [hD]
  exact this

theorem isPstAt_of_isSstAt {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {a : ℕ} (r : ↥Gw →* GL (Fin a) (Om l)) :
    IsSstAt P Bw r → IsPstAt P Bw r := by
  rintro ⟨LL', r', hm, hs⟩
  obtain ⟨T⟩ := hT
  haveI := LL'.2
  exact ⟨LL', r', hm, isPst_of_isSst P AI T _ hs⟩

theorem isSstAt_twist (hD : GlobalTheory.Published.DeRhamPotSemistable) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {a : ℕ}
    (r : ↥Gw →* GL (Fin a) (Om l)) (c : ↥Gw →* GL (Fin 1) (Om l))
    (hr : Continuous fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))
    (hc : Continuous fun g => ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)))
    (h1 : IsSstAt P Bw r) (h2 : IsCrysAt P Bw c) :
    IsSstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) :=
  GlobalTheory.T.isSemistableAtPlace_twist_crystallineCharacter hD l P AI hT E Ω Gw O Bw a r c hr hc h1 h2

end GlobalTheory.GalCut.IwaTwist

namespace GlobalTheory.GalCut.IwaTwist

end GlobalTheory.GalCut.IwaTwist

namespace GlobalTheory.GalCut.IwaTwist

end GlobalTheory.GalCut.IwaTwist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermSecRestrictGlobalAlgebraMap
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeCoh

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Sp k)

def germSec {V : X.Opens} (hη : genericPoint X ∈ V) : Sec s V →+* X.functionField :=
  (X.presheaf.germ V (genericPoint X) hη).hom

theorem semiHom_germSec {V : X.Opens} (hη : genericPoint X ∈ V) :
    letI := ffAlg s; SemiHom (RingHom.id k) (germSec s hη) := by
  letI := ffAlg s
  intro r b
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply]
  congr 1
  change (X.presheaf.germ V (genericPoint X) hη).hom ((secMap s V).hom r) =
    (X.presheaf.germ ⊤ (genericPoint X) trivial).hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r))
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 2
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appLE ⊤ V le_top) ≫ _ = _
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  rfl

theorem germSec_restrictGlobal_algebraMap {V : X.Opens} (hη : genericPoint X ∈ V) (r : k) :
    letI := algΓ s; letI := ffAlg s
    germSec s hη (restrictGlobal X V (algebraMap k Γ(X, ⊤) r)) = algebraMap k X.functionField r := by
  letI := algΓ s; letI := ffAlg s
  change (X.presheaf.germ V (genericPoint X) hη).hom ((X.presheaf.map (homOfLE le_top).op).hom _) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
  rfl

def formGerm (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) :
    letI := algΓ s; letI := ffAlg s
    sectionsOn (Omega s j) V →ₗ[k] DR k X.functionField :=
  letI := algΓ s; letI := ffAlg s
  { toFun := fun x ↦ (semiHom_germSec s hη).mDR
      ((toOmEquiv s j hV).symm (sectionsOn.toΓ _ _ x) : DR k (Sec s V))
    map_add' := fun x y ↦ by
      rw [map_add (f := _), map_add (f := _), Submodule.coe_add, map_add (f := _)]
    map_smul' := fun r x ↦ by
      rw [sectionsOn.toΓ_smul]
      have h1 : (toOmEquiv s j hV).symm (restrictGlobal X V (algebraMap k Γ(X, ⊤) r) •
          sectionsOn.toΓ _ _ x) = (show Sec s V from restrictGlobal X V (algebraMap k Γ(X, ⊤) r)) •
          (toOmEquiv s j hV).symm (sectionsOn.toΓ _ _ x) :=
        (toOmEquiv s j hV).symm.map_smul _ _
      rw [h1, Submodule.coe_smul, SemiHom.mDR_smul]
      change germSec s hη (restrictGlobal X V (algebraMap k Γ(X, ⊤) r)) • _ = _
      rw [germSec_restrictGlobal_algebraMap, algebraMap_smul]
      rfl }

def formGermI (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V)
    [inst : Algebra k X.functionField] (hinst : inst = ffAlg s) :
    letI := algΓ s; sectionsOn (Omega s j) V →ₗ[k] DR k X.functionField := by
  subst hinst; exact formGerm s j hV hη

theorem formGermI_ffAlg (j : ℕ) {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) :
    formGermI (inst := ffAlg s) s j hV hη rfl = formGerm s j hV hη := rfl

end GlobalTheory.HodgeCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitAtOfDegOne
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section
namespace GlobalTheory.CongEx

open UpperTheory.V.Af

theorem exists_place_over (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  have hp : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Int.prime_iff_natAbs_prime.2 (by simpa using (Fact.out : l.Prime))).irreducible
  have hker : RingHom.ker (algebraMap ℤ (𝓞 E)) ≤ Ideal.span {(l : ℤ)} := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := by exact_mod_cast (algebraMap ℤ (𝓞 E)).injective_int (hx.trans (map_zero _).symm)
    rw [this]; exact zero_mem _
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) _ hker
  have hl : ((l : ℕ) : 𝓞 E) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun h => ?_⟩, hl⟩
  rw [h] at hQc
  have h0 : (l : ℤ) ∈ Ideal.span {(l : ℤ)} := Ideal.mem_span_singleton_self _
  rw [← hQc] at h0
  change (l : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) ⊥ at h0
  rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 E)).injective_int] at h0
  have := (Fact.out : l.Prime).ne_zero
  simp_all

theorem eventually_not_mem_l (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

end GlobalTheory.CongEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothSectionsInFunctionField
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem smooth_sections_in_functionField : ∀ (Z' : Scheme.{0}) [IsIntegral Z'] (p' : Z' ⟶ Sp ℂ) [inst' : Algebra ℂ Z'.functionField], Smooth p' → inst' = ffAlg p' → ∀ (W : Z'.Opens), IsAffineOpen W → ∀ (hW : genericPoint Z' ∈ W) (B : Subalgebra ℂ Z'.functionField), (∀ y, y ∈ B ↔ ∃ g : Γ(Z', W), (Z'.presheaf.germ W (genericPoint Z') hW).hom g = y) → Algebra.Smooth ℂ B := by
  intro Z' _ p' inst' hp hinst W hWa hW B hB
  subst hinst
  letI : Algebra ℂ Z'.functionField := ffAlg p'
  let φ : ℂ →+* Γ(Z', W) := (p'.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have h := HasRingHomProperty.appLE @Smooth p' hp ⟨⊤, isAffineOpen_top _⟩ ⟨W, hWa⟩ le_top
  have h' : RingHom.Smooth φ :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.bijective) h
  letI : Algebra ℂ Γ(Z', W) := φ.toAlgebra
  have hs : Algebra.Smooth ℂ Γ(Z', W) := h'
  let g := (Z'.presheaf.germ W (genericPoint Z') hW).hom
  have hg : Function.Injective g := germ_injective_of_isIntegral Z' (genericPoint Z') hW
  have hc : ∀ c : ℂ, g (algebraMap ℂ Γ(Z', W) c) = algebraMap ℂ Z'.functionField c := by
    intro c
    show g (φ c) = _
    simp only [φ, g, Scheme.Hom.appLE, CommRingCat.comp_apply, RingHom.comp_apply]
    show _ = (Z'.presheaf.germ ⊤ (genericPoint Z') trivial).hom ((p'.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c))
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_res]
    rfl
  let gA : Γ(Z', W) →ₐ[ℂ] Z'.functionField := { g with commutes' := hc }
  let f : Γ(Z', W) →ₐ[ℂ] B := gA.codRestrict B (fun x => (hB _).2 ⟨x, rfl⟩)
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => hg (congrArg Subtype.val hab), fun y => ?_⟩
    obtain ⟨x, hx⟩ := (hB y.1).1 y.2
    exact ⟨x, Subtype.ext hx⟩
  exact Algebra.Smooth.of_equiv (AlgEquiv.ofBijective f hf)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GermCompatId
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

namespace GlobalTheory.W1.Lef

def GermCompat {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (c : Y ⟶ Z) (ψ : Z.functionField → Y.functionField) : Prop :=
  ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
    ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom (c.app V g)

set_option autoImplicit false in
theorem _root_.GlobalTheory.W1.Lef.germCompat_id (Z : Scheme.{0}) [IsIntegral Z] :
    _root_.GlobalTheory.W1.Lef.GermCompat (𝟙 Z) (fun y => y) := by
  intro V hV hV' g
  rfl

abbrev omCx {K : Type} [Field K] [Algebra ℂ K] {ι : Type} [LinearOrder ι] (B : Finset ι → Subalgebra ℂ K) (a : ℕ) :
    Cx ℂ (Finset ι → DR ℂ K) := GlobalTheory.PD.cech fun I => omB ℂ K (B I) a

def mapL (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L] :
    DR ℂ K →ₗ[ℂ] DR ℂ L := (mapDR ℂ K L).toLinearMap.restrictScalars ℂ

theorem mapL_apply (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    (ω : DR ℂ K) : mapL K L ω = mapDR ℂ K L ω := rfl

def locTerm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a : ℕ) : ℂ :=
  (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C)).coeff a / (1 - A).det

end GlobalTheory.W1.Lef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FlatHermRootLineDegree
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PD.PullMap

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

theorem prod_prod_erase (g : κ → κ → ℤ) {t : Finset κ} {i : κ} (hi : i ∈ t) (hg : g i i = 1) :
    ∏ a ∈ t, ∏ b ∈ t, g a b =
      (∏ a ∈ t.erase i, ∏ b ∈ t.erase i, g a b) * ∏ a ∈ t.erase i, (g a i * g i a) := by
  have row : ∀ a, ∏ b ∈ t, g a b = g a i * ∏ b ∈ t.erase i, g a b :=
    fun a => (Finset.mul_prod_erase t (g a) hi).symm
  have h1 := Finset.mul_prod_erase t (fun a => ∏ b ∈ t, g a b) hi
  rw [← h1, row i, hg, one_mul, Finset.prod_congr rfl (fun a _ => row a)]
  simp only [Finset.prod_mul_distrib]
  ring

theorem cubeSign_eq_prod (t : Finset κ) (i : κ) :
    cubeSign t i = ∏ a ∈ t, (if a < i then (-1 : ℤ) else 1) := by
  rw [cubeSign, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem cubeSign_image {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) (i : κ) :
    cubeSign (t.image τ) (τ i) = ∏ a ∈ t, (if τ a < τ i then (-1 : ℤ) else 1) := by
  rw [cubeSign_eq_prod, Finset.prod_image (by intro x hx y hy hxy; exact h hx hy hxy)]

theorem pair_sign {τ : κ → ι} {x i : κ} (hx : x ≠ i) (hτ : τ x ≠ τ i) :
    (if x < i ∧ τ i < τ x then (-1 : ℤ) else 1) * (if i < x ∧ τ x < τ i then (-1 : ℤ) else 1) =
      (if x < i then (-1 : ℤ) else 1) * (if τ x < τ i then (-1 : ℤ) else 1) := by
  rcases lt_or_gt_of_ne hx with h | h <;> rcases lt_or_gt_of_ne hτ with h' | h' <;>
    simp [h, h', lt_asymm h, lt_asymm h']

theorem sortSign_eq_erase {τ : κ → ι} {s : Finset κ} {i : κ} (hi : i ∈ s)
    (hne : ∀ x ∈ s.erase i, τ x ≠ τ i) :
    sortSign τ s = sortSign τ (s.erase i) *
      ∏ x ∈ s.erase i, ((if x < i then (-1 : ℤ) else 1) * (if τ x < τ i then (-1 : ℤ) else 1)) := by
  have := prod_prod_erase (fun x y => if x < y ∧ τ y < τ x then (-1 : ℤ) else 1) hi (by simp)
  beta_reduce at this
  unfold sortSign
  rw [this]
  congr 1
  exact Finset.prod_congr rfl fun x hx => pair_sign (Finset.ne_of_mem_erase hx) (hne x hx)

theorem sign_inj {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) {i : κ} (hi : i ∈ t) :
    sortSign τ t * cubeSign (t.image τ) (τ i) = cubeSign t i * sortSign τ (t.erase i) := by
  have e1 := sortSign_eq_erase (τ := τ) hi (fun x hx e =>
    Finset.ne_of_mem_erase hx (h (Finset.mem_of_mem_erase hx) hi e))
  rw [Finset.prod_mul_distrib] at e1
  have e2 : cubeSign t i = ∏ a ∈ t.erase i, (if a < i then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ hi]
    simp
  have e3 : cubeSign (t.image τ) (τ i) = ∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1) := by
    rw [cubeSign_image h, ← Finset.mul_prod_erase t _ hi]
    simp
  have hQ : (∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1)) *
      ∏ a ∈ t.erase i, (if τ a < τ i then (-1 : ℤ) else 1) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun a _ => by split_ifs <;> norm_num
  rw [e1, e2, e3]
  linear_combination (sortSign τ (t.erase i) * ∏ a ∈ t.erase i, (if a < i then (-1 : ℤ) else 1)) * hQ

theorem sign_pair {τ : κ → ι} {t : Finset κ} {a b : κ} (ha : a ∈ t) (hb : b ∈ t) (hab : a ≠ b)
    (he : τ a = τ b) (h : Set.InjOn τ (t.erase a)) :
    cubeSign t a * sortSign τ (t.erase a) = -(cubeSign t b * sortSign τ (t.erase b)) := by
  have hb' : b ∈ t.erase a := Finset.mem_erase.2 ⟨hab.symm, hb⟩
  have ha' : a ∈ t.erase b := Finset.mem_erase.2 ⟨hab, ha⟩
  have hu' : (t.erase b).erase a = (t.erase a).erase b := Finset.erase_right_comm
  have mem : ∀ x ∈ (t.erase a).erase b, τ x ≠ τ b := by
    intro x hx e
    have hx1 := Finset.mem_erase.1 hx
    exact hx1.1 (h hx1.2 hb' e)
  have e1 := sortSign_eq_erase (τ := τ) hb' mem
  have e2 := sortSign_eq_erase (τ := τ) ha' (by rw [hu', he]; exact mem)
  rw [hu', he] at e2
  have c1 : cubeSign t a = (if b < a then (-1 : ℤ) else 1) *
      ∏ x ∈ (t.erase a).erase b, (if x < a then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ hb, ← Finset.mul_prod_erase (t.erase b) _ ha', hu']
    simp only [lt_self_iff_false, if_false, one_mul]
  have c2 : cubeSign t b = (if a < b then (-1 : ℤ) else 1) *
      ∏ x ∈ (t.erase a).erase b, (if x < b then (-1 : ℤ) else 1) := by
    rw [cubeSign_eq_prod, ← Finset.mul_prod_erase t _ ha, ← Finset.mul_prod_erase (t.erase a) _ hb']
    simp only [lt_self_iff_false, if_false, one_mul]
  have hs : (if b < a then (-1 : ℤ) else 1) = -(if a < b then (-1 : ℤ) else 1) := by
    rcases lt_or_gt_of_ne hab with h' | h' <;> simp [h', lt_asymm h']
  rw [e1, e2, c1, c2, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hs]
  ring

theorem image_erase_of_injOn {τ : κ → ι} {t : Finset κ} (h : Set.InjOn τ t) {i : κ} (hi : i ∈ t) :
    (t.image τ).erase (τ i) = (t.erase i).image τ := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hy, x, hx, rfl⟩
    exact ⟨x, ⟨fun e => hy (congrArg τ e), hx⟩, rfl⟩
  · rintro ⟨x, ⟨hxi, hx⟩, rfl⟩
    exact ⟨fun e => hxi (h hx hi e), x, hx, rfl⟩

theorem image_erase_eq {τ : κ → ι} {t : Finset κ} {a b : κ} (hb : b ∈ t) (hab : a ≠ b) (he : τ a = τ b) :
    (t.erase a).image τ = t.image τ := by
  ext y
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨_, hx⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    by_cases hxa : x = a
    · exact ⟨b, ⟨hab.symm, hb⟩, by rw [hxa]; exact he.symm⟩
    · exact ⟨x, ⟨hxa, hx⟩, rfl⟩

theorem injOn_erase_swap {τ : κ → ι} {t : Finset κ} {a b : κ} (hb : b ∈ t) (hab : a ≠ b)
    (he : τ a = τ b) (h : Set.InjOn τ (t.erase a)) : Set.InjOn τ (t.erase b) := by
  intro x hx y hy hxy
  simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hx hy
  have hb' : b ∈ (↑(t.erase a) : Set κ) := by simp [hab.symm, hb]
  by_cases hxa : x = a <;> by_cases hya : y = a
  · rw [hxa, hya]
  · exact absurd (h (by simp [hya, hy.1]) hb' (by rw [← hxy, hxa, he])) hy.2
  · exact absurd (h (by simp [hxa, hx.1]) hb' (by rw [hxy, hya, he])) hx.2
  · exact h (by simp [hxa, hx.1]) (by simp [hya, hy.1]) hxy

variable {k : Type} [Field k] {E E' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']

open Classical in
theorem pullC_apply (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) (s : Finset κ) :
    pullC τ φ c s = if Set.InjOn τ s then sortSign τ s • φ (c (s.image τ)) else 0 := rfl

theorem pullC_delta (τ : κ → ι) (φ : E →ₗ[k] E') (c : Finset ι → E) :
    pullC τ φ (GlobalTheory.DI.delta c) = GlobalTheory.DI.delta (pullC τ φ c) := by
  funext t
  rw [pullC_apply]
  simp only [GlobalTheory.DI.delta]
  by_cases h : Set.InjOn τ t
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [if_pos h, Finset.sum_image (by intro x hx y hy hxy; exact h hx hy hxy), map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [pullC_apply, if_pos (h.mono (Finset.coe_subset.2 (Finset.erase_subset i t))), map_zsmul,
        ← image_erase_of_injOn h hi, smul_smul, smul_smul, sign_inj h hi]
  · rw [if_neg h]
    have h' : ∃ a ∈ t, ∃ b ∈ t, τ a = τ b ∧ a ≠ b := by
      by_contra hc
      push_neg at hc
      exact h (by intro x hx y hy hxy; exact hc x hx y hy hxy)
    obtain ⟨a, ha, b, hb, he, hab⟩ := h'
    have zero_of : ∀ s : Finset κ, a ∈ s → b ∈ s → pullC τ φ c s = 0 := fun s has hbs => by
      rw [pullC_apply, if_neg]
      intro hs
      exact hab (hs has hbs he)
    rw [Finset.sum_eq_add_of_mem a b ha hb hab (fun x _ hne => by
      rw [zero_of _ (Finset.mem_erase.2 ⟨hne.1.symm, ha⟩) (Finset.mem_erase.2 ⟨hne.2.symm, hb⟩), smul_zero])]
    by_cases hia : Set.InjOn τ (t.erase a)
    · have hib := injOn_erase_swap hb hab he hia
      rw [pullC_apply, pullC_apply, if_pos hia, if_pos hib, image_erase_eq hb hab he,
        image_erase_eq ha hab.symm he.symm, smul_smul, smul_smul, ← add_smul, sign_pair ha hb hab he hia,
        neg_add_cancel, zero_smul]
    · have hib : ¬ Set.InjOn τ (t.erase b) := fun hib => hia (injOn_erase_swap ha hab.symm he.symm hib)
      rw [pullC_apply, pullC_apply, if_neg hia, if_neg hib, smul_zero, smul_zero, add_zero]

theorem pullC_mem (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') (τ : κ → ι) (φ : E →ₗ[k] E')
    (hφ : ∀ s : Finset κ, s.Nonempty → ∀ y ∈ A (s.image τ), φ y ∈ B s) (n : ℤ) (c : Finset ι → E)
    (hc : c ∈ cechC A n) : pullC τ φ c ∈ cechC B n := by
  simp only [cechC, Submodule.mem_pi, Set.mem_univ, true_implies, forall_const] at hc ⊢
  intro s
  rw [pullC_apply]
  split_ifs with hs hinj
  · have hcard := Finset.card_image_of_injOn hinj
    have hc' := hc (s.image τ)
    rw [if_pos ⟨hs.1.image τ, by rw [hcard]; exact hs.2⟩] at hc'
    exact zsmul_mem (hφ s hs.1 _ hc') _
  · exact Submodule.zero_mem _
  · rename_i hinj
    have hc' := hc (s.image τ)
    rw [if_neg (fun h' => hs ⟨Finset.image_nonempty.1 h'.1, by
      rw [← Finset.card_image_of_injOn hinj]; exact h'.2⟩), Submodule.mem_bot] at hc'
    rw [hc', map_zero, smul_zero]
    exact Submodule.zero_mem _
  · exact Submodule.zero_mem _

end GlobalTheory.PD.PullMap

namespace GlobalTheory.PD

theorem pullC_isMap : ∀ (k : Type) [Field k] (ι κ : Type) [LinearOrder ι] [LinearOrder κ] (E E' : Type)
    [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') (τ : κ → ι) (φ : E →ₗ[k] E'),
    (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) →
    (∀ s : Finset κ, s.Nonempty → ∀ y ∈ A (s.image τ), φ y ∈ B s) →
    IsMap (GlobalTheory.PD.cech A) (GlobalTheory.PD.cech B) (pullC τ φ) := by
  intro k _ ι κ _ _ E E' _ _ _ _ A B τ φ _ _ hφ n c hc
  exact ⟨PullMap.pullC_mem A B τ φ hφ n c hc, PullMap.pullC_delta τ φ c⟩

end GlobalTheory.PD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechHomologyEquivFam
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechHomologyEquivFam
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

universe v

namespace GlobalTheory.CechFam

variable {R : Type} [Field R] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module R E]
  {C : GlobalTheory.Cube.{v} ι R} (g : ∀ s, C.obj s →ₗ[R] E)

def famMap (p : ℕ) : Cube.Term C p →ₗ[R] (Finset ι → E) where
  toFun x s := g s (Cube.extend C p x s)
  map_add' x y := by funext s; simp
  map_smul' r x := by funext s; simp

theorem famMap_apply (p : ℕ) (x : Cube.Term C p) (s : Finset ι) :
    famMap g p x s = g s (Cube.extend C p x s) := rfl

theorem famMap_of_eq {p : ℕ} (x : Cube.Term C p) {s : Finset ι} (h : s.card = p) :
    famMap g p x s = g s (x ⟨s, h⟩) := by
  rw [famMap_apply, Cube.extend_apply_of_eq]

theorem famMap_of_ne {p : ℕ} (x : Cube.Term C p) {s : Finset ι} (h : s.card ≠ p) :
    famMap g p x s = 0 := by
  rw [famMap_apply, Cube.extend_apply_of_ne C x h, map_zero]

variable {g}

theorem famMap_d (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x)
    (m : ℕ) (x : Cube.Term C (m + 1)) :
    famMap g (m + 1 + 1) (Cube.d C (m + 1) x) = deltaL R ι E (famMap g (m + 1) x) := by
  funext t
  change _ = GlobalTheory.DI.delta (famMap g (m + 1) x) t
  unfold GlobalTheory.DI.delta
  by_cases ht : t.card = m + 1 + 1
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [famMap_of_eq g _ ht, Cube.d_apply_extend, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hn : (t.erase i).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hi, ht]; omega
    rw [map_zsmul, famMap_apply, hres _ _ _ hn]
  · rw [famMap_of_ne g _ ht]
    symm
    refine Finset.sum_eq_zero fun i hi => ?_
    have h1 : 0 < t.card := Finset.card_pos.2 ⟨i, hi⟩
    rw [famMap_of_ne g _ (by rw [Finset.card_erase_of_mem hi]; omega), smul_zero]

theorem famMap_injective (hinj : ∀ s, s.Nonempty → Function.Injective (g s)) (m : ℕ) :
    Function.Injective (famMap g (m + 1)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  funext s
  have h := congrFun hx s.1
  rw [famMap_of_eq g x s.2] at h
  exact hinj s.1 (Finset.card_pos.1 (by rw [s.2]; omega)) (h.trans (map_zero _).symm)

variable {A : Finset ι → Submodule R E}

theorem cechC_apply_mem {n : ℕ} {w : Finset ι → E} (hw : w ∈ cechC A (n : ℤ)) {s : Finset ι}
    (h : s.card = n + 1) : w s ∈ A s := by
  have := (Submodule.mem_pi.1 hw) s (Set.mem_univ _)
  rwa [if_pos ⟨Finset.card_pos.1 (by omega), by omega⟩] at this

theorem cechC_apply_eq_zero {n : ℕ} {w : Finset ι → E} (hw : w ∈ cechC A (n : ℤ)) {s : Finset ι}
    (h : s.card ≠ n + 1) : w s = 0 := by
  have := (Submodule.mem_pi.1 hw) s (Set.mem_univ _)
  rw [if_neg (fun h' => h (by omega))] at this
  exact (Submodule.mem_bot R).1 this

theorem famMap_mem (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s) (n : ℕ)
    (x : Cube.Term C (n + 1)) : famMap g (n + 1) x ∈ cechC A (n : ℤ) := by
  refine Submodule.mem_pi.2 fun s _ => ?_
  split_ifs with h
  · rw [famMap_of_eq g x (by omega : s.card = n + 1), ← hrange s h.1]
    exact LinearMap.mem_range_self _ _
  · rw [famMap_of_ne g x (fun h' => h ⟨Finset.card_pos.1 (by omega), by omega⟩)]
    exact Submodule.zero_mem _

theorem famMap_eq_of_agree {n : ℕ} (x : Cube.Term C (n + 1)) {w : Finset ι → E}
    (hw : w ∈ cechC A (n : ℤ)) (h : ∀ t : {s : Finset ι // s.card = n + 1}, w t.1 = g t.1 (x t)) :
    famMap g (n + 1) x = w := by
  funext s
  by_cases hs : s.card = n + 1
  · rw [famMap_of_eq g x hs]; exact (h ⟨s, hs⟩).symm
  · rw [famMap_of_ne g x hs, cechC_apply_eq_zero hw hs]

theorem famMap_surj (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s) {n : ℕ}
    {w : Finset ι → E} (hw : w ∈ cechC A (n : ℤ)) : ∃ x, famMap g (n + 1) x = w := by
  have : ∀ s : {s : Finset ι // s.card = n + 1}, ∃ y, g s.1 y = w s.1 := fun s => by
    have h := cechC_apply_mem hw s.2
    rw [← hrange _ (Finset.card_pos.1 (by rw [s.2]; omega))] at h
    exact h
  choose x hx using this
  exact ⟨x, famMap_eq_of_agree x hw fun t => (hx t).symm⟩

end GlobalTheory.CechFam

namespace GlobalTheory.CechFam

variable {R : Type} [Field R] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module R E]
  {C : GlobalTheory.Cube.{v} ι R} {g : ∀ s, C.obj s →ₗ[R] E} {A : Finset ι → Submodule R E}

theorem famMap_mem_Z (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ)
    (z : LinearMap.ker (Cube.d C (n + 1))) : famMap g (n + 1) z.1 ∈ (GlobalTheory.PD.cech A).Z (n : ℤ) := by
  refine Submodule.mem_inf.2 ⟨famMap_mem hrange n z.1, ?_⟩
  rw [LinearMap.mem_ker]
  change deltaL R ι E (famMap g (n + 1) z.1) = 0
  rw [← famMap_d hres, LinearMap.mem_ker.1 z.2, map_zero]

def cocMap (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ) :
    LinearMap.ker (Cube.d C (n + 1)) →ₗ[R] (GlobalTheory.PD.cech A).H (n : ℤ) :=
  Submodule.mkQ (((GlobalTheory.PD.cech A).B (n : ℤ)).submoduleOf ((GlobalTheory.PD.cech A).Z (n : ℤ))) ∘ₗ
    LinearMap.codRestrict ((GlobalTheory.PD.cech A).Z (n : ℤ)) (famMap g (n + 1) ∘ₗ (LinearMap.ker _).subtype)
      (famMap_mem_Z hrange hres n)

theorem cocMap_apply (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ)
    (z : LinearMap.ker (Cube.d C (n + 1))) :
    cocMap hrange hres n z = Submodule.Quotient.mk ⟨famMap g (n + 1) z.1, famMap_mem_Z hrange hres n z⟩ :=
  rfl

theorem cocMap_surjective (hinj : ∀ s, s.Nonempty → Function.Injective (g s))
    (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ) :
    Function.Surjective (cocMap hrange hres n) := by
  intro c
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨x, hx⟩ := famMap_surj hrange (Submodule.mem_inf.1 hw).1
  have hd : Cube.d C (n + 1) x = 0 := by
    apply famMap_injective hinj (n + 1)
    rw [famMap_d hres, hx, map_zero]
    exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 hw).2
  refine ⟨⟨x, LinearMap.mem_ker.2 hd⟩, ?_⟩
  rw [cocMap_apply]
  congr 1
  exact Subtype.ext hx

theorem ker_cocMap (hinj : ∀ s, s.Nonempty → Function.Injective (g s))
    (hrange : ∀ s, s.Nonempty → LinearMap.range (g s) = A s)
    (hres : ∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) (n : ℕ) :
    LinearMap.ker (cechClass C n) = LinearMap.ker (cocMap hrange hres n) := by
  ext z
  rw [LinearMap.mem_ker, LinearMap.mem_ker, cocMap_apply, Submodule.Quotient.mk_eq_zero]
  change _ ↔ famMap g (n + 1) z.1 ∈ ((GlobalTheory.PD.cech A).C ((n : ℤ) - 1)).map (deltaL R ι E)
  rw [Submodule.mem_map]
  cases n with
  | zero =>
    rw [cechClass_zero_eq_zero_iff]
    constructor
    · rintro rfl
      exact ⟨0, Submodule.zero_mem _, by rw [map_zero, ZeroMemClass.coe_zero, map_zero]⟩
    · rintro ⟨y, hy, hyz⟩
      have hy0 : y = 0 := by
        funext s
        have := (Submodule.mem_pi.1 hy) s (Set.mem_univ _)
        rw [if_neg (fun h => by
          have := Finset.card_pos.2 h.1
          push_cast at h
          omega)] at this
        exact (Submodule.mem_bot R).1 this
      rw [hy0, map_zero] at hyz
      exact Subtype.ext (famMap_injective hinj 0 (hyz.symm.trans (map_zero _).symm))
  | succ m =>
    rw [cechClass_succ_eq_zero_iff]
    have hc : (GlobalTheory.PD.cech A).C (((m + 1 : ℕ) : ℤ) - 1) = cechC A (m : ℤ) := by
      change cechC A _ = _
      congr 1
      push_cast
      ring
    rw [hc]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨famMap g (m + 1) y, famMap_mem hrange m y, ?_⟩
      rw [← famMap_d hres, hy]
    · rintro ⟨y, hy, hyz⟩
      obtain ⟨x, rfl⟩ := famMap_surj hrange hy
      refine ⟨x, famMap_injective hinj (m + 1) ?_⟩
      rw [famMap_d hres]
      exact hyz

end GlobalTheory.CechFam

open GlobalTheory.CechFam in
theorem GlobalTheory.cechHomologyEquivFam : ∀ (R : Type) [Field R] (ι : Type) [LinearOrder ι] (E : Type) [AddCommGroup E] [Module R E]
    (A : Finset ι → Submodule R E) (C : GlobalTheory.Cube ι R) (g : ∀ s, C.obj s →ₗ[R] E),
    (∀ s, s.Nonempty → Function.Injective (g s)) → (∀ s, s.Nonempty → LinearMap.range (g s) = A s) →
    (∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) →
    ∀ n : ℕ, ∃ e : (cechComplex C).homology n ≃ₗ[R] (GlobalTheory.PD.cech A).H (n : ℤ),
      (∀ (z : LinearMap.ker (Cube.d C (n + 1))) (w : (GlobalTheory.PD.cech A).Z (n : ℤ)),
        (∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (z.1 t)) →
        e (cechClass C n z) = Submodule.Quotient.mk w) ∧
      (∀ z : LinearMap.ker (Cube.d C (n + 1)), ∃ w : (GlobalTheory.PD.cech A).Z (n : ℤ),
        ∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (z.1 t)) ∧
      (∀ (x : Cube.Term C (n + 1)) (w : (GlobalTheory.PD.cech A).Z (n : ℤ)),
        (∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (x t)) →
        Cube.d C (n + 1) x = 0) := by
  intro R _ ι _ E _ _ A C g hinj hrange hres n
  let e : (cechComplex C).homology n ≃ₗ[R] (GlobalTheory.PD.cech A).H (n : ℤ) :=
    ((cechClass C n).quotKerEquivOfSurjective (cechClass_surjective C n)).symm.trans
      ((Submodule.quotEquivOfEq _ _ (ker_cocMap hinj hrange hres n)).trans
        ((cocMap hrange hres n).quotKerEquivOfSurjective (cocMap_surjective hinj hrange hres n)))
  have he : ∀ z, e (cechClass C n z) = cocMap hrange hres n z := by
    intro z
    have h1 : ((cechClass C n).quotKerEquivOfSurjective (cechClass_surjective C n)).symm
        (cechClass C n z) = Submodule.Quotient.mk z := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [e, LinearEquiv.trans_apply, h1, Submodule.quotEquivOfEq_mk]
    rfl
  refine ⟨e, fun z w hw => ?_, fun z => ⟨⟨_, famMap_mem_Z hrange hres n z⟩, fun t => ?_⟩,
    fun x w hw => ?_⟩
  · rw [he, cocMap_apply]
    congr 1
    exact Subtype.ext (famMap_eq_of_agree z.1 (Submodule.mem_inf.1 w.2).1 hw)
  · exact famMap_of_eq g z.1 t.2
  · have hx := famMap_eq_of_agree x (Submodule.mem_inf.1 w.2).1 hw
    apply famMap_injective hinj (n + 1)
    rw [famMap_d hres, hx, map_zero]
    exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 w.2).2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechHomologyEquivFamStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechHomologyEquivFamAlt : ∀ (R : Type) [Field R] (ι : Type) [LinearOrder ι] (E : Type) [AddCommGroup E] [Module R E]
    (A : Finset ι → Submodule R E) (C : GlobalTheory.Cube ι R) (g : ∀ s, C.obj s →ₗ[R] E),
    (∀ s, s.Nonempty → Function.Injective (g s)) → (∀ s, s.Nonempty → LinearMap.range (g s) = A s) →
    (∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) →
    ∀ n : ℕ, ∃ e : (cechComplex C).homology n ≃ₗ[R] (GlobalTheory.PD.cech A).H (n : ℤ),
      (∀ (z : LinearMap.ker (Cube.d C (n + 1))) (w : (GlobalTheory.PD.cech A).Z (n : ℤ)),
        (∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (z.1 t)) →
        e (cechClass C n z) = Submodule.Quotient.mk w) ∧
      (∀ z : LinearMap.ker (Cube.d C (n + 1)), ∃ w : (GlobalTheory.PD.cech A).Z (n : ℤ),
        ∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (z.1 t)) ∧
      (∀ (x : Cube.Term C (n + 1)) (w : (GlobalTheory.PD.cech A).Z (n : ℤ)),
        (∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (x t)) →
        Cube.d C (n + 1) x = 0) := by
  first | (exact @GlobalTheory.cechHomologyEquivFam) | (exact GlobalTheory.cechHomologyEquivFam) | (intros; apply GlobalTheory.cechHomologyEquivFam  <;> assumption)
end
end
