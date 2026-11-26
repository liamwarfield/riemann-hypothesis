module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelign
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalModelPolynomialOnStdFramesInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

noncomputable section

namespace GlobalTheory.WeakBaseChange

theorem isSSRep_of_finiteIndex {Γ k : Type} [Group Γ] [Field k] [CharZero k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (N : Subgroup Γ) [N.FiniteIndex] (h : IsSSRep (r.comp N.subtype)) : IsSSRep r := by
  classical
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W (fun g v hv => hW g v hv)
  let ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun g => (r g : Matrix (Fin n) (Fin n) k).mulVecLin
  have hρ : ∀ g h v, ρ g (ρ h v) = ρ (g * h) v := by
    intro g h v; simp [ρ, Matrix.mulVec_mulVec, map_mul]
  have hρ1 : ∀ v, ρ 1 v = v := by intro v; simp [ρ]
  have hWρ : ∀ g, ∀ v ∈ W, ρ g v ∈ W := fun g v hv => hW g v hv
  let p : (Fin n → k) →ₗ[k] (Fin n → k) := W.subtype ∘ₗ W.linearProjOfIsCompl W' hc
  have hpW : ∀ v, p v ∈ W := fun v => (W.linearProjOfIsCompl W' hc v).2
  have hpl : ∀ w ∈ W, p w = w := fun w hw => by
    have e := congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨w, hw⟩)
    exact e
  have hpr : ∀ w ∈ W', p w = 0 := fun w hw => by
    have e := congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩)
    exact e
  have hpN : ∀ m ∈ N, ∀ v, p (ρ m v) = ρ m (p v) := by
    intro m hm v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top : v ∈ W ⊔ W')
    have hb' : ρ m b ∈ W' := hW' ⟨m, hm⟩ b hb
    rw [show p (a + b) = a by rw [map_add (f := _), hpl a ha, hpr b hb, add_zero], map_add (f := _), map_add (f := _), hpl _ (hWρ m a ha),
      hpr _ hb', add_zero]
  let T : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun g => ρ g ∘ₗ p ∘ₗ ρ g⁻¹
  have hTN : ∀ g, ∀ m ∈ N, T (g * m) = T g := by
    intro g m hm; refine LinearMap.ext fun v => ?_
    simp only [T, LinearMap.comp_apply]
    rw [mul_inv_rev, ← hρ m⁻¹ g⁻¹ v, hpN _ (inv_mem hm), hρ (g * m), mul_inv_cancel_right]
  have hTc : ∀ h g v, ρ h (T g v) = T (h * g) (ρ h v) := by
    intro h g v
    simp only [T, LinearMap.comp_apply]
    rw [hρ h g, hρ, mul_inv_rev, inv_mul_cancel_right]
  have hTW : ∀ g v, T g v ∈ W := fun g v => hWρ g _ (hpW _)
  have hTfix : ∀ g, ∀ w ∈ W, T g w = w := by
    intro g w hw
    simp only [T, LinearMap.comp_apply]
    rw [hpl _ (hWρ _ w hw), hρ, mul_inv_cancel, hρ1]
  haveI : Fintype (Γ ⧸ N) := Fintype.ofFinite _
  let S : (Fin n → k) →ₗ[k] (Fin n → k) := ∑ q : Γ ⧸ N, T q.out
  have hout : ∀ (h : Γ) (q : Γ ⧸ N), T (h • q).out = T (h * q.out) := by
    intro h q
    have e1 : ((h * q.out : Γ) : Γ ⧸ N) = h • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hm : (h * q.out)⁻¹ * (h • q).out ∈ N := QuotientGroup.eq.mp (e1.trans (QuotientGroup.out_eq' _).symm)
    rw [← hTN (h * q.out) _ hm, mul_inv_cancel_left]
  have hS : ∀ h v, ρ h (S v) = S (ρ h v) := by
    intro h v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [S, LinearMap.sum_apply, map_sum, hTc h]
    rw [← Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (Γ ⧸ N)) (fun q => T (Quotient.out q) (ρ h v))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [hout]
  set c : k := (Fintype.card (Γ ⧸ N) : k) with hc_def
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let P : (Fin n → k) →ₗ[k] (Fin n → k) := c⁻¹ • S
  have hPW : ∀ v, P v ∈ W := fun v => by
    simp only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]
    exact W.smul_mem _ (W.sum_mem fun q _ => hTW _ _)
  have hPfix : ∀ w ∈ W, P w = w := fun w hw => by
    simp only [P, S, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [Finset.sum_congr rfl fun q _ => hTfix q.out w hw, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
      smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hP : ∀ h v, ρ h (P v) = P (ρ h v) := fun h v => by
    simp only [P, LinearMap.smul_apply, map_smul, hS]
  refine ⟨LinearMap.ker P, fun g v hv => ?_, ?_⟩
  · show P (ρ g v) = 0
    rw [← hP, LinearMap.mem_ker.mp hv, map_zero]
  · refine ⟨Submodule.disjoint_def.mpr fun v hv hv' => ?_, codisjoint_iff.mpr (eq_top_iff.mpr fun v _ => ?_)⟩
    · rw [← hPfix v hv]; exact hv'
    · have : v = P v + (v - P v) := by abel
      rw [this]
      refine Submodule.add_mem_sup (hPW v) ?_
      rw [LinearMap.mem_ker, map_sub, hPfix _ (hPW v), sub_self]

end GlobalTheory.WeakBaseChange

namespace GlobalTheory.WeakBaseChange

theorem finiteIndex_range_res (E M Ω : Type) [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M]
    [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] : (res E Ω M).range.FiniteIndex := by
  classical
  haveI : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite ℚ E M
  let f : G E Ω ⧸ (res E Ω M).range → (M →ₐ[E] Ω) := fun q =>
    ((Quotient.out q : G E Ω) : Ω →ₐ[E] Ω).comp (IsScalarTower.toAlgHom E M Ω)
  have hf : Function.Injective f := by
    intro q q' hqq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    apply QuotientGroup.eq.mpr
    set a : G E Ω := Quotient.out q
    set b : G E Ω := Quotient.out q'
    have hab : ∀ x : M, a (algebraMap M Ω x) = b (algebraMap M Ω x) := fun x => DFunLike.congr_fun hqq x
    let ρ : G M Ω := AlgEquiv.ofRingEquiv (f := (a⁻¹ * b).toRingEquiv) (fun x => by
      show a.symm (b (algebraMap M Ω x)) = algebraMap M Ω x
      rw [← hab, AlgEquiv.symm_apply_apply])
    exact ⟨ρ, AlgEquiv.ext fun x => rfl⟩
  haveI : Finite (G E Ω ⧸ (res E Ω M).range) := Finite.of_injective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

end GlobalTheory.WeakBaseChange

namespace GlobalTheory.WeakBaseChange

theorem finiteIndex_comap {Γ Γ' : Type} [Group Γ] [Group Γ'] (f : Γ' →* Γ) (N : Subgroup Γ) [N.FiniteIndex] :
    (N.comap f).FiniteIndex := by
  classical
  let g : Γ' ⧸ N.comap f → Γ ⧸ N := fun q => ((f (Quotient.out q) : Γ) : Γ ⧸ N)
  have hg : Function.Injective g := by
    intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    apply QuotientGroup.eq.mpr
    have := QuotientGroup.eq.mp h
    rw [Subgroup.mem_comap, map_mul, map_inv]
    exact this
  haveI : Finite (Γ' ⧸ N.comap f) := Finite.of_injective g hg
  exact Subgroup.finiteIndex_of_finite_quotient

theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have hr : ((((q : ℝ) ^ f) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ^ f := by
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _), ← Real.rpow_mul_natCast (Nat.cast_nonneg _),
      mul_comm]
  induction B using Multiset.induction_on with
  | empty => rfl
  | cons b B ih =>
    simp only [algSat, Multiset.map_cons] at ih ⊢
    simp [hr, mul_pow] at ih ⊢

end GlobalTheory.WeakBaseChange


open GlobalTheory.WeakBaseChange in
theorem GlobalTheory.GalCut.weak_comp_res : ∀ (E M Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] [Field Ω] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] [IsAlgClosure E Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (P : CuspSub M a), IsLift π P → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω M)) := by
  intro E M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι a π P hL r hr
  obtain ⟨hc, hss, hatt⟩ := hr
  refine ⟨hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom E M Ω), ?_, ?_⟩
  · haveI := finiteIndex_range_res E M Ω
    set H := (res E Ω M).range with hH
    haveI : (H.normalCore.comap (res E Ω M)).FiniteIndex := finiteIndex_comap _ _
    refine isSSRep_of_finiteIndex _ (H.normalCore.comap (res E Ω M)) ?_
    have hrange : ((res E Ω M).comp (H.normalCore.comap (res E Ω M)).subtype).range = H.normalCore := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        obtain ⟨y, hy⟩ := (Subgroup.normalCore_le H hx : x ∈ (res E Ω M).range)
        exact ⟨⟨y, by rw [Subgroup.mem_comap, hy]; exact hx⟩, hy⟩
    have := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r ((res E Ω M).comp (H.normalCore.comap (res E Ω M)).subtype)
      (by rw [hrange]; exact Subgroup.normalCore_normal H) hss
    rwa [MonoidHom.comp_assoc]
  · filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under E M).eventually hatt] with w h
    obtain ⟨B, hB, hF⟩ := h
    have h2 := GlobalTheory.AttResTower.normV_under_pow (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    refine ⟨B.map (· ^ f), hL.sat w f B h2 hB, ?_⟩
    have h3 := (UpperTheory.frobenius_power_compatibility E M Ω l ι w f h2).1 a r _ hF
    rw [h2, algSat_pow]
    exact h3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRestStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weaklyAttachedGaloisRepresentation_baseChange_restrict : ∀ (E M Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] [Field Ω] [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] [IsAlgClosure E Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (P : CuspSub M a), IsLift π P → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω M)) := by
  first | exact @GlobalTheory.GalCut.weak_comp_res | exact GlobalTheory.GalCut.weak_comp_res | (intros; apply GlobalTheory.GalCut.weak_comp_res <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeakRepIso
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.GalCut

theorem weak_repIso : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : CuspSub E a) (r r' : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak π ι r' → UpperTheory.V.Af.RepIso r r' := by
  intro E Ω _ _ _ _ _ _ l _ ι a π r r' h h'
  obtain ⟨hc, hss, hev⟩ := h
  obtain ⟨hc', hss', hev'⟩ := h'
  refine GlobalTheory.IsoOfFrobFree.main E Ω l ι a r r' hc hc' hss hss' ?_
  filter_upwards [hev, hev'] with w ⟨B, hB, hF⟩ ⟨B', hB', hF'⟩
  obtain rfl := CG.HasSat.unique hB hB'
  exact ⟨_, hF, hF'⟩

end GlobalTheory.GalCut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceNormVEq
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open Polynomial

namespace GlobalTheory.PlaceNormDec

theorem exists_place_normV_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Q : GlobalTheory.RealGal.QCM E Ω) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range → ∃ w' : HeightOneSpectrum (𝓞 ↥Q.K), w'.under (𝓞 E) = w ∧ IsPlaceOver A w' ∧ normV w' = normV w := by
  intro E Ω _ _ _ _ _ Q w A hA hD
  obtain ⟨w', hw', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω (↥Q.K) w A hA hD
  refine ⟨w', ?_, hw', ?_⟩
  · have hl := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA hw'
    exact HeightOneSpectrum.ext hl.over.symm
  · obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w hA (↥Q.K) Ω A w' hw' (RingEquiv.refl Ω) (algebraMap E ↥Q.K) i hi
    exact hq

end GlobalTheory.PlaceNormDec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlaces
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TwV.Joint.basesAt_span : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → ∀ v, (sysS H X std).latAt v j La.2 = colSpan ((sysS H X std).G.P.W v) ((basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om j La.2) v : Matrix _ _ ((sysS H X std).G.P.Qq v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j La hLa v
  obtain ⟨g, hdet, hg'⟩ := Formalism.L2.G.Pend.latAt_isLattice (sysS H X std) j La.2 hLa v
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hdet
  unfold basesAt
  exact Classical.epsilon_spec (p := fun g' : GL (Fin (((sysS H X std).Pj j).m + 1)) ((sysS H X std).G.P.Qq v) =>
      (sysS H X std).latAt v j La.2 = colSpan ((sysS H X std).G.P.W v) (g' : Matrix _ _ _)) ⟨hu.unit, by rw [hu.unit_spec]; exact hg'⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlacesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tuple_bases_span_at_places : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → ∀ v, (sysS H X std).latAt v j La.2 = colSpan ((sysS H X std).G.P.W v) ((basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om j La.2) v : Matrix _ _ ((sysS H X std).G.P.Qq v)) := by
  first | exact @GlobalTheory.TwV.Joint.basesAt_span | exact GlobalTheory.TwV.Joint.basesAt_span | (intros; apply GlobalTheory.TwV.Joint.basesAt_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSucc
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSucc
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV


set_option maxHeartbeats 2000000 in
theorem Joint.pt_succ_isPt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), J.IsPt std (j + 1) hj La (J.pt std (j + 1) hj La) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) (J.pt std (j + 1) hj La).1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La
  have hG := (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).good
  obtain ⟨x0, hx0⟩ := exists_unitary_pt hG ((I.at' j hj).st.eC.symm La.1).2
    (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2)
  have hspec := Classical.epsilon_spec (p := fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
    (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) x ∧
    x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ⟨x0, hx0⟩
  have hy : (J.cp std).y (j + 1) La = Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm)
      (Classical.epsilon fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
        (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    show (chAt _ _ _ _ _ _ _ _ _ I _ _ _ _ (j + 1) La).y = _
    simp only [chAt, dif_pos hj]
  have hre : ∀ {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (y : GL (Fin m) R), Formalism.L2.PairingIndexBounds.F.reGL (finCongr h.symm) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = y := by
    intro R _ m n h y
    subst h
    ext a b
    simp [Formalism.L2.PairingIndexBounds.F.reGL]
  have key : ∃ x, J.IsPt std (j + 1) hj La x :=
    ⟨⟨_, hspec.2⟩, ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk, by
      rw [hy]
      exact (hre ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm _).symm⟩
  have hpt : J.IsPt std (j + 1) hj La (J.pt std (j + 1) hj La) := Classical.epsilon_spec key
  refine ⟨hpt, ?_⟩
  obtain ⟨hr, hx⟩ := hpt
  rw [hx, hy, hre]
  exact hspec.1

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSuccStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tuple_adelic_point_step_succ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), J.IsPt std (j + 1) hj La (J.pt std (j + 1) hj La) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) (J.pt std (j + 1) hj La).1 := by
  first | exact @GlobalTheory.TwV.Joint.pt_succ_isPt | exact GlobalTheory.TwV.Joint.pt_succ_isPt | (intros; apply GlobalTheory.TwV.Joint.pt_succ_isPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddings
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LamPosOfPosEmb
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.PlaceAbove

theorem involution_conj (D : D7) (x : D.host.E) : sigD D (D.host.conj x) = x := by
  have h3 : ∀ y : D.host.E, sigD D y = D.host.conj y := fun y => bridge_star_holds D.R D.host y
  rw [h3, ← Formalism.L2.Herm.star_conj, ← Formalism.L2.Herm.star_conj, star_star]

theorem posArg_eq_self (D : D7) {n : ℕ} (s : Fin n) (x : D.host.E) :
    (if Even s.val then (if IsOddPos s then D.host.conj x else x)
      else sigD D (if IsOddPos s then D.host.conj x else x)) = x := by
  by_cases hs : s.val % 2 = 1
  · have hodd : IsOddPos s := hs
    have hne : ¬ Even s.val := by rw [Nat.not_even_iff_odd, Nat.odd_iff]; exact hs
    rw [if_neg hne, if_pos hodd, involution_conj]
  · have hodd : ¬ IsOddPos s := hs
    have hev : Even s.val := by rw [Nat.even_iff]; omega
    rw [if_pos hev, if_neg hodd]

end GlobalTheory.TwU.PlaceAbove


open GlobalTheory.TwU.PlaceAbove in
theorem GlobalTheory.TwU.lamPos_of_posEmb : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) (e : D.what₂.LL →+* X.G.Kf), (∀ (z : D.what₂.LL) (hz : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ), E.iK (e z) = lam ⟨D.what₂.embLL z, hz⟩) → (∀ (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : D.host.E), e (tEL D (pos ⟨v, s⟩) (if Even s.val then x else sigD D x)) = X.G.P.ι v ((X.G.P.σ v ^ s.val) (ρ v x))) → LamPos X E pos lam ρ := by
  intro p _ X E D pos lam ρ e hK hpos
  intro v s x
  have h1 := hpos v s (if IsOddPos s then D.host.conj x else x)
  rw [posArg_eq_self D s x] at h1
  have hz := embLL_mem_alg D (tEL D (pos ⟨v, s⟩) x)
  have h2 := hK (tEL D (pos ⟨v, s⟩) x) hz
  have he : Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x = D.what₂.embLL (tEL D (pos ⟨v, s⟩) x) := (tEL_emb D (pos ⟨v, s⟩) x).symm
  have hL : Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = lam ⟨D.what₂.embLL (tEL D (pos ⟨v, s⟩) x), hz⟩ := by
    unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dite_eq_left (he ▸ hz)]
    congr 1
    exact Subtype.ext he
  show Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = _
  rw [hL, ← h2, h1]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddings
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem pos_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  exact GlobalTheory.TwU.lamPos_of_posEmb (sysS H X std) S.E.toCEmb D _ S.lam _ (ex.cmp.embW u w hg) S.hK (J.Gd.cmp.tie u w hg).pos_emb

end GlobalTheory.TwV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddingsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.site_place_induces_position_embeddings : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos) := by
  first | exact @GlobalTheory.TwV.pos_at_site | exact GlobalTheory.TwV.pos_at_site | (intros; apply GlobalTheory.TwV.pos_at_site <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFiniteDataLevelPosBadPrimeFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFiniteDataLevelPosBadPrimeFactors
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV


set_option maxHeartbeats 2000000 in
theorem sNum_lev_site : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), SNum (t.O u μ).S (t.rd u μ).lev := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ _ _
  exact Formalism.L2.Ker.level_structure_counting D L hT Gi Gl Kc Dx cX ex t u μ

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFiniteDataLevelPosBadPrimeFactorsStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.site_finite_data_level_pos_bad_prime_factors : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), SNum (t.O u μ).S (t.rd u μ).lev := by
  first | exact @GlobalTheory.TwV.sNum_lev_site | exact GlobalTheory.TwV.sNum_lev_site | (intros; apply GlobalTheory.TwV.sNum_lev_site <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteBaseDatumIntegralOffBadPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteBaseDatumIntegralOffBadPrimes
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV


set_option maxHeartbeats 2000000 in
theorem Joint.site_base_datum_integral_off_bad_primes : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), ∀ j La La' z, IntOff (t.O u μ).S (J.xi0 std S.Xi j La La' z) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J S j La La' z
  unfold Joint.xi0
  split_ifs with h
  · exact S.law.int _ _ _ _ _ _ _
  · exact Formalism.L2.PairingIndexBounds.F.intOff_zero _

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteBaseDatumIntegralOffBadPrimesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intOff_xi0_of_joint : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), ∀ j La La' z, IntOff (t.O u μ).S (J.xi0 std S.Xi j La La' z) := by
  first | exact @GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes | exact GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes | (intros; apply GlobalTheory.TwV.Joint.site_base_datum_integral_off_bad_primes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartSuccEqComponentChart
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartSuccEqComponentChart
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.TwV.ChartSucc

theorem castSt_ofStepIn_chart {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (St : GlobalTheory.TwU.StepCharts C' i hi) (hSt : St = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn S))
    (c : C.cls i) (c' : C'.cls i) (hc' : c' = castCls h i c) (β : S.Ch) (hβ : S.chOf c = β) :
    St.T = S.T ∧ (St.K (St.chOf c')).lev.Lb = (S.K β).lev.Lb ∧ (St.K (St.chOf c')).lev.U = (S.K β).lev.U ∧
      (St.K (St.chOf c')).lev.Uloc = (S.K β).lev.Uloc ∧ ∀ hc : S.chOf c = β, St.y c' = (S.K β).y ⟨c, hc⟩ := by
  subst hSt hc' h hβ
  exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

end GlobalTheory.TwV.ChartSucc

theorem GlobalTheory.TwV.chart_succ_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → (I.at' j hj).st.T = (D.mem u).A.T ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Lb ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Uloc = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Uloc ∧ ∀ hc : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) = ((I.at' j hj).st.eC.symm La.1).1, (J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2) = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩ := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  have hc := clsOf_chart (S := (I.at' j hj).st) (H.core j hj) La.1 La.2 hLa
  obtain ⟨hT', hLb, hU, hUl, hy⟩ := GlobalTheory.TwV.ChartSucc.castSt_ofStepIn_chart (X.onCh j hj) (I.at' j hj).st (J.St (j + 1) hj) (J.st j hj)
    _ (clsAt X H (j + 1) La.1 La.2) (clsAt_succ X H j hj La.1 La.2) _ hc
  refine ⟨hT'.symm.trans (J.tie.T_eq (j + 1) hj), hLb, hU, hUl, hy⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartSuccEqComponentChartStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → (I.at' j hj).st.T = (D.mem u).A.T ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Lb ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Uloc = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Uloc ∧ ∀ hc : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) = ((I.at' j hj).st.eC.symm La.1).1, (J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2) = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩ := by
  first | exact @GlobalTheory.TwV.chart_succ_eq | exact GlobalTheory.TwV.chart_succ_eq | (intros; apply GlobalTheory.TwV.chart_succ_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZero
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZero
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TwV.Joint.isPt_pt_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), J.IsPt std 0 (Nat.zero_le _) La (J.pt std 0 (Nat.zero_le _) La) ∧ (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) (J.pt std 0 (Nat.zero_le _) La).1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La
  have hr := (lev0At J.Gd u w hg).A.rk
  obtain ⟨x0, hx0⟩ := GlobalTheory.TwU.exists_unitary_pt J.one.good La.1
    (basesAt (chainAt H hT) std (sysS H X std).vp (sysS H X std).unif (sysS H X std).eO (sysS H X std).eO_spec (sysS H X std).dG
      (sysS H X std).dG_spec (sysS H X std).om 0 La.2)
  have hs := Classical.epsilon_spec (p := fun x => (lev0At J.Gd u w hg).A.IsPt La.1
      (basesAt (chainAt H hT) std (sysS H X std).vp (sysS H X std).unif (sysS H X std).eO (sysS H X std).eO_spec (sysS H X std).dG
        (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧ x ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ⟨x0, hx0⟩
  have hex : ∃ x, J.IsPt std 0 (Nat.zero_le _) La x := by
    refine ⟨⟨_, hs.2⟩, hr, ?_⟩
    ext i j
    rfl
  have hp := Classical.epsilon_spec hex
  obtain ⟨hr', he⟩ := hp
  refine ⟨⟨hr', he⟩, ?_⟩
  have h1 : (J.pt std 0 (Nat.zero_le _) La).1 = Classical.epsilon (fun x => (lev0At J.Gd u w hg).A.IsPt La.1
      (basesAt (chainAt H hT) std (sysS H X std).vp (sysS H X std).unif (sysS H X std).eO (sysS H X std).eO_spec (sysS H X std).dG
        (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧ x ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [show (J.pt std 0 (Nat.zero_le _) La).1 = _ from he]
    ext i j
    rfl
  rw [h1]
  exact hs.1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZeroStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tuple_adelic_point_step_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), J.IsPt std 0 (Nat.zero_le _) La (J.pt std 0 (Nat.zero_le _) La) ∧ (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) (J.pt std 0 (Nat.zero_le _) La).1 := by
  first | exact @GlobalTheory.TwV.Joint.isPt_pt_zero | exact GlobalTheory.TwV.Joint.isPt_pt_zero | (intros; apply GlobalTheory.TwV.Joint.isPt_pt_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealisingPolynomialBlockwiseHomogeneous
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealisingPolynomialBlockwiseHomogeneous
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA.BlockHom

open MvPolynomial

theorem two_zpow_inj {a b : ℤ} (h : (2 : ℂ) ^ a = (2 : ℂ) ^ b) : a = b := by
  have h' := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_zpow, Complex.norm_ofNat] at h'
  exact zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num) h'

theorem eval_aeval_gen {σ κ : Type} (g : κ → ℂ) (φ : σ → MvPolynomial κ ℂ) (Q : MvPolynomial σ ℂ) :
    MvPolynomial.eval g (MvPolynomial.aeval φ Q) = MvPolynomial.eval (fun s => MvPolynomial.eval g (φ s)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p s hp => rw [map_mul, map_mul, aeval_X, map_mul, hp, eval_X]

open Classical in
theorem evFr_scale (D : D7) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ)
    (hQ : Q ∈ WtPol ℂ ν) (τ₀ : D.what₂.Tau) (t : ℂ) (ht : t ≠ 0) (y : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    GL3Theta.evFr D Q (fun τ => if τ = τ₀ then t • y τ else y τ) = t ^ (∑ r, ν τ₀ r) * GL3Theta.evFr D Q y := by
  set β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ => if τ = τ₀ then t • (1 : Matrix (Fin n) (Fin n) ℂ) else 1 with hβ
  have hB : IsBor β := by
    intro τ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp only [hβ]; split_ifs <;> simp [Matrix.one_apply_ne (ne_of_lt hsr).symm]
    · simp only [hβ]; split_ifs <;> simp [ht]
  have h1 := congrArg (MvPolynomial.eval (fun k : GL3Theta.FrV D n => y k.1 k.2.1 k.2.2)) (hQ β hB)
  have hL : MvPolynomial.eval (fun k : GL3Theta.FrV D n => y k.1 k.2.1 k.2.2) (colSub β Q) =
      GL3Theta.evFr D Q (fun τ => if τ = τ₀ then t • y τ else y τ) := by
    unfold colSub GL3Theta.evFr
    rw [eval_aeval_gen]
    apply congrArg (fun F => MvPolynomial.eval F Q)
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, eval_C, eval_X, hβ]
    by_cases hk : k.1 = τ₀
    · simp [hk, Matrix.one_apply, mul_comm]
    · simp [hk, Matrix.one_apply]
  rw [← hL, h1, MvPolynomial.smul_eval]
  unfold GL3Theta.evFr
  congr 1
  rw [Finset.prod_eq_single τ₀]
  · simp [hβ, Finset.prod_pow_eq_pow_sum]
  · intro τ _ hτ
    simp [hβ, hτ]
  · simp

open Classical in
theorem prod_scale {ι : Type} [Fintype ι] (τ₀ : ι) (A B : ι → ℂ) (k : ℂ)
    (hAB : ∀ τ, A τ = if τ = τ₀ then k * B τ else B τ) (e : ι → ℤ) :
    ∏ τ, A τ ^ e τ = k ^ e τ₀ * ∏ τ, B τ ^ e τ := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ₀), ← Finset.mul_prod_erase (s := Finset.univ) (fun τ => B τ ^ e τ) (Finset.mem_univ τ₀)]
  rw [hAB τ₀, ite_eq_left rfl, mul_zpow, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro τ hτ
  rw [hAB τ, ite_eq_right (Finset.ne_of_mem_erase hτ)]

open Classical in
theorem zT_scale {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}
    (f f' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, IsUnit (f τ).det) (τ₀ : D.what₂.Tau) (c : ℂ) (hc : c ≠ 0)
    (hf' : ∀ τ, f' τ = if τ = τ₀ then (if IsOddPos (pos.symm τ₀).2 then c⁻¹ else c) • f τ else f τ) (τ : D.what₂.Tau) :
    zT X D pos f' τ = if τ = τ₀ then c • zT X D pos f τ else zT X D pos f τ := by
  unfold zT
  rw [hf' τ]
  by_cases hτ : τ = τ₀
  · subst hτ
    simp only [ite_true]
    by_cases ho : IsOddPos (pos.symm τ).2
    · simp only [ho, ite_true]
      rw [show c⁻¹ • f τ = (Units.mk0 c⁻¹ (inv_ne_zero hc)) • f τ from rfl, Matrix.inv_smul' (k := Units.mk0 c⁻¹ (inv_ne_zero hc)) (h := hf τ)]
      ext a b
      simp [Matrix.submatrix_apply, Matrix.transpose_apply, Units.smul_def]
    · simp [ho]
  · simp [hτ]

def dg {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) (τ₀ : D.what₂.Tau)
    (m : Var (X.Pj i) →₀ ℕ) : ℕ :=
  ∑ x : Var (X.Pj i), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀ then m x else 0

open Classical in
theorem valZ_scale {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (R : XR (X.Pj i) ℂ) (f f' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, IsUnit (f τ).det)
    (τ₀ : D.what₂.Tau) (hf' : ∀ τ, f' τ = if τ = τ₀ then (if IsOddPos (pos.symm τ₀).2 then (2:ℂ)⁻¹ else 2) • f τ else f τ) :
    valZ X D pos i h R f' = valZ X D pos i h (∑ m ∈ R.support, monomial m (AddMonoidAlgebra.coeff R m * 2 ^ (dg X D pos i τ₀ m))) f := by
  have hg : ∀ x : Var (X.Pj i), zT X D pos f' (posJ X D pos i ⟨x.1, x.2.1⟩) (Fin.cast h x.2.2.1) (Fin.cast h x.2.2.2) =
      (2:ℂ) ^ (if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀ then 1 else 0) *
        zT X D pos f (posJ X D pos i ⟨x.1, x.2.1⟩) (Fin.cast h x.2.2.1) (Fin.cast h x.2.2.2) := by
    intro x
    rw [zT_scale X D pos f f' hf τ₀ 2 two_ne_zero hf']
    by_cases hb : (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀
    · simp [hb]
    · have e : posJ X D pos i ⟨x.1, x.2.1⟩ ≠ τ₀ := fun e => hb (by rw [← e]; simp)
      simp [e, hb]
  unfold valZ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.eval_eq, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have hsum : (∑ x ∈ m.support, (if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ₀ then 1 else 0) * m x) = dg X D pos i τ₀ m := by
    unfold dg
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).trans ?_
    · intro x _ hx
      have hx0 : m x = 0 := by simpa using hx
      simp [hx0]
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
  simp only [hg, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  rw [hsum, Finset.prod_subset (Finset.subset_univ m.support) (fun x _ hx => by
    have hx0 : m x = 0 := by simpa using hx
    simp [hx0])]
  ring

theorem realises_blockHom : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ), Q ∈ WtPol ℂ ν → Realises X D pos i h a Q R → ∀ m ∈ R.support, ∀ τ, (∑ x : Var (X.Pj i), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ then (m x : ℤ) else 0) = (if IsOddPos (pos.symm τ).2 then -1 else 1) * ((∑ r, (ν τ r : ℤ)) - n * a τ) - n * eT X D pos i τ := by
  intro p _ X D pos i n h a ν Q R hQ hR m hm τ₀
  classical
  obtain ⟨ε, hε⟩ : ∃ ε : ℤ, ε = if IsOddPos (pos.symm τ₀).2 then -1 else 1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℂ, t = if IsOddPos (pos.symm τ₀).2 then (2:ℂ)⁻¹ else 2 := ⟨_, rfl⟩
  have htε : t = (2:ℂ) ^ ε := by
    rw [ht, hε]; split_ifs <;> simp
  have ht0 : t ≠ 0 := by rw [htε]; exact zpow_ne_zero _ two_ne_zero
  obtain ⟨R2, hR2⟩ : ∃ R2 : XR (X.Pj i) ℂ, R2 = ∑ m ∈ R.support, monomial m (AddMonoidAlgebra.coeff R m * 2 ^ (dg X D pos i τ₀ m)) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (((2:ℂ) ^ n) ^ eT X D pos i τ₀)⁻¹ * ((t ^ n) ^ (-(a τ₀)) * t ^ (∑ r, ν τ₀ r)) := ⟨_, rfl⟩
  have key : ∀ f : Fr1 D n, ev1 X D pos i h R2 f = c * ev1 X D pos i h R f := by
    intro f
    have hfu : ∀ τ, IsUnit (f.1 τ).det := f.2
    let f' : Fr1 D n := ⟨fun τ => if τ = τ₀ then t • f.1 τ else f.1 τ, by
      intro τ
      by_cases hτ : τ = τ₀
      · simp only [hτ, ite_true, Matrix.det_smul]
        exact (IsUnit.mk0 _ (pow_ne_zero _ ht0)).mul (hfu τ₀)
      · simp only [hτ, ite_false]; exact hfu τ⟩
    have hf' : ∀ τ, f'.1 τ = if τ = τ₀ then (if IsOddPos (pos.symm τ₀).2 then (2:ℂ)⁻¹ else 2) • f.1 τ else f.1 τ := by
      intro τ; rw [← ht]
    have e1 := GlobalTheory.T.evalStdFrames_eq_detPower_mul_blockValue X D pos i h R2 f
    have e2 := GlobalTheory.T.evalStdFrames_eq_detPower_mul_blockValue X D pos i h R f'
    have e3 := hR f'
    have e4 := hR f
    have hv : valZ X D pos i h R f'.1 = valZ X D pos i h R2 f.1 := by
      rw [hR2]; exact valZ_scale X D pos i h R f.1 f'.1 hfu τ₀ hf'
    have hdz : ∏ τ, (zT X D pos f'.1 τ).det ^ eT X D pos i τ =
        ((2:ℂ) ^ n) ^ eT X D pos i τ₀ * ∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ := by
      apply prod_scale
      intro τ
      rw [zT_scale X D pos f.1 f'.1 hfu τ₀ 2 two_ne_zero hf' τ]
      split_ifs <;> simp
    have hdf : ∏ τ, (f'.1 τ).det ^ (-(a τ)) = (t ^ n) ^ (-(a τ₀)) * ∏ τ, (f.1 τ).det ^ (-(a τ)) := by
      apply prod_scale
      intro τ
      show (if τ = τ₀ then t • f.1 τ else f.1 τ).det = _
      split_ifs <;> simp
    have hq : GL3Theta.evFr D Q f'.1 = t ^ (∑ r, ν τ₀ r) * GL3Theta.evFr D Q f.1 := evFr_scale D ν Q hQ τ₀ t ht0 f.1
    have hK : ((2:ℂ) ^ n) ^ eT X D pos i τ₀ ≠ 0 := zpow_ne_zero _ (pow_ne_zero _ two_ne_zero)
    have hE := e2.symm.trans e3
    rw [hv, hdz, hdf, hq] at hE
    rw [e1, e4, hc]
    calc (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R2 f.1
        = (((2:ℂ) ^ n) ^ eT X D pos i τ₀)⁻¹ * (((2:ℂ) ^ n) ^ eT X D pos i τ₀ *
            (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos i τ) * valZ X D pos i h R2 f.1) := by
          field_simp
      _ = _ := by rw [hE]; ring
  have hz : R2 - c • R = 0 := by
    apply GlobalTheory.T.evalModelPolynomialOnStdFrames_injective X D pos i h
    intro f
    rw [map_sub, map_smul]
    simp [key f]
  have hcoef : AddMonoidAlgebra.coeff R2 m = AddMonoidAlgebra.coeff R m * 2 ^ (dg X D pos i τ₀ m) := by
    rw [hR2, coeff_sum]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      rw [coeff_monomial, ite_eq_right hb]
    · intro hm'; exact absurd hm hm'
  have hm0 : AddMonoidAlgebra.coeff R m ≠ 0 := (mem_support_iff.mp hm)
  have h2 : (2:ℂ) ^ (dg X D pos i τ₀ m) = c := by
    have := congrArg (AddMonoidAlgebra.coeff · m) hz
    rw [coeff_sub, coeff_smul, hcoef, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, sub_eq_zero, smul_eq_mul] at this
    exact mul_left_cancel₀ hm0 (by rw [this]; ring)
  have hcz : c = (2:ℂ) ^ (-((n : ℤ) * eT X D pos i τ₀) + (ε * ((n : ℤ) * (-(a τ₀))) + ε * ((∑ r, ν τ₀ r : ℕ) : ℤ))) := by
    have a1 : ((2:ℂ) ^ n) ^ (eT X D pos i τ₀) = (2:ℂ) ^ ((n : ℤ) * eT X D pos i τ₀) := by rw [zpow_mul, zpow_natCast]
    have a2 : (((2:ℂ) ^ ε) ^ n) ^ (-(a τ₀)) = (2:ℂ) ^ (ε * ((n : ℤ) * (-(a τ₀)))) := by rw [zpow_mul, zpow_mul, zpow_natCast]
    have a3 : ((2:ℂ) ^ ε) ^ (∑ r, ν τ₀ r) = (2:ℂ) ^ (ε * ((∑ r, ν τ₀ r : ℕ) : ℤ)) := by rw [zpow_mul, zpow_natCast]
    rw [hc, htε, a1, a2, a3, zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_neg]
  have hfin : ((dg X D pos i τ₀ m : ℕ) : ℤ) = -((n : ℤ) * eT X D pos i τ₀) + (ε * ((n : ℤ) * (-(a τ₀))) + ε * ((∑ r, ν τ₀ r : ℕ) : ℤ)) :=
    two_zpow_inj (by rw [zpow_natCast, h2, hcz])
  unfold dg at hfin
  push_cast at hfin
  rw [hfin, hε]
  ring

end GlobalTheory.TwV.DelA.BlockHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealisingPolynomialBlockwiseHomogeneousStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realising_polynomial_blockwise_homogeneous : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ), Q ∈ WtPol ℂ ν → Realises X D pos i h a Q R → ∀ m ∈ R.support, ∀ τ, (∑ x : Var (X.Pj i), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj i).nV, Fin ((X.Pj i).n' v)) = (posJ X D pos i).symm τ then (m x : ℤ) else 0) = (if IsOddPos (pos.symm τ).2 then -1 else 1) * ((∑ r, (ν τ r : ℤ)) - n * a τ) - n * eT X D pos i τ := by
  first | exact @GlobalTheory.TwV.DelA.BlockHom.realises_blockHom | exact GlobalTheory.TwV.DelA.BlockHom.realises_blockHom | (intros; apply GlobalTheory.TwV.DelA.BlockHom.realises_blockHom <;> assumption)
end
end
