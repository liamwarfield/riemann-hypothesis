module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzBruhatSchroedingerFixedLocalField
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeEqHarishChandraOfGap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaTrilinearFormLocalGroupInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaTrilinearFormLocalGroupInvariant
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod
namespace GlobalTheory.ThetaLocInv

theorem thetaRead_inv : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (X : RowMod D rep (D.nd.j i)) (μ η : HChar D.host.E) (Θ : ThetaMod D M i X μ η) (s : SplitPlace D.host.E) (μw ηw : (s.w.adicCompletion D.host.E)ˣ →* ℂˣ) (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Θ.Ω) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r), TrivOutside {s.v} h → TrivOutside {s.v} g → ∀ Φ Φ' : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)), (Φ' : Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E) → ℂ) = om μw (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV h)) Φ → Θ.ω (h, g) (ι Φ) = ((ηw (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV h))) : ℂˣ) : ℂ) • ι Φ') → ∀ (Wl Vl : Type) [AddCommGroup Wl] [Module ℂ Wl] [AddCommGroup Vl] [Module ℂ Vl] (πl : Representation ℂ (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)) Wl) (σl : Representation ℂ (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) Vl) (T' : Wl →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)), (∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a, ((T' (πl (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) : ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)) : GAf D.host.E D.R.nV → (M.loc i).wt.W) = NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → (M.loc i).wt.W)) → ∀ (T'' : Vl →ₗ[ℂ] ↥X.C), (∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a, ((T'' (σl (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) = X.ρ x (T'' a)) → ∀ (g : GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) (h : GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)) (Φ Φ' : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E))), (Φ' : Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E) → ℂ) = om μw g h Φ → ∀ a c', Θ.Λ (ι Φ') (T' (GlobalTheory.SmGL.twist πl (detChar (Fin D.R.nV) ηw) h a)) (T'' (σl g c')) = Θ.Λ (ι Φ) (T' a) (T'' c') := by
  intro D M i rep X μ η Θ s μw ηw ι c hι Wl Vl _ _ _ _ πl σl T' hT' T'' hT'' g h Φ Φ' hΦ' a c'
  obtain ⟨xh, hxh, exh⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
  obtain ⟨xg, hxg, exg⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.r s
    (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)
  have back : ∀ (n : ℕ) (A : GL (Fin n) (s.w.adicCompletion D.host.E)),
      Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom A) = A := by
    intro n A
    ext k l
    simp
  have eh : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV xh) = h := by rw [exh, back]
  have eg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r xg) = g := by rw [exg, back]
  have hω := hι xh xg hxh hxg Φ Φ' (by rw [eh, eg]; exact hΦ')
  have key := Θ.inv xh xg (ι Φ) (T' a) (T' (πl h a)) (T'' c') (T'' (σl g c'))
    (by rw [← hT' xh hxh a, eh]) (by rw [← hT'' xg hxg c', eg])
  rw [hω, eh] at key
  rw [twist_apply, detChar_apply, map_smul, LinearMap.map_smul, LinearMap.smul_apply]
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at key
  simpa using key

end GlobalTheory.ThetaLocInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaTrilinearFormLocalGroupInvariantStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTrilinearForm_localGroup_invariant : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (X : RowMod D rep (D.nd.j i)) (μ η : HChar D.host.E) (Θ : ThetaMod D M i X μ η) (s : SplitPlace D.host.E) (μw ηw : (s.w.adicCompletion D.host.E)ˣ →* ℂˣ) (ι : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] Θ.Ω) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r), TrivOutside {s.v} h → TrivOutside {s.v} g → ∀ Φ Φ' : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E)), (Φ' : Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E) → ℂ) = om μw (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV h)) Φ → Θ.ω (h, g) (ι Φ) = ((ηw (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV h))) : ℂˣ) : ℂ) • ι Φ') → ∀ (Wl Vl : Type) [AddCommGroup Wl] [Module ℂ Wl] [AddCommGroup Vl] [Module ℂ Vl] (πl : Representation ℂ (GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)) Wl) (σl : Representation ℂ (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) Vl) (T' : Wl →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)), (∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a, ((T' (πl (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) : ↥(NG.AFall D.host.E D.R.nV (M.loc i).wt.ρ)) : GAf D.host.E D.R.nV → (M.loc i).wt.W) = NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → (M.loc i).wt.W)) → ∀ (T'' : Vl →ₗ[ℂ] ↥X.C), (∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a, ((T'' (σl (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) = X.ρ x (T'' a)) → ∀ (g : GL (Fin D.R.r) (s.w.adicCompletion D.host.E)) (h : GL (Fin D.R.nV) (s.w.adicCompletion D.host.E)) (Φ Φ' : SB (Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E))), (Φ' : Matrix (Fin D.R.nV) (Fin D.R.r) (s.w.adicCompletion D.host.E) → ℂ) = om μw g h Φ → ∀ a c', Θ.Λ (ι Φ') (T' (GlobalTheory.SmGL.twist πl (detChar (Fin D.R.nV) ηw) h a)) (T'' (σl g c')) = Θ.Λ (ι Φ) (T' a) (T'' c') := by
  first | exact @GlobalTheory.ThetaLocInv.thetaRead_inv | exact GlobalTheory.ThetaLocInv.thetaRead_inv | (intros; apply GlobalTheory.ThetaLocInv.thetaRead_inv <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.PairReadPf

theorem exists_splitPlace_w (D : D7) (w : PlE D.host) (hw : IsSplitPl D.host w) :
    ∃ s : SplitPlace D.host.E, s.w = w := by
  have hstar : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun _ =>
    D.host.φ₀.injective (by
      rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])
  obtain ⟨x0, hx0, hx0'⟩ := hw
  have hc0 : IsCMField.ringOfIntegersComplexConj D.host.E x0 ∉ w.asIdeal :=
    hx0' _ (by rw [hstar, IsCMField.coe_ringOfIntegersComplexConj])
  obtain ⟨s, hs⟩ := GlobalTheory.SplitConjPlace.exists_splitPlace w x0 hx0 hc0
  have hsw : s.w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) =
      w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
    rw [s.w_under, hs]; rfl
  rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE w s.w hsw with h | h
  · exact ⟨s, h⟩
  · refine ⟨GlobalTheory.SplitConjPlace.conjSP s, HeightOneSpectrum.ext (Ideal.ext fun x => ?_)⟩
    rw [GlobalTheory.SplitConjPlace.mem_conj_w, h, GlobalTheory.SplitConjPlace.mem_conjPlE, GlobalTheory.SplitConjPlace.cO_cO]

theorem exists_ne_of_mem_iSup {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Sort*} (p : ι → Submodule ℂ M)
    (ℓ : M →+ ℂ) {x : M} (hx : x ∈ ⨆ i, p i) (h : ℓ x ≠ 0) : ∃ i, ∃ y ∈ p i, ℓ y ≠ 0 := by
  by_contra H
  push_neg at H
  exact h (Submodule.iSup_induction p (motive := fun z => ℓ z = 0) hx (fun i y hy => H i y hy) (map_zero ℓ)
    (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero]))

theorem exists_ne_of_mem_iSup_sub {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Sort*} (A : Submodule ℂ M)
    (p : ι → Submodule ℂ M) (hpA : ∀ i, p i ≤ A) (ℓ : A →+ ℂ) (x : A) (hx : (x : M) ∈ ⨆ i, p i)
    (h : ℓ x ≠ 0) : ∃ i, ∃ y : A, (y : M) ∈ p i ∧ ℓ y ≠ 0 := by
  by_contra H
  push_neg at H
  obtain ⟨_, hk⟩ := Submodule.iSup_induction p (motive := fun z => ∃ hz : z ∈ A, ℓ ⟨z, hz⟩ = 0) hx
    (fun i y hy => ⟨hpA i hy, H i ⟨y, hpA i hy⟩ hy⟩) ⟨A.zero_mem, by exact map_zero ℓ⟩
    (fun a b ⟨ha, ea⟩ ⟨hb, eb⟩ => ⟨A.add_mem ha hb, by
        have e : (⟨a + b, A.add_mem ha hb⟩ : A) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [e, map_add (f := _), ea, eb, add_zero]⟩)
  exact h hk

def precompₛ {V C : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup C] [Module ℂ C] (T : V →ₗ[ℂ] C) :
    (C →ₗ⋆[ℂ] ℂ) →ₗ[ℂ] (V →ₗ⋆[ℂ] ℂ) where
  toFun f := f.comp T
  map_add' f g := by ext; rfl
  map_smul' a f := by ext; rfl

end GlobalTheory.PairReadPf


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
noncomputable section

namespace GlobalTheory.LocVec

open scoped BigOperators

section Algebra

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def stabSub (π : Representation ℂ G V) (w : V) : Subgroup G where
  carrier := {g | π g w = w}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_eigen_of_sum {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : Representation ℂ G V) (θ : G →* ℂˣ) (H : Subgroup G) [H.FiniteIndex] (hHθ : H ≤ θ.ker)
    {ι : Type} (s : Finset ι) (u : ι → V) (hu : ∀ i ∈ s, ∀ h ∈ H, π h (u i) = u i)
    (T : ι → V →ₗ[ℂ] M) (f : M) (hf0 : f ≠ 0)
    (hf : ∀ g, ∑ i ∈ s, T i (π g (u i)) = ((θ g : ℂˣ) : ℂ) • f) :
    ∃ w : V, w ≠ 0 ∧ ∀ g, π g w = ((θ g : ℂˣ) : ℂ) • w := by
  classical
  haveI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
  let F : V → G → V := fun w x => ((θ x : ℂˣ) : ℂ)⁻¹ • π x w
  have hFg : ∀ w g x, π g (F w x) = ((θ g : ℂˣ) : ℂ) • F w (g * x) := by
    intro w g x
    simp only [F, map_smul, map_mul, Module.End.mul_apply, Units.val_mul, mul_inv, smul_smul]
    congr 1
    have : ((θ g : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  have hFH : ∀ i ∈ s, ∀ x y : G, (x : G ⧸ H) = y → F (u i) x = F (u i) y := by
    intro i hi x y hxy
    have hm : x⁻¹ * y ∈ H := QuotientGroup.eq.1 hxy
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, y = x * h := ⟨x⁻¹ * y, hm, by group⟩
    have hθh : θ h = 1 := hHθ hh
    simp only [F, map_mul, Module.End.mul_apply, hu i hi h hh, hθh, mul_one]
  let e : V → V := fun w => ∑ q : G ⧸ H, F w q.out
  have heig : ∀ i ∈ s, ∀ g, π g (e (u i)) = ((θ g : ℂˣ) : ℂ) • e (u i) := by
    intro i hi g
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_sum, hFg, ← Finset.smul_sum]
    congr 1
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun q => ?_
    apply hFH i hi
    rw [MulAction.toPerm_apply, QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have htot : ∑ i ∈ s, T i (e (u i)) = (Fintype.card (G ⧸ H) : ℂ) • f := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, map_sum]
    rw [Finset.sum_comm]
    have : ∀ q : G ⧸ H, ∑ i ∈ s, T i (F (u i) q.out) = f := by
      intro q
      simp only [F, map_smul, ← Finset.smul_sum, hf, smul_smul]
      rw [inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  by_contra hne
  push_neg at hne
  have hz : ∀ i ∈ s, e (u i) = 0 := by
    intro i hi
    by_contra h0
    obtain ⟨g, hg⟩ := hne _ h0
    exact hg (heig i hi g)
  rw [Finset.sum_eq_zero (fun i hi => by rw [hz i hi, map_zero])] at htot
  have hc : (Fintype.card (G ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact hf0 ((smul_eq_zero.1 htot.symm).resolve_left hc)

end Algebra

section Topology

theorem finiteIndex_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) {C : Set G} (hC : IsCompact C) (hKC : (K : Set G) ⊆ C) (H : Subgroup K)
    (hH : IsOpen (H : Set K)) : H.FiniteIndex := by
  classical
  open scoped Pointwise in
  obtain ⟨W, hWo, hWH⟩ := isOpen_induced_iff.1 hH
  have h1 : (1 : G) ∈ W := by
    have : (1 : K) ∈ (H : Set K) := H.one_mem
    rw [← hWH] at this
    exact this
  obtain ⟨V, hV, hVW⟩ := exists_nhds_split_inv (hWo.mem_nhds h1)
  have hV' : V⁻¹ ∈ nhds (1 : G) := inv_mem_nhds_one G hV
  have hint : (interior V⁻¹).Nonempty := ⟨1, mem_interior_iff_mem_nhds.2 hV'⟩
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates hC hint
  have key : ∀ g : G, ((QuotientGroup.mk : K → K ⧸ H) '' {k : K | g * (k : G) ∈ V⁻¹}).Subsingleton := by
    rintro g _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    apply QuotientGroup.eq.2
    have hk1 : (g * (k : G))⁻¹ ∈ V := hk
    have hk2 : (g * (k' : G))⁻¹ ∈ V := hk'
    have := hVW _ hk1 _ hk2
    have hmem : ((k⁻¹ * k' : K) : G) ∈ W := by
      convert this using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv, inv_inv, mul_inv_rev]
      group
    have : (k⁻¹ * k' : K) ∈ Subtype.val ⁻¹' W := hmem
    rw [hWH] at this
    exact this
  have hfin : (Set.univ : Set (K ⧸ H)).Finite := by
    refine (t.finite_toSet.biUnion fun g _ => (key g).finite).subset ?_
    rintro q -
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g, hg⟩ : ∃ g ∈ t, (k : G) ∈ (fun h => g * h) ⁻¹' V⁻¹ := by
      simpa using ht (hKC k.2)
    exact Set.mem_biUnion hg.1 ⟨k, hg.2, rfl⟩
  haveI : Finite (K ⧸ H) := Set.finite_univ_iff.1 hfin
  exact Subgroup.finiteIndex_of_finite_quotient

end Topology

end GlobalTheory.LocVec

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocVec

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ K, NG.rt L n κ f = ((θ ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f) → ∃ u : σ.V, u ≠ 0 ∧ ∀ g (h : g ∈ K), σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((θ ⟨g, h⟩ : ℂˣ) : ℂ) • u := by
  intro L _ _ _ n a S hS s σ hσ c hc hci K θ hK hθ f hf hf0 hrt
  classical
  have hmem := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent L n a S hS s σ hσ c hc hci hf
  rw [iSup_subtype'] at hmem
  obtain ⟨φ, hφ, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ f).1 hmem
  choose u hu using fun i => LinearMap.mem_range.1 (hφ i)
  let m : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) →* GL (Fin n) (s.w.adicCompletion L) :=
    Matrix.GeneralLinearGroup.map c.toRingHom
  have hm : Continuous m := Units.continuous_map (continuous_id.matrix_map hc)
  let π : Representation ℂ K σ.V := σ.ρ.comp (m.comp K.subtype)
  have hπ : ∀ g : K, π g = σ.ρ (m g) := fun g => rfl
  have hsumF : ∀ g : K, ∑ i ∈ φ.support, (i.1 : σ.V →ₗ[ℂ] _) (π g (u i)) = ((θ g : ℂˣ) : ℂ) • f := by
    rintro ⟨g, hg⟩
    obtain ⟨κ, hκ, rfl⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s g
    have : ∀ i ∈ φ.support, (i.1 : σ.V →ₗ[ℂ] _) (π ⟨s.loc n κ, hg⟩ (u i)) = NG.rt L n κ (φ i) := by
      intro i _
      rw [hπ, ← hu i]
      exact i.2.2 κ hκ (u i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl this, ← map_sum, ← hrt κ hκ hg]
    rw [← hsum]
    rfl
  let H : Subgroup K := θ.ker ⊓ ⨅ i ∈ φ.support, stabSub π (u i)
  have hHo : IsOpen (H : Set K) := by
    rw [Subgroup.coe_inf]
    refine hθ.inter ?_
    simp only [Subgroup.coe_iInf]
    refine isOpen_biInter_finset fun i _ => ?_
    have : (stabSub π (u i) : Set K) = (fun g : K => m g) ⁻¹' {x | σ.ρ x (u i) = u i} := rfl
    rw [this]
    exact (σ.smooth (u i)).preimage (hm.comp continuous_subtype_val)
  have hC : IsCompact (Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :
      Set (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) := by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
    exact GlobalTheory.SplitFlip.isCompact_KO
  haveI : H.FiniteIndex := finiteIndex_of_isOpen K hC (fun g hg => hK g hg) H hHo
  obtain ⟨w, hw0, hw⟩ := exists_eigen_of_sum π θ H inf_le_left φ.support u
    (fun i hi h hh => by
      have := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hh).2 i)
      exact (Subgroup.mem_iInf.1 this hi))
    (fun i => (i.1 : σ.V →ₗ[ℂ] _)) f hf0 hsumF
  exact ⟨w, hw0, fun g hg => hw ⟨g, hg⟩⟩

end GlobalTheory.LocVec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsotyStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localComponent_eigenvector_at_splitPlace_isotypic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ K, NG.rt L n κ f = ((θ ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f) → ∃ u : σ.V, u ≠ 0 ∧ ∀ g (h : g ∈ K), σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((θ ⟨g, h⟩ : ℂˣ) : ℂ) • u := by
  first | exact @GlobalTheory.LocVec.main | exact GlobalTheory.LocVec.main | (intros; apply GlobalTheory.LocVec.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodGenericCharacterOfSeriesTypes
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenericLevelCharacterAlternatingSignConjInv
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField Matrix Formalism.DivisionValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodGenericInv

theorem typeSum_inv_eq {K G : Type} [Field K] [Group G] (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) (χ : G → K)
    (hχ : ∀ g h, χ (g * h * g⁻¹) = χ h) (t : G) (ht : ∀ h ∈ P, t * h * t⁻¹ ∈ P)
    (hψ : ∀ (h : G) (hh : h ∈ P), ψ ⟨t * h * t⁻¹, ht h hh⟩ = (ψ ⟨h, hh⟩)⁻¹) :
    ∑ h : P, χ (h : G) * ((((ψ⁻¹) h)⁻¹ : Kˣ) : K) = ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  have hinj : Function.Injective (fun h : P => (⟨t * h * t⁻¹, ht h h.2⟩ : P)) := by
    intro a b e
    apply Subtype.ext
    have := congrArg Subtype.val e
    simpa using this
  have hbij : Function.Bijective (fun h : P => (⟨t * h * t⁻¹, ht h h.2⟩ : P)) :=
    (Finite.injective_iff_bijective).1 hinj
  rw [← (Equiv.ofBijective _ hbij).sum_comp]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Equiv.ofBijective_apply, MonoidHom.inv_apply, inv_inv]
  rw [hχ, hψ h h.2]

def sgnDiag (κ : Type) [CommRing κ] (r : ℕ) : GL (Fin r) κ where
  val := Matrix.diagonal fun i => (-1) ^ i.val
  inv := Matrix.diagonal fun i => (-1) ^ i.val
  val_inv := by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [← pow_add, ← two_mul, pow_mul]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem sgnDiag_conj_apply {κ : Type} [CommRing κ] {r : ℕ} (u : GL (Fin r) κ) (i j : Fin r) :
    ((sgnDiag κ r * u * (sgnDiag κ r)⁻¹ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      (-1) ^ i.val * (-1) ^ j.val * (u : Matrix (Fin r) (Fin r) κ) i j := by
  show (Matrix.diagonal (fun i : Fin r => ((-1 : κ)) ^ i.val) * (u : Matrix (Fin r) (Fin r) κ) *
    Matrix.diagonal (fun i : Fin r => ((-1 : κ)) ^ i.val)) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

variable {κ : Type} [CommRing κ] {r : ℕ}

theorem sgnDiag_conj_mem_unip {u : GL (Fin r) κ} (hu : u ∈ unip κ r) :
    sgnDiag κ r * u * (sgnDiag κ r)⁻¹ ∈ unip κ r := by
  refine ⟨?_, fun i => ?_⟩
  · intro i j h
    rw [sgnDiag_conj_apply, unip_lower hu (show j < i from h), mul_zero]
  · rw [sgnDiag_conj_apply, unip_diag hu i, ← pow_add, ← two_mul, pow_mul]
    simp

theorem edgeSum_sup_conj (u : GL (Fin r) κ) :
    edgeSum supEdge (sgnDiag κ r * u * (sgnDiag κ r)⁻¹) = - edgeSum supEdge u := by
  unfold edgeSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [sgnDiag_conj_apply]
    unfold supEdge at h
    have hs : ((-1 : κ)) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by rw [← mul_pow]; simp
    rw [h, pow_succ]
    linear_combination (-(u : Matrix (Fin r) (Fin r) κ) i j) * hs
  · simp

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}

def alternatingSignDiagonalLevelGroup (Pg : Finset (Pl E)) (r : ℕ) : G0 Pg r := fun PP => sgnDiag (kP PP.1) r

theorem alternatingSignDiagonal_conj_mem_genericLevel (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) {x : G0 Pg r} (hx : x ∈ (P0 Pg r ψ).H) :
    alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹ ∈ (P0 Pg r ψ).H := by
  intro PP _
  exact sgnDiag_conj_mem_unip (hx PP (Set.mem_univ _))

theorem genericLevelCharacter_alternatingSign_conj_inv (ψ : ∀ PP : Pl E, AddChar (kP PP) ℂ) {x : G0 Pg r} (hx : x ∈ (P0 Pg r ψ).H) :
    (P0 Pg r ψ).chi ⟨alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ hx⟩ = ((P0 Pg r ψ).chi ⟨x, hx⟩)⁻¹ := by
  letI : IsOneApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* ℂˣ) := ⟨fun _ => rfl⟩
  letI : IsMulApply ((Subgroup.pi Set.univ (fun PP : ↥Pg => unip (kP PP.1) r)) →* ℂˣ) := ⟨fun _ _ _ => rfl⟩
  show (∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP))
      ⟨alternatingSignDiagonalLevelGroup Pg r * x * (alternatingSignDiagonalLevelGroup Pg r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ hx⟩ =
    ((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP => unip (kP PP.1) r) PP)) ⟨x, hx⟩)⁻¹
  rw [prod_apply, prod_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun PP _ => ?_
  apply Units.ext
  simp only [MonoidHom.comp_apply, addCharHom, MonoidHom.coe_toHomUnits, Units.val_inv_eq_inv_val]
  show ψ PP.1 (Multiplicative.toAdd (Multiplicative.ofAdd (edgeSum supEdge (sgnDiag (kP PP.1) r * x PP * (sgnDiag (kP PP.1) r)⁻¹)))) =
    (ψ PP.1 (Multiplicative.toAdd (Multiplicative.ofAdd (edgeSum supEdge (x PP)))))⁻¹
  rw [toAdd_ofAdd, toAdd_ofAdd, edgeSum_sup_conj, AddChar.map_neg_eq_inv]

end GlobalTheory.GoodGenericInv

namespace GlobalTheory.GoodGenericInv

theorem level_character_eq_of_eq {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    {L L' : LevelP Pg r LL} (h : L = L') (x : G0 Pg r) (hx : x ∈ L.H) (hx' : x ∈ L'.H) :
    L.chi ⟨x, hx⟩ = L'.chi ⟨x, hx'⟩ := by
  subst h; rfl

end GlobalTheory.GoodGenericInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodGenericCharacterOfSeriesTypes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GoodGenericSer

open GlobalTheory.GoodGenericInv

theorem goodGenericCharacter_of_seriesTypes : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ s, A3.fam3.Ok3 s → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → GoodGeneric A3.A.X F.P0 F.ψ0 ∧ GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hC s hOk hser
  have hG := hC.base.grp
  have hOk2 : A3.A.fam.Ok s := hOk.ok2
  have hprod : ∀ χ ∈ A3.A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g) :=
    GlobalTheory.T.goodCharacter_placewise_cuspidal_parabolic_product D G Pl0 T A3.A Ks R.toRealDat hG.record hser (fun χ hχ => hOk2.irr χ hχ)
  letI : Fintype F.P0 := Fintype.ofFinite _
  have hsum : ∀ χ ∈ A3.A.X, ∑ h : F.P0, χ (h : G) * (((F.ψ0 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (Fintype.card F.P0 : D.what₂.LL) :=
    fun χ hχ => by
      letI : Fintype F.lv2.P0 := (inferInstance : Fintype F.P0)
      exact GlobalTheory.RealOneVector.typeSum_base_eq_card D G Pl0 T A3.A Ks R.toRealDat F.lv2 hG.levels hprod χ hχ
  have hone : ∀ χ ∈ A3.A.X, χ 1 ≠ 0 := fun χ hχ h =>
    GlobalTheory.FinGL.LeviChar.irrChar_one_ne_zero
      (GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar D.what₂.embLL (hOk2.irr χ hχ)) (by rw [h, map_zero])
  have hcard : (Fintype.card F.P0 : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun χ hχ => GlobalTheory.GoodTypeGeneric.chiIdem_mul_lvlIdem_ne_zero _ _ (hone χ hχ) (by rw [hsum χ hχ]; exact hcard),
    fun χ hχ => ?_⟩
  obtain ⟨ψ', -, hlev, -⟩ := hG.levels
  have hcls : ∀ g h, χ (g * h * g⁻¹) = χ h := by
    obtain ⟨n, ρ, -, hρ⟩ := hOk2.irr χ hχ
    intro g h
    apply (algebraMap D.what₂.LL (AlgebraicClosure D.what₂.LL)).injective
    rw [← hρ, ← hρ, ρ.char_conj]
  have hmem : ∀ x : G0 R.Pg D.R.r, R.eG.symm x ∈ F.P0 →
      R.eG.symm (alternatingSignDiagonalLevelGroup R.Pg D.R.r * x * (alternatingSignDiagonalLevelGroup R.Pg D.R.r)⁻¹) ∈ F.P0 := by
    intro x hx
    have h1 : x ∈ (P0 R.Pg D.R.r ψ').H := (congrArg LevelP.H hlev) ▸ (show x ∈ (R.toRealDat.levR F.lv2 false).H from hx)
    have h2 := alternatingSignDiagonal_conj_mem_genericLevel ψ' h1
    have h3 : _ ∈ (R.toRealDat.levR F.lv2 false).H := (congrArg LevelP.H hlev).symm ▸ h2
    exact h3
  let t : G := R.eG.symm (alternatingSignDiagonalLevelGroup R.Pg D.R.r)
  have he : ∀ x, t * R.eG.symm x * t⁻¹ = R.eG.symm (alternatingSignDiagonalLevelGroup R.Pg D.R.r * x * (alternatingSignDiagonalLevelGroup R.Pg D.R.r)⁻¹) := by
    intro x; simp only [t, map_mul, map_inv]
  have ht : ∀ h ∈ F.P0, t * h * t⁻¹ ∈ F.P0 := by
    intro h hh
    obtain ⟨x, rfl⟩ := R.eG.symm.surjective h
    rw [he]; exact hmem x hh
  have hψ : ∀ (h : G) (hh : h ∈ F.P0), F.ψ0 ⟨t * h * t⁻¹, ht h hh⟩ = (F.ψ0 ⟨h, hh⟩)⁻¹ := by
    intro h hh
    obtain ⟨x, rfl⟩ := R.eG.symm.surjective h
    have hs : (⟨t * R.eG.symm x * t⁻¹, ht _ hh⟩ : F.P0) = ⟨_, hmem x hh⟩ := Subtype.ext (he x)
    rw [hs]
    apply Units.ext
    apply D.what₂.embLL.injective
    have hx1 : x ∈ (P0 R.Pg D.R.r ψ').H := (congrArg LevelP.H hlev) ▸ (show x ∈ (R.toRealDat.levR F.lv2 false).H from hh)
    have k1 : Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hmem x hh⟩) =
        (Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hh⟩))⁻¹ :=
      calc Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hmem x hh⟩)
          = (R.toRealDat.levR F.lv2 false).chi ⟨alternatingSignDiagonalLevelGroup R.Pg D.R.r * x * (alternatingSignDiagonalLevelGroup R.Pg D.R.r)⁻¹, hmem x hh⟩ := rfl
        _ = (P0 R.Pg D.R.r ψ').chi ⟨alternatingSignDiagonalLevelGroup R.Pg D.R.r * x * (alternatingSignDiagonalLevelGroup R.Pg D.R.r)⁻¹, alternatingSignDiagonal_conj_mem_genericLevel ψ' hx1⟩ :=
            level_character_eq_of_eq hlev _ _ _
        _ = ((P0 R.Pg D.R.r ψ').chi ⟨x, hx1⟩)⁻¹ := genericLevelCharacter_alternatingSign_conj_inv ψ' hx1
        _ = ((R.toRealDat.levR F.lv2 false).chi ⟨x, hh⟩)⁻¹ := by rw [level_character_eq_of_eq hlev x hh hx1]
        _ = (Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hh⟩))⁻¹ := rfl
    have k3 := congrArg Units.val k1
    simpa [Units.coe_map, Units.val_inv_eq_inv_val, map_inv₀] using k3
  refine GlobalTheory.GoodTypeGeneric.chiIdem_mul_lvlIdem_ne_zero _ _ (hone χ hχ) ?_
  rw [typeSum_inv_eq F.P0 F.ψ0 χ hcls t ht hψ, hsum χ hχ]
  exact hcard

end GlobalTheory.GoodGenericSer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodGenericCharacterOfSeriesTypesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodGenericCharacter_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ s, A3.fam3.Ok3 s → (∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod (D.host.g k))) (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) C), ∀ f, D.ntypes.eSer k f = Formalism.L2.NT.eSerO O D.R.r f) → GoodGeneric A3.A.X F.P0 F.ψ0 ∧ GoodGeneric A3.A.X F.P0 F.ψ0⁻¹ := by
  first | exact @GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes | exact GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes | (intros; apply GlobalTheory.GoodGenericSer.goodGenericCharacter_of_seriesTypes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open Filter Topology
namespace GlobalTheory.TypeBlockFix

variable {F : Type} [Field F] [NumberField F] {F' : Type} [Field F'] [NumberField F']

theorem v_lt_one_iff_tendsto (p : HeightOneSpectrum (𝓞 F)) (y : p.adicCompletion F) :
    Valued.v y < 1 ↔ Tendsto (fun n : ℕ => y ^ n) atTop (𝓝 0) := by
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F p
  rw [tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  exact (Valued.toNormedField.norm_lt_one_iff).symm

theorem v_map_lt_one_iff (p : HeightOneSpectrum (𝓞 F)) (q : HeightOneSpectrum (𝓞 F'))
    (c : p.adicCompletion F ≃+* q.adicCompletion F') (hc : Continuous c) (y : p.adicCompletion F) :
    Valued.v (c y) < 1 ↔ Valued.v y < 1 := by
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F p
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F' q
  have hc' : Continuous c.symm := GlobalTheory.SlocVal.continuous_symm c hc
  rw [v_lt_one_iff_tendsto, v_lt_one_iff_tendsto]
  constructor
  · intro h; simpa using GlobalTheory.SlocVal.tendsto_pow_map c.symm.toRingHom hc' h
  · intro h; simpa using GlobalTheory.SlocVal.tendsto_pow_map c.toRingHom hc h

theorem v_map_le_one_iff (p : HeightOneSpectrum (𝓞 F)) (q : HeightOneSpectrum (𝓞 F'))
    (c : p.adicCompletion F ≃+* q.adicCompletion F') (hc : Continuous c) (y : p.adicCompletion F) :
    Valued.v (c y) ≤ 1 ↔ Valued.v y ≤ 1 := by
  by_cases hy : y = 0
  · simp [hy]
  have hcy : c y ≠ 0 := by simpa using hy
  rw [← not_lt, ← not_lt, Valuation.one_lt_val_iff _ hy, Valuation.one_lt_val_iff _ hcy, ← map_inv₀,
    v_map_lt_one_iff p q c hc]

section loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end loc

theorem complRel_lt_one (p : HeightOneSpectrum (𝓞 F)) (x : p.adicCompletion F) :
    ValuativeRel.valuation (p.adicCompletion F) x < 1 ↔ Valued.v x < 1 := by
  haveI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).lt_one_iff_lt_one

theorem complRel_le_one (p : HeightOneSpectrum (𝓞 F)) (x : p.adicCompletion F) :
    ValuativeRel.valuation (p.adicCompletion F) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  haveI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

end GlobalTheory.TypeBlockFix

namespace GlobalTheory.TypeBlockFix
open ValuativeRel

theorem det_ne_zero_of_mem_blockGrp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (h : GL (Fin (r + t)) k), h ∈ GlobalTheory.BlockType.blockGrp k r t → (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := by
  intro k _ _ _ _ r t h hh
  obtain ⟨⟨g, rfl⟩, hcol⟩ := hh
  set M : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k] := g.val.map (IsLocalRing.residue 𝒪[k]) with hM
  have hcolM : ∀ (a : Fin (r + t)) (j : Fin r), M a (Fin.castAdd t j) = (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k]) a (Fin.castAdd t j) := by
    intro a j
    have h1 := hcol a j
    have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val - 1) a (Fin.castAdd t j) =
        ((g.val a (Fin.castAdd t j) - (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j) : 𝒪[k]) : k) := by
      by_cases e : a = Fin.castAdd t j <;> simp [Matrix.one_apply, e] <;> rfl
    rw [e] at h1
    have hm : g.val a (Fin.castAdd t j) - (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j) ∈ 𝓂[k] :=
      (IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 h1)
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub] at hm
    have : IsLocalRing.residue 𝒪[k] ((1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j)) =
        (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k]) a (Fin.castAdd t j) := by
      by_cases e : a = Fin.castAdd t j <;> simp [Matrix.one_apply, e]
    rw [hM, Matrix.map_apply, ← this]
    exact sub_eq_zero.1 hm
  have hdetM : M.det ≠ 0 := by
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((Matrix.isUnits_det_units g).map _).ne_zero
  set M' := Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm M with hM'
  have h21 : M'.toBlocks₂₁ = 0 := by
    ext i j
    simp only [hM', Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    rw [hcolM]
    exact Matrix.one_apply_ne (fun e => by have := congrArg Fin.val e; simp at this; omega)
  have h11 : M'.toBlocks₁₁ = 1 := by
    ext i j
    simp only [hM', Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Matrix.of_apply, finSumFinEquiv_apply_left]
    rw [hcolM]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne (fun e' => e (Fin.castAdd_inj.1 e')), Matrix.one_apply_ne e]
  have hdet' : M.det = (M.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    rw [← Matrix.det_reindex_self finSumFinEquiv.symm M, ← hM', ← Matrix.fromBlocks_toBlocks M', h21, h11,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
    rfl
  have hD : (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := by
    intro h0
    apply hdetM
    rw [hdet', hM, show (g.val.map (IsLocalRing.residue 𝒪[k])).submatrix (Fin.natAdd r) (Fin.natAdd r) =
      (IsLocalRing.residue 𝒪[k]).mapMatrix (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)) from rfl,
      ← RingHom.map_det, h0, map_zero]
  intro h0
  apply hD
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
      algebraMap 𝒪[k] k (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
    rw [RingHom.map_det]; rfl
  rw [e] at h0
  exact (FaithfulSMul.algebraMap_injective 𝒪[k] k) (h0.trans (map_zero _).symm)

end GlobalTheory.TypeBlockFix

namespace GlobalTheory.TypeBlockFix
open Filter Topology

theorem comp_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (χ : HChar L) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → NG.IsCompAt χ s ξ → GlobalTheory.NPin.IsComp χ s.w μ → ∀ u, ξ u = μ (Units.map c.toRingHom.toMonoidHom u) := by
  intro L _ _ _ s χ ξ μ c hc hci hξ hμ
  let ψ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ := μ.comp (Units.map c.toRingHom.toMonoidHom)
  have hψ : ∀ u, ψ u = μ (Units.map c.toRingHom.toMonoidHom u) := fun u => rfl

  have hkξ : IsOpen (ξ.ker : Set (s.v.adicCompletion (maximalRealSubfield L))ˣ) := by
    obtain ⟨N, hN⟩ := hξ.1
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (maximalRealSubfield L) s.v
    set z : s.v.adicCompletion (maximalRealSubfield L) := (algebraMap _ _ π) ^ N with hz
    have hvz : Valued.v z = WithZero.exp (-(N : ℤ)) := by
      rw [hz, map_pow, adic_valued_algebraMap, hπ, ← WithZero.exp_nsmul]
      congr 1
      simp
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, map_zero] at hvz; exact WithZero.zero_ne_coe hvz
    have hr0 : Valued.v.restrict z ≠ 0 := by
      rw [Ne, map_eq_zero]; exact hz0
    have hS : {y : s.v.adicCompletion (maximalRealSubfield L) | Valued.v (y - 1) < WithZero.exp (-(N : ℤ))} ∈
        𝓝 (1 : s.v.adicCompletion (maximalRealSubfield L)) := by
      refine Valued.mem_nhds.2 ⟨Units.mk0 _ hr0, fun y hy => ?_⟩
      simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hy
      rw [← hvz]; exact hy
    have := Units.continuous_val.continuousAt (x := (1 : (s.v.adicCompletion (maximalRealSubfield L))ˣ)) hS
    refine Filter.mem_of_superset this fun u hu => ?_
    exact hN u (le_of_lt hu)

  have hkψ : IsOpen (ψ.ker : Set (s.v.adicCompletion (maximalRealSubfield L))ˣ) := by
    have : (ψ.ker : Set (s.v.adicCompletion (maximalRealSubfield L))ˣ) =
        (Units.map c.toRingHom.toMonoidHom) ⁻¹' (μ.ker : Set (s.w.adicCompletion L)ˣ) := by
      ext u; simp [ψ]
    rw [this]
    exact hμ.1.preimage (Continuous.units_map _ hc)
  set H := MonoidHom.eqLocus ξ ψ with hH
  have hHo : IsOpen (H : Set (s.v.adicCompletion (maximalRealSubfield L))ˣ) := by
    refine Subgroup.isOpen_mono (H₁ := ξ.ker ⊓ ψ.ker) ?_ (hkξ.inter hkψ)
    intro u hu
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hu
    show ξ u = ψ u
    rw [hu.1, hu.2]

  have hagree : ∀ (a : maximalRealSubfield L) (ha : algebraMap _ (s.v.adicCompletion (maximalRealSubfield L)) a ≠ 0),
      Units.mk0 _ ha ∈ H := by
    intro a ha
    have hx : algebraMap (maximalRealSubfield L) L a ≠ 0 := by
      intro h0; apply ha
      rw [← s.i.commutes a, h0, map_zero]
    have e1 : Units.mk0 _ ha = Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 _ hx) := by
      ext; simp
    have e2 : Units.map c.toRingHom.toMonoidHom (Units.mk0 _ ha) =
        Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom (Units.mk0 _ hx) := by
      ext; simp [← hci]
    show ξ _ = ψ _
    rw [hψ, e2, hμ.2, e1, hξ.2]
  intro u
  show u ∈ H
  have hSo : IsOpen {z : (s.v.adicCompletion (maximalRealSubfield L))ˣ | u⁻¹ * z ∈ H} :=
    hHo.preimage (continuous_const.mul continuous_id)
  have hSu : {z : (s.v.adicCompletion (maximalRealSubfield L))ˣ | u⁻¹ * z ∈ H} ∈ 𝓝 u :=
    hSo.mem_nhds (by simp [H.one_mem])
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap] at hSu
  obtain ⟨T, hT, hTS⟩ := hSu
  have hT' : T ∩ {x | x ≠ 0} ∈ 𝓝 (u : s.v.adicCompletion (maximalRealSubfield L)) :=
    Filter.inter_mem hT (isOpen_ne.mem_nhds u.ne_zero)
  obtain ⟨a, ha1, ha2⟩ := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) s.v).mem_nhds hT'
  have hw : u⁻¹ * Units.mk0 _ ha2 ∈ H := hTS ha1
  have := H.mul_mem hw (H.inv_mem (hagree a ha2))
  rw [mul_inv_cancel_right] at this
  simpa using H.inv_mem this

end GlobalTheory.TypeBlockFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalStdLatticeStabilizerMemMaxCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalStdLatticeStabilizerMemMaxCompact
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertStdLat.loc_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (κ : GAf L n), κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
  GlobalTheory.InertKU.loc_mem_KU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalStdLatticeStabilizerMemMaxCompactStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (κ : GAf L n), κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  first | exact @GlobalTheory.InertStdLat.loc_mem_KU | exact GlobalTheory.InertStdLat.loc_mem_KU | (intros; apply GlobalTheory.InertStdLat.loc_mem_KU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalInjectiveOnTrivOutside
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalInjectiveOnTrivOutside
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertLocInj

open TensorProduct

theorem loc_injective : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x y : GAf L n), TrivOutside {v} x → TrivOutside {v} y →
    Dv.loc x = Dv.loc y → x = y := by
  intro L _ _ _ n v w Dv x y hx hy h
  unfold InertDatum.loc at h
  have h1 := mul_left_cancel (mul_right_cancel h)
  apply Subtype.ext; apply Units.ext
  apply GlobalTheory.SplitAdelic.mat_ext
  intro u
  obtain rfl | hu := eq_or_ne u v
  · ext i j
    have h2 := congrArg (fun g : GL (Fin n) (w.adicCompletion L) => g.val i j) h1
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.GeneralLinearGroup.map] at h2
    simp only [Matrix.map_apply]
    exact Dv.e.injective h2
  · rw [hx u (by simpa using hu), hy u (by simpa using hu)]

end GlobalTheory.InertLocInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalInjectiveOnTrivOutsideStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertDatum_local_injective_on_trivOutside : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x y : GAf L n), TrivOutside {v} x → TrivOutside {v} y → Dv.loc x = Dv.loc y → x = y := by
  first | exact @GlobalTheory.InertLocInj.loc_injective | exact GlobalTheory.InertLocInj.loc_injective | (intros; apply GlobalTheory.InertLocInj.loc_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalMemUnitaryGroupAntidiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalMemUnitaryGroupAntidiagonal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem unitary_conj_by_inverse_pair_preserves_form {K : Type} [CommRing K] (σ : K →+* K) {n : ℕ}
    (P Q M J : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1) (hM2 : Formalism.UG.cT σ M * M = 1)
    (hJ : Formalism.UG.cT σ P * P = J) : Formalism.UG.cT σ (Q * M * P) * J * (Q * M * P) = J := by
  have hQP : Formalism.UG.cT σ Q * Formalism.UG.cT σ P = 1 := by rw [← Formalism.UG.cT_mul, hPQ, Formalism.UG.cT_one]
  subst hJ
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  calc _ = Formalism.UG.cT σ P * Formalism.UG.cT σ M * (Formalism.UG.cT σ Q * Formalism.UG.cT σ P) * (P * Q) * M * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ P * P := by
        rw [hQP, hPQ, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc (Formalism.UG.cT σ P), hM2, Matrix.mul_one]

open Formalism.UG in
theorem inertLoc_mem_GU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by

  have hcomm : ∀ a : AL L, compAt L v (conjAL L a) =
      Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))
        (compAt L v a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [compAt, conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  set f : AL L →+* w.adicCompletion L := (Dv.e : _ →+* w.adicCompletion L).comp (compAt L v) with hf
  have hfc : ∀ a, f (conjAL L a) = Dv.σw (f a) := by
    intro a; simp only [hf, RingHom.comp_apply, hcomm]; exact Dv.comm _
  set A : Matrix (Fin n) (Fin n) (AL L) := ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hA
  have hx : A * conjT (conjAL L) A = 1 := x.2
  set M : Matrix (Fin n) (Fin n) (w.adicCompletion L) := A.map f with hM
  have hMc : (conjT (conjAL L) A).map f = cT Dv.σw M := by
    ext i j; simp [conjT, cT, hM, hfc]
  have hM1 : M * cT Dv.σw M = 1 := by
    rw [← hMc, hM, ← Matrix.map_mul, hx, Matrix.map_one f (map_zero f) (map_one f)]
  have hM2 : cT Dv.σw M * M = 1 := mul_eq_one_comm.mp hM1
  have hloc : ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * M *
        (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := by
    simp only [Formalism.AUTREP.InertDatum.loc, Units.val_mul, hM, hA, hf]
    congr 2
  have hPQ : (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key := unitary_conj_by_inverse_pair_preserves_form Dv.σw _ _ M _ hPQ hM2 Dv.Panti
  rw [← hloc] at key
  exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalMemUnitaryGroupAntidiagonalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by
  first | exact @GlobalTheory.inertLoc_mem_GU | exact GlobalTheory.inertLoc_mem_GU | (intros; apply GlobalTheory.inertLoc_mem_GU <;> assumption)
end
end
