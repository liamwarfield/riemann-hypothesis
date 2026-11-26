module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CharpolyEqProd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtDense
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtinLit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.PtSmall

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HeckeMap
noncomputable def UpperTheory.Reformulated.B.Qf17.heckePol :
    {A : Type} → [inst : CommRing A] → ℕ → ℕ → (ℕ → A) → Polynomial A :=
    fun {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) ↦
      ∑ j ∈ Finset.range (n + (1 : ℕ)),
        (Polynomial.C : A → Polynomial A) ((-1 : A) ^ j * (↑q : A) ^ (j * (j - (1 : ℕ)) / (2 : ℕ)) * a j) *
          Polynomial.X ^ (n - j)

theorem UpperTheory.Reformulated.B.Qf17.hecke_map :
    ∀ {A B : Type} [inst : CommRing A] [inst_1 : CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A),
      Polynomial.map f (UpperTheory.Reformulated.B.Qf17.heckePol n q a) = UpperTheory.Reformulated.B.Qf17.heckePol n q fun (j : ℕ) ↦ (f : A → B) (a j) := by
  intro A B _ _ f n q a
  unfold UpperTheory.Reformulated.B.Qf17.heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    map_mul f, map_mul f, map_pow f, map_pow f, map_neg f, map_one f, map_natCast f]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.WdCharpoly
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.DiagOfCong
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Hi.Up

private theorem cong_roots {K : Type} [NormedField K] [IsUltrametricDist K] {N : ℕ} (hN : ‖(N : K)‖ = 1)
    (s t : Multiset K) (hs : ∀ a ∈ s, a ^ N = 1) (ht : ∀ a ∈ t, a ^ N = 1)
    (h : ∀ k, ‖((s.map fun a => X - C a).prod).coeff k - ((t.map fun a => X - C a).prod).coeff k‖ < 1) : s = t := by
  let O : ValuationSubring K := (NormedField.valuation (K := K)).valuationSubring
  have hm : ∀ a : O, residue O a = 0 ↔ ‖(a : K)‖ < 1 := fun a => by
    rw [residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact Iff.rfl
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  let T := {a : O // a ^ N = 1}
  have lift : ∀ s : Multiset K, (∀ a ∈ s, a ^ N = 1) → ∃ s' : Multiset T, s = s'.map fun a => (a.1 : K) := fun s hs =>
    ⟨s.attach.map fun a => ⟨⟨a.1, show ‖a.1‖₊ ≤ 1 from
      ((pow_eq_one_iff_left hN0).1 (by rw [← nnnorm_pow, hs _ a.2, nnnorm_one])).le⟩, Subtype.ext (hs _ a.2)⟩, by
        simp [Multiset.map_map]⟩
  obtain ⟨s, rfl⟩ := lift s hs
  obtain ⟨t, rfl⟩ := lift t ht
  have inj : Function.Injective fun a : T => residue O a.1 := by
    intro a b hab
    have hab : residue O a.1 = residue O b.1 := hab
    have h1 := Commute.geom_sum₂_mul (Commute.all a.1 b.1) N
    rw [a.2, b.2, sub_self, mul_eq_zero] at h1
    refine Subtype.ext (sub_eq_zero.1 (h1.resolve_left fun h2 => ?_))
    have h3 := congrArg (residue O) h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, hab, map_zero] at h3
    rw [geom_sum₂_self, mul_eq_zero] at h3
    rcases h3 with h3 | h3
    · rw [← map_natCast (residue O), hm] at h3
      simp [hN] at h3
    · have h4 := congrArg (residue O) b.2
      rw [map_pow, eq_zero_of_pow_eq_zero h3, zero_pow hN0, map_one] at h4
      exact zero_ne_one h4
  have e : ∀ s : Multiset T, ((s.map fun a => (a.1 : K)).map fun a => X - C a).prod =
      ((s.map fun a : T => X - C a.1).prod).map O.subtype := fun s => by
    simp [Polynomial.map_multiset_prod, Multiset.map_map]
  have e' : ∀ s : Multiset T, ((s.map fun a : T => X - C a.1).prod).map (residue O) =
      ((s.map fun a => residue O a.1).map fun a => X - C a).prod := fun s => by
    simp [Polynomial.map_multiset_prod, Multiset.map_map]
  have h5 : ((s.map fun a : T => X - C a.1).prod).map (residue O) = ((t.map fun a : T => X - C a.1).prod).map (residue O) := by
    ext k
    have := h k
    rw [e, e, coeff_map, coeff_map, ← map_sub] at this
    rw [coeff_map, coeff_map, ← sub_eq_zero, ← map_sub, hm]
    exact this
  have h6 := congrArg Polynomial.roots h5
  rw [e', e', roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h6
  rw [Multiset.map_injective inj h6]

private theorem fin_range {Γ K H : Type} [Group Γ] [Field K] [Group H] {n N : ℕ} (hN : N ≠ 0) (t : Fin n → Γ →* Kˣ)
    (ht : ∀ i g, t i g ^ N = 1) (ρ : Γ →* H) (hρ : ∀ g, (∀ i, t i g = 1) → ρ g = 1) : (Set.range ρ).Finite := by
  haveI : NeZero N := ⟨hN⟩
  let T : Γ → Fin n → rootsOfUnity N K := fun g i => ⟨t i g, ht i g⟩
  refine (Set.finite_range fun z => ρ (Function.invFun T z)).subset ?_
  rintro _ ⟨g, rfl⟩
  refine ⟨T g, ?_⟩
  have h1 : T (Function.invFun T (T g)) = T g := Function.invFun_eq ⟨g, rfl⟩
  have h2 := hρ (Function.invFun T (T g) * g⁻¹) fun i => by
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact congrArg Subtype.val (congrFun h1 i)
  rwa [map_mul, map_inv, mul_inv_eq_one] at h2

theorem diag_of_cong {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] {n N : ℕ} (hN : ‖(N : Qbar l)‖ = 1)
    (t : Fin n → Γ →* (Qbar l)ˣ) (ht : ∀ i g, t i g ^ N = 1) (ρ : Γ →* GL (Fin n) (Qbar l))
    (hρ : ∀ g, (∀ i, t i g = 1) → ρ g = 1)
    (h : ∀ g k, ‖(ρ g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff k - (∏ i, (X - C (t i g : Qbar l))).coeff k‖ < 1) :
    ∃ P : GL (Fin n) (Qbar l), ∀ g, ((P * ρ g * P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Matrix.diagonal fun i => (t i g : Qbar l) := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  let δ : Γ →* GL (Fin n) (Qbar l) := (W.diagRep t).toHomUnits
  have hδ : ∀ g, (δ g : Matrix (Fin n) (Fin n) (Qbar l)) = Matrix.diagonal fun i => (t i g : Qbar l) := fun g => rfl
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ δ (Formalism.MainNotions.SumRepresentations.isSSRep_of_finite ρ (fin_range hN0 t ht ρ hρ))
    (Formalism.MainNotions.SumRepresentations.isSSRep_of_finite δ (fin_range hN0 t ht δ fun g hg => Units.ext (by simp [hδ, hg]))) fun g => by
      rw [hδ, Matrix.charpoly_diagonal]
      have hs := (IsAlgClosed.splits (ρ g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly).eq_prod_roots_of_monic
        (Matrix.charpoly_monic _)
      have e : ∏ i, (X - C (t i g : Qbar l)) = ((Finset.univ.val.map fun i => (t i g : Qbar l)).map fun a => X - C a).prod := by
        rw [Multiset.map_map]; rfl
      refine hs.trans (e ▸ congrArg (fun s : Multiset (Qbar l) => (s.map fun a => X - C a).prod)
        (cong_roots hN _ _ (fun a ha => ?_) (fun a ha => ?_) fun k => by rw [← e, ← hs]; exact h g k))
      · have h1 := spectrum.pow_mem_pow _ N (Matrix.mem_spectrum_iff_isRoot_charpoly.2 (isRoot_of_mem_roots ha))
        rw [← Units.val_pow_eq_pow_val, ← map_pow, hρ _ fun i => by rw [map_pow, ht], Units.val_one] at h1
        by_contra h2
        refine h1 ?_
        rw [← map_one (algebraMap (Qbar l) _), resolventSet, Set.mem_setOf_eq, ← map_sub]
        exact (IsUnit.mk0 _ (sub_ne_zero.2 h2)).map _
      · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha
        rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  refine ⟨P⁻¹, fun g => ?_⟩
  rw [inv_inv, ← hδ, ← hP g]

end UpperTheory.V.Hi.Up
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Hi.Up

theorem comp_ex {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ)
    {w : Plc L} (hw : IsSplitAt w) :
    ∃ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL L n w hw
  obtain ⟨τ, -, -, f, h0, h1, h2⟩ := GlobalTheory.T.exists_admissible_localComponent_definiteUnitary L n ⟨σ, hσ⟩ w
  refine ⟨GlobalTheory.InertSatake.transport e τ, (GlobalTheory.InertSatake.transport e τ).irred, f, h0, h1, fun x v => ?_⟩
  have := GlobalTheory.InertSatake.transport_apply e τ x v
  rw [he] at this
  exact (congrArg f this).trans (h2 x v)

section WD

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {w : Plc F} {A : ValuationSubring Ω} {h : IsPlaceOver A w}

theorem wd_charpoly (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {r r' : G F Ω →* GL (Fin n) (Qbar l)} {x : WD h}
    (hx : IsWDOf ι r x) (hx' : IsWDOf ι r' x) (g : Weil h) :
    (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = (r' g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
  have e := hx.wdOf_eq hl
  have e' := hx'.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  obtain ⟨t', ht', φ', hφ', N', b', hN', -⟩ := hx'
  refine Polynomial.map_injective ι.toRingHom ι.injective ?_
  rw [← hN.charPol_wdOf hl ht ι g, ← hN'.charPol_wdOf hl ht' ι g, e, e']

theorem wd_type (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {r : G F Ω →* GL (Fin n) (Qbar l)} (χ : Fin n → Ine (F := F) A →* (Qbar l)ˣ)
    (hχ : ∀ i, IsOpen ((χ i).ker : Set (Ine (F := F) A))) (g : GL (Fin n) (Qbar l))
    (hg : ∀ s : Ine (F := F) A, ((g * r s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Matrix.diagonal fun i => (χ i s : Qbar l)) {x : WD h} (hx : IsWDOf ι r x) :
    IsTypeWD h (fun i => W.pushCh ι.toRingHom (χ i)) x := by
  let r' : G F Ω →* GL (Fin n) (Qbar l) := (MulAut.conj g).toMonoidHom.comp r
  have hr' : ∀ s, r' s = g * r s * g⁻¹ := fun s => rfl
  have hx' : IsWDOf ι r' x := hx.of_conj hl g fun s => by rw [hr', inv_mul_cancel_right]
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx'
  have hs : IsSmooth (r'.comp (Weil h).subtype) := by
    refine .of_open (isOpen_iInter_of_finite hχ) (Set.mem_iInter.2 fun i => (χ i).ker.one_mem) fun σ hσ => Units.ext ?_
    change (r' σ : Matrix (Fin n) (Fin n) (Qbar l)) = 1
    rw [hr', hg σ]
    simp [fun i => show χ i σ = 1 from Set.mem_iInter.1 hσ i]
  obtain rfl : N = 0 := hN.unique ht ((isMonodromy_zero_iff (h := h)).mpr hs)
  refine ⟨a, rfl, ?_, fun s => ?_⟩
  · rw [ha.1, map_zero]
  · rw [IsFrobSS.ρ_ineIncl (ρ := hN.rep hl ht hφ ι) ha (hN.isSmooth_rep hl ht _ ι), hN.rep_apply, wdMat_zero, coe_ineIncl, hr',
      hg s, toEndC_apply, Matrix.diagonal_map (map_zero ι)]
    rfl

end WD

theorem chi_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G) (y : MonoidAlgebra A H) :
    (D.comap φ).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A φ y) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp

section Pt

variable {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : Resid F c.O n} {B : UniversalOrdinaryDeterminantRing r}
  (x : B.B →ₐ[c.O] Qbar l) {Γ : Type} [Group Γ] (p : Γ →* F.G₀) (ρ : Γ →* GL (Fin n) (Qbar l))
  (hx : (B.u.D.map (x : B.B →+* Qbar l)).comap p = W.GDet.ofRep (W.mat ρ))

include hx

theorem chi_pt (g : Γ) : (B.u.D.chi (MonoidAlgebra.single (p g) 1)).map (x : B.B →+* Qbar l) =
    (ρ g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
  have e := (AlgebraTools.Det.repApi (W.mat ρ)).2.1 g
  rw [← hx, chi_comap] at e
  rw [← (AlgebraTools.Det.mapApi B.u.D (x : B.B →+* Qbar l)).1]
  simp only [MonoidAlgebra.mapRingHom_single, map_one]
  simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single] at e
  exact e

theorem chi_cong (g : Γ) (P : c.O[X]) (hP : r.Dbar.chi (MonoidAlgebra.single (p g) 1) = P.map (residue c.O)) (k : ℕ) :
    ‖(ρ g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.coeff k - (P.map (algebraMap c.O (Qbar l))).coeff k‖ < 1 := by
  rw [← chi_pt x p ρ hx, coeff_map, coeff_map]
  refine pt_res x _ _ ?_
  have e := (AlgebraTools.Det.mapApi B.u.D (Alg.res c.O B.B : B.B →+* ResidueField c.O)).1 (MonoidAlgebra.single (p g) 1)
  rw [B.u.red, MonoidAlgebra.mapRingHom_single, map_one, hP] at e
  have := congrArg (·.coeff k) e
  simp only [coeff_map] at this
  exact this.symm

theorem diag_pt (hn : 1 ≤ n) (hs : Formalism.MainNotions.N.IsSSRep ρ) (t : Fin n → F.G₀ →* c.Oˣ) (ht : r.IsTeich t) (u : F.St) (I : Subgroup Γ)
    (hI : ∀ g ∈ I, p g ∈ F.Iu u) : ∃ P : GL (Fin n) (Qbar l), ∀ g : I,
      ((P * ρ g * P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
        Matrix.diagonal fun i => (W.pushCh (algebraMap c.O (Qbar l)) ((t i).comp (p.comp I.subtype)) g : Qbar l) := by
  obtain ⟨-, hfin, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine diag_of_cong (N := Nat.card (ResidueField c.O) - 1) ?_ _ (fun i g => ?_) (ρ.comp I.subtype) (fun g hg => ?_) fun g k => ?_
  · have h1 : IsUnit ((Nat.card (ResidueField c.O) - 1 : ℕ) : c.O) := by
      rw [← residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_pred Nat.card_pos]
      letI := Fintype.ofFinite (ResidueField c.O)
      simp [Nat.card_eq_fintype_card]
    have := pt_unit x (h1.map (algebraMap c.O B.B)).unit
    rwa [IsUnit.unit_spec, map_natCast, map_natCast] at this
  · rw [MonoidHom.comp_apply, ← map_pow]
    exact (congrArg _ (ht i _).2).trans (map_one _)
  · refine UpperTheory.eq_one_of_trace_translation_invariant_semisimple Γ (Qbar l) n ρ hs g fun h => ?_
    have h1 : p g ∈ r.Ip u := ⟨hI g g.2, Subgroup.mem_iInf.2 fun i => Units.ext (by
      have h2 : (t i (p g) : c.O) = 1 := Subtype.ext (congrArg Units.val (hg i))
      rw [← (ht i _).1, h2, map_one, Units.val_one])⟩
    have h2 := congrArg x (B.u.I u _ h1 (p h))
    have h3 := (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn (MonoidAlgebra.single h 1 * (MonoidAlgebra.single (g : Γ) 1 - 1))
    rw [← hx, W.GDet.tr, W.GDet.lam, chi_comap] at h3
    have h4 := (AlgebraTools.Det.mapApi B.u.D (x : B.B →+* Qbar l)).2.1 1 (MonoidAlgebra.single (p h) 1 * (MonoidAlgebra.single (p g) 1 - 1))
    rw [W.GDet.lam] at h4
    simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapRingHom_single] at h4
    simp only [map_mul, map_sub, map_one] at h3
    simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single] at h3
    have h5 := h3.symm.trans (h4.trans (h2.trans (map_zero x)))
    simp only [W.GDet.repAlg, MonoidAlgebra.lift_single, one_smul] at h5
    rw [mul_sub, mul_one, Matrix.trace_sub, sub_eq_zero, ← map_mul] at h5
    simpa [W.mat] using h5
  · have := chi_cong x p ρ hx g (∏ i, (X - C (t i (p g) : c.O))) (by
      rw [Resid.Dbar, (AlgebraTools.Det.repApi _).2.1, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, (ht _ _).1]
      exact Matrix.charpoly_diagonal _) k
    simp only [Polynomial.map_prod, Polynomial.map_sub, map_X, map_C] at this
    exact this

end Pt

end UpperTheory.V.Hi.Up
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Hi.Up

theorem hecke_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A) :
    (heckePol n q a).map f = heckePol n q fun j => f (a j) :=
  _root_.UpperTheory.Reformulated.B.Qf17.hecke_map f n q a

private theorem hecke_coeff {A : Type} [CommRing A] (n q : ℕ) (a : ℕ → A) (j : ℕ) (hj : j ≤ n) :
    (heckePol n q a).coeff (n - j) = (-1) ^ j * (q : A) ^ (j * (j - 1) / 2) * a j := by
  rw [heckePol, finsetSum_coeff, Finset.sum_eq_single j]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro i hi hij
    rw [coeff_C_mul_X_pow, if_neg]
    have := Finset.mem_range.1 hi
    omega
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

theorem hecke_cong {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (f : O →+* Qbar l) (ι : Qbar l ≃+* ℂ) {n q : ℕ}
    (hq : ‖(q : Qbar l)‖ = 1) (P : (Qbar l)[X]) (a : ℕ → ℂ) (b : ℕ → O) (hP : P.map ι.toRingHom = heckePol n q a)
    (h : ∀ k, ‖P.coeff k - ((heckePol n q b).map f).coeff k‖ < 1) (j : ℕ) (hj : j ≤ n) : ‖ι.symm (a j) - f (b j)‖ < 1 := by
  have e : P = heckePol n q fun j => ι.symm (a j) := by
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    rw [hP, hecke_map]
    simp
  have := h (n - j)
  rw [e, hecke_map, hecke_coeff _ _ _ _ hj, hecke_coeff _ _ _ _ hj, ← mul_sub] at this
  simpa [hq] using this

section Loc

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {w : Plc F} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}

private theorem ord_val (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (ha : IsLocalArtin h a) {lam : Wt F l n} {i : Fin n}
    {ω : (w.adicCompletion F)ˣ →* ℂˣ} {ψ : Dec (F := F) A →* (Qbar l)ˣ} (ho : OrdChar ι a ω (htW lam i) ψ) (s : Weil h) :
    (ψ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) * (cycBar F Ω l s : Qbar l) ^ (i : ℕ) =
      (algPow w (lowW lam i) (a s : w.adicCompletion F))⁻¹ * (ι.symm (ω (a s)) * (((normV w : ℕ) : Qbar l) ^ deg s) ^ (i : ℕ)) := by
  have h1 : (ψ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) = _ := ho.val s _ rfl (Set.mem_univ _)
  have h2 : algPow w (-htW lam i) (a s : w.adicCompletion F) * algPow w (fun _ => 1) (a s : w.adicCompletion F) ^ (i : ℕ) =
      (algPow w (lowW lam i) (a s : w.adicCompletion F))⁻¹ := by
    haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
    haveI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
    unfold algPow
    simp only [finprod_eq_prod_of_fintype]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [zpow_one, ← zpow_natCast, ← zpow_add₀ ((map_ne_zero j.1).2 (a s).ne_zero), ← zpow_neg]
    simp [htW]
  rw [h1, UpperTheory.V.Loc.epsArt hN.aut.art h hw a ha s, ← h2]
  ring

theorem ord_uniq {hh : (F →+* Qbar l) → ℤ} {ω : (w.adicCompletion F)ˣ →* ℂˣ} {ψ ψ' : Dec (F := F) A →* (Qbar l)ˣ}
    (ho : OrdChar ι a ω hh ψ) (ho' : OrdChar ι a ω hh ψ') : ψ = ψ' := by
  have hd : DenseRange (Subgroup.inclusion (Weil_le_Dec h)) := UpperTheory.weil_group_dense_in_galois_group F Ω _ _ h
  refine MonoidHom.ext (congrFun (Continuous.ext_on hd ho.cont ho'.cont ?_))
  rintro _ ⟨s, rfl⟩
  exact Units.ext ((ho.val s _ rfl (Set.mem_univ _)).trans (ho'.val s _ rfl (Set.mem_univ _)).symm)

end Loc

section Set

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} {Q : QData V} {c : Coef l} {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r}
  {Λ : LamObj r} (R : HD Q ι Λ) (x : B.Pt) {lam : Wt L l n}

theorem under_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext z
  exact ((s.hw v) (algebraMap _ _ z)).symm.trans ((s.hA v) z)

theorem fin_part (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hA : (hset Q R.τ₀).Ax) (v : V.frame.Vl) (i : Fin n)
    {ω : ((s.w v.1).adicCompletion L)ˣ →* ℂˣ} (ho : OrdChar ι (artOf (s.hw v.1)) ω (htW lam i) (x.psi v i))
    (u : Uo ((s.w v.1).adicCompletion L)) :
    (ω u : ℂ) * ι ((hset Q R.τ₀).finPart R.θ (x.comp (Λ.toPair B.u)).toRingHom lam v i u) = 1 := by
  have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := hA.art_spec v
  obtain ⟨t, ht⟩ := ha.surj u
  have hd : deg t = 0 := by
    have := ha.ord_eq t
    rw [ht, ord_eq_zero u.2] at this
    omega
  have h1 := congrArg (fun z : Λ.Λˣ => x (Λ.toPair B.u z))
    (R.theta v i t (Subgroup.inclusion (Weil_le_Dec _) t) (deg_eq_zero_iff.1 hd) u rfl ht)
  have h2 := ord_val (w := s.w v.1) hN (hA.Sl_over v) ha ho t
  have h3 := congrArg (fun z : B.Bˣ => x z) (DFunLike.congr_fun (W.LamObj.toPair_spec r Λ B.u v i)
    ⟨Subgroup.inclusion (Weil_le_Dec _) t, deg_eq_zero_iff.1 hd⟩)
  have h4 : x (Λ.toPair B.u ((hset Q R.τ₀).epsV Λ.Λ v (Subgroup.inclusion (Weil_le_Dec _) t) : Λ.Λˣ)) = cycBar L Ω l t :=
    (x.comp (Λ.toPair B.u)).commutes _
  simp only [Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h1
  erw [h4] at h1
  rw [hd, ht, zpow_zero, one_pow, mul_one] at h2
  have h5 := (congrArg (· * _) (h2.symm.trans (congrArg (· * _) h3.symm))).trans h1
  rw [← ι.apply_symm_apply (ω u : ℂ), ← map_mul, ← map_one ι, ← h5]
  congr 1
  change _ * (x (Λ.toPair B.u _) / algPow (s.w v.1) _ _) = _
  rw [div_eq_inv_mul]
  ring

theorem unif_val (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hA : (hset Q R.τ₀).Ax) (v : V.frame.Vl)
    {ω : Fin n → ((s.w v.1).adicCompletion L)ˣ →* ℂˣ} (ho : ∀ i, OrdChar ι (artOf (s.hw v.1)) (ω i) (htW lam i) (x.psi v i))
    (j : Fin n) : ‖ι.symm (((hset Q R.τ₀).lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1))‖ = 1 ∧
      ‖ι.symm (((hset Q R.τ₀).lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)) - algebraMap c.O (Qbar l) (R.a (.inr (v, j)))‖ < 1 := by
  have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := hA.art_spec v
  obtain ⟨t, ht⟩ := ha.surj (unif _)
  have hd : deg t = -1 := by
    have := ha.ord_eq t
    rw [ht, ord_eq_one GlAx.unif_spec] at this
    omega
  let g : Dec (F := L) (s.A v.1) := Subgroup.inclusion (Weil_le_Dec _) t
  let b : B.Bˣ := ∏ i with i ≤ j, B.u.ψ v i g * (hset Q R.τ₀).epsV B.B v g ^ (i : ℕ)
  have h1 : ι.symm (((hset Q R.τ₀).lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)) = x b := by
    have h4 : x ((hset Q R.τ₀).epsV B.B v g : B.Bˣ) = cycBar L Ω l t := x.commutes _
    have e : (Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1) = Finset.univ.filter fun i : Fin n => i ≤ j :=
      Finset.filter_congr fun i _ => Nat.lt_succ_iff
    simp only [b, HSet.lowVal, psEig, e, Units.coe_prod, map_prod, map_mul, map_inv₀, Units.val_mul, Units.val_pow_eq_pow_val,
      map_pow, h4, RingEquiv.symm_apply_apply, map_natCast]
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h2 := ord_val (w := s.w v.1) hN (hA.Sl_over v) ha (ho i) t
    rw [hd, ht, ← resCard_eq_normV, zpow_neg_one, inv_pow] at h2
    exact h2.symm
  rw [h1]
  refine ⟨pt_unit x b, pt_res x _ _ ?_⟩
  rw [← R.res.unif v j t g rfl ht]
  have h4 : Alg.res c.O B.B ((hset Q R.τ₀).epsV B.B v g : B.Bˣ) = ((hset Q R.τ₀).epsV (ResidueField c.O) v g : (ResidueField c.O)ˣ) :=
    (Alg.res c.O B.B).commutes _
  simp only [b, Units.coe_prod, map_prod, map_mul, Units.val_mul, Units.val_pow_eq_pow_val, map_pow, h4]
  exact Finset.prod_congr rfl fun i _ => congrArg (· * _) ((B.u.psi v i).red g)

end Set

end UpperTheory.V.Hi.Up
