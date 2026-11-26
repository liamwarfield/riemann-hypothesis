module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdelicExtensionOfAlgebraicWeightDefiniteUn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglandsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.SerSys.SuppTame

section Chain

open GlobalTheory.LocGL

theorem isIrreducible_of_isIrrRep {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : IsIrrRep ρ) : ρ.IsIrreducible := by
  obtain ⟨hn, hW⟩ := h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => hv ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← e] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  · rcases hW S.toSubmodule (fun x w hw => S.apply_mem_toSubmodule x hw) with h0 | h1
    · exact Or.inl (Subrepresentation.ext (by rw [h0]; rfl))
    · exact Or.inr (Subrepresentation.ext (by rw [h1]; rfl))

theorem isIrrRep_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : IsIrrRep ρ := by
  haveI := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)
    exact bot_ne_top this
  · rcases eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

theorem hasSupport_zero (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) {g : ℕ} [Fact g.Prime] {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin 0) ℚ_[g]) V) (hs : GlobalTheory.PRep.IsSmooth π)
    (hi : π.IsIrreducible) : HasSupport π (0 : Multiset (IrrGL (k := ℚ_[g]))) := by
  obtain ⟨s, hs'⟩ := SupportRing.exists_hasSupport hZ (IrrGL.of π hs hi)
  have h1 : HasSupport π s := hs'.of_equiv (IrrGL.equivOf π hs hi).symm
  have h2 := h1.sum_fst
  rw [Fintype.card_fin] at h2
  have h3 : s = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hne
    have h4 := (h1.isCusp hy).1
    have h5 : y.1 ≤ (s.map Sigma.fst).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hy)
    omega
  rwa [h3] at h1

theorem chain : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (g : ℕ) [Fact g.Prime] (π : Supp.GLRep g), IsIrrRep π.2.ρ → GlobalTheory.PRep.IsSmooth π.2.ρ → ∃ (L : List (Supp.GLRep g)) (y : List (GlobalTheory.LocGL.IrrGL (k := ℚ_[g]))), Supp.InInd π L ∧ (∀ ρ ∈ L, 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ GlobalTheory.PRep.IsSmooth ρ.2.ρ ∧ ρ.2.ρ.IsIrreducible ∧ GlobalTheory.SmGL.IsCuspidal ρ.2.ρ) ∧ GlobalTheory.LocGL.HasSupport π.2.ρ (y : Multiset (GlobalTheory.LocGL.IrrGL (k := ℚ_[g]))) ∧ List.Forall₂ (fun (ρ : Supp.GLRep g) (x : GlobalTheory.LocGL.IrrGL (k := ℚ_[g])) => ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (GlobalTheory.LocGL.IrrGL.of ρ.2.ρ hs hi).Inert x) L y := by
  intro hZ g _
  have H : ∀ (N : ℕ) (π : Supp.GLRep g), π.1 = N → IsIrrRep π.2.ρ → GlobalTheory.PRep.IsSmooth π.2.ρ →
      ∃ (L : List (Supp.GLRep g)) (y : List (IrrGL (k := ℚ_[g]))), Supp.InInd π L ∧
        (∀ ρ ∈ L, 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ GlobalTheory.PRep.IsSmooth ρ.2.ρ ∧ ρ.2.ρ.IsIrreducible ∧
          GlobalTheory.SmGL.IsCuspidal ρ.2.ρ) ∧ HasSupport π.2.ρ (y : Multiset (IrrGL (k := ℚ_[g]))) ∧
        List.Forall₂ (fun (ρ : Supp.GLRep g) (x : IrrGL (k := ℚ_[g])) =>
          ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (IrrGL.of ρ.2.ρ hs hi).Inert x) L y := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro π hN hπ hs
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · subst h0
        refine ⟨[], [], Supp.InInd.nil π hN hπ, by simp, ?_, List.Forall₂.nil⟩
        obtain ⟨n, π⟩ := π
        simp only at hN
        subst hN
        exact hasSupport_zero hZ _ hs (isIrreducible_of_isIrrRep hπ)
      · obtain ⟨a, b, hab, W, W', _, _, _, _, σ, ρ, hb, hσs, hσi, hρs, hρi, hρc, φ, hφ⟩ :=
          GlobalTheory.JacFactor.exists_map_jac₂ ℚ_[g] π.1 _ π.2.ρ hs (isIrreducible_of_isIrrRep hπ) (hN ▸ hpos)
        have hM : Supp.MapsToProd π.2.ρ σ ρ := GlobalTheory.GLp.Supp.mapsToProd_of_jac₂ g a b π.1 hab _ _ _ π.2.ρ σ ρ φ hφ
        let σ' : Supp.GLRep g := ⟨a, Rep.of σ⟩
        let ρ' : Supp.GLRep g := ⟨b, Rep.of ρ⟩
        obtain ⟨Lσ, yσ, hI, hL, hS, hF⟩ :=
          ih a (by omega) σ' rfl (isIrrRep_of_isIrreducible hσi) hσs
        have hρsupp : HasSupport ρ {IrrGL.of ρ hρs hρi} :=
          (hasSupport_self (IrrGL.isCusp_of.2 ⟨hb, hρc⟩)).of_equiv (IrrGL.equivOf ρ hρs hρi).symm
        obtain ⟨μ₁, μ₂, h₁, h₂, hsupp⟩ := GlobalTheory.IndChain.SuppStep.supp_of_mapsToProd hZ g _ _ _ _ _ _ π.2.ρ σ ρ hs (isIrreducible_of_isIrrRep hπ) hM
          yσ {IrrGL.of ρ hρs hρi} hS hρsupp
        refine ⟨ρ' :: Lσ, (IrrGL.of ρ hρs hρi).tw μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₂) ::
          yσ.map (fun x => x.tw μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₁)), ?_, ?_, ?_, ?_⟩
        · exact Supp.InInd.cons π σ' ρ' Lσ hπ (isIrrRep_of_isIrreducible hρi) hI hM
        · exact List.forall_mem_cons.2 ⟨⟨hb, isIrrRep_of_isIrreducible hρi, hρs, hρi, hρc⟩, hL⟩
        · convert hsupp using 1
          rw [← Multiset.cons_coe, ← Multiset.map_coe, Multiset.map_singleton, add_comm, Multiset.singleton_add]
        · refine List.Forall₂.cons ⟨hρs, hρi, μ₂, h₂, rfl⟩ ?_
          refine List.forall₂_map_right_iff.2 (hF.imp fun ρ x ⟨hs, hi, hin⟩ => ⟨hs, hi, ?_⟩)
          exact IrrGL.inert_equivalence.trans hin ⟨μ₁, h₁, rfl⟩
  intro π hπ hs
  exact H _ π rfl hπ hs

end Chain

end GlobalTheory.SerSys.SuppTame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.SplitAdelic

open TensorProduct GlobalTheory.InertUmax GlobalTheory.SplitLift

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem exists_imag (L : Type) [Field L] [NumberField L] [IsCMField L] :
    ∃ δ : L, IsCMField.complexConj L δ = -δ ∧ δ ≠ 0 := by
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  refine ⟨y - IsCMField.complexConj L y, ?_, sub_ne_zero.2 (Ne.symm hy)⟩
  rw [map_sub, IsCMField.complexConj_apply_apply]; ring

theorem linIndep_one_imag (δ : L) (hδ : IsCMField.complexConj L δ = -δ) (hδ0 : δ ≠ 0) :
    LinearIndependent L⁺ ![(1 : L), δ] := by
  rw [LinearIndependent.pair_iff]
  intro a t h
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
  have h2 := congrArg (IsCMField.complexConj L) h
  rw [map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hδ, map_zero] at h2
  have ht : algebraMap L⁺ L t * δ = 0 := by linear_combination (h - h2) / 2
  have ht' : algebraMap L⁺ L t = 0 := (mul_eq_zero.mp ht).resolve_right hδ0
  have hs : algebraMap L⁺ L a = 0 := by linear_combination (h + h2) / 2
  exact ⟨(algebraMap L⁺ L).injective (hs.trans (map_zero _).symm),
    (algebraMap L⁺ L).injective (ht'.trans (map_zero _).symm)⟩

theorem compAt_eq_zero_of_proj (s : SplitPlace L) (a : AL L) (h1 : s.proj a = 0)
    (h2 : s.proj (conjAL L a) = 0) : compAt L s.v a = 0 := by
  obtain ⟨δ, hδ, hδ0⟩ := exists_imag L
  let b : Module.Basis (Fin 2) L⁺ L := basisOfLinearIndependentOfCardEqFinrank
    (linIndep_one_imag δ hδ hδ0)
    (by rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = δ := by simp [b]
  obtain ⟨A, B, hAB⟩ := tensor_decomp b a
  rw [hb0, hb1] at hAB
  subst hAB
  rw [map_add (f := _), proj_tmul, proj_tmul, map_one, one_mul] at h1
  rw [map_add (f := _), conjAL_tmul, conjAL_tmul, map_one, hδ, map_add (f := _), proj_tmul, proj_tmul, map_one, one_mul,
    map_neg] at h2
  have hr : s.i δ ≠ 0 := (_root_.map_ne_zero _).2 hδ0
  have hA2 : 2 * A s.v = 0 := by linear_combination h1 + h2
  have hA : A s.v = 0 := (mul_eq_zero.mp hA2).resolve_left (two_ne s)
  have hB2 : 2 * (s.i δ * B s.v) = 0 := by linear_combination h1 - h2
  have hB : s.i δ * B s.v = 0 := (mul_eq_zero.mp hB2).resolve_left (two_ne s)
  have hB' : B s.v = 0 := (mul_eq_zero.mp hB).resolve_left hr
  rw [map_add (f := _), compAt_tmul, compAt_tmul, hA, hB', tmul_zero, tmul_zero, add_zero]

theorem loc_apply (s : SplitPlace L) {n : ℕ} (x : GAf L n) (i j : Fin n) :
    ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) _) i j =
      s.proj (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j) := rfl

theorem conj_entry {n : ℕ} (x : GAf L n) (i j : Fin n) :
    conjAL L (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
  have hm := x.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  have h1 : (((x : GL (Fin n) (AL L))⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) (x : GL (Fin n) (AL L)) :=
    Units.inv_eq_of_mul_eq_one_right hm
  rw [InvMemClass.coe_inv, h1]
  simp [conjT]

theorem compAt_entries_eq (s : SplitPlace L) {n : ℕ} (x g : GAf L n) (h : s.loc n x = s.loc n g)
    (i j : Fin n) :
    compAt L s.v (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j) =
      compAt L s.v (((g : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j) := by
  rw [← sub_eq_zero, ← map_sub]
  apply compAt_eq_zero_of_proj
  · rw [map_sub, sub_eq_zero, ← loc_apply, ← loc_apply, h]
  · have hinv : s.loc n x⁻¹ = s.loc n g⁻¹ := by rw [map_inv, map_inv, h]
    rw [map_sub, map_sub, sub_eq_zero, conj_entry, conj_entry, ← loc_apply, ← loc_apply, hinv]

theorem mat_ext {n : ℕ} (M N : Matrix (Fin n) (Fin n) (AL L))
    (h : ∀ w, M.map (compAt L w) = N.map (compAt L w)) : M = N := by
  ext i j
  rw [← sub_eq_zero]
  apply eq_zero_of_compAt
  intro w
  rw [map_sub, sub_eq_zero]
  exact congrFun (congrFun (h w) i) j

theorem ext_of_loc (s : SplitPlace L) {n : ℕ} (x y : GAf L n) (hx : TrivOutside {s.v} x)
    (hy : TrivOutside {s.v} y) (h : s.loc n x = s.loc n y) : x = y := by
  apply Subtype.ext; apply Units.ext
  apply mat_ext
  intro w
  obtain rfl | hw := eq_or_ne w s.v
  · ext i j
    exact compAt_entries_eq s x y h i j
  · rw [hx w hw, hy w hw]

theorem mul_coe {n : ℕ} (x y : GAf L n) :
    (((x * y : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
        ((y : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) := rfl

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L),
    (∀ g : GAf L n, ∃ x y : GAf L n, TrivOutside {s.v} x ∧ TrivOutside {s.v}ᶜ y ∧ g = x * y) ∧
    (∀ x y : GAf L n, TrivOutside {s.v} x → TrivOutside {s.v}ᶜ y → Commute x y) ∧
    (∀ A : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      ∃! x : GAf L n, TrivOutside {s.v} x ∧ s.loc n x = A) := by
  intro L _ _ _ n s
  refine ⟨fun g => ?_, fun x y hx hy => ?_, fun A => ?_⟩
  · obtain ⟨x, hx, hxg⟩ := exists_trivOutside_loc_eq n s (s.loc n g)
    refine ⟨x, x⁻¹ * g, hx, ?_, (mul_inv_cancel_left x g).symm⟩
    intro w hw
    have hw' : w = s.v := by simpa using hw
    subst hw'
    rw [mul_coe, Matrix.map_mul]
    have hg : (((g : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L s.v) =
        (((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L s.v) := by
      ext i j
      exact (compAt_entries_eq s x g hxg i j).symm
    rw [hg, ← Matrix.map_mul, ← mul_coe, inv_mul_cancel]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · show x * y = y * x
    apply Subtype.ext; apply Units.ext
    change (((x * y : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      (((y * x : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))
    apply mat_ext
    intro w
    rw [mul_coe, mul_coe, Matrix.map_mul, Matrix.map_mul]
    obtain rfl | hw := eq_or_ne w s.v
    · rw [hy _ (by simp), mul_one, one_mul]
    · rw [hx w hw, mul_one, one_mul]
  · obtain ⟨x, hx, hxA⟩ := exists_trivOutside_loc_eq n s A
    exact ⟨x, ⟨hx, hxA⟩, fun y ⟨hy, hyA⟩ => ext_of_loc s y x hy hx (hyA.trans hxA.symm)⟩

end GlobalTheory.SplitAdelic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L), (∀ g : GAf L n, ∃ x y : GAf L n, TrivOutside {s.v} x ∧ TrivOutside {s.v}ᶜ y ∧ g = x * y) ∧ (∀ x y : GAf L n, TrivOutside {s.v} x → TrivOutside {s.v}ᶜ y → Commute x y) ∧ (∀ A : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)), ∃! x : GAf L n, TrivOutside {s.v} x ∧ s.loc n x = A) := by
  first | exact @GlobalTheory.SplitAdelic.main | exact GlobalTheory.SplitAdelic.main | (intros; apply GlobalTheory.SplitAdelic.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2PairOfAdmissible
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.PointRepAboveL

theorem place_unique {D : D7} {i : D.nd.Loc} {τ : D.host.E →+* Qbar (D.nd.l i)} {w w' : PlE D.host}
    (h : InducesW D.nd i τ w) (h' : InducesW D.nd i τ w') : w' = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [← h x, h' x]

end GlobalTheory.PointRepAboveL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.SplitHeckeComm

theorem gelfand {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Subgroup G)
    (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ J, ∃ k₂ ∈ J, τ g = k₁ * g * k₂) (hJ : ∀ k ∈ J, τ k ∈ J) (α β : G) (R S : Finset G)
    (hR : ∀ γ ∈ R, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α * k₂)
    (hR' : ∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J)
    (hS : ∀ γ ∈ S, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * β * k₂)
    (hS' : ∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * β * k₂) → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ J)
    (x : W) (hx : ∀ k ∈ J, ρ k x = x) :
    ∑ γ ∈ R, ρ γ (∑ δ ∈ S, ρ δ x) = ∑ δ ∈ S, ρ δ (∑ γ ∈ R, ρ γ x) := by
  classical
  let f : G ⧸ J → W := fun c => ρ c.out x
  have hf : ∀ g : G, f (g : G ⧸ J) = ρ g x := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul J g
    simp only [f, hk, map_mul, Module.End.mul_apply, hx k k.2]
  have key : ∀ A B : Finset G, ∑ γ ∈ A, ρ γ (∑ δ ∈ B, ρ δ x)
      = ∑ p ∈ A ×ˢ B, f ((p.1 * p.2 : G) : G ⧸ J) := fun A B => by
    rw [Finset.sum_product]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hf, map_sum, map_mul, Module.End.mul_apply]
  rw [key, key]
  let T : Finset (G ⧸ J) := (R ×ˢ S).image (fun p => ((p.1 * p.2 : G) : G ⧸ J)) ∪
    (S ×ˢ R).image (fun p => ((p.1 * p.2 : G) : G ⧸ J))
  rw [← Finset.sum_fiberwise_of_maps_to' (s := R ×ˢ S) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ J))
      (fun p hp => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)) f,
    ← Finset.sum_fiberwise_of_maps_to' (s := S ×ˢ R) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ J))
      (fun p hp => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)) f]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, Finset.sum_const]
  congr 1
  apply le_antisymm
  · convert GelfandTrick.card_pairs_le J τ hmul hinv hdc hJ α β R S hR hR' hS hS' c
  · convert GelfandTrick.card_pairs_le J τ hmul hinv hdc hJ β α S R hS hS' hR hR' c

theorem gelfand_sub {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (H U : Subgroup G)
    (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a) (hH : ∀ k ∈ H, τ k ∈ H)
    (hU : ∀ k ∈ U, τ k ∈ U)
    (hdc : ∀ g ∈ H, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ τ g = k₁ * g * k₂) (α β : G) (R S : Finset G)
    (hα : α ∈ H) (hβ : β ∈ H)
    (hR' : ∀ x : G, (∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ U)
    (hR : ∀ γ ∈ R, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ γ = k₁ * α * k₂)
    (hS' : ∀ x : G, (∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ x = k₁ * β * k₂) → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ U)
    (hS : ∀ γ ∈ S, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ γ = k₁ * β * k₂)
    (x : W) (hx : ∀ k ∈ U, k ∈ H → ρ k x = x) :
    ∑ γ ∈ R, ρ γ (∑ δ ∈ S, ρ δ x) = ∑ δ ∈ S, ρ δ (∑ γ ∈ R, ρ γ x) := by
  classical
  have hmem : ∀ (a : G) (A : Finset G), a ∈ H →
      (∀ γ ∈ A, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ γ = k₁ * a * k₂) → ∀ γ ∈ A, γ ∈ H := by
    intro a A ha h γ hγ
    obtain ⟨k₁, -, k₂, -, h₁, h₂, rfl⟩ := h γ hγ
    exact H.mul_mem (H.mul_mem h₁ ha) h₂
  have hsum : ∀ A : Finset G, (∀ γ ∈ A, γ ∈ H) → ∀ y : W,
      ∑ γ ∈ A, ρ γ y = ∑ γ ∈ A.subtype (· ∈ H), ρ (γ : G) y := fun A hA y =>
    (Finset.sum_subtype_of_mem (fun γ => ρ γ y) hA).symm
  have h1 : ∀ (a : G) (ha : a ∈ H) (A : Finset G),
      (∀ γ ∈ A, ∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ γ = k₁ * a * k₂) →
      ∀ γ ∈ (A.subtype (· ∈ H) : Finset H), ∃ k₁ ∈ U.subgroupOf H, ∃ k₂ ∈ U.subgroupOf H, γ = k₁ * ⟨a, ha⟩ * k₂ := by
    intro a ha A h γ hγ
    obtain ⟨k₁, u₁, k₂, u₂, h₁, h₂, e⟩ := h γ (Finset.mem_subtype.1 hγ)
    exact ⟨⟨k₁, h₁⟩, u₁, ⟨k₂, h₂⟩, u₂, Subtype.ext e⟩
  have h2 : ∀ (a : G) (ha : a ∈ H) (A : Finset G), (∀ γ ∈ A, γ ∈ H) →
      (∀ x : G, (∃ k₁ ∈ U, ∃ k₂ ∈ U, k₁ ∈ H ∧ k₂ ∈ H ∧ x = k₁ * a * k₂) → ∃! γ, γ ∈ A ∧ γ⁻¹ * x ∈ U) →
      ∀ x : H, (∃ k₁ ∈ U.subgroupOf H, ∃ k₂ ∈ U.subgroupOf H, x = k₁ * ⟨a, ha⟩ * k₂) →
        ∃! γ, γ ∈ (A.subtype (· ∈ H) : Finset H) ∧ γ⁻¹ * x ∈ U.subgroupOf H := by
    rintro a ha A hA h x ⟨k₁, u₁, k₂, u₂, e⟩
    obtain ⟨γ, ⟨hγ, hu⟩, huniq⟩ := h x ⟨k₁, u₁, k₂, u₂, k₁.2, k₂.2, congrArg Subtype.val e⟩
    refine ⟨⟨γ, hA γ hγ⟩, ⟨Finset.mem_subtype.2 hγ, hu⟩, fun δ hδ => Subtype.ext ?_⟩
    exact huniq δ ⟨Finset.mem_subtype.1 hδ.1, hδ.2⟩
  have hRH := hmem α R hα hR
  have hSH := hmem β S hβ hS
  rw [hsum R hRH, hsum S hSH x, hsum S hSH, hsum R hRH x]
  refine gelfand (ρ.comp H.subtype) (U.subgroupOf H) (fun g => ⟨τ g, hH g g.2⟩)
    (fun a b => Subtype.ext (hmul a b)) (fun a => Subtype.ext (hinv a)) (fun g => ?_) (fun k hk => hU k hk)
    ⟨α, hα⟩ ⟨β, hβ⟩ _ _ (h1 α hα R hR) (h2 α hα R hRH hR') (h1 β hβ S hS) (h2 β hβ S hSH hS') x
    (fun k hk => hx k hk k.2)
  obtain ⟨k₁, u₁, k₂, u₂, h₁, h₂, e⟩ := hdc g g.2
  exact ⟨⟨k₁, h₁⟩, u₁, ⟨k₂, h₂⟩, u₂, Subtype.ext e⟩

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => NumberField.maximalRealSubfield L

def trivSub (n : ℕ) (T : Set (HeightOneSpectrum (𝓞 L⁺))) : Subgroup (GAf L n) where
  carrier := {x | TrivOutside T x}
  mul_mem' := by
    intro x y hx hy w hw
    show ((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1
    rw [Units.val_mul, Matrix.map_mul, hx w hw, hy w hw, mul_one]
  one_mem' := by
    intro w _
    show ((1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) = 1
    rw [Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  inv_mem' := by
    intro x hx w hw
    have h1 : (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
        (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
      rfl
    have h2 := congrArg (fun M => M.map (compAt L w)) h1
    simp only [Matrix.map_mul, hx w hw, mul_one] at h2
    rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

def tr (x : GAf L n) : GAf L n :=
  ⟨Formalism.UG.P.heckecomm_tr x.1, by
    have hm : (x.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) x.1 = 1 := x.2
    have h := congrArg Matrix.transpose (mul_eq_one_comm.mp hm)
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h
    exact h⟩

theorem loc_tr (s : SplitPlace L) (x : GAf L n) : s.loc n (tr x) = Formalism.UG.P.heckecomm_tr (s.loc n x) :=
  Units.ext rfl

theorem mem_Umax_of_loc (s : SplitPlace L) (x : GAf L n) (hx : TrivOutside {s.v} x)
    (h : s.loc n x ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov L⁺ s.v)) : x ∈ Umax L n := by
  have hint : ∀ a ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov L⁺ s.v), ∀ i j,
      Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1 := by
    rintro _ ⟨g, rfl⟩ i j
    exact ((g : Matrix (Fin n) (Fin n) (Formalism.UG.Ov L⁺ s.v)) i j).2
  have h1 := hint _ h
  have h2 := hint _ (inv_mem h)
  rw [← map_inv] at h2
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  intro i j
  have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    have hm : (x.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) x.1 = 1 := x.2
    have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
  have hz : (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    apply GlobalTheory.mem_ALint_of_supported_at_split L s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := rfl
      rw [map_sub, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h1 i j) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i := rfl
      rw [map_sub, map_sub, hconj, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h2 j i) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have := add_mem hz (show (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
  simpa using this

theorem tr_mem_trivSub (T : Set (HeightOneSpectrum (𝓞 L⁺))) (x : GAf L n) (hx : x ∈ trivSub n T) :
    tr x ∈ trivSub n T := by
  intro w hw
  have h := congrArg Matrix.transpose (hx w hw)
  rw [Matrix.transpose_one] at h
  exact h

theorem tr_doubleCoset (s : SplitPlace L) (g : GAf L n) (hg : g ∈ trivSub n {s.v}) :
    ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, k₁ ∈ trivSub n {s.v} ∧ k₂ ∈ trivSub n {s.v} ∧ tr g = k₁ * g * k₂ := by
  obtain ⟨a, b, e⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp L⁺ s.v n (s.loc n g)
  obtain ⟨k, hk, ek⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s a.1
  have hk' : k ∈ trivSub n {s.v} := hk
  have ht : (k * g)⁻¹ * tr g ∈ trivSub n {s.v} := mul_mem (inv_mem (mul_mem hk' hg)) (tr_mem_trivSub _ g hg)
  refine ⟨k, mem_Umax_of_loc s k hk (ek ▸ a.2), (k * g)⁻¹ * tr g, mem_Umax_of_loc s _ ht ?_, hk', ht, by group⟩
  rw [map_mul, map_inv, map_mul, loc_tr, e, ek, inv_mul_cancel_left]
  exact b.2

def rtRep (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ (GAf L n) (GAf L n → W) where
  toFun := NG.rt L n
  map_one' := LinearMap.ext fun f => funext fun g => congrArg f (mul_one g)
  map_mul' x y := LinearMap.ext fun f => funext fun g => congrArg f (mul_assoc g x y).symm

theorem doubleCoset_comm : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L) (α β : GAf L n) (Ra Rb : Finset (GAf L n)), TrivOutside {s.v} α → TrivOutside {s.v} β → (∀ x : GAf L n, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * α * k₂) → ∃! γ, γ ∈ Ra ∧ γ⁻¹ * x ∈ Umax L n) → (∀ γ ∈ Ra, ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ γ = k₁ * α * k₂) → (∀ x : GAf L n, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * β * k₂) → ∃! γ, γ ∈ Rb ∧ γ⁻¹ * x ∈ Umax L n) → (∀ γ ∈ Rb, ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ γ = k₁ * β * k₂) → ∀ f : GAf L n → W, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → ∑ γ ∈ Ra, NG.rt L n γ (∑ δ ∈ Rb, NG.rt L n δ f) = ∑ δ ∈ Rb, NG.rt L n δ (∑ γ ∈ Ra, NG.rt L n γ f) := by
  intro L _ _ _ n W _ _ s α β Ra Rb hα hβ hR' hR hS' hS f hf
  exact gelfand_sub (rtRep L n W) (trivSub n {s.v}) (Umax L n) tr
    (fun a b => Subtype.ext (Formalism.UG.P.heckecomm_tr_mul a.1 b.1)) (fun a => Subtype.ext (Formalism.UG.P.heckecomm_tr_tr a.1))
    (tr_mem_trivSub _) (fun k hk i j => hk j i) (tr_doubleCoset s) α β Ra Rb hα hβ hR' hR hS' hS f hf

end GlobalTheory.SplitHeckeComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSphericalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (s : SplitPlace L) (α β : GAf L n) (Ra Rb : Finset (GAf L n)), TrivOutside {s.v} α → TrivOutside {s.v} β → (∀ x : GAf L n, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * α * k₂) → ∃! γ, γ ∈ Ra ∧ γ⁻¹ * x ∈ Umax L n) → (∀ γ ∈ Ra, ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ γ = k₁ * α * k₂) → (∀ x : GAf L n, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * β * k₂) → ∃! γ, γ ∈ Rb ∧ γ⁻¹ * x ∈ Umax L n) → (∀ γ ∈ Rb, ∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ γ = k₁ * β * k₂) → ∀ f : GAf L n → W, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → ∑ γ ∈ Ra, NG.rt L n γ (∑ δ ∈ Rb, NG.rt L n δ f) = ∑ δ ∈ Rb, NG.rt L n δ (∑ γ ∈ Ra, NG.rt L n γ f) := by
  first | exact @GlobalTheory.SplitHeckeComm.doubleCoset_comm | exact GlobalTheory.SplitHeckeComm.doubleCoset_comm | (intros; apply GlobalTheory.SplitHeckeComm.doubleCoset_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivOutsideLoc
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitSec

theorem exists_trivOutside_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (u : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), ∃ x : GAf L n, TrivOutside {s.v} (x : GA L n) ∧ s.loc n x = u := by
  intro L _ _ _ n s u
  exact GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s u

end GlobalTheory.SplitSec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZero
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FieldTransport

section General
variable {G H : Type} [Group G] [Group H]

def compEquiv {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ H V} {τ : Representation ℂ H W} (φ : ρ.Equiv τ) (f : G →* H) :
    Representation.Equiv (ρ.comp f : Representation ℂ G V) (τ.comp f : Representation ℂ G W) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    have := congrArg (fun L => L v) (φ.toIntertwiningMap.isIntertwining' (f g))
    simpa using this

def compCompEquiv {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (f : H →* G)
    (g : G →* H) (h : ∀ x, f (g x) = x) : Representation.Equiv ((ρ.comp f).comp g : Representation ℂ G V) ρ :=
  .mk (LinearEquiv.refl ℂ V) fun x => LinearMap.ext fun v => by simp [h]

variable [TopologicalSpace G] [TopologicalSpace H]

def pullRep (f : G →* H) (hf : Continuous f) (hs : Function.Surjective f) (σ : IrrRep H) : IrrRep G :=
  ⟨σ.V, σ.ρ.comp f, fun v => (σ.smooth v).preimage hf,
    GlobalTheory.JacFactor.isIrreducible_comp_surj σ.ρ f hs σ.irr⟩

end General

section GLmap
variable {R S : Type} [CommRing R] [CommRing S]

abbrev mapGL (e : R ≃+* S) (n : ℕ) : GL (Fin n) R →* GL (Fin n) S := GeneralLinearGroup.map e.toRingHom

theorem mapGL_symm_mapGL (e : R ≃+* S) (n : ℕ) (g : GL (Fin n) R) : mapGL e.symm n (mapGL e n g) = g := by
  ext a b; simp [mapGL]

theorem mapGL_mapGL_symm (e : R ≃+* S) (n : ℕ) (g : GL (Fin n) S) : mapGL e n (mapGL e.symm n g) = g := by
  ext a b; simp [mapGL]

theorem mapGL_surjective (e : R ≃+* S) (n : ℕ) : Function.Surjective (mapGL e n) :=
  fun g => ⟨_, mapGL_mapGL_symm e n g⟩

theorem continuous_mapGL [TopologicalSpace R] [TopologicalSpace S] (e : R ≃+* S) (he : Continuous e) (n : ℕ) :
    Continuous (mapGL e n) :=
  Units.continuous_map (continuous_id.matrix_map he)

end GLmap
end GlobalTheory.FieldTransport

namespace GlobalTheory.FieldTransport

section Fields
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

def transportFun (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL (k := k)) : IrrGL (k := k') :=
  ⟨x.1, (pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1) (mapGL_surjective i.symm x.1) x.2.rep).cl⟩

theorem transportFun_left (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) (x : IrrGL (k := k)) :
    transportFun i.symm (by simpa using hi) (transportFun i hi' x) = x := by
  refine congrArg (Sigma.mk x.1) ((IrrRep.cl_eq_iff.2 ?_).trans x.2.cl_rep)
  obtain ⟨ψ⟩ := IrrRep.nonempty_equiv_rep
    (pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1) (mapGL_surjective i.symm x.1) x.2.rep)
  exact ⟨(compEquiv ψ (mapGL i.symm.symm x.1)).trans
    (compCompEquiv x.2.rep.ρ (mapGL i.symm x.1) (mapGL i.symm.symm x.1) fun g => mapGL_symm_mapGL i x.1 g)⟩

theorem repRel_iff (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL (k := k)) (x' : IrrGL (k := k')) :
    RepRel i x x' ↔ transportFun i hi' x = x' := by
  constructor
  · rintro ⟨n, π, π', e, rfl, rfl, he⟩
    refine congrArg (Sigma.mk n) (IrrRep.cl_eq_iff.2 ?_)
    obtain ⟨ψ⟩ := IrrRep.nonempty_equiv_rep π
    refine ⟨(compEquiv ψ (mapGL i.symm n)).trans (.mk e fun g => LinearMap.ext fun v => ?_)⟩
    have := he (mapGL i.symm n g) v
    rw [show GeneralLinearGroup.map i.toRingHom (mapGL i.symm n g) = g from mapGL_mapGL_symm i n g] at this
    simpa using this
  · rintro rfl
    refine ⟨x.1, x.2.rep, pullRep (mapGL i.symm x.1) (continuous_mapGL i.symm hi' x.1)
      (mapGL_surjective i.symm x.1) x.2.rep, LinearEquiv.refl ℂ _,
      congrArg (Sigma.mk x.1) x.2.cl_rep.symm, rfl, fun g v => ?_⟩
    show x.2.rep.ρ g v = x.2.rep.ρ (mapGL i.symm x.1 (mapGL i x.1 g)) v
    rw [mapGL_symm_mapGL]

theorem exists_transport (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) :
    ∃ T : IrrGL (k := k) ≃ IrrGL (k := k'), (∀ x x', RepRel i x x' ↔ T x = x') ∧ ∀ x, (T x).1 = x.1 := by
  have hi2 : Continuous i.symm.symm := by simpa using hi
  refine ⟨⟨transportFun i hi', transportFun i.symm hi2, fun x => transportFun_left i hi hi' x, fun y => ?_⟩,
    repRel_iff i hi', fun x => rfl⟩
  have := transportFun_left i.symm hi' hi2 y
  simpa using this

end Fields
end GlobalTheory.FieldTransport


open GlobalTheory.FieldTransport in
theorem GlobalTheory.transport_irrGL_bijective : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∃ T : IrrGL (k := k) ≃ IrrGL (k := k'), (∀ x x', RepRel i x x' ↔ T x = x') ∧ ∀ x, (T x).1 = x.1 := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  exact exists_transport i hi (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi).1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZeroStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportIrrGL_bijective_degree_charZero : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∃ T : IrrGL (k := k) ≃ IrrGL (k := k'), (∀ x x', RepRel i x x' ↔ T x = x') ∧ ∀ x, (T x).1 = x.1 := by
  first | exact @GlobalTheory.transport_irrGL_bijective | exact GlobalTheory.transport_irrGL_bijective | (intros; apply GlobalTheory.transport_irrGL_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsQuotientOfIrreducibleUnitarySegmentPr
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsQuotientOfIrreducibleUnitarySegmentPr
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory

theorem isL_of_irreducible_prod_unitarisable_nu :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V), σ.IsIrreducible →
    ∀ (m : ℕ) (δ : Fin m → IrrGL (k := k)) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
      IsL ↑(List.ofFn fun j => (Δ j).nu (s j)) σ := by
  intro k _ _ _ _ hprec a V _ _ σ hσ m δ Δ s hL hU hs hd ⟨e⟩
  refine ⟨m, fun j => (δ j).nu (s j), hd, ⟨fun j => (Δ j).nu (s j), ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Fin.univ_val_map _
  · intro i j _ h
    have h1 := hprec (δ i) (δ j) (Δ i) (Δ j) (hL i) (hU i) (hL j) (hU j) (s i) (s j) h
    have hi := abs_lt.1 (hs i)
    have hj := abs_lt.1 (hs j)
    linarith
  · intro j
    exact ((hL j).tw _ (isSmoothChar_absPow _)).of_equiv ((δ j).twEquiv _ _)
  · exact (isCosocle_self hσ).of_equiv (.refl _) e

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsQuotientOfIrreducibleUnitarySegmentPrStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLanglandsQuotient_of_irreducible_unitary_segment_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    (∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V), σ.IsIrreducible →
    ∀ (m : ℕ) (δ : Fin m → IrrGL (k := k)) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
      IsL ↑(List.ofFn fun j => (Δ j).nu (s j)) σ := by
  first | exact @GlobalTheory.isL_of_irreducible_prod_unitarisable_nu | exact GlobalTheory.isL_of_irreducible_prod_unitarisable_nu | (intros; apply GlobalTheory.isL_of_irreducible_prod_unitarisable_nu <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProduct
noncomputable section

open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
  GlobalTheory.CuspRep GlobalTheory.DefiniteBC

namespace GlobalTheory.SpehRec

theorem isL_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} {π' : Representation ℂ (GL (Fin N) k) W}
    (h : IsL 𝔪 π) (e : π.Equiv π') : IsL 𝔪 π' := by
  obtain ⟨m, x, hd, hx, hc⟩ := h
  exact ⟨m, x, hd, hx, hc.of_equiv e (.refl _)⟩

section Sum

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem sumList_append (l l' : List (WD h)) : sumList (l ++ l') = (sumList l).lpSum (sumList l') := by
  induction l with
  | nil => simp [sumList, WD.lpSum_comm (WD.lpZero (h := h)), WD.lpSum_zero]
  | cons x l ih =>
    simp only [List.cons_append, sumList, List.foldr_cons] at ih ⊢
    rw [ih, WD.lpSum_assoc]

theorem sumList_flatMap {α : Type*} (L : List α) (f : α → List (WD h)) :
    sumList (L.flatMap f) = sumList (L.map fun i => sumList (f i)) := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.flatMap_cons, sumList_append, ih]
    rfl

end Sum

theorem rec_spehQuot : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h),
    IsRec h rc → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (a d n : ℕ) (hd : ∑ _ : Fin d, a = n) (σ : LocIrr w a) (σ' : LocIrr w n),
      IsUnitarisable σ.ρ → IsGeneric σ.ρ → IsSpehQuot hd σ σ' →
      rc (cls (ParLaws.toRep σ')) =
        sumList ((List.range d).map fun k : ℕ => (rc (cls (ParLaws.toRep σ))).lpTw (((d : ℝ) - 1) / 2 - k)) := by
  intro E Ω _ _ _ _ _ A w
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro h rc hrc hTZ hLM a d n hd σ σ' hu hg hq
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨m, δ, Δ, s, hΔ, hδu, hs, hd0, hφ⟩ := hTZ.exists_prod σ.smooth σ.irred hu hg
  have hA := GlobalTheory.T.isLanglandsQuotient_of_irreducible_unitary_segment_product _ (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) a _ σ.ρ σ.irred m δ Δ s hΔ hδu hs hd0 hφ
  have hB := GlobalTheory.T.langlandsQuotient_of_speh_type_product_isL _ hLM (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) (GlobalTheory.T.parabolicInduction_in_stages_product_of_products _) a _ σ.ρ m δ Δ s hΔ hδu hs hd0 hφ d n hd _ σ'.ρ σ'.irred hq
  have h4 := GlobalTheory.lpSum_segments_nu E Ω A w h rc hrc
  obtain ⟨a', ha', ε, -, L⟩ := hrc
  rw [L.langlands _ _ (isL_of_equiv hB (equivRep (ParLaws.toRep σ'))),
    L.langlands _ _ (isL_of_equiv hA (equivRep (ParLaws.toRep σ))), List.map_flatMap, sumList_flatMap]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact h4 _ _

end GlobalTheory.SpehRec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProductStatement
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_speh_product : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h),
    IsRec h rc → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (a d n : ℕ) (hd : ∑ _ : Fin d, a = n) (σ : LocIrr w a) (σ' : LocIrr w n),
      IsUnitarisable σ.ρ → IsGeneric σ.ρ → IsSpehQuot hd σ σ' →
      rc (cls (ParLaws.toRep σ')) =
        sumList ((List.range d).map fun k : ℕ => (rc (cls (ParLaws.toRep σ))).lpTw (((d : ℝ) - 1) / 2 - k)) := by
  first | exact @GlobalTheory.SpehRec.rec_spehQuot | exact GlobalTheory.SpehRec.rec_spehQuot | (intros; apply GlobalTheory.SpehRec.rec_spehQuot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarMapMulFiniteIdeleOfUniformizerPowers
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarMapMulFiniteIdeleOfUniformizerPowers
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
open scoped Pointwise

namespace GlobalTheory.AdeleScale

variable {E : Type} [Field E] [NumberField E]

theorem qV_ne_zero (v : HeightOneSpectrum (𝓞 E)) : (qV E v : ℝ) ≠ 0 := by
  rw [qV, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

theorem finId_adl_snd (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (v : HeightOneSpectrum (𝓞 E)) :
    ((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).2 v = ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) := by
  change ((1 : Af E) - 1 + ((GlobalTheory.CellDec.adl ϖ m : (Af E)ˣ) : Af E)) v = _
  rw [sub_self, zero_add]
  rfl

theorem finId_fst (a : (Af E)ˣ) : ((finId E a : AdeleRing (𝓞 E) E)).1 = 1 := by
  change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
  rw [sub_zero, add_zero]

theorem ideleModule_finId_adl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ)
    (hϖ : ∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))) (hs : ∀ v, v ∉ s → m v = 0) :
    (GroundTheory.Global.IdeleGroup.ideleModule E (finId E (GlobalTheory.CellDec.adl ϖ m)) : ℝ) =
      ∏ v ∈ s, ((qV E v : ℝ) ^ m v)⁻¹ := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h1 : ∀ w : InfinitePlace E,
      ‖((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).1 w‖ ^ w.mult = 1 := fun w => by
    rw [finId_fst]
    change ‖(1 : w.Completion)‖ ^ w.mult = 1
    rw [norm_one, one_pow]
  have h2 : ∀ v : HeightOneSpectrum (𝓞 E),
      ‖((finId E (GlobalTheory.CellDec.adl ϖ m) : AdeleRing (𝓞 E) E)).2 v‖ = ((qV E v : ℝ) ^ m v)⁻¹ := fun v => by
    have hu : Valued.v ((ϖ v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := hϖ v
    rw [finId_adl_snd, Units.val_zpow_eq_zpow_val, norm_zpow, GroundTheory.Global.norm_uniformizer hu, _root_.inv_zpow]
    rfl
  rw [Finset.prod_eq_one fun w _ => h1 w, one_mul]
  simp_rw [h2]
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hvs
  exact hv (by show ((qV E v : ℝ) ^ m v)⁻¹ = 1; rw [hs v hvs, zpow_zero, inv_one])

end GlobalTheory.AdeleScale


open GlobalTheory.AdeleScale in
theorem GlobalTheory.AdeleScale.map_mul_finId_adl : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))), (∀ v, v ∉ s → m v = 0) →
    ∀ [MeasurableSpace (AdeleRing (𝓞 E) E)] [BorelSpace (AdeleRing (𝓞 E) E)] (μR : Measure (AdeleRing (𝓞 E) E)) [μR.IsAddHaarMeasure],
    Measure.map (fun x : AdeleRing (𝓞 E) E => ((finId E (GlobalTheory.CellDec.adl ϖ m) : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E) * x) μR =
      ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) • μR := by
  intro E _ _ ϖ hϖ m s hs _ _ μR _
  set a : (AdeleRing (𝓞 E) E)ˣ := finId E (GlobalTheory.CellDec.adl ϖ m) with ha
  have hm : Measurable fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x :=
    (continuous_const.mul continuous_id).measurable
  have hchar : distribHaarChar (AdeleRing (𝓞 E) E) a • μR.map (fun x => (a : AdeleRing (𝓞 E) E) * x) = μR := by
    ext S hS
    rw [Measure.smul_apply, Measure.map_apply hm hS]
    have h1 := distribHaarChar_mul μR a ((fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x) ⁻¹' S)
    have e : a • ((fun x : AdeleRing (𝓞 E) E => (a : AdeleRing (𝓞 E) E) * x) ⁻¹' S) = S := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp [Units.smul_def]
    rw [e] at h1
    rw [ENNReal.smul_def, smul_eq_mul]
    exact h1
  have hmod : (distribHaarChar (AdeleRing (𝓞 E) E) a : ℝ) = ∏ v ∈ s, ((qV E v : ℝ) ^ m v)⁻¹ := by
    rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing]
    exact ideleModule_finId_adl ϖ hϖ m s hs
  have hone : ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) * (distribHaarChar (AdeleRing (𝓞 E) E) a : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun v _ =>
      zpow_nonneg (Nat.cast_nonneg _) _), hmod, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun v _ => mul_inv_cancel₀ (zpow_ne_zero _ (qV_ne_zero v)), ENNReal.ofReal_one]
  conv_rhs => rw [← hchar]
  rw [ENNReal.smul_def (distribHaarChar (AdeleRing (𝓞 E) E) a), smul_smul, hone, one_smul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarMapMulFiniteIdeleOfUniformizerPowersStatement
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addHaar_map_mul_finiteIdeleOfUniformizerPowers : ∀ (E : Type) [Field E] [NumberField E] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (m : HeightOneSpectrum (𝓞 E) →₀ ℤ)
    (s : Finset (HeightOneSpectrum (𝓞 E))), (∀ v, v ∉ s → m v = 0) →
    ∀ [MeasurableSpace (AdeleRing (𝓞 E) E)] [BorelSpace (AdeleRing (𝓞 E) E)] (μR : Measure (AdeleRing (𝓞 E) E)) [μR.IsAddHaarMeasure],
    Measure.map (fun x : AdeleRing (𝓞 E) E => ((finId E (GlobalTheory.CellDec.adl ϖ m) : (AdeleRing (𝓞 E) E)ˣ) : AdeleRing (𝓞 E) E) * x) μR =
      ENNReal.ofReal (∏ v ∈ s, (qV E v : ℝ) ^ m v) • μR := by
  first | exact @GlobalTheory.AdeleScale.map_mul_finId_adl | exact GlobalTheory.AdeleScale.map_mul_finId_adl | (intros; apply GlobalTheory.AdeleScale.map_mul_finId_adl <;> assumption)
end
end
