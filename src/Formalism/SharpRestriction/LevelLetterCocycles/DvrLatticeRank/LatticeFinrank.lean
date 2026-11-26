module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DescentValuation
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfD

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.SpanLeRange
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LVSmulA
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.OthDisj
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrMultVOfNotJump
set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

theorem tele (f : ℤ → ℤ) (m : ℤ) (d : ℕ) :
    ∑ a ∈ Finset.Ico m (m + d), (f a - f (a + 1)) = f m - f (m + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hI : Finset.Ico m (m + ((d + 1 : ℕ) : ℤ)) = insert (m + d) (Finset.Ico m (m + d)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      push_cast
      omega
    rw [hI, Finset.sum_insert (by simp), ih]
    push_cast
    ring

section Fil

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem fr_filV_succ (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨t, rfl⟩
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul v b =>
    exact LinearMap.mem_range.2 ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, by simp⟩
  | add s t hs ht =>
    rw [map_add (f := _)]
    exact add_mem hs ht

theorem fr_filV_anti : Antitone (fun a : ℤ => FilV PD (LL := LL) (V := V) a) := antitone_int_of_succ_le fun a => fr_filV_succ PD a

theorem fr_filV_exh (x : V ⊗[Qp] BdR) : ∃ a : ℤ, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, LinearMap.mem_range.2 ⟨v ⊗ₜ ⟨b, ha⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    exact ⟨min a a', add_mem (fr_filV_anti PD (min_le_left a a') ha)
      (fr_filV_anti PD (min_le_right a a') ha')⟩

theorem fr_filV_fd (U : Submodule LL (V ⊗[Qp] BdR)) [FiniteDimensional LL ↥U] :
    ∃ a : ℤ, U ≤ FilV PD (LL := LL) (V := V) a := by
  classical
  have hfin : ∀ s : Finset (V ⊗[Qp] BdR), ∃ a : ℤ, ∀ x ∈ s, x ∈ FilV PD (LL := LL) (V := V) a := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert y s hy ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := fr_filV_exh PD (LL := LL) y
      refine ⟨min a b, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact fr_filV_anti PD (min_le_right a b) hb
      · exact fr_filV_anti PD (min_le_left a b) (ha x hx)
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional U).2 inferInstance
  obtain ⟨a, ha⟩ := hfin s
  exact ⟨a, hs ▸ Submodule.span_le.2 fun x hx => ha x hx⟩

theorem fr_filV_sep (x : V ⊗[Qp] BdR) (hx : ∀ a, x ∈ FilV PD (LL := LL) (V := V) a) : x = 0 := by
  classical
  let bV := Module.Basis.ofVectorSpace Qp V
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV
  have hmem : ∀ a (y : V ⊗[Qp] BdR), y ∈ FilV PD (LL := LL) (V := V) a → ∀ i, e y i ∈ PD.Fil a := by
    intro a y hy i
    obtain ⟨t, rfl⟩ := LinearMap.mem_range.1 hy
    clear hy
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.coe_subtype, e,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, Finsupp.mapRange_apply]
      exact Submodule.smul_of_tower_mem _ _ b.2
    | add s t hs ht =>
      rw [map_add (f := _), map_add (f := _), Finsupp.add_apply]
      exact add_mem hs ht
  have hz : e x = 0 := by
    ext i
    exact PD.Fil_sep _ fun a => hmem a x (hx a) i
  exact e.injective (hz.trans (map_zero e).symm)

variable (ρ : Representation LL G V)

theorem fr_fildR_anti (τ : K →ₐ[Qp] LL) : Antitone (FildR PD ρ τ) := fun a b hab => inf_le_inf_left _ (fr_filV_anti PD hab)

theorem fr_fildR_lo (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ lo : ℤ, ∀ a ≤ lo, FildR PD ρ τ a = DdRE PD ρ τ := by
  obtain ⟨lo, hlo⟩ := fr_filV_fd PD (LL := LL) (V := V) (DdRE PD ρ τ)
  refine ⟨lo, fun a ha => ?_⟩
  unfold FildR
  exact inf_eq_left.2 (hlo.trans (fr_filV_anti PD ha))

theorem fr_fildR_hi (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ hi : ℤ, ∀ a, hi ≤ a → FildR PD ρ τ a = ⊥ := by
  classical
  have hfd : ∀ a, FiniteDimensional LL ↥(FildR PD ρ τ a) := fun a =>
    Submodule.finiteDimensional_of_le inf_le_left
  have hex : ∃ n : ℕ, ∃ a : ℤ, finrank LL ↥(FildR PD ρ τ a) = n := ⟨_, 0, rfl⟩
  obtain ⟨a0, ha0⟩ := Nat.find_spec hex
  have hmin : ∀ a, finrank LL ↥(FildR PD ρ τ a0) ≤ finrank LL ↥(FildR PD ρ τ a) := by
    intro a
    rw [ha0]
    exact Nat.find_min' hex ⟨a, rfl⟩
  haveI := hfd a0
  have hstab : ∀ a, a0 ≤ a → FildR PD ρ τ a = FildR PD ρ τ a0 := fun a ha =>
    Submodule.eq_of_le_of_finrank_le (fr_fildR_anti PD ρ τ ha) (hmin a)
  have hbot : FildR PD ρ τ a0 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply fr_filV_sep PD (LL := LL) x
    intro b
    rcases le_total a0 b with h | h
    · rw [← hstab b h] at hx
      exact hx.2
    · exact fr_filV_anti PD h hx.2
  exact ⟨a0, fun a ha => by rw [hstab a ha, hbot]⟩

theorem fr_multV_of_not_jump (τ : K →ₐ[Qp] LL) (a : ℤ) (h : ¬ IsJumpV PD ρ τ a) :
    multV PD ρ τ a = 0 := by
  unfold IsJumpV at h
  unfold multV
  rw [not_not.1 h, sub_self]

theorem fr_sum_multV (τ : K →ₐ[Qp] LL) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, multV PD ρ τ a =
      (finrank LL ↥(FildR PD ρ τ m) : ℤ) - finrank LL ↥(FildR PD ρ τ k) := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = m + d := ⟨(k - m).toNat, by omega⟩
  exact tele (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) m d

end Fil

end Formalism.MainNotions.N.Ln34.UniversalFiltration
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FinrankMapMkQ
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Module

variable {LL X : Type*} [Field LL] [AddCommGroup X] [Module LL X]

theorem finrank_map_mkQ (Oth S : Submodule LL X) (h : Disjoint S Oth) :
    finrank LL ↥(S.map Oth.mkQ) = finrank LL ↥S := by
  have hinj : Function.Injective (Oth.mkQ ∘ₗ S.subtype) := by
    intro x y hxy
    have hxy' : Oth.mkQ (x : X) = Oth.mkQ (y : X) := hxy
    simp only [Submodule.mkQ_apply] at hxy'
    rw [Submodule.Quotient.eq] at hxy'
    have h0 : (x : X) - y = 0 := (Submodule.disjoint_def.mp h) _ (sub_mem x.2 y.2) hxy'
    exact Subtype.ext (sub_eq_zero.mp h0)
  have hr : LinearMap.range (Oth.mkQ ∘ₗ S.subtype) = S.map Oth.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  calc finrank LL ↥(S.map Oth.mkQ)
        = finrank LL ↥(LinearMap.range (Oth.mkQ ∘ₗ S.subtype)) := by rw [hr]
    _ = finrank LL ↥S := ((LinearEquiv.ofInjective _ hinj).finrank_eq).symm

theorem match_fil (I D Oth : Submodule LL X) [FiniteDimensional LL ↥I] [FiniteDimensional LL ↥D]
    (hDO : Disjoint D Oth) (hdim : finrank LL ↥I = finrank LL ↥D) (hDI : D ≤ I ⊔ Oth) :
    Disjoint I Oth ∧ ∀ F : Submodule LL X, F ≤ D → finrank LL ↥(I ⊓ (F ⊔ Oth)) = finrank LL ↥F := by
  have hsupmap : ∀ P : Submodule LL X, (P ⊔ Oth).map Oth.mkQ = P.map Oth.mkQ := by
    intro P
    first
      | rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
      | simp [Submodule.map_sup]
  have hmap : D.map Oth.mkQ ≤ I.map Oth.mkQ := by
    calc D.map Oth.mkQ ≤ (I ⊔ Oth).map Oth.mkQ := Submodule.map_mono hDI
      _ = I.map Oth.mkQ := hsupmap I
  haveI hfin : FiniteDimensional LL ↥(I.map Oth.mkQ) := by
    first
      | infer_instance
      | exact Module.Finite.map I Oth.mkQ
  have hDmap : finrank LL ↥(D.map Oth.mkQ) = finrank LL ↥D :=
    finrank_map_mkQ Oth D hDO
  have hIle : finrank LL ↥(I.map Oth.mkQ) ≤ finrank LL ↥I := by
    first
      | exact Submodule.finrank_map_le _ _
      | apply Submodule.finrank_map_le
  have hle2 : finrank LL ↥(D.map Oth.mkQ) ≤ finrank LL ↥(I.map Oth.mkQ) := by
    first
      | exact Submodule.finrank_le_finrank_of_le hmap
      | exact LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hmap)
  have hIeq : finrank LL ↥(I.map Oth.mkQ) = finrank LL ↥I := by omega
  have hrI : LinearMap.range (Oth.mkQ ∘ₗ I.subtype) = I.map Oth.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hrn := LinearMap.finrank_range_add_finrank_ker (Oth.mkQ ∘ₗ I.subtype)
  have hr' : finrank LL ↥(LinearMap.range (Oth.mkQ ∘ₗ I.subtype)) = finrank LL ↥I := by
    rw [hrI]; exact hIeq
  have hk : finrank LL ↥(LinearMap.ker (Oth.mkQ ∘ₗ I.subtype)) = 0 := by omega
  have hkb : LinearMap.ker (Oth.mkQ ∘ₗ I.subtype) = ⊥ := by
    first
      | exact Submodule.finrank_eq_zero.mp hk
      | exact (Submodule.finrank_eq_zero (S := LinearMap.ker (Oth.mkQ ∘ₗ I.subtype))).mp hk
      | (haveI := Module.finrank_zero_iff.mp hk; exact Submodule.eq_bot_of_subsingleton)
  have hinj : Function.Injective (Oth.mkQ ∘ₗ I.subtype) := LinearMap.ker_eq_bot.mp hkb
  have hdisj : Disjoint I Oth := by
    rw [Submodule.disjoint_def]
    intro x hxI hxO
    have h1 : (Oth.mkQ ∘ₗ I.subtype) ⟨x, hxI⟩ = (Oth.mkQ ∘ₗ I.subtype) 0 := by
      rw [map_zero]
      show Oth.mkQ x = 0
      first
        | (rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hxO)
        | simp [hxO]
    have h2 := hinj h1
    first
      | exact congrArg Subtype.val h2
      | simpa using congrArg Subtype.val h2
  refine ⟨hdisj, fun F hF => ?_⟩
  have hFO : Disjoint F Oth := hDO.mono_left hF
  have hJO : Disjoint (I ⊓ (F ⊔ Oth)) Oth := hdisj.mono_left inf_le_left
  have heq : (I ⊓ (F ⊔ Oth)).map Oth.mkQ = F.map Oth.mkQ := by
    apply le_antisymm
    · calc (I ⊓ (F ⊔ Oth)).map Oth.mkQ ≤ (F ⊔ Oth).map Oth.mkQ := Submodule.map_mono inf_le_right
        _ = F.map Oth.mkQ := hsupmap F
    · intro y hy
      obtain ⟨f, hfF, rfl⟩ := Submodule.mem_map.mp hy
      have hfD : Oth.mkQ f ∈ I.map Oth.mkQ := hmap (Submodule.mem_map.mpr ⟨f, hF hfF, rfl⟩)
      obtain ⟨i, hiI, hif⟩ := Submodule.mem_map.mp hfD
      have hsub : i - f ∈ Oth := by
        simp only [Submodule.mkQ_apply] at hif
        exact (Submodule.Quotient.eq Oth).mp hif
      have h3 : f + (i - f) ∈ F ⊔ Oth := Submodule.add_mem_sup hfF hsub
      have hi : i ∈ F ⊔ Oth := by
        first
          | simpa using h3
          | (rw [add_sub_cancel] at h3; exact h3)
      exact Submodule.mem_map.mpr ⟨i, Submodule.mem_inf.mpr ⟨hiI, hi⟩, hif⟩
  calc finrank LL ↥(I ⊓ (F ⊔ Oth))
        = finrank LL ↥((I ⊓ (F ⊔ Oth)).map Oth.mkQ) :=
          (finrank_map_mkQ Oth _ hJO).symm
    _ = finrank LL ↥(F.map Oth.mkQ) := by rw [heq]
    _ = finrank LL ↥F := finrank_map_mkQ Oth F hFO

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34
open scoped TensorProduct

section DiscreteGroups

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem oth_disj [CharZero Qp] [FiniteDimensional Qp K] (τ : K →ₐ[Qp] LL) :
    Disjoint (DdRE PD ρ τ) (⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD ρ τ') := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element Qp K
  have hint : IsIntegral Qp α := IsIntegral.of_finite Qp α
  have hadj : Algebra.adjoin Qp {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hα,
      IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective (fun τ : K →ₐ[Qp] LL => τ α) := by
    intro τ₁ τ₂ h
    have hle := AlgHom.adjoin_le_equalizer τ₁ τ₂ (s := {α}) (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h)
    rw [hadj] at hle
    exact AlgHom.ext fun y => hle (Algebra.mem_top (x := y))
  set f : Module.End LL (V ⊗[Qp] BdR) := mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) α
  have hE : ∀ τ' : K →ₐ[Qp] LL, DdRE PD ρ τ' ≤ f.eigenspace (τ' α) := by
    intro τ' x hx
    rw [Module.End.mem_eigenspace_iff]
    have h := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hx).2 α
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at h
    exact h
  have hind := Module.End.eigenspaces_iSupIndep f (τ α)
  refine Disjoint.mono (hE τ) ?_ hind
  refine iSup₂_le fun τ' hτ' => ?_
  exact le_trans (hE τ') (le_iSup₂_of_le (τ' α) (fun h => hτ' (hinj h)) le_rfl)

end DiscreteGroups

section Pt

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem dR_le (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {ζ : LL} {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    [FiniteDimensional LL ↥(DdRE PD T.ρ τ)] :
    DdRE PD T.ρ τ ≤ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' := by
  obtain ⟨hi, hhi⟩ := fr_fildR_hi PD T.ρ τ
  obtain ⟨lo, hlo⟩ := fr_fildR_lo PD T.ρ τ
  have key : ∀ d : ℕ, FildR PD T.ρ τ (hi - d) ≤
      Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' := by
    intro d
    induction d with
    | zero =>
      rw [Nat.cast_zero, sub_zero, hhi hi le_rfl]
      exact bot_le
    | succ d ih =>
      intro w hw
      have e1 : -(-(hi - ((d + 1 : ℕ) : ℤ))) = hi - ((d + 1 : ℕ) : ℤ) := neg_neg _
      obtain ⟨x, a, -, -, hx⟩ := (hp4.2 c ζ τ hPt).2.2 (-(hi - ((d + 1 : ℕ) : ℤ))) w (by rwa [e1])
      have e2 : -(-(hi - ((d + 1 : ℕ) : ℤ))) + 1 = hi - (d : ℤ) := by push_cast; ring
      rw [e2] at hx
      have hmem1 : a • W.levN T c ζ ((letE c : LetA O n) • x) (-(hi - ((d + 1 : ℕ) : ℤ))) ∈
          Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' :=
        Submodule.mem_sup_left (Submodule.smul_mem _ _
          (Submodule.mem_inf.1 ((hp4.2 c ζ τ hPt).2.1 x (-(hi - ((d + 1 : ℕ) : ℤ))))).1)
      have hF : Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (hi - (d : ℤ)) ≤
          Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ' := by
        unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
        exact sup_le ih le_sup_right
      have := Submodule.sub_mem _ hmem1 (hF hx)
      rwa [sub_sub_cancel] at this
  have h := key (hi - lo).toNat
  rwa [hlo _ (by omega)] at h

end Pt

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.ModelFPf
open scoped TensorProduct

section Span

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL)

def LV (K : ℕ) (x : W.DD T) : T.V ⊗[Qp] BdR :=
  open Classical in
  if h : W.Q ^ K • W.φD T x ∈ W.N T then W.levN T c ζ ⟨_, h⟩ K else 0

theorem LV_eq (K : ℕ) (x : W.DD T) (h : W.Q ^ K • W.φD T x ∈ W.N T) :
    LV W T c ζ K x = W.levN T c ζ ⟨_, h⟩ K := by
  unfold LV
  rw [dite_eq_left h]

theorem LV_add (K : ℕ) (x y : W.DD T) (hx : W.Q ^ K • W.φD T x ∈ W.N T)
    (hy : W.Q ^ K • W.φD T y ∈ W.N T) : LV W T c ζ K (x + y) = LV W T c ζ K x + LV W T c ζ K y := by
  have hxy : W.Q ^ K • W.φD T (x + y) ∈ W.N T := by
    rw [map_add (f := _), smul_add]
    exact Submodule.add_mem _ hx hy
  rw [LV_eq W T c ζ K _ hxy, LV_eq W T c ζ K _ hx, LV_eq W T c ζ K _ hy]
  rw [show (⟨_, hxy⟩ : ↥(W.N T)) = ⟨_, hx⟩ + ⟨_, hy⟩ from
    Subtype.ext (by simp only [map_add (f := _), smul_add, Submodule.coe_add]), map_add (f := _)]
  rfl

theorem LV_smulA (K : ℕ) (a : LetA O n) (x : W.DD T) (hx : W.Q ^ K • W.φD T x ∈ W.N T)
    (hv : ∀ j : ℤ, j < K → W.levN T c ζ ⟨_, hx⟩ j = 0) :
    W.Q ^ K • W.φD T (a • x) ∈ W.N T ∧
      LV W T c ζ K (a • x) = PowerSeries.constantCoeff (W.lev c ζ (W.φA a)) • LV W T c ζ K x := by
  have e : W.Q ^ K • W.φD T (a • x) = W.φA a • (W.Q ^ K • W.φD T x) := by
    rw [Formalism.MainNotions.LiftingTheory.wmap_φD_smul, smul_comm]
  have hax : W.Q ^ K • W.φD T (a • x) ∈ W.N T := e ▸ Submodule.smul_mem _ _ hx
  refine ⟨hax, ?_⟩
  rw [LV_eq W T c ζ K _ hax, LV_eq W T c ζ K _ hx]
  have hs : (⟨_, hax⟩ : ↥(W.N T)) = W.φA a • (⟨_, hx⟩ : ↥(W.N T)) := Subtype.ext e
  rw [hs, levN_eq_serMul, serMul_eq_sum _ _ K hv K 1 (by omega), Finset.sum_range_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

theorem LV_smulO (K : ℕ) (o : O) (x : W.DD T) (hx : W.Q ^ K • W.φD T x ∈ W.N T) :
    W.Q ^ K • W.φD T (o • x) ∈ W.N T ∧
      LV W T c ζ K (o • x) = algebraMap O LL o • LV W T c ζ K x := by
  have e : W.Q ^ K • W.φD T (o • x) = algebraMap O (LetA O n) o • (W.Q ^ K • W.φD T x) := by
    rw [map_smul, smul_comm, algebraMap_smul]
  have hox : W.Q ^ K • W.φD T (o • x) ∈ W.N T := e ▸ Submodule.smul_mem _ _ hx
  refine ⟨hox, ?_⟩
  rw [LV_eq W T c ζ K _ hox, LV_eq W T c ζ K _ hx]
  have hs : (⟨_, hox⟩ : ↥(W.N T)) = algebraMap O (LetA O n) o • (⟨_, hx⟩ : ↥(W.N T)) := Subtype.ext e
  have hC : algebraMap O (PowerSeries LL) o = PowerSeries.C (algebraMap O LL o) := by
    rw [IsScalarTower.algebraMap_apply O LL (PowerSeries LL)]
    rfl
  rw [hs, levN_eq_serMul, AlgHom.commutes, hC]
  unfold serMul
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [PowerSeries.coeff_C, if_neg hj, zero_smul]

variable {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem levN_val (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (hc0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hc1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : W.DD T) (hxN : x ∈ W.N T) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) :
    W.levN T c ζ ⟨_, hk⟩ k = PowerSeries.coeff 1 (W.lev c ζ W.Q) ^ k • valAt W T c ζ x := by
  classical
  have hex : ∃ k, W.Q ^ k • W.φD T x ∈ W.N T := ⟨k, hk⟩
  unfold valAt
  rw [dite_eq_left hex]
  have hk0 : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hk0m := Nat.find_spec hex
  have hv : ∀ j : ℤ, j < (Nat.find hex : ℤ) → W.levN T c ζ ⟨_, hk0m⟩ j = 0 :=
    fun j hj => ((hp4.2 c ζ τ hPt).1.1 ⟨x, hxN⟩ _ hk0m j).2 hj
  have hs : (⟨_, hk⟩ : ↥(W.N T)) = W.Q ^ (k - Nat.find hex) • (⟨_, hk0m⟩ : ↥(W.N T)) :=
    Subtype.ext (by
      show W.Q ^ k • W.φD T x = W.Q ^ (k - Nat.find hex) • W.Q ^ Nat.find hex • W.φD T x
      rw [smul_smul, ← pow_add, Nat.sub_add_cancel hk0])
  obtain ⟨B', hB'⟩ := PowerSeries.X_dvd_iff.2 hc0
  have hB0 : PowerSeries.constantCoeff B' = PowerSeries.coeff 1 (W.lev c ζ W.Q) := by
    rw [hB', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [hs, levN_eq_serMul, serMul_eq_sum _ _ _ hv k (k - Nat.find hex + 1) (by omega),
    Finset.sum_eq_single (k - Nat.find hex)]
  · have e1 : (k : ℤ) - ((k - Nat.find hex : ℕ) : ℤ) = (Nat.find hex : ℤ) := by
      rw [Nat.cast_sub hk0]
      ring
    have hcoef : PowerSeries.coeff (k - Nat.find hex) ((W.lev c ζ W.Q) ^ (k - Nat.find hex)) =
        PowerSeries.coeff 1 (W.lev c ζ W.Q) ^ (k - Nat.find hex) := by
      rw [hB', mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [e1, map_pow, hcoef, smul_smul, ← pow_sub₀ _ hc1 hk0]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [map_pow, pow_vanish' _ hc0 _ j h, zero_smul]
    · rw [hv _ (by omega), smul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

end Span

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.N.Ln34.ModelFPf
open scoped TensorProduct

section Span2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL)

theorem N_φ' (x : W.DD T) (hx : x ∈ W.N T) : ∃ k : ℕ, W.Q ^ k • W.φD T x ∈ W.N T :=
  W.N_φ T x hx

theorem Qpow_mono {x : W.DD T} {k K : ℕ} (hk : W.Q ^ k • W.φD T x ∈ W.N T) (hK : k ≤ K) :
    W.Q ^ K • W.φD T x ∈ W.N T := by
  rw [show K = (K - k) + k by omega, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ hk

theorem LV_zero (K : ℕ) : LV W T c ζ K 0 = 0 := by
  have h0 : W.Q ^ K • W.φD T 0 ∈ W.N T := by rw [map_zero, smul_zero]; exact Submodule.zero_mem _
  rw [LV_eq W T c ζ K _ h0]
  rw [show (⟨_, h0⟩ : ↥(W.N T)) = 0 from Subtype.ext (by simp), map_zero]
  rfl

theorem LV_sum {ι : Type} (K : ℕ) (s : Finset ι) (f : ι → W.DD T)
    (hf : ∀ i, W.Q ^ K • W.φD T (f i) ∈ W.N T) :
    W.Q ^ K • W.φD T (∑ i ∈ s, f i) ∈ W.N T ∧
      LV W T c ζ K (∑ i ∈ s, f i) = ∑ i ∈ s, LV W T c ζ K (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by rw [Finset.sum_empty, map_zero, smul_zero]; exact Submodule.zero_mem _, ?_⟩
    rw [Finset.sum_empty, Finset.sum_empty, LV_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨by rw [map_add (f := _), smul_add]; exact Submodule.add_mem _ (hf a) ih.1, ?_⟩
    rw [LV_add W T c ζ K _ _ (hf a) ih.1, ih.2]

theorem letE_idem (d : ZMod n) : (letE d : LetA O n) * letE d = letE d := by
  funext i
  simp only [Pi.mul_apply, letE, Pi.single_apply]
  split_ifs <;> simp

variable {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop}

theorem span_le_range (hp4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T) {τ : K →ₐ[Qp] LL} (hPt : Pt c ζ τ)
    (hc0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hc1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (π' : LetA O n) (hφπ : PowerSeries.constantCoeff (W.lev c ζ (W.φA π')) = 0)
    {r0 : ℕ} (b : Fin r0 → W.DD T) (hbΔ : ∀ j, b j ∈ W.NΔ T)
    (hbu : ∀ x ∈ W.N T, ∃! a : Fin r0 → LetA O n, x = ∑ j, a j • b j)
    {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (rep : Fin r → W.DD T)
    (hrep : ∀ k, rep k ∈ NcS W T (c - 1)) (hbrep : ∀ k, bL k = mkL W T π' c (rep k) (hrep k)) :
    Formalism.MainNotions.DeltaInvariantLattices.ιDi W T c ≤ LinearMap.range (UniversalLiftFrames.Phi W T c ζ rep) := by
  classical
  set R := LinearMap.range (UniversalLiftFrames.Phi W T c ζ rep)
  set c1 := PowerSeries.coeff 1 (W.lev c ζ W.Q)
  have hvan : ∀ (x : W.DD T) (hx : x ∈ W.N T) (K : ℕ) (hK : W.Q ^ K • W.φD T x ∈ W.N T) (j : ℤ),
      j < K → W.levN T c ζ ⟨_, hK⟩ j = 0 :=
    fun x hx K hK j hj => ((hp4.2 c ζ τ hPt).1.1 ⟨x, hx⟩ K hK j).2 hj
  have hLV : ∀ (x : W.DD T) (hx : x ∈ W.N T) (K : ℕ) (hK : W.Q ^ K • W.φD T x ∈ W.N T),
      LV W T c ζ K x = c1 ^ K • valAt W T c ζ x := by
    intro x hx K hK
    rw [LV_eq W T c ζ K _ hK, levN_val W T c ζ hp4 hPt hc0 hc1 x hx K hK]
  have hcancel : ∀ (K : ℕ) (u : T.V ⊗[Qp] BdR), c1 ^ K • u ∈ R → u ∈ R := by
    intro K u hu
    have := Submodule.smul_mem R ((c1 ^ K)⁻¹) hu
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hc1), one_smul] at this
  have hrepR : ∀ k, valAt W T c ζ (rep k) ∈ R := by
    intro k
    refine ⟨Pi.single k 1, ?_⟩
    rw [UniversalLiftFrames.Phi_apply]
    simp [Pi.single_apply]

  have hA : ∀ y (hy : y ∈ NcS W T (c - 1)), valAt W T c ζ y ∈ R := by
    intro y hy
    set p := (PiNS W T π' 1).comap (NcS W T (c - 1)).subtype
    set o := bL.repr (mkL W T π' c y hy)
    have h2 : (∑ k, o k • bL k) = p.mkQ (∑ k, o k • (⟨rep k, hrep k⟩ : ↥(NcS W T (c - 1)))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hbrep]
      rfl
    have h3 : (Submodule.Quotient.mk (⟨y, hy⟩ : ↥(NcS W T (c - 1))) : LcQ W T π' c) =
        Submodule.Quotient.mk (∑ k, o k • (⟨rep k, hrep k⟩ : ↥(NcS W T (c - 1)))) := by
      have := bL.sum_repr (mkL W T π' c y hy)
      rw [h2] at this
      exact this.symm
    have h4 := (Submodule.Quotient.eq p).1 h3
    rw [Submodule.mem_comap] at h4
    have hz : y - ∑ k, o k • rep k ∈ PiNS W T π' 1 := by simpa using h4
    obtain ⟨⟨y', hy'N, hy'⟩, -⟩ := (mem_PiNS W T π' 1 _).1 hz
    have hyeq : y = ∑ k, o k • rep k + π' • y' := by
      rw [pow_one] at hy'
      rw [hy']
      abel
    have hyN := ((mem_NcS W T _ y).1 hy).1
    have hrN : ∀ k, rep k ∈ W.N T := fun k => ((mem_NcS W T _ _).1 (hrep k)).1
    choose Kr hKr using fun k => N_φ' W T (rep k) (hrN k)
    obtain ⟨Ky, hKy⟩ := N_φ' W T y hyN
    obtain ⟨Kz, hKz⟩ := N_φ' W T y' hy'N
    set K := Ky + ∑ k, Kr k + Kz
    have hKk : ∀ k, W.Q ^ K • W.φD T (rep k) ∈ W.N T := fun k =>
      Qpow_mono W T (hKr k) (by
        have := Finset.single_le_sum (f := Kr) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        omega)
    have hKo : ∀ k, W.Q ^ K • W.φD T (o k • rep k) ∈ W.N T :=
      fun k => (LV_smulO W T c ζ K (o k) (rep k) (hKk k)).1
    have hKz' : W.Q ^ K • W.φD T y' ∈ W.N T := Qpow_mono W T hKz (by omega)
    have hKy' : W.Q ^ K • W.φD T y ∈ W.N T := Qpow_mono W T hKy (by omega)
    obtain ⟨hKπ, hLπ⟩ := LV_smulA W T c ζ K π' y' hKz' (hvan y' hy'N K hKz')
    obtain ⟨hKs, hLs⟩ := LV_sum W T c ζ K Finset.univ (fun k => o k • rep k) hKo
    apply hcancel K
    rw [← hLV y hyN K hKy']
    have e : LV W T c ζ K y = LV W T c ζ K (∑ k, o k • rep k + π' • y') := by rw [← hyeq]
    rw [e, LV_add W T c ζ K _ _ hKs hKπ, hLs, hLπ, hφπ, zero_smul, add_zero]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [(LV_smulO W T c ζ K (o k) (rep k) (hKk k)).2, hLV _ (hrN k) K (hKk k), smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hrepR k))

  rw [← (hp4.2 c ζ τ hPt).1.2]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, k, hk, rfl⟩
  set d : ZMod n := c - 1
  have hx'N : (letE d : LetA O n) • (x : W.DD T) ∈ W.N T := Submodule.smul_mem _ _ x.2
  have ek : (letE c : LetA O n) • (W.Q ^ k • W.φD T x) = W.Q ^ k • W.φD T ((letE d : LetA O n) • (x : W.DD T)) := by
    rw [show d = c - 1 from rfl, φD_letE, smul_comm]
  have hk' : W.Q ^ k • W.φD T ((letE d : LetA O n) • (x : W.DD T)) ∈ W.N T := ek ▸ Submodule.smul_mem _ _ hk
  have hw : W.levN T c ζ ⟨_, hk⟩ k = W.levN T c ζ ⟨_, hk'⟩ k := by
    rw [← levN_letE W T c ζ ⟨_, hk⟩ k]
    rw [show (letE c : LetA O n) • (⟨_, hk⟩ : ↥(W.N T)) = ⟨_, hk'⟩ from
      Subtype.ext (by rw [Submodule.coe_smul]; exact ek)]
  rw [SetLike.mem_coe, hw, levN_val W T c ζ hp4 hPt hc0 hc1 _ hx'N k hk']
  refine Submodule.smul_mem _ _ ?_
  set x' := (letE d : LetA O n) • (x : W.DD T)
  obtain ⟨a, hax, -⟩ := hbu x' hx'N
  have hx'eq : x' = ∑ j, a j • ((letE d : LetA O n) • b j) := by
    have h1 : x' = (letE d : LetA O n) • x' := by
      show _ = (letE d : LetA O n) • ((letE d : LetA O n) • (x : W.DD T))
      rw [smul_smul, letE_idem]
    rw [h1, hax, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
  have hebN : ∀ j, (letE d : LetA O n) • b j ∈ NcS W T (c - 1) := by
    intro j
    refine (mem_NcS W T _ _).2 ⟨Submodule.smul_mem _ _ (hbΔ j).1, fun δ hδ => ?_, ?_⟩
    · rw [γD_letE, (hbΔ j).2 δ hδ]
    · rw [smul_smul, letE_idem]
  have hebN' : ∀ j, (letE d : LetA O n) • b j ∈ W.N T := fun j => ((mem_NcS W T _ _).1 (hebN j)).1
  choose Kb hKb using fun j => N_φ' W T _ (hebN' j)
  set K := k + ∑ j, Kb j
  have hKb' : ∀ j, W.Q ^ K • W.φD T ((letE d : LetA O n) • b j) ∈ W.N T := fun j =>
    Qpow_mono W T (hKb j) (by
      have := Finset.single_le_sum (f := Kb) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega)
  have hKa : ∀ j, W.Q ^ K • W.φD T (a j • ((letE d : LetA O n) • b j)) ∈ W.N T :=
    fun j => (LV_smulA W T c ζ K (a j) _ (hKb' j) (hvan _ (hebN' j) K (hKb' j))).1
  have hKx : W.Q ^ K • W.φD T x' ∈ W.N T := Qpow_mono W T hk' (by omega)
  apply hcancel K
  rw [← hLV x' hx'N K hKx]
  have e : LV W T c ζ K x' = LV W T c ζ K (∑ j, a j • ((letE d : LetA O n) • b j)) := by
    rw [← hx'eq]
  rw [e, (LV_sum W T c ζ K Finset.univ _ hKa).2]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [(LV_smulA W T c ζ K (a j) _ (hKb' j) (hvan _ (hebN' j) K (hKb' j))).2,
    hLV _ (hebN' j) K (hKb' j)]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hA _ (hebN j)))

end Span2

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
end

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem lattice_finrank {O LL V : Type*} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) [Module.Free O T] [Module.Finite O T]
    (hspan : Submodule.span LL (T : Set V) = ⊤) : finrank O T = finrank LL V := by
  classical
  set bT := Module.Free.chooseBasis O T
  set v : Module.Free.ChooseBasisIndex O T → V := fun i => (bT i : V)
  have hli : LinearIndependent O v := bT.linearIndependent.map' T.subtype T.ker_subtype
  have hliLL : LinearIndependent LL v := (LinearIndependent.iff_fractionRing O LL).1 hli
  have hsp : Submodule.span LL (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.2 fun x hx => ?_
    have e : x = ∑ i, bT.repr ⟨x, hx⟩ i • v i := by
      conv_lhs => rw [show x = ((⟨x, hx⟩ : T) : V) from rfl, ← bT.sum_repr ⟨x, hx⟩]
      rw [Submodule.coe_sum]
      rfl
    rw [SetLike.mem_coe, e]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [Module.finrank_eq_card_chooseBasisIndex, ← finrank_top LL V, ← hsp, finrank_span_eq_card hliLL]

set_option maxHeartbeats 1000000 in
theorem r_eq (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (r : ℕ)
    (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) : r = finrank ↥LL.1 T.V := by
  classical
  have : IsFractionRing ↥(OL LL) ↥LL.1 := GenPf.isFractionRing LL
  set W := (HW l).W K 1 LL hG
  have hs : W.s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨-, ⟨-, -, -, ⟨r0, b, hbΔ, hbu, hbe⟩, -⟩, -⟩ :=
    (hA l K 1 LL hG).2.2.2.2.2.2.2.2.1 T hT hs (by rw [hp]; exact hl)
  obtain ⟨-, huniq, ⟨w₁, hw₁⟩, -⟩ := hp9
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  obtain ⟨bL0⟩ := MQ.basis_L W T π' (sK l K) hsK w₁ hw₁ huniq b hbΔ hbu hbe c
  have h1 : r = r0 := by
    have e1 := Module.finrank_eq_card_basis bL
    have e2 := Module.finrank_eq_card_basis bL0
    simp only [Fintype.card_fin] at e1 e2
    omega

  have hli : LinearIndependent (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (fun j => (⟨b j, (hbΔ j).1⟩ : W.N T)) := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have h1 : (∑ j, g j • b j) = 0 := by
      have := congrArg Subtype.val hg
      simpa using this
    obtain ⟨a0, _, hu⟩ := hbu 0 (W.N T).zero_mem
    have e1 := hu g h1.symm
    have e2 := hu 0 (by simp)
    intro i
    rw [e1, ← e2]
    rfl
  have hsp : ⊤ ≤ Submodule.span (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
      (Set.range fun j => (⟨b j, (hbΔ j).1⟩ : W.N T)) := by
    rintro ⟨x, hx⟩ _
    obtain ⟨a, ha, _⟩ := hbu x hx
    have : (⟨x, hx⟩ : W.N T) = ∑ j, a j • (⟨b j, (hbΔ j).1⟩ : W.N T) := by
      apply Subtype.ext
      simp [ha]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let bN := Module.Basis.mk hli hsp
  let bD := IsBaseChange.basis bN (W.N_base T hT)
  have : Nontrivial W.EE := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' : algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) W.EE 0 =
        algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) W.EE 1 := by rw [map_zero, map_one]; exact h
    have h0 := congrFun (W.EE_inj h') 0
    exact zero_ne_one h0
  have h2 : r0 = finrank W.EE (W.DD T) := by
    rw [Module.finrank_eq_card_basis bD, Fintype.card_fin]
  have h3 := (W.DD_free T).2
  have : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  rw [h1, h2, h3]
  exact lattice_finrank T.L.T T.L.span

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
