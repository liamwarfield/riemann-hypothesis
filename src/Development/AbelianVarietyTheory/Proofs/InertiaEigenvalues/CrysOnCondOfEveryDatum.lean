module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTheoremModule
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsoluteGaloisMemFixingSubgroupMaxUnramified
noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

section Bases

variable {Z O R M J ι : Type} [CommRing Z] [CommRing O] [CommRing R] [Algebra Z O] [Algebra Z R]
  [AddCommGroup M] [Module O M] [Fintype J] [Fintype ι] (o : Module.Basis J Z O) {r : ℕ}
  (e : Fin r ≃ ι × J)

end Bases

section Module

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {Z R RA : Type} [CommRing Z] [CommRing R] [CommRing RA] [Algebra Z O]
    [Algebra Z R] [Algebra O RA] {inclR : RA →ₐ[O] O ⊗[Z] R} {φR : O ⊗[Z] R →ₐ[O] O ⊗[Z] R}
    {gR : G → (O ⊗[Z] R →ₐ[O] O ⊗[Z] R)} {πA : RA}
    (E : EtTie W RA (O ⊗[Z] R) inclR φR gR πA) (A : Subring R)
    (hA : ∀ (lam : O →ₗ[Z] Z) a, cf lam (sc E a) ∈ A) {Y : LocLat G Qp LL O}
    {J ι : Type} [Fintype J] [Fintype ι] (o : Module.Basis J Z O)



end Module

section Transport

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'}


end Transport

section RankOne

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {ψ : G →* LLˣ} (L : Lattice (O := O) (charRep ψ))


end RankOne

section Situation

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

theorem finrank_maxUnramified_levelFieldFiniteExtension (K : FinExt l) (s : ℕ) (hs : 1 ≤ s) :
    Module.finrank ℚ_[l] ↥(K0 (levelField K s)) = Module.finrank ℚ_[l] ↥(K0 K) := by
  have h1 : Ks (levelField K s) s = Ks K s := by
    refine le_antisymm (sup_le inf_le_left le_sup_right) (sup_le_sup_right ?_ _)
    exact le_inf le_sup_left inf_le_right
  have h2 := GlobalTheory.Cyc.finrank_Ks (levelField K s) s hs
  rw [h1, GlobalTheory.Cyc.finrank_Ks K s hs] at h2
  have h3 : 2 ≤ l := (Fact.out : l.Prime).two_le
  exact (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by omega) (pow_pos (by omega) _)) h2).symm

theorem val_le_iff (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (s : ℕ) :
    (s : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) ↔ ‖x‖ ≤ (l : ℝ) ^ (-(s : ℤ)) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl1 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  obtain ⟨y, rfl⟩ : ∃ y, x = (l : ℚ_[l]) ^ s * y := ⟨((l : ℚ_[l]) ^ s)⁻¹ * x, by field_simp⟩
  rw [map_mul, map_pow, map_natCast, AddValuation.map_mul, AddValuation.map_pow, P.v_l,
    norm_mul, norm_pow, Padic.norm_p, nsmul_one, inv_pow, ← zpow_natCast, ← zpow_neg,
    mul_le_iff_le_one_right (zpow_pos hl1 _)]
  have h1 : (s : WithTop ℚ) ≤ s + P.v LL (algebraMap ℚ_[l] ↥LL.1 y) ↔
      0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 y) := by
    conv_lhs => lhs; rw [← add_zero (s : WithTop ℚ)]
    exact WithTop.add_le_add_iff_left (WithTop.natCast_ne_top s)
  rw [h1, P.v_O]
  change IsIntegral ℤ_[l] _ ↔ _
  rw [isIntegral_algebraMap_iff , IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩

theorem absoluteGalois_mem_fixingSubgroup_maxUnramified {K : FinExt l} (g : ↥(GK K)) : (g : GQ l) ∈ (K0 K).fixingSubgroup :=
  fun x => g.2 ⟨x.1, x.2.1⟩

section Wach

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}

theorem mem_GKs (hs : W.s = s) (g : ↥(GK K)) : g ∈ W.GKs ↔ (g : GQ l) ∈ GK (levelField K s) := by
  rw [W.GKs_def, hs, P.PD_χ, ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub, val_le_iff]
  exact (((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g (absoluteGalois_mem_fixingSubgroup_maxUnramified g)).1 s).symm

theorem prim_ζQ (P : LocPrime l) (m : ℕ) : IsPrimitiveRoot (P.ζQ (m + 1)) (l ^ (m + 1)) := by
  have h : ∀ j, P.ζQ (j + 1) ^ l ^ j = P.ζQ 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [h]; exact P.ζQ_one
  have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by rw [pow_succ, pow_mul, h, P.ζQ_succ, P.ζQ_zero]
  rw [← orderOf_eq_prime_pow h1 h2]
  exact IsPrimitiveRoot.orderOf _

theorem resΓ_eq_one (g : ↥(GK K)) (hg : ∀ j : ℕ, (g : GQ l) (P.ζQ j) = P.ζQ j) : W.resΓ g = 1 := by
  have h1 : (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
    by_contra hne
    obtain ⟨m, hm⟩ := GlobalTheory.Cyc.exists_zpow_neg_lt (l := l) (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    have h2 := GlobalTheory.Cyc.IsCyc.norm_sub_one_le_of_prim P.χQ_cyc g _ (prim_ζQ P m) (hg _)
    have h3 : (l : ℝ) ^ (-((m + 1 : ℕ) : ℤ)) ≤ (l : ℝ) ^ (-(m : ℤ)) :=
      zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : l.Prime).one_le) (by push_cast; omega)
    exact absurd (h2.trans h3) (not_le.mpr hm)
  apply W.χΓ_inj
  apply Units.ext
  apply Subtype.val_injective
  have h2 := W.χΓ_res g
  rw [P.PD_χ, h1, map_one] at h2
  rw [map_one]
  exact h2

variable (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piS AI s))

end Wach

end Situation

end GlobalTheory.TorsionBoundCompare
end
end

noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

section Hyp

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime] (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) {K : FinExt l}
  {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem actVB_res (Y : Lat K LL) (g : ↥(GK K)) (g' : ↥(GK (levelField K s))) (hg : (g : GQ l) = g') :
    actVB ((LT l).PD K) Y.ρ g = actVB ((LT l).PD (levelField K s)) (resKs h Y) g' := by
  have h2 : Y.ρ g = resKs h Y g' := congrArg Y.ρ (Subtype.ext hg)
  have h3 : (((LT l).PD K).actB g).toAlgHom.toLinearMap.restrictScalars ℚ_[l] =
      (((LT l).PD (levelField K s)).actB g').toAlgHom.toLinearMap.restrictScalars ℚ_[l] :=
    LinearMap.ext fun b => (((LT l).PD_actB K g b).trans (by rw [hg])).trans
      ((LT l).PD_actB (levelField K s) g' b).symm
  unfold actVB
  rw [h2, h3]

theorem iInf_eq_of {α β γ : Type} [CompleteLattice γ] (f : α → γ) (g : β → γ)
    (h1 : ∀ a, ∃ b, f a = g b) (h2 : ∀ b, ∃ a, f a = g b) : ⨅ a, f a = ⨅ b, g b :=
  le_antisymm (le_iInf fun b => by obtain ⟨a, ha⟩ := h2 b; exact ha ▸ iInf_le f a)
    (le_iInf fun a => by obtain ⟨b, hb⟩ := h1 a; exact hb ▸ iInf_le g b)

theorem finrank_congr {R M : Type} [Field R] [AddCommGroup M] [Module R M] {X X' : Submodule R M}
    (e : X = X') : Module.finrank R ↥X = Module.finrank R ↥X' := by rw [e]

theorem fixed_eq (Y : Lat K LL) : (⨅ g : ((HW l).W K s LL h).GKs,
      LinearMap.ker (actVB ((LT l).PD K) Y.ρ (g : ↥(GK K)) - LinearMap.id)) =
      Dcris ((LT l).PD (levelField K s)) (resKs h Y) := by
  refine iInf_eq_of _ _ (fun g => ?_) fun g' => ?_
  · have hg : (g.1.1 : GQ l) ∈ GK (levelField K s) := (mem_GKs ((HW l).W_s K s LL h) g.1).mp g.2
    exact ⟨⟨g.1.1, hg⟩,
      congrArg (fun T => LinearMap.ker (T - LinearMap.id)) (actVB_res LT h Y g.1 ⟨g.1.1, hg⟩ rfl)⟩
  · exact ⟨⟨⟨g'.1, GK_le (K := K) (K' := levelField K s) h.2.2.1 g'.2⟩,
      (mem_GKs ((HW l).W_s K s LL h) _).mpr g'.2⟩,
      congrArg (fun T => LinearMap.ker (T - LinearMap.id)) (actVB_res LT h Y _ _ rfl)⟩

theorem crys_iff (Y : Lat K LL) :
    IsCrysOn (sit LT HW l AI K s LL h) (sit LT HW l AI K s LL h).W.GKs Y ↔
      IsCrys ((LT l).PD (levelField K s)) (resKs h Y) := by
  have h1 := finrank_congr (fixed_eq LT HW h Y)
  have h2 := congrArg (· * Module.finrank ↥LL.1 Y.V) (finrank_maxUnramified_levelFieldFiniteExtension K s h.1).symm
  exact iff_of_eq (congrArg₂ Eq h1 h2)

end Hyp

section Final

open Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

variable (LT : LocTheory) (HW : HWOf LT) (AI : LocAinf l (LT l)) {K : FinExt l}
  {s : ℕ} {LL : FinExt l} (h : Good K s LL)

variable (D : Formalism.BasicNotions.D7) (H : HWOf D.loc) (F : FonOf D.loc D.locA H)

end Final

end GlobalTheory.TorsionBoundCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOnOfIsCrys
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CrysOnLevel

theorem isCrysOn_of_isCrys : ∀ (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (Y : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) Y.ρ → Formalism.MainNotions.LocalSituation.IsCrysOn (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((HW l).W K s LL h).GKs Y := by
  intro D HW l _ K s LL h Y hY
  exact (GlobalTheory.TorsionBoundCompare.crys_iff D.loc HW (D.locA l) h Y).mpr
    ((GlobalTheory.T.restrict_crystalline_deRham_finiteExt l (D.loc l) (D.locA l) (D.locT l) K (GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.levelField K s) LL h.2.2.1
      Y.V Y.ρ).1 hY)

end GlobalTheory.CrysOnLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatum
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem crysOnCond_all : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), CrysOnCond D HW F :=
  fun D HW _ l _ K s LL h Y hY => GlobalTheory.CrysOnLevel.isCrysOn_of_isCrys D HW l K s LL h Y hY

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatumStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crysOnCond_of_every_datum : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), CrysOnCond D HW F := by
  first | exact @GlobalTheory.crysOnCond_all | exact GlobalTheory.crysOnCond_all | (intros; apply GlobalTheory.crysOnCond_all <;> assumption)
end
