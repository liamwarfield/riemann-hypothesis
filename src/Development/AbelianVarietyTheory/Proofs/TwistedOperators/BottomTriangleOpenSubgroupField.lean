module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharacterEqAtDetRootsOfCongruent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitCharEqOfNatCong

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupFixingVacuumFixesVector
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFrameCongruenceUnitaryAdelicStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFrameCongruenceUnitaryAdelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.FrameCongOpen

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def congInt (N : ℕ) : Subgroup (GL (Fin n) (Formalism.L2.Herm.intAf F E)) :=
  (Matrix.GeneralLinearGroup.map (n := Fin n)
    (Ideal.Quotient.mk (Ideal.span {((N : ℕ) : Formalism.L2.Herm.intAf F E)}))).ker

theorem mem_congInt_span {N : ℕ} (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    z ∈ congInt N ↔ ∀ a b, z.1 a b - (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) a b ∈
      Ideal.span {((N : ℕ) : Formalism.L2.Herm.intAf F E)} := by
  rw [congInt, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  rw [← Ideal.Quotient.eq]
  change Ideal.Quotient.mk _ (z.1 a b) = (1 : Matrix (Fin n) (Fin n) _) a b ↔ _
  simp only [Matrix.one_apply]
  split_ifs
  · rw [map_one]
  · rw [map_zero]

theorem mem_congInt {N : ℕ} (z : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    z ∈ congInt N ↔ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf F E,
      ((z.1 a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b = (N : E ⊗[F] Formalism.L2.Herm.Af F) * w := by
  have hone : ∀ a b, (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) a b : Formalism.L2.Herm.intAf F E) :
      E ⊗[F] Formalism.L2.Herm.Af F) = (1 : Matrix (Fin n) (Fin n) _) a b := fun a b => by
    simp only [Matrix.one_apply]; split_ifs <;> rfl
  rw [mem_congInt_span]
  refine forall₂_congr fun a b => ?_
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, c.2, ?_⟩
    rw [← hone, ← AddSubgroupClass.coe_sub, ← hc, Subring.coe_mul, Subring.coe_natCast, mul_comm]
  · rintro ⟨w, hw, e⟩
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, Subring.coe_natCast, AddSubgroupClass.coe_sub, hone, e, mul_comm]

theorem mem_cong (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : ℕ)
    (h1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ i j, (β⁻¹ * x * β)⁻¹.1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h3 : ∀ i j, ∃ z ∈ Formalism.L2.Herm.intAf F E,
      (β⁻¹ * x * β).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j = (N : E ⊗[F] Formalism.L2.Herm.Af F) * z) :
    x ∈ (congInt (F := F) (E := E) (n := n) N).map (frGL β) := by
  have hx : x = β * (β⁻¹ * x * β) * β⁻¹ := by group
  generalize β⁻¹ * x * β = m at h1 h2 h3 hx
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) =>
      A.map (Formalism.L2.Herm.intAf F E).subtype := Matrix.map_injective Subtype.val_injective
  let y : GL (Fin n) (Formalism.L2.Herm.intAf F E) :=
    ⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩,
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.mul_inv),
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.inv_mul)⟩
  have hy : frGL β y = x := by
    have : intGL F E n y = m := Units.ext rfl
    rw [hx, ← this]
    rfl
  exact ⟨y, (mem_congInt y).2 fun i j => h3 i j, hy⟩

theorem eventually_cong_mat (β : GL (Fin n) (E ⊗[F] Af F)) (N : ℕ) (hN : 0 < N) {X : Type} [TopologicalSpace X]
    {x₀ : X} {φ : X → GL (Fin n) (Af F ⊗[F] E)} (hf : Continuous φ) (h₀ : φ x₀ = 1) :
    ∀ᶠ κ in 𝓝 x₀, Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ) ∈
      (congInt (F := F) (E := E) (n := n) N).map (frGL β) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho := (GlobalTheory.Mass.intTens_open_compact F E).1
  set s := GlobalTheory.Mass.swapTens F E (Af F)
  let β' : GL (Fin n) (Af F ⊗[F] E) := Formalism.UG.bc (s.symm : _ →+* _) β
  have hβ : Formalism.UG.bc (s : _ →+* _) β' = β := Units.ext (Matrix.ext fun i j => s.apply_symm_apply _)
  let m : X → GL (Fin n) (Af F ⊗[F] E) := fun κ => β'⁻¹ * φ κ * β'
  have hm : Continuous m := (continuous_const.mul hf).mul continuous_const
  have hm1 : m x₀ = 1 := by simp only [m, h₀, mul_one, inv_mul_cancel]
  have hs : ∀ κ, β⁻¹ * Formalism.UG.bc (s : _ →+* _) (φ κ) * β = Formalism.UG.bc (s : _ →+* _) (m κ) := fun κ => by
    simp only [m, map_mul, map_inv, hβ]
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j ∈
      GlobalTheory.Mass.intTens F E := fun i j => by
    simp only [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  have e1 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ).1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_val.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀).1 i j ∈ _ by rw [hm1]; exact hone i j)
  have e2 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ)⁻¹.1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_coe_inv.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀)⁻¹.1 i j ∈ _ by rw [hm1, inv_one]; exact hone i j)
  have e3 : ∀ᶠ κ in 𝓝 x₀, ∀ i j,
      algebraMap F _ ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    have hc : Continuous fun κ => algebraMap F (Af F ⊗[F] E) ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) :=
      continuous_const.mul (((Units.continuous_val.comp hm).matrix_elem i j).sub continuous_const)
    refine (ho.preimage hc).mem_nhds ?_
    rw [Set.mem_preimage, hm1, Units.val_one, sub_self, mul_zero]
    exact (GlobalTheory.Mass.intTens F E).zero_mem
  filter_upwards [e1, e2, e3] with κ h1 h2 h3
  refine mem_cong β _ N ?_ ?_ ?_
  · rw [hs]; exact h1
  · rw [hs, ← map_inv]; exact h2
  · intro i j
    refine ⟨_, h3 i j, ?_⟩
    have hN' : ((N : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have e : (m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j =
        (N : ℕ) * (algebraMap F _ ((N : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j)) := by
      rw [← mul_assoc, ← map_natCast (algebraMap F (Af F ⊗[F] E)), ← map_mul,
        mul_inv_cancel₀ hN', map_one, one_mul]
    have := congrArg s e
    rw [map_mul, map_natCast, map_sub] at this
    rw [hs]
    refine Eq.trans ?_ this
    congr 1
    simp only [Matrix.one_apply]; split_ifs <;> simp

def congFr (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (N : ℕ) : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
  (congInt (F := F) (E := E) (n := n) N).map (frGL β)

theorem mem_congFr {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N : ℕ} (hx : x ∈ congFr β N) :
    ∃ z : GL (Fin n) (Formalism.L2.Herm.intAf F E), frGL β z = x ∧ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf F E,
      ((z.1 a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) a b = (N : E ⊗[F] Formalism.L2.Herm.Af F) * w := by
  obtain ⟨z, hz, e⟩ := Subgroup.mem_map.1 hx
  exact ⟨z, e, (mem_congInt z).1 hz⟩

end General

theorem exists_open_cong : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ κ ∈ U, ∃ z : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.frGL β z = Lev.finE V κ ∧ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w := by
  intro D V β N hN
  refine ⟨(congFr β N).comap (Formalism.IndefR.Lev.finE V),
    ?_, fun κ hκ => ?_⟩
  · haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
    haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
    have hf : Continuous (finHom V) :=
      (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
    exact eventually_cong_mat β N hN hf (map_one _)
  · exact mem_congFr (Subgroup.mem_comap.1 hκ)

end GlobalTheory.FrameCongOpen

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_frame_congruence_unitaryAdelic : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ κ ∈ U, ∃ z : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.frGL β z = Lev.finE V κ ∧ ∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w := by
  first | exact @GlobalTheory.FrameCongOpen.exists_open_cong | exact GlobalTheory.FrameCongOpen.exists_open_cong | (intros; apply GlobalTheory.FrameCongOpen.exists_open_cong <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardPairFirstInvariantCongruenceOneStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardPairFirstInvariantCongruenceOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdFstInv

theorem mul_sub_mem {R : Type} [CommRing R] (O : Subring R) (c : R) {b a : ℕ} (Z : Matrix (Fin b) (Fin b) R)
    (hZ : ∀ i j, ∃ w ∈ O, Z i j - (1 : Matrix (Fin b) (Fin b) R) i j = c * w)
    (Y : Matrix (Fin b) (Fin a) R) (hY : ∀ i j, Y i j ∈ O) (i : Fin b) (j : Fin a) :
    ∃ w ∈ O, (Z * Y) i j - Y i j = c * w := by
  choose w hwO hw using hZ
  refine ⟨∑ k, w i k * Y k j, O.sum_mem fun k _ => O.mul_mem (hwO i k) (hY k j), ?_⟩
  have hsplit : (Z * Y) i j - Y i j = ∑ k, (Z i k - (1 : Matrix (Fin b) (Fin b) R) i k) * Y k j := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [← Matrix.mul_apply, ← Matrix.mul_apply, Matrix.one_mul]
  rw [hsplit, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hw i k, mul_assoc]

theorem mem_iff {R : Type} [CommRing R] (O : Subring R) (J : Ideal O) (N : ℕ) (hN : (N : O) ∈ J) {p q w : R}
    (hp : p ∈ O) (hw : w ∈ O) (h : q - p = (N : R) * w) :
    (∃ h : q ∈ O, (⟨q, h⟩ : O) ∈ J) ↔ ∃ h : p ∈ O, (⟨p, h⟩ : O) ∈ J := by
  have hq : q ∈ O := by
    have e : q = p + (N : R) * w := by linear_combination h
    rw [e]
    exact O.add_mem hp (O.mul_mem (natCast_mem O N) hw)
  have key : (⟨q, hq⟩ : O) = ⟨p, hp⟩ + (N : O) * ⟨w, hw⟩ := by
    apply Subtype.ext
    show q = p + ((N : O) : R) * w
    rw [show ((N : O) : R) = (N : R) from map_natCast O.subtype N]
    linear_combination h
  have hNw : (N : O) * ⟨w, hw⟩ ∈ J := J.mul_mem_right _ hN
  constructor
  · rintro ⟨_, hJ⟩
    refine ⟨hp, ?_⟩
    rw [key] at hJ
    exact (J.add_mem_iff_left hNw).1 hJ
  · rintro ⟨_, hJ⟩
    refine ⟨hq, ?_⟩
    rw [key]
    exact J.add_mem hJ hNw

theorem fixed_mul {R : Type} [CommRing R] {b a : ℕ} (e : R) (M : Matrix (Fin b) (Fin b) R) (x : Matrix (Fin b) (Fin a) R)
    (H : ∀ i j, e * x i j = x i j) (i : Fin b) (j : Fin a) : e * (M * x) i j = (M * x) i j := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, H k j]

theorem fixed_iff {R : Type} [CommRing R] {b a : ℕ} (e : R) (M : GL (Fin b) R) (P : Matrix (Fin a) (Fin a) R) (hP : P = 1)
    (x : Matrix (Fin b) (Fin a) R) :
    (∀ i j, e * (M.val * x * P) i j = (M.val * x * P) i j) ↔ ∀ i j, e * x i j = x i j := by
  subst hP
  simp only [Matrix.mul_one]
  constructor
  · intro h i j
    have hx : x = (M⁻¹).val * (M.val * x) := by
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [hx]
    exact fixed_mul e _ _ h i j
  · intro h i j
    exact fixed_mul e _ _ h i j

variable {D : D7}

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V (1 : GA D V)⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [inv_one, map_one, Units.val_one]

theorem actO_neg_one (A WW : HSp D) (κ : GA D WW) (x : WO A WW) :
    actO (GlobalTheory.Grid.neg A) WW 1 κ x = actO A WW 1 κ x := by
  unfold actO
  rw [mt_one, mt_one]

theorem isHalf_iff (A WW : HSp D) (κ : GA D WW) (e : AE D) (x : WO A WW) :
    IsHalf e (actO A WW 1 κ x) ↔ IsHalf e x := by
  unfold IsHalf actO
  exact fixed_iff e (matHom WW κ) _ (mt_one A) x

theorem frMapO_eq {A WW : HSp D} (βA : GL (Fin A.rank) (Lev.EAf D)) {βW : GL (Fin WW.rank) (Lev.EAf D)}
    {κ : GA D WW} {z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hz : Formalism.L2.DIV.frGL βW z = Lev.finE WW κ) (x : WO A WW) :
    frMapO A WW βA βW (actO A WW 1 κ x) =
      ((intGL D.host.F D.host.E _ z⁻¹)⁻¹).val * frMapO A WW βA βW x *
        (intGL D.host.F D.host.E _ (1 : GL (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))).val := by
  have h1 := GlobalTheory.FrameRed.frMapO_actO (βS := βA) (βT := βW) (g := (1 : GA D A)) (h := κ⁻¹)
    (y := 1) (z := z⁻¹) (by rw [map_one, map_one]) (by rw [map_inv, map_inv, hz]) x
  rw [inv_one, inv_inv] at h1
  exact h1

set_option maxHeartbeats 1600000 in
theorem frMapO_eq' {A WW : HSp D} (βA : GL (Fin A.rank) (Lev.EAf D)) {βW : GL (Fin WW.rank) (Lev.EAf D)}
    {κ : GA D WW} {z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hz : Formalism.L2.DIV.frGL βW z = Lev.finE WW κ) (x : WO A WW) :
    frMapO A WW βA βW (actO A WW 1 κ x) = (intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x := by
  rw [frMapO_eq βA hz x, map_inv (intGL D.host.F D.host.E WW.rank), inv_inv,
    map_one (intGL D.host.F D.host.E A.rank), Units.val_one, Matrix.mul_one]

theorem topL_int {b a : ℕ} (k : ℕ) {Y : Matrix (Fin b) (Fin a) (Lev.EAf D)} (hY : IsIntM (D := D) Y) :
    IsIntM (D := D) (topL k Y) := by
  intro i j
  unfold topL
  split_ifs with hij
  · exact hY _ _
  · exact zero_mem _

theorem topL_sub {R : Type} [CommRing R] (O : Subring R) (c : R) {b a : ℕ} (k : ℕ) {Y Y' : Matrix (Fin b) (Fin a) R}
    (h : ∀ i j, ∃ w ∈ O, Y' i j - Y i j = c * w) (i j : Fin k) :
    ∃ w ∈ O, topL k Y' i j - topL k Y i j = c * w := by
  unfold topL
  split_ifs with hij
  · exact h _ _
  · exact ⟨0, O.zero_mem, by rw [sub_self, mul_zero]⟩

set_option maxHeartbeats 1600000 in
theorem stdFst_actO : ∀ (D : D7) (A WW : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ (I : Ideal (𝓞 D.host.E)) (βA : GL (Fin A.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ((N : ℕ) : 𝓞 D.host.E) ∈ I → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ (κ : GA D WW) (z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), Formalism.L2.DIV.frGL βW z = Lev.finE WW κ → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin WW.rank) (Fin WW.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w) → ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (actO (GlobalTheory.Grid.neg A) WW 1 κ x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW x := by
  intro D A WW ν e Sf hSf I βA βW N hN hNI hNS hν κ z hz hz1 x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [actO_neg_one, isHalf_iff, frMapO_eq' βA hz x]
  have hInt : IsIntM (D := D) ((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) ↔
      IsIntM (D := D) (frMapO A WW βA βW x) := by
    have h2 := GlobalTheory.FrameRed.isIntM_iff (D := D) z⁻¹
      (1 : GL (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (frMapO A WW βA βW x)
    rwa [map_inv (intGL D.host.F D.host.E WW.rank), inv_inv, map_one (intGL D.host.F D.host.E A.rank),
      Units.val_one, Matrix.mul_one] at h2
  by_cases hM : IsIntM (D := D) (frMapO A WW βA βW x)
  · have hc : ∀ i j, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
        ((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) i j - frMapO A WW βA βW x i j =
          (N : Lev.EAf D) * w :=
      mul_sub_mem (Formalism.L2.Herm.intAf D.host.F D.host.E) (N : Lev.EAf D) (intGL D.host.F D.host.E _ z).val hz1 _ hM
    have hNJ : ((N : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ Formalism.L2.DIV.idS D.host.F I := by
      rw [← map_natCast (Formalism.L2.DIV.oToS D.host.F D.host.E) N]
      exact Ideal.mem_map_of_mem _ hNI
    have hId : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (((intGL D.host.F D.host.E _ z).val * frMapO A WW βA βW x) i j) ↔
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (frMapO A WW βA βW x i j) := fun i j => by
      obtain ⟨w, hw, hq⟩ := hc i j
      exact GlobalTheory.StdFstInv.mem_iff _ _ N hNJ (hM i j) hw hq
    have hU := GlobalTheory.UnitCharCong.unitChar_eq_of_natCong D ν e Sf hSf N hN hNS hν _ _ (topL_int A.rank hM)
      (topL_sub _ _ A.rank hc)
    rw [hU]
    have hcond := and_congr (Iff.rfl (a := IsHalf e x)) (and_congr hInt
      (forall_congr' fun (i : Fin WW.rank) => forall_congr' fun (j : Fin A.rank) =>
        imp_congr (Iff.rfl (a := A.rank ≤ (i : ℕ))) (hId i j)))
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hcond.1 h1) h2
    · exact absurd (hcond.2 h2) h1
    · rfl
  · rw [if_neg (fun h => hM (hInt.1 h.2.1)), if_neg (fun h => hM h.2.1)]

end GlobalTheory.StdFstInv

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairFirst_invariant_congruenceOne : ∀ (D : D7) (A WW : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ (I : Ideal (𝓞 D.host.E)) (βA : GL (Fin A.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ((N : ℕ) : 𝓞 D.host.E) ∈ I → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ (κ : GA D WW) (z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), Formalism.L2.DIV.frGL βW z = Lev.finE WW κ → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin WW.rank) (Fin WW.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w) → ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (actO (GlobalTheory.Grid.neg A) WW 1 κ x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW x := by
  first | exact @GlobalTheory.StdFstInv.stdFst_actO | exact GlobalTheory.StdFstInv.stdFst_actO | (intros; apply GlobalTheory.StdFstInv.stdFst_actO <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelUnitaryHeckeCharacterTrivialCongruenc
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelUnitaryHeckeCharacterTrivialCongruenc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.HeckeLevel

theorem add_mul_sub_one {R : Type} [CommRing R] (m c : ℕ) (w : R) :
    1 + ((m * c : ℕ) : R) * w - 1 = m • ((c : R) * w) := by
  rw [nsmul_eq_mul]
  push_cast
  ring

theorem exists_level : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ∣ N → ∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1 := by
  intro D ν hν
  obtain ⟨N₀, hN₀, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν.1
  refine ⟨N₀, hN₀, ?_⟩
  rintro N ⟨c, rfl⟩ u hu ⟨w, hw, e⟩ ⟨w', hw', e'⟩
  have key : ∀ z : Af D.host.F ⊗[D.host.F] D.host.E,
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z : Lev.EAf D) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E → z ∈ intAE D :=
    fun z hz => (GlobalTheory.IdemSupport.mem_intAE_iff z).2 hz
  have hint : ∀ (a : AE D) (v : Lev.EAf D), v ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
      toEAf D a = 1 + ((N₀ * c : ℕ) : Lev.EAf D) * v → finPart D a ∈ intAE D := by
    intro a v hv ha
    refine key _ ?_
    change toEAf D a ∈ _
    rw [ha]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ _) hv)
  refine hker u ⟨hu, hint _ w hw e, hint _ w' hw' e'⟩
    ⟨(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm ((c : Lev.EAf D) * w), key _ ?_, ?_⟩
  · rw [AlgEquiv.apply_symm_apply]
    exact mul_mem (natCast_mem _ _) hw
  · apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    rw [map_sub, map_one, map_nsmul, AlgEquiv.apply_symm_apply]
    have e2 : (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (u : AE D)) : Lev.EAf D) =
      1 + ((N₀ * c : ℕ) : Lev.EAf D) * w := e
    rw [e2]
    exact add_mul_sub_one N₀ c w

end GlobalTheory.HeckeLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelUnitaryHeckeCharacterTrivialCongruencStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_unitaryHeckeCharacter_trivial_congruence : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ∣ N → ∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1 := by
  first | exact @GlobalTheory.HeckeLevel.exists_level | exact GlobalTheory.HeckeLevel.exists_level | (intros; apply GlobalTheory.HeckeLevel.exists_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupFixingVacuumFixesVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.RowTest

theorem IsBottomTri.exists_open_fix_f : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac →
      X.ω t (1, κ) (X.f t) = X.f t := by
  intro D T L sc G W i j A A' WW X hX t
  have h := hX.is
  have hom := h.weil t
  have hT2 : IsHeckeChar D ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) / (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))) :=
    hom.hecT
  have hx : ∀ x, ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) x =
      (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) / (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))) x)⁻¹ := fun x => by
    rw [MonoidHom.div_apply, MonoidHom.div_apply, inv_div]
  have hνH : IsHeckeChar D ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) :=
    ⟨hT2.1.inv.congr fun x => (hx x).symm, fun x => by rw [hx, hT2.2, inv_one]⟩
  obtain ⟨N₀, hN₀, hN₀'⟩ := GlobalTheory.T.exists_level_unitaryHeckeCharacter_trivial_congruence D _ hνH
  have hI : X.ideal (locPl G) t ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  set N : ℕ := N₀ * Ideal.absNorm (X.ideal (locPl G) t) * ∏ w ∈ locPl G t, Ideal.absNorm w.asIdeal with hNdef
  have hNpos : 0 < N := by
    refine Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hN₀.ne' ?_) (Finset.prod_ne_zero_iff.2 fun w _ => ?_))
    · exact fun h0 => hI (Ideal.absNorm_eq_zero_iff.1 h0)
    · exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hNI : ((N : ℕ) : 𝓞 D.host.E) ∈ X.ideal (locPl G) t := by
    rw [hNdef, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _))
  have hNw : ∀ w ∈ locPl G t, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := fun w hw => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w : Formalism.L2.DIV.Pl D.host.E => Ideal.absNorm w.asIdeal) hw
    rw [hNdef, hc, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))
  have hNdiv : N₀ ∣ N := ⟨Ideal.absNorm (X.ideal (locPl G) t) * ∏ w ∈ locPl G t, Ideal.absNorm w.asIdeal, by rw [hNdef, mul_assoc]⟩
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.exists_open_frame_congruence_unitaryAdelic D WW X.rW.β N hNpos
  refine ⟨U, hUo, fun κ hκ _ hvac => ?_⟩
  obtain ⟨z, hz, hzc⟩ := hU κ hκ
  have hst : Lev.finE WW κ ∈ Formalism.L2.DIV.St X.rW.β := ⟨z, hz⟩
  have hinv := GlobalTheory.T.standardPairFirst_invariant_congruenceOne D A WW _ (X.e t) (locPl G t) (h.idem t) (X.ideal (locPl G) t) X.rA.β X.rW.β N hNpos hNI hNw
    (hN₀' N hNdiv) κ z hz hzc
  have hsdA := isSelfDualC_neg' h.rigA.1
  have hsdW := h.rigW.1
  have hsg : ∀ f, (X.ω t).toSgn true (1, κ) f = X.ω t (1, κ) f := fun f => by
    simp [GlobalTheory.Grid.WRep.toSgn]
  have key := GlobalTheory.ExportSeries.DualType.om_theta_move hom
    (fun Tm hT Ψ hΨ => GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ h.isVac.1 _ WW _ _ hsdA hsdW _
      (GlobalTheory.PlaceDatum.idemSum_mul_self (h.idem t)) (GlobalTheory.PlaceDatum.infPart_idemSum (h.idem t)) _ h.isVac.2.theta Tm hT Ψ hΨ)
    (h.fst t) (h.fst t) (g := 1) (h := κ)
    (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D _ WW _ _ _ _ hsdA hsdW h.rigA.2.1 h.rigW.2.1 1 κ (by rw [map_one]; exact one_mem _) hst)
    one_ne_zero (c' := 1) (by rw [one_smul, hsg]; exact hvac) (fun x => by rw [one_mul, hinv x])
  rw [hsg, one_mul, one_smul] at key
  exact key

end GlobalTheory.RowTest

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupFixingVacuumFixesVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_exists_open_fixes_finiteVector : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac →
      X.ω t (1, κ) (X.f t) = X.f t := by
  first | exact @GlobalTheory.RowTest.IsBottomTri.exists_open_fix_f | exact GlobalTheory.RowTest.IsBottomTri.exists_open_fix_f | (intros; apply GlobalTheory.RowTest.IsBottomTri.exists_open_fix_f <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.BottomLevel

theorem fin_vec_fix : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) (X.f t) = X.f t := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U₁, h₁, hU₁⟩ := GlobalTheory.T.exists_open_fixing_seesaw_vacuum_definite_bottom hX t
  obtain ⟨U₂, h₂, hU₂⟩ := GlobalTheory.T.definiteBottom_exists_open_fixes_finiteVector hX t
  exact ⟨U₁ ⊓ U₂, h₁.inter h₂, fun κ hκ hf => hU₂ κ hκ.2 hf (hU₁ κ hκ.1 hf)⟩

end GlobalTheory.BottomLevel
