module

public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FirstLatticeBaseChange
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CharacterDataBaseChange
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
public import ReciprocityTheory.DualLattices.ImportsBis
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChange
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, LocFree R n (D.af R p (χ τ)) ∧ LocFree R n (D.hh R p (χ τ)) ∧ D.af R p (χ τ) ≤ stdLat R _ ∧ ∀ i, LocFree R 1 (D.xId (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → (D.bc RC).Good₁ RC p (fun τ a => algebraMap Ω C (χ τ a)) ∧ ∀ τ, (D.bc RC).af RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.af R p (χ τ)) ∧ (D.bc RC).hh RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.hh R p (χ τ)) ∧ ∀ i, (D.bc RC).xId (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.xId (χ τ) i) := by
  exact @PositivityTheory.Xgn.good_lattice_base_change

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_good_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, LocFree R n (D.af R p (χ τ)) ∧ LocFree R n (D.hh R p (χ τ)) ∧ D.af R p (χ τ) ≤ stdLat R _ ∧ ∀ i, LocFree R 1 (D.xId (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → (D.bc RC).Good₁ RC p (fun τ a => algebraMap Ω C (χ τ a)) ∧ ∀ τ, (D.bc RC).af RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.af R p (χ τ)) ∧ (D.bc RC).hh RC p (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.hh R p (χ τ)) ∧ ∀ i, (D.bc RC).xId (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.xId (χ τ) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBaseChangeLargerRingHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBaseChangeLargerRingHolds
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem lattice_base_change_larger_ring : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → CharData RC p (algebraMap Ω C w) (fun τ a => algebraMap Ω C (χ τ a)) ∧ (D.bc RC).Base RC p (algebraMap Ω C w) :=
  @PositivityTheory.Xgn.character_data_base_change

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBaseChangeLargerRingHoldsStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_base_change_larger_ring_holds : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → CharData RC p (algebraMap Ω C w) (fun τ a => algebraMap Ω C (χ τ a)) ∧ (D.bc RC).Base RC p (algebraMap Ω C w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.lattice_base_change_larger_ring | exact GlobalTheory.CompanionTheory.Ar.Num.lattice_base_change_larger_ring | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.lattice_base_change_larger_ring <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderLatticeBase
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderLatticeBase
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CompanionTheory.Ar.Num.StepOnto

def stepSub (F : Type) [Field F] (n i : ℕ) : AddSubgroup (Fin n → F) where
  carrier := {x | ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0}
  add_mem' := by
    intro a b ha hb j hj
    simp [ha j hj, hb j hj]
  zero_mem' := by
    intro j _
    rfl
  neg_mem' := by
    intro a ha j hj
    simp [ha j hj]

theorem exists_inv_add_sq {C R : Type} [Field C] [IsAlgClosed C] [CharZero C] [CommRing R]
    [Algebra R C] (v : Valuation C NNReal) (hv : v.Integers R) {N : Type} [AddCommGroup N]
    [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) (g : N → C)
    (hg : g ∈ AA.carrier) (h0 : g 0 = 0) (hK : ∀ k ∈ K, g k = 0) :
    ∃ h ∈ AA.carrier, ∃ q ∈ sqIdeal (augIdeal AA.carrier),
      h 0 = 0 ∧ (∀ x, ∀ k ∈ K, h (x + k) = h x) ∧ g = h + q := by
  classical
  obtain ⟨-, -, -, H4⟩ := ReciprocityTheory.PGsh.L2.h3 C R ‹IsAlgClosed C› ‹CharZero C› v hv N K AA
  have hg' : g ∈ augIdeal AA.carrier := by
    refine Submodule.mem_inf.2 ⟨hg, ?_⟩
    rw [LinearMap.mem_ker]
    exact h0
  have hres : ReciprocityTheory.PGsh.L2.resK (R := R) K g = 0 := by
    funext k
    show g k = 0
    exact hK k k.2
  have h2 := H4 g hg' (by rw [hres]; exact zero_mem _)
  obtain ⟨h, hh, q, hq, hgq⟩ := Submodule.mem_sup.1 h2
  obtain ⟨b, hb, rfl⟩ := hh
  obtain ⟨hbA, hb0⟩ := Submodule.mem_inf.1 hb
  refine ⟨_, hbA, q, ?_, ?_, ?_, hgq.symm⟩
  · have hsq : augIdeal AA.carrier * augIdeal AA.carrier ≤ sqIdeal (augIdeal AA.carrier) := by
      rw [Submodule.mul_le]
      intro x hx y hy
      show x * y ∈ Submodule.span R {h | ∃ f ∈ augIdeal AA.carrier, ∃ f' ∈ augIdeal AA.carrier, h = f * f'}
      exact Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
    exact hsq hq
  · show b (QuotientAddGroup.mk 0) = 0
    rw [QuotientAddGroup.mk_zero]
    exact LinearMap.mem_ker.1 hb0
  · intro x k hk
    show b (QuotientAddGroup.mk (x + k)) = b (QuotientAddGroup.mk x)
    have hk0 : (QuotientAddGroup.mk k : N ⧸ K) = 0 := (QuotientAddGroup.eq_zero_iff k).2 hk
    rw [QuotientAddGroup.mk_add, hk0, add_zero]

theorem avg_mem {C V X F : Type} [Field C] [AddCommGroup V] [Module C V] [Field F] [Fintype F]
    [DecidableEq F] [AddCommGroup X] [Module F X]
    (T : AddSubgroup ((X → C) × V)) (S : Set C) (hs : ∀ a ∈ S, ∀ t ∈ T, a • t ∈ T)
    (χ : F → C) (hS : ∀ a, χ a ∈ S) (hmul : ∀ a b, χ (a * b) = χ a * χ b) (h1 : χ 1 = 1)
    (u : C) (hu : u ∈ S) (hu' : u * (Fintype.card Fˣ : C) = 1)
    (heq : ∀ (a : F) g m, (g, m) ∈ T → ((fun x => g (a • x)), χ a • m) ∈ T)
    (h : X → C) (m : V) (hm : (h, m) ∈ T) :
    ((fun x => u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)), m) ∈ T := by
  have hmem : ∀ a : Fˣ, (u • χ ((a⁻¹ : Fˣ) : F) • ((fun x => h ((a : F) • x)), χ (a : F) • m)) ∈ T :=
    fun a => hs u hu _ (hs _ (hS _) _ (heq _ h m hm))
  suffices e : ((fun x => u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)), m) =
      ∑ a : Fˣ, u • χ ((a⁻¹ : Fˣ) : F) • ((fun x => h ((a : F) • x)), χ (a : F) • m) by
    rw [e]
    exact T.sum_mem (fun a _ => hmem a)
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    funext x
    dsimp only
    rw [Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · rw [Prod.snd_sum]
    have hterm : ∀ a : Fˣ, (u • χ ((a⁻¹ : Fˣ) : F) • ((fun x => h ((a : F) • x)), χ (a : F) • m)).2 = u • m := by
      intro a
      simp only [Prod.smul_snd, smul_smul]
      rw [mul_assoc, ← hmul, Units.inv_mul, h1, mul_one]
    rw [Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul C, smul_smul, mul_comm, hu', one_smul]

theorem avg_smul {C X F : Type} [Field C] [Field F] [Fintype F] [DecidableEq F] [AddCommGroup X]
    [Module F X] (χ : F → C) (hmul : ∀ a b, χ (a * b) = χ a * χ b) (h1 : χ 1 = 1) (u : C)
    (h : X → C) (b : Fˣ) (x : X) :
    u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (b : F) • x) =
      χ (b : F) * (u * ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)) := by
  have key : ∑ a : Fˣ, χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (b : F) • x) =
      ∑ c : Fˣ, χ (b : F) * (χ ((c⁻¹ : Fˣ) : F) * h ((c : F) • x)) := by
    refine Fintype.sum_equiv (Equiv.mulRight b) _ _ (fun a => ?_)
    show χ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (b : F) • x) =
      χ (b : F) * (χ (((a * b)⁻¹ : Fˣ) : F) * h (((a * b : Fˣ) : F) • x))
    rw [smul_smul, ← mul_assoc, ← hmul, Units.val_mul, mul_inv_rev, Units.val_mul, ← mul_assoc,
      Units.mul_inv, one_mul]
  rw [key, ← Finset.mul_sum]
  ring

theorem mem_vanSub {C F : Type} [Field C] [Field F] {n i : ℕ} (g : (Fin n → F) → C) :
    g ∈ (vanSub C F n i).toAddSubgroup ↔ ∀ x : Fin n → F, (∀ j : Fin n, i ≤ (j : ℕ) → x j = 0) → g x = 0 := by
  rw [Submodule.mem_toAddSubgroup]
  show g ∈ Submodule.pi {x : Fin n → F | ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0} (fun _ => (⊥ : Submodule C C)) ↔ _
  simp only [Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]

theorem eq_on_step {C F : Type} [Field C] [Field F] {n : ℕ} (i : Fin n) (H : (Fin n → F) → C)
    (χ : F → C) (hχ0 : χ 0 = 0)
    (hinv : ∀ y, ∀ k ∈ stepSub F n i, H (y + k) = H y)
    (hsm : ∀ (b : Fˣ) y, H ((b : F) • y) = χ (b : F) * H y) (h0 : H 0 = 0)
    (x : Fin n → F) (hx : ∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → x j = 0) :
    H x = H (Pi.single i 1) * χ (x i) := by
  have hk : x - x i • Pi.single i 1 ∈ stepSub F n i := by
    show ∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → (x - x i • (Pi.single i 1 : Fin n → F) : Fin n → F) j = 0
    intro j hj
    rcases eq_or_lt_of_le hj with hij | hij
    · have hji : j = i := Fin.ext hij.symm
      subst hji
      simp
    · have hne : j ≠ i := fun e => by subst e; exact lt_irrefl _ hij
      simp [hx j hij, Pi.single_apply, hne]
  have e : H x = H (x i • Pi.single i 1) := by
    have := hinv (x i • Pi.single i 1) _ hk
    rwa [add_sub_cancel] at this
  rw [e]
  by_cases hxi : x i = 0
  · rw [hxi, zero_smul, h0, hχ0, mul_zero]
  · have := hsm (Units.mk0 (x i) hxi) (Pi.single i 1)
    rw [Units.val_mk0] at this
    rw [this, mul_comm]

end GlobalTheory.CompanionTheory.Ar.Num.StepOnto

namespace GlobalTheory.CompanionTheory.Ar.Num

open StepOnto

theorem stepGraph_snd_eq_kk : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] [IsAlgClosed C] [CharZero C] (RC : Subalgebra o C) (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → ∀ (p : ℕ) [Fact p.Prime], v (p : C) < 1 → ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (φ : Equiv.Perm Sg), D.Base RC p w → ∀ AA : HopfOrder (C := C) RC (Fin n → F), AA.carrier.toAddSubgroup = D.M → FStable F AA.carrier → ∀ (σ : MulChar F RC), IsFund p σ → FlagConcl v p AA.carrier (Pi.basisFun F (Fin n)) σ → ∀ e : Sg → ℕ, (∀ τ a, χ τ a = ((σ ^ p ^ e τ) a : RC)) → (∀ τ, σ ^ p ^ e (φ τ) = σ ^ p ^ (e τ + 1)) → (∀ τ, (∀ g ∈ sqIdeal (augIdeal AA.carrier), (g, 0) ∈ D.Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ D.Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ D.Th τ) ∧ ∀ g ∈ eig AA.carrier (σ ^ p ^ e τ), (g, 0) ∈ D.Th τ → g ∈ sqIdeal (augIdeal AA.carrier)) → ∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i := by
  intro o C _ _ _ _ _ RC v hRC p _ hp F _ _ _ _ n Sg r s D w χ φ hB AA hAA hFS σ hσ hfl e hχ hφ hTh τ i
  obtain ⟨hsq, heq, -⟩ := hTh τ
  have hth := (hB.th τ).1
  have hstab : ∀ a ∈ RC, ∀ t ∈ D.Th τ, a • t ∈ D.Th τ := fun a ha t ht => ((hB.stable τ) a ha).2.2 t ht
  have hχ0 : χ τ 0 = 0 := by
    rw [hχ, MulChar.map_zero]
    rfl
  ext m
  constructor
  · rintro ⟨⟨a, m'⟩, hmem, rfl⟩
    have hmem' : ((a • fun y : Fin n → F => χ τ (y i)), m') ∈
        D.Th τ ⊔ (vanSub C F n (↑i + 1)).toAddSubgroup.prod ⊥ := hmem
    obtain ⟨⟨g, m1⟩, hgm, ⟨f, m2⟩, hf, hsum⟩ := AddSubgroup.mem_sup.1 hmem'
    obtain ⟨hfv, hm2⟩ := AddSubgroup.mem_prod.1 hf
    have hm2' : m2 = 0 := AddSubgroup.mem_bot.1 hm2
    have e0 : g + f = a • (fun y : Fin n → F => χ τ (y i)) := congrArg Prod.fst hsum
    have e1 : m1 + m2 = m' := congrArg Prod.snd hsum
    rw [hm2', add_zero] at e1
    subst e1
    have e2 : g = a • (fun y : Fin n → F => χ τ (y i)) - f := eq_sub_of_add_eq e0
    show m1 ∈ AddSubgroup.map (AddMonoidHom.snd _ _) (D.Th τ ⊓ (vanSub C F n ↑i).toAddSubgroup.prod ⊤)
    refine AddSubgroup.mem_map.2 ⟨(g, m1), AddSubgroup.mem_inf.2 ⟨hgm, AddSubgroup.mem_prod.2 ⟨?_, AddSubgroup.mem_top _⟩⟩, rfl⟩
    refine (mem_vanSub g).2 (fun x hx => ?_)
    have hxi : x i = 0 := hx i le_rfl
    have hfx : f x = 0 := (mem_vanSub f).1 hfv x (fun j hj => hx j (by omega))
    rw [e2]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hxi, hχ0, mul_zero, hfx, sub_zero]
  · intro hm
    have hm' : m ∈ AddSubgroup.map (AddMonoidHom.snd _ _) (D.Th τ ⊓ (vanSub C F n ↑i).toAddSubgroup.prod ⊤) := hm
    obtain ⟨⟨g, m'⟩, hgm, rfl⟩ := AddSubgroup.mem_map.1 hm'
    obtain ⟨hgTh, hgp⟩ := AddSubgroup.mem_inf.1 hgm
    have hgv : g ∈ (vanSub C F n ↑i).toAddSubgroup := (AddSubgroup.mem_prod.1 hgp).1
    obtain ⟨hgM, hg0⟩ := (hth g).1 ⟨m', hgTh⟩
    have hgA : g ∈ AA.carrier := by
      rw [← hAA] at hgM
      exact (Submodule.mem_toAddSubgroup _).1 hgM
    have hgK : ∀ k ∈ stepSub F n ↑i, g k = 0 := fun k hk => (mem_vanSub g).1 hgv k hk
    have hv : v.Integers RC :=
      ⟨fun a b hab => Subtype.ext hab, fun x => (hRC x).1 x.2, fun r hr => ⟨⟨r, (hRC r).2 hr⟩, rfl⟩⟩
    obtain ⟨h, hhA, q, hq, hh0, hhinv, hgq⟩ := exists_inv_add_sq v hv AA (stepSub F n ↑i) g hgA hg0 hgK
    have hhTh : (h, m') ∈ D.Th τ := by
      have e3 : (h, m') = (g, m') - (q, 0) := by
        rw [hgq]
        simp
      rw [e3]
      exact sub_mem hgTh (hsq q hq)
    have hcard : ((Fintype.card Fˣ : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hu' : ((Fintype.card Fˣ : ℕ) : C)⁻¹ * (Fintype.card Fˣ : C) = 1 := inv_mul_cancel₀ hcard
    have hvF : v ((Fintype.card F : ℕ) : C) < 1 := by
      obtain ⟨k, -, hk⟩ := FiniteField.card F p
      rw [hk, Nat.cast_pow, map_pow]
      exact pow_lt_one₀ zero_le' hp (PNat.ne_zero k)
    have hvU : v ((Fintype.card Fˣ : ℕ) : C) = 1 := by
      have e3 : ((Fintype.card Fˣ : ℕ) : C) = -(1 - ((Fintype.card F : ℕ) : C)) := by
        rw [Fintype.card_units, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
        ring
      rw [e3, Valuation.map_neg, Valuation.map_one_sub_of_lt v hvF]
    have hu : ((Fintype.card Fˣ : ℕ) : C)⁻¹ ∈ RC := (hRC _).2 (by rw [map_inv₀, hvU, inv_one])
    have hS : ∀ a, χ τ a ∈ (RC : Set C) := fun a => by
      rw [hχ]
      exact Subtype.prop _
    have hmul : ∀ a b, χ τ (a * b) = χ τ a * χ τ b := fun a b => by
      rw [hχ, hχ, hχ, map_mul]
      rfl
    have h1 : χ τ 1 = 1 := by
      rw [hχ, map_one]
      rfl
    have hav := avg_mem (D.Th τ) (RC : Set C) hstab (χ τ) hS hmul h1 _ hu hu' heq h m' hhTh
    let H' : (Fin n → F) → C := fun x =>
      ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • x)
    have hinv' : ∀ y, ∀ k ∈ stepSub F n ↑i, H' (y + k) = H' y := by
      intro y k hk
      have hk' : ∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → k j = 0 := hk
      show ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (y + k)) =
        ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • y)
      congr 1
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have hak : (a : F) • k ∈ stepSub F n ↑i := by
        show ∀ j : Fin n, (i : ℕ) ≤ (j : ℕ) → ((a : F) • k) j = 0
        intro j hj
        rw [Pi.smul_apply, hk' j hj, smul_zero]
      rw [smul_add, hhinv _ _ hak]
    have hsm' : ∀ (b : Fˣ) y, H' ((b : F) • y) = χ τ (b : F) * H' y := fun b y =>
      avg_smul (χ τ) hmul h1 _ h b y
    have h0' : H' 0 = 0 := by
      show ((Fintype.card Fˣ : ℕ) : C)⁻¹ * ∑ a : Fˣ, χ τ ((a⁻¹ : Fˣ) : F) * h ((a : F) • (0 : Fin n → F)) = 0
      simp [hh0]
    have hstep := eq_on_step i H' (χ τ) hχ0 hinv' hsm' h0'
    show m' ∈ AddSubgroup.map (AddMonoidHom.snd _ _) (D.stepGraph τ (χ τ) i)
    refine AddSubgroup.mem_map.2 ⟨(H' (Pi.single i 1), m'), ?_, rfl⟩
    show ((H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)), m') ∈
      D.Th τ ⊔ (vanSub C F n (↑i + 1)).toAddSubgroup.prod ⊥
    refine AddSubgroup.mem_sup.2 ⟨(H', m'), hav, ((H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)) - H', 0),
      AddSubgroup.mem_prod.2 ⟨?_, zero_mem _⟩, ?_⟩
    · refine (mem_vanSub _).2 (fun x hx => ?_)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hstep x hx, sub_self]
    · refine Prod.ext ?_ ?_
      · show H' + ((H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)) - H') =
          H' (Pi.single i 1) • fun y : Fin n → F => χ τ (y i)
        abel
      · show m' + 0 = m'
        rw [add_zero]

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderLatticeBaseStatement
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_lattice_base : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] [IsAlgClosed C] [CharZero C] (RC : Subalgebra o C) (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → ∀ (p : ℕ) [Fact p.Prime], v (p : C) < 1 → ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (φ : Equiv.Perm Sg), D.Base RC p w → ∀ AA : HopfOrder (C := C) RC (Fin n → F), AA.carrier.toAddSubgroup = D.M → FStable F AA.carrier → ∀ (σ : MulChar F RC), IsFund p σ → FlagConcl v p AA.carrier (Pi.basisFun F (Fin n)) σ → ∀ e : Sg → ℕ, (∀ τ a, χ τ a = ((σ ^ p ^ e τ) a : RC)) → (∀ τ, σ ^ p ^ e (φ τ) = σ ^ p ^ (e τ + 1)) → (∀ τ, (∀ g ∈ sqIdeal (augIdeal AA.carrier), (g, 0) ∈ D.Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ D.Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ D.Th τ) ∧ ∀ g ∈ eig AA.carrier (σ ^ p ^ e τ), (g, 0) ∈ D.Th τ → g ∈ sqIdeal (augIdeal AA.carrier)) → ∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk | exact GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnramifiedPrimeIdempotent
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.Gsplit
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Gsplit

theorem coprime_different (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ NumberField.discr E) :
    IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨a, b, hab⟩ := (hpz.irreducible.coprime_iff_not_dvd).mpr hd
  rw [Ideal.isCoprime_iff_exists]
  refine ⟨(a : 𝓞 E) * p, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _),
    (b : 𝓞 E) * (NumberField.discr E : 𝓞 E),
    Ideal.mul_mem_left _ _ (NumberField.discr_mem_differentIdeal E (𝓞 E)), ?_⟩
  have := congrArg (Int.cast : ℤ → 𝓞 E) hab
  push_cast at this
  exact this

theorem not_sq_dvd (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ NumberField.discr E) (w : Ideal (𝓞 E)) (hw : w ≠ ⊤) :
    ¬ w ^ 2 ∣ Ideal.span {(p : 𝓞 E)} := by
  intro h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hne : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hpz.ne_zero
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hdiff : w ^ (2 - 1) ∣ differentIdeal ℤ (𝓞 E) :=
    pow_sub_one_dvd_differentIdeal ℤ w 2 hne (by rw [hmap]; exact h)
  rw [show 2 - 1 = 1 from rfl, pow_one] at hdiff
  have hspan : w ∣ Ideal.span {(p : 𝓞 E)} := (dvd_pow_self w two_ne_zero).trans h
  exact hw (Ideal.isUnit_iff.mp
    ((PositivityTheory.HtPt.Gsplit.coprime_different E p hp hd).isUnit_of_dvd' hspan hdiff))

theorem glue_split : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (w : Ideal (𝓞 E)) [w.IsPrime], (p : 𝓞 E) ∈ w → ∃ ε : 𝓞 E, ε - 1 ∈ w ∧ (∀ w' : Ideal (𝓞 E), w'.IsPrime → (p : 𝓞 E) ∈ w' → w' ≠ w → ε ∈ w') ∧ (∀ a : 𝓞 E, (p : 𝓞 E) ∣ ε * a ↔ a ∈ w) ∧ (p : 𝓞 E) ∣ ε * ε - ε ∧ IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) := by
  intro E hEf hEn p hp hd w hw hpw
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hwtop : w ≠ ⊤ := hw.ne_top
  have hwbot : w ≠ ⊥ := fun h => hp0 (by rw [h] at hpw; exact Ideal.mem_bot.mp hpw)
  have hmax : w.IsMaximal := hw.isMaximal hwbot
  obtain ⟨J, hJ⟩ : w ∣ Ideal.span {(p : 𝓞 E)} := Ideal.dvd_span_singleton.mpr hpw
  have hJw : ¬ J ≤ w := by
    intro hle
    apply PositivityTheory.HtPt.Gsplit.not_sq_dvd E p hp hd w hwtop
    rw [hJ, pow_two]
    exact mul_dvd_mul_left w (Ideal.dvd_iff_le.mpr hle)
  have hsup : w ⊔ J = ⊤ := by
    by_contra hne
    apply hJw
    have heq : w ⊔ J = w := by
      by_contra h'
      exact hne (hmax.out.2 _ (lt_of_le_of_ne le_sup_left (Ne.symm h')))
    exact le_sup_right.trans heq.le
  have h1 : (1 : 𝓞 E) ∈ w ⊔ J := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨x, hx, ε, hε, hxε⟩ := Submodule.mem_sup.mp h1
  have hε1 : ε - 1 ∈ w := by
    have heq : ε - 1 = -x := by
      rw [← hxε]
      ring
    rw [heq]
    exact w.neg_mem hx
  have hεw : ε ∉ w := fun h => hwtop ((Ideal.eq_top_iff_one w).mpr (by
    have h2 := w.sub_mem h hε1
    simpa using h2))
  have hmemI : ∀ b, (p : 𝓞 E) ∣ b ↔ b ∈ w * J := by
    intro b
    rw [← Ideal.mem_span_singleton, hJ]
  refine ⟨ε, hε1, ?_, ?_, ?_, PositivityTheory.HtPt.Gsplit.coprime_different E p hp hd⟩
  · intro w' hw' hpw' hne
    have hle : w * J ≤ w' := by
      rw [← hJ, Ideal.span_singleton_le_iff_mem]
      exact hpw'
    rcases hw'.mul_le.mp hle with h | h
    · exact absurd (hmax.eq_of_le hw'.ne_top h).symm hne
    · exact h hε
  · intro a
    rw [hmemI]
    constructor
    · intro h
      have hle' : w * J ≤ w := Ideal.mul_le_left
      have hw1 : ε * a ∈ w := hle' h
      rcases hw.mem_or_mem hw1 with h' | h'
      · exact absurd h' hεw
      · exact h'
    · intro ha
      rw [mul_comm ε a]
      exact Ideal.mul_mem_mul ha hε
  · rw [hmemI]
    have heq : ε * ε - ε = (ε - 1) * ε := by ring
    rw [heq]
    exact Ideal.mul_mem_mul hε1 hε

end PositivityTheory.HtPt.Gsplit
end

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem unramified_prime_idempotent : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (w : Ideal (𝓞 E)) [w.IsPrime], (p : 𝓞 E) ∈ w → ∃ ε : 𝓞 E, ε - 1 ∈ w ∧ (∀ w' : Ideal (𝓞 E), w'.IsPrime → (p : 𝓞 E) ∈ w' → w' ≠ w → ε ∈ w') ∧ (∀ a : 𝓞 E, (p : 𝓞 E) ∣ ε * a ↔ a ∈ w) ∧ (p : 𝓞 E) ∣ ε * ε - ε ∧ IsCoprime (Ideal.span {(p : 𝓞 E)}) (differentIdeal ℤ (𝓞 E)) :=
  PositivityTheory.HtPt.Gsplit.glue_split

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PtAfTypeMain
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPtAfType
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace PositivityTheory.Xgn.A_pt_af_type

variable {o C : Type} [CommRing o] [Field C] [Algebra o C]

theorem mem_mul_std (RC : Subalgebra o C) (p : ℕ) {X : Type} (f : X → C) :
    f ∈ mulLat (p : C) (stdLat RC X) ↔ ∀ y, f y ∈ pInt (C := C) RC p := by
  constructor
  · rintro ⟨g, hg, rfl⟩ y
    have hy : g y ∈ RC := hg y (Set.mem_univ y)
    refine Submodule.mem_span_singleton.2 ⟨⟨g y, hy⟩, ?_⟩
    change g y * (p : C) = (p : C) * g y
    ring
  · intro h
    choose a ha using fun y => Submodule.mem_span_singleton.1 (h y)
    refine ⟨fun y => (a y : C), fun y _ => (a y).2, ?_⟩
    funext y
    rw [← ha y]
    change (p : C) * (a y : C) = (a y : C) * (p : C)
    ring

theorem pInt_mem (RC : Subalgebra o C) (p : ℕ) {c : C} (h : c ∈ pInt (C := C) RC p) : c ∈ RC := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 h
  change (a : C) * (p : C) ∈ RC
  exact RC.mul_mem a.2 (natCast_mem RC p)

theorem coe_mem_pInt (RC : Subalgebra o C) (p : ℕ) {c : RC} (h : c ∈ Ideal.span {(p : RC)}) :
    (c : C) ∈ pInt (C := C) RC p := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 h
  refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
  change (a : C) * (p : C) = _
  push_cast
  rfl

theorem mem_af (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}
    (D : LieLatticeData C F n Sg r s) (χ : F → C) (u : Fin n → C) :
    u ∈ D.af RC p χ ↔ ∃ g ∈ D.M, ∀ y : Fin n → F,
      (∑ k, u k * χ (y k)) - g y ∈ pInt (C := C) RC p := by
  have hl : ∀ y : Fin n → F, linMap n χ u y = ∑ k, u k * χ (y k) := by
    intro y
    simp [linMap, Fintype.linearCombination_apply, Finset.sum_apply]
  change linMap n χ u ∈ D.M ⊔ mulLat (p : C) (stdLat RC _) ↔ _
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨g, hg, f, hf, h⟩
    refine ⟨g, hg, fun y => ?_⟩
    have := (mem_mul_std RC p f).1 hf y
    rw [← hl, ← h]
    simpa using this
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, linMap n χ u - g, (mem_mul_std RC p _).2 fun y => ?_, by abel⟩
    rw [Pi.sub_apply, hl]
    exact h y

theorem mem_dotDual (RC : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C)) (u : Fin m → C) :
    u ∈ dotDual RC L ↔ ∀ l ∈ L, l ⬝ᵥ u ∈ RC := by
  simp only [dotDual, AddSubgroup.mem_iInf]
  rfl

theorem congr_lin (RC : Subalgebra o C) (p : ℕ) {I : Type} [Fintype I] {n : ℕ}
    (Pm : Matrix (Fin n) I RC) (a : I → RC) (b : Fin n → RC)
    (h : ∀ k, (∑ j, Pm k j * a j) - b k ∈ Ideal.span {(p : RC)}) (l : Fin n → RC) :
    algebraMap RC C (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, (l k : C) * (b k : C)
      ∈ pInt (C := C) RC p := by
  have h1 : ∑ k, l k * ((∑ j, Pm k j * a j) - b k) ∈ Ideal.span {(p : RC)} :=
    Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h k)
  have h2 : ∑ k, l k * ((∑ j, Pm k j * a j) - b k)
      = (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k := by
    simp only [mul_sub, Finset.sum_sub_distrib, Matrix.vecMul, dotProduct, Finset.sum_mul,
      Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  rw [h2] at h1
  have h3 := coe_mem_pInt RC p h1
  have h4 : (((∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k : RC) : C)
      = algebraMap RC C (∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, (l k : C) * (b k : C) := by
    change algebraMap RC C ((∑ j, Matrix.vecMul l Pm j * a j) - ∑ k, l k * b k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum (algebraMap RC C) (fun k => l k * b k)]
    simp only [map_mul]
    rfl
  rwa [h4] at h3

theorem dot_eq (RC : Subalgebra o C) {I : Type} [Fintype I] {n : ℕ}
    (J : Matrix I (Fin n) RC) (l : I → RC) (u : Fin n → C) :
    (∑ j, (l j : C) * (J.map (algebraMap RC C)).mulVec u j)
      = (fun k => ((Matrix.vecMul l J k : RC) : C)) ⬝ᵥ u := by
  have h : ∀ k, ((Matrix.vecMul l J k : RC) : C) = ∑ j, (l j : C) * algebraMap RC C (J j k) := by
    intro k
    change algebraMap RC C (∑ j, l j * J j k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul]
    rfl
  simp only [h, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  rw [Finset.sum_comm]

end PositivityTheory.Xgn.A_pt_af_type

open PositivityTheory.Xgn.A_pt_af_type in
theorem PositivityTheory.Xgn.t_pt_af_type : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (MM : Submodule RC ((I → ZMod p) → C)), MM ≤ intFun RC _ → ∀ {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (χ : F → RC), χ 0 = 0 → χ 1 = 1 → ∀ (i : (Fin n → F) →+ (I → ZMod p)) (π : (I → ZMod p) →+ (Fin n → F)), (∀ y, π (i y) = y) → (∀ h ∈ MM, (fun x => h (i (π x))) ∈ MM) → (MM.map (LinearMap.funLeft RC C (i : (Fin n → F) → (I → ZMod p)))).toAddSubgroup = D.M → ∀ (Pm : Matrix (Fin n) I RC) (J : Matrix I (Fin n) RC), Pm * J = 1 → (∀ (k : Fin n) (x : I → ZMod p), (∑ j, Pm k j * ((x j).val : RC)) - χ (π x k) ∈ Ideal.span {(p : RC)}) → (∀ l ∈ afLat p MM, Matrix.vecMul l (J * Pm) ∈ afLat p MM) → (∀ l : Fin n → RC, (fun k => (l k : C)) ∈ D.af RC p (fun a => (χ a : C)) ↔ Matrix.vecMul l Pm ∈ afLat p MM) ∧ ∀ u : Fin n → C, u ∈ D.hh RC p (fun a => (χ a : C)) ↔ ∀ l ∈ afLat p MM, (∑ j, (l j : C) * (J.map (algebraMap RC C)).mulVec u j) ∈ RC := by
  intro o C _ _ _ RC p _ I _ _ MM hint F _ _ n Sg r s D χ h0 h1 i π hπ hst hM Pm J hPJ hc hAF
  have hMM : ∀ g, g ∈ D.M ↔ ∃ h ∈ MM, (fun y => h (i y)) = g := by
    intro g
    rw [← hM]
    exact Submodule.mem_map
  have P1 : ∀ l : Fin n → RC, (fun k => (l k : C)) ∈ D.af RC p (fun a => (χ a : C)) ↔
      Matrix.vecMul l Pm ∈ afLat p MM := by
    intro l
    rw [mem_af]
    constructor
    · rintro ⟨g, hg, h⟩
      obtain ⟨h', hh', rfl⟩ := (hMM g).1 hg
      refine ⟨_, hst h' hh', fun x => ?_⟩
      have e1 := congr_lin RC p Pm (fun j => ((x j).val : RC)) (fun k => χ (π x k))
        (fun k => hc k x) l
      have e2 := h (π x)
      have e3 := Submodule.neg_mem _ (Submodule.add_mem _ e1 e2)
      convert e3 using 1
      ring
    · rintro ⟨g, hg, h⟩
      refine ⟨_, (hMM _).2 ⟨g, hg, rfl⟩, fun y => ?_⟩
      have e1 := congr_lin RC p Pm (fun j => ((i y j).val : RC)) (fun k => χ (π (i y) k))
        (fun k => hc k (i y)) l
      rw [hπ] at e1
      have e2 := h (i y)
      have e3 := Submodule.neg_mem _ (Submodule.add_mem _ e1 e2)
      convert e3 using 1
      ring
  have hco : ∀ u ∈ D.af RC p (fun a => (χ a : C)), ∀ k, u k ∈ RC := by
    intro u hu k
    obtain ⟨g, hg, h⟩ := (mem_af RC p D _ u).1 hu
    obtain ⟨h', hh', rfl⟩ := (hMM g).1 hg
    have e1 := pInt_mem RC p (h (Pi.single k 1))
    have e2 : ∑ j, u j * ((χ ((Pi.single k 1 : Fin n → F) j) : RC) : C) = u k := by
      rw [Finset.sum_eq_single k]
      · simp [h1]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj, h0]
      · simp
    rw [e2] at e1
    have e3 : h' (i (Pi.single k 1)) ∈ RC := by
      have := hint hh'
      obtain ⟨a, ha⟩ := this (i (Pi.single k 1))
      rw [← ha]
      exact a.2
    simpa using RC.add_mem e1 e3
  refine ⟨P1, fun u => ?_⟩
  rw [LieLatticeData.hh, mem_dotDual]
  constructor
  · intro h l hl
    rw [dot_eq]
    refine h _ ((P1 _).2 ?_)
    rw [Matrix.vecMul_vecMul]
    exact hAF l hl
  · intro h l hl
    let l' : Fin n → RC := fun k => ⟨l k, hco l hl k⟩
    have e := h _ ((P1 l').1 hl)
    rw [dot_eq, Matrix.vecMul_vecMul, hPJ, Matrix.vecMul_one] at e
    exact e
end

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem pt_af_type_main : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) [Fact p.Prime] {I : Type} [Fintype I] [DecidableEq I] (MM : Submodule RC ((I → ZMod p) → C)), MM ≤ intFun RC _ → ∀ {F : Type} [Field F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (χ : F → RC), χ 0 = 0 → χ 1 = 1 → ∀ (i : (Fin n → F) →+ (I → ZMod p)) (π : (I → ZMod p) →+ (Fin n → F)), (∀ y, π (i y) = y) → (∀ h ∈ MM, (fun x => h (i (π x))) ∈ MM) → (MM.map (LinearMap.funLeft RC C (i : (Fin n → F) → (I → ZMod p)))).toAddSubgroup = D.M → ∀ (Pm : Matrix (Fin n) I RC) (J : Matrix I (Fin n) RC), Pm * J = 1 → (∀ (k : Fin n) (x : I → ZMod p), (∑ j, Pm k j * ((x j).val : RC)) - χ (π x k) ∈ Ideal.span {(p : RC)}) → (∀ l ∈ afLat p MM, Matrix.vecMul l (J * Pm) ∈ afLat p MM) → (∀ l : Fin n → RC, (fun k => (l k : C)) ∈ D.af RC p (fun a => (χ a : C)) ↔ Matrix.vecMul l Pm ∈ afLat p MM) ∧ ∀ u : Fin n → C, u ∈ D.hh RC p (fun a => (χ a : C)) ↔ ∀ l ∈ afLat p MM, (∑ j, (l j : C) * (J.map (algebraMap RC C)).mulVec u j) ∈ RC :=
  @PositivityTheory.Xgn.t_pt_af_type

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactStandardLattice
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.Gamdel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Gamdel

theorem mem_mulLat_iff {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {w : Ω} (hw : w ≠ 0)
    (L : AddSubgroup V) (v : V) : v ∈ mulLat w L ↔ w⁻¹ • v ∈ L := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.mulLat
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨u, hu, huv⟩
    rw [← huv]
    simpa [inv_smul_smul₀ hw] using hu
  · intro h
    exact ⟨w⁻¹ • v, h, by simp [smul_inv_smul₀ hw]⟩

theorem smul_mem_stdLat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    (ι : Type) {a : Ω} (ha : a ∈ R) {v : ι → Ω} (hv : v ∈ stdLat R ι) : a • v ∈ stdLat R ι := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.stdLat at hv ⊢
  rw [AddSubgroup.mem_pi] at hv ⊢
  intro j hj
  have hvj : v j ∈ R := by simpa using hv j hj
  simpa [smul_eq_mul] using R.mul_mem ha hvj

def graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V') (f : V →ₗ[Ω] V') :
    AddSubgroup (V × V') where
  carrier := {p | w • p.1 ∈ A ∧ p.2 - f p.1 ∈ B}
  zero_mem' := by
    refine ⟨by simp, by simp⟩
  add_mem' := by
    rintro p q ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · have := A.add_mem h1 h3
      simpa [smul_add] using this
    · have := B.add_mem h2 h4
      convert this using 1
      simp only [Prod.snd_add, Prod.fst_add, map_add (f := _)]
      abel
  neg_mem' := by
    rintro p ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := A.neg_mem h1
      simpa [smul_neg] using this
    · have := B.neg_mem h2
      convert this using 1
      simp only [Prod.snd_neg, Prod.fst_neg, map_neg]
      abel

theorem mem_graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V') (f : V →ₗ[Ω] V') (a : V)
    (b : V') : (a, b) ∈ graphLat w A B f ↔ w • a ∈ A ∧ b - f a ∈ B := Iff.rfl

theorem smul_mem_graphLat {Ω V V' : Type} [Field Ω] [AddCommGroup V] [Module Ω V]
    [AddCommGroup V'] [Module Ω V'] (w : Ω) (A : AddSubgroup V) (B : AddSubgroup V')
    (f : V →ₗ[Ω] V') (a : Ω) (hA : ∀ v ∈ A, a • v ∈ A) (hB : ∀ v ∈ B, a • v ∈ B)
    (v : V × V') (hv : v ∈ graphLat w A B f) : a • v ∈ graphLat w A B f := by
  have hv' := (PositivityTheory.HtPt.Gamdel.mem_graphLat w A B f v.1 v.2).1 hv
  refine (PositivityTheory.HtPt.Gamdel.mem_graphLat w A B f (a • v).1 (a • v).2).2 ⟨?_, ?_⟩
  · rw [Prod.smul_fst, smul_smul, mul_comm, ← smul_smul]
    exact hA _ hv'.1
  · rw [Prod.smul_snd, Prod.smul_fst, map_smul, ← smul_sub]
    exact hB _ hv'.2

theorem glue_gamdel : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω), w ∈ R → w ≠ 0 → ∀ (r s n : ℕ) (W : AddSubgroup (Fin r → Ω)) (om : AddSubgroup (Fin s → Ω)), (∀ a ∈ R, ∀ v ∈ W, a • v ∈ W) → (∀ a ∈ R, ∀ v ∈ om, a • v ∈ om) → ∀ (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)), (∀ a ∈ W, i a ∈ stdLat R (Fin n)) → (∀ b ∈ stdLat R (Fin n), q b ∈ om) → (∀ a ∈ W, i a ∈ mulLat w (stdLat R (Fin n)) → a ∈ mulLat w W) → (∀ b ∈ stdLat R (Fin n), q b ∈ mulLat w om ↔ ∃ a ∈ W, b - i a ∈ mulLat w (stdLat R (Fin n))) → (∀ c ∈ om, ∃ b ∈ stdLat R (Fin n), c - q b ∈ mulLat w om) → ∃ (Gam : AddSubgroup ((Fin r → Ω) × (Fin n → Ω))) (Del : AddSubgroup ((Fin n → Ω) × (Fin s → Ω))), (∀ a b, (a, b) ∈ Gam ↔ w • a ∈ W ∧ b - i a ∈ stdLat R (Fin n)) ∧ (∀ b c, (b, c) ∈ Del ↔ w • b ∈ stdLat R (Fin n) ∧ c - q b ∈ om) ∧ (∀ a ∈ R, (∀ v ∈ Gam, a • v ∈ Gam) ∧ ∀ v ∈ Del, a • v ∈ Del) ∧ ((∀ a, (∃ b, (a, b) ∈ Gam) ↔ w • a ∈ W) ∧ (∀ b, (0, b) ∈ Gam ↔ b ∈ stdLat R (Fin n)) ∧ ∀ a, (a, 0) ∈ Gam ↔ a ∈ W) ∧ ((∀ b, (∃ c, (b, c) ∈ Del) ↔ w • b ∈ stdLat R (Fin n)) ∧ (∀ c, (∃ b, (b, c) ∈ Del) ↔ w • c ∈ om) ∧ (∀ c, (0, c) ∈ Del ↔ c ∈ om) ∧ ∀ b, (b, 0) ∈ Del ↔ ∃ a, (a, b) ∈ Gam) := by
  intro o Ω _ _ _ R w hwR hw r s n W om hW hom i q hiW hqS hexW hexS hsurj
  have hS : ∀ a ∈ R, ∀ v ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n),
      a • v ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n) :=
    fun a ha v hv => PositivityTheory.HtPt.Gamdel.smul_mem_stdLat R (Fin n) ha hv
  have hmem := fun {V : Type} [AddCommGroup V] [Module Ω V] (L : AddSubgroup V) (x : V) =>
    PositivityTheory.HtPt.Gamdel.mem_mulLat_iff hw L x
  refine ⟨PositivityTheory.HtPt.Gamdel.graphLat w W (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) i,
    PositivityTheory.HtPt.Gamdel.graphLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) om q,
    fun a b => PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _, fun b c => PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _,
    fun a ha => ⟨PositivityTheory.HtPt.Gamdel.smul_mem_graphLat _ _ _ _ a (hW a ha) (hS a ha),
      PositivityTheory.HtPt.Gamdel.smul_mem_graphLat _ _ _ _ a (hS a ha) (hom a ha)⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a
    constructor
    · rintro ⟨b, hb⟩
      exact ((PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).1 hb).1
    · intro ha
      refine ⟨i a, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨ha, ?_⟩⟩
      rw [sub_self]
      exact AddSubgroup.zero_mem _
  · intro b
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, smul_zero, map_zero, sub_zero]
    exact ⟨fun h => h.2, fun h => ⟨W.zero_mem, h⟩⟩
  · intro a
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, zero_sub, neg_mem_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : i (w • a) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) := by
        rw [hmem, map_smul, inv_smul_smul₀ hw]
        exact h2
      have h4 := hexW _ h1 h3
      rwa [hmem, inv_smul_smul₀ hw] at h4
    · intro ha
      exact ⟨hW w hwR a ha, hiW a ha⟩
  · intro b
    constructor
    · rintro ⟨c, hc⟩
      exact ((PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).1 hc).1
    · intro hb
      refine ⟨q b, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨hb, ?_⟩⟩
      rw [sub_self]
      exact AddSubgroup.zero_mem _
  · intro c
    constructor
    · rintro ⟨b, hb⟩
      rw [PositivityTheory.HtPt.Gamdel.mem_graphLat] at hb
      have h1 := hom w hwR _ hb.2
      have h2 := hqS _ hb.1
      have hc : w • c = w • (c - q b) + q (w • b) := by
        rw [map_smul, smul_sub, sub_add_cancel]
      rw [hc]
      exact om.add_mem h1 h2
    · intro hc
      obtain ⟨b0, hb0, h⟩ := hsurj _ hc
      rw [hmem, smul_sub, inv_smul_smul₀ hw] at h
      refine ⟨w⁻¹ • b0, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨?_, ?_⟩⟩
      · rwa [smul_inv_smul₀ hw]
      · rwa [map_smul]
  · intro c
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, smul_zero, map_zero, sub_zero]
    exact ⟨fun h => h.2, fun h => ⟨AddSubgroup.zero_mem _, h⟩⟩
  · intro b
    rw [PositivityTheory.HtPt.Gamdel.mem_graphLat, zero_sub, neg_mem_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : q (w • b) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w om := by
        rw [hmem, map_smul, inv_smul_smul₀ hw]
        exact h2
      obtain ⟨a0, ha0, h4⟩ := (hexS _ h1).1 h3
      rw [hmem, smul_sub, inv_smul_smul₀ hw] at h4
      refine ⟨w⁻¹ • a0, (PositivityTheory.HtPt.Gamdel.mem_graphLat _ _ _ _ _ _).2 ⟨?_, ?_⟩⟩
      · rwa [smul_inv_smul₀ hw]
      · rwa [map_smul]
    · rintro ⟨a, ha⟩
      rw [PositivityTheory.HtPt.Gamdel.mem_graphLat] at ha
      obtain ⟨h1, h2⟩ := ha
      have hwb : w • b ∈ GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n) := by
        have e : w • b = w • (b - i a) + i (w • a) := by
          rw [map_smul, smul_sub, sub_add_cancel]
        rw [e]
        exact AddSubgroup.add_mem _ (hS w hwR _ h2) (hiW _ h1)
      refine ⟨hwb, ?_⟩
      have h3 : w • b - i (w • a) ∈ GlobalTheory.CompanionTheory.Ar.Num.mulLat w (GlobalTheory.CompanionTheory.Ar.Num.stdLat R (Fin n)) := by
        rw [hmem, map_smul, ← smul_sub, inv_smul_smul₀ hw]
        exact h2
      have h4 := (hexS _ hwb).2 ⟨w • a, h1, h3⟩
      rwa [hmem, map_smul, inv_smul_smul₀ hw] at h4

end PositivityTheory.HtPt.Gamdel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactStandardLattice
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem glue_gamdel_graphs : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω), w ∈ R → w ≠ 0 → ∀ (r s n : ℕ) (W : AddSubgroup (Fin r → Ω)) (om : AddSubgroup (Fin s → Ω)), (∀ a ∈ R, ∀ v ∈ W, a • v ∈ W) → (∀ a ∈ R, ∀ v ∈ om, a • v ∈ om) → ∀ (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)), (∀ a ∈ W, i a ∈ stdLat R (Fin n)) → (∀ b ∈ stdLat R (Fin n), q b ∈ om) → (∀ a ∈ W, i a ∈ mulLat w (stdLat R (Fin n)) → a ∈ mulLat w W) → (∀ b ∈ stdLat R (Fin n), q b ∈ mulLat w om ↔ ∃ a ∈ W, b - i a ∈ mulLat w (stdLat R (Fin n))) → (∀ c ∈ om, ∃ b ∈ stdLat R (Fin n), c - q b ∈ mulLat w om) → ∃ (Gam : AddSubgroup ((Fin r → Ω) × (Fin n → Ω))) (Del : AddSubgroup ((Fin n → Ω) × (Fin s → Ω))), (∀ a b, (a, b) ∈ Gam ↔ w • a ∈ W ∧ b - i a ∈ stdLat R (Fin n)) ∧ (∀ b c, (b, c) ∈ Del ↔ w • b ∈ stdLat R (Fin n) ∧ c - q b ∈ om) ∧ (∀ a ∈ R, (∀ v ∈ Gam, a • v ∈ Gam) ∧ ∀ v ∈ Del, a • v ∈ Del) ∧ ((∀ a, (∃ b, (a, b) ∈ Gam) ↔ w • a ∈ W) ∧ (∀ b, (0, b) ∈ Gam ↔ b ∈ stdLat R (Fin n)) ∧ ∀ a, (a, 0) ∈ Gam ↔ a ∈ W) ∧ ((∀ b, (∃ c, (b, c) ∈ Del) ↔ w • b ∈ stdLat R (Fin n)) ∧ (∀ c, (∃ b, (b, c) ∈ Del) ↔ w • c ∈ om) ∧ (∀ c, (0, c) ∈ Del ↔ c ∈ om) ∧ ∀ b, (b, 0) ∈ Del ↔ ∃ a, (a, b) ∈ Gam) :=
  PositivityTheory.HtPt.Gamdel.glue_gamdel

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactStandardLatticeStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_exact_standard_lattice : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω), w ∈ R → w ≠ 0 → ∀ (r s n : ℕ) (W : AddSubgroup (Fin r → Ω)) (om : AddSubgroup (Fin s → Ω)), (∀ a ∈ R, ∀ v ∈ W, a • v ∈ W) → (∀ a ∈ R, ∀ v ∈ om, a • v ∈ om) → ∀ (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)), (∀ a ∈ W, i a ∈ stdLat R (Fin n)) → (∀ b ∈ stdLat R (Fin n), q b ∈ om) → (∀ a ∈ W, i a ∈ mulLat w (stdLat R (Fin n)) → a ∈ mulLat w W) → (∀ b ∈ stdLat R (Fin n), q b ∈ mulLat w om ↔ ∃ a ∈ W, b - i a ∈ mulLat w (stdLat R (Fin n))) → (∀ c ∈ om, ∃ b ∈ stdLat R (Fin n), c - q b ∈ mulLat w om) → ∃ (Gam : AddSubgroup ((Fin r → Ω) × (Fin n → Ω))) (Del : AddSubgroup ((Fin n → Ω) × (Fin s → Ω))), (∀ a b, (a, b) ∈ Gam ↔ w • a ∈ W ∧ b - i a ∈ stdLat R (Fin n)) ∧ (∀ b c, (b, c) ∈ Del ↔ w • b ∈ stdLat R (Fin n) ∧ c - q b ∈ om) ∧ (∀ a ∈ R, (∀ v ∈ Gam, a • v ∈ Gam) ∧ ∀ v ∈ Del, a • v ∈ Del) ∧ ((∀ a, (∃ b, (a, b) ∈ Gam) ↔ w • a ∈ W) ∧ (∀ b, (0, b) ∈ Gam ↔ b ∈ stdLat R (Fin n)) ∧ ∀ a, (a, 0) ∈ Gam ↔ a ∈ W) ∧ ((∀ b, (∃ c, (b, c) ∈ Del) ↔ w • b ∈ stdLat R (Fin n)) ∧ (∀ c, (∃ b, (b, c) ∈ Del) ↔ w • c ∈ om) ∧ (∀ c, (0, c) ∈ Del ↔ c ∈ om) ∧ ∀ b, (b, 0) ∈ Del ↔ ∃ a, (a, b) ∈ Gam) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.glue_gamdel_graphs | exact GlobalTheory.CompanionTheory.Ar.Num.glue_gamdel_graphs | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.glue_gamdel_graphs <;> assumption)
end
end
