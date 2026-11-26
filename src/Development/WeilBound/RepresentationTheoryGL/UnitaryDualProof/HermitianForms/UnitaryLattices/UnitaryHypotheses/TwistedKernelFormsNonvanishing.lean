module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.UnipBLeColFixOne
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.QIterSurjective

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.AtomEqZero
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.IsLatticeStandardLattice
noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lat


variable (k) in
def lat0 (m : ℕ) : AddSubgroup (Fin (m + 1) → k) where
  carrier := {x | ∀ i, valuation k (x i) ≤ valuation k ((1 : kˣ) : k)}
  add_mem' := fun {a b} ha hb i => by
    show valuation k (a i + b i) ≤ _
    exact ((valuation k).map_add _ _).trans (max_le (ha i) (hb i))
  zero_mem' := fun i => by simp
  neg_mem' := fun {a} ha i => by
    show valuation k (-(a i)) ≤ _
    rw [Valuation.map_neg]
    exact ha i

theorem coe_standard_lattice (m : ℕ) : (lat0 k m : Set (Fin (m + 1) → k)) = Set.univ.pi fun _ => cball (1 : kˣ) := by
  ext x
  simp only [Set.mem_univ_pi, cball, Set.mem_setOf_eq]
  exact Iff.rfl

theorem isLattice_standard_lattice (m : ℕ) : IsLat (lat0 k m) := by
  unfold IsLat
  rw [coe_standard_lattice]
  exact ⟨isCompact_univ_pi fun _ => isCompact_cball _, isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball _⟩

theorem isLat_sup {m : ℕ} {A₁ A₂ : AddSubgroup (Fin (m + 1) → k)} (h1 : IsLat A₁) (h2 : IsLat A₂) :
    IsLat (A₁ ⊔ A₂) := by
  unfold IsLat at *
  rw [AddSubgroup.add_normal]
  exact ⟨h1.1.add h2.1, h2.2.add_left⟩

end Lat

section Transport

variable {ψ : AddChar k Circle} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}

theorem kills_congr {a b : ℕ} (hab : a = b) {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (h : Kills ψ π a B) : Kills ψ π b B := by
  subst hab; exact h

theorem mirEq_congr {a b : ℕ} (hab : a = b) {ha : a + 1 ≤ N} {hb : b + 1 ≤ N} {s t : ℝ} (hst : s = t)
    {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (h : MirEq π a ha s B) : MirEq π b hb t B := by
  subst hab; subst hst; exact h

theorem lvl_congr {a b : ℕ} (hab : a = b) {ha : a + 2 ≤ N} {hb : b + 2 ≤ N} {s t : ℝ} (hst : s = t)
    {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (h : Lvl k ψ π a ha s B) : Lvl k ψ π b hb t B := by
  subst hab; subst hst; exact h

theorem isDens_smul {m : ℕ} {h : m + 2 ≤ N} {A₀ : AddSubgroup (Fin (m + 1) → k)} {B B' I C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}
    (hB : IsDens ψ h π A₀ B B') (hI : IsDens ψ h π A₀ I C) (c : ℂ) (hIc : ∀ v w, I v w = c * B v w) :
    ∀ v w, C v w = c * B' v w := by
  intro v w
  obtain ⟨A₁, hA₁, -, hB1⟩ := hB v w
  obtain ⟨A₂, hA₂, -, hI2⟩ := hI v w
  have hL := isLat_sup hA₁ hA₂
  rw [hI2 _ hL le_sup_right, hB1 _ hL le_sup_left, hIc]
  ring

end Transport

section Chain


open Classical in
def chain (hUD : UDens k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : ℕ → (V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  | 0 => B
  | d + 1 =>
    if h : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) then
      Classical.choose (hUD ψ hψc hψ1 (N - 2 - d) N (by obtain ⟨hN, -⟩ := h; omega) V π hs (d : ℝ)
        (chain hUD hψc hψ1 π hs B d) h.2
        (lat0 k (N - 2 - d)) (isLattice_standard_lattice _))
    else 0

variable (hUD : UDens k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ} {V : Type}
  [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

theorem chain_zero : chain hUD hψc hψ1 π hs B 0 = B := rfl

theorem chain_succ (d : ℕ) (hN : d + 2 ≤ N)
    (hL : Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d)) :
    IsDens ψ (by omega : N - 2 - d + 2 ≤ N) π (lat0 k (N - 2 - d)) (chain hUD hψc hψ1 π hs B d)
        (chain hUD hψc hψ1 π hs B (d + 1)) ∧
      IsPsd (chain hUD hψc hψ1 π hs B (d + 1)) ∧ Kills ψ π (N - 2 - d + 1) (chain hUD hψc hψ1 π hs B (d + 1)) ∧
      MirEq π (N - 2 - d) (by omega) ((d : ℝ) + 1) (chain hUD hψc hψ1 π hs B (d + 1)) ∧
      (∀ v, chain hUD hψc hψ1 π hs B (d + 1) v v = 0 →
        v ∈ twKer π (derUnip k N (N - 2 - d + 1)) (lvlChar k ψ N (N - 2 - d + 1)) ⊔
          LinearMap.ker (chain hUD hψc hψ1 π hs B d)) := by
  have hh : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) := ⟨hN, hL⟩
  simp only [chain, dif_pos hh]
  exact Classical.choose_spec (hUD ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ)
    (chain hUD hψc hψ1 π hs B d) hL (lat0 k (N - 2 - d)) (isLattice_standard_lattice _))

theorem isPsd_of_inv (hB : IsInvForm π B) : IsPsd B := by
  obtain ⟨h1, h2, -⟩ := hB
  unfold IsPsd
  refine ⟨h1, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · exact (h2 v hv).le

theorem chain_lvl (hB : IsInvForm π B) :
    ∀ d (hd : d + 2 ≤ N), Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) := by
  intro d
  induction d with
  | zero =>
    intro hd
    refine ⟨isPsd_of_inv π B hB, ?_, ?_⟩
    · refine kills_congr (a := N) (by omega) ?_
      intro v hv w
      rw [twKer_derUnip_self ψ π] at hv
      rw [(Submodule.mem_bot ℂ).1 hv]
      simp
    · intro p _ v w
      simp [chain_zero, hB.2.2]
  | succ d ih =>
    intro hd
    obtain ⟨-, h2, h3, h4, -⟩ := chain_succ hUD hψc hψ1 π hs B d (by omega) (ih (by omega))
    exact ⟨h2, kills_congr (by omega) h3, mirEq_congr (by omega) (by push_cast; ring) h4⟩

end Chain

end PositivityTheory.RgUd.Form.U.Asm
end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blkAt_self (N : ℕ) (h : N ≤ N) (g : GL (Fin N) k) : blkAt k N N h g = g := by
  ext a b
  rw [blkAt_apply]
  simp [a.2, b.2]


open Classical in
def atom (hUD : UDens k) (hUA : UAtom k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (d : ℕ) : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ :=
  if h : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) then
    Classical.choose (hUA ψ hψc hψ1 (N - 2 - d) N (by obtain ⟨hN, -⟩ := h; omega) V π hs (d : ℝ)
      (chain hUD hψc hψ1 π hs B d) h.2)
  else 0

variable (hUD : UDens k) (hUA : UAtom k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
  (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

theorem atom_spec (d : ℕ) (hN : d + 2 ≤ N)
    (hL : Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d)) :
    IsAtom (by omega : N - 2 - d + 2 ≤ N) π (chain hUD hψc hψ1 π hs B d) (atom hUD hUA hψc hψ1 π hs B d) ∧
      IsPsd (atom hUD hUA hψc hψ1 π hs B d) ∧
      (∀ v, (atom hUD hUA hψc hψ1 π hs B d v v).re ≤ (chain hUD hψc hψ1 π hs B d v v).re) ∧
      (∀ v ∈ DerKer k ψ π (N - 2 - d), ∀ w, atom hUD hUA hψc hψ1 π hs B d v w = 0) ∧
      GLEq k π (N - 2 - d) (by omega) (d : ℝ) (atom hUD hUA hψc hψ1 π hs B d) ∧
      MirEq π (N - 2 - d + 1) (by omega) (d : ℝ) (atom hUD hUA hψc hψ1 π hs B d) := by
  have hh : ∃ hN : d + 2 ≤ N, Lvl k ψ π (N - 2 - d) (by omega) (d : ℝ) (chain hUD hψc hψ1 π hs B d) := ⟨hN, hL⟩
  have e : atom hUD hUA hψc hψ1 π hs B d = Classical.choose (hUA ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ)
      (chain hUD hψc hψ1 π hs B d) hL) := by
    rw [atom, dite_eq_left hh]
  rw [e]
  exact Classical.choose_spec (hUA ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ) (chain hUD hψc hψ1 π hs B d) hL)

theorem lift (hUL : ULift k) (hTB : ThmB k) (hirr : π.IsIrreducible) (hB : IsInvForm π B) :
    ∀ d (hd : d + 1 ≤ N) (C : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ), IsPsd C → Kills ψ π (N - d) C →
      MirEq π (N - d - 1) (by omega) (d : ℝ) C →
      (∀ v, (C v v).re ≤ (chain hUD hψc hψ1 π hs B d v v).re) →
      ∃ c : ℂ, ∀ v w, C v w = c * chain hUD hψc hψ1 π hs B d v w := by
  have level : ∀ j (hj : j + 2 ≤ N),
      Lvl k ψ π (N - 2 - j) (by omega) (j : ℝ) (chain hUD hψc hψ1 π hs B j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [chain_zero]
      refine ⟨isPsd_of_inv π B hB, kills_congr (a := N) (by omega) ?_, ?_⟩
      · intro v hv w
        rw [twKer_derUnip_self ψ π] at hv
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
      · intro p _ v w
        simp [hB.2.2]
    | succ j ih =>
      intro hj
      obtain ⟨-, hP, hK, hM, -⟩ := chain_succ hUD hψc hψ1 π hs B j (by omega) (ih (by omega))
      exact ⟨hP, kills_congr (by omega) hK, mirEq_congr (by omega) (by push_cast; ring) hM⟩
  intro d
  induction d with
  | zero =>
    intro hd C _ _ hC3 _
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    have hM : MirEq π n (by omega) ((0 : ℕ) : ℝ) C := mirEq_congr (by omega) rfl hC3
    rw [chain_zero]
    refine hTB n V π hs hirr B hB C fun p hp v w => ?_
    have := hM p hp v w
    rw [blkAt_self] at this
    simpa using this
  | succ d ih =>
    intro _hd C hC1 hC2 hC3 hC4
    have hL := level d (by omega)
    obtain ⟨hD, -⟩ := chain_succ hUD hψc hψ1 π hs B d (by omega) hL
    obtain ⟨I, hIL, hIle, hID, -⟩ := hUL ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ)
      (chain hUD hψc hψ1 π hs B d) (chain hUD hψc hψ1 π hs B (d + 1)) C (lat0 k (N - 2 - d)) hL (isLattice_standard_lattice _) hD hC1
      (kills_congr (by omega) hC2) (mirEq_congr (by omega) (by push_cast; ring) hC3) hC4
    obtain ⟨c, hc⟩ := ih (by omega) I hIL.1 (kills_congr (by omega) hIL.2.1)
      (mirEq_congr (by omega) rfl hIL.2.2) hIle
    exact ⟨c, isDens_smul hD hID c hc⟩

theorem chain_rad (hB : IsInvForm π B) (d : ℕ) (hd : d + 1 ≤ N) :
    ∀ v, chain hUD hψc hψ1 π hs B d v v = 0 →
      v ∈ twKer π (derUnip k N (N - d)) (lvlChar k ψ N (N - d)) := by
  revert d
  have level : ∀ j (hj : j + 2 ≤ N),
      Lvl k ψ π (N - 2 - j) (by omega) (j : ℝ) (chain hUD hψc hψ1 π hs B j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [chain_zero]
      refine ⟨isPsd_of_inv π B hB, kills_congr (a := N) (by omega) ?_, ?_⟩
      · intro v hv w
        rw [twKer_derUnip_self ψ π] at hv
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
      · intro p _ v w
        simp [hB.2.2]
    | succ j ih =>
      intro hj
      obtain ⟨-, hP, hK, hM, -⟩ := chain_succ hUD hψc hψ1 π hs B j (by omega) (ih (by omega))
      exact ⟨hP, kills_congr (by omega) hK, mirEq_congr (by omega) (by push_cast; ring) hM⟩
  intro d
  induction d with
  | zero =>
    intro _ v hv
    have : v = 0 := by
      by_contra hne
      have := hB.2.1 v hne
      rw [chain_zero] at hv
      rw [hv] at this
      simp at this
    rw [this]
    exact zero_mem _
  | succ d ih =>
    intro hd v hv
    have hL := level d (by omega)
    obtain ⟨-, -, -, -, hR⟩ := chain_succ hUD hψc hψ1 π hs B d (by omega) hL
    have hmem := hR v hv
    have e : N - 2 - d + 1 = N - (d + 1) := by omega
    rw [e] at hmem
    suffices hle : LinearMap.ker (chain hUD hψc hψ1 π hs B d) ≤
        twKer π (derUnip k N (N - (d + 1))) (lvlChar k ψ N (N - (d + 1))) from (sup_le le_rfl hle) hmem
    intro x hx
    have hx0 : chain hUD hψc hψ1 π hs B d x x = 0 := by
      rw [LinearMap.mem_ker] at hx
      rw [hx]
      rfl
    have hK := ih (by omega) x hx0
    rw [lvlChar_def] at hK ⊢
    exact twKer_derUnip_le ψ π (a := N - d) (b := N - (d + 1)) (x := N - d - 1) (y := N - (d + 1) - 1)
      (by omega) (by omega) (by omega) hK

theorem atom_prop (hUL : ULift k) (hTB : ThmB k) (hirr : π.IsIrreducible) (hB : IsInvForm π B) (d : ℕ)
    (hd : d + 2 ≤ N) : ∃ c : ℂ, ∀ v w, atom hUD hUA hψc hψ1 π hs B d v w = c * chain hUD hψc hψ1 π hs B d v w := by
  have level : ∀ j (hj : j + 2 ≤ N),
      Lvl k ψ π (N - 2 - j) (by omega) (j : ℝ) (chain hUD hψc hψ1 π hs B j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [chain_zero]
      refine ⟨isPsd_of_inv π B hB, kills_congr (a := N) (by omega) ?_, ?_⟩
      · intro v hv w
        rw [twKer_derUnip_self ψ π] at hv
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
      · intro p _ v w
        simp [hB.2.2]
    | succ j ih =>
      intro hj
      obtain ⟨-, hP, hK, hM, -⟩ := chain_succ hUD hψc hψ1 π hs B j (by omega) (ih (by omega))
      exact ⟨hP, kills_congr (by omega) hK, mirEq_congr (by omega) (by push_cast; ring) hM⟩
  have hL := level d hd
  obtain ⟨-, hA1, hA2, hA3, -, hA5⟩ := atom_spec hUD hUA hψc hψ1 π hs B d hd hL
  refine lift hUD hψc hψ1 π hs B hUL hTB hirr hB d (by omega) _ hA1 ?_ (mirEq_congr (by omega) rfl hA5) hA2
  intro v hv w
  refine hA3 v ?_ w
  simp only [DerKer]
  rw [lvlChar_def] at hv
  rw [derChar_def]
  exact twKer_derUnip_le ψ π (a := N - d) (b := N - 2 - d + 1) (x := N - d - 1) (y := N - 2 - d + 1)
    (by omega) (by omega) (by omega) hv

theorem atom_eq_zero (hUS : USplit k) (hUL : ULift k) (hTB : ThmB k) (hirr : π.IsIrreducible) (hB : IsInvForm π B)
    (d : ℕ) (hd : d + 2 ≤ N) (hne : ∃ v, chain hUD hψc hψ1 π hs B (d + 1) v v ≠ 0) :
    ∀ v w, atom hUD hUA hψc hψ1 π hs B d v w = 0 := by
  have level : ∀ j (hj : j + 2 ≤ N),
      Lvl k ψ π (N - 2 - j) (by omega) (j : ℝ) (chain hUD hψc hψ1 π hs B j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [chain_zero]
      refine ⟨isPsd_of_inv π B hB, kills_congr (a := N) (by omega) ?_, ?_⟩
      · intro v hv w
        rw [twKer_derUnip_self ψ π] at hv
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
      · intro p _ v w
        simp [hB.2.2]
    | succ j ih =>
      intro hj
      obtain ⟨-, hP, hK, hM, -⟩ := chain_succ hUD hψc hψ1 π hs B j (by omega) (ih (by omega))
      exact ⟨hP, kills_congr (by omega) hK, mirEq_congr (by omega) (by push_cast; ring) hM⟩
  have hL := level d hd
  obtain ⟨hAt, -⟩ := atom_spec hUD hUA hψc hψ1 π hs B d hd hL
  obtain ⟨hD, -⟩ := chain_succ hUD hψc hψ1 π hs B d hd hL
  obtain ⟨c, hc⟩ := atom_prop hUD hUA hψc hψ1 π hs B hUL hTB hirr hB d hd
  have h0 := (hUS ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ) (chain hUD hψc hψ1 π hs B d)
    (atom hUD hUA hψc hψ1 π hs B d) (chain hUD hψc hψ1 π hs B (d + 1)) (lat0 k (N - 2 - d)) hL (isLattice_standard_lattice _)
    hAt hD).2 c hc hne
  intro v w
  rw [hc, h0, zero_mul]

theorem atom_eq_self (hUS : USplit k) (hB : IsInvForm π B) (d : ℕ) (hd : d + 2 ≤ N)
    (h0 : ∀ v, chain hUD hψc hψ1 π hs B (d + 1) v v = 0) :
    atom hUD hUA hψc hψ1 π hs B d = chain hUD hψc hψ1 π hs B d := by
  have level : ∀ j (hj : j + 2 ≤ N),
      Lvl k ψ π (N - 2 - j) (by omega) (j : ℝ) (chain hUD hψc hψ1 π hs B j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [chain_zero]
      refine ⟨isPsd_of_inv π B hB, kills_congr (a := N) (by omega) ?_, ?_⟩
      · intro v hv w
        rw [twKer_derUnip_self ψ π] at hv
        rw [(Submodule.mem_bot ℂ).1 hv]
        simp
      · intro p _ v w
        simp [hB.2.2]
    | succ j ih =>
      intro hj
      obtain ⟨-, hP, hK, hM, -⟩ := chain_succ hUD hψc hψ1 π hs B j (by omega) (ih (by omega))
      exact ⟨hP, kills_congr (by omega) hK, mirEq_congr (by omega) (by push_cast; ring) hM⟩
  have hL := level d hd
  obtain ⟨hAt, -⟩ := atom_spec hUD hUA hψc hψ1 π hs B d hd hL
  obtain ⟨hD, -⟩ := chain_succ hUD hψc hψ1 π hs B d hd hL
  exact (hUS ψ hψc hψ1 (N - 2 - d) N (by omega) V π hs (d : ℝ) (chain hUD hψc hψ1 π hs B d)
    (atom hUD hUA hψc hψ1 π hs B d) (chain hUD hψc hψ1 π hs B (d + 1)) (lat0 k (N - 2 - d)) hL (isLattice_standard_lattice _)
    hAt hD).1 h0

end PositivityTheory.RgUd.Form.U.Asm
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.ExistsOrthOfFinset
noncomputable section

open GlobalTheory.PRep

namespace PositivityTheory.RgUd.Form.U.Asm

theorem mem_fixed_iff_irr {G D : Type} [Group G] [AddCommGroup D] [Module ℂ D] (ρ : Representation ℂ G D)
    (K : Subgroup G) (v : D) : v ∈ fixed ρ K ↔ ∀ h : K, ρ (h : G) v = v := by
  change (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp

theorem exists_orth_of_finset {D : Type} [AddCommGroup D] [Module ℂ D] (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re) (s : Finset D) :
    ∀ u : D, ∃ w ∈ Submodule.span ℂ (s : Set D), ∀ m ∈ Submodule.span ℂ (s : Set D), B (u - w) m = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro u
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    intro m hm
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hm
    simp [hm]
  | insert a s ha ih =>
    intro u
    obtain ⟨wa, hwa, hwa'⟩ := ih a
    obtain ⟨wu, hwu, hwu'⟩ := ih u
    obtain ⟨a', ha'⟩ : ∃ a' : D, a' = a - wa := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = B (u - wu) a' / B a' a' := ⟨_, rfl⟩
    have hsub : Submodule.span ℂ (s : Set D) ≤ Submodule.span ℂ ((insert a s : Finset D) : Set D) :=
      Submodule.span_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
    have hamem : a ∈ Submodule.span ℂ ((insert a s : Finset D) : Set D) :=
      Submodule.subset_span (by simp)
    refine ⟨wu + c • a', ?_, ?_⟩
    · rw [ha']
      exact Submodule.add_mem _ (hsub hwu) (Submodule.smul_mem _ _ (Submodule.sub_mem _ hamem (hsub hwa)))
    · have hexp : ∀ m, B (u - (wu + c • a')) m = B (u - wu) m - c * B a' m := by
        intro m
        rw [show u - (wu + c • a') = (u - wu) - c • a' by abel, map_sub, map_smul,
          LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      have hs : ∀ m ∈ Submodule.span ℂ (s : Set D), B (u - (wu + c • a')) m = 0 := by
        intro m hm
        rw [hexp, hwu' m hm, ha', hwa' m hm, mul_zero, sub_zero]
      have key : ∀ m ∈ ((insert a s : Finset D) : Set D), B (u - (wu + c • a')) m = 0 := by
        intro m hm
        rw [Finset.coe_insert, Set.mem_insert_iff] at hm
        rcases hm with hm | hm
        · have hsplit : m = a' + wa := by rw [hm, ha']; abel
          rw [hsplit, map_add (f := _), hs wa hwa, add_zero, hexp]
          by_cases h0 : B a' a' = 0
          · have h0' : a' = 0 := by
              by_contra hne
              have := hBp a' hne
              rw [h0] at this
              simp at this
            simp [h0']
          · rw [hc, div_mul_cancel₀ _ h0, sub_self]
        · exact hs m (Submodule.subset_span hm)
      intro m hm
      have hle : Submodule.span ℂ ((insert a s : Finset D) : Set D) ≤ LinearMap.ker (B (u - (wu + c • a'))) :=
        Submodule.span_le.2 (fun m hm => LinearMap.mem_ker.2 (key m hm))
      exact LinearMap.mem_ker.1 (hle hm)

theorem exists_orth_decomp {G D : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup D]
    [Module ℂ D] (ρ : Representation ℂ G D) (hA : IsAdmissible ρ) (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G))
    (hK₁c : IsCompact (K₁ : Set G)) (χ : G → ℝ) (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hBe : ∀ g x y, B (ρ g x) (ρ g y) = (χ g : ℂ) * B x y) (W : Submodule ℂ D)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (u : D) :
    ∃ w ∈ W, ∀ w' ∈ W, B (u - w) w' = 0 := by
  classical
  by_cases hu : u = 0
  · exact ⟨0, W.zero_mem, fun w' _ => by simp [hu]⟩
  let S : Subgroup G :=
    { carrier := {g | ρ g u = u}
      mul_mem' := by
        intro a b (ha : ρ a u = u) (hb : ρ b u = u)
        show ρ (a * b) u = u
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        show ρ 1 u = u
        simp
      inv_mem' := by
        intro a (ha : ρ a u = u)
        show ρ a⁻¹ u = u
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hA.1 u
  let K : Subgroup G := K₁ ⊓ S
  have hKo : IsOpen (K : Set G) := by
    rw [Subgroup.coe_inf]; exact hK₁o.inter hSo
  have hKc : IsCompact (K : Set G) := by
    rw [Subgroup.coe_inf]; exact hK₁c.inter_right (Subgroup.isClosed_of_isOpen S hSo)
  have hKS : ∀ k : K, ρ (k : G) u = u := fun k => (Subgroup.mem_inf.1 k.2).2
  have hBu : B u u ≠ 0 := by
    intro h; have := hBp u hu; rw [h] at this; simp at this
  have hχ : ∀ k : K, (χ k : ℂ) = 1 := by
    intro k
    have h := hBe k u u
    rw [hKS k] at h
    have h2 : ((χ k : ℂ) - 1) * B u u = 0 := by rw [sub_mul, ← h]; ring
    rcases mul_eq_zero.1 h2 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hBu
  have hBK : ∀ (k : K) x y, B (ρ (k : G) x) (ρ (k : G) y) = B x y := by
    intro k x y; rw [hBe, hχ, one_mul]
  have : FiniteDimensional ℂ (fixed ρ K) := hA.2 K hKo hKc
  let M : Submodule ℂ D := W ⊓ fixed ρ K
  have : FiniteDimensional ℂ M := Submodule.finiteDimensional_of_le inf_le_right
  obtain ⟨s, hs⟩ : M.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨w, hwM, hw⟩ := exists_orth_of_finset B hBp s u
  rw [hs] at hwM hw
  refine ⟨w, (Submodule.mem_inf.1 hwM).1, ?_⟩
  have huF : u - w ∈ fixed ρ K :=
    Submodule.sub_mem _ ((mem_fixed_iff_irr ρ K u).2 hKS) (Submodule.mem_inf.1 hwM).2
  have hfix := (mem_fixed_iff_irr ρ K _).1 huF
  intro w' hw'
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let f : K → D := fun k => ρ (k : G) w'
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro k0
    refine ⟨(fun k : K => (k0 : G)⁻¹ * (k : G)) ⁻¹' {g | ρ g w' = w'},
      (hA.1 w').preimage (continuous_const.mul continuous_subtype_val), ?_, ?_⟩
    · simp
    · intro k hk
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hk
      simp only [f]
      conv_lhs => rw [show (k : G) = (k0 : G) * ((k0 : G)⁻¹ * (k : G)) by group]
      rw [map_mul, Module.End.mul_apply, hk]
  obtain ⟨T, hTmem⟩ : ∃ T : Finset D, ∀ v, v ∈ T ↔ ∃ k : K, ρ (k : G) w' = v :=
    ⟨hf.range_finite.toFinset, fun v => by simp only [Set.Finite.mem_toFinset, Set.mem_range, f]⟩
  have hTst : ∀ h : K, ∀ v ∈ T, ρ (h : G) v ∈ T := by
    intro h v hv
    obtain ⟨k, rfl⟩ := (hTmem v).1 hv
    exact (hTmem _).2 ⟨h * k, by rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  have hinv : ∀ h : K, ∀ v, ρ ((h⁻¹ : K) : G) (ρ (h : G) v) = v := by
    intro h v
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hinv' : ∀ h : K, ∀ v, ρ (h : G) (ρ ((h⁻¹ : K) : G) v) = v := by
    intro h v
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  have hsumF : ∑ v ∈ T, v ∈ M := by
    refine Submodule.mem_inf.2 ⟨Submodule.sum_mem _ (fun v hv => ?_), ?_⟩
    · obtain ⟨k, rfl⟩ := (hTmem v).1 hv; exact hW _ _ hw'
    · rw [mem_fixed_iff_irr]
      intro h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_nbij' (fun v => ρ (h : G) v) (fun v => ρ ((h⁻¹ : K) : G) v) (hTst h) (hTst h⁻¹)
        (fun v _ => hinv h v) (fun v _ => hinv' h v) (fun v _ => rfl)
  have h0 := hw _ hsumF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h0
  have hterm : ∀ v ∈ T, B (u - w) v = B (u - w) w' := by
    intro v hv
    obtain ⟨k, rfl⟩ := (hTmem v).1 hv
    conv_lhs => rw [← hfix k]
    exact hBK k _ _
  rw [Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hcard : T.card ≠ 0 := Finset.card_ne_zero_of_mem ((hTmem w').2 ⟨1, by simp⟩)
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 hcard
  · exact h1

theorem irr_of_forms {G D : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup D] [Module ℂ D]
    [Nontrivial D] (ρ : Representation ℂ G D) (hA : IsAdmissible ρ) (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G))
    (hK₁c : IsCompact (K₁ : Set G)) (χ : G → ℝ) (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBh : ∀ x y, B y x = starRingEnd ℂ (B x y)) (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hBe : ∀ g x y, B (ρ g x) (ρ g y) = (χ g : ℂ) * B x y)
    (hC : ∀ C : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ, (∀ x y, C y x = starRingEnd ℂ (C x y)) → (∀ x, 0 ≤ (C x x).re) →
      (∀ x, (C x x).re ≤ (B x x).re) → (∀ g x y, C (ρ g x) (ρ g y) = (χ g : ℂ) * C x y) →
      ∃ c : ℂ, ∀ x y, C x y = c * B x y) :
    ρ.IsIrreducible := by
  classical
  have key : ∀ W : Subrepresentation ρ, W ≠ ⊥ → W = ⊤ := by
    intro W hWb
    let Wm : Submodule ℂ D := W.toSubmodule
    have hWs : ∀ g, ∀ w ∈ Wm, ρ g w ∈ Wm := fun g w hw => W.apply_mem_toSubmodule g hw
    let Wp : Submodule ℂ D :=
      { carrier := {x | ∀ w ∈ Wm, B x w = 0}
        add_mem' := by
          intro a b ha hb w hw
          rw [map_add (f := _), LinearMap.add_apply, ha w hw, hb w hw, add_zero]
        zero_mem' := by intro w _; simp
        smul_mem' := by
          intro c x hx w hw
          rw [map_smul, LinearMap.smul_apply, hx w hw, smul_zero] }
    have hWp : ∀ x, x ∈ Wp ↔ ∀ w ∈ Wm, B x w = 0 := fun x => Iff.rfl
    have hWps : ∀ g, ∀ x ∈ Wp, ρ g x ∈ Wp := by
      intro g x hx
      rw [hWp]
      intro w hw
      have h1 : ρ g (ρ g⁻¹ w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [← h1, hBe, (hWp x).1 hx _ (hWs _ _ hw), mul_zero]
    have hdec := fun u => exists_orth_decomp ρ hA K₁ hK₁o hK₁c χ B hBp hBe Wm hWs u
    have hcompl : IsCompl Wm Wp := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x hx hxp
        by_contra hne
        have := hBp x hne
        rw [(hWp x).1 hxp x hx] at this
        simp at this
      · rw [codisjoint_iff, eq_top_iff]
        intro u _
        obtain ⟨w, hw, hw'⟩ := hdec u
        rw [show u = w + (u - w) by abel]
        exact Submodule.add_mem_sup hw ((hWp _).2 hw')
    let P : D →ₗ[ℂ] D := Wm.projection Wp hcompl
    have hPW : ∀ x, P x ∈ Wm := fun x => Submodule.projection_apply_mem hcompl x
    have hPw : ∀ w ∈ Wm, P w = w := fun w hw => Submodule.projection_apply_of_mem_left hcompl hw
    have hPq : ∀ x, x - P x ∈ Wp := fun x => Submodule.sub_projection_mem hcompl x
    have hP0 : ∀ q ∈ Wp, P q = 0 := fun q hq => Submodule.projection_apply_of_mem_right hcompl hq
    have hPρ : ∀ g x, P (ρ g x) = ρ g (P x) := by
      intro g x
      have hx : ρ g x = ρ g (P x) + ρ g (x - P x) := by
        rw [← map_add (f := _)]; congr 1; abel
      rw [hx, map_add (f := _), hPw _ (hWs g _ (hPW x)), hP0 _ (hWps g _ (hPq x)), add_zero]
    let C : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ := (B ∘ₗ P).compl₂ P
    have hCapp : ∀ x y, C x y = B (P x) (P y) := fun x y => rfl
    have hBsplit : ∀ x, B x x = B (P x) (P x) + B (x - P x) (x - P x) := by
      intro x
      have h1 : B (x - P x) (P x) = 0 := (hWp _).1 (hPq x) _ (hPW x)
      have h2 : B (P x) (x - P x) = 0 := by rw [hBh (x - P x) (P x), h1, map_zero]
      conv_lhs => rw [show x = P x + (x - P x) by abel]
      simp only [map_add (f := _), LinearMap.add_apply, h1, h2, add_zero, zero_add]
    have hnn : ∀ x, 0 ≤ (B x x).re := by
      intro x
      by_cases h : x = 0
      · rw [h]; simp
      · exact (hBp _ h).le
    obtain ⟨c, hc⟩ := hC C (fun x y => by rw [hCapp, hCapp, hBh]) (fun x => by rw [hCapp]; exact hnn _)
      (fun x => by
        rw [hCapp, hBsplit x, Complex.add_re]
        have := hnn (x - P x)
        linarith)
      (fun g x y => by rw [hCapp, hCapp, hPρ, hPρ, hBe])
    obtain ⟨w0, hw0, hw0ne⟩ : ∃ w ∈ Wm, w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hWb
      apply Subrepresentation.toSubmodule_injective
      show Wm = ⊥
      exact (Submodule.eq_bot_iff _).2 hcon
    have hc1 : c = 1 := by
      have h := hc w0 w0
      rw [hCapp, hPw w0 hw0] at h
      have hB0 : B w0 w0 ≠ 0 := by
        intro h0; have := hBp w0 hw0ne; rw [h0] at this; simp at this
      have h2 : (c - 1) * B w0 w0 = 0 := by rw [sub_mul, ← h]; ring
      rcases mul_eq_zero.1 h2 with h1 | h1
      · exact sub_eq_zero.1 h1
      · exact absurd h1 hB0
    apply Subrepresentation.toSubmodule_injective
    show Wm = ⊤
    rw [eq_top_iff]
    intro x _
    have hq : x - P x = 0 := by
      by_contra hne
      have h := hc (x - P x) (x - P x)
      rw [hCapp, hc1, one_mul, hP0 _ (hPq x), map_zero] at h
      have := hBp _ hne
      rw [← h] at this
      simp at this
    have hx : x = P x := sub_eq_zero.1 hq
    rw [hx]
    exact hPW x
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : D)
    have h1 : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ D))
    rw [← h] at h1
    exact hx ((Submodule.mem_bot ℂ).1 (h1 : x ∈ (⊥ : Submodule ℂ D)))
  exact { exists_pair_ne := ⟨⊥, ⊤, hne⟩
          eq_bot_or_eq_top := fun W => by
            by_cases h : W = ⊥
            · exact Or.inl h
            · exact Or.inr (key W h) }

end PositivityTheory.RgUd.Form.U.Asm
end
end

noncomputable section

set_option linter.unusedSectionVars false

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Twist

theorem twist_irr {G D : Type} [Group G] [AddCommGroup D] [Module ℂ D] (ρ : Representation ℂ G D) (χ : G →* ℂˣ)
    (h : ρ.IsIrreducible) : (twist ρ χ).IsIrreducible := by
  let f : Subrepresentation ρ ≃o Subrepresentation (twist ρ χ) :=
    { toFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        show ((χ g : ℂˣ) : ℂ) • ρ g v ∈ W.toSubmodule
        exact W.toSubmodule.smul_mem _ (W.apply_mem_toSubmodule g hv)⟩
      invFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        have h1 := W.apply_mem_toSubmodule g hv
        have h2 : ρ g v = (((χ g)⁻¹ : ℂˣ) : ℂ) • (twist ρ χ g v) := by
          show ρ g v = (((χ g)⁻¹ : ℂˣ) : ℂ) • (((χ g : ℂˣ) : ℂ) • ρ g v)
          rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
        rw [h2]
        exact W.toSubmodule.smul_mem _ h1⟩
      left_inv := fun W => rfl
      right_inv := fun W => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff f).1 h

end Twist

section Casts

theorem sub_iff_twKer (ψ : AddChar k Circle) (n j : ℕ) (π : GRep k (n + (j + 1))) :
    Subsingleton (derivB ψ (j + 1) π).V ↔
      twKer π.ρ (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) = ⊤ := by
  obtain ⟨q, hqs, hqk, -⟩ := derDict ψ n j π.ρ
  rw [← hqk]
  constructor
  · intro hs
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_top, iff_true]
    exact @Subsingleton.elim _ hs _ _
  · intro hk
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, rfl⟩ := hqs x
    obtain ⟨b, rfl⟩ := hqs y
    have ha : a ∈ LinearMap.ker q := hk ▸ Submodule.mem_top
    have hb : b ∈ LinearMap.ker q := hk ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at ha hb
    exact ha.trans hb.symm

theorem cast_twKer (ψ : AddChar k Circle) {a b : ℕ} (e : a = b) (π : GRep k a) (m : ℕ) :
    twKer (π.cast e).ρ (derUnip k b m) (derChar k ψ b m) = ⊤ ↔ twKer π.ρ (derUnip k a m) (derChar k ψ a m) = ⊤ := by
  subst e
  rfl

end Casts

section Desc

variable (hUD : UDens k) (hUA : UAtom k) {ψ : AddChar k Circle} (hψc : Continuous ψ) (hψ1 : ψ ≠ 1) {N : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π)
  (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)

theorem chain_psd (hB : IsInvForm π B) : ∀ d, d + 1 ≤ N → IsPsd (chain hUD hψc hψ1 π hs B d)
  | 0, _ => isPsd_of_inv π B hB
  | d + 1, hd => by
    have hd2 : d + 2 ≤ N := by omega
    have hL := chain_lvl hUD hψc hψ1 π hs B hB d hd2
    exact (chain_succ hUD hψc hψ1 π hs B d hd2 hL).2.1

theorem chain_kills (hB : IsInvForm π B) : ∀ d, d + 1 ≤ N → Kills ψ π (N - d) (chain hUD hψc hψ1 π hs B d) := by
  have killsZero : Kills ψ π N (chain hUD hψc hψ1 π hs B 0) := by
    intro v hv w
    rw [twKer_derUnip_self ψ π] at hv
    rw [(Submodule.mem_bot ℂ).1 hv]
    simp
  intro d hd
  cases d with
  | zero => exact killsZero
  | succ d =>
    have hd2 : d + 2 ≤ N := by omega
    have hL := chain_lvl hUD hψc hψ1 π hs B hB d hd2
    exact kills_congr (by omega) (chain_succ hUD hψc hψ1 π hs B d hd2 hL).2.2.1


include hUA in
theorem twisted_kernel_forms_nonvanishing (hUS : USplit k) (hB : IsInvForm π B) :
    ∀ e d, d + e + 1 = N → (∃ v, chain hUD hψc hψ1 π hs B d v v ≠ 0) →
      ∃ n', n' + d + 1 ≤ N ∧ twKer π (derUnip k N n') (derChar k ψ N n') ≠ ⊤ := by
  intro e
  induction e with
  | zero =>
    rintro d hde ⟨v, hv⟩
    refine ⟨0, by omega, fun htop => hv ?_⟩
    have hK := chain_kills hUD hψc hψ1 π hs B hB d (by omega)
    have e1 : N - d = 1 := by omega
    rw [e1] at hK
    refine hK v ?_ v
    have hle : twKer π (derUnip k N 0) (derChar k ψ N 0) ≤ twKer π (derUnip k N 1) (lvlChar k ψ N 1) :=
      twKer_mono π _ _ (le_inf inf_le_left (inf_le_left.trans (unipB_le_colFix_one N))) fun u => rfl
    exact hle (htop ▸ Submodule.mem_top)
  | succ e ih =>
    rintro d hde ⟨v, hv⟩
    have hd2 : d + 2 ≤ N := by omega
    by_cases h0 : ∀ w, chain hUD hψc hψ1 π hs B (d + 1) w w = 0
    · have hA := atom_eq_self hUD hUA hψc hψ1 π hs B hUS hB d hd2 h0
      have hL := chain_lvl hUD hψc hψ1 π hs B hB d hd2
      have hK := (atom_spec hUD hUA hψc hψ1 π hs B d hd2 hL).2.2.2.1
      refine ⟨N - 2 - d + 1, by omega, fun htop => hv ?_⟩
      have hmem : v ∈ DerKer k ψ π (N - 2 - d) := by
        unfold DerKer
        rw [htop]
        exact Submodule.mem_top
      have := hK v hmem v
      rwa [hA] at this
    · have hnext : ∃ w, chain hUD hψc hψ1 π hs B (d + 1) w w ≠ 0 := not_forall.mp h0
      obtain ⟨n', hn', hne⟩ := ih (d + 1) (by omega) hnext
      exact ⟨n', by omega, hne⟩

theorem chain_ne_of (hB : IsInvForm π B) (d n' : ℕ) (hd : d + 1 ≤ N) (hn' : n' + d < N)
    (hne : twKer π (derUnip k N n') (derChar k ψ N n') ≠ ⊤) : ∃ v, chain hUD hψc hψ1 π hs B d v v ≠ 0 := by
  have radical : ∀ j, j + 1 ≤ N → ∀ v, chain hUD hψc hψ1 π hs B j v v = 0 →
      v ∈ twKer π (derUnip k N (N - j)) (lvlChar k ψ N (N - j)) := by
    intro j
    induction j with
    | zero =>
      intro _ v hv
      rw [chain_zero] at hv
      by_cases h : v = 0
      · rw [h]
        exact zero_mem _
      · have hpos := hB.2.1 v h
        simp [hv] at hpos
    | succ j ih =>
      intro hj v hv
      have hj2 : j + 2 ≤ N := by omega
      have hL := chain_lvl hUD hψc hψ1 π hs B hB j hj2
      obtain ⟨-, -, -, -, hR⟩ := chain_succ hUD hψc hψ1 π hs B j hj2 hL
      have hmem := hR v hv
      have e : N - 2 - j + 1 = N - (j + 1) := by omega
      rw [e] at hmem
      suffices hle : LinearMap.ker (chain hUD hψc hψ1 π hs B j) ≤
          twKer π (derUnip k N (N - (j + 1))) (lvlChar k ψ N (N - (j + 1))) from
        (sup_le le_rfl hle) hmem
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hx0 : chain hUD hψc hψ1 π hs B j x x = 0 := by simp [hx]
      have hK := ih (by omega) x hx0
      rw [lvlChar_def] at hK ⊢
      exact twKer_derUnip_le ψ π (a := N - j) (b := N - (j + 1))
        (x := N - j - 1) (y := N - (j + 1) - 1) (by omega) (by omega) (by omega) hK
  by_contra hall
  apply hne
  rw [eq_top_iff]
  intro v _
  have hv := radical d hd v (not_exists_not.mp hall v)
  rw [lvlChar_def] at hv
  rw [derChar_def]
  exact twKer_derUnip_le ψ π (a := N - d) (b := n') (x := N - d - 1) (y := n') (by omega) (by omega) (by omega) hv

end Desc

end PositivityTheory.RgUd.Form.U.Asm
