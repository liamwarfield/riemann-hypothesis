module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots
namespace KStar

section Def

variable {R : Type*} [CommRing R]

noncomputable def nuStar (p : R) (U : Set R) (tr : ℕ) : ℕ∞ :=
  sInf ((fun u => emultiplicity p (u ^ tr - 1)) '' U)

theorem le_nuStar_iff (p : R) (U : Set R) (tr n : ℕ) :
    (n : ℕ∞) ≤ nuStar p U tr ↔ ∀ u ∈ U, p ^ n ∣ u ^ tr - 1 := by
  unfold nuStar
  rw [le_sInf_iff, Set.forall_mem_image]
  exact forall₂_congr fun u _ => pow_dvd_iff_le_emultiplicity.symm

theorem exists_eq_nuStar {p : R} {U : Set R} (hU : U.Nonempty) (tr : ℕ) :
    ∃ u ∈ U, emultiplicity p (u ^ tr - 1) = nuStar p U tr := by
  have h := csInf_mem (hU.image (fun u => emultiplicity p (u ^ tr - 1)))
  obtain ⟨u, hu, e⟩ := h
  exact ⟨u, hu, e⟩

theorem exists_exact_of_nuStar_eq {p : R} {U : Set R} {tr ν : ℕ} (h : nuStar p U tr = ν) :
    ∃ u ∈ U, p ^ ν ∣ u ^ tr - 1 ∧ ¬ p ^ (ν + 1) ∣ u ^ tr - 1 := by
  rcases U.eq_empty_or_nonempty with hU | hU
  · subst hU
    simp [nuStar] at h
  obtain ⟨u, hu, e⟩ := exists_eq_nuStar hU tr
  rw [h] at e
  refine ⟨u, hu, pow_dvd_iff_le_emultiplicity.mpr e.ge, fun hd => ?_⟩
  have := pow_dvd_iff_le_emultiplicity.mp hd
  rw [e] at this
  norm_cast at this
  omega

theorem eq_nuStar_of_forall {p : R} {U : Set R} {tr : ℕ} (m : ℕ∞)
    (hm : ∀ n : ℕ, (n : ℕ∞) ≤ m ↔ ∀ u ∈ U, p ^ n ∣ u ^ tr - 1) : m = nuStar p U tr := by
  refine le_antisymm ?_ ?_
  · refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
    exact (le_nuStar_iff p U tr n).mpr ((hm n).mp hn)
  · refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
    exact (hm n).mpr ((le_nuStar_iff p U tr n).mp hn)

end Def

section Domain

variable {R : Type*} [CommRing R] [IsDomain R]

end Domain

section Int

end Int

section Inhabitant

end Inhabitant

end KStar
end

namespace KStar.TotallyRealRoots

variable (l : ℕ) [Fact l.Prime]

noncomputable def nu (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) : ℕ∞ :=
  nuStar (l : ℤ_[l]) ((fun u : ℤ_[l]ˣ => (u : ℤ_[l])) '' (U : Set ℤ_[l]ˣ)) tr

noncomputable def redPow (a : ℕ) : ℤ_[l]ˣ →* (ZMod (l ^ a))ˣ :=
  Units.map (PadicInt.toZModPow a : ℤ_[l] →+* ZMod (l ^ a)).toMonoidHom

noncomputable def red : ℤ_[l]ˣ →* (ZMod l)ˣ :=
  Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom

noncomputable def princ (a : ℕ) : Subgroup ℤ_[l]ˣ := (redPow l a).ker

noncomputable def resOrder (U : Subgroup ℤ_[l]ˣ) : ℕ := Nat.card (U.map (red l))

abbrev QmodZ : Type := ℚ_[l] ⧸ (1 : Submodule ℤ_[l] ℚ_[l])

def twistInv (A : Type*) [AddCommGroup A] [Module ℤ_[l] A] (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) :
    Submodule ℤ_[l] A where
  carrier := {x | ∀ u ∈ U, ((u : ℤ_[l]) ^ tr) • x = x}
  zero_mem' := fun u _ => smul_zero _
  add_mem' := fun {x y} hx hy u hu => by rw [smul_add, hx u hu, hy u hu]
  smul_mem' := fun c x hx u hu => by rw [smul_comm, hx u hu]

noncomputable def H0 (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) : Submodule ℤ_[l] (QmodZ l) := twistInv l (QmodZ l) U tr

noncomputable def levelGroup (N : ℕ) (H : Subgroup (ZMod N)ˣ) : Subgroup ℤ_[l]ˣ :=
  (H.map (ZMod.unitsMap (Nat.ordProj_dvd N l))).comap (redPow l (N.factorization l))

noncomputable def levelInertia (N : ℕ) : Subgroup (ZMod N)ˣ :=
  (ZMod.unitsMap (Nat.ordCompl_dvd N l)).ker

variable {l}

theorem mem_princ {a : ℕ} {u : ℤ_[l]ˣ} : u ∈ princ l a ↔ (l : ℤ_[l]) ^ a ∣ (u : ℤ_[l]) - 1 := by
  rw [princ, MonoidHom.mem_ker, ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, map_one, sub_eq_zero, Units.ext_iff]
  simp [redPow]

theorem le_nu_iff {U : Subgroup ℤ_[l]ˣ} {tr n : ℕ} :
    (n : ℕ∞) ≤ nu l U tr ↔ ∀ u ∈ U, (l : ℤ_[l]) ^ n ∣ (u : ℤ_[l]) ^ tr - 1 := by
  rw [nu, le_nuStar_iff, Set.forall_mem_image]
  rfl

theorem le_nu_iff_pow_mem_princ {U : Subgroup ℤ_[l]ˣ} {tr n : ℕ} :
    (n : ℕ∞) ≤ nu l U tr ↔ ∀ u ∈ U, u ^ tr ∈ princ l n := by
  rw [le_nu_iff]
  simp only [mem_princ, Units.val_pow_eq_pow_val]

theorem mem_twistInv {A : Type*} [AddCommGroup A] [Module ℤ_[l] A] {U : Subgroup ℤ_[l]ˣ} {tr : ℕ}
    {x : A} : x ∈ twistInv l A U tr ↔ ∀ u ∈ U, ((u : ℤ_[l]) ^ tr) • x = x := Iff.rfl

theorem mem_levelGroup {N : ℕ} {H : Subgroup (ZMod N)ˣ} {u : ℤ_[l]ˣ} :
    u ∈ levelGroup l N H ↔
      ∃ h ∈ H, ZMod.unitsMap (Nat.ordProj_dvd N l) h = redPow l (N.factorization l) u := Iff.rfl

end KStar.TotallyRealRoots
