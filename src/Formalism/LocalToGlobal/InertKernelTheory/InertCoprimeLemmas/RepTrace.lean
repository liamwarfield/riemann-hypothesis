module

public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FrLocB
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb

@[expose] public section

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTrace
noncomputable section

namespace Formalism.L2.KerInert.RepFrame

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem trace_tau_sum (D : D7) : TraceTau D := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.sum_tau_trace D

section Rank

variable (D : D7)

theorem exists_nat_integral {N N' : ℕ} (B : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ n : ℕ, 0 < n ∧ ∀ i j, IsIntegral ℤ ((n : D.host.E) * B i j) := by
  classical
  choose k hk hkB using fun x : Fin N' × Fin N => Formalism.L2.KerInert.FrLocB.nat_mult (D := D) (B x.1 x.2)
  refine ⟨∏ x, k x, Finset.prod_pos fun x _ => hk x, fun i j => ?_⟩
  have h := Finset.mul_prod_erase Finset.univ k (Finset.mem_univ (i, j))
  have he : ((∏ x, k x : ℕ) : D.host.E) * B i j =
      ((∏ x ∈ Finset.univ.erase (i, j), k x : ℕ) : D.host.E) * ((k (i, j) : D.host.E) * B i j) := by
    rw [← h, Nat.cast_mul]; ring
  rw [he]
  have hi : IsIntegral ℤ ((∏ x ∈ Finset.univ.erase (i, j), k x : ℕ) : D.host.E) := by
    have := isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := ((∏ x ∈ Finset.univ.erase (i, j), k x : ℕ) : ℤ))
    simpa using this
  exact hi.mul (hkB (i, j))

variable {D}

theorem mem_span_of_locBasis {p : ℕ} [hp : Fact p.Prime] {N N' r : ℕ}
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
    (hb : LocBasis D p Y b) {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ Y) :
    y ∈ Submodule.span D.host.K (Set.range b) := by
  obtain ⟨s, hs, c, hc⟩ := hb.2.2 y hy
  have hs0 : (s : D.host.K) ≠ 0 := by
    exact_mod_cast Formalism.L2.KerInert.FrLocB.ne_zero_of_coprime p hs
  have h1 : (s : D.host.K) • y ∈ Submodule.span D.host.K (Set.range b) := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, hc]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Formalism.L2.KerInert.IntegralOrthonormalChange.smul_eq_K D _ (c i : D.host.K).2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h2 := Submodule.smul_mem _ (s : D.host.K)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at h2

theorem span_top_of_locBasis {p : ℕ} [Fact p.Prime] {N N' r : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : LocBasis D p (YYl D L L') b) :
    ⊤ ≤ Submodule.span D.host.K (Set.range b) := by
  obtain ⟨M, hM, hlow⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.YY_lower D L L' hL hL'
  intro B _
  obtain ⟨n, hn, hnB⟩ := exists_nat_integral D B
  have hA : ∀ i j, IsIntegral ℤ (((n : D.host.E) • B) i j) := fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hnB i j
  have h1 := mem_span_of_locBasis hb (hlow _ hA)
  rw [Int.cast_smul_eq_zsmul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.K,
    ← Int.cast_smul_eq_zsmul D.host.K, smul_smul] at h1
  have hMn : ((M : D.host.K) * (n : D.host.K)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hM) (by exact_mod_cast hn.ne')
  have h2 := Submodule.smul_mem _ ((M : D.host.K) * (n : D.host.K))⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hMn, one_smul] at h2

theorem rank_of_locBasis {p : ℕ} [Fact p.Prime] {N N' r : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L) (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : LocBasis D p (YYl D L L') b) :
    r = Fintype.card (D.what₂.Tau × Fin N' × Fin N) := by
  have hbas := Module.Basis.mk hb.1 (span_top_of_locBasis L L' hL hL' hb)
  have h1 := Module.finrank_eq_card_basis hbas
  rw [Module.finrank_matrix, Fintype.card_fin, Fintype.card_fin] at h1
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Formalism.L2.Ker.cardTau D]
  rw [Fintype.card_fin] at h1
  rw [← h1]; ring

end Rank

variable {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

section Witness

variable (D : D7)

end Witness

end Formalism.L2.KerInert.RepFrame

set_option pp.fullNames true
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepDataRec
noncomputable section

namespace Formalism.L2.KerInert.RepRec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

theorem intOff_mono {S S' : Finset ℕ} (hSS : S ⊆ S') {r : ℂ} (h : IntOff S r) : IntOff S' r :=
  ⟨h.1, fun q _ lam hq => h.2 q lam (fun hm => hq (hSS hm))⟩

theorem intOff_natCast (S : Finset ℕ) (n : ℕ) : IntOff S (n : ℂ) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact IntOff.zero
  | succ m ih => rw [Nat.cast_succ]; exact IntOff.add ih IntOff.one

theorem dataRec_iff {p : ℕ} [hp : Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (D : D7) (cl : ℕ)
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) :
    DataRec X D cl Ξ ↔ ClAway p cl ∧ XiAway X D Ξ := by
  constructor
  · rintro ⟨S, ⟨hcl, hS⟩, hpS, hΞ⟩
    exact ⟨⟨hcl, fun hd => hpS (hS p hp.out hd)⟩, ⟨S, hpS, hΞ⟩⟩
  · rintro ⟨⟨hcl, hnd⟩, S₀, hp0, hΞ⟩
    refine ⟨S₀ ∪ cl.primeFactors,
      ⟨hcl, fun q hq hd => Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hq, hd, hcl.ne'⟩)⟩, ?_,
      fun j La La' y => intOff_mono Finset.subset_union_left (hΞ j La La' y)⟩
    rw [Finset.mem_union, not_or]
    exact ⟨hp0, fun h => hnd (Nat.dvd_of_mem_primeFactors h)⟩

theorem dataRec_movD {p : ℕ} [Fact p.Prime] (X : Formalism.MainNotions.FormalGroupSystem.Sys p) (D : D7) (cl : ℕ)
    (Ξ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) (G : ∀ j, X.Lt j → X.Lt (j + 1) → (Formalism.L2.Col.Sp D.host.E ((X.Pj j).m + 1) ≃ₗ[D.host.E] Formalism.L2.Col.Sp D.host.E ((X.Pj j).m + 1))) (G' : ∀ j, X.Lt j → X.Lt (j + 1) → (Formalism.L2.Col.Sp D.host.E ((X.Pj (j + 1)).m + 1) ≃ₗ[D.host.E] Formalism.L2.Col.Sp D.host.E ((X.Pj (j + 1)).m + 1))) (h : DataRec X D cl Ξ) :
    DataRec X D cl (fun j La La' => Formalism.L2.PairingIndexBounds.F.movD (Ξ j La La') (G j La La') (G' j La La')) := by
  obtain ⟨S, hS, hpS, hΞ⟩ := h
  exact ⟨S, hS, hpS, fun j La La' x => Formalism.L2.KerInert.RepComb.intOff_movD _ _ _ (hΞ j La La') x⟩

end Formalism.L2.KerInert.RepRec
end
end
