module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLocC

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppCharC
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppCharN
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppCharB
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppCharA
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW

variable {D : D7} (X : HidaSetting D)

abbrev wK (kv : Σ k : Fin 2, D.nd.PlG k) : HeightOneSpectrum (𝓞 X.B.I.E) := wB X (D.naut.plGw kv.1 kv.2)

theorem card_wK (kv : Σ k : Fin 2, D.nd.PlG k) :
    Nat.card (𝓞 X.B.I.E ⧸ (wK X kv).asIdeal) = D.host.g kv.1 := by
  rw [card_wB, card_res_host]

theorem card_wc {I : AutInst} (w : HeightOneSpectrum (𝓞 I.E)) :
    Nat.card (𝓞 I.E ⧸ (wc I w).asIdeal) = Nat.card (𝓞 I.E ⧸ w.asIdeal) :=
  Nat.card_congr (Ideal.quotientEquiv (wc I w).asIdeal w.asIdeal (sigO I)
    (Ideal.map_comap_of_surjective _ (sigO I).surjective w.asIdeal).symm).toEquiv

theorem card_wKc (kv : Σ k : Fin 2, D.nd.PlG k) :
    Nat.card (𝓞 X.B.I.E ⧸ (wc X.B.I (wK X kv)).asIdeal) = D.host.g kv.1 := by
  rw [card_wc, card_wK]

theorem mem_wB (w : HeightOneSpectrum (𝓞 D.host.E)) (a : 𝓞 X.B.I.E) :
    a ∈ (wB X w).asIdeal ↔ RingOfIntegers.mapRingEquiv X.ιE a ∈ w.asIdeal := Iff.rfl

theorem gk_mem (kv : Σ k : Fin 2, D.nd.PlG k) : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
  rw [mem_wB, map_natCast]; exact D.naut.plGw_over kv.1 kv.2

theorem gk_mem_c (kv : Σ k : Fin 2, D.nd.PlG k) :
    ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) ∈ (wc X.B.I (wK X kv)).asIdeal :=
  natCast_mem_wc X.B.I (gk_mem X kv)

theorem not_both (P : Ideal (𝓞 X.B.I.E)) (hP : P ≠ ⊤) (h0 : ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ∈ P)
    (h1 : ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) ∈ P) : False := by
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) := by
    have h' : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    simpa using h'.map (Int.castRingHom (𝓞 X.B.I.E))
  obtain ⟨a, b, hab⟩ := hcop
  have := P.add_mem (P.mul_mem_left a h0) (P.mul_mem_left b h1)
  rw [hab] at this
  exact hP ((Ideal.eq_top_iff_one _).2 this)

theorem not_both' (P : Ideal (𝓞 X.B.I.E)) (hP : P ≠ ⊤) {k k' : Fin 2} (hk : k ≠ k')
    (h0 : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P) (h1 : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ∈ P) : False := by
  fin_cases k <;> fin_cases k'
  · exact hk rfl
  · exact not_both X P hP h0 h1
  · exact not_both X P hP h1 h0
  · exact hk rfl

theorem g_eq_cast : ((X.B.g : ℕ) : 𝓞 X.B.I.E) = ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) := by
  rw [X.g_eq]; push_cast; ring

theorem gk_of_g {P : Ideal (𝓞 X.B.I.E)} (hP : P.IsPrime) (h : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P) :
    ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P := by
  rw [g_eq_cast] at h
  rcases hP.mem_or_mem h with h | h
  exacts [⟨0, h⟩, ⟨1, h⟩]

theorem g_mem_of_gk {P : Ideal (𝓞 X.B.I.E)} {k : Fin 2} (h : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P) :
    ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P := by
  rw [g_eq_cast]
  fin_cases k
  · exact P.mul_mem_right _ h
  · exact P.mul_mem_left _ h

theorem over_gk (P : HeightOneSpectrum (𝓞 X.B.I.E)) (k : Fin 2) (hP : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal) :
    ∃ v : D.nd.PlG k, P = wK X ⟨k, v⟩ ∨ P = wc X.B.I (wK X ⟨k, v⟩) := by
  have hwH : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (toH X P).asIdeal := by
    show (RingOfIntegers.mapRingEquiv X.ιE).symm ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
    rw [map_natCast]; exact hP
  obtain ⟨v, hv | hv⟩ := cover X k (toH X P) hwH
  · exact ⟨v, Or.inl (by rw [← wB_toH X P, hv])⟩
  · exact ⟨v, Or.inr (by rw [← wB_toH X P, hv, wB_conjH X])⟩

theorem over_g (P : HeightOneSpectrum (𝓞 X.B.I.E)) (hP : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal) :
    ∃ kv : Σ k : Fin 2, D.nd.PlG k, P = wK X kv ∨ P = wc X.B.I (wK X kv) := by
  obtain ⟨k, hk⟩ := gk_of_g X P.isPrime hP
  obtain ⟨v, hv⟩ := over_gk X P k hk
  exact ⟨⟨k, v⟩, hv⟩

theorem wB_inj {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : wB X w = wB X w') : w = w' := by
  refine HeightOneSpectrum.ext ?_
  ext a
  obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv X.ιE).surjective a
  rw [← mem_wB, ← mem_wB, h]

theorem wK_ne {kv kv' : Σ k : Fin 2, D.nd.PlG k} (h : kv ≠ kv') : wK X kv ≠ wK X kv' := by
  obtain ⟨k, v⟩ := kv
  obtain ⟨k', v'⟩ := kv'
  intro he
  by_cases hk : k = k'
  · subst hk
    have hv : v ≠ v' := fun hv => h (by rw [hv])
    exact hv (D.naut.plGw_inj k (wB_inj X he))
  · have h0 := gk_mem X ⟨k, v⟩
    have h1 := gk_mem X ⟨k', v'⟩
    rw [← he] at h1
    exact not_both' X _ (wK X ⟨k, v⟩).isPrime.ne_top hk h0 h1

theorem wK_ne_wc (kv kv' : Σ k : Fin 2, D.nd.PlG k) : wK X kv ≠ wc X.B.I (wK X kv') := by
  obtain ⟨k, v⟩ := kv
  obtain ⟨k', v'⟩ := kv'
  intro he
  by_cases hk : k = k'
  · subst hk
    rw [show wc X.B.I (wK X ⟨k, v'⟩) = wB X (conjH (D.naut.plGw k v')) from (wB_conjH X _).symm] at he
    have he' := wB_inj X he
    apply D.naut.plGw_nconj k v' v
    have := isConjPl_conjH X (D.naut.plGw k v')
    rw [← he'] at this
    exact this
  · have h0 := gk_mem X ⟨k, v⟩
    have h1 := gk_mem_c X ⟨k', v'⟩
    rw [← he] at h1
    exact not_both' X _ (wK X ⟨k, v⟩).isPrime.ne_top hk h0 h1

theorem mem_g_of_all {a : 𝓞 X.B.I.E}
    (ha : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → a ∈ P.asIdeal) :
    ∃ c : 𝓞 X.B.I.E, a = ((X.B.g : ℕ) : 𝓞 X.B.I.E) * c := by
  have hk : ∀ k : Fin 2, a ∈ Ideal.span {((D.host.g k : ℕ) : 𝓞 X.B.I.E)} := by
    intro k
    refine mem_span_of_all (D.host.g_prime k) (unram X k) fun P hPm hgP => ?_
    let P' : HeightOneSpectrum (𝓞 X.B.I.E) := ⟨P, hPm.isPrime, fun hb => by
      rw [hb] at hgP
      exact (by exact_mod_cast (D.host.g_prime k).ne_zero : ((D.host.g k : ℕ) : 𝓞 X.B.I.E) ≠ 0)
        ((Submodule.mem_bot _).1 hgP)⟩
    exact ha P' (g_mem_of_gk X hgP)
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (hk 0)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hk 1)
  have hcop : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) := by
    have h' : IsCoprime ((D.host.g 0 : ℕ) : ℤ) ((D.host.g 1 : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    simpa using h'.map (Int.castRingHom (𝓞 X.B.I.E))
  obtain ⟨α, β, hαβ⟩ := hcop
  refine ⟨α * v + β * u, ?_⟩
  rw [g_eq_cast]
  calc a = (α * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) + β * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E)) * a := by rw [hαβ, one_mul]
    _ = α * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E) * (v * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E)) +
        β * ((D.host.g 1 : ℕ) : 𝓞 X.B.I.E) * (u * ((D.host.g 0 : ℕ) : 𝓞 X.B.I.E)) := by
          rw [hv, hu]; ring
    _ = _ := by ring

theorem exists_eps (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ ε : 𝓞 X.B.I.E, ε - 1 ∈ (wK X kv).asIdeal ∧
      ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv → ε ∈ P.asIdeal := by
  classical
  let S : Set (HeightOneSpectrum (𝓞 X.B.I.E)) :=
    Formalism.MainNotions.BridgeLemma.plOver X.B.I.E (D.host.g 0) ∪ Formalism.MainNotions.BridgeLemma.plOver X.B.I.E (D.host.g 1)
  have hS : S.Finite := (Formalism.MainNotions.BridgeLemma.finite_plOver X.B.I.E (D.host.g_prime 0)).union
    (Formalism.MainNotions.BridgeLemma.finite_plOver X.B.I.E (D.host.g_prime 1))
  have : Finite S := hS.to_subtype
  have hcop : Pairwise (Function.onFun IsCoprime fun P : S => (P.1).asIdeal) := by
    intro P Q hPQ
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    refine Ideal.IsMaximal.coprime_of_ne (P.1).isMaximal (Q.1).isMaximal fun h => hPQ ?_
    exact Subtype.ext (HeightOneSpectrum.ext h)
  obtain ⟨ε, hε⟩ := Ideal.exists_forall_sub_mem_ideal hcop fun P => if P.1 = wK X kv then 1 else 0
  have hmem : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ∈ S := by
    intro P hP
    obtain ⟨k, hk⟩ := gk_of_g X P.isPrime hP
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr hk
  refine ⟨ε, ?_, fun P hP hne => ?_⟩
  · have := hε ⟨wK X kv, hmem _ (g_mem_of_gk X (gk_mem X kv))⟩
    simpa using this
  · have := hε ⟨P, hmem P hP⟩
    simp only [if_neg hne, sub_zero] at this
    exact this

theorem eps_other (kv : Σ k : Fin 2, D.nd.PlG k) {ε : 𝓞 X.B.I.E}
    (hε : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv → ε ∈ P.asIdeal)
    (k' : Fin 2) (hk : k' ≠ kv.1) : ε ∈ Ideal.span {((D.host.g k' : ℕ) : 𝓞 X.B.I.E)} := by
  refine mem_span_of_all (D.host.g_prime k') (unram X k') fun P hPm hgP => ?_
  let P' : HeightOneSpectrum (𝓞 X.B.I.E) := ⟨P, hPm.isPrime, fun hb => by
    rw [hb] at hgP
    exact (by exact_mod_cast (D.host.g_prime k').ne_zero : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ≠ 0)
      ((Submodule.mem_bot _).1 hgP)⟩
  refine hε P' (g_mem_of_gk X hgP) fun he => ?_
  have h0 := gk_mem X kv
  have h1 : ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by rw [← he]; exact hgP
  exact not_both' X _ (wK X kv).isPrime.ne_top hk h1 h0

end Formalism.L2.SG.Pf.KppChar
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.RedBasicsPf

variable {D : D7} (X : HidaSetting D)

theorem g_pos : 0 < X.B.g := by
  rw [X.g_eq]; exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem divN_add (a b : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    divN X.B.I X.B.g (a + b) = divN X.B.I X.B.g a + divN X.B.I X.B.g b := by
  unfold divN; ring

theorem divN_g (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    divN X.B.I X.B.g ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * c) = c := by
  unfold divN
  have hg : ((X.B.g : ℕ) : X.B.I.F) ≠ 0 := Nat.cast_ne_zero.2 (g_pos X).ne'
  rw [← mul_assoc, ← map_natCast (algebraMap X.B.I.F (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)), ← map_mul,
    inv_mul_cancel₀ hg, map_one, one_mul]

theorem psi_modg (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) {d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hd : d ∈ IntAf X.B.I.F X.B.I.E) :
    X.psiEf (divN X.B.I X.B.g (c + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * d)) = X.psiEf (divN X.B.I X.B.g c) := by
  rw [divN_add, X.psiEf_add, divN_g, X.psiEf_int d hd, mul_one]

theorem divN_incl (y : X.B.I.E) : divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y) =
    Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((X.B.g : ℕ) : X.B.I.E)⁻¹ * y) := by
  unfold divN
  rw [Algebra.TensorProduct.algebraMap_apply, map_mul]
  congr 1
  show algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) ⊗ₜ[X.B.I.F] (1 : Af X.B.I.F) =
    Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((X.B.g : ℕ) : X.B.I.E)⁻¹)
  rw [map_inv₀, map_natCast]
  rfl

theorem psiEinf_star (y : X.B.I.E) : psiEinf X.B.I (star y) = psiEinf X.B.I y := by
  unfold psiEinf
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [X.B.I.cm.cmUnram.2.1 (X.B.I.φ v) y]
  congr 2
  simp only [starRingEnd_apply, star_star]
  ring

theorem psi_incl_star (y : X.B.I.E) :
    X.psiEf (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (star y)) =
      X.psiEf (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y) := by
  have h1 := X.psiEf_rat (star y)
  have h2 := X.psiEf_rat y
  rw [psiEinf_star] at h1
  have hne : psiEinf X.B.I y ≠ 0 := by intro h; rw [h, mul_zero] at h2; exact zero_ne_one h2
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

theorem psi_sig (ε : 𝓞 X.B.I.E) (m : ℕ) :
    X.psiEf (divN X.B.I X.B.g (iE X.B.I (sigO X.B.I ε) * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) =
      X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := by
  have e : ∀ a : 𝓞 X.B.I.E, iE X.B.I a * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((a : X.B.I.E) * m) := by
    intro a; rw [map_mul, map_natCast]
  rw [e, e, divN_incl, divN_incl, sigO_coe]
  have : ((X.B.g : ℕ) : X.B.I.E)⁻¹ * (star (ε : X.B.I.E) * m) = star (((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) * m)) := by
    rw [star_mul, star_mul, star_inv₀, star_natCast, star_natCast]; ring
  rw [this, psi_incl_star]

variable {kv : Σ k : Fin 2, D.nd.PlG k}

theorem g_split_mul {k k' : Fin 2} (hk : k' ≠ k) :
    ((D.host.g k : ℕ) : 𝓞 X.B.I.E) * ((D.host.g k' : ℕ) : 𝓞 X.B.I.E) = ((X.B.g : ℕ) : 𝓞 X.B.I.E) := by
  rw [g_eq_cast]
  fin_cases k <;> fin_cases k'
  · exact absurd rfl hk
  · rfl
  · exact mul_comm _ _
  · exact absurd rfl hk

theorem other_ne (k : Fin 2) : (1 - k) ≠ k := by fin_cases k <;> decide

theorem psi_period {ε : 𝓞 X.B.I.E} (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)}) (m q : ℕ) :
    X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * ((m + D.host.g kv.1 * q : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) =
      X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := by
  obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.1 hε
  have e : iE X.B.I ε * ((m + D.host.g kv.1 * q : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I δ * q) := by
    have hg : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
        iE X.B.I (((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) * ((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)) := by
      rw [g_split_mul X (other_ne kv.1)]; simp [iE]
    rw [hg, ← hδ]
    simp only [iE, map_mul, map_natCast, Nat.cast_add, Nat.cast_mul]
    ring
  rw [e, psi_modg X _ (mul_mem (iE_int X.B.I δ) (natCast_mem _ q))]

def psiK (ε : 𝓞 X.B.I.E) (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)}) :
    AddChar (ZMod (D.host.g kv.1)) ℂ where
  toFun t := X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)))
  map_zero_eq_one' := by
    simp only [ZMod.val_zero, Nat.cast_zero, mul_zero]
    unfold divN; rw [mul_zero]; exact X.psiEf_int 0 (zero_mem _)
  map_add_eq_mul' a b := by
    have : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
    have hval : a.val + b.val = (a + b).val + D.host.g kv.1 * ((a.val + b.val) / D.host.g kv.1) := by
      rw [ZMod.val_add]; exact (Nat.mod_add_div _ _).symm
    rw [← psi_period X hε (a + b).val ((a.val + b.val) / D.host.g kv.1), ← hval, Nat.cast_add, mul_add, divN_add,
      X.psiEf_add]

theorem psiK_apply (ε : 𝓞 X.B.I.E) (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)})
    (t : ZMod (D.host.g kv.1)) :
    psiK X ε hε t = X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := rfl

end Formalism.L2.SG.Pf.KppChar
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.RedBasicsPf

variable {D : D7} (X : HidaSetting D) {kv : Σ k : Fin 2, D.nd.PlG k}

theorem level_mem_wB' (kv : Σ k : Fin 2, D.nd.PlG k) : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal :=
  g_mem_of_gk X (gk_mem X kv)

theorem psiK_ne {ε : 𝓞 X.B.I.E} (hε1 : ε - 1 ∈ (wK X kv).asIdeal)
    (hεP : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv → ε ∈ P.asIdeal)
    (hε : ε ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)}) : psiK X ε hε ≠ 1 := by
  intro h1
  have hp := D.host.g_prime kv.1
  have : NeZero (D.host.g kv.1) := ⟨hp.ne_zero⟩

  have hm : ∀ m : ℕ, X.psiEf (divN X.B.I X.B.g (iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) = 1 := by
    intro m
    have h2 := congrArg (fun ψ : AddChar (ZMod (D.host.g kv.1)) ℂ => ψ (m : ZMod (D.host.g kv.1))) h1
    simp only [psiK_apply, AddChar.one_apply, ZMod.val_natCast] at h2
    rw [← psi_period X hε (m % D.host.g kv.1) (m / D.host.g kv.1), Nat.mod_add_div] at h2
    exact h2

  have hb : ∀ b : 𝓞 X.B.I.F, X.psiEf (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) * ((algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) b : 𝓞 X.B.I.E) : X.B.I.E)))) = 1 := by
    intro b
    set bE : 𝓞 X.B.I.E := algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) b
    obtain ⟨c, hc⟩ := int_surj X.B.I (wK X kv) hp (card_wK X kv) (Ideal.Quotient.mk _ bE)
    set m : ℕ := ((c : ZMod (D.host.g kv.1)).val : ℕ)
    have hbm : bE - (m : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
      have h1' : bE - (c : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, hc, sub_self]
      have h2' : ((c : 𝓞 X.B.I.E) - (m : 𝓞 X.B.I.E)) ∈ (wK X kv).asIdeal := by
        have : ((c - (m : ℤ) : ℤ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
          rw [int_mem_iff X.B.I (wK X kv) hp (card_wK X kv), ← ZMod.intCast_eq_intCast_iff_dvd_sub]
          simp [m]
        simpa using this
      have := add_mem h1' h2'
      simpa using this
    have hall : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal →
        ε * (bE - (m : 𝓞 X.B.I.E)) ∈ P.asIdeal := by
      intro P hP
      by_cases hPw : P = wK X kv
      · rw [hPw]; exact Ideal.mul_mem_left _ _ hbm
      · exact Ideal.mul_mem_right _ _ (hεP P hP hPw)
    obtain ⟨c', hc'⟩ := mem_g_of_all X hall
    have e : iE X.B.I (ε * bE) = iE X.B.I ε * (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * iE X.B.I c' := by
      have : ε * bE = ε * (m : 𝓞 X.B.I.E) + ((X.B.g : ℕ) : 𝓞 X.B.I.E) * c' := by rw [← hc']; ring
      rw [this]; simp [iE]
    have h3 := hm m
    rw [← psi_modg X _ (iE_int X.B.I c'), ← e] at h3
    have e2 : iE X.B.I (ε * bE) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((ε : X.B.I.E) * (bE : X.B.I.E)) := by
      simp [iE]
    rw [e2, divN_incl] at h3
    exact h3

  set τ := PI.ScPsiExists.UnitaryGroupMassFormula.tau X.B.I.cm.fixed
  set y : X.B.I.F := (((X.B.g : ℕ) : X.B.I.F))⁻¹ * τ (ε : X.B.I.E)
  have htr : ∀ z : 𝓞 X.B.I.F, ∃ n : ℤ, Algebra.trace ℚ X.B.I.F (y * algebraMap (𝓞 X.B.I.F) X.B.I.F z) = n := by
    intro z
    have h4 := X.psiEf_rat (((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) *
      ((algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) z : 𝓞 X.B.I.E) : X.B.I.E)))
    rw [hb z, one_mul] at h4
    obtain ⟨n, hn⟩ := PsiCondAllPf.trace_of_psi X.B.I _ h4
    refine ⟨n, ?_⟩
    rw [← hn]
    congr 1
    have hz : ((algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) z : 𝓞 X.B.I.E) : X.B.I.E) =
        algebraMap X.B.I.F X.B.I.E (algebraMap (𝓞 X.B.I.F) X.B.I.F z) := rfl
    have e3 : ((X.B.g : ℕ) : X.B.I.E)⁻¹ * ((ε : X.B.I.E) * algebraMap X.B.I.F X.B.I.E (algebraMap (𝓞 X.B.I.F) X.B.I.F z)) =
        (((X.B.g : ℕ) : X.B.I.F)⁻¹ * algebraMap (𝓞 X.B.I.F) X.B.I.F z) • (ε : X.B.I.E) := by
      rw [Algebra.smul_def, map_mul, map_inv₀, map_natCast]; ring
    rw [hz, e3, LinearMap.map_smul, smul_eq_mul]
    ring

  let v : HeightOneSpectrum (𝓞 X.B.I.F) :=
    { asIdeal := (wK X kv).asIdeal.comap (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro hbot
        have h5 : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.F) ∈ (wK X kv).asIdeal.comap (algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E)) := by
          rw [Ideal.mem_comap, map_natCast]; exact gk_mem X kv
        rw [hbot] at h5
        exact (by exact_mod_cast hp.ne_zero : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.F) ≠ 0) ((Submodule.mem_bot _).1 h5) }
  have hv : ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := by
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]; exact gk_mem X kv
  have hun : Algebra.IsUnramifiedAt ℤ v.asIdeal := by
    letI : Algebra X.B.I.F D.host.E := (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).toAlgebra
    exact PsiCondAllPf.unram_of (D.host.g kv.1) hp v hv
      (Formalism.L2.SG.Pf.TypedLoc.tower_ef X.B.I.F D.host.E hp (D.nd.g_split kv.1) v hv).1
  obtain ⟨d, hd, hdv⟩ := PsiCondAllPf.exists_diff_not_mem v hun
  obtain ⟨c, hc⟩ := PsiCondAllPf.mul_diff_int y htr d hd
  obtain ⟨t, ht⟩ := PI.ScPsiExists.UnitaryGroupMassFormula.tau_int X.B.I.cm.fixed ε

  have hgc : ((X.B.g : ℕ) : 𝓞 X.B.I.F) * c = t * d := by
    apply FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) X.B.I.F
    have hg0 : ((X.B.g : ℕ) : X.B.I.F) ≠ 0 := Nat.cast_ne_zero.2 (g_pos X).ne'
    rw [map_mul, map_mul, hc, ht, map_natCast]
    show (X.B.g : X.B.I.F) * ((((X.B.g : ℕ) : X.B.I.F))⁻¹ * τ (ε : X.B.I.E) * _) = τ (algebraMap (𝓞 X.B.I.E) X.B.I.E ε) * _
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hg0, one_mul]
  have htd : t * d ∈ v.asIdeal := by
    rw [← hgc]
    refine Ideal.mul_mem_right _ _ ?_
    show _ ∈ Ideal.comap _ _
    rw [Ideal.mem_comap, map_natCast]
    exact g_mem_of_gk X (gk_mem X kv)
  have htv : t ∈ v.asIdeal := (v.isPrime.mem_or_mem htd).resolve_right hdv

  have htw : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) t ∈ (wK X kv).asIdeal := htv
  have hte : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) t = ε + sigO X.B.I ε := by
    apply RingOfIntegers.ext
    show algebraMap X.B.I.F X.B.I.E (algebraMap (𝓞 X.B.I.F) X.B.I.F t) = (ε : X.B.I.E) + star (ε : X.B.I.E)
    rw [ht, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply]
  have hsig : sigO X.B.I ε ∈ (wK X kv).asIdeal := by
    have : ε ∈ (wc X.B.I (wK X kv)).asIdeal :=
      hεP _ (natCast_mem_wc X.B.I (level_mem_wB' X kv)) (wK_ne_wc X kv kv).symm
    rwa [mem_wc] at this
  rw [hte] at htw
  have h1w : (1 : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := by
    have := sub_mem (sub_mem htw hε1) hsig
    convert this using 1; ring
  exact (wK X kv).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1w)

end Formalism.L2.SG.Pf.KppChar
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppChar

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.AllRowsRedKerA
  Formalism.L2.SG.Pf.AllRowsRedKer Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.RedBasicsPf

variable {D : D7} (X : HidaSetting D)

theorem Wq_of_congW_zero {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {t : I.E ⊗[I.F] Af I.F} (h : CongW (w := w) p t 0) : t ∈ Wq I w := by
  obtain ⟨c, hc, ht⟩ := h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc
  obtain ⟨q, rfl⟩ := hc
  have : ((((p : ℤ) * q : ℤ)) : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    push_cast
    exact Wq_mul' (natCast_Wq hp hcard) (intCast_mem _ q)
  have := add_mem ht this
  simpa using this

theorem psi_sum {ι : Type*} (s : Finset ι) (f : ι → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) :
    X.psiEf (divN X.B.I X.B.g (∑ i ∈ s, f i)) = ∏ i ∈ s, X.psiEf (divN X.B.I X.B.g (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    unfold divN; rw [mul_zero]; exact X.psiEf_int 0 (zero_mem _)
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, divN_add, X.psiEf_add, ih]

theorem congW_iE {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} {a : 𝓞 I.E} {m : ℤ}
    (h : a - (m : 𝓞 I.E) ∈ w.asIdeal) : CongW (w := w) p (iE I a) (m : ZMod p) := by
  refine ⟨m, rfl, ?_⟩
  have := iE_mem (I := I) h
  simpa [iE] using this

variable (ε : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), 𝓞 X.B.I.E)

theorem chi_split (hε1 : ∀ kv, ε kv - 1 ∈ (wK X kv).asIdeal)
    (hεP : ∀ kv (P : HeightOneSpectrum (𝓞 X.B.I.E)), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → P ≠ wK X kv →
      ε kv ∈ P.asIdeal)
    (hε : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ε kv ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)})
    (hn : 0 < X.B.I.n) {C : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (hC : C ∈ IntAf X.B.I.F X.B.I.E)
    (t1 t2 : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1))
    (h1 : ∀ kv, CongW (w := wK X kv) (D.host.g kv.1) C (t1 kv))
    (h2 : ∀ kv, CongW (w := wc X.B.I (wK X kv)) (D.host.g kv.1) C (t2 kv)) :
    X.psiEf (divN X.B.I X.B.g C) = ∏ kv, psiK X (ε kv) (hε kv) (t1 kv + t2 kv) := by
  classical
  set T : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := ∑ kv, (iE X.B.I (ε kv) * (((t1 kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
    iE X.B.I (sigO X.B.I (ε kv)) * (((t2 kv).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) with hT
  have hTint : T ∈ IntAf X.B.I.F X.B.I.E :=
    sum_mem fun kv _ => add_mem (mul_mem (iE_int _ _) (natCast_mem _ _)) (mul_mem (iE_int _ _) (natCast_mem _ _))

  have hgP : ∀ kv, ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wK X kv).asIdeal := fun kv => level_mem_wB' X kv
  have hgPc : ∀ kv, ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ (wc X.B.I (wK X kv)).asIdeal :=
    fun kv => natCast_mem_wc X.B.I (level_mem_wB' X kv)
  have hΔ : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → C - T ∈ Wq X.B.I P := by
    intro P hP
    obtain ⟨kv0, hP0 | hP0⟩ := over_g X P hP
    · subst hP0
      have hp := D.host.g_prime kv0.1
      have : NeZero (D.host.g kv0.1) := ⟨hp.ne_zero⟩
      have hTc : CongW (w := wK X kv0) (D.host.g kv0.1) T (t1 kv0) := by
        have h3 : CongW (w := wK X kv0) (D.host.g kv0.1) T
            (∑ kv, ((if kv = kv0 then 1 else 0) * (((t1 kv).val : ℕ) : ZMod (D.host.g kv0.1)) +
              0 * (((t2 kv).val : ℕ) : ZMod (D.host.g kv0.1)))) := by
          refine congW_sum _ fun kv _ => congW_add ?_ ?_
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            by_cases hk : kv = kv0
            · subst hk
              rw [if_pos rfl]
              have := congW_iE (p := D.host.g kv.1) (m := 1) (by simpa using hε1 kv)
              simpa using this
            · rw [if_neg hk]
              have := congW_iE (p := D.host.g kv0.1) (m := 0)
                (by simpa using hεP kv (wK X kv0) (hgP kv0) (wK_ne X (Ne.symm hk)))
              simpa using this
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            have hm : ε kv ∈ (wc X.B.I (wK X kv0)).asIdeal := hεP kv _ (hgPc kv0) (wK_ne_wc X kv kv0).symm
            rw [mem_wc] at hm
            have := congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)
            simpa using this
        convert h3 using 1
        simp [Finset.sum_ite_eq']
      have := congW_sub (h1 kv0) hTc
      rw [sub_self] at this
      exact Wq_of_congW_zero hp (card_wK X kv0) this
    · subst hP0
      have hp := D.host.g_prime kv0.1
      have : NeZero (D.host.g kv0.1) := ⟨hp.ne_zero⟩
      have hTc : CongW (w := wc X.B.I (wK X kv0)) (D.host.g kv0.1) T (t2 kv0) := by
        have h3 : CongW (w := wc X.B.I (wK X kv0)) (D.host.g kv0.1) T
            (∑ kv, (0 * (((t1 kv).val : ℕ) : ZMod (D.host.g kv0.1)) +
              (if kv = kv0 then 1 else 0) * (((t2 kv).val : ℕ) : ZMod (D.host.g kv0.1)))) := by
          refine congW_sum _ fun kv _ => congW_add ?_ ?_
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            have hm : ε kv ∈ (wc X.B.I (wK X kv0)).asIdeal := hεP kv _ (hgPc kv0) (wK_ne_wc X kv kv0).symm
            have := congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)
            simpa using this
          · refine congW_mul (natCast_mem _ _) ?_ (congW_natCast _)
            by_cases hk : kv = kv0
            · subst hk
              rw [if_pos rfl]
              have hm : sigO X.B.I (ε kv) - 1 ∈ (wc X.B.I (wK X kv)).asIdeal := by
                rw [mem_wc, map_sub, sigO_sigO, map_one]; exact hε1 kv
              have := congW_iE (p := D.host.g kv.1) (m := 1) (by simpa using hm)
              simpa using this
            · rw [if_neg hk]
              have hm : sigO X.B.I (ε kv) ∈ (wc X.B.I (wK X kv0)).asIdeal := by
                rw [mem_wc, sigO_sigO]; exact hεP kv (wK X kv0) (hgP kv0) (wK_ne X (Ne.symm hk))
              have := congW_iE (p := D.host.g kv0.1) (m := 0) (by simpa using hm)
              simpa using this
        convert h3 using 1
        simp [Finset.sum_ite_eq']
      have := congW_sub (h2 kv0) hTc
      rw [sub_self] at this
      exact Wq_of_congW_zero hp (card_wKc X kv0) this

  obtain ⟨a, r', hr', hr⟩ := PIW.AdelClassFin.dual_dense X.B.I.F X.B.I.E X.B.g (g_pos X) (C - T) (sub_mem hC hTint)
  have ha : ∀ P : HeightOneSpectrum (𝓞 X.B.I.E), ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ P.asIdeal → a ∈ P.asIdeal := by
    intro P hP
    have hgW : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ Wq X.B.I P := by
      have := iE_mem (I := X.B.I) hP; simpa [iE] using this
    have hiE : iE X.B.I a ∈ Wq X.B.I P := by
      have := sub_mem (hΔ P hP) (Wq_mul' hgW hr')
      rw [hr] at this
      simpa [iE] using this
    obtain ⟨kv0, hP0 | hP0⟩ := over_g X P hP
    · subst hP0; exact int_of_Wq (D.host.g_prime kv0.1) (card_wK X kv0) hn hiE
    · subst hP0; exact int_of_Wq (D.host.g_prime kv0.1) (card_wKc X kv0) hn hiE
  obtain ⟨c, hc⟩ := mem_g_of_all X ha
  have hCT : C = T + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I c + r') := by
    have : C - T = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (iE X.B.I c + r') := by
      rw [hr, hc]; simp [iE]; ring
    rw [← this]; ring
  rw [hCT, psi_modg X _ (add_mem (iE_int _ c) hr'), hT, psi_sum]
  refine Finset.prod_congr rfl fun kv _ => ?_
  rw [divN_add, X.psiEf_add, psi_sig, AddChar.map_add_eq_mul, psiK_apply, psiK_apply]

end Formalism.L2.SG.Pf.KppChar
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppFwdPf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.RowDictPf
  PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW
  Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx Formalism.L2.SG.Pf.KppLoc Formalism.L2.SG.Pf.KppChar Formalism.L2.SG.Pf.AllRowsRho
  Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsKpp

variable {D : D7} (X : HidaSetting D)

theorem n_pos : 0 < X.B.I.n := by
  rw [X.n_eq, hrD D]
  omega

theorem Wq_of_smul {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hn : 0 < I.n) {t : I.E ⊗[I.F] Af I.F} (ht : t ∈ IntAf I.F I.E)
    (h : ∀ y ∈ I.Lf, t • y ∈ Lq I w) : t ∈ Wq I w := by
  obtain ⟨m, c, -, hc⟩ := congW_exists hp hcard ht
  have hcy : ∀ y ∈ I.Lf, ((c : ℤ) : I.E ⊗[I.F] Af I.F) • y ∈ Lq I w := by
    intro y hy
    have h1 := (Lq I w).sub_mem (h y hy) (Wq_smul hc hy)
    rwa [sub_smul, sub_sub_cancel] at h1
  obtain ⟨b, hb⟩ := Formalism.L2.SG.Pf.RedBasicsPf.exists_redBasis I w hp hcard
  set i0 : Fin I.n := ⟨0, hn⟩
  have hv : iv I (∑ j, (((Pi.single i0 c : Fin I.n → ℤ) j : ℤ) : I.E) • b j) ∈ lamAf (F := I.F) (wLat0 I w) := by
    rw [iv_sum_int]
    have hs : ∑ j, (((Pi.single i0 c : Fin I.n → ℤ) j : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) =
        ((c : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b i0) := by
      rw [Finset.sum_eq_single i0]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h0
        exact absurd (Finset.mem_univ _) h0
    rw [hs]
    exact hcy _ (Submodule.subset_span ⟨⟨b i0, hb.1 i0⟩, rfl⟩)
  have hdvd : (p : ℤ) ∣ c := by
    have := Formalism.L2.SG.Pf.RedBasicsPf.redBasis_indep I w hp hcard hb (Pi.single i0 c : Fin I.n → ℤ)
      (Formalism.L2.SG.Pf.RedBasicsPf.inter I w hv) i0
    simpa using this
  obtain ⟨k, rfl⟩ := hdvd
  have hcW : ((p * k : ℤ) : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    push_cast
    exact Wq_mul' (natCast_Wq hp hcard) (intCast_int k)
  have := (Wq I w).add_mem hc hcW
  simpa using this

private theorem congW_sub_mem_of_prime_residue_card {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {t : I.E ⊗[I.F] Af I.F} {c : ℕ}
    (h : CongW (w := w) p t (c : ZMod p)) : t - (c : I.E ⊗[I.F] Af I.F) ∈ Wq I w :=
  Wq_of_congW_zero hp hcard (by simpa using congW_sub h (congW_natCast (w := w) (p := p) c))

theorem ew_res (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ ob : Bool, X.ew - (if ob then 1 else 0) ∈ Wq X.B.I (wK X kv) ∧
      sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I (wK X kv) := by
  have hp := D.host.g_prime kv.1
  have hcard := card_wK X kv
  have hn := n_pos X
  have : Fact (D.host.g kv.1).Prime := ⟨hp⟩
  have hsI : sg X.B.I X.ew ∈ IntAf X.B.I.F X.B.I.E := by
    obtain ⟨m0, c, -, hc⟩ := congW_exists (w := wc X.B.I (wK X kv)) hp (card_wKc X kv) X.ew_int
    have h1 := sg_Wq hc
    rw [wc_wc, map_sub, sg_intCast] at h1
    have h2 := (IntAf X.B.I.F X.B.I.E).add_mem (Wq_int h1) (intCast_int c)
    simpa using h2
  have hA : 1 - X.ew - sg X.B.I X.ew ∈ Wq X.B.I (wK X kv) := by
    refine Wq_of_smul hp hcard hn ?_ ?_
    · exact (IntAf X.B.I.F X.B.I.E).sub_mem
        ((IntAf X.B.I.F X.B.I.E).sub_mem (IntAf X.B.I.F X.B.I.E).one_mem X.ew_int) hsI
    · intro y hy
      exact mL_le (level_mem_wB' X kv) (X.ew_full y hy)
  have key : ∀ ob : Bool, sg X.B.I X.ew - (if ob then 0 else 1) =
      -(1 - X.ew - sg X.B.I X.ew) - (X.ew - (if ob then 1 else 0)) := by
    intro ob
    cases ob <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
  obtain ⟨m, hm⟩ := congW_exists (w := wK X kv) hp hcard X.ew_int
  have hmm : m * m = m := by
    have h1 := congW_mul X.ew_int hm hm
    rw [X.ew_idem] at h1
    exact congW_unique hp hcard hn h1 hm
  have h01 : m = 0 ∨ m = 1 := by
    have h1 : m * (m - 1) = 0 := by rw [mul_sub, mul_one, hmm, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hfin : ∀ ob : Bool, X.ew - (if ob then 1 else 0) ∈ Wq X.B.I (wK X kv) →
      ∃ ob : Bool, X.ew - (if ob then 1 else 0) ∈ Wq X.B.I (wK X kv) ∧
        sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I (wK X kv) := by
    intro ob hob
    refine ⟨ob, hob, ?_⟩
    rw [key ob]
    exact (Wq X.B.I (wK X kv)).sub_mem ((Wq X.B.I (wK X kv)).neg_mem hA) hob
  rcases h01 with h0 | h1
  · refine hfin false ?_
    have := congW_sub_mem_of_prime_residue_card hp hcard (c := 0) (by simpa [h0] using hm)
    simpa using this
  · refine hfin true ?_
    have := congW_sub_mem_of_prime_residue_card hp hcard (c := 1) (by simpa [h1] using hm)
    simpa using this

private theorem exists_conj_rhoX_JPred_of_mem_K2 (kv : Σ k : Fin 2, D.nd.PlG k) :
    ∃ Pm : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), ∀ x : KSub X.B.I, (x : X.B.I.Gf) ∈ X.K2 →
      JPred D.R.k D.R.rS ((Pm⁻¹ * rhoX X x kv * Pm : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) ∧
      ∃ t1 t2 : ZMod (D.host.g kv.1), CongW (w := wK X kv) (D.host.g kv.1) (argC X x) t1 ∧
        CongW (w := wc X.B.I (wK X kv)) (D.host.g kv.1) (argC X x) t2 ∧
        t1 + t2 = phiJ D.R.k D.R.rS ((Pm⁻¹ * rhoX X x kv * Pm : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  have hp := D.host.g_prime kv.1
  have hcard := card_wK X kv
  have hn := n_pos X
  have hg := level_mem_wB' X kv
  have : NeZero (D.host.g kv.1) := ⟨hp.ne_zero⟩
  obtain ⟨ob, hew, hsew⟩ := ew_res X kv
  have hgr := gram X ob hg hew hsew
  obtain ⟨c, hc⟩ := exists_lifts hp hcard (fr_L X ob)
  have hcL : ∀ j, c j ∈ X.B.I.L := fun j => (hc j).1
  have hcq : ∀ j, fr X ob j - iv X.B.I (c j) ∈ Lq X.B.I (wK X kv) := fun j => (hc j).2
  have hgc := gram_lift (frd_L X ob) hgr hcq
  have hbc : IsRedBasis0 X.B.I (wK X kv) c :=
    isRedBasis_of_gram hp hcard X.n_eq.symm (frd_L X ob) hcL hgc
  obtain ⟨P0, Q0, hPQ, hQP, hconj⟩ := conj_basis hp hcard X.n_eq.symm (redBX X kv).hb hbc
  have hdd : (dM D.R.rS D.R.k ob : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) *
      dM D.R.rS D.R.k ob = 1 := dM_sq ob
  have hPm : ∃ Pm : GL (Fin D.R.r) (ZMod (D.host.g kv.1)),
      (Pm : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) = P0 * dM D.R.rS D.R.k ob ∧
      ((Pm⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) =
        dM D.R.rS D.R.k ob * Q0 := by
    refine ⟨⟨P0 * dM D.R.rS D.R.k ob, dM D.R.rS D.R.k ob * Q0, ?_, ?_⟩, rfl, rfl⟩
    · rw [mul_assoc, ← mul_assoc (dM D.R.rS D.R.k ob), hdd, one_mul, hPQ]
    · rw [mul_assoc, ← mul_assoc Q0, hQP, one_mul, hdd]
  obtain ⟨Pm, hPm1, hPm2⟩ := hPm
  refine ⟨Pm, fun x hx => ?_⟩
  have hxK : (x : X.B.I.Gf) ∈ X.B.I.Kset := hx.1
  have hxi : (x : X.B.I.Gf)⁻¹ ∈ X.K2 := (Formalism.L2.SG.Closed.level_subgroup_is_group X).2.2.1 _ hx
  have hxiK : (x : X.B.I.Gf)⁻¹ ∈ X.B.I.Kset := hxi.1
  have hM : RedMatB X.B.I (wK X kv) (D.host.g kv.1) (redBX X kv).b (x : X.B.I.Gf)
      ((rhoX X x kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
        Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
    rw [rhoX_apply]
    exact rhoB_spec (redBX X kv) x
  obtain ⟨N, hN⟩ := redMatB_exists X.B.I (wK X kv) hp hcard hbc hxK
  obtain ⟨N', hN'⟩ := redMatB_exists X.B.I (wK X kv) hp hcard hbc hxiK
  have hMN := hconj _ hxK _ N hM hN
  have hval : ((Pm⁻¹ * rhoX X x kv * Pm : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) =
      dM D.R.rS D.R.k ob * N * dM D.R.rS D.R.k ob := by
    rw [Units.val_mul, Units.val_mul, hPm1, hPm2]
    calc dM D.R.rS D.R.k ob * Q0 * ((rhoX X x kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
            Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) * (P0 * dM D.R.rS D.R.k ob)
        = dM D.R.rS D.R.k ob * Q0 * (((rhoX X x kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
            Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) * P0) * dM D.R.rS D.R.k ob := by
          simp only [mul_assoc]
      _ = dM D.R.rS D.R.k ob * (Q0 * P0) * N * dM D.R.rS D.R.k ob := by
          rw [hMN]
          simp only [mul_assoc]
      _ = dM D.R.rS D.R.k ob * N * dM D.R.rS D.R.k ob := by
          rw [hQP, mul_one]
  have hW := entry (frd_L X ob) hcL hcq hgc hxK hN
  have hW' := entry (frd_L X ob) hcL hcq hgc hxiK hN'
  have hJ := shape X ob hg hew hsew hp hcard hn hx hW
  have hJ' := shape X ob hg hew hsew hp hcard hn hxi hW'
  have hmul : N * N' = 1 := by
    have h1 := redMatB_mul X.B.I (wK X kv) hp hcard hcL hxK hN hN'
    rw [mul_inv_cancel] at h1
    exact redMatB_unique X.B.I (wK X kv) hp hcard X.n_eq.symm hbc h1 (redMatB_one X.B.I (wK X kv) hp c)
  have hinv := inv_super hJ hJ' hmul
  rw [hval]
  exact ⟨jPred_conj (hrD D) ob hJ, tW (D := D) ob N, tWc (D := D) ob N', congC X ob hew hxK hW,
    congCc X ob hsew hxK hW', sum_eq ob hinv⟩

theorem kppFwd_holds : KppFwd X := by
  have hs : D.R.m / 2 - 1 = D.R.rS := by
    have h1 := r_eq D
    have h2 := hrD D
    omega
  choose Pm hPm using exists_conj_rhoX_JPred_of_mem_K2 X
  choose ε hε1 hεP using exists_eps X
  have hε : ∀ kv : (Σ k : Fin 2, D.nd.PlG k),
      ε kv ∈ Ideal.span {((D.host.g (1 - kv.1) : ℕ) : 𝓞 X.B.I.E)} :=
    fun kv => eps_other X kv (hεP kv) (1 - kv.1) (other_ne kv.1)
  unfold KppFwd
  refine ⟨Pm, fun kv => psiK X (ε kv) (hε kv), fun kv => psiK_ne X (hε1 kv) (hεP kv) (hε kv), ?_⟩
  intro x hx
  rw [hs]
  choose t1 t2 h1 h2 h12 using fun kv => (hPm kv x hx).2
  refine ⟨fun kv => (hPm kv x hx).1, ?_⟩
  rw [quadratic_character_eq_additive X (x : X.B.I.Gf), chi_split X ε hε1 hεP hε (n_pos X) (argC_int X hx.1) t1 t2 h1 h2]
  exact Finset.prod_congr rfl fun kv _ => by rw [h12 kv]

end Formalism.L2.SG.Pf.KppFwdPf
