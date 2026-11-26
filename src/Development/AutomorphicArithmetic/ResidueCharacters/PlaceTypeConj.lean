module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ResidueCharacters.PlaceTypeConj
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe GlobalTheory.SplitType GlobalTheory.SplitDecl

namespace UpperTheory.N

theorem place_type_conj (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i ≠ 2) (hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1)
    (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hw' : w' ∈ placesOver D.host.E (D.nd.l i)) (hc : IsConjPl D.host w w') :
    (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨
      (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  obtain ⟨s, hs, hn⟩ := exists_sqrt (D.nd.l i) D.host.d h2 hj
  obtain ⟨s₀, hs₀, h₀⟩ := exists_root
    ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[D.nd.l i] (D.nd.O i))) hs
    (map_sqrt_sq D.host ((D.nd.embK i).comp D.embE))
  have hs0 : s₀ ^ 2 = -(D.host.d : ℤ_[D.nd.l i]) := by rcases hs₀ with rfl | rfl <;> simp [hs]
  have hn0 : ‖2 * s₀‖ = 1 := by rcases hs₀ with rfl | rfl <;> simpa using hn
  have hne : s₀ ≠ -s₀ := fun e => by
    rw [show 2 * s₀ = 0 by linear_combination e] at hn0
    simp at hn0
  have key : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.nd.l i)),
      ∃ t : ℤ_[D.nd.l i], algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
        (D.nbr i v hv).j (algebraMap D.host.E D.nd.Om (D.host.sqd)) ∧
        ((t = s₀ ∧ PlIn (N := D.nd) D.nbr i true v hv) ∨ (t = -s₀ ∧ PlIn (N := D.nd) D.nbr i false v hv)) := by
    intro v hv
    obtain ⟨t, ht, h⟩ := exists_root
      ((algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i))).comp PadicInt.Coe.ringHom) hs0
      (map_sqrt_sq D.host ((D.nbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)))
    refine ⟨t, h, ?_⟩
    rcases ht with ht | ht
    · refine Or.inl ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact e.1
      · exact absurd (ht.symm.trans ((root_of_embIn D i v hv h₀ h τ).2 e.1)) hne
    · refine Or.inr ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact absurd (((root_of_embIn D i v hv h₀ h τ).1 e.1).symm.trans ht) hne
      · exact e.1
  obtain ⟨t, ht, h⟩ := key w hw
  obtain ⟨t', ht', h'⟩ := key w' hw'
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨e, h'⟩ | ⟨e, h'⟩
  · exact (root_ne D i w w' hw hw' hc hn0 ht (e ▸ ht')).elim
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact (root_ne D i w w' hw hw' hc (by simpa using hn0) ht (e ▸ ht')).elim

theorem columns_xor (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i ≠ 2) (hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1) (s : Bool) :
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
  intro w hw w' h
  have hw' := GlobalTheory.SplitCount.mem_placesOver_of_conj D.host hw h
  have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
  have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
  rcases place_type_conj D i h2 hj w w' hw hw' h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
  · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
  · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
  · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
  · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩

theorem decl_split (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i ≠ 2) (hj : jacobiSym (-(D.host.d : ℤ)) (D.nd.l i) = 1) (ep : Bool) :
    (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.ambTypeD (D := D) i ep := by
  have hl : D.nd.l i ≠ 0 := (D.nd.lPrime i).out.ne_zero
  have hx := columns_xor D i h2 hj ep
  refine ⟨⟨decl D i hl ep, ?_, ?_⟩, ?_⟩
  · intro v hv
    rw [mem_col, plTypeUe_iff]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hv, hv, h⟩⟩
  · intro v
    rw [mem_row]
    constructor
    · rintro ⟨hv, hnc⟩
      obtain ⟨v', hv', hc⟩ := GlobalTheory.SplitPlaces.exists_conjPl D.host _ v hv
      have hv'c : v' ∈ columns (N := D.nd) D.nbr i ep := by
        rcases hx v hv v' hc with h | h
        · exact absurd h.1 hnc
        · exact h.1
      exact ⟨v', (mem_col D i hl ep v').2 ⟨hv', hv'c⟩, GlobalTheory.Proof.ConjugatePlaces.isConjPl_symm hc⟩
    · rintro ⟨u, hu, hc⟩
      obtain ⟨hu, huc⟩ := (mem_col D i hl ep u).1 hu
      refine ⟨GlobalTheory.SplitCount.mem_placesOver_of_conj D.host hu hc, fun hvc => ?_⟩
      rcases hx u hu v hc with h | h
      · exact h.2 hvc
      · exact h.2 huc
  · intro u hu hU w hw hc τ₀ hτ
    have hnb : ∀ v hv τ, ¬ (EmbIn (N := D.nd) D.nbr i true v hv τ ∧ EmbIn (N := D.nd) D.nbr i false v hv τ) := by
      rintro v hv τ ⟨a, b⟩
      rcases embIn_xor D i v hv τ with h | h
      · exact h.2 b
      · exact h.2 a
    have hUin : ∀ τ, EmbIn (N := D.nd) D.nbr i ep u hu τ := fun τ => (embTypeUe_iff ep τ).1 (hU τ)
    have hwin : EmbIn (N := D.nd) D.nbr i ep w hw τ₀ := (embTypeUe_iff ep τ₀).1 hτ
    rcases place_type_conj D i h2 hj u w hu hw hc with ⟨hpu, hpw⟩ | ⟨hpu, hpw⟩ <;> cases ep
    · obtain ⟨τ⟩ := hpu.1
      exact hnb u hu τ ⟨hpu.2 τ, hUin τ⟩
    · exact hnb w hw τ₀ ⟨hwin, hpw.2 τ₀⟩
    · exact hnb w hw τ₀ ⟨hpw.2 τ₀, hwin⟩
    · obtain ⟨τ⟩ := hpu.1
      exact hnb u hu τ ⟨hUin τ, hpu.2 τ⟩

end UpperTheory.N

end
end

section -- merged from Development.AutomorphicArithmetic.ResidueCharacters.TwoDecl
section -- merged from Development.AutomorphicArithmetic.ResidueCharacters.TwoRoot
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe GlobalTheory.SplitType

namespace UpperTheory.N.Two

theorem norm_two {l : ℕ} [Fact l.Prime] (h2 : l = 2) : ‖(2 : ℤ_[l])‖ = 1 / 2 := by
  subst h2
  have := PadicInt.norm_p (p := 2)
  simpa using this

theorem exists_sqrt {l : ℕ} [Fact l.Prime] (h2 : l = 2) {d k : ℕ} (hk : d + 1 = 8 * k) :
    ∃ s : ℤ_[l], s ^ 2 = -(d : ℤ_[l]) := by
  have n2 := norm_two h2
  have hk' : (((1 : ℤ) ^ 2 + d : ℤ) : ℤ_[l]) = 2 * 2 * 2 * k := by
    have : ((d + 1 : ℕ) : ℤ_[l]) = ((8 * k : ℕ) : ℤ_[l]) := by rw [hk]
    push_cast at this ⊢
    linear_combination this
  obtain ⟨s, hs⟩ := Misc.isSquare_of_hensel l d 1 (by
    rw [hk', norm_mul, norm_mul, norm_mul, n2]
    have e : ((2 * 1 : ℤ) : ℤ_[l]) = 2 := by norm_num
    rw [e, n2]
    have := PadicInt.norm_le_one (k : ℤ_[l])
    nlinarith)
  exact ⟨s, by rw [sq, ← hs]; simp⟩

theorem exists_half {l : ℕ} [Fact l.Prime] (h2 : l = 2) {d k : ℕ} (hk : d + 1 = 8 * k) {t : ℤ_[l]}
    (ht : t ^ 2 = -(d : ℤ_[l])) : ∃ u : ℤ_[l], 2 * u = 1 + t ∧ u * (1 - u) = 2 * k := by
  have n2 := norm_two h2
  have hk' : (d : ℤ_[l]) + 1 = 8 * k := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[l]) hk
  have hp : (1 + t) * (1 - t) = 2 * (4 * k) := by linear_combination hk' - ht
  have small : ∀ z : ℤ_[l], ‖2 * z‖ < 1 := fun z => by
    rw [norm_mul, n2]
    have := PadicInt.norm_le_one z
    linarith
  have h1 : ‖1 + t‖ < 1 := by
    by_contra hn
    have e1 : ‖1 + t‖ = 1 := le_antisymm (PadicInt.norm_le_one _) (not_lt.1 hn)
    have e2 : ‖1 - t‖ < 1 := by
      have := small (4 * k)
      rwa [← hp, norm_mul, e1, one_mul] at this
    have e3 := PadicInt.nonarchimedean (1 - t) (2 * t)
    rw [show 1 - t + 2 * t = 1 + t by ring, e1] at e3
    exact absurd e3 (not_le.2 (max_lt e2 (small t)))
  obtain ⟨u, hu⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 h1
  have hu' : 2 * u = 1 + t := by rw [hu]; subst h2; norm_num
  refine ⟨u, hu', ?_⟩
  have h4 : (4 : ℤ_[l]) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  have : t = 2 * u - 1 := by linear_combination -hu'
  subst this
  linear_combination hp

variable (D : D7) (i : D.nd.Loc)

theorem root_ne (h2 : D.nd.l i = 2) (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hw' : w' ∈ placesOver D.host.E (D.nd.l i)) (hc : IsConjPl D.host w w') {t : ℤ_[D.nd.l i]}
    (hs : t ^ 2 = -(D.host.d : ℤ_[D.nd.l i]))
    (ht : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om (D.host.sqd)))
    (ht' : algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
      (D.nbr i w' hw').j (algebraMap D.host.E D.nd.Om (D.host.sqd))) : False := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 8 * k := ⟨(D.host.d + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩
  obtain ⟨u, hu, huk⟩ := exists_half h2 hk hs
  have hkE : (D.host.d : D.host.E) + 1 = 8 * k := by exact_mod_cast congrArg (Nat.cast : ℕ → D.host.E) hk
  set ω : D.host.E := (1 + D.host.sqd) / 2 with hω
  have hq : ω ^ 2 - ω + 2 * k = 0 := by
    have := sqrtE_sq D.host
    rw [hω]
    linear_combination (1 / 4 : D.host.E) * this - (1 / 4 : D.host.E) * hkE
  have hint : IsIntegral ℤ ω := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * k : ℤ), ?_, ?_⟩
    · monicity!
    · simpa using hq
  let β : 𝓞 D.host.E := ⟨ω, hint⟩
  have hβ : (β : D.host.E) = ω := rfl
  have hy : ((1 - β : 𝓞 D.host.E) : D.host.E) = 1 - ω := by simp [← hβ]
  have hconj : D.host.conj ω = 1 - ω := by
    rw [hω, map_div₀, map_add (f := _), map_one, conj_sqrtE, map_ofNat]; ring
  have huQ : (u : ℚ_[D.nd.l i]) = (1 + (t : ℚ_[D.nd.l i])) / 2 := by
    have := congrArg (fun z : ℤ_[D.nd.l i] => (z : ℚ_[D.nd.l i])) hu
    push_cast at this
    have e : ((2 : ℤ_[D.nd.l i]) : ℚ_[D.nd.l i]) = 2 := rfl
    rw [← this, e]
    field_simp
  have a1 : β ∈ w.asIdeal ↔ ‖u‖ < 1 := mem_iff_norm D i w hw β u (by
    rw [hβ, hω, huQ]; simp only [map_div₀, map_add (f := _), map_one, map_ofNat, ht])
  have a2 : 1 - β ∈ w'.asIdeal ↔ ‖1 - u‖ < 1 := mem_iff_norm D i w' hw' (1 - β) (1 - u) (by
    rw [hy, hω]; push_cast; rw [huQ]; simp only [map_sub, map_div₀, map_add (f := _), map_one, map_ofNat, ht'])
  have a3 : β ∈ w.asIdeal ↔ 1 - β ∈ w'.asIdeal := hc β (1 - β) (by rw [hy, hβ, hconj])
  have hiff : ‖u‖ < 1 ↔ ‖1 - u‖ < 1 := a1.symm.trans (a3.trans a2)
  have hprod : ‖u‖ * ‖1 - u‖ < 1 := by
    rw [← norm_mul, huk, norm_mul, norm_two h2]
    have := PadicInt.norm_le_one (k : ℤ_[D.nd.l i])
    linarith
  have b1 : ‖u‖ < 1 := by
    by_contra hn
    have e1 : ‖u‖ = 1 := le_antisymm (PadicInt.norm_le_one _) (not_lt.1 hn)
    rw [e1, one_mul] at hprod
    exact absurd (hiff.2 hprod) (by rw [e1]; exact lt_irrefl _)
  have h6 := PadicInt.nonarchimedean u (1 - u)
  rw [show u + (1 - u) = 1 by ring, norm_one] at h6
  exact absurd h6 (not_le.2 (max_lt b1 (hiff.1 b1)))

theorem place_type_conj (h2 : D.nd.l i = 2)
    (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hw' : w' ∈ placesOver D.host.E (D.nd.l i)) (hc : IsConjPl D.host w w') :
    (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨
      (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 8 * k := ⟨(D.host.d + 1) / 8, by have := D.host.hyp.2.2.2.1; omega⟩
  obtain ⟨s, hs⟩ := exists_sqrt h2 hk
  obtain ⟨s₀, hs₀, h₀⟩ := exists_root
    ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).comp (algebraMap ℤ_[D.nd.l i] (D.nd.O i))) hs
    (map_sqrt_sq D.host ((D.nd.embK i).comp D.embE))
  have hs0 : s₀ ^ 2 = -(D.host.d : ℤ_[D.nd.l i]) := by rcases hs₀ with rfl | rfl <;> simp [hs]
  have hne : s₀ ≠ -s₀ := fun e => by
    have h0 : s₀ = 0 := by
      have : (2 : ℤ_[D.nd.l i]) * s₀ = 0 := by linear_combination e
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    rw [h0] at hs0
    have : (D.host.d : ℤ_[D.nd.l i]) = 0 := by linear_combination hs0
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have key : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.nd.l i)),
      ∃ t : ℤ_[D.nd.l i], algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i)) (t : ℚ_[D.nd.l i]) =
        (D.nbr i v hv).j (algebraMap D.host.E D.nd.Om (D.host.sqd)) ∧
        ((t = s₀ ∧ PlIn (N := D.nd) D.nbr i true v hv) ∨ (t = -s₀ ∧ PlIn (N := D.nd) D.nbr i false v hv)) := by
    intro v hv
    obtain ⟨t, ht, h⟩ := exists_root
      ((algebraMap ℚ_[D.nd.l i] (Loc.Om (D.nd.l i))).comp PadicInt.Coe.ringHom) hs0
      (map_sqrt_sq D.host ((D.nbr i v hv).j.comp (algebraMap D.host.E D.nd.Om)))
    refine ⟨t, h, ?_⟩
    rcases ht with ht | ht
    · refine Or.inl ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact e.1
      · exact absurd (ht.symm.trans ((root_of_embIn D i v hv h₀ h τ).2 e.1)) hne
    · refine Or.inr ⟨ht, nonempty_emb D i v hv, fun τ => ?_⟩
      rcases embIn_xor D i v hv τ with e | e
      · exact absurd (((root_of_embIn D i v hv h₀ h τ).1 e.1).symm.trans ht) hne
      · exact e.1
  obtain ⟨t, ht, h⟩ := key w hw
  obtain ⟨t', ht', h'⟩ := key w' hw'
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rcases h' with ⟨e, h'⟩ | ⟨e, h'⟩
  · exact (root_ne D i h2 w w' hw hw' hc hs0 ht (e ▸ ht')).elim
  · exact Or.inl ⟨h, h'⟩
  · exact Or.inr ⟨h, h'⟩
  · exact (root_ne D i h2 w w' hw hw' hc (by simpa using hs0) ht (e ▸ ht')).elim

end UpperTheory.N.Two

end
end

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
open GlobalTheory.SplitRowProbe GlobalTheory.SplitType GlobalTheory.SplitDecl

namespace UpperTheory.N.Two

theorem columns_xor (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i = 2) (s : Bool) :
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ w', IsConjPl D.host w w' →
      Xor (w ∈ columns (N := D.nd) D.nbr i s) (w' ∈ columns (N := D.nd) D.nbr i s) := by
  intro w hw w' h
  have hw' := GlobalTheory.SplitCount.mem_placesOver_of_conj D.host hw h
  have n1 := GlobalTheory.SplitRowProbe.not_both_columns D i w hw
  have n2 := GlobalTheory.SplitRowProbe.not_both_columns D i w' hw'
  rcases Two.place_type_conj D i h2 w w' hw hw' h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases s
  · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h1, h3⟩⟩
  · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h3, h2⟩⟩
  · exact Or.inl ⟨⟨hw, h1⟩, fun ⟨_, h3⟩ => n2 ⟨h2, h3⟩⟩
  · exact Or.inr ⟨⟨hw', h2⟩, fun ⟨_, h3⟩ => n1 ⟨h3, h1⟩⟩

theorem decl_split (D : D7) (i : D.nd.Loc) (h2 : D.nd.l i = 2) (ep : Bool) :
    (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.ambTypeD (D := D) i ep := by
  have hl : D.nd.l i ≠ 0 := (D.nd.lPrime i).out.ne_zero
  have hx := columns_xor D i h2 ep
  refine ⟨⟨decl D i hl ep, ?_, ?_⟩, ?_⟩
  · intro v hv
    rw [mem_col, plTypeUe_iff]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hv, hv, h⟩⟩
  · intro v
    rw [mem_row]
    constructor
    · rintro ⟨hv, hnc⟩
      obtain ⟨v', hv', hc⟩ := GlobalTheory.SplitPlaces.exists_conjPl D.host _ v hv
      have hv'c : v' ∈ columns (N := D.nd) D.nbr i ep := by
        rcases hx v hv v' hc with h | h
        · exact absurd h.1 hnc
        · exact h.1
      exact ⟨v', (mem_col D i hl ep v').2 ⟨hv', hv'c⟩, GlobalTheory.Proof.ConjugatePlaces.isConjPl_symm hc⟩
    · rintro ⟨u, hu, hc⟩
      obtain ⟨hu, huc⟩ := (mem_col D i hl ep u).1 hu
      refine ⟨GlobalTheory.SplitCount.mem_placesOver_of_conj D.host hu hc, fun hvc => ?_⟩
      rcases hx u hu v hc with h | h
      · exact h.2 hvc
      · exact h.2 huc
  · intro u hu hU w hw hc τ₀ hτ
    have hnb : ∀ v hv τ, ¬ (EmbIn (N := D.nd) D.nbr i true v hv τ ∧ EmbIn (N := D.nd) D.nbr i false v hv τ) := by
      rintro v hv τ ⟨a, b⟩
      rcases embIn_xor D i v hv τ with h | h
      · exact h.2 b
      · exact h.2 a
    have hUin : ∀ τ, EmbIn (N := D.nd) D.nbr i ep u hu τ := fun τ => (embTypeUe_iff ep τ).1 (hU τ)
    have hwin : EmbIn (N := D.nd) D.nbr i ep w hw τ₀ := (embTypeUe_iff ep τ₀).1 hτ
    rcases Two.place_type_conj D i h2 u w hu hw hc with ⟨hpu, hpw⟩ | ⟨hpu, hpw⟩ <;> cases ep
    · obtain ⟨τ⟩ := hpu.1
      exact hnb u hu τ ⟨hpu.2 τ, hUin τ⟩
    · exact hnb w hw τ₀ ⟨hwin, hpw.2 τ₀⟩
    · exact hnb w hw τ₀ ⟨hpw.2 τ₀, hwin⟩
    · obtain ⟨τ⟩ := hpu.1
      exact hnb u hu τ ⟨hUin τ, hpu.2 τ⟩

end UpperTheory.N.Two

end
end
