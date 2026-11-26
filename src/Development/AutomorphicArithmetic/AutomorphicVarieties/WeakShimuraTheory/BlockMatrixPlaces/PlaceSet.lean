module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PlaceSet
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.placeSet :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (B : ValuationSubring Ω), (∀ p ∈ S, p.Prime) → l ∈ S → B.valuation (l : Ω) < 1 →
          ∃ (S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (Av : S' → ValuationSubring Ω) (v0 : S'), ContainsAbove S' l ∧ (∀ v, IsPlaceOver (Av v) v.1) ∧ Av v0 = B ∧ ((l : ℕ) : 𝓞 ℚ) ∈ v0.1.asIdeal ∧
            ∀ K : Subgroup (G ℚ Ω), K.Normal → IsClosed (K : Set (G ℚ Ω)) → (∀ A, Raw.Away S A → Ine (F := ℚ) A ≤ K) → NS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ K := by
  intro Ω _ _ _ l hl S B hS hlS hB
  classical
  have hfin : Set.Finite {v : HeightOneSpectrum (𝓞 ℚ) | ∃ p ∈ S, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} := by
    have e : {v : HeightOneSpectrum (𝓞 ℚ) | ∃ p ∈ S, ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal} =
        ⋃ p ∈ (S : Set ℕ), {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 ℚ)}} := by
      ext v
      simp [Ideal.dvd_span_singleton]
    rw [e]
    refine S.finite_toSet.biUnion fun p hp => Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (hS p hp).ne_zero
  obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.Base.places ℚ Ω l B
  obtain ⟨w, hw⟩ := h1 fun h => (h2 h).2 hB
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := (h3 w hw).1 hB
  have hex : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ (v = w → A = B) := by
    intro v
    by_cases e : v = w
    · exact ⟨B, e ▸ hw, fun _ => rfl⟩
    · obtain ⟨A, hA⟩ := (exists_isPlaceOver Ω v : ∃ A : ValuationSubring Ω, IsPlaceOver A v)
      exact ⟨A, hA, fun h => absurd h e⟩
  choose f hf hf' using hex
  refine ⟨hfin.toFinset, fun v => f v.1, ⟨w, hfin.mem_toFinset.2 ⟨l, hlS, hlw⟩⟩,
    fun v hv => hfin.mem_toFinset.2 ⟨l, hlS, hv⟩, fun v => hf v.1, hf' w rfl, hlw, fun K hK hc hI => ?_⟩
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc
  intro g hg
  simp only [Set.mem_iUnion] at hg
  obtain ⟨v, hv, A, hA, hg⟩ := hg
  refine hI A (fun p hp h => hv ?_) hg
  refine Finset.mem_coe.2 (hfin.mem_toFinset.2 ⟨p, hp, (hA ((p : ℕ) : 𝓞 ℚ)).1 ?_⟩)
  simpa using h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UMFacts
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private def uMat {R : Type} [CommRing R] (v : Fin 3 → R) : UpperTheory.V.GradeZeroInterpolatingElement.M4 R :=
  !![0, 0, 0, 0; v 0, 0, v 1, 0; 0, 0, 0, 0; v 2, 0, -v 0, 0]

private theorem uMat_mem {R : Type} [CommRing R] (v : Fin 3 → R) : uMat v ∈ uM R := by
  show uMat v ∈ hAB R ⊓ sp4 R
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · show ∀ i j, ¬ lamW i < lamW j → uMat v i j = 0
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [uMat, lamW]
  · show adj (uMat v) = -uMat v
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, uMat, Fin.rev]

private theorem uMat_eq {R : Type} [CommRing R] (Y : uM R) : uMat ![Y.1 1 0, Y.1 1 2, Y.1 3 0] = Y.1 := by
  obtain ⟨Y, hY⟩ := Y
  have hA := (Submodule.mem_inf.mp hY).1
  have hS := (Submodule.mem_inf.mp hY).2
  change ∀ i j, ¬ lamW i < lamW j → Y i j = 0 at hA
  change adj Y = -Y at hS
  have h32 := congrFun (congrFun hS 3) 2
  simp [adj_apply, sgn, Fin.rev] at h32
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat] <;> first
    | exact (hA _ _ (by decide)).symm
    | (rw [h32]; ring)
    | skip

private theorem uMat_add {R : Type} [CommRing R] (v w : Fin 3 → R) : uMat (v + w) = uMat v + uMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat] <;> ring

private theorem uMat_smul {R : Type} [CommRing R] (c : R) (v : Fin 3 → R) : uMat (c • v) = c • uMat v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

private def uEq (R : Type) [CommRing R] : (Fin 3 → R) ≃ₗ[R] uM R where
  toFun v := ⟨uMat v, uMat_mem v⟩
  map_add' v w := Subtype.ext (uMat_add v w)
  map_smul' c v := Subtype.ext (uMat_smul c v)
  invFun Y := ![Y.1 1 0, Y.1 1 2, Y.1 3 0]
  left_inv v := by
    ext i
    fin_cases i <;> rfl
  right_inv Y := Subtype.ext (uMat_eq Y)

theorem UpperTheory.V.Ws.Bl.uMFacts :
    ∀ (R : Type) [CommRing R], Module.Finite R (uM R) ∧ Module.Free R (uM R) ∧ ∀ (I : Ideal R) (Y : uM R), Y ∈ (I • ⊤ : Submodule R (uM R)) ↔ ∀ i j, Y.1 i j ∈ I := by
  intro R _
  refine ⟨Module.Finite.equiv (uEq R), Module.Free.of_equiv (uEq R), ?_⟩
  intro I Y
  constructor
  · intro hY i j
    refine Submodule.smul_induction_on hY ?_ ?_
    · intro r hr n _
      simpa using I.mul_mem_right (n.1 i j) hr
    · intro x y hx hy
      simpa using I.add_mem hx hy
  · intro h
    have hv : (uEq R).symm Y = ∑ k : Fin 3, ((uEq R).symm Y k) • Pi.single k 1 := by
      simpa using ((Pi.basisFun R (Fin 3)).sum_repr ((uEq R).symm Y)).symm
    have hY : Y = ∑ k : Fin 3, ((uEq R).symm Y k) • (uEq R) (Pi.single k 1) := by
      calc Y = uEq R ((uEq R).symm Y) := ((uEq R).apply_symm_apply Y).symm
        _ = _ := by
          conv_lhs => rw [hv]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          simp only [map_smul]
    rw [hY]
    refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem_smul ?_ Submodule.mem_top)
    fin_cases k
    · exact h 1 0
    · exact h 1 2
    · exact h 3 0
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.RedMem
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.redMem :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T) (n : ℕ) z y, IsZn ρ c N H P (n + 1) z y → IsZn ρ c N H P n (fun g => redn A T n (z g)) (redn A T n y) ∧
          (Prim z → 0 < n → Prim fun g => redn A T n (z g)) ∧ (Prim (fun g => redn A T n (z g)) → Prim z) := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P n z y hz
  have eqv : ∀ (g : Γ) (w : T ⧸ lev A T (n + 1)),
      redn A T n (modRep ρ (n + 1) g w) = modRep ρ n g (redn A T n w) := by
    intro g w
    obtain ⟨x, rfl⟩ := (lev A T (n + 1)).mkQ_surjective w
    rw [modRep_mk, redn_mk, redn_mk, modRep_mk]
  have img : ∀ (Q : Submodule A T) (w : T ⧸ lev A T (n + 1)), w ∈ Q.map (lev A T (n + 1)).mkQ →
      redn A T n w ∈ Q.map (lev A T n).mkQ := by
    rintro Q _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  refine ⟨⟨hz.lc.comp (redn A T n), fun g h => ?_, ?_, fun g hg => ?_, fun h hh => ?_⟩, ?_, ?_⟩
  · rw [hz.coc, map_add (f := _), eqv]
  · rw [hz.cz, map_zero]
  · rw [hz.kill g hg, map_zero]
  · have := img P _ (hz.loc h hh)
    rw [map_sub, map_sub, eqv] at this
    exact this
  · rintro ⟨g, hg⟩ hn
    refine ⟨g, fun hm => hg ?_⟩
    obtain ⟨x, hx⟩ := (lev A T (n + 1)).mkQ_surjective (z g)
    obtain ⟨x', hx', e⟩ := hm
    have e' : (lev A T n).mkQ x' = (lev A T n).mkQ x := by rw [e, ← redn_mk, hx]
    have hd : x' - x ∈ lev A T n := (Submodule.Quotient.eq _).1 e'
    have hle : lev A T n ≤ lev A T 1 := Submodule.smul_mono_left (Ideal.pow_le_pow_right hn)
    refine ⟨x, ?_, hx⟩
    have := (lev A T 1).sub_mem hx' (hle hd)
    rwa [sub_sub_cancel] at this
  · rintro ⟨g, hg⟩
    exact ⟨g, fun hm => hg (img _ _ hm)⟩
end
