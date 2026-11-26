module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.PowNeZero
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IsLiftMap
noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Fr

namespace UpperTheory.V.J

section Lift

variable {O R C : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
  [CommRing C] [Algebra O C] [IsCO O C]

private theorem map_max_le (f : R →ₐ[O] C) :
    (maximalIdeal R).map (f : R →+* C) ≤ maximalIdeal C := by
  refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
  show f a ∈ maximalIdeal C
  rw [← res_eq_zero_iff O C, res_map, res_eq_zero_iff]
  exact ha

private theorem adic_map {Γ : Type} [TopologicalSpace Γ] (f : R →ₐ[O] C) {u : Γ → R}
    (hu : AdicCont (maximalIdeal R) u) : AdicCont (maximalIdeal C) fun g => f (u g) := by
  intro N
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal C ^ N).comap (f : R →+* C) := by
    refine Ideal.map_le_iff_le_comap.1 ?_
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_max_le f) N
  exact (hu N).comp (Ideal.quotientMap (maximalIdeal C ^ N) (f : R →+* C) hle)

variable {l : ℕ} [Fact l.Prime] {F : Frame l (ResidueField O)} {n : ℕ}

private theorem isLift_map (f : R →ₐ[O] C) {ρ : NRep F n R} (h : UpperTheory.V.Fr.IsLift O ρ) :
    UpperTheory.V.Fr.IsLift O (ρ.map (f : R →+* C)) := by
  obtain ⟨hc, hb, hd⟩ := h
  have hres : ((res O C : C →ₐ[O] ResidueField O) : C →+* ResidueField O).comp (f : R →+* C) =
      ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O) := by
    ext x
    exact res_map f x
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ?_, ?_⟩
  · exact adic_map f (hc.1 i j)
  · exact adic_map f (hc.2 v i)
  · rw [NRep.map_map, hres]
    exact hb
  · rw [NRep.map_map, hres]
    exact hd

end Lift

theorem det : Det := by
  intro l _ O _ _ _ _ F n S ξ D hD hr hψ
  haveI hc : IsAdicComplete (maximalIdeal O) O := UpperTheory.V.Fr.IsCoef.complete (l := l)
  haveI hn : IsNoetherianRing O := PrincipalIdealRing.isNoetherianRing
  haveI : IsCO O O := IsCO.self O
  haveI : IsCO O (TrivSqZeroExt O O) := co_sqz O O O (fun c => rfl)
  obtain ⟨y, hy⟩ := (der_hom O S.R O O ξ D).1 ⟨D, hD, rfl⟩
  let z : S.R →ₐ[O] TrivSqZeroExt O O := (TrivSqZeroExt.inlAlgHom O O O).comp ξ
  have key : ∀ a : S.R, D a = 0 → y a = z a := fun a ha =>
    TrivSqZeroExt.ext (hy a).1 (by rw [(hy a).2, ha]; rfl)
  have hmap : NRep.map (y : S.R →+* TrivSqZeroExt O O) S.ρ =
      NRep.map (z : S.R →+* TrivSqZeroExt O O) S.ρ := by
    apply NRep.ext
    · refine MonoidHom.ext fun g => Matrix.ext fun i j => ?_
      exact key _ (hr g i j)
    · funext v i
      refine MonoidHom.ext fun g => Units.ext ?_
      exact key _ (hψ v i g)
  obtain ⟨f, _, huniq⟩ := S.univ (TrivSqZeroExt O O) _ (isLift_map z S.lift)
  have e : y = z := (huniq y hmap).trans (huniq z rfl).symm
  ext a
  have h2 := (hy a).2
  rw [e] at h2
  rw [← h2]
  rfl

end UpperTheory.V.J

end
end

set_option linter.overlappingInstances false

noncomputable section

open UpperTheory.V.Alg UpperTheory.V.Fr

namespace UpperTheory.V.J

section Grading

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {K : Type} [CommRing K]

private theorem mon_mul {ρ : NRep F n K} {a b : K} {i j : ℤ} (ha : a ∈ ρ.mon i) (hb : b ∈ ρ.mon j) :
    a * b ∈ ρ.mon (i + j) := by
  obtain ⟨L1, h1, rfl⟩ := ha
  obtain ⟨L2, h2, rfl⟩ := hb
  refine ⟨L1 ++ L2, ?_, ?_⟩
  · rw [List.map_append, List.sum_append, h1, h2]
  · rw [List.map_append, List.prod_append]

private theorem mon_entry (ρ : NRep F n K) (g : F.G0) (i j : Fin n) : ρ.r g i j ∈ ρ.mon (w n i - w n j) :=
  ⟨[(g, i, j)], by simp, by simp⟩

private theorem w_lower : ∀ i j : Fin 3, j < i → w 3 i - w 3 j = -1 ∨ w 3 i - w 3 j = -2 := by
  decide

private theorem w_upper : ∀ i j : Fin 3, i < j → w 3 i - w 3 j = 1 ∨ w 3 i - w 3 j = 2 := by
  decide

private theorem w_odd : ∀ i j : Fin 3, Odd (w 3 i - w 3 j) → w 3 i - w 3 j = 1 ∨ w 3 i - w 3 j = -1 := by
  decide

private theorem exists_mon (ρ : NRep F 3 K) (P : Ideal K) [hP : P.IsPrime] (h : ρ.TI P) :
    (∃ p ∈ ρ.mon 1, p ∉ P) ∧ ∃ q ∈ ρ.mon (-1), q ∉ P := by
  obtain ⟨⟨hP', hM'⟩, hee⟩ := h
  have ex : ∀ {S : Set K}, ¬ Ideal.span S ≤ P → ∃ s ∈ S, s ∉ P := by
    intro S hS
    by_contra hc
    push_neg at hc
    exact hS (Ideal.span_le.mpr hc)
  have hmul : ∀ {a b : K}, a ∉ P → b ∉ P → a * b ∉ P := fun ha hb hm =>
    (hP.mem_or_mem hm).elim ha hb
  obtain ⟨_, ⟨g1, i1, j1, hj1, rfl⟩, hy⟩ := ex (S := {x | ∃ g i, ∃ j < i, x = ρ.r g i j}) hP'
  obtain ⟨_, ⟨g2, i2, j2, hj2, rfl⟩, hz⟩ := ex (S := {x | ∃ g i j, i < j ∧ x = ρ.r g i j}) hM'
  obtain ⟨_, ⟨g3, i3, j3, hodd, rfl⟩, hx⟩ :=
    ex (S := {x | ∃ g i j, Odd (w 3 i - w 3 j) ∧ x = ρ.r g i j}) (hee rfl)
  have my := mon_entry ρ g1 i1 j1
  have mz := mon_entry ρ g2 i2 j2
  have mx := mon_entry ρ g3 i3 j3
  rcases w_odd i3 j3 hodd with hx1 | hx1
  · rw [hx1] at mx
    refine ⟨⟨_, mx, hx⟩, ?_⟩
    rcases w_lower i1 j1 hj1 with hy1 | hy1
    · rw [hy1] at my
      exact ⟨_, my, hy⟩
    · rw [hy1] at my
      have m := mon_mul my mx
      norm_num at m
      exact ⟨_, m, hmul hy hx⟩
  · rw [hx1] at mx
    refine ⟨?_, ⟨_, mx, hx⟩⟩
    rcases w_upper i2 j2 hj2 with hz1 | hz1
    · rw [hz1] at mz
      exact ⟨_, mz, hz⟩
    · rw [hz1] at mz
      have m := mon_mul mz mx
      norm_num at m
      exact ⟨_, m, hmul hz hx⟩

end Grading

private theorem cancel {O : Type} [CommRing O] [IsDomain O] {a b : O} (ha : a ≠ 0) (h : a * b = 0) : b = 0 :=
  (mul_eq_zero.mp h).resolve_left ha

section Der

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fr.IsCoef l O]
  {F : Fr.Frame l (IsLocalRing.ResidueField O)} {S : Fr.Space O F 3} {ξ : S.R →ₐ[O] O}

private theorem der_zero {p q : S.R} (hp : p ∈ S.ρ.mon 1) (hq : q ∈ S.ρ.mon (-1)) (hξp : ξ p ≠ 0) (hξq : ξ q ≠ 0)
    {E : S.R →ₗ[O] O} (hE : E ∈ PtDer ξ O) (hB : ∀ a ∈ S.B, E a = 0) (hEp : E p = 0) : E = 0 := by
  have hder : ∀ f g : S.R, E (f * g) = ξ f • E g + ξ g • E f := hE
  have canc : ∀ {x y : S.R}, ξ y ≠ 0 → E y = 0 → E (x * y) = 0 → E x = 0 := by
    intro x y hy hEy hxy
    rw [hder, hEy, smul_zero, zero_add, smul_eq_mul] at hxy
    exact cancel hy hxy
  have mB0 : ∀ {x : S.R}, x ∈ S.ρ.mon 0 → E x = 0 := fun hx => hB _ (S.mon_mem hx)
  have hEq : E q = 0 := canc hξp hEp (mB0 (by
    have m := mon_mul hq hp
    norm_num at m
    exact m))
  have e1 : ∀ {x : S.R}, x ∈ S.ρ.mon 1 → E x = 0 := fun hx => canc hξq hEq (mB0 (by
    have m := mon_mul hx hq
    norm_num at m
    exact m))
  have em1 : ∀ {x : S.R}, x ∈ S.ρ.mon (-1) → E x = 0 := fun hx => canc hξp hEp (mB0 (by
    have m := mon_mul hx hp
    norm_num at m
    exact m))
  have e2 : ∀ {x : S.R}, x ∈ S.ρ.mon 2 → E x = 0 := fun hx => canc hξq hEq (e1 (by
    have m := mon_mul hx hq
    norm_num at m
    exact m))
  have em2 : ∀ {x : S.R}, x ∈ S.ρ.mon (-2) → E x = 0 := fun hx => canc hξp hEp (em1 (by
    have m := mon_mul hx hp
    norm_num at m
    exact m))
  have hrange : ∀ i j : Fin 3, w 3 i - w 3 j = -2 ∨ w 3 i - w 3 j = -1 ∨ w 3 i - w 3 j = 0 ∨
      w 3 i - w 3 j = 1 ∨ w 3 i - w 3 j = 2 := by
    decide
  refine det l O F 3 S ξ E hE (fun g i j => ?_) (fun v i g => hB _ (S.ψ_mem v i g))
  have m := mon_entry S.ρ g i j
  rcases hrange i j with h | h | h | h | h <;> rw [h] at m
  · exact em2 m
  · exact em1 m
  · exact mB0 m
  · exact e1 m
  · exact e2 m

end Der

theorem tor : Tor := by
  intro l _ O _ _ _ _ F S ξ hTI D hD D' hD' hB hB' hli
  haveI : Nontrivial O := IsDomain.toNontrivial
  haveI : (RingHom.ker ξ).IsPrime := RingHom.ker_isPrime ξ
  obtain ⟨⟨p, hp, hpP⟩, ⟨q, hq, hqP⟩⟩ := exists_mon S.ρ (RingHom.ker ξ) hTI
  have hξp : ξ p ≠ 0 := fun h => hpP (RingHom.mem_ker.mpr h)
  have hξq : ξ q ≠ 0 := fun h => hqP (RingHom.mem_ker.mpr h)
  have hE : (D' p) • D + (-(D p)) • D' ∈ PtDer ξ O :=
    (PtDer ξ O).add_mem ((PtDer ξ O).smul_mem _ hD) ((PtDer ξ O).smul_mem _ hD')
  have hEB : ∀ a ∈ S.B, ((D' p) • D + (-(D p)) • D') a = 0 := by
    intro a ha
    simp [hB a ha, hB' a ha]
  have hEp : ((D' p) • D + (-(D p)) • D') p = 0 := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hE0 := der_zero hp hq hξp hξq hE hEB hEp
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hli _ _ hE0
  have hDp : D p = 0 := neg_eq_zero.mp h2
  have hD0 : D = 0 := der_zero hp hq hξp hξq hD hB hDp
  exact hli.ne_zero 0 hD0

end UpperTheory.V.J

end
end

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr

namespace UpperTheory.V.J

private theorem coef_inj {l : ℕ} [Fact l.Prime] (c : Coef l) : Function.Injective (algebraMap c.O (Qbar l)) :=
  Subtype.val_injective

theorem endJ : End := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro Ω _ _ _ l _ c η Ψ σ g₁ B M L _ _ _ _ _ Φ k c₁ _ f ka R φ hφ hs J ξ w hJ hTI har hirr hann D hD D' hD' h1 h2
    have key : ∀ E ∈ PtDer ξ (↥c₁.O),
        (∀ (v : (Φ.ext f).V) (i : Fin 3), ∀ g ∈ (Φ.ext f).Iv v, E ((R.S.ρ.ψ v i) g : R.S.R) = 0) →
        ∀ a ∈ R.S.B, E a = 0 := by
      intro E hE hI a ha
      have hmul : ∀ x y : R.S.R, E (x * y) = ξ x * E y + ξ y * E x := fun x y => hE x y
      have hone : E 1 = 0 := by
        have h := hmul 1 1
        simp at h
        exact h
      have halg : ∀ (r : ↥c₁.O), E (algebraMap (↥c₁.O) R.S.R r) = 0 := by
        intro r
        rw [Algebra.algebraMap_eq_smul_one, map_smul, hone, smul_zero]
      have hJa : ∀ a ∈ J, ξ ((φ a : R.S.B) : R.S.R) = 0 ∧ E ((φ a : R.S.B) : R.S.R) = 0 := by
        intro x hx
        obtain ⟨s, hs1, hs2⟩ := hann x hx
        have e : (s : R.S.R) * ((φ x : R.S.B) : R.S.R) = 0 := by
          have h := congrArg Subtype.val hs2
          simpa [Fr.Space.inc] using h
        have hξs : ξ (s : R.S.R) ≠ 0 := by
          intro h0
          apply hs1
          simp [ptA, h0]
        have hξ : ξ ((φ x : R.S.B) : R.S.R) = 0 := by
          have h := congrArg ξ e
          rw [map_mul, map_zero] at h
          exact (mul_eq_zero.mp h).resolve_left hξs
        refine ⟨hξ, ?_⟩
        have h := hmul (s : R.S.R) ((φ x : R.S.B) : R.S.R)
        rw [e, map_zero, hξ, zero_mul, add_zero] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hξs
      let incl : ↥R.S.B →ₐ[↥c₁.O] R.S.R := Subalgebra.val R.S.B
      let δ : R.B₀.B →ₗ[↥c₁.O] Qbar l :=
        (Algebra.ofId (↥c₁.O) (Qbar l)).toLinearMap ∘ₗ E ∘ₗ (AlgHom.toLinearMap (AlgHom.comp incl φ))
      have hδ : δ ∈ PtDer (ptOf R φ ξ) (Qbar l) := by
        intro x y
        simp [δ, incl, ptOf, hmul]
      have hle : J ≤ RingHom.ker (ptOf R φ ξ) := by
        intro x hx
        simp [ptOf, (hJa x hx).1]
      have hδJ : ∀ x ∈ J, δ x = 0 := by
        intro x hx
        simp [δ, incl, (hJa x hx).2]
      have hδψ : ∀ (v : R.V.frame.Vl) (i : Fin 3), ∀ g ∈ R.V.frame.Iv v, δ ((R.B₀.u.ψ v i) g : R.B₀.B) = 0 := by
        intro v i g hg
        have hm := congrArg (fun χ => ((χ g : (R.S.R)ˣ) : R.S.R)) (hφ.2 v i)
        simp only [pushCh, TwLink.twψ, TwLink.κA] at hm
        have hm' : ((φ ((R.B₀.u.ψ v i) g : R.B₀.B) : R.S.B) : R.S.R) =
            ((R.S.ρ.ψ (R.K.e v) i ((R.K.lam v) g) : R.S.Rˣ) : R.S.R) *
              algebraMap (↥c₁.O) R.S.R ((R.K.κ (R.V.frame.φ v g) : (↥c₁.O)ˣ) : ↥c₁.O) := hm
        have hin : (R.K.lam v) g ∈ (Φ.ext f).Iv (R.K.e v) := (R.K.lam_I v g).mpr hg
        simp only [δ, incl, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, AlgHom.coe_comp,
          Subalgebra.coe_val]
        rw [hm', hmul, halg, hI _ _ _ hin]
        simp
      have h0 := hJ (ptOf R φ ξ) w hle har hirr δ hδ hδJ hδψ
      obtain ⟨b, hb⟩ := hs ⟨a, ha⟩
      have h := LinearMap.congr_fun h0 b
      have h' : algebraMap (↥c₁.O) (Qbar l) (E a) = 0 := by
        simpa [δ, incl, hb] using h
      exact coef_inj c₁ (by rw [h', map_zero])
    exact tor l (↥c₁.O) (Φ.ext f) R.S ξ hTI D hD D' hD' (key D hD h1) (key D' hD' h2)

end UpperTheory.V.J
