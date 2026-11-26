module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.SeedII
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MixSeedOf

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ContRes
open UpperTheory.V.Z.Win.Birth

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

private theorem cont_res {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω)
    [NumberField F] : Continuous (resQ F) := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  exact (galEmbTop ℚ F Ω).1.continuous

private theorem not_both {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q : ℕ} (h : p.Coprime q)
    (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (q : Ω) < 1 := by
  intro hq
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (a : Ω) * p + (b : Ω) * q = 1 := by exact_mod_cast congrArg (Int.cast (R := Ω)) hab
  have hz : ∀ (z : ℤ) (x : Ω), A.valuation x < 1 → A.valuation (z * x) < 1 := fun z x hx => by
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right ((A.valuation_le_one_iff _).2 (intCast_mem A z)) zero_le hx
  have := A.valuation.map_add_lt (hz a _ hp) (hz b _ hq)
  rw [e, map_one] at this
  exact lt_irrefl _ this

theorem UpperTheory.V.Z.Win.Birth.mixOfP :
    MixSeedP → MixOfP := by
  intro hP Ω _ _ _ l hl c D T k₀ _ _ φ ι H C
  have hl2 : l ≠ 2 := H.good.l_odd
  obtain ⟨hsp, w, w', hne, hw, hw', hpl⟩ := UpperTheory.quadratic_field_split_prime_two_places Ω k₀ H.deg l hl.out H.spl
  obtain ⟨hsp2, u, -, -, hu, -, -⟩ := UpperTheory.quadratic_field_split_prime_two_places Ω k₀ H.deg 2 Nat.prime_two H.sp2
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  have hker : ∀ g : G ℚ Ω, D.ξ g = 1 → up D.ξ g = 1 := fun g hg => by
    change Units.map _ (D.ξ g) = 1
    rw [hg, map_one]
  have lift : ∀ g : G T.F Ω, resQ T.F g ∈ k₀.fixingSubgroup → ∃ s : G k₀ Ω, resQ k₀ s = resQ T.F g := fun g hg =>
    ⟨k₀.fixingSubgroupEquiv ⟨_, hg⟩, rfl⟩
  obtain ⟨Au, hAu⟩ := exists_isPlaceOver Ω u
  have hAu2 : Au.valuation ((2 : ℕ) : Ω) < 1 := by
    have h := (hAu _).2 hu
    rwa [show algebraMap k₀ Ω (((2 : ℕ) : 𝓞 k₀) : k₀) = ((2 : ℕ) : Ω) from
      map_natCast ((algebraMap k₀ Ω).comp (algebraMap (𝓞 k₀) k₀)) 2] at h
  obtain ⟨g, hg, hg4⟩ := H.two.big2 Au (by simpa using hAu2)
  rw [Ne, C.al] at hg4
  obtain ⟨s, hs⟩ := lift g (H.sp2 Au hAu2 hg.1)
  have hsI : s ∈ Ine (F := k₀) Au := by
    have h1 : resQ T.F g ∈ Ine (F := ℚ) Au := ⟨hg.1, hg.2⟩
    rw [← hs] at h1
    exact ⟨h1.1, h1.2⟩
  obtain ⟨k, t, π, r, hk, ht, hkl, -, hc, hi, ha, hd, hr, ⟨haw, hrw⟩, hab⟩ :=
    hP k₀ Ω l hl2 (by rw [H.deg]; exact even_two) hsp ι ((up D.ξ).comp (resQ k₀))
      (Subgroup.isOpen_mono (H₁ := D.ξ.ker.comap (resQ k₀)) (fun x hx => hker _ hx)
        (H.good.xi_open.preimage (cont_res k₀)))
      (fun x hx => by
        have h1 : IsConj (resQ k₀ x) D.cc := UpperTheory.complex_conjugations_are_conjugate Ω _ _ hx H.good.isCC
        have h2 : D.ξ (resQ k₀ x) = -1 := by
          rw [← H.good.xi_odd]
          exact isConj_iff_eq.1 (D.ξ.map_isConj h1)
        change Units.map _ (D.ξ (resQ k₀ x)) = -1
        rw [h2]
        exact Units.ext (by simp))
      (fun A hA x hx => hker _ (H.two.xi A (fun p hp => by
        rw [Finset.mem_singleton.1 hp]
        exact not_both A ((Nat.coprime_primes hl.out Nat.prime_two).2 hl2) hA) ⟨hx.1, hx.2⟩))
      ⟨u, Au, (by
        rw [show normV u = Ideal.absNorm u.asIdeal by
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
          rfl]
        exact (hsp2 u hu).1), hAu, fun h => hg4 (by
        have h1 : up D.ξ (resQ k₀ s) = 1 := h hsI
        rw [← hs, h1]
        simp [Cong])⟩
      ⟨s ^ 2, by
        rw [map_pow, ← pow_mul, MonoidHom.comp_apply, hs]
        exact hg4⟩
      (fun A hA => by
        obtain ⟨x, hx, hx4⟩ := H.two.bigL A hA
        rw [Ne, C.al] at hx4
        obtain ⟨y, hy⟩ := lift x (H.spl A hA hx)
        have h1 : resQ T.F x ∈ Dec (F := ℚ) A := hx
        rw [← hy] at h1
        refine ⟨y ^ 4, pow_mem (show y ∈ Dec (F := k₀) A from h1) 4, ?_⟩
        rw [map_pow, MonoidHom.comp_apply, hy]
        exact hx4)
      {w} ⟨w, rfl, hw⟩ ⟨w', hne.symm, hw'⟩
  obtain ⟨h1, h1'⟩ := (hab w hw).1 rfl
  obtain ⟨h2, h2'⟩ := (hab w' hw').2 hne.symm
  obtain ⟨he, he'⟩ := UpperTheory.exists_ringHom_to_localField_inducing_place k₀ l ι
  obtain ⟨τ, hτ⟩ := he w hw
  obtain ⟨τ', hτ'⟩ := he w' hw'
  refine ⟨k, t, r, And.symm ⟨hrw, ?_⟩⟩
  refine ⟨hk, ht, hkl, hc, hi, ⟨π, ha, _, _, fun h => hne (he' w w' τ τ' hτ hτ' h), h1' τ hτ, h2' τ' hτ'⟩,
    hd, hr, haw, fun A A' hA x hx hAA => ?_⟩
  rcases hpl A A' hA x hx hAA with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨h1 A a, h2 A' b⟩
  · exact Or.inr ⟨h2 A a, h1 A' b⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BirthSeedII
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.InducedFinalStatement
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FinalS
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Matrix
namespace UpperTheory.V.Sd.S2
section Alg
variable {k : Type} [Field k]
variable {Γ₀ Γ : Type} [Group Γ₀] [Group Γ]
end Alg
section Norm
variable {l : ℕ} [Fact l.Prime]
end Norm
section Gal
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
variable {D : Raw Ω c} (T : Tower D)
end Gal
def Final_s : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D)
    (ι : Qbar l ≃+* ℂ) (P : PD T.ι (G T.F Ω) (Qbar l)), GlobOk T P.r → LocOk T P → T.IsSeedAlt ι P →
    ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPairAlt ι h Q ∧
      Fr.InV (Φ := T.fr ∅) (Q.map (residue c₁.O)) ∧
      (Ent (Q.map (residue c₁.O)).r (-wAl) ∨ (Ent (Q.map (residue c₁.O)).r wBe ∧ Ent (Q.map (residue c₁.O)).r (-wTh)))
end UpperTheory.V.Sd.S2
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.ConjugateSelfDual IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd.S2
section
variable {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R')
private theorem fin_adj (X : M4 R) : adj (X.map j) = (adj X).map j := by
  ext a b
  simp only [adj_apply, Matrix.map_apply, map_zsmul]
private theorem fin_conj (X Y : M4 R) : adj (X.map j) * Y.map j * X.map j = (adj X * Y * X).map j := by
  rw [fin_adj, Matrix.map_mul, Matrix.map_mul]
private theorem fin_gsp (hj : Function.Injective j) (ν : R) (X : M4 R) (h : IsGSp (j ν) (X.map j)) : IsGSp ν X := by
  unfold IsGSp at h ⊢
  rw [fin_adj, ← Matrix.map_mul] at h
  ext a b
  apply hj
  have h1 := congrFun (congrFun h a) b
  rw [Matrix.map_apply] at h1
  rw [h1]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul]
  split_ifs <;> simp
private theorem fin_psi {ι Γ : Type} [Group Γ] (P : PD ι Γ R) (v : ι) (i : Fin 4) (s : Γ) :
    (P.map j).ψ v i s = j (P.ψ v i s) :=
  congrFun (congrFun (fin_conj j (P.n v) (P.r s)) i) i
end
private theorem fin_q (i j : Fin 4) (h : i ≠ j) (h' : wt i j ∉ qQ) : i < j ∨ (i = 2 ∧ j = 1) := by
  revert i j; decide
private theorem fin_v (w : ℤ × ℤ) (h : w ∉ nP) : w ∉ vV := by
  simp only [nP, vV, Finset.mem_insert, Finset.mem_singleton] at h ⊢
  tauto
theorem UpperTheory.induced_final_statement_alt :
    _root_.UpperTheory.V.Sd.S2.Final_s := by
  intro Ω _ _ _ l _ c D T ι P hG hL hS
  haveI : IsGalois T.F Ω := IsAlgClosure.isGalois T.F Ω
  obtain ⟨c₁, h, Q, hQ, hc⟩ := (UpperTheory.automorphic_forms_descent_to_smaller_level l c).2 T.ι (G T.F Ω) P hG.cont hG.int fun v => (hL.low v).2.1
  subst hQ
  have hinj : Function.Injective (algebraMap c₁.O (Qbar l)) := Subtype.val_injective
  have hz : ∀ x : c₁.O, residue c₁.O x = 0 ↔ ‖algebraMap c₁.O (Qbar l) x‖ < 1 := fun x =>
    (residue_eq_zero_iff x).trans ((UpperTheory.automorphic_forms_descent_to_smaller_level l c₁).1 x).2
  have hne : ∀ x : c₁.O, ‖algebraMap c₁.O (Qbar l) x‖ = 1 → residue c₁.O x ≠ 0 := fun x hx h0 =>
    absurd ((hz x).1 h0) (by rw [hx]; exact lt_irrefl _)
  have heq : ∀ x y : c₁.O, ‖algebraMap c₁.O (Qbar l) x - algebraMap c₁.O (Qbar l) y‖ < 1 →
      residue c₁.O x = residue c₁.O y := fun x y hxy => by
    rw [← sub_eq_zero, ← map_sub, hz, map_sub]
    exact hxy
  have h0 : ∀ x : c₁.O, algebraMap c₁.O (Qbar l) x = 0 → x = 0 := fun x hx => hinj (by rw [hx, map_zero])
  have hV : Supp vV (Q.map (residue c₁.O)).r := fun g i j hij hw => (hz _).2 (hG.supp g i j hij hw)
  have hq : ∀ v, SuppM qQ ((Q.map (residue c₁.O)).n v) := fun v i j hij hw => by
    rcases fin_q i j hij hw with hlt | ⟨rfl, rfl⟩
    · refine (hz _).2 ?_
      have h1 : algebraMap c₁.O (Qbar l) (Q.n v i j) = 0 := (hL.low v).1.2.2 i j hlt
      rw [h1, norm_zero]
      exact one_pos
    · exact (hz _).2 (hL.low v).2.2.1
  refine ⟨c₁, h, Q, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hc, ⟨?_, ?_, Or.inl ⟨?_, hq⟩⟩, hS⟩,
    ⟨hV, fun v => ⟨hq v, hne _ (hL.low v).2.2.2⟩⟩, ?_⟩
  · exact fun g => fin_gsp _ hinj _ _ (hG.mult g)
  · intro g hg
    ext i j
    have h1 := congrFun (congrFun (hG.kill g hg) i) j
    have h2 : algebraMap c₁.O (Qbar l) ((1 : M4 c₁.O) i j) = (1 : M4 (Qbar l)) i j := by
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    exact h1.trans h2.symm
  · exact fun i j hij => h0 _ (hG.nrm hij)
  · intro v
    obtain ⟨a1, a2, a3⟩ := (hL.low v).1
    refine ⟨fin_gsp _ hinj _ _ (by rw [map_one]; exact a1), fun i => hinj (by rw [map_one]; exact a2 i),
      fun i j hij => h0 _ (a3 i j hij)⟩
  · intro v s hs i j hij
    refine h0 _ ?_
    have h1 := hL.flag v s hs i j hij
    exact (congrFun (congrFun (fin_conj (algebraMap c₁.O (Qbar l)) (Q.n v) (Q.r s)) i) j).symm.trans h1
  · intro v s hs i
    refine hinj ?_
    exact ((fin_psi (algebraMap c₁.O (Qbar l)) Q v i s).symm.trans (hL.mu v s hs i)).trans (map_one _).symm
  · exact fun g i => heq _ _ (hG.diag g i)
  · intro v s hs i
    refine (fin_psi (residue c₁.O) Q v i s).trans (heq _ _ ?_)
    have h1 := hL.char v s hs i
    rw [fin_psi (algebraMap c₁.O (Qbar l)) Q v i s] at h1
    exact h1
  · exact fun g i j hij hw => hV g i j hij (fin_v _ hw)
  · rcases hG.ent with ⟨g, hg⟩ | ⟨⟨g, hg⟩, g', hg'⟩
    · exact Or.inl ⟨g, 1, 0, by decide, hne _ hg⟩
    · exact Or.inr ⟨⟨g, 1, 2, by decide, hne _ hg⟩, g', 3, 0, by decide, hne _ hg'⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
section
variable {l : ℕ} [Fact l.Prime]
private theorem lt_add {a b : Qbar l} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)
private theorem norm_of_cong {a b : Qbar l} (h : ‖a - b‖ < 1) (hb : ‖b‖ = 1) : ‖a‖ = 1 := by
  have e : a = (a - b) + b := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hb]; exact h.ne), hb, max_eq_right h.le]
private theorem root_ex {a : Qbar l} (ha : ‖a - 1‖ < 1) {z : (Qbar l)ˣ} (hz : Cong z 1 ∨ Cong z (-1)) :
    ∃ α : (Qbar l)ˣ, (α : Qbar l) ^ 2 = a ∧ Cong α z := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq a two_pos
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [← hx] at ha
    simp at ha
  have h1 : ∃ y : Qbar l, y ≠ 0 ∧ y ^ 2 = a ∧ ‖y - 1‖ < 1 := by
    have e : ‖x - 1‖ * ‖-x - 1‖ < 1 := by
      rw [← norm_mul, show (x - 1) * (-x - 1) = -(a - 1) by rw [← hx]; ring, norm_neg]
      exact ha
    by_cases h : ‖x - 1‖ < 1
    · exact ⟨x, hx0, hx, h⟩
    · refine ⟨-x, neg_ne_zero.2 hx0, by rw [← hx]; ring, ?_⟩
      nlinarith [norm_nonneg (-x - 1), not_lt.1 h]
  obtain ⟨y, hy0, hy, hy1⟩ := h1
  rcases hz with hz | hz
  · refine ⟨Units.mk0 y hy0, hy, ?_⟩
    have := lt_add hy1 (by rw [norm_neg]; exact hz : ‖-((z : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l))‖ < 1)
    simpa [Cong] using this
  · refine ⟨-Units.mk0 y hy0, by simpa using hy, ?_⟩
    have := lt_add hy1 hz
    rw [← norm_neg] at this
    have e : ((-Units.mk0 y hy0 : (Qbar l)ˣ) : Qbar l) - z = -(y - 1 + ((z : Qbar l) - ((-1 : (Qbar l)ˣ) : Qbar l))) := by
      rw [Units.val_neg, Units.val_neg, Units.val_mk0, Units.val_one]
      ring
    rw [Cong, e]
    exact this
end
private theorem indEx (hP : MixOfP) :
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T : Tower D),
    D.Good → T.Ok → T.Two → T.Deep → ∀ ι : Qbar l ≃+* ℂ,
    ∃ (k₀ : IntermediateField ℚ Ω) (_ : NumberField k₀) (_ : IsTotallyReal k₀) (φ : G ℚ Ω →* (Qbar l)ˣ) (k t : ℕ)
      (r : G k₀ Ω →* GL (Fin 2) (Qbar l)) (α β : (Qbar l)ˣ) (R : G ℚ Ω →* GL (Fin 4) (Qbar l)) (δ : G T.F Ω →* (Qbar l)ˣ),
      IndDat T k₀ φ ι k t r α β R δ ∧ PR ι r := by
  intro Ω _ _ _ l _ c D T hg hok h2 hd ι
  obtain ⟨k₀, _, _, φ, hyp, hrange, hidx, hemb⟩ := UpperTheory.exists_quadratic_character_of_subgroup_index_two Ω l c D T hg hok h2 hd
  have hc := UpperTheory.galois_character_residual_decomposition Ω l c D T k₀ φ hyp
  obtain ⟨k, t, r₀, dat₀, hrw⟩ := hP Ω l c D T k₀ φ ι hyp hc
  obtain ⟨u, hu⟩ : resQ T.F T.g0 * resQ T.F T.g0 ∈ (resQ k₀).range := hrange ▸ Subgroup.mul_self_mem_of_index_two hidx _
  obtain ⟨r, iso, h01, h10, rib, ns⟩ := UpperTheory.exists_ribet_lattice Ω l c D T k₀ φ ι k t r₀ hyp hc dat₀ u hu
  have dat := UpperTheory.galoisRep_properties_invariant_under_conjugation Ω l k₀ ι _ k t r₀ r dat₀ iso
  set μ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ k * up D.ξ * φ with hμ
  have hF : ∀ g : G T.F Ω, resQ T.F g ∈ T.F.fixingSubgroup := fun g => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => g.commutes ⟨x, hx⟩
  have hdet : ∀ h, Matrix.GeneralLinearGroup.det (r h) = μ (resQ k₀ h) := fun h => by
    have e := DFunLike.congr_fun dat.det h
    have e' : φ (resQ k₀ h) = 1 := hyp.φ_in _ (hrange ▸ ⟨h, rfl⟩)
    simp only [hμ, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, e', mul_one] at e ⊢
    rw [e]
    rfl
  have ru := rib u (by rw [hu, ← map_mul]; exact hF _)
  obtain ⟨α, hα, hαc⟩ := root_ex ru.1 hc.c3
  have hmu := hc.mult k dat.dvd
  have hμ1 : ∀ g : G T.F Ω, ‖(μ (resQ T.F g) : Qbar l)‖ = 1 := fun g =>
    norm_of_cong (by rw [norm_sub_rev]; exact hmu g) (hc.unit _ _)
  have hα1 : ‖(α : Qbar l)‖ = 1 := norm_of_cong hαc (hc.unit _ _)
  obtain ⟨R, hR, hgsp⟩ := UpperTheory.symmetric_square_mixed_exists (Qbar l) _ _ (resQ k₀) (resQ T.F T.g0) α (μ (resQ T.F T.g0) / α) r μ two_ne_zero
    hemb.injective (hrange ▸ hidx) (hrange ▸ hc.out) (fun u' hu' => by
      obtain rfl : u' = u := hemb.injective (hu'.trans hu.symm)
      have e := congrArg Units.val (hdet u')
      rw [hu, map_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h01, h10, ← hα, Units.val_mul] at e
      ext i j
      fin_cases i <;> fin_cases j
      · simp [hα]
      · simp [h01]
      · simp [h10]
      · have := α.ne_zero
        simp only [Fin.mk_one, Fin.isValue, Matrix.diagonal_apply_eq, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          Units.val_div_eq_div_val]
        field_simp
        linear_combination e) hdet (mul_div_cancel _ _)
  have hres : Continuous (resQ T.F) := (emb ℚ T.F Ω).continuous
  obtain ⟨δ, hδc, hδ2, hδ1⟩ := UpperTheory.exists_square_root_of_character_near_one l hg.l_odd _ ((up D.th / μ).comp (resQ T.F)) ((hc.cont k).comp hres) fun g => by
    have := (μ (resQ T.F g)).ne_zero
    have e : (((up D.th / μ).comp (resQ T.F) g : (Qbar l)ˣ) : Qbar l) - ((1 : (Qbar l)ˣ) : Qbar l) =
        ((up D.th (resQ T.F g) : Qbar l) - μ (resQ T.F g)) / μ (resQ T.F g) := by
      rw [MonoidHom.comp_apply, MonoidHom.div_apply, Units.val_div_eq_div_val, Units.val_one, sub_div, div_self this]
    rw [Cong, e, norm_div, hμ1, div_one]
    exact hmu g
  haveI : FaithfulSMul k₀ Ω := (faithfulSMul_iff_algebraMap_injective k₀ Ω).2 (algebraMap k₀ Ω).injective
  haveI : Module.IsTorsionFree k₀ Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  refine ⟨k₀, ‹_›, ‹_›, φ, k, t, r, α, _, R, δ, ⟨hyp, hc, dat, rib, ns, hR,
    UpperTheory.continuous_mix_family l _ _ _ _ _ _ r R hR hemb dat.cont, hgsp, hαc, ?_, hδc, fun g => ?_, hδ1⟩, prIso k₀ Ω l ι 2 r₀ r iso hrw⟩
  · have e0 := congrArg Units.val (hc.mul 0 (resQ T.F T.g0))
    have := α.ne_zero
    have e : ((μ (resQ T.F T.g0) / α : (Qbar l)ˣ) : Qbar l) - ch T 0 (resQ T.F T.g0) =
        (-((up D.th (resQ T.F T.g0) : Qbar l) - μ (resQ T.F T.g0)) +
          -(ch T 0 (resQ T.F T.g0) * ((α : Qbar l) - ch T 3 (resQ T.F T.g0)))) / α := by
      rw [← e0, Units.val_div_eq_div_val, Units.val_mul, show (0 : Fin 4).rev = 3 from rfl]
      field_simp
      ring
    rw [Cong, e, norm_div, hα1, div_one]
    refine lt_add (by rw [norm_neg]; exact hmu _) ?_
    rw [norm_neg, norm_mul, hc.unit, one_mul]
    exact hαc
  · rw [hδ2, MonoidHom.comp_apply, MonoidHom.div_apply, div_mul_cancel]
theorem UpperTheory.V.Z.Bc.seedII_of_p_alt :
    MixOfP → IndAutLP → _root_.UpperTheory.V.Ws.SeedIIAlt := by
  intro hP hI Ω _ _ _ l _ c D T hctx hok h2 hd ι
  obtain ⟨k₀, _, _, φ, k, t, r, α, β, R, δ, h, hrw⟩ := indEx hP Ω l c D T hctx.1 hok h2 hd ι
  have hirr : IsIrr ((R.comp (resQ T.F)).comp T.G'.subtype) := UpperTheory.induced_irreducible Ω l c D T k₀ φ ι k t r α β R δ h
  obtain ⟨n, hloc, m, b, N, hm, hw, hN, hfin⟩ := indLoc0 Ω l c D T k₀ φ ι k t r α β R δ h
  obtain ⟨⟨π, hreg, hatt⟩, hW⟩ := hI Ω l c D T k₀ φ ι k t r α β R δ h hrw
  refine _root_.UpperTheory.induced_final_statement_alt Ω l c D T ι ⟨twF T R δ, n⟩ (indGlob_of_kill UpperTheory.induced_representation_constituent_vanishing Ω l c D T k₀ φ ι k t r α β R δ h) hloc ⟨?_, ?_⟩
  · rw [(irrIff _).1]
    have := (shapeFacts l _ 4 _ (δ.comp T.G'.subtype)).2.2.2.2.2 hirr
    convert this using 1
    ext g : 2
    rfl
  · have hcont : Continuous (resLe T.F_le) := by
      rw [(emb ℚ T.F Ω).continuous_iff]
      exact (emb ℚ T.L Ω).continuous
    refine ⟨fun i => 2 * m i + b, (δ.comp (resLe T.F_le))⁻¹, π, -b, N, fun i => ⟨m i.castSucc - m i.succ, by linarith [hm i], by ring⟩,
      hw, (h.δ_cont.comp hcont).inv, hN, ⟨m 0, by ring⟩, fun A _ s _ => ?_, _root_.UpperTheory.V.Z.Win.Birth.mkReg' hreg (hW π hreg hatt), ?_⟩
    · have e := hfin (resLe T.F_le s)
      have e' : cycBar T.L Ω l s = cycBar T.F Ω l (resLe T.F_le s) := rfl
      rw [← inv_eq_one, ← inv_pow, ← e, e']
      simp [mul_comm]
    · convert hatt using 1
      ext g : 2
      rw [tw_val]
      change _ • (tw (R.comp (resQ T.F)) δ (resLe T.F_le g)).val = _
      rw [tw_val, smul_smul]
      simp
      rfl
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPropMHol
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THolLift
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THolFin
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Sd.holomorphic_finite_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.HolFin := fun _ => UpperTheory.V.Br.holFin0
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
namespace UpperTheory.V.Sd
variable {F : Type} [Field F] [NumberField F]
private theorem val_pow (ω : HChar F) (w : Pl F) (n : ℕ) : (ω ^ n).val w = ω.val w ^ n := by
  induction n with
  | zero => simp [HChar.val, HChar.locK, HChar.loc]
  | succ n ih => rw [pow_succ, pow_succ, HChar.val_mul, ih]
private theorem norm_chiI {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (ω : HChar F) (hω : IsOfFinOrder ω) (c : Pl F → ℕ)
    (I : Ideal (𝓞 F)) : ‖ι.symm (chiI ω c I)‖ ≤ 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hω
  refine finprod_induction (fun x : ℂ => ‖ι.symm x‖ ≤ 1) (by simp) ?_ ?_
  · intro x y hx hy
    rw [map_mul, norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  · intro w
    rw [map_pow, norm_pow]
    refine pow_le_one₀ (norm_nonneg _) ?_
    split_ifs
    · have h1 : (ι.symm ((ω.val w : ℂˣ) : ℂ)) ^ n = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, ← val_pow, h, ← pow_zero ω, val_pow]; simp
      have h2 := congrArg norm h1
      rw [norm_pow, norm_one] at h2
      exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2).le
    · simp
private abbrev Idx (F : Type) [Field F] : Type := {𝔪 : Ideal (𝓞 F) // 𝔪 ≠ ⊥}
open Classical in
private def fT {K : Type} [Field K] (w : Pl F) (e : K) : Module.End K (Idx F → K) where
  toFun v 𝔪 := v ⟨w.asIdeal * 𝔪.1, mul_ne_zero w.ne_bot 𝔪.2⟩ +
    e * if h : ∃ 𝔫, 𝔪.1 = w.asIdeal * 𝔫 then
      v ⟨h.choose, fun h0 => 𝔪.2 (by rw [h.choose_spec, h0, Ideal.mul_bot])⟩ else 0
  map_add' c d := by
    funext n
    by_cases h : ∃ 𝔫, n.1 = w.asIdeal * 𝔫 <;> simp only [h, dif_pos, dif_neg, not_false_eq_true, Pi.add_apply] <;> ring
  map_smul' a c := by
    funext n
    by_cases h : ∃ 𝔫, n.1 = w.asIdeal * 𝔫 <;>
      simp only [h, dif_pos, dif_neg, not_false_eq_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring
open Classical in
omit [NumberField F] in
private theorem fT_apply {K : Type} [Field K] (w : Pl F) (e : K) (v : Idx F → K) (𝔪 : Idx F) :
    fT w e v 𝔪 = v ⟨w.asIdeal * 𝔪.1, mul_ne_zero w.ne_bot 𝔪.2⟩ +
    e * if h : ∃ 𝔫, 𝔪.1 = w.asIdeal * 𝔫 then
      v ⟨h.choose, fun h0 => 𝔪.2 (by rw [h.choose_spec, h0, Ideal.mul_bot])⟩ else 0 := rfl
variable [IsTotallyReal F]
private def SS (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) : Submodule ℂ (TR.Sm F 2) where
  carrier := {φ | IsHol k c ω φ ∧ ∃ c₀ a, HasExp φ.1 k c₀ a}
  zero_mem' := ⟨(holLin F k c ω).1, _, _, (holLin F k c ω).2.1⟩
  add_mem' := by
    rintro φ ψ ⟨h1, c₀, a, h2⟩ ⟨h3, d₀, b, h4⟩
    have e1 := (holLin F k c ω).2.2.1 φ ψ 1 h1 h3
    have e2 := (holLin F k c ω).2.2.2.1 φ.1 ψ.1 1 _ _ _ _ h2 h4
    rw [one_smul] at e1 e2
    exact ⟨e1, _, _, e2⟩
  smul_mem' := by
    rintro z ψ ⟨h3, d₀, b, h4⟩
    have e1 := (holLin F k c ω).2.2.1 0 ψ z (holLin F k c ω).1 h3
    have e2 := (holLin F k c ω).2.2.2.1 0 ψ.1 z _ _ _ _ (holLin F k c ω).2.1 h4
    rw [zero_add] at e1 e2
    exact ⟨e1, _, _, e2⟩
private def cf {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) : Ideal (𝓞 F) → ℂ := φ.2.2.choose_spec.choose
private theorem cf_spec {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) : ∃ c₀, HasExp φ.1.1 k c₀ (cf φ) :=
  ⟨_, φ.2.2.choose_spec.choose_spec⟩
private theorem cf_eq {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a} (h : HasExp φ.1.1 k c₀ a) (𝔪 : Idx F) :
    cf φ 𝔪.1 = a 𝔪.1 := by
  obtain ⟨d, hd⟩ := cf_spec φ
  exact (expUnique F _ k _ _ _ _ hd h).2 _ 𝔪.2
private def Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (k : ℕ) (c : Pl F → ℕ) (ω : HChar F) :
    SS k c ω →ₛₗ[(ι.symm : ℂ →+* Qbar l)] (Idx F → Qbar l) where
  toFun φ 𝔪 := ι.symm (cf φ 𝔪.1)
  map_add' φ ψ := by
    funext 𝔪
    obtain ⟨_, h2⟩ := cf_spec φ
    obtain ⟨_, h4⟩ := cf_spec ψ
    have e2 := (holLin F k c ω).2.2.2.1 _ _ 1 _ _ _ _ h2 h4
    simp only [one_smul] at e2
    rw [cf_eq (φ + ψ) e2]
    simp
  map_smul' z ψ := by
    funext 𝔪
    obtain ⟨_, h4⟩ := cf_spec ψ
    have e2 := (holLin F k c ω).2.2.2.1 0 _ z _ _ _ _ (holLin F k c ω).2.1 h4
    simp only [zero_add] at e2
    rw [cf_eq (z • ψ) e2]
    simp
private theorem Phi_eq {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a}
    (h : HasExp φ.1.1 k c₀ a) (𝔪 : Idx F) : Phi ι k c ω φ 𝔪 = ι.symm (a 𝔪.1) := congrArg ι.symm (cf_eq φ h 𝔪)
private theorem fT_Phi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (φ : SS k c ω) {c₀ a}
    (h : HasExp φ.1.1 k c₀ a) (w : Pl F) (𝔪 : Idx F) :
    fT w (ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))) (Phi ι k c ω φ) 𝔪 = ι.symm (hkCoef k c ω w a 𝔪.1) := by
  rw [fT_apply, Phi_eq ι φ h, hkCoef, map_add (f := _), map_mul ι.symm _ (coefDiv _ _ _), coefDiv]
  split_ifs with hd
  · rw [Phi_eq ι φ h]
  · rw [map_zero]
private def hkS {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F} (hω : IsOfFinOrder ω) (w : Pl F) (φ : SS k c ω) : SS k c ω :=
  ⟨hk k w (c w) φ.1, (holHk F k hk1 c ω hω φ.1 φ.2.1 w).1, by
    obtain ⟨_, h⟩ := cf_spec φ
    obtain ⟨d, hd⟩ := (holHk F k hk1 c ω hω φ.1 φ.2.1 w).2.2 _ _ h
    exact ⟨d, _, hd⟩⟩
private theorem Phi_hkS {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F}
    (hω : IsOfFinOrder ω) (w : Pl F) (φ : SS k c ω) :
    fT w (ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))) (Phi ι k c ω φ) = Phi ι k c ω (hkS hk1 c hω w φ) := by
  funext 𝔪
  obtain ⟨_, h⟩ := cf_spec φ
  obtain ⟨d, hd⟩ := (holHk F k hk1 c ω hω φ.1 φ.2.1 w).2.2 _ _ h
  rw [fT_Phi ι φ h, Phi_eq ι (hkS hk1 c hω w φ) hd]
private theorem Phi_inj {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : ℕ} (hk1 : 1 ≤ k) (c : Pl F → ℕ) {ω : HChar F}
    (hω : IsOfFinOrder ω) : Function.Injective (Phi ι k c ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro φ h0
  obtain ⟨_, h⟩ := cf_spec φ
  refine Subtype.ext (expInj F k hk1 c ω hω φ.1 φ.2.1 _ _ h fun 𝔪 h𝔪 => ?_)
  have := congrFun h0 ⟨𝔪, h𝔪⟩
  rw [Phi_eq ι φ h] at this
  simpa using this
end UpperTheory.V.Sd
open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.holLift_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.HolLift := by
  intro hP F _ _ _ l _ ι k hk1 c hc ω hω φ c₀ a t hφ hexp hint h1 ht hcong
  haveI : RingHomSurjective (ι.symm : ℂ →+* Qbar l) := ⟨ι.symm.surjective⟩
  haveI := _root_.UpperTheory.V.Sd.holomorphic_finite_of_printed_hida hP F k c hc ω hω
  haveI : FiniteDimensional ℂ (SS k c ω) :=
    Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ : TR.Sm F 2 | IsHol k c ω φ})
      fun ψ hψ => Submodule.subset_span hψ.1
  set V : Submodule (Qbar l) (Idx F → Qbar l) := (⊤ : Submodule ℂ (SS k c ω)).map (Phi ι k c ω) with hV
  have hfd : FiniteDimensional (Qbar l) V :=
    Module.Finite.iff_fg.2 (Submodule.FG.map _ (IsNoetherian.noetherian _))
  let e : Pl F → Qbar l := fun w => ι.symm (chiI ω c w.asIdeal * (normV w : ℂ) ^ (k - 1))
  have he : ∀ p, ‖e p‖ ≤ 1 := by
    intro p
    simp only [e, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    exact mul_le_one₀ (norm_chiI ι ω hω c _) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _))
  have hmem : ∀ p : Pl F, ∀ v ∈ V, fT p (e p) v ∈ V := by
    rintro p _ ⟨g, -, rfl⟩
    exact ⟨hkS hk1 c hω p g, trivial, (Phi_hkS ι hk1 c hω p g).symm⟩
  let T : Pl F → Module.End (Qbar l) V := fun p => (fT p (e p)).restrict (hmem p)
  have hT : ∀ p (v : V), (T p v).1 = fT p (e p) v.1 := fun _ _ => rfl
  let f : SS k c ω := ⟨φ, hφ, _, _, hexp⟩
  obtain ⟨h, b, hne, -, heig, hb⟩ := delSerre l (Idx F) (Pl F) V hfd T
    (by
      intro p q
      ext1 v
      apply Subtype.ext
      obtain ⟨_, g, -, rfl⟩ := v
      simp only [Module.End.mul_apply, hT, e, Phi_hkS ι hk1 c hω]
      exact congrArg _ (Subtype.ext ((holHk F k hk1 c ω hω g.1 g.2.1 p).2.1 q)))
    (by
      intro p v hv n
      rw [hT, fT_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv _) ?_)
      rw [norm_mul]
      refine mul_le_one₀ (he p) (norm_nonneg _) ?_
      split_ifs
      · exact hv _
      · simp)
    (by
      intro p v hv n
      rw [hT, fT_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hv _) ?_)
      rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) (he p)).trans_lt ?_
      split_ifs
      · exact hv _
      · simp)
    ⟨Phi ι k c ω f, f, trivial, rfl⟩ (fun p => ι.symm (t p))
    (by
      intro n
      show ‖Phi ι k c ω f n‖ ≤ 1
      rw [Phi_eq ι f hexp]
      exact hint _ n.2)
    ⟨⟨⊤, top_ne_bot⟩, by
      show ‖Phi ι k c ω f _‖ = 1
      rw [Phi_eq ι f hexp]; exact h1⟩
    ht
    (by
      intro p n
      rw [hT]
      show ‖fT p (e p) (Phi ι k c ω f) n - ι.symm (t p) * Phi ι k c ω f n‖ < 1
      rw [fT_Phi ι f hexp, Phi_eq ι f hexp, ← map_mul, ← map_sub]
      exact hcong p _ n.2)
  obtain ⟨_, g, hg, rfl⟩ := h
  refine ⟨g.1, fun w => ι (b w), ⟨g.2.1, fun h0 => hne ?_, fun w => ?_⟩, fun w => ?_⟩
  · apply Subtype.ext
    show Phi ι k c ω g = 0
    rw [show g = 0 from Subtype.ext h0, map_zero]
  · have h2 : fT w (e w) (Phi ι k c ω g) = b w • Phi ι k c ω g := congrArg Subtype.val (heig w)
    have h3 : hkS hk1 c hω w g = ι (b w) • g := by
      apply Phi_inj ι hk1 c hω
      rw [← Phi_hkS, LinearMap.map_smulₛₗ]
      refine h2.trans ?_
      simp
    exact congrArg Subtype.val h3
  · rw [map_sub, RingEquiv.symm_apply_apply]
    exact hb w
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Base UpperTheory.V.Sd
section SlopeTestRemainingChoices
variable {l : ℕ} [Fact l.Prime]
private theorem sm_add {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)
private theorem sm_sub {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]; exact sm_add hx (by rwa [norm_neg])
private theorem sm_mul {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1) : ‖x * y‖ < 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt hy
private theorem le_of_cong {x y : Qbar l} (h : ‖x - y‖ < 1) (hy : ‖y‖ ≤ 1) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.le hy)
private theorem eq_of_cong {x y : Qbar l} (h : ‖x - y‖ < 1) (hy : ‖y‖ = 1) : ‖x‖ = 1 := by
  refine le_antisymm (le_of_cong h hy.le) (not_lt.1 fun hx => ?_)
  have := sm_sub hx h
  rw [sub_sub_cancel, hy] at this
  exact lt_irrefl _ this
private theorem inv_cong {x : Qbar l} (h : ‖x⁻¹ - 1‖ < 1) : ‖x - 1‖ < 1 := by
  have h1 := eq_of_cong h norm_one
  rw [norm_inv, inv_eq_one] at h1
  have h0 : x ≠ 0 := by rintro rfl; simp at h1
  have := sm_mul h1.le h
  rw [mul_sub, mul_inv_cancel₀ h0, mul_one, norm_sub_rev] at this
  exact this
private theorem norm_nat_lt {n : ℕ} (h : l ∣ n) : ‖(n : Qbar l)‖ < 1 := by
  obtain ⟨m, rfl⟩ := h
  rw [Nat.cast_mul, mul_comm]
  refine sm_mul (IsUltrametricDist.norm_natCast_le_one _ _) ?_
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one
private theorem pow_cong {n k : ℕ} (h : ¬ l ∣ n) (hk : l - 1 ∣ k) : ‖(n : Qbar l) ^ k - 1‖ < 1 := by
  obtain ⟨m, rfl⟩ := hk
  have hp : l.Prime := Fact.out
  have h1 : n ^ (l - 1) ≡ 1 [MOD l] := by
    rw [← Nat.totient_prime hp]
    exact Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
  have h2 : n ^ ((l - 1) * m) ≡ 1 [MOD l] := by
    rw [pow_mul]; simpa using h1.pow m
  have h0 : 1 ≤ n ^ ((l - 1) * m) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h))
  have := norm_nat_lt ((Nat.modEq_iff_dvd' h0).1 h2.symm)
  rwa [Nat.cast_sub h0, Nat.cast_pow, Nat.cast_one] at this
variable {F : Type} [Field F] [NumberField F]
private theorem dvd_normV (w : Pl F) : l ∣ normV w ↔ ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  rw [normV, Nat.card_eq_fintype_card, ← prime_dvd_char_iff_dvd_card, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    ringChar.spec]
  have hq : (ringChar (𝓞 F ⧸ w.asIdeal)).Prime := CharP.prime_ringChar _
  rw [Nat.prime_dvd_prime_iff_eq Fact.out hq, Nat.prime_dvd_prime_iff_eq hq Fact.out, eq_comm]
private theorem norm_val (ι : Qbar l ≃+* ℂ) {η : HChar F} (h : IsOfFinOrder η) (x : Ideles F) :
    ‖ι.symm (η.1 x : ℂˣ)‖ = 1 := by
  obtain ⟨m, hm, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : η.1 x ^ m = 1 := DFunLike.congr_fun (congrArg Subtype.val e) x
  have e2 : ‖ι.symm (η.1 x : ℂˣ)‖ ^ m = 1 := by
    rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, e1, Units.val_one, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e2
private theorem chiI_prime (ω : HChar F) (c : Pl F → ℕ) (w : Pl F) :
    chiI ω c w.asIdeal = if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0 := by
  classical
  rw [chiI, finprod_eq_single _ w]
  · rw [ordI, Associates.count_self w.associates_irreducible, pow_one]
  · intro v hv
    rw [ordI, Associates.count_eq_zero_of_ne v.associates_irreducible w.associates_irreducible, pow_zero]
    intro e
    exact hv (HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 e)))
private theorem gal_of (hA : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {η₁ η₂ : HChar F} (h₁ : IsOfFinOrder η₁)
    (h₂ : IsOfFinOrder η₂) {S : Set (Pl F)} (hS : S.Finite)
    (h : ∀ w ∉ S, η₁.UnrAt w ∧ η₂.UnrAt w ∧ (‖ι.symm (η₁.val w : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.val w : ℂˣ) - 1‖ < 1))
    (x : Ideles F) : ‖ι.symm (η₁.1 x : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.1 x : ℂˣ) - 1‖ < 1 := by
  obtain ⟨art, ha⟩ := hA F (AlgebraicClosure F)
  obtain ⟨m₁, hm₁, e₁⟩ := isOfFinOrder_iff_pow_eq_one.1 h₁
  obtain ⟨m₂, hm₂, e₂⟩ := isOfFinOrder_iff_pow_eq_one.1 h₂
  obtain ⟨δ₁, c₁, L₁⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η₁) hm₁ e₁)
  obtain ⟨δ₂, c₂, L₂⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η₂) hm₂ e₂)
  have hcl : IsClosed ((fun σ => (δ₁ σ : Qbar l)) ⁻¹' Metric.ball 1 1 ∪ (fun σ => (δ₂ σ : Qbar l)) ⁻¹' Metric.ball 1 1) :=
    ((IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp c₁)).union
      ((IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp c₂))
  obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
  have hd := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := AlgebraicClosure F) GlobalTheory.Published.chebotarevDegreeOne' hS
  have hm := hcl.closure_subset_iff.2 ?_ (hd σ)
  · have f₁ := L₁ x σ hσ.symm
    have f₂ := L₂ x σ hσ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one] at f₁ f₂
    simpa only [Set.mem_union, Set.mem_preimage, mem_ball_iff_norm, f₁, f₂] using hm
  · rintro τ ⟨v, hv, -, B, hB, hτ⟩
    obtain ⟨u₁, u₂, hh⟩ := h v hv
    simp only [Set.mem_union, Set.mem_preimage, mem_ball_iff_norm, L₁.frob_unr ha (Or.inr rfl) u₁ hB hτ,
      L₂.frob_unr ha (Or.inr rfl) u₂ hB hτ]
    exact hh.imp (fun t => inv_cong (by rwa [inv_inv])) fun t => inv_cong (by rwa [inv_inv])
end SlopeTestRemainingChoices
theorem UpperTheory.V.Z.Bc.propMHolZ_alt :
    _root_.UpperTheory.V.Z.Bc.Hypotheses4Z' → UpperTheory.V.Sd.PropMHol := by
  intro PP F _ _ _ l _ hl ι ω c hω hodd hc hne hcl P hP hQ B
  have hp : l.Prime := Fact.out
  obtain ⟨v, hvP, hvl, hv⟩ := hP
  obtain ⟨v', hvQ, hvl', hv'⟩ := hQ
  obtain ⟨φ, a, hφ, eφ, a1, aint, aeig⟩ := emix PP.eis F l ι ω c hω hodd hc hne hcl P ⟨v, hvP, hvl⟩
  have hl1 : 0 < l - 1 := Nat.sub_pos_of_lt hp.one_lt
  obtain ⟨k, hkB, hk0, hkd', ψ, d₀, b, hψ, eψ, hd, hb⟩ := PP.one F l hl ι B
  obtain ⟨χ, a', hχ, eχ, ha'⟩ := holMul F l ι 1 k (levL l c) ω hω φ ψ a d₀ b hφ hψ eφ eψ aint hd hb
  rw [add_comm 1 k] at hχ eχ
  simp only [map_sub] at ha'
  have hfin : {w | levL l c w ≠ 0}.Finite := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
    refine ((Ideal.finite_factors h0).union (GlobalTheory.Mem.UnrAe.unr_ae_and_level F ω).1).subset fun w hw => ?_
    by_cases h : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · exact Or.inl (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
    · refine Or.inr fun hu => hw ?_
      rw [levL, if_neg h]
      exact Nat.le_zero.1 ((hc w).2 fun x hx _ => hu x hx)
  have hL0 : ∀ w, levL l c w = 0 → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ∧ c w = 0 := fun w hw => by
    by_cases h : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [levL, if_pos h] at hw; exact absurd hw one_ne_zero
    · rw [levL, if_neg h] at hw; exact ⟨h, hw⟩
  have nval : ∀ {η : HChar F}, IsOfFinOrder η → ∀ w, ‖ι.symm (η.val w : ℂˣ)‖ = 1 := fun h w => norm_val ι h _
  have hpow : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖(normV w : Qbar l) ^ k - 1‖ < 1 := fun w hw =>
    pow_cong (mt (dvd_normV w).1 hw) hkd'
  have ht : ∀ w, ‖ι.symm (eisT l ω c P w)‖ ≤ 1 := fun w => by
    rw [eisT]
    split_ifs
    · exact (nval hω w).le
    · simp
    · rw [map_add (f := _), map_one]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le norm_one.le (nval hω w).le)
    · simp
  obtain ⟨g, lam, hg, hlam⟩ := _root_.UpperTheory.V.Sd.holLift_alt PP.h F l ι (k + 1) (Nat.le_add_left _ _) (levL l c) hfin ω hω χ 0 a'
    (eisT l ω c P) hχ eχ (fun 𝔪 h => le_of_cong (ha' 𝔪 h) (aint 𝔪 h))
    (eq_of_cong (ha' ⊤ top_ne_bot) (by rw [a1, map_one, norm_one])) ht (fun w 𝔪 h𝔪 => by
      have e := aeig w 𝔪 h𝔪
      have h1 := ha' _ (mul_ne_zero w.ne_bot h𝔪)
      have h2 := sm_mul (ht w) (ha' 𝔪 h𝔪)
      have h3 : ‖ι.symm (coefDiv a w.asIdeal 𝔪)‖ ≤ 1 ∧
          ‖ι.symm (coefDiv a' w.asIdeal 𝔪) - ι.symm (coefDiv a w.asIdeal 𝔪)‖ < 1 := by
        unfold coefDiv
        split_ifs with h
        · have h0 : h.choose ≠ ⊥ := fun h0 => h𝔪 (by rw [h.choose_spec, h0, Ideal.mul_bot])
          exact ⟨aint _ h0, ha' _ h0⟩
        · simp
      rw [hkCoef, chiI_prime, Nat.sub_self, pow_zero, mul_one] at e
      have e' := congrArg ι.symm e
      rw [hkCoef, chiI_prime, Nat.add_sub_cancel]
      split_ifs at e' ⊢ with h0
      · have h4 := sm_mul (nval hω w).le (sm_add (sm_mul (le_of_cong (hpow w (hL0 w h0).1) norm_one.le) h3.2)
          (sm_mul h3.1 (hpow w (hL0 w h0).1)))
        convert sm_add (sm_sub h1 h2) h4 using 2
        simp only [map_add (f := _), map_sub, map_mul, map_pow, map_natCast] at e' ⊢
        linear_combination e'
      · convert sm_sub h1 h2 using 2
        simp only [map_add (f := _), map_sub, map_mul, map_pow, map_natCast, map_zero] at e' ⊢
        linear_combination e')
  refine ⟨k, hkB, hkd', g, lam, hg, ?_, hlam⟩
  by_contra hcusp
  obtain ⟨η₁, η₂, f₁, f₂, rfl, hu, hr⟩ := holEis F (k + 1) (Nat.le_add_left _ _) (levL l c) hfin ω hω g lam hg hcusp
  simp only [map_sub, Nat.add_sub_cancel] at hlam hu hr
  have key := gal_of PP.h.litN.aut.art ι f₁ f₂ hfin fun w hw => by
    have h0 : levL l c w = 0 := not_not.1 hw
    obtain ⟨u₁, u₂, e⟩ := hu w h0
    refine ⟨u₁, u₂, ?_⟩
    have h1 := hlam w
    rw [e, eisT, if_neg (hL0 w h0).1, if_pos (hL0 w h0).2, HChar.val_mul] at h1
    have h2 := sm_sub (sm_mul (nval f₂ w).le (hpow w (hL0 w h0).1)) h1
    have h3 : ‖ι.symm (η₁.val w : ℂˣ) - 1‖ * ‖ι.symm (η₂.val w : ℂˣ) - 1‖ < 1 := by
      rw [← norm_mul]
      convert h2 using 2
      simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_one, Units.val_mul]
      ring
    by_contra hn
    rw [not_or, not_lt, not_lt] at hn
    exact h3.not_ge (one_le_mul_of_one_le_of_one_le hn.1 hn.2)
  have hab : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l (η₁ * η₂) c P w)‖ = 1 →
      ‖ι.symm (η₁.val w : ℂˣ) - ι.symm (eisT l (η₁ * η₂) c P w)‖ < 1 := fun w hw h1 => by
    have h2 := eq_of_cong (hlam w) h1
    rcases hr w (fun h0 => (hL0 w h0).1 hw) with e | ⟨-, e⟩ | ⟨-, e⟩
    · simp [e] at h2
    · exact e ▸ hlam w
    · rw [e, map_mul, map_pow, map_natCast, ← Nat.cast_pow] at h2
      exact absurd h2 (sm_mul (nval f₂ w).le (norm_nat_lt (dvd_pow ((dvd_normV w).2 hw) hk0.ne'))).ne
  have e₁ : eisT l (η₁ * η₂) c P v = ((η₁ * η₂).val v : ℂˣ) := by rw [eisT, if_pos hvl, if_pos hvP]
  have e₂ : eisT l (η₁ * η₂) c P v' = 1 := by rw [eisT, if_pos hvl', if_neg hvQ]
  have a₁ := hab v hvl (by rw [e₁]; exact nval hω v)
  have a₂ := hab v' hvl' (by rw [e₂, map_one, norm_one])
  rw [e₁] at a₁
  rw [e₂, map_one] at a₂
  have kk : ‖ι.symm (η₁.val v * η₁.val v' : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.val v * η₂.val v' : ℂˣ) - 1‖ < 1 := by
    have := key (localIdele F v (atFin v (unif v)) * localIdele F v' (atFin v' (unif v')))
    rw [map_mul η₁.1, map_mul η₂.1] at this
    exact this
  simp only [HChar.val_mul, Units.val_mul, map_mul] at kk a₁ hv hv'
  have n₁ := nval f₁ v
  have n₂ := nval f₂ v
  have n₃ := nval f₁ v'
  have n₄ := nval f₂ v'
  generalize ι.symm (η₁.val v : ℂˣ) = x at *
  generalize ι.symm (η₂.val v : ℂˣ) = y at *
  generalize ι.symm (η₁.val v' : ℂˣ) = x' at *
  generalize ι.symm (η₂.val v' : ℂˣ) = y' at *
  have hy : ‖y - 1‖ < 1 := by
    rwa [← mul_one_sub, norm_mul, n₁, one_mul, norm_sub_rev] at a₁
  rcases kk with h | h
  · refine hv ?_
    convert sm_sub (sm_sub h (sm_mul n₁.le a₂)) a₁ using 2
    ring
  · refine hv' ?_
    convert sm_add (sm_sub h (sm_mul n₄.le hy)) (sm_mul n₄.le a₂) using 2
    ring
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
namespace UpperTheory.V.Z.Bc
theorem seedII_Z_alt (h : _root_.UpperTheory.V.Z.Bc.Hypotheses4Z') (hI : _root_.UpperTheory.V.Z.Win.Birth.IndAutLP) : _root_.UpperTheory.V.Ws.SeedIIAlt :=
  _root_.UpperTheory.V.Z.Bc.seedII_of_p_alt (_root_.UpperTheory.V.Z.Win.Birth.mixOfP (_root_.UpperTheory.Esk.mixSeed_of_alt h.h (_root_.UpperTheory.V.Z.Bc.propMHolZ_alt h))) hI
end UpperTheory.V.Z.Bc
end
