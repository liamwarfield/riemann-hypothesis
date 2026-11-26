module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpFlag

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NnDefs
open IsLocalRing UpperTheory.V.Alg

namespace UpperTheory.V.Ws

def Pins (l : ℕ) {G : Type} [Group G] [TopologicalSpace G] (I : Subgroup G) (S : Set G) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R], (l : R) = 0 → ∀ ψ : G →* Rˣ,
    AdicCont (maximalIdeal R) (fun g => ((ψ g : Rˣ) : R)) → (∀ g ∈ I, ((ψ g : Rˣ) : R) - 1 ∈ maximalIdeal R) →
    (∀ g ∈ S, ψ g = 1) → ∀ g ∈ I, ψ g = 1

theorem eq_one_of_pow {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h0 : (l : R) = 0)
    {x : R} (hx : x - 1 ∈ maximalIdeal R) {N : ℕ} (hN : N ≠ 0) (h : x ^ N = 1) : x = 1 := by
  haveI : CharP R l := (CharP.charP_iff_prime_eq_zero hl.out).2 h0
  obtain ⟨k, M, hlM, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.out.ne_one
  have hz1 : x ^ l ^ k - 1 = (x - 1) ^ l ^ k := by rw [sub_pow_char_pow, one_pow]
  have hzM : (x ^ l ^ k) ^ M = 1 := by rw [← pow_mul]; exact h
  have hMu : IsUnit (M : R) := by
    have hu : IsUnit (M : ZMod l) := isUnit_iff_ne_zero.mpr (by rwa [Ne, ZMod.natCast_eq_zero_iff])
    simpa using hu.map (ZMod.castHom (dvd_refl l) R)
  have hzm : x ^ l ^ k - 1 ∈ maximalIdeal R := by
    rw [hz1]; exact Ideal.pow_mem_of_mem _ hx _ (pow_pos hl.out.pos _)
  have hS : IsUnit (∑ i ∈ Finset.range M, (x ^ l ^ k) ^ i) := by
    have key : (∑ i ∈ Finset.range M, (x ^ l ^ k) ^ i) - (M : R) ∈ maximalIdeal R := by
      have e : (∑ i ∈ Finset.range M, (x ^ l ^ k) ^ i) - (M : R) =
          ∑ i ∈ Finset.range M, ((x ^ l ^ k) ^ i - 1) := by
        simp [Finset.sum_sub_distrib]
      rw [e]
      refine Ideal.sum_mem _ fun i _ => ?_
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (x ^ l ^ k) 1 i
      rw [one_pow] at hc
      rw [hc]
      exact Ideal.mul_mem_right _ _ hzm
    by_contra hns
    have hmem : (∑ i ∈ Finset.range M, (x ^ l ^ k) ^ i) ∈ maximalIdeal R := by
      rw [mem_maximalIdeal, mem_nonunits_iff]; exact hns
    have hM : (M : R) ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ hmem key
      simpa using this
    rw [mem_maximalIdeal, mem_nonunits_iff] at hM
    exact hM hMu
  have hz1' : x ^ l ^ k = 1 := by
    have h2 : (x ^ l ^ k - 1) * ∑ i ∈ Finset.range M, (x ^ l ^ k) ^ i = 0 := by
      rw [mul_comm, geom_sum_mul, hzM, sub_self]
    exact sub_eq_zero.mp (hS.mul_left_eq_zero.mp h2)
  have h3 : (x - 1) ^ l ^ k = 0 := by rw [← hz1, hz1', sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ hl.out.ne_zero) |>.mp h3)

theorem adicCont_units {G R : Type} [TopologicalSpace G] [CommRing R] (m : Ideal R) (f : G → Rˣ) :
    AdicCont m (fun g => ((f g : Rˣ) : R)) ↔
      ∀ N, IsLocallyConstant fun g => Units.map (Ideal.Quotient.mk (m ^ N) : R →* R ⧸ m ^ N) (f g) := by
  unfold AdicCont
  refine forall_congr' fun N => ⟨fun h => ?_, fun h => ?_⟩
  · refine IsLocallyConstant.desc _ Units.val ?_ fun a b hab => Units.ext hab
    convert h using 1
    ext g
    simp
  · convert h.comp Units.val using 1
    ext g
    simp

theorem Pins.eq {l : ℕ} {G : Type} [Group G] [TopologicalSpace G] {I : Subgroup G} {S : Set G} (h : Pins l I S)
    {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (h0 : (l : R) = 0) (ψ ψ' : G →* Rˣ)
    (hc : AdicCont (maximalIdeal R) fun g => ((ψ g : Rˣ) : R)) (hc' : AdicCont (maximalIdeal R) fun g => ((ψ' g : Rˣ) : R))
    (h1 : ∀ g ∈ I, ((ψ g : Rˣ) : R) - 1 ∈ maximalIdeal R) (h1' : ∀ g ∈ I, ((ψ' g : Rˣ) : R) - 1 ∈ maximalIdeal R)
    (hS : ∀ g ∈ S, ψ g = ψ' g) : ∀ g ∈ I, ψ g = ψ' g := by
  intro g hg
  obtain ⟨χ, hχ⟩ : ∃ χ : G →* Rˣ, ∀ g, χ g = ψ g / ψ' g := ⟨ψ / ψ', fun g => rfl⟩
  have hres : ∀ u : Rˣ, (u : R) - 1 ∈ maximalIdeal R ↔
      Units.map (Ideal.Quotient.mk (maximalIdeal R) : R →* R ⧸ maximalIdeal R) u = 1 := by
    intro u
    rw [Units.ext_iff, ← Ideal.Quotient.eq]
    simp
  have hcχ : AdicCont (maximalIdeal R) fun g => ((χ g : Rˣ) : R) := by
    rw [adicCont_units] at hc hc' ⊢
    intro N
    have := (hc N).comp₂ (hc' N) (· / ·)
    convert this using 1
    ext g
    simp [hχ, map_div]
  have h1χ : ∀ g ∈ I, ((χ g : Rˣ) : R) - 1 ∈ maximalIdeal R := by
    intro g hg
    rw [hres, hχ, map_div, (hres _).1 (h1 g hg), (hres _).1 (h1' g hg), div_one]
  have hSχ : ∀ g ∈ S, χ g = 1 := by
    intro g hg
    rw [hχ, hS g hg, div_self']
  have key := h R h0 χ hcχ h1χ hSχ g hg
  rw [hχ, div_eq_one] at key
  exact key

theorem isClosed_ker_of_adicCont {G R : Type} [Group G] [TopologicalSpace G] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ψ : G →* Rˣ) (hc : AdicCont (maximalIdeal R) fun g => ((ψ g : Rˣ) : R)) : IsClosed (ψ.ker : Set G) := by
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) Ideal.IsPrime.ne_top'
  have e : (ψ.ker : Set G) = ⋂ N, {g | Ideal.Quotient.mk (maximalIdeal R ^ N) ((ψ g : Rˣ) : R) =
      Ideal.Quotient.mk (maximalIdeal R ^ N) 1} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq, Ideal.Quotient.eq]
    constructor
    · intro h N
      simp [h]
    · intro h
      have hm : ((ψ g : Rˣ) : R) - 1 ∈ ⨅ N, maximalIdeal R ^ N := (Submodule.mem_iInf _).2 h
      rw [hK, Ideal.mem_bot, sub_eq_zero] at hm
      exact Units.ext hm
  rw [e]
  exact isClosed_iInter fun N => (hc N).isClosed_fiber _

end UpperTheory.V.Ws
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DeformationSpaceLocalCharactersContinuous
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PseudoDeformationDiagCharactersMulRevEqSimilitud
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem adj_tri {R : Type} [CommRing R] {A : M4 R} (h : IsUp A) : (adj A).BlockTriangular id := by
  intro i j hij
  rw [adj_apply, h j.rev i.rev (Fin.rev_lt_rev.2 hij), smul_zero]

private theorem adj_dg {R : Type} [CommRing R] (A : M4 R) (i : Fin 4) : adj A i i = A i.rev i.rev := by
  rw [adj_apply]
  fin_cases i <;> simp [sgn]

theorem UpperTheory.pseudoDeformation_diag_characters_mul_rev_eq_similitude :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R) (P : PD Φ.ι Γ R), Φ.IsPair a P → ∀ (v : Φ.ι) (i : Fin 4), P.ψ v i 1 = 1 ∧ (∀ s ∈ Φ.Gv v, ∀ t ∈ Φ.Gv v, P.ψ v i (s * t) = P.ψ v i s * P.ψ v i t) ∧ ∀ s ∈ Φ.Gv v, P.ψ v i s * P.ψ v i.rev s = a (Φ.ν s) := by
  intro O Γ _ _ Φ R _ a P hP v i
  have hn : adj (P.n v) * P.n v = 1 := by
    have h := (hP.low v).1
    unfold IsGSp at h
    simpa using h
  have hn' : P.n v * adj (P.n v) = 1 := mul_eq_one_comm.mp hn
  refine ⟨?_, ?_, ?_⟩
  · simp [PD.ψ, hn]
  · intro s hs t ht
    have e : adj (P.n v) * P.r (s * t) * P.n v =
        (adj (P.n v) * P.r s * P.n v) * (adj (P.n v) * P.r t * P.n v) := by
      rw [map_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (P.n v) (adj (P.n v)), hn', Matrix.one_mul]
    unfold PD.ψ
    rw [e]
    exact UpperTheory.V.Loc.SpFlag.tri_mul_diag (fun p q h => hP.flag v s hs p q h) (fun p q h => hP.flag v t ht p q h) i
  · intro s hs
    have hB := hP.flag v s hs
    have hg := hP.mult s
    unfold IsGSp at hg
    have e : adj (adj (P.n v) * P.r s * P.n v) * (adj (P.n v) * P.r s * P.n v) = a (Φ.ν s) • 1 := by
      rw [UpperTheory.V.Loc.SpFlag.adj_mul, UpperTheory.V.Loc.SpFlag.adj_mul, UpperTheory.V.Loc.SpFlag.adj_adj]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (P.n v) (adj (P.n v)), hn', Matrix.one_mul, ← Matrix.mul_assoc (adj (P.r s)), hg]
      simp [hn]
    have d := UpperTheory.V.Loc.SpFlag.tri_mul_diag (adj_tri hB) (fun p q h => hB p q h) i
    rw [e, adj_dg] at d
    unfold PD.ψ
    rw [mul_comm, ← d]
    simp
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem l_mem {l : ℕ} [Fact l.Prime] (c : Coef l) : (l : c.O) ∈ maximalIdeal c.O := by
  obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
  intro hu
  have h0 := IsUnit.of_map (algebraMap ℤ_[l] c.O) _ hu
  rw [PadicInt.isUnit_iff, PadicInt.norm_p, inv_eq_one] at h0
  have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  linarith

private theorem inc_mem {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) {x : c.O}
    (hx : x ∈ maximalIdeal c.O) : inc h x ∈ maximalIdeal c'.O := by
  obtain ⟨hinj, -⟩ := dvrFacts l c.O
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have hx' : π ∣ x := by
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hx
    exact hx
  have hl0 : (l : c.O) ≠ 0 := by
    rw [← map_natCast (algebraMap ℤ_[l] c.O)]
    exact (map_ne_zero_iff _ hinj).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hπ
  obtain ⟨w, hw⟩ : (l : c.O) ∣ x ^ n := hn.dvd_iff_dvd_left.2 (pow_dvd_pow_of_dvd hx' n)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hu' := hu.pow n
  rw [← map_pow, hw, map_mul, map_natCast] at hu'
  exact (IsLocalRing.mem_maximalIdeal _).1 (l_mem c') (isUnit_of_mul_isUnit_left hu')

theorem UpperTheory.deformationSpace_local_characters_continuous :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Ok → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (R : Type) [CommRing R] [IsLocalRing R] (f : X.B →+* R), (∀ b ∈ maximalIdeal X.B, f b ∈ maximalIdeal R) → (∀ a ∈ maximalIdeal c'.O, f (algebraMap c'.O X.B a) = 0) → (l : R) = 0 ∧ ∃ κ : ∀ v : T.ι, Fin 4 → Dec (F := T.F) (T.pl v) →* Rˣ, ∀ v i, (∀ s, ((κ v i s : Rˣ) : R) = f (X.ψ v i s)) ∧ AdicCont (maximalIdeal R) (fun s => ((κ v i s : Rˣ) : R)) ∧ ∀ s : Dec (F := T.F) (T.pl v), (s : G T.F Ω) ∈ Ine (F := T.F) (T.pl v) → ((κ v i s : Rˣ) : R) - 1 ∈ maximalIdeal R ∧ κ v i s * κ v i.rev s = 1 := by
  intro Ω _ _ _ l _ c D T hT c' h X R _ _ f hf hf0
  have hl' : f (algebraMap c'.O X.B (l : c'.O)) = 0 := hf0 _ (l_mem c')
  rw [map_natCast, map_natCast] at hl'
  have hP := UpperTheory.pseudoDeformation_diag_characters_mul_rev_eq_similitude (T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) X.P X.pair
  have one : ∀ v i, X.ψ v i 1 = 1 := by
    intro v i
    apply X.inj
    rw [X.ψ_map v i 1 (Subgroup.one_mem _), map_one]
    exact (hP v i).1
  have mul : ∀ v i, ∀ s ∈ (T.fr ∅).Gv v, ∀ t ∈ (T.fr ∅).Gv v,
      X.ψ v i (s * t) = X.ψ v i s * X.ψ v i t := by
    intro v i s hs t ht
    apply X.inj
    rw [map_mul, X.ψ_map v i _ (Subgroup.mul_mem _ hs ht), X.ψ_map v i s hs, X.ψ_map v i t ht]
    exact (hP v i).2.1 s hs t ht
  have nu : ∀ v i, ∀ s ∈ (T.fr ∅).Gv v,
      X.ψ v i s * X.ψ v i.rev s = algebraMap c'.O X.B (inc h ↑((T.fr ∅).ν s)) := by
    intro v i s hs
    apply X.inj
    rw [map_mul, X.ψ_map v i s hs, X.ψ_map v i.rev s hs, (hP v i).2.2 s hs, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply c'.O X.B X.A]
  have hunit : ∀ (v : T.ι) (i : Fin 4) (s : Dec (F := T.F) (T.pl v)), IsUnit (f (X.ψ v i s)) := by
    intro v i s
    have hu : IsUnit (X.ψ v i s * X.ψ v i.rev s) := by
      rw [nu v i s s.2]
      exact ((Units.isUnit _).map (inc h)).map (algebraMap c'.O X.B)
    exact (isUnit_of_mul_isUnit_left hu).map f
  have key : ∀ u : (c.O)ˣ, residue c.O ↑u = 1 → f (algebraMap c'.O X.B (inc h ↑u)) = 1 := by
    intro u hu
    have h1 : (↑u : c.O) - 1 ∈ maximalIdeal c.O :=
      (residue_eq_zero_iff _).1 (by rw [map_sub, hu, map_one, sub_self])
    have h2 := hf0 _ (inc_mem h h1)
    rwa [map_sub, map_one, map_sub, map_one, map_sub, map_one, sub_eq_zero] at h2
  refine ⟨hl', fun v i => IsUnit.liftRight
    { toFun := fun s => f (X.ψ v i s)
      map_one' := by
        simp only [OneMemClass.coe_one]
        exact (congrArg f (one v i)).trans (map_one f)
      map_mul' := by
        intro s t
        simp only [Subgroup.coe_mul]
        rw [mul v i s s.2 t t.2, map_mul] } (fun s => hunit v i s), ?_⟩
  intro v i
  refine ⟨fun s => rfl, ?_, ?_⟩
  · intro N
    have hle : maximalIdeal X.B ^ N ≤ (maximalIdeal R ^ N).comap f := by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 (fun b hb => Ideal.mem_comap.2 (hf b hb))) N
    exact (X.ψ_cont v i N).comp (Ideal.quotientMap (maximalIdeal R ^ N) f hle)
  · intro s hs
    have hr := hT.ineL (T.pl v) (T.ovl v) s hs
    have hps : ∀ j, residue c.O ↑(D.ps j (resQ T.F s)) = 1 := fun j => by
      have e := congrArg (fun M => M j j) hr
      simpa [Raw.rbar, Raw.r0, mapRep_apply, diagRep] using e
    refine ⟨?_, ?_⟩
    · show f (X.ψ v i s) - 1 ∈ maximalIdeal R
      have hres : residue c'.O (inc h ↑(D.ps (lab T.pr i) (resQ T.F s))) = 1 := by
        have h1 : (↑(D.ps (lab T.pr i) (resQ T.F s)) : c.O) - 1 ∈ maximalIdeal c.O :=
          (residue_eq_zero_iff _).1 (by rw [map_sub, hps, map_one, sub_self])
        have h2 := inc_mem h h1
        rw [map_sub, map_one, ← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero] at h2
        exact h2
      have hB : X.ψ v i s - 1 ∈ maximalIdeal X.B := by
        rw [← res_eq_zero_iff c'.O X.B, map_sub, map_one, X.ψ_red v i s s.2]
        show residue c'.O (inc h ↑(D.ps (lab T.pr i) (resQ T.F s))) - 1 = 0
        rw [hres, sub_self]
      have := hf _ hB
      rwa [map_sub, map_one] at this
    · apply Units.ext
      show f (X.ψ v i s) * f (X.ψ v i.rev s) = 1
      rw [← map_mul, nu v i s s.2]
      exact key _ (hps 0)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsPlaceOverLLocDegMulCardEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem td_move {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A B : ValuationSubring Ω}
    (g : G F Ω) (hg : ∀ x, g x ∈ A ↔ x ∈ B) {w : HeightOneSpectrum (𝓞 F)} (hw : IsPlaceOver A w) :
    IsPlaceOver B w := by
  intro x
  rw [← hw x, valuation_lt_one_iff', valuation_lt_one_iff']
  have hy : g (algebraMap F Ω x) = algebraMap F Ω x := g.commutes _
  have hyi : g (algebraMap F Ω x)⁻¹ = (algebraMap F Ω x)⁻¹ := by rw [map_inv₀, hy]
  rw [← hg (algebraMap F Ω x), hy, ← hg (algebraMap F Ω x)⁻¹, hyi]

private theorem td_count (l : ℕ) [hl : Fact l.Prime] (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] {V : Type}
    (pl : V → HeightOneSpectrum (𝓞 F)) (hi : Function.Injective pl) (hm : ∀ v, ((l : ℕ) : 𝓞 F) ∈ (pl v).asIdeal)
    (hs : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ v, pl v = w) (v : V) :
    locDeg (pl v) * Nat.card V = Module.finrank ℚ F := by
  classical
  let p : Ideal ℤ := Ideal.span {((l : ℕ) : ℤ)}
  have hpp : p.IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)
  haveI hpmax : p.IsMaximal :=
    hpp.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.out.ne_zero)
  have hlo : ∀ P : Ideal (𝓞 F), P.IsPrime → ((l : ℕ) : 𝓞 F) ∈ P → P.LiesOver p := by
    intro P hP hlP
    constructor
    apply hpmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 F) ((l : ℕ) : ℤ) ∈ P
    rwa [map_natCast]
  let f : V → p.primesOver (𝓞 F) := fun u =>
    ⟨(pl u).asIdeal, (pl u).isPrime, hlo _ (pl u).isPrime (hm u)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      apply hi
      exact HeightOneSpectrum.ext (congrArg Subtype.val h)
    · rintro ⟨P, hP, hPl⟩
      have hlP : ((l : ℕ) : 𝓞 F) ∈ P := by
        have hm' : ((l : ℕ) : ℤ) ∈ p := Ideal.subset_span (Set.mem_singleton _)
        rw [hPl.over] at hm'
        have hm'' := Ideal.mem_comap.1 hm'
        rwa [map_natCast] at hm''
      have hne : P ≠ ⊥ := by
        intro h
        rw [h, Ideal.mem_bot] at hlP
        exact hl.out.ne_zero (by exact_mod_cast hlP)
      obtain ⟨u, hu⟩ := hs ⟨P, hP, hne⟩ hlP
      exact ⟨u, Subtype.ext (congrArg HeightOneSpectrum.asIdeal hu)⟩
  have key : (p.primesOver (𝓞 F)).ncard = Nat.card V := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_eq_of_bijective f hf).symm
  have hG := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p (𝓞 F) (F ≃ₐ[ℚ] F)
  haveI := hlo _ (pl v).isPrime (hm v)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p (pl v).asIdeal (F ≃ₐ[ℚ] F),
    Ideal.inertiaDegIn_eq_inertiaDeg p (pl v).asIdeal (F ≃ₐ[ℚ] F), key,
    IsGalois.card_aut_eq_finrank] at hG
  rw [← hG, mul_comm]
  rfl

theorem UpperTheory.exists_place_over_l_locDeg_mul_card_eq :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (v : T.ι), ∃ w : HeightOneSpectrum (𝓞 T.F), IsPlaceOver (T.pl v) w ∧ ((l : ℕ) : 𝓞 T.F) ∈ w.asIdeal ∧ locDeg w * Nat.card T.ι = T.d := by
  intro Ω _ _ _ l _ c D T v
  haveI := T.nF
  haveI := T.abF
  haveI hac : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  have hlt : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 T.F)), IsPlaceOver A w →
      (A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 T.F) ∈ w.asIdeal) := by
    intro A w hA
    rw [← hA]
    simp
  choose P hPS hP using fun u => GlobalTheory.DecLocal.exists_place_below (p := l) (F := T.F) (T.pl u) (T.ovl u)
  have hPl : ∀ u, ((l : ℕ) : 𝓞 T.F) ∈ (P u).asIdeal := fun u => hPS u
  refine ⟨P v, hP v, hPl v, td_count l T.F P ?_ hPl ?_ v⟩
  · intro u u' h
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hP u) (by rw [h]; exact hP u')
    obtain ⟨v0, -, huniq⟩ := T.cover (T.pl u) (T.ovl u)
    have e1 := huniq u ⟨1, fun x => by simp⟩
    have e2 := huniq u' ⟨σ⁻¹, fun x => by
      rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]⟩
    exact e1.trans e2.symm
  · intro w hw
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨u, ⟨g, hg⟩, -⟩ := T.cover A ((hlt A w hA).2 hw)
    exact ⟨u, eq_of_isPlaceOver (hP u) (td_move g hg hA)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.NonemptyLocalWeilDataDecompositionGroupOfMemPlac
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

private theorem ab_map {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] (f : G →* G') (hf : Continuous f) :
    ∃ F : TopologicalAbelianization G →* TopologicalAbelianization G',
      ∀ g : G, F (QuotientGroup.mk' _ g) = QuotientGroup.mk' _ (f g) := by
  have hc : (commutator G).topologicalClosure ≤ ((commutator G').topologicalClosure).comap f := by
    apply Subgroup.topologicalClosure_minimal
    · rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact Subgroup.le_topologicalClosure _
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    · exact (Subgroup.isClosed_topologicalClosure _).preimage hf
  exact ⟨QuotientGroup.map _ _ f hc, fun g => rfl⟩

private theorem map_prim {A B : Type} [CommGroup A] [CommGroup B] (l : ℕ) [Fact l.Prime] (F : A →* B) {x : A}
    (hx : x ∈ CommGroup.primaryComponent A l) : F x ∈ CommGroup.primaryComponent B l := by
  obtain ⟨k, hk⟩ := (Iff.rfl : x ∈ CommGroup.primaryComponent A l ↔ ∃ k : ℕ, x ^ l ^ k = 1).mp hx
  exact (Iff.rfl : F x ∈ CommGroup.primaryComponent B l ↔ ∃ k : ℕ, F x ^ l ^ k = 1).mpr
    ⟨k, by rw [← map_pow, hk, map_one]⟩

open UpperTheory.V.W in
private theorem locAb_transport (l : ℕ) [Fact l.Prime] {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (e : G ≃* G') (he : Continuous e) (he' : Continuous e.symm)
    (I : Subgroup G) (I' : Subgroup G') (hI : ∀ g, e g ∈ I' ↔ g ∈ I) (d : ℕ) (A : LocAb l G' I' d) :
    Nonempty (LocAb l G I d) := by
  obtain ⟨Fe, hFe⟩ := ab_map e.toMonoidHom he
  obtain ⟨Fs, hFs⟩ := ab_map e.symm.toMonoidHom he'
  have mu1 : ∀ g, g ∈ muG l G → e g ∈ muG l G' := by
    intro g hg
    have h1 := map_prim l Fe (x := QuotientGroup.mk' (commutator G).topologicalClosure g) hg
    have h2 := hFe g
    simp only [MulEquiv.coe_toMonoidHom] at h2
    rw [h2] at h1
    exact h1
  have mu2 : ∀ g', g' ∈ muG l G' → e.symm g' ∈ muG l G := by
    intro g hg
    have h1 := map_prim l Fs (x := QuotientGroup.mk' (commutator G').topologicalClosure g) hg
    have h2 := hFs g
    simp only [MulEquiv.coe_toMonoidHom] at h2
    rw [h2] at h1
    exact h1
  let bm : CommGroup.primaryComponent (TopologicalAbelianization G') l →*
      CommGroup.primaryComponent (TopologicalAbelianization G) l :=
    MonoidHom.codRestrict (Fs.comp (CommGroup.primaryComponent _ l).subtype) _
      (fun x => map_prim l Fs x.2)
  refine ⟨LocAb.mk (A.a.comp e.toMonoidHom) (A.cont.comp he) (A.surj.comp e.surjective) ?_ ?_
    ((bm.comp A.b).comp e.toMonoidHom) ?_ ?_⟩
  · intro x
    rw [← A.inertia x]
    constructor
    · rintro ⟨g, hg, h⟩
      exact ⟨e g, (hI g).2 hg, h⟩
    · rintro ⟨g', hg', h⟩
      exact ⟨e.symm g', (hI _).1 (by simpa using hg'), by simpa using h⟩
  · intro C _ _ hC χ hχo hmu
    have key := A.univ C hC (χ.comp e.symm.toMonoidHom) (hχo.preimage he') (by
      intro g' hg'
      exact (MonoidHom.mem_ker).1 (hmu (mu2 g' hg')))
    intro g hg
    have h3 : e g ∈ (χ.comp e.symm.toMonoidHom).ker :=
      key (MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hg))
    have h5 := MonoidHom.mem_ker.1 h3
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h5
    exact MonoidHom.mem_ker.2 h5
  · refine Subgroup.isOpen_mono (H₁ := A.b.ker.comap e.toMonoidHom) ?_ (A.b_open.preimage he)
    intro g hg
    rw [Subgroup.mem_comap, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, hg, map_one]
  · intro g hg
    show Fs ((A.b (e g)) : TopologicalAbelianization G') = _
    rw [A.b_mu _ (mu1 g hg)]
    have h4 := hFs (e g)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h4
    exact h4

open Formalism.BasicNotions.Loc in
theorem UpperTheory.nonempty_localWeilData_decompositionGroup_of_mem_place :
    ∀ (l : ℕ) [Fact l.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)), IsPlaceOver A w → ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → Nonempty (UpperTheory.V.W.LocAb l (Dec (F := F) A) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) (locDeg w)) := by
  intro l _ F Ω _ _ _ _ _ _ A w hA hl
  obtain ⟨j, hj⟩ := (UpperTheory.V.Loc.decEmb (F := F) (Ω := Ω) (v := l)).1 A w hA hl
  subst hj
  obtain ⟨-, φ, hφ, -, hran, hin, -, hidx⟩ := (UpperTheory.V.Loc.decEmb (F := F) (Ω := Ω) (v := l)).2 j
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : F => j (algebraMap F Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK : ∀ τ, τ ∈ GK K ↔ ∀ x : F, τ (j (algebraMap F Ω x)) = j (algebraMap F Ω x) :=
    GlobalTheory.PlaceBridge.mem_GK_iff (E := F) (Ω := Ω) K rfl
  have hR : φ.range = GK K := by
    ext τ
    rw [hran τ, hK τ]
  have hd : Module.finrank ℚ_[l] K.1 = locDeg w := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← hidx w hA, hR]
    rfl
  obtain ⟨B⟩ := UpperTheory.V.W.lam_local l K
  rw [hd] at B
  let e := (MonoidHom.ofInjective hφ.injective).trans (MulEquiv.subgroupCongr hR)
  refine locAb_transport l e ?_ ?_ _ _ ?_ _ B
  · exact continuous_induced_rng.2 hφ.continuous
  · refine hφ.toIsEmbedding.continuous_iff.2 ?_
    have h : (⇑φ ∘ ⇑e.symm) = Subtype.val := funext fun τ => congrArg Subtype.val (e.apply_symm_apply τ)
    rw [h]
    exact continuous_subtype_val
  · intro g
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hin g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsMemPinsInsertKerOfPadicCharacter
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Ws

theorem UpperTheory.exists_mem_pins_insert_ker_of_padic_character :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (I : Subgroup G), IsClosed (I : Set G) → ∀ ε : G →* ℤ_[l]ˣ, Continuous ε → ∃ s ∈ I, Pins l I (insert s {g | g ∈ I ∧ ε g = 1}) := by
  intro l _ hl G _ _ _ _ I hI ε hε
  have hclo : ∀ K : Subgroup G, IsClosed (K : Set G) →
      IsClosed ((K.map ε : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    intro K hK
    rw [Subgroup.coe_map]
    exact (hK.isCompact.image hε).isClosed
  obtain ⟨γ, hγ, hV⟩ := UpperTheory.V.Kum.existsGen l (I.map ε) (hclo I hI) (Or.inl hl)
  obtain ⟨s, hsI, rfl⟩ := Subgroup.mem_map.mp hγ
  refine ⟨s, hsI, ?_⟩
  intro R _ _ _ _ _ ψ hψ _ hS g hg
  have hK : IsClosed ((ψ.ker ⊓ I : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]
    exact (isClosed_ker_of_adicCont ψ hψ).inter hI
  have hsK : s ∈ ψ.ker ⊓ I :=
    Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr (hS s (Set.mem_insert _ _)), hsI⟩
  have hle : I.map ε ≤ (ψ.ker ⊓ I).map ε := by
    refine hV.trans (Subgroup.topologicalClosure_minimal _ ?_ (hclo _ hK))
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_map_of_mem _ hsK
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_map_of_mem ε hg))
  have hk' := Subgroup.mem_inf.mp hk
  have h1 : ψ (g * k⁻¹) = 1 :=
    hS _ (Set.mem_insert_of_mem _ ⟨I.mul_mem hg (I.inv_mem hk'.2), by simp [hkg]⟩)
  have hk1 : ψ k = 1 := MonoidHom.mem_ker.mp hk'.1
  simpa [hk1] using h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsPinningElementsOfLocAb
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Ws

section
open UpperTheory.V.W

end

private theorem exists_pow_l_pow_eq_one_of_mem_muG {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (ψ : G →* Rˣ) (hψc : AdicCont (maximalIdeal R) fun g => ((ψ g : Rˣ) : R))
    (g : G) (hg : g ∈ UpperTheory.V.W.muG l G) : ∃ n : ℕ, ψ g ^ (l ^ n) = 1 := by
  obtain ⟨n, hn⟩ := CommGroup.mem_primaryComponent.1 hg
  refine ⟨n, ?_⟩
  have h1 : g ^ (l ^ n) ∈ (commutator G).topologicalClosure := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hn
  have hker : (commutator G).topologicalClosure ≤ ψ.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker ψ)
      (isClosed_ker_of_adicCont ψ hψc)
  rw [← map_pow]
  exact hker h1

theorem UpperTheory.exists_pinning_elements_of_locAb :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (I : Subgroup G) (d : ℕ), UpperTheory.V.W.LocAb l G I d → ∃ s : Fin d → G, (∀ k, s k ∈ I) ∧ Pins l I (Set.range s) := by
  intro l _ G _ _ _ _ I d A
  have hlp : l.Prime := Fact.out
  have hs : ∀ k : Fin d, ∃ g ∈ I,
      A.a g = Multiplicative.ofAdd ((Pi.single k 1 : Fin d → ℤ_[l]), (0 : ℤ_[l])) :=
    fun k => (A.inertia _).2 rfl
  choose s hsI hsa using hs
  refine ⟨s, hsI, ?_⟩
  intro R _ _ _ _ hl ψ hψc hψI hψs g hg
  haveI : CharP R l := (CharP.charP_iff_prime_eq_zero hlp).2 hl
  have hsk : ∀ k, ψ (s k) = 1 := fun k => hψs _ ⟨k, rfl⟩
  have hq : ∀ (N : ℕ) (u : Rˣ),
      Units.map (↑(Ideal.Quotient.mk (maximalIdeal R ^ N)) : R →* R ⧸ maximalIdeal R ^ N) u = 1 ↔
        (u : R) - 1 ∈ maximalIdeal R ^ N := by
    intro N u
    rw [Units.ext_iff]
    show Ideal.Quotient.mk (maximalIdeal R ^ N) (u : R) = 1 ↔ _
    rw [← map_one (Ideal.Quotient.mk (maximalIdeal R ^ N)), Ideal.Quotient.eq]
  let ρN : (N : ℕ) → G →* (R ⧸ maximalIdeal R ^ N)ˣ := fun N =>
    (Units.map (↑(Ideal.Quotient.mk (maximalIdeal R ^ N)) : R →* R ⧸ maximalIdeal R ^ N)).comp ψ
  have hloc : ∀ N, IsLocallyConstant (ρN N) := fun N => (adicCont_units _ _).1 hψc N
  haveI hfin1 : Finite (ρN 1).range := (hloc 1).range_finite.to_subtype
  set M := Nat.card (ρN 1).range with hMdef
  have hM0 : M ≠ 0 := Nat.card_pos.ne'
  have hres : ∀ g, ((ψ g ^ M : Rˣ) : R) - 1 ∈ maximalIdeal R := by
    intro g
    have h1 := congrArg (fun u : (ρN 1).range => (u : (R ⧸ maximalIdeal R ^ 1)ˣ))
      (pow_card_eq_one' (G := (ρN 1).range) (x := ⟨ρN 1 g, g, rfl⟩))
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, ← hMdef] at h1
    rw [← map_pow] at h1
    simpa using (hq 1 _).1 h1
  have hmu : ∀ g ∈ UpperTheory.V.W.muG l G, ψ g ^ M = 1 := by
    intro g hg
    obtain ⟨n, hn⟩ := exists_pow_l_pow_eq_one_of_mem_muG ψ hψc g hg
    apply Units.ext
    refine eq_one_of_pow hl (hres g) (pow_ne_zero n hlp.ne_zero) ?_
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hn, one_pow, Units.val_one]
  let φN : (N : ℕ) → G →* (R ⧸ maximalIdeal R ^ N)ˣ := fun N => (powMonoidHom M).comp (ρN N)
  have hφloc : ∀ N, IsLocallyConstant (φN N) := fun N => (hloc N).comp (fun u => u ^ M)
  have hφ : ∀ N g, φN N g = 1 ↔ ((ψ g ^ M : Rˣ) : R) - 1 ∈ maximalIdeal R ^ N := by
    intro N g
    rw [← hq]
    rw [map_pow]
    exact Iff.rfl
  have hφp : ∀ N g, (φN N g) ^ (l ^ N) = 1 := by
    intro N g
    rw [← map_pow, hφ]
    set y := ((ψ g ^ M : Rˣ) : R) - 1 with hy
    have hym : y ∈ maximalIdeal R := hres g
    have : (((ψ g ^ M) ^ (l ^ N) : Rˣ) : R) = 1 + y ^ (l ^ N) := by
      rw [Units.val_pow_eq_pow_val, show ((ψ g ^ M : Rˣ) : R) = 1 + y by rw [hy]; ring,
        add_pow_char_pow, one_pow]
    rw [map_pow, ← pow_mul, mul_comm (l ^ N) M, pow_mul, this, add_sub_cancel_left]
    exact Ideal.pow_le_pow_right (Nat.lt_pow_self hlp.one_lt).le (Ideal.pow_mem_pow hym _)
  have hK : ∀ N, A.a.ker ≤ (φN N).ker := by
    intro N
    haveI : Finite (φN N).range := (hφloc N).range_finite.to_subtype
    have hP : IsPGroup l (φN N).range := by
      rintro ⟨x, g, rfl⟩
      exact ⟨N, Subtype.ext (hφp N g)⟩
    have := A.univ (φN N).range hP (φN N).rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict]; exact (hφloc N).isOpen_fiber 1)
      (by
        intro g hg
        rw [MonoidHom.ker_rangeRestrict]
        exact (hφ N g).2 (by rw [hmu g hg, Units.val_one, sub_self]; exact zero_mem _))
    rwa [MonoidHom.ker_rangeRestrict] at this
  have hclosed : ∀ N, IsClosed ((Subgroup.map A.a (φN N).ker : Subgroup _) :
      Set (Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l]))) := by
    intro N
    rw [Subgroup.coe_map]
    exact (((hφloc N).isClosed_fiber 1).isCompact.image A.cont).isClosed
  have hmem : ∀ N (x : Fin d → ℤ_[l]),
      Multiplicative.ofAdd (x, (0 : ℤ_[l])) ∈ Subgroup.map A.a (φN N).ker := by
    intro N
    have hint : ∀ z : Fin d → ℤ, Multiplicative.ofAdd ((fun k => (z k : ℤ_[l])), (0 : ℤ_[l])) ∈
        Subgroup.map A.a (φN N).ker := by
      intro z
      have he : ((fun k => (z k : ℤ_[l])), (0 : ℤ_[l])) =
          ∑ k, z k • ((Pi.single k 1 : Fin d → ℤ_[l]), (0 : ℤ_[l])) := by
        refine Prod.ext ?_ ?_
        · funext j
          rw [Prod.fst_sum, Finset.sum_apply]
          simp [Pi.single_apply]
        · rw [Prod.snd_sum]
          simp
      rw [he, ofAdd_sum]
      refine Subgroup.prod_mem _ fun k _ => ?_
      rw [ofAdd_zsmul]
      refine Subgroup.zpow_mem _ ?_ _
      refine ⟨s k, ?_, hsa k⟩
      exact (hφ N (s k)).2 (by rw [hsk, one_pow, Units.val_one, sub_self]; exact zero_mem _)
    have hT : IsClosed {x : Fin d → ℤ_[l] |
        Multiplicative.ofAdd (x, (0 : ℤ_[l])) ∈ Subgroup.map A.a (φN N).ker} :=
      (hclosed N).preimage (continuous_ofAdd.comp (continuous_id.prodMk continuous_const))
    have hD : DenseRange (Pi.map fun (_ : Fin d) (z : ℤ) => (z : ℤ_[l])) :=
      DenseRange.piMap fun _ => PadicInt.denseRange_intCast
    intro x
    have hx : x ∈ closure (Set.range (Pi.map fun (_ : Fin d) (z : ℤ) => (z : ℤ_[l]))) := by
      rw [hD.closure_eq]
      exact Set.mem_univ x
    exact hT.closure_subset_iff.2 (by rintro _ ⟨z, rfl⟩; exact hint z) hx
  have hgN : ∀ N, φN N g = 1 := by
    intro N
    obtain ⟨x, hx⟩ : ∃ x, A.a g = Multiplicative.ofAdd x := ⟨Multiplicative.toAdd (A.a g), rfl⟩
    have hx2 : x.2 = 0 := (A.inertia x).1 ⟨g, hg, hx⟩
    obtain ⟨h, hh, hah⟩ := hmem N x.1
    have hk : h⁻¹ * g ∈ A.a.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hah, hx, inv_mul_eq_one, ← hx2]
    have := hK N hk
    rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.1 hh, inv_one, one_mul] at this
    exact this
  have hzero : ((ψ g ^ M : Rˣ) : R) - 1 = 0 := by
    have : ((ψ g ^ M : Rˣ) : R) - 1 ∈ ⨅ N, maximalIdeal R ^ N :=
      Ideal.mem_iInf.2 fun N => (hφ N g).1 (hgN N)
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
      Ideal.mem_bot] at this
  apply Units.ext
  refine eq_one_of_pow hl (hψI g hg) hM0 ?_
  rw [← Units.val_pow_eq_pow_val]
  exact sub_eq_zero.1 hzero
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.KrullDimQuotientLeCardOfRadicalParameters
open IsLocalRing

theorem UpperTheory.krullDim_quotient_le_card_of_radical_parameters :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (q : Ideal B) (κ : Type) [Finite κ] (x : κ → B), (∀ k, x k ∈ maximalIdeal B) → (∀ p : Ideal B, p.IsPrime → q ≤ p → (∀ k, x k ∈ p) → maximalIdeal B ≤ p) → ringKrullDim (B ⧸ q) ≤ Nat.card κ := by
  intro B _ _ _ q κ _ x hx h
  classical
  by_cases hq : q = ⊤
  · subst hq
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  haveI : Nontrivial (B ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hq
  haveI : IsLocalRing (B ⧸ q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let s : Set (B ⧸ q) := Set.range (fun k => Ideal.Quotient.mk q (x k))
  have hs : s.Finite := Set.finite_range _
  have hmin : maximalIdeal (B ⧸ q) ∈ (Ideal.span s).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      exact map_nonunit (Ideal.Quotient.mk q) _ (hx k)
    · rintro P ⟨hP, hsP⟩ _
      have h1 : maximalIdeal B ≤ P.comap (Ideal.Quotient.mk q) := by
        refine h _ (Ideal.comap_isPrime _ _) ?_ ?_
        · intro a ha
          rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
          exact P.zero_mem
        · intro k
          exact hsP (Ideal.subset_span ⟨k, rfl⟩)
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply h1
      rw [mem_maximalIdeal] at hy ⊢
      exact fun hu => hy (hu.map _)
  have h2 := Ideal.height_le_card_of_mem_minimalPrimes_span hs hmin
  have h3 : s.ncard ≤ Nat.card κ := by
    rw [← Set.ncard_univ, show s = (fun k => Ideal.Quotient.mk q (x k)) '' Set.univ from Set.image_univ.symm]
    exact Set.ncard_image_le Set.finite_univ
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have h4 : (maximalIdeal (B ⧸ q)).height ≤ (Nat.card κ : ℕ∞) := h2.trans (by exact_mod_cast h3)
  exact_mod_cast h4
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.nn :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PM ι X J → ∀ (v : T.ι) (i j : Fin 4), i ≠ j → ∀ (q : Ideal X.B), q.IsPrime → J ≤ q → (maximalIdeal c'.O).map (algebraMap c'.O X.B) ≤ q →
      (∀ s ∈ T.U1 v, X.ψ v i s - X.ψ v j s ∈ q) → ∀ dv : ℕ, dv * Nat.card T.ι = T.d → ringKrullDim (X.B ⧸ q) + dv ≤ (2 * T.d + 1 : ℕ) := by
  classical
  intro _ Ω _ _ _ l _ c D T hFit _ ι c' h X J hPM v i j hij q hq hJ hϖ hU dv hdv
  have hOk := hFit.1
  have hl2 : l ≠ 2 := by
    rcases hFit.2 with h | h
    · exact h.1.1.l_odd
    · exact h.1.1.l_odd
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  haveI : IsGalois T.F Ω := IsAlgClosure.isGalois T.F Ω
  haveI : Nonempty T.ι := ⟨v⟩
  have hg : 0 < Nat.card T.ι := Nat.card_pos
  haveI hcD : ∀ u, CompactSpace (Dec (F := T.F) (T.pl u)) := fun u =>
    isCompact_iff_compactSpace.1 (isClosed_Dec (T.pl u)).isCompact
  let I : ∀ u, Subgroup (Dec (F := T.F) (T.pl u)) := fun u => (Ine (F := T.F) (T.pl u)).subgroupOf _
  have hs : ∀ u, ∃ s : Fin dv → Dec (F := T.F) (T.pl u), (∀ k, s k ∈ I u) ∧ Pins l (I u) (Set.range s) := fun u => by
    obtain ⟨w, hw, hlw, hd⟩ := UpperTheory.exists_place_over_l_locDeg_mul_card_eq D T u
    obtain ⟨A⟩ := UpperTheory.nonempty_localWeilData_decompositionGroup_of_mem_place l (T.pl u) w hw hlw
    obtain rfl : locDeg w = dv := Nat.eq_of_mul_eq_mul_right hg (hd.trans hdv.symm)
    exact UpperTheory.exists_pinning_elements_of_locAb l _ _ _ A
  choose s hsI hsP using hs
  obtain ⟨s0, hs0, hP0⟩ := UpperTheory.exists_mem_pins_insert_ker_of_padic_character l hl2 _ (I v) ((isClosed_Ine (T.pl v)).preimage continuous_subtype_val)
    ((cycZ T.F Ω l).comp (Dec (F := T.F) (T.pl v)).subtype) ((continuous_cycZ T.F Ω l).comp continuous_subtype_val)
  obtain ⟨a, ha, ha'⟩ : ∃ a : Fin 4, (a = j ∨ j = i.rev) ∧ ∀ m : Fin 4, m = a ∨ m = a.rev ∨ m = i ∨ m = i.rev :=
    (by decide : ∀ i j : Fin 4, i ≠ j → ∃ a : Fin 4, (a = j ∨ j = i.rev) ∧
      ∀ m : Fin 4, m = a ∨ m = a.rev ∨ m = i ∨ m = i.rev) i j hij
  let x : (T.ι × Fin dv) ⊕ ({u // u ≠ v} × Fin dv) ⊕ Unit → X.B :=
    Sum.elim (fun y => X.ψ y.1 a (s y.1 y.2) - 1)
      (Sum.elim (fun y => X.ψ y.1.1 i (s y.1.1 y.2) - 1) fun _ => X.ψ v i s0 - X.ψ v j s0)
  have hm : ∀ u m (t : Dec (F := T.F) (T.pl u)), t ∈ I u → X.ψ u m t - 1 ∈ maximalIdeal X.B := fun u m t ht => by
    obtain ⟨-, κ, hκ⟩ := UpperTheory.deformationSpace_local_characters_continuous D T hOk c' h X _ (residue X.B) (fun b hb => by
      rw [(residue_eq_zero_iff b).2 hb]; exact zero_mem _) (fun b hb => (residue_eq_zero_iff _).2 (map_nonunit _ b hb))
    have h1 := ((hκ u m).2.2 t ht).1
    rw [(hκ u m).1, maximalIdeal_eq_bot, Ideal.mem_bot, ← map_one (residue X.B), ← map_sub, residue_eq_zero_iff] at h1
    exact h1
  have hdim := UpperTheory.krullDim_quotient_le_card_of_radical_parameters X.B q _ x ?_ ?_
  · have hc : Nat.card ((T.ι × Fin dv) ⊕ ({u // u ≠ v} × Fin dv) ⊕ Unit) + dv = 2 * T.d + 1 := by
      have h1 : Nat.card {u // u ≠ v} + 1 = Nat.card T.ι := by
        rw [← Finite.card_option]
        exact Nat.card_congr (Equiv.optionSubtypeNe v)
      simp only [Nat.card_sum, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin dv), Fintype.card_fin, Nat.card_unique]
      rw [← hdv, ← h1]
      ring
    rw [← hc, Nat.cast_add]
    gcongr
  · rintro (y | y | y)
    · exact hm _ _ _ (hsI _ _)
    · exact hm _ _ _ (hsI _ _)
    · simpa [x] using sub_mem (hm v i s0 hs0) (hm v j s0 hs0)
  intro p hp hqp hx
  haveI : IsLocalRing (X.B ⧸ p) := IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk p) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨h0, κ, hκ⟩ := UpperTheory.deformationSpace_local_characters_continuous D T hOk c' h X _ (Ideal.Quotient.mk p) (fun b hb => map_nonunit _ b hb)
    (fun b hb => Ideal.Quotient.eq_zero_iff_mem.2 (hqp (hϖ (Ideal.mem_map_of_mem _ hb))))
  have h1 : ∀ u m (t : Dec (F := T.F) (T.pl u)), κ u m t = 1 ↔ X.ψ u m t - 1 ∈ p := fun u m t => by
    rw [← Units.val_eq_one, (hκ u m).1, ← Ideal.Quotient.eq, map_one]
  have hpin : ∀ u m, (∀ k, X.ψ u m (s u k) - 1 ∈ p) → ∀ t ∈ I u, κ u m t = 1 := fun u m hk =>
    hsP u _ h0 (κ u m) (hκ u m).2.1 (fun t ht => ((hκ u m).2.2 t ht).1) (by
      rintro _ ⟨k, rfl⟩; exact (h1 _ _ _).2 (hk k))
  have hA : ∀ u, ∀ t ∈ I u, κ u a t = 1 := fun u => hpin u a fun k => hx (.inl (u, k))
  have hE : ∀ t ∈ I v, κ v i t = κ v j t := by
    refine hP0.eq h0 _ _ (hκ v i).2.1 (hκ v j).2.1 (fun t ht => ((hκ v i).2.2 t ht).1)
      (fun t ht => ((hκ v j).2.2 t ht).1) fun t ht => Units.ext ?_
    rw [(hκ v i).1, (hκ v j).1, Ideal.Quotient.eq]
    rcases ht with rfl | ⟨ht, ht'⟩
    · exact hx (.inr (.inr ()))
    · exact hqp (hU t ⟨ht, ht', hOk.ineL _ (T.ovl v) _ ht⟩)
  have hI : ∀ u, ∀ t ∈ I u, κ u i t = 1 := fun u => by
    by_cases hu : u = v
    · subst hu
      intro t ht
      rcases ha with rfl | rfl
      · exact (hE t ht).trans (hA u t ht)
      · have h2 := (hκ u i).2.2 t ht
        refine Units.val_eq_one.1 (eq_one_of_pow h0 h2.1 two_ne_zero ?_)
        rw [← Units.val_pow_eq_pow_val, sq, Units.val_eq_one]
        rw [← hE t ht] at h2
        exact h2.2
    · exact hpin u i fun k => hx (.inr (.inl (⟨u, hu⟩, k)))
  have hall : ∀ u m, ∀ t ∈ I u, κ u m t = 1 := fun u m t ht => by
    rcases ha' m with rfl | rfl | rfl | rfl
    · exact hA u t ht
    · simpa [hA u t ht] using ((hκ u a).2.2 t ht).2
    · exact hI u t ht
    · simpa [hI u t ht] using ((hκ u i).2.2 t ht).2
  obtain ⟨n, hn⟩ := hPM.fin
  refine hp.le_of_pow_le (n := n) (hn.trans (sup_le (sup_le (hJ.trans hqp) (hϖ.trans hqp)) (Ideal.span_le.2 ?_)))
  rintro _ ⟨u, m, t, ht, rfl⟩
  exact (h1 u m ⟨t, Ine_le_Dec _ ht⟩).1 (hall u m _ ht)
