module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuotDivLatMulLatHomAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT

theorem finite_quot_divLat_mulLat_homAt :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (cA c : ℕ), Submodule.IsLattice E N → Submodule.IsLattice E N' → 0 < cA → 0 < c → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
  by
  intro E _ _ _ a b S N N' cA cB hN hN' hA hB
  classical
  obtain ⟨G, hG⟩ := hN.fg
  have hA' : (cA : E) ≠ 0 := by exact_mod_cast hA.ne'
  have hB' : (cB : E) ≠ 0 := by exact_mod_cast hB.ne'
  have memD : ∀ x : HomE E a b, x ∈ divLat cA (homAt S N N') ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, (cA : 𝓞 E) • x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  have memM : ∀ x : HomE E a b, x ∈ mulLat cB (homAt S N N') ↔
      ∃ h ∈ homAt S N N', (cB : 𝓞 E) • h = x := fun x => Iff.rfl
  have memH : ∀ x : HomE E a b, x ∈ homAt S N N' ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  let ev : HomE E a b →ₗ[𝓞 E] (G → Sp E b) :=
    { toFun := fun x g => (cA : 𝓞 E) • x g
      map_add' := by intro x y; funext g; simp
      map_smul' := by intro r x; funext g; simp [smul_comm r] }
  let T : Submodule (𝓞 E) (G → Sp E b) := Submodule.pi Set.univ fun _ => N'
  have hT : T.FG := Submodule.fg_pi fun _ => hN'.fg
  let Z : Submodule (𝓞 E) (HomE E a b) := T.comap ev
  have memZ : ∀ x : HomE E a b, x ∈ Z ↔ ∀ g : G, (cA : 𝓞 E) • x g ∈ N' := fun x =>
    ⟨fun h g => h g trivial, fun h g _ => h g⟩
  have hZD : Z ≤ divLat cA (homAt S N N') := by
    intro x hx
    rw [memD]
    intro P hP y hy
    obtain ⟨s, hs, hsy⟩ := (mem_locP P N y).1 hy
    have : ∀ w ∈ N, (cA : 𝓞 E) • x w ∈ N' := by
      intro w hw
      rw [← hG] at hw
      induction hw using Submodule.span_induction with
      | mem g hg => exact (memZ x).1 hx ⟨g, hg⟩
      | zero => simp
      | add u v _ _ hu hv => rw [map_add (f := _), smul_add]; exact N'.add_mem hu hv
      | smul r u _ hu => rw [LinearMap.map_smul_of_tower, smul_comm]; exact N'.smul_mem r hu
    refine (mem_locP P N' _).2 ⟨s, hs, ?_⟩
    have h := this _ hsy
    rwa [LinearMap.map_smul_of_tower, smul_comm] at h
  have hc : ((cB : 𝓞 E) * cA) ≠ 0 := by
    have : cB * cA ≠ 0 := by positivity
    exact_mod_cast this
  have : Finite (𝓞 E ⧸ Ideal.span {(cB : 𝓞 E) * cA}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa [Ideal.span_singleton_eq_bot] using hc)
  have hsurj : Function.Surjective
      (((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype).mkQ ∘ₗ Submodule.inclusion hZD) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    let I : Ideal (𝓞 E) := Z.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
    have hI : ∀ P ∈ S, ∃ s ∈ I, s ∉ P.asIdeal := by
      intro P hP
      have h1 : ∀ g : G, ∃ s ∉ P.asIdeal, s • (cA : 𝓞 E) • x g ∈ N' := fun g =>
        (mem_locP P N' _).1 ((memD x).1 hx P hP g (le_locP P N (hG ▸ Submodule.subset_span g.2)))
      choose f hf hf' using h1
      refine ⟨∏ g, f g, ?_, ?_⟩
      · show (∏ g, f g) • x ∈ Z
        rw [memZ]
        intro g
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ g), LinearMap.smul_apply, smul_comm, mul_smul]
        exact N'.smul_mem _ (hf' g)
      · intro h
        have := P.isPrime
        obtain ⟨g, _, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
        exact hf g hg
    obtain ⟨s, hs, t, r, ht, htr⟩ := GlobalTheory.exists_mem_one_sub_loc_dvd S I hI ((cB : 𝓞 E) * cA)
    refine ⟨⟨s • x, hs⟩, ?_⟩
    symm
    refine (Submodule.Quotient.eq _).2 ?_
    show x - s • x ∈ mulLat cB (homAt S N N')
    have hBinv : ∀ {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] (w : W),
        (cB : 𝓞 E) • (cB : E)⁻¹ • w = w := by
      intro W _ _ _ w
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hB', one_smul]
    rw [memM]
    refine ⟨(cB : E)⁻¹ • (x - s • x), ?_, hBinv _⟩
    rw [memH]
    intro P hP y hy
    obtain ⟨u, hu, huy⟩ := (mem_locP P N' _).1 ((memD x).1 hx P hP y hy)
    refine (mem_locP P N' _).2 ⟨u * t, fun h => (P.isPrime.mem_or_mem h).elim hu (ht P hP), ?_⟩
    have e1 : t • ((cB : E)⁻¹ • (x - s • x)) y = r • (cA : 𝓞 E) • x y := by
      have e2 : (x - s • x) y = (1 - s) • x y := by simp [sub_smul]
      rw [LinearMap.smul_apply, smul_comm, e2, smul_smul t, htr, mul_assoc, mul_smul, smul_comm, hBinv, mul_comm, mul_smul]
    rw [mul_smul, e1, smul_comm]
    exact N'.smul_mem r huy
  let f : Z →ₗ[𝓞 E] T := ev.restrict (p := Z) (q := T) fun x hx => hx
  let q : Z →ₗ[𝓞 E] _ :=
    ((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype).mkQ ∘ₗ Submodule.inclusion hZD
  have hk : LinearMap.ker f ≤ LinearMap.ker q := by
    intro x hx
    have hxg : ∀ g : G, (x : HomE E a b) g = 0 := by
      intro g
      have h := congrFun (congrArg Subtype.val (LinearMap.mem_ker.mp hx)) g
      have h2 : (cA : E) • (x : HomE E a b) g = 0 := by
        rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
        exact h
      exact (smul_eq_zero.mp h2).resolve_left hA'
    have hxN : ∀ y ∈ N, (x : HomE E a b) y = 0 := by
      intro y hy
      rw [← hG] at hy
      induction hy using Submodule.span_induction with
      | mem g hg => exact hxg ⟨g, hg⟩
      | zero => simp
      | add u v _ _ hu hv => simp [hu, hv]
      | smul r u _ hu => simp [LinearMap.map_smul_of_tower, hu]
    have hxloc : ∀ (P : HeightOneSpectrum (𝓞 E)), ∀ y ∈ localization₂ P.asIdeal N, (x : HomE E a b) y = 0 := by
      intro P y hy
      obtain ⟨s, hs, hsy⟩ := (mem_locP P N y).1 hy
      have hs0 : (s : E) ≠ 0 := by
        intro h
        have : s = 0 := by exact_mod_cast h
        exact hs (this ▸ P.asIdeal.zero_mem)
      have h := hxN _ hsy
      rw [LinearMap.map_smul_of_tower] at h
      have h' : (s : E) • (x : HomE E a b) y = 0 := by
        exact h
      exact (smul_eq_zero.mp h').resolve_left hs0
    apply LinearMap.mem_ker.mpr
    change Submodule.Quotient.mk (Submodule.inclusion hZD x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change (x : HomE E a b) ∈ mulLat cB (homAt S N N')
    rw [memM]
    refine ⟨(cB : E)⁻¹ • (x : HomE E a b), ?_, ?_⟩
    · rw [memH]
      intro P hP y hy
      simp [hxloc P y hy]
    · ext y
      simp only [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, mul_inv_cancel₀ hB', one_smul]
  have : Module.Finite (𝓞 E) T := Module.Finite.iff_fg.2 hT
  have : Module.Finite (𝓞 E) (LinearMap.range f) := Module.Finite.of_injective
    (LinearMap.range f).subtype Subtype.val_injective
  have : Module.Finite (𝓞 E) (Z ⧸ LinearMap.ker f) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  let q' := (LinearMap.ker f).liftQ q hk
  have hq' : Function.Surjective q' := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨Submodule.Quotient.mk x, hx⟩
  have := Module.Finite.of_surjective q' hq' 
  have : Module.Finite ℤ (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
    Module.Finite.trans (𝓞 E) _
  refine Module.finite_of_fg_torsion _ ?_
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨⟨((cB * cA : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
  rw [Submonoid.mk_smul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  show ((cB * cA : ℕ) : 𝓞 E) • x ∈ mulLat cB (homAt S N N')
  rw [memM]
  exact ⟨(cA : 𝓞 E) • x, hx, by rw [smul_smul, Nat.cast_mul]⟩


end GlobalTheory.MomT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RingHomEqOfComapEqUnramifiedDegreeOne
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem ringHom_eq_of_comap_eq_unramified_degree_one
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (φ ψ : E →+* K)
    (w : HeightOneSpectrum (𝓞 K)) (Q : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hp : p.Prime)
    (hN : Ideal.absNorm Q.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2)
    (hφ : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom φ r ∈ w.asIdeal)
    (hψ : ∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom ψ r ∈ w.asIdeal) :
    φ = ψ := by
  set f := RingOfIntegers.mapRingHom φ with hf
  set g := RingOfIntegers.mapRingHom ψ with hg
  have hpQ : ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal := hN ▸ Ideal.absNorm_mem Q.asIdeal
  have hQp := Q.isPrime

  have h1 : ∀ x : 𝓞 E, ∃ a : ℤ, x - (a : 𝓞 E) ∈ Q.asIdeal := by
    intro x
    haveI : Fact p.Prime := ⟨hp⟩
    have hc : Nat.card (𝓞 E ⧸ Q.asIdeal) = p := by
      rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have h := mem_zmultiples_of_prime_card (g := (1 : 𝓞 E ⧸ Q.asIdeal))
      (g' := Ideal.Quotient.mk Q.asIdeal x) hc one_ne_zero
    obtain ⟨a, ha⟩ := AddSubgroup.mem_zmultiples_iff.1 h
    refine ⟨a, Ideal.Quotient.eq.1 ?_⟩
    rw [← ha, map_intCast, zsmul_one]
  have h2 : Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2 = Q.asIdeal := by
    have h := Ideal.eq_prime_pow_of_succ_lt_of_le (P := Q.asIdeal) (i := 1)
      (I := Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2) Q.ne_bot ?_ ?_
    · simpa using h
    · refine lt_of_le_of_ne le_sup_right fun h => hsq ?_
      have h' : ((p : ℕ) : 𝓞 E) ∈ Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ 2 :=
        Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
      rw [← h] at h'
      exact h'
    · rw [pow_one]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hpQ) (Ideal.pow_le_self two_ne_zero)
  have h3 : ∀ n : ℕ, Q.asIdeal ≤ Ideal.span {((p : ℕ) : 𝓞 E)} ⊔ Q.asIdeal ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rcases n with _ | n
      · simp
      refine h2.ge.trans (sup_le le_sup_left ?_)
      rw [sq]
      refine (Ideal.mul_mono_right ih).trans ?_
      rw [Ideal.mul_sup, ← pow_succ']
      exact sup_le_sup_right Ideal.mul_le_right _
  have hmap : ∀ (k : 𝓞 E →+* 𝓞 K), (∀ r : 𝓞 E, r ∈ Q.asIdeal ↔ k r ∈ w.asIdeal) →
      ∀ (n : ℕ) (z : 𝓞 E), z ∈ Q.asIdeal ^ n → k z ∈ w.asIdeal ^ n := by
    intro k hk n z hz
    have h := Ideal.mem_map_of_mem k hz
    rw [Ideal.map_pow] at h
    refine Ideal.pow_right_mono ?_ n h
    exact Ideal.map_le_iff_le_comap.2 fun r hr => (hk r).1 hr
  have hpw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal := by
    simpa using (hφ _).1 hpQ
  have h4 : ∀ (n : ℕ) (x : 𝓞 E), f x - g x ∈ w.asIdeal ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x
      obtain ⟨a, ha⟩ := h1 x
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h3 (n + 1) ha)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have hx : x = c * p + z + a := by rw [hyz]; ring
      have he : f x - g x = (f c - g c) * p + (f z - g z) := by
        rw [hx]; simp only [map_add (f := _), map_mul, map_natCast, map_intCast]; ring
      rw [he]
      refine add_mem ?_ (sub_mem (hmap f hφ _ _ hz) (hmap g hψ _ _ hz))
      rw [pow_succ]
      exact Ideal.mul_mem_mul (ih c) hpw
  have h5 : ∀ x : 𝓞 E, f x = g x := by
    intro x
    have hb := Ideal.iInf_pow_eq_bot_of_isDomain w.asIdeal w.isPrime.ne_top
    have : f x - g x ∈ (⊥ : Ideal (𝓞 K)) := by
      rw [← hb]; exact Ideal.mem_iInf.2 fun n => h4 n x
    exact sub_eq_zero.1 (Ideal.mem_bot.1 this)
  refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => ?_
  exact congrArg (algebraMap (𝓞 K) K) (h5 x)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjPConjP
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
open nonZeroDivisors
noncomputable section
namespace GlobalTheory.CharVal.Vp
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem conjP_conjP' (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext x
  rw [mem_conjP, mem_conjP, cO_cO]

omit [StarRing E] in
theorem ne0 (P : HeightOneSpectrum (𝓞 E)) : (P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 P.ne_bot

omit [StarRing E] in
theorem maxV_self (P : HeightOneSpectrum (𝓞 E)) :
    MaxV P ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) (WithZero.exp (-1 : ℤ)) := by
  constructor
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have := (P.intValuation_le_pow_iff_mem r 1).2 (by simpa using hr)
    simpa using this
  · obtain ⟨r, hr⟩ := P.intValuation_exists_uniformizer
    refine ⟨algebraMap _ _ r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, ?_, rfl⟩, ?_⟩
    · have := (P.intValuation_le_pow_iff_mem r 1).1 (by simpa using hr.le)
      simpa using this
    · rw [HeightOneSpectrum.valuation_of_algebraMap, hr]

omit [StarRing E] in
theorem maxV_ne (Q P : HeightOneSpectrum (𝓞 E)) (h : Q ≠ P) :
    MaxV Q ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) 1 := by
  constructor
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    exact Q.valuation_le_one r
  · have : ¬ P.asIdeal ≤ Q.asIdeal := fun hle =>
      h (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle).symm)
    obtain ⟨r, hr, hr'⟩ := SetLike.not_le_iff_exists.1 this
    exact ⟨algebraMap _ _ r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩,
      (HeightOneSpectrum.valuation_eq_one_iff_notMem Q).2 hr'⟩

omit [StarRing E] in
theorem maxV_inv {Q P : HeightOneSpectrum (𝓞 E)} {γ : WithZero (Multiplicative ℤ)} (h0 : γ ≠ 0)
    (h : MaxV Q ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) γ) :
    MaxV Q (((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) γ⁻¹ :=
  h.inv h0 (by rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (ne0 P), FractionalIdeal.coe_one])

theorem mem_vp (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    x ∈ vpIdeal P ↔ ∀ r ∈ (conjPrime₂ P).asIdeal, ∃ s ∈ P.asIdeal, algebraMap _ E s = x * algebraMap _ E r := by
  unfold vpIdeal
  rw [← div_eq_mul_inv, FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero (ne0 _)]
  constructor
  · intro h r hr
    exact (FractionalIdeal.mem_coeIdeal _).1 (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩))
  · intro h y hy
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_coeIdeal _).2 (h r hr)

theorem star_mem_vp (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : x ∈ vpIdeal P) : star x ∈ vpIdeal (conjPrime₂ P) := by
  rw [mem_vp] at h ⊢
  intro r hr
  rw [conjP_conjP'] at hr
  obtain ⟨s, hs, e⟩ := h (cO E r) (by rwa [mem_conjP, cO_cO])
  refine ⟨cO E s, by rwa [mem_conjP, cO_cO], ?_⟩
  have e1 : algebraMap _ E (cO E s) = star (algebraMap _ E s) := rfl
  have e2 : algebraMap _ E (cO E r) = star (algebraMap _ E r) := rfl
  rw [e1, e, e2, star_mul, star_star, mul_comm]

theorem detLat_vp (P : HeightOneSpectrum (𝓞 E)) : detLat (vpLat P) = vpIdeal P := by
  unfold detLat
  rw [← Submodule.span_eq (vpIdeal P)]
  congr 1
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    have := hA _ (single_mem_stdLat (E := E) (0 : Fin 1) 1)
    rw [Matrix.det_fin_one]
    simpa [vpLat, Matrix.mulVec_single] using this
  · intro hx
    refine ⟨Matrix.of fun _ _ => x, fun v hv => ?_, by simp⟩
    obtain ⟨r, hr⟩ := (mem_stdLat v).1 hv 0
    have : (Matrix.of fun _ _ => x : Matrix (Fin 1) (Fin 1) E).mulVec v 0 = r • x := by
      simp [Matrix.mulVec, dotProduct, ← hr, Algebra.smul_def, mul_comm]
    show (Matrix.of fun _ _ => x : Matrix (Fin 1) (Fin 1) E).mulVec v 0 ∈ vpIdeal P
    rw [this]
    exact (vpIdeal P).smul_mem r hx

theorem vp_main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)), P ≠ conjPrime₂ P → (∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ star x ∈ vpIdeal P) ∧ vpIdeal P * J = 1) ∧ MaxV P (vpIdeal P) (WithZero.exp (-1 : ℤ)) ∧ MaxV (conjPrime₂ P) (vpIdeal P) (WithZero.exp (1 : ℤ)) ∧ (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q ≠ conjPrime₂ P → MaxV Q (vpIdeal P) 1) ∧ detLat (vpLat P) = vpIdeal P := by
  intro E _ _ _ P hP
  refine ⟨⟨vpIdeal (conjPrime₂ P), fun x => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩, ?_, ?_, fun Q h1 h2 => ?_, detLat_vp P⟩
  · have := star_mem_vp _ _ h
    rwa [conjP_conjP'] at this
  · simpa using star_mem_vp _ _ h
  · unfold vpIdeal
    rw [conjP_conjP', ← FractionalIdeal.coe_mul, mul_assoc, inv_mul_cancel_left₀ (ne0 _), mul_inv_cancel₀ (ne0 _),
      FractionalIdeal.coe_one]
  · have := (maxV_self P).mul (maxV_inv one_ne_zero (maxV_ne P _ hP))
    rw [inv_one, mul_one, ← FractionalIdeal.coe_mul] at this
    exact this
  · have := (maxV_ne _ P hP.symm).mul (maxV_inv WithZero.exp_ne_zero (maxV_self (conjPrime₂ P)))
    rw [one_mul, ← WithZero.exp_neg, neg_neg, ← FractionalIdeal.coe_mul] at this
    exact this
  · have := (maxV_ne Q P h1).mul (maxV_inv one_ne_zero (maxV_ne Q _ h2))
    rw [inv_one, mul_one, ← FractionalIdeal.coe_mul] at this
    exact this

end GlobalTheory.CharVal.Vp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiIndEqInter
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.XiIndZero

open GlobalTheory.ThetaInter

variable {V : Type} [AddCommGroup V]

theorem isReps_repsOf {L₁ L₂ : AddSubgroup V} (h : relIdx L₁ L₂ ≠ 0) : IsReps L₁ L₂ (repsOf L₁ L₂) := by
  classical
  have : Fintype (L₂ ⧸ L₁.addSubgroupOf L₂) := AddSubgroup.fintypeOfIndexNeZero h
  refine Classical.epsilon_spec (p := fun S => IsReps L₁ L₂ S)
    ⟨Finset.univ.image fun c : L₂ ⧸ L₁.addSubgroupOf L₂ => ((Quotient.out c : L₂) : V), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact (Quotient.out c : L₂).2
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hy
    have : d = c := by
      rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' d, QuotientAddGroup.eq,
        AddSubgroup.mem_addSubgroupOf]
      simpa [neg_add_eq_sub] using hxy
    rw [this]
  · intro y hy
    refine ⟨_, Finset.mem_image.2 ⟨((⟨y, hy⟩ : L₂) : L₂ ⧸ L₁.addSubgroupOf L₂), Finset.mem_univ _, rfl⟩, ?_⟩
    have := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' ((⟨y, hy⟩ : L₂) : L₂ ⧸ L₁.addSubgroupOf L₂))
    rw [AddSubgroup.mem_addSubgroupOf] at this
    simpa [neg_add_eq_sub] using this

theorem sum_reps {M : Type*} [AddCommMonoid M] {L₁ L₂ : AddSubgroup V} [Fintype (L₂ ⧸ L₁.addSubgroupOf L₂)]
    {S : Finset V} (hS : IsReps L₁ L₂ S) (f : V → M) (hf : ∀ a ∈ L₂, ∀ s ∈ L₂, s ∈ L₁ → f (a + s) = f a) :
    ∑ x ∈ S, f x = ∑ c : L₂ ⧸ L₁.addSubgroupOf L₂, f ((Quotient.out c : L₂) : V) := by
  refine Finset.sum_bij (fun x hx => ((⟨x, hS.1 x hx⟩ : L₂) : L₂ ⧸ L₁.addSubgroupOf L₂))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro x hx y hy hxy
    have := QuotientAddGroup.eq.1 hxy.symm
    rw [AddSubgroup.mem_addSubgroupOf] at this
    exact hS.2.1 x hx y hy (by simpa [neg_add_eq_sub] using this)
  · intro c _
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨x, hx, hxy⟩ := hS.2.2 y y.2
    refine ⟨x, hx, QuotientAddGroup.eq.2 ?_⟩
    rw [AddSubgroup.mem_addSubgroupOf]
    simpa [neg_add_eq_sub] using hxy
  · intro x hx
    set c := ((⟨x, hS.1 x hx⟩ : L₂) : L₂ ⧸ L₁.addSubgroupOf L₂) with hc
    have := QuotientAddGroup.eq.1 ((QuotientAddGroup.out_eq' c).trans hc)
    rw [AddSubgroup.mem_addSubgroupOf] at this
    have h2 := hf _ (Quotient.out c : L₂).2 _ (-(Quotient.out c : L₂) + ⟨x, hS.1 x hx⟩ : L₂).2 this
    simpa using h2

theorem card_reps {L₁ L₂ : AddSubgroup V} (h : relIdx L₁ L₂ ≠ 0) {S : Finset V} (hS : IsReps L₁ L₂ S) :
    S.card = relIdx L₁ L₂ := by
  have : Fintype (L₂ ⧸ L₁.addSubgroupOf L₂) := AddSubgroup.fintypeOfIndexNeZero h
  have h1 := sum_reps hS (fun _ => (1 : ℕ)) fun _ _ _ _ _ => rfl
  rw [relIdx, AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
  simpa using h1

theorem xiInd_eq_inter : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V) (vol : ℝ) (θ : V → ℂ) (s z : V), IsHerm H → IsSelfDual H B → IsSemiChar H B α → IsSelfDual H Λ → θ ∈ fixedBy H α Λ → 0 < vol → Λ ≤ (Λ ⊓ A) ⊔ (Λ ⊓ B) → relIdx B Λ ≠ 0 → relIdx Λ B ≠ 0 → ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiInd H α vol B (repsOf B (Λ ⊓ A)) (repsOf Λ B) θ s z = ((Real.sqrt (relIdx B Λ : ℕ) : ℝ) : ℂ)⁻¹ * (α s * opU H (-s) (inter H α Λ B θ) z) := by
  intro V _ _ H α A B Λ vol θ s z hH hdB hsB hdΛ hθ hvol hle h1 h2
  classical
  have i1 : Fintype (Λ ⧸ B.addSubgroupOf Λ) := AddSubgroup.fintypeOfIndexNeZero h1
  have i2 : Fintype (B ⧸ Λ.addSubgroupOf B) := AddSubgroup.fintypeOfIndexNeZero h2
  have hA : IsReps B (Λ ⊓ A) (repsOf B (Λ ⊓ A)) :=
    isReps_repsOf fun h => h1 (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  have hB : IsReps Λ B (repsOf Λ B) := isReps_repsOf h2
  set SA := repsOf B (Λ ⊓ A)
  set SB := repsOf Λ B
  have hA' : IsReps B Λ SA := by
    refine ⟨fun x hx => (hA.1 x hx).1, hA.2.1, fun y hy => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 (hle hy)
    obtain ⟨x, hx, hxa⟩ := hA.2.2 a ha
    exact ⟨x, hx, by rw [add_sub_right_comm]; exact B.add_mem hxa hb.2⟩
  have hcard : SA.card = relIdx B Λ := card_reps h1 hA'
  have hidx : relIdx Λ B = relIdx B Λ := by
    simp only [relIdx, AddSubgroup.relIndex, AddSubgroup.index, Nat.card_eq_fintype_card]
    exact card_eq_card hH hdB hdΛ
  obtain ⟨t₀, ht₀, ht₀B⟩ := hA'.2.2 0 Λ.zero_mem
  have ht₀B' : t₀ ∈ B := by simpa using ht₀B
  have hhat : ∀ y ∈ B, hatS H vol SA (indL B) y =
      ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℂ) / (relIdx B Λ : ℂ)) := by
    intro y hy
    rw [hatS, hcard, Finset.sum_eq_single_of_mem t₀ ht₀]
    · have : brk H y t₀ = 1 := by
        rw [← (chi_eq_one_iff t₀ y).2 (hdB.ge ht₀B' y hy), brk, chi]
        congr 1; ring
      simp [this, indL, ht₀B']
    · intro t ht hne
      have : t ∉ B := fun h => hne (hA'.2.1 t ht t₀ ht₀ (B.sub_mem h ht₀B'))
      simp [indL, this]
  have hn : (0 : ℝ) < (relIdx B Λ : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero h1
  set r : ℂ := ((Real.sqrt (relIdx B Λ : ℕ) : ℝ) : ℂ) with hr
  have hr0 : r ≠ 0 := by rw [hr]; exact_mod_cast (Real.sqrt_pos.2 hn).ne'
  have hr2 : (relIdx B Λ : ℂ) = r ^ 2 := by rw [hr]; exact_mod_cast (Real.sq_sqrt hn.le).symm
  set v : ℂ := ((Real.sqrt vol : ℝ) : ℂ) with hv
  have hv0 : v ≠ 0 := by rw [hv]; exact_mod_cast (Real.sqrt_pos.2 hvol).ne'
  have hv2 : (vol : ℂ) = v ^ 2 := by rw [hv]; exact_mod_cast (Real.sq_sqrt hvol.le).symm
  have hxi : xiS H α vol SA SB (indL B) θ = fun w => (v * r⁻¹) * inter H α Λ B θ w := by
    funext w
    rw [inter, finsum_eq_sum_of_fintype, hidx, ← hr,
      ← sum_reps hB (fun y => α y * opU H y θ w) ?_, xiS, sumU, ← mul_assoc, Finset.mul_sum]
    · refine Finset.sum_congr rfl fun y hy => ?_
      rw [hhat y (hB.1 y hy), hr2, hv2]
      field_simp
    · intro a ha b hb hbΛ
      have e : (fun w => α b * opU H b θ w) = θ := funext (hθ b hbΛ)
      show α (a + b) * opU H (a + b) θ w = α a * opU H a θ w
      rw [alpha_opU_add hH hdB hsB ha hb, ← opU_mul, e]
  rw [xiInd, hxi]
  simp only [opU_mul]
  field_simp

end GlobalTheory.XiIndZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalBasisSnocOfLocalBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalBasisSnocOfLocalBasis
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.LocBasisSnoc

variable {E : Type} [Field E] {n : ℕ}

def blk (A : Matrix (Fin n) (Fin n) E) (c : E) : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases c (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i

theorem blk_mulVec_castSucc (A : Matrix (Fin n) (Fin n) E) (c : E) (x : Fin (n + 1) → E) (i : Fin n) :
    (blk A c *ᵥ x) i.castSucc = (A *ᵥ Fin.init x) i := by
  simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.init]

theorem blk_mulVec_last (A : Matrix (Fin n) (Fin n) E) (c : E) (x : Fin (n + 1) → E) :
    (blk A c *ᵥ x) (Fin.last n) = c * x (Fin.last n) := by
  simp [blk, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

theorem blk_mulVec_ext {P Q : Matrix (Fin (n + 1)) (Fin (n + 1)) E} (h : ∀ x, P *ᵥ x = Q *ᵥ x) : P = Q :=
  Matrix.ext_of_mulVec_single fun j => h _

theorem blk_mul (A A' : Matrix (Fin n) (Fin n) E) (c c' : E) :
    blk A c * blk A' c' = blk (A * A') (c * c') := by
  refine blk_mulVec_ext fun x => ?_
  rw [← Matrix.mulVec_mulVec]
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [blk_mulVec_last, blk_mulVec_last, blk_mulVec_last, mul_assoc]
  · rw [blk_mulVec_castSucc, blk_mulVec_castSucc, ← Matrix.mulVec_mulVec]
    congr 2
    funext k
    exact blk_mulVec_castSucc _ _ _ _

theorem blk_one : blk (1 : Matrix (Fin n) (Fin n) E) 1 = 1 := by
  refine blk_mulVec_ext fun x => ?_
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [blk_mulVec_last, one_mul, Matrix.one_mulVec]
  · rw [blk_mulVec_castSucc, Matrix.one_mulVec, Matrix.one_mulVec]
    rfl

end GlobalTheory.LocBasisSnoc


open GlobalTheory.LocBasisSnoc in
theorem GlobalTheory.isLocBasis_snoc : ∀ {E : Type} [Field E] [NumberField E] {N n : ℕ} (hN : N = n + 1) (t : E), t ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ L ↔ iniH hN x ∈ L' ∧ t * x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E)) → ∀ (p : ℕ) (B' : GL (Fin n) E), p.Prime → IsLocBasis p (L' : Set (Fin n → E)) B' → ∃ B : GL (Fin N) E, (∀ x, iniH hN ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) = (B' : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x) ∧ (∀ x, t * ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) ∧ IsLocBasis p (L : Set (Fin N → E)) B := by
  intro E _ _ N n hN t ht L L' hL p B' hp hB'
  subst hN
  let B : GL (Fin (n + 1)) E :=
    ⟨blk (B' : Matrix (Fin n) (Fin n) E) t⁻¹, blk ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t,
      by rw [blk_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, inv_mul_cancel₀ ht, blk_one],
      by rw [blk_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_inv_cancel₀ ht, blk_one]⟩
  have hini : ∀ y : Fin (n + 1) → E, iniH rfl y = Fin.init y := fun y => rfl
  have hlast : (Br.iL (rfl : n + 1 = n + 1)) = Fin.last n := rfl
  refine ⟨B, fun x => ?_, fun x => ?_, ?_⟩
  · rw [hini, hini]
    funext i
    exact blk_mulVec_castSucc _ _ _ _
  · rw [hlast]
    show t * (blk _ t⁻¹ *ᵥ x) (Fin.last n) = _
    rw [blk_mulVec_last, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]
  · intro x
    have hinv : ((B⁻¹ : GL (Fin (n + 1)) E) : Matrix _ _ E) = blk ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t := rfl
    rw [hinv]
    set R := (algebraMap (𝓞 E) E).range
    have hR : ∀ (s : ℕ) {y : E}, y ∈ R → (s : E) * y ∈ R := fun s y hy => R.mul_mem (natCast_mem R s) hy
    have key : ∀ s : ℕ, (∀ a, (s : E) * (blk ((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) t *ᵥ x) a ∈ R) ↔
        (∀ a, (s : E) * (((B'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ Fin.init x) a ∈ R) ∧
          (s : E) * (t * x (Fin.last n)) ∈ R := by
      intro s
      constructor
      · intro h
        refine ⟨fun a => ?_, ?_⟩
        · have := h a.castSucc
          rwa [blk_mulVec_castSucc] at this
        · have := h (Fin.last n)
          rwa [blk_mulVec_last] at this
      · rintro ⟨h1, h2⟩ a
        refine Fin.lastCases ?_ (fun i => ?_) a
        · rw [blk_mulVec_last]; exact h2
        · rw [blk_mulVec_castSucc]; exact h1 i
    have memL : ∀ s : ℕ, (s : E) • x ∈ L ↔ (s : E) • Fin.init x ∈ L' ∧ (s : E) * (t * x (Fin.last n)) ∈ R := by
      intro s
      rw [hL, hini, hlast, Submodule.mem_one]
      have e : t * ((s : E) • x) (Fin.last n) = (s : E) * (t * x (Fin.last n)) := by
        rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
      rw [e]
      rfl
    have hnd : ∀ a b : ℕ, ¬ p ∣ a → ¬ p ∣ b → ¬ p ∣ a * b := fun a b ha hb h =>
      (hp.dvd_mul.mp h).elim ha hb
    have hB := hB' (Fin.init x)
    constructor
    · rintro ⟨s, hs, hx⟩
      obtain ⟨h1, h2⟩ := (memL s).mp hx
      obtain ⟨s', hs', h3⟩ := hB.mp ⟨s, hs, h1⟩
      refine ⟨s * s', hnd _ _ hs hs', (key _).mpr ⟨fun a => ?_, ?_⟩⟩
      · rw [Nat.cast_mul, mul_assoc]; exact hR s (h3 a)
      · rw [Nat.cast_mul, mul_comm (s : E), mul_assoc]; exact hR s' h2
    · rintro ⟨s, hs, h⟩
      obtain ⟨h1, h2⟩ := (key s).mp h
      obtain ⟨s', hs', h3⟩ := hB.mpr ⟨s, hs, h1⟩
      refine ⟨s * s', hnd _ _ hs hs', (memL _).mpr ⟨?_, ?_⟩⟩
      · rw [Nat.cast_mul, mul_smul, Nat.cast_smul_eq_nsmul]
        exact nsmul_mem h3 s
      · rw [Nat.cast_mul, mul_comm (s : E), mul_assoc]; exact hR s' h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLocalBasisSnocOfLocalBasisStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localBasis_snoc_of_localBasis : ∀ {E : Type} [Field E] [NumberField E] {N n : ℕ} (hN : N = n + 1) (t : E), t ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin n → E)), (∀ x, x ∈ L ↔ iniH hN x ∈ L' ∧ t * x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E)) → ∀ (p : ℕ) (B' : GL (Fin n) E), p.Prime → IsLocBasis p (L' : Set (Fin n → E)) B' → ∃ B : GL (Fin N) E, (∀ x, iniH hN ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) = (B' : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x) ∧ (∀ x, t * ((B : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) ∧ IsLocBasis p (L : Set (Fin N → E)) B := by
  first | exact @GlobalTheory.isLocBasis_snoc | exact GlobalTheory.isLocBasis_snoc | (intros; apply GlobalTheory.isLocBasis_snoc <;> assumption)
end
end
