module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInvOfDirectedUnion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceAbsolutelyIntegrallyCloseStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceTensorPowerIntegralClosur
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvQuotIInfKerRetractions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvQuotIInfKerRetractions
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem homotopyInv_quot_iInf_ker_retractions : ∀ (q : ℕ) [NeZero q] (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], IsUnit (q : D) → HInv q T → (∀ (E' : Type) [CommRing E'] [Algebra D E'] [Algebra.IsIntegral D E'] (s : D), s ≠ 0 → algebraMap D E' s = 0 → HInv q E') → ∀ (ι : T →ₐ[D] E) (X : Finset (E →ₐ[D] T)), (∀ χ ∈ X, χ.comp ι = AlgHom.id D T) → HInv q (E ⧸ ⨅ χ ∈ X, RingHom.ker χ) := by
  intro q _ D T E _ _ _ _ _ _ _ _ _ hq hT hlow ι X
  classical
  induction X using Finset.induction_on with
  | empty =>
    intro _
    apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton
    rw [Ideal.Quotient.subsingleton_iff]
    simp
  | @insert χ Y hχY ih =>
    intro hX
    have hχ : χ.comp ι = AlgHom.id D T := hX χ (Finset.mem_insert_self _ _)
    have ih' := ih (fun ψ hψ => hX ψ (Finset.mem_insert_of_mem hψ))
    have hχι : ∀ t, χ (ι t) = t := fun t => by
      simpa using DFunLike.congr_fun hχ t
    have hins : (⨅ ψ ∈ insert χ Y, RingHom.ker ψ) = RingHom.ker χ ⊓ ⨅ ψ ∈ Y, RingHom.ker ψ := by
      rw [Finset.iInf_insert]
    rw [hins]
    set P : Ideal E := RingHom.ker χ with hPdef
    set I : Ideal E := ⨅ ψ ∈ Y, RingHom.ker ψ with hIdef
    by_cases hIP : I ≤ P
    · rw [inf_eq_right.mpr hIP]; exact ih'
    · obtain ⟨y, hyI, hyP⟩ := Set.not_subset.mp hIP
      have hy0 : χ y ≠ 0 := fun h => hyP (RingHom.mem_ker.mpr h)
      have hint : IsIntegral D (χ y) := Algebra.IsIntegral.isIntegral _
      have hne := Ideal.comap_ne_bot_of_integral_mem hy0 (Ideal.mem_span_singleton_self (χ y)) hint
      obtain ⟨s, hsmem, hs0⟩ := Submodule.ne_bot_iff _ |>.mp hne
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hsmem
      obtain ⟨u, hu⟩ := hsmem
      have hsPI : algebraMap D E s ∈ P ⊔ I := by
        have h1 : algebraMap D E s - ι u * y ∈ P := by
          rw [hPdef, RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes, hχι, hu, sub_self]
        have h2 : ι u * y ∈ I := Ideal.mul_mem_left _ _ hyI
        have : algebraMap D E s = (algebraMap D E s - ι u * y) + ι u * y := by ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
      set J : Ideal E := P ⊓ I with hJ
      have hJP : J ≤ P := inf_le_left
      have hJI : J ≤ I := inf_le_right
      apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (E ⧸ J) (P.map (Ideal.Quotient.mk J)) (I.map (Ideal.Quotient.mk J))
      · intro x hx
        obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective x
        have h1 := (Ideal.mem_quotient_iff_mem hJP).mp hx.1
        have h2 := (Ideal.mem_quotient_iff_mem hJI).mp hx.2
        have : Ideal.Quotient.mk J e = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ⟨h1, h2⟩
        rw [this]; exact zero_mem _
      · have := hq.map (algebraMap D (E ⧸ J))
        simpa using this
      · have hsurj : Function.Surjective χ := fun t => ⟨ι t, hχι t⟩
        have e1 := DoubleQuot.quotQuotEquivQuotOfLE hJP
        have e2 := (Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv
        exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q T _ (e1.trans e2).symm hT
      · exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ (DoubleQuot.quotQuotEquivQuotOfLE hJI).symm ih'
      · apply hlow _ s hs0
        change Ideal.Quotient.mk _ (Ideal.Quotient.mk J (algebraMap D E s)) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.map_sup]
        exact Ideal.mem_map_of_mem _ hsPI

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvQuotIInfKerRetractionsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hInv_quot_iInf_ker_retractions : ∀ (q : ℕ) [NeZero q] (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], IsUnit (q : D) → HInv q T → (∀ (E' : Type) [CommRing E'] [Algebra D E'] [Algebra.IsIntegral D E'] (s : D), s ≠ 0 → algebraMap D E' s = 0 → HInv q E') → ∀ (ι : T →ₐ[D] E) (X : Finset (E →ₐ[D] T)), (∀ χ ∈ X, χ.comp ι = AlgHom.id D T) → HInv q (E ⧸ ⨅ χ ∈ X, RingHom.ker χ) := by
  first | (exact @GlobalTheory.homotopyInv_quot_iInf_ker_retractions) | (exact GlobalTheory.homotopyInv_quot_iInf_ker_retractions) | (intros; apply GlobalTheory.homotopyInv_quot_iInf_ker_retractions  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantIntegralKilledOfLowerDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantIntegralKilledOfLowerDim
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

private theorem ringKrullDim_le_quotient_of_algebraMap_eq_zero (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (s : R) (hs : algebraMap R S s = 0) :
    ringKrullDim S ≤ ringKrullDim (R ⧸ Ideal.span {s}) := by
  rw [ringKrullDim_quotient]
  have hmem : ∀ P : PrimeSpectrum S, (⟨P.asIdeal.comap (algebraMap R S), inferInstance⟩ : PrimeSpectrum R) ∈
      PrimeSpectrum.zeroLocus (R := R) (Ideal.span {s}) := fun P => by
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hs, Ideal.zero_mem]
  exact Order.krullDim_le_of_strictMono (fun P => ⟨_, hmem P⟩)
    (fun P Q h => Subtype.mk_lt_mk.mpr (Ideal.IsIntegral.comap_lt_comap (R := R) h))

private theorem hInv_adjoin_of_dim_quotient_lt (q : ℕ) [NeZero q] (d : ℕ)
    (hlow : ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R)
    (D : Type) [CommRing D] [Algebra.FiniteType ℤ D] (hqD : IsUnit (q : D)) (E : Type) [CommRing E]
    [Algebra D E] [Algebra.IsIntegral D E] (s : D) (hsE : algebraMap D E s = 0)
    (hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d) (F : Finset E) :
    HInv q ((Algebra.adjoin D (F : Set E)).restrictScalars ℤ) := by
  set T := Algebra.adjoin D (F : Set E)
  have : Algebra.IsIntegral D T := ⟨fun x =>
    (isIntegral_algHom_iff T.val Subtype.val_injective).mp (Algebra.IsIntegral.isIntegral (x : E))⟩
  have : Algebra.FiniteType D T := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset F)
  have : Algebra.FiniteType ℤ T := Algebra.FiniteType.trans (R := ℤ) (S := D) inferInstance inferInstance
  have hsT : algebraMap D T s = 0 := Subtype.ext (by simpa using hsE)
  have h1 : ringKrullDim T < d := (ringKrullDim_le_quotient_of_algebraMap_eq_zero D T s hsT).trans_lt hlt
  have h2 : IsUnit (q : T) := by simpa using hqD.map (algebraMap D T)
  exact hlow T h2 h1


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.hInv_of_integral_killed_of_lower : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ (E : Type) [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (s : D), s ≠ 0 → algebraMap D E s = 0 → HInv q E := by
  intro q _ d hlow D _ _ _ hqD hdD E _ _ _ s hs0 hsE
  have hquot := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hs0)
  have hlt : ringKrullDim (D ⧸ Ideal.span {s}) < d := by
    have h := hquot.trans hdD
    generalize ringKrullDim (D ⧸ Ideal.span {s}) = a at h ⊢
    cases a using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe a =>
      have h' : a + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
      have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_self_add h')
      exact_mod_cast (ENat.add_one_le_iff ha).mp h'
  exact GlobalTheory.T.hInv_of_directed_union_subalgebras q E (Finset E) (fun F => (Algebra.adjoin D (F : Set E)).restrictScalars ℤ)
    (fun F G h x hx => Algebra.adjoin_mono (Finset.coe_subset.mpr h) hx)
    (fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩)
    (fun F => by
      have h := hqD.map (algebraMap D (Algebra.adjoin D (F : Set E)))
      rw [map_natCast] at h
      exact h)
    (fun F => hInv_adjoin_of_dim_quotient_lt q d hlow D hqD E s hsE hlt F)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantIntegralKilledOfLowerDimStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariant_integral_killed_of_lowerDim : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ (E : Type) [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (s : D), s ≠ 0 → algebraMap D E s = 0 → HInv q E := by
  first | (exact @GlobalTheory.hInv_of_integral_killed_of_lower) | (exact GlobalTheory.hInv_of_integral_killed_of_lower) | (intros; apply GlobalTheory.hInv_of_integral_killed_of_lower  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIsNilpotentMulFiniteInfFgIdeals
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIsNilpotentMulFiniteInfFgIdeals
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.FinInterNil

theorem exists_ne_zero_isNilpotent_mul {D E : Type} [CommRing D] [IsDomain D] [CommRing E]
    [Algebra D E] (y : E)
    (hy : ∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → y ∈ Q) :
    ∃ t : D, t ≠ 0 ∧ IsNilpotent (algebraMap D E t * y) := by
  by_contra hcon
  push_neg at hcon
  let M : Submonoid E :=
    { carrier := {z | ∃ t : D, t ≠ 0 ∧ ∃ n : ℕ, z = algebraMap D E t * y ^ n}
      mul_mem' := by
        rintro a b ⟨t, ht, n, rfl⟩ ⟨t', ht', m, rfl⟩
        exact ⟨t * t', mul_ne_zero ht ht', n + m, by rw [map_mul, pow_add]; ring⟩
      one_mem' := ⟨1, one_ne_zero, 0, by simp⟩ }
  have h0 : (0 : E) ∉ M := by
    rintro ⟨t, ht, n, hz⟩
    apply hcon t ht
    refine ⟨n + 1, ?_⟩
    calc (algebraMap D E t * y) ^ (n + 1)
        = algebraMap D E t ^ n * y * (algebraMap D E t * y ^ n) := by ring
      _ = 0 := by rw [← hz, mul_zero]
  have hdisj : Disjoint ((⊥ : Ideal E) : Set E) (M : Set E) := by
    rw [Set.disjoint_left]
    intro z hz hzM
    have hz0 : z = 0 := by simpa using hz
    exact h0 (hz0 ▸ hzM)
  obtain ⟨Q, hQ, -, hQM⟩ := Ideal.exists_le_prime_disjoint ⊥ M hdisj
  have hcomap : Q.comap (algebraMap D E) = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Ideal.mem_bot]
    by_contra htne
    have hm : algebraMap D E t ∈ M := ⟨t, htne, 0, by simp⟩
    exact Set.disjoint_left.mp hQM (Ideal.mem_comap.mp ht) hm
  have hyQ := hy Q hQ hcomap
  have hm : y ∈ M := ⟨1, one_ne_zero, 1, by simp⟩
  exact Set.disjoint_left.mp hQM hyQ hm

theorem main : ∀ (D E : Type) [CommRing D] [IsDomain D] [CommRing E] [Algebra D E] (ι : Type)
    (X : Finset ι) (P : ι → Ideal E), (∀ i ∈ X, (P i).FG) →
    (∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → (⨅ i ∈ X, P i) ≤ Q) →
    ∃ s : D, s ≠ 0 ∧ ∀ y ∈ (⨅ i ∈ X, P i), IsNilpotent (algebraMap D E s * y) := by
  intro D E _ _ _ _ ι X P hFG hQ
  classical
  have hstep : ∀ y ∈ (⨅ i ∈ X, P i), ∃ t : D, t ≠ 0 ∧ IsNilpotent (algebraMap D E t * y) :=
    fun y hy => exists_ne_zero_isNilpotent_mul y (fun Q hQp hQc => hQ Q hQp hQc hy)
  have hJfg : (∏ i ∈ X, P i).FG := by
    refine Finset.prod_induction P (fun J : Ideal E => J.FG) (fun a b ha hb => ha.mul hb) ?_ hFG
    exact ⟨{1}, by simp⟩
  have hJI : ∀ g ∈ ∏ i ∈ X, P i, g ∈ (⨅ i ∈ X, P i) := by
    intro g hg
    simp only [Submodule.mem_iInf]
    intro i hi
    exact (Ideal.prod_le_inf.trans (Finset.inf_le hi)) hg
  obtain ⟨S, hS⟩ := hJfg
  have hSI : ∀ g : S, (g : E) ∈ (⨅ i ∈ X, P i) := fun g =>
    hJI g (hS ▸ Submodule.subset_span g.2)
  choose t ht using fun g : S => hstep g.1 (hSI g)
  refine ⟨∏ g : S, t g, Finset.prod_ne_zero_iff.mpr (fun g _ => (ht g).1), ?_⟩
  set s := ∏ g : S, t g with hs
  let K : Ideal E := Submodule.comap (LinearMap.mulLeft E (algebraMap D E s)) (nilradical E)
  have hK : ∀ z, z ∈ K ↔ IsNilpotent (algebraMap D E s * z) := by
    intro z
    simp [K, mem_nilradical]
  have hJK : (∏ i ∈ X, P i) ≤ K := by
    rw [← hS, Submodule.span_le]
    intro g hg
    rw [SetLike.mem_coe, hK]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ (⟨g, hg⟩ : S))
    have he : algebraMap D E s * g = algebraMap D E c * (algebraMap D E (t ⟨g, hg⟩) * g) := by
      rw [hs, hc, map_mul]; ring
    rw [he]
    exact (Commute.all _ _).isNilpotent_mul_left (ht ⟨g, hg⟩).2
  intro y hy
  have hyN : y ^ X.card ∈ ∏ i ∈ X, P i := by
    have := Ideal.prod_mem_prod (s := X) (I := P) (x := fun _ => y) (fun i hi => by
      have := hy
      simp only [Submodule.mem_iInf] at this
      exact this i hi)
    simpa [Finset.prod_const] using this
  have hn := (hK _).mp (hJK hyN)
  have hpow : IsNilpotent ((algebraMap D E s * y) ^ (X.card + 1)) := by
    have he : (algebraMap D E s * y) ^ (X.card + 1)
        = (algebraMap D E s ^ X.card * y) * (algebraMap D E s * y ^ X.card) := by ring
    rw [he]
    exact (Commute.all _ _).isNilpotent_mul_left hn
  obtain ⟨k, hk⟩ := hpow
  exact ⟨(X.card + 1) * k, by rw [pow_mul, hk]⟩

end GlobalTheory.FinInterNil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroIsNilpotentMulFiniteInfFgIdealsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_isNilpotent_mul_finite_inf_fg_ideals : ∀ (D E : Type) [CommRing D] [IsDomain D] [CommRing E] [Algebra D E] (ι : Type) (X : Finset ι) (P : ι → Ideal E), (∀ i ∈ X, (P i).FG) → (∀ Q : Ideal E, Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → (⨅ i ∈ X, P i) ≤ Q) → ∃ s : D, s ≠ 0 ∧ ∀ y ∈ (⨅ i ∈ X, P i), IsNilpotent (algebraMap D E s * y) := by
  first | (exact @GlobalTheory.FinInterNil.main) | (exact GlobalTheory.FinInterNil.main) | (intros; apply GlobalTheory.FinInterNil.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRetractionsOfAdjoinFinsetIntegralDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRetractionsOfAdjoinFinsetIntegralDomain
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem finite_retractions_of_adjoin_finset_integral
    (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T]
    [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E)
    (hF : Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤) :
    {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite := by
  classical
  choose p hpm hp0 using fun x : E => (Algebra.IsIntegral.isIntegral (R := D) x)
  have hfin : (Set.pi Set.univ fun f : F =>
      ((((p f.1).map (algebraMap D T)).roots.toFinset : Finset T) : Set T)).Finite :=
    Set.Finite.pi (fun f => Finset.finite_toSet _)
  refine Set.Finite.of_finite_image (f := fun χ : E →ₐ[D] T => fun f : F => χ f.1)
    (hfin.subset ?_) ?_
  · rintro _ ⟨χ, _, rfl⟩
    refine Set.mem_univ_pi.2 fun f => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots ((hpm f.1).map (algebraMap D T)).ne_zero, Polynomial.IsRoot,
      Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply,
      Polynomial.aeval_def, hp0, map_zero]
  · intro χ₁ h₁ χ₂ h₂ he
    apply AlgHom.ext_of_adjoin_eq_top hF
    rintro x (⟨t, rfl⟩ | hx)
    · have e₁ := AlgHom.congr_fun (show χ₁.comp ι = AlgHom.id D T from h₁) t
      have e₂ := AlgHom.congr_fun (show χ₂.comp ι = AlgHom.id D T from h₂) t
      simp only [AlgHom.comp_apply, AlgHom.id_apply] at e₁ e₂
      rw [e₁, e₂]
    · exact congrFun he ⟨x, hx⟩

theorem finite_retractions_of_adjoin_finset_integral' :
    ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T]
      [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E),
      Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ →
        {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite :=
  fun D T E _ _ _ _ _ _ _ _ ι F hF => finite_retractions_of_adjoin_finset_integral D T E ι F hF

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRetractionsOfAdjoinFinsetIntegralDomainStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_retractions_of_adjoin_finset_integral_domain : ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite := by
  first | (exact @GlobalTheory.finite_retractions_of_adjoin_finset_integral') | (exact GlobalTheory.finite_retractions_of_adjoin_finset_integral') | (intros; apply GlobalTheory.finite_retractions_of_adjoin_finset_integral'  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRetractionFg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRetractionFg
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem ker_retraction_fg : ∀ (D T E : Type) [CommRing D] [CommRing T] [Algebra D T] [CommRing E] [Algebra D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → ∀ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T → (RingHom.ker χ).FG := by
  intro D T E _ _ _ _ _ ι F hF χ hχ
  have hχι : ∀ t, χ (ι t) = t := fun t => by simpa using DFunLike.congr_fun hχ t
  set J : Ideal E := Ideal.span ((fun f => f - ι (χ f)) '' (F : Set E)) with hJ
  have key : ∀ x, x - ι (χ x) ∈ J := by
    intro x
    have hx : x ∈ Algebra.adjoin D (Set.range ι ∪ (F : Set E)) := by rw [hF]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨t, rfl⟩ | hx
      · simp [hχι]
      · exact Ideal.subset_span ⟨x, hx, rfl⟩
    | algebraMap r => simp [AlgHom.commutes]
    | add x y _ _ hx hy =>
      have e : x + y - ι (χ (x + y)) = (x - ι (χ x)) + (y - ι (χ y)) := by
        simp only [map_add (f := _)]; ring
      rw [e]; exact J.add_mem hx hy
    | mul x y _ _ hx hy =>
      have e : x * y - ι (χ (x * y)) = (x - ι (χ x)) * y + ι (χ x) * (y - ι (χ y)) := by
        simp only [map_mul]; ring
      rw [e]; exact J.add_mem (J.mul_mem_right _ hx) (J.mul_mem_left _ hy)
  have hker : RingHom.ker χ = J := by
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      simpa [hx] using key x
    · rw [hJ, Ideal.span_le]
      rintro _ ⟨f, _, rfl⟩
      simp [RingHom.mem_ker, hχι]
  rw [hker]
  classical
  exact ⟨F.image (fun f => f - ι (χ f)), by rw [Finset.coe_image]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRetractionFgStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_retraction_fg_of_adjoin_finset : ∀ (D T E : Type) [CommRing D] [CommRing T] [Algebra D T] [CommRing E] [Algebra D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → ∀ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T → (RingHom.ker χ).FG := by
  first | (exact @GlobalTheory.ker_retraction_fg) | (exact GlobalTheory.ker_retraction_fg) | (intros; apply GlobalTheory.ker_retraction_fg  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionOfMonicPolynomialsHaveRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionOfMonicPolynomialsHaveRoots
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

open Polynomial

theorem mem_range_of_AIC_of_eval₂_eq_zero {T L : Type} [CommRing T] [CommRing L] [IsDomain L]
    (hA : AIC T) (f : T →+* L) (x : L) :
    ∀ (n : ℕ) (p : T[X]), p.natDegree = n → p.Monic → p.eval₂ f x = 0 → x ∈ Set.range f := by
  intro n
  haveI : Nontrivial T := f.domain_nontrivial
  induction n with
  | zero =>
    intro p hd hm hx
    have hp : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    subst hp
    simp at hx
  | succ n ih =>
    intro p hd hm hx
    obtain ⟨a, ha⟩ := hA p hm (by omega)
    have hroot : IsRoot p a := ha
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
    set q := p /ₘ (X - C a) with hq
    have hXm : (X - C a : T[X]).Monic := Polynomial.monic_X_sub_C a
    have hqm : q.Monic := by
      exact Polynomial.Monic.of_mul_monic_left hXm (by rw [hfac]; exact hm)
    have hqd : q.natDegree = n := by
      have h1 : ((X - C a) * q).natDegree = (X - C a).natDegree + q.natDegree :=
        hXm.natDegree_mul hqm
      rw [hfac, hd, Polynomial.natDegree_X_sub_C] at h1
      omega
    rw [← hfac, Polynomial.eval₂_mul] at hx
    rcases mul_eq_zero.mp hx with h | h
    · refine ⟨a, ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at h
      exact (sub_eq_zero.mp h).symm
    · exact ih q hqd hqm h

theorem exists_retraction_of_AIC : ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T]
    [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E],
    AIC T → ∀ (ι : T →ₐ[D] E) (Q : Ideal E), Q.IsPrime → Q.comap (algebraMap D E) = ⊥ →
    ∃ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T ∧ RingHom.ker χ = Q := by
  intro D T E _ _ _ _ _ _ _ _ _ hA ι Q hQ hQD
  let π : E →ₐ[D] E ⧸ Q := Ideal.Quotient.mkₐ D Q
  let f : T →ₐ[D] E ⧸ Q := π.comp ι

  have hker : RingHom.ker (f : T →+* E ⧸ Q) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := D)
    rw [← hQD]
    ext d
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    change f (algebraMap D T d) = 0 ↔ _
    rw [f.commutes]
    change algebraMap D (E ⧸ Q) d = 0 ↔ _
    rw [IsScalarTower.algebraMap_apply D E (E ⧸ Q), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  have hinj : Function.Injective f := by
    have := (RingHom.injective_iff_ker_eq_bot (f : T →+* E ⧸ Q)).mpr hker
    exact this

  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpm, hpe⟩ := (Algebra.IsIntegral.isIntegral (R := D) e)
    have hmem := mem_range_of_AIC_of_eval₂_eq_zero hA (f : T →+* E ⧸ Q) (Ideal.Quotient.mk Q e)
      _ (p.map (algebraMap D T)) rfl (hpm.map _) (by
        rw [Polynomial.eval₂_map]
        have hc : (f : T →+* E ⧸ Q).comp (algebraMap D T) = (Ideal.Quotient.mk Q).comp (algebraMap D E) := by
          ext d
          simp only [RingHom.comp_apply, RingHom.coe_coe]
          rw [f.commutes]
          rfl
        rw [hc, ← Polynomial.hom_eval₂, hpe, map_zero])
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, ht⟩
  let eqv : T ≃ₐ[D] E ⧸ Q := AlgEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨(eqv.symm : E ⧸ Q →ₐ[D] T).comp π, ?_, ?_⟩
  · ext t
    simp only [AlgHom.comp_apply, AlgHom.id_apply, AlgHom.coe_coe]
    apply eqv.injective
    change eqv (eqv.symm (π (ι t))) = eqv t
    rw [AlgEquiv.apply_symm_apply]
    rfl
  · ext e
    rw [RingHom.mem_ker]
    change eqv.symm (π e) = 0 ↔ e ∈ Q
    rw [AlgEquiv.symm_apply_eq, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionOfMonicPolynomialsHaveRootsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_retraction_of_monicPolynomialsHaveRoots : ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], AIC T → ∀ (ι : T →ₐ[D] E) (Q : Ideal E), Q.IsPrime → Q.comap (algebraMap D E) = ⊥ → ∃ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T ∧ RingHom.ker χ = Q := by
  first | (exact @GlobalTheory.exists_retraction_of_AIC) | (exact GlobalTheory.exists_retraction_of_AIC) | (intros; apply GlobalTheory.exists_retraction_of_AIC  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetFgOverFirst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetFgOverFirst
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_fg_over_first : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A), ∃ F' : Finset (firstAndFinite R A k F), Algebra.adjoin R (Set.range (firstIncl R A k F) ∪ (F' : Set (firstAndFinite R A k F))) = ⊤ := by
  intro R A _ _ _ k F
  classical
  set S := firstAndFinite R A k F with hS
  let g : Fin (k + 1) × F → S := fun p =>
    ⟨PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) p.1 p.2.1,
      Algebra.subset_adjoin (Or.inr (Set.mem_iUnion.2 ⟨p.1, p.2.1, p.2.2, rfl⟩))⟩
  refine ⟨Finset.univ.image g, ?_⟩
  apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  conv_rhs => rw [hS, firstAndFinite]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext x
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨_, ⟨a, rfl⟩, rfl⟩
  · ext x
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_image, Set.mem_range,
      Set.mem_iUnion, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨⟨i, a, ha⟩, rfl⟩, rfl⟩
      exact ⟨i, a, ha, rfl⟩
    · rintro ⟨i, a, ha, rfl⟩
      exact ⟨g (i, ⟨a, ha⟩), ⟨(i, ⟨a, ha⟩), rfl⟩, rfl⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetFgOverFirstStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_fg_over_first : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A), ∃ F' : Finset (firstAndFinite R A k F), Algebra.adjoin R (Set.range (firstIncl R A k F) ∪ (F' : Set (firstAndFinite R A k F))) = ⊤ := by
  first | (exact @GlobalTheory.EtC.firstAndFinite_fg_over_first) | (exact GlobalTheory.EtC.firstAndFinite_fg_over_first) | (intros; apply GlobalTheory.EtC.firstAndFinite_fg_over_first  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetMemTensorPowerFirstFactorAdjoinFinse
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetMemTensorPowerFirstFactorAdjoinFinse
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_mono (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    {F G : Finset A} (h : F ⊆ G) : firstAndFinite R A k F ≤ firstAndFinite R A k G := by
  unfold firstAndFinite
  apply Algebra.adjoin_mono
  apply Set.union_subset_union_right
  apply Set.iUnion_mono
  intro i
  exact Set.image_mono (by exact_mod_cast h)

theorem tprod_eq_prod_singleAlgHom (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    (f : Fin (k + 1) → A) :
    PiTensorProduct.tprod R f = ∏ i, PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) i (f i) := by
  classical
  simp only [PiTensorProduct.singleAlgHom_apply]
  have := map_prod (PiTensorProduct.tprodMonoidHom R (A := fun _ : Fin (k + 1) => A))
    (fun u => MonoidHom.mulSingle (fun _ : Fin (k + 1) => A) u (f u)) Finset.univ
  refine Eq.trans ?_ this
  simp only [MonoidHom.mulSingle_apply]
  rw [Finset.univ_prod_mulSingle]
  rfl

theorem exists_finset_mem_firstAndFinite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    (x : PiTensorProduct R (fun _ : Fin (k + 1) => A)) : ∃ F : Finset A, x ∈ firstAndFinite R A k F := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine ⟨Finset.univ.image f, ?_⟩
    refine Subalgebra.smul_mem _ ?_ r
    rw [tprod_eq_prod_singleAlgHom]
    refine Subalgebra.prod_mem _ fun i _ => ?_
    apply Algebra.subset_adjoin
    refine Or.inr (Set.mem_iUnion.2 ⟨i, f i, by simp, rfl⟩)
  | add x y hx hy =>
    obtain ⟨F, hF⟩ := hx
    obtain ⟨G, hG⟩ := hy
    exact ⟨F ∪ G, Subalgebra.add_mem _ (firstAndFinite_mono R A k Finset.subset_union_left hF)
      (firstAndFinite_mono R A k Finset.subset_union_right hG)⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetMemTensorPowerFirstFactorAdjoinFinseStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_mem_tensorPowerFirstFactorAdjoinFinset : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (x : PiTensorProduct R (fun _ : Fin (k + 1) => A)), ∃ F : Finset A, x ∈ firstAndFinite R A k F := by
  first | (exact @GlobalTheory.EtC.exists_finset_mem_firstAndFinite) | (exact GlobalTheory.EtC.exists_finset_mem_firstAndFinite) | (intros; apply GlobalTheory.EtC.exists_finset_mem_firstAndFinite  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetIsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetIsIntegral
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_isIntegral (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A) :
    Algebra.IsIntegral R (firstAndFinite R A k F) := by
  unfold firstAndFinite
  apply Algebra.IsIntegral.adjoin
  rintro x (⟨a, rfl⟩ | hx)
  · exact (Algebra.IsIntegral.isIntegral a).map _
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a, -, rfl⟩ := hi
    exact (Algebra.IsIntegral.isIntegral a).map _

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetIsIntegralStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_isIntegral : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A), Algebra.IsIntegral R (firstAndFinite R A k F) := by
  first | (exact @GlobalTheory.EtC.firstAndFinite_isIntegral) | (exact GlobalTheory.EtC.firstAndFinite_isIntegral) | (intros; apply GlobalTheory.EtC.firstAndFinite_isIntegral  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceTensorPowerIntegralClosur
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem hInv_of_finite_over_aic (q : ℕ) [NeZero q] (d : ℕ) (hH : (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R))
    (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D] (hq : IsUnit (q : D))
    (hd : ringKrullDim D ≤ d) (T : Type) [CommRing T] [IsDomain T] [Algebra D T]
    [Algebra.IsIntegral D T] (hT : AIC T) (hTq : HInv q T) (E : Type) [CommRing E] [Algebra D E]
    [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E)
    (hF : Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤) : HInv q E := by
  have hlow := GlobalTheory.T.etaleHomotopyInvariant_integral_killed_of_lowerDim q d hH D hq hd
  have hqE : IsUnit (q : E) := by simpa using hq.map (algebraMap D E)
  set X : Finset (E →ₐ[D] T) := (GlobalTheory.T.finite_retractions_of_adjoin_finset_integral_domain D T E ι F hF).toFinset with hX
  have hXid : ∀ χ ∈ X, χ.comp ι = AlgHom.id D T := fun χ hχ => by simpa [hX] using hχ
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.exists_ne_zero_isNilpotent_mul_finite_inf_fg_ideals D E (E →ₐ[D] T) X (fun χ => RingHom.ker χ)
    (fun χ hχ => GlobalTheory.T.ker_retraction_fg_of_adjoin_finset D T E ι F hF χ (hXid χ hχ))
    (fun Q hQ hQc => by
      obtain ⟨χ, hχι, hχQ⟩ := GlobalTheory.T.exists_retraction_of_monicPolynomialsHaveRoots D T E hT ι Q hQ hQc
      have hmem : χ ∈ X := by simpa [hX] using hχι
      rw [← hχQ]
      exact iInf₂_le χ hmem)
  set I : Ideal E := ⨅ χ ∈ X, RingHom.ker χ with hI
  set J : Ideal E := Ideal.span {algebraMap D E s} with hJ
  have hIJ : I ⊓ J ≤ nilradical E := by
    intro y hy
    obtain ⟨hyI, hyJ⟩ := Ideal.mem_inf.mp hy
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hyJ
    obtain ⟨m, hm⟩ := hs _ hyI
    refine ⟨2 * m, ?_⟩
    calc (a * algebraMap D E s) ^ (2 * m)
        = a ^ m * (algebraMap D E s * (a * algebraMap D E s)) ^ m := by ring
      _ = 0 := by rw [hm, mul_zero]
  have hJs : ∀ K : Ideal E, J ≤ K → algebraMap D (E ⧸ K) s = 0 := by
    intro K hK
    rw [IsScalarTower.algebraMap_apply D E (E ⧸ K), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hK (Ideal.mem_span_singleton_self _)
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q E I J hIJ hqE (GlobalTheory.T.hInv_quot_iInf_ker_retractions q D T E hq hTq hlow ι X hXid)
    (hlow (E ⧸ J) s hs0 (hJs J le_rfl)) (hlow (E ⧸ (I ⊔ J)) s hs0 (hJs _ le_sup_right))

def subalgebraOfSubringEquiv {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) :
    S ≃+* subalgebraOfSubring S.toSubring where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem hInv_tensorPower_integralClosure : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ k : ℕ, HInv q (PiTensorProduct D (fun _ : Fin (k + 1) => integralClosure D (AlgebraicClosure (FractionRing D)))) := by
  intro q _ d hH D _ _ _ hq hd k
  have hqDp : IsUnit (q : integralClosure D (AlgebraicClosure (FractionRing D))) := by
    simpa using hq.map (algebraMap D (integralClosure D (AlgebraicClosure (FractionRing D))))
  have hTq := GlobalTheory.T.etaleHomotopyInvariance_absolutelyIntegrallyClosed q _ (GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure D) hqDp
  have hqS : ∀ F, IsUnit (q : firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F) :=
    fun F => by simpa using hq.map (algebraMap D (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F))
  refine GlobalTheory.T.hInv_of_directed_union_subalgebras q _ (Finset (integralClosure D (AlgebraicClosure (FractionRing D))))
    (fun F => subalgebraOfSubring (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F).toSubring)
    ?_ ?_ ?_ ?_
  · intro F G hFG x hx
    rw [mem_subalgebraOfSubring] at hx ⊢
    exact Algebra.adjoin_mono (Set.union_subset_union_right _
      (Set.iUnion_mono fun i => Set.image_mono (Finset.coe_subset.mpr hFG))) hx
  · intro x
    obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_mem_tensorPowerFirstFactorAdjoinFinset D _ k x
    exact ⟨F, (mem_subalgebraOfSubring).mpr hF⟩
  · intro F
    simpa using (hqS F).map (subalgebraOfSubringEquiv (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F))
  · intro F
    haveI := GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_isIntegral D (integralClosure D (AlgebraicClosure (FractionRing D))) k F
    obtain ⟨F', hF'⟩ := GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_fg_over_first D (integralClosure D (AlgebraicClosure (FractionRing D))) k F
    exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ (subalgebraOfSubringEquiv _)
      (hInv_of_finite_over_aic q d hH D hq hd _ (GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure D) hTq _ (firstIncl D _ k F) F' hF')

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceTensorPowerIntegralClosurStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_homotopy_invariance_tensor_power_integral_closure : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ k : ℕ, HInv q (PiTensorProduct D (fun _ : Fin (k + 1) => integralClosure D (AlgebraicClosure (FractionRing D)))) := by
  first | (exact @GlobalTheory.EtC.hInv_tensorPower_integralClosure) | (exact GlobalTheory.EtC.hInv_tensorPower_integralClosure) | (intros; apply GlobalTheory.EtC.hInv_tensorPower_integralClosure  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfDomainsOfDimLt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfDomainsOfDimLt
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem hInv_quot_inf (q : ℕ) [NeZero q] (R : Type) [CommRing R] (I J : Ideal R)
    (hq : IsUnit (q : R)) (hI : HInv q (R ⧸ I)) (hJ : HInv q (R ⧸ J))
    (hIJ : HInv q (R ⧸ (I ⊔ J))) : HInv q (R ⧸ (I ⊓ J)) := by
  set K := I ⊓ J with hK
  let f := Ideal.Quotient.mk K
  have hqA : IsUnit (q : R ⧸ K) := by simpa using hq.map f
  have hinf : Ideal.map f I ⊓ Ideal.map f J ≤ nilradical (R ⧸ K) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hx.1
    obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective).mp hx.2
    have h1 : b - a ∈ K := Ideal.Quotient.eq.mp hab
    have haJ : a ∈ J := by
      have := J.sub_mem hb h1.2
      simpa using this
    have : f a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ⟨ha, haJ⟩
    rw [this]
    exact (nilradical (R ⧸ K)).zero_mem
  have eI : (R ⧸ K) ⧸ Ideal.map f I ≃+* R ⧸ I := DoubleQuot.quotQuotEquivQuotOfLE inf_le_left
  have eJ : (R ⧸ K) ⧸ Ideal.map f J ≃+* R ⧸ J := DoubleQuot.quotQuotEquivQuotOfLE inf_le_right
  have eIJ : (R ⧸ K) ⧸ (Ideal.map f I ⊔ Ideal.map f J) ≃+* R ⧸ (I ⊔ J) :=
    (Ideal.quotEquivOfEq (Ideal.map_sup f I J).symm).trans
      (DoubleQuot.quotQuotEquivQuotOfLE (inf_le_left.trans le_sup_left))
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q (R ⧸ K) (Ideal.map f I) (Ideal.map f J) hinf hqA
    (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eI.symm hI) (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eJ.symm hJ)
    (GlobalTheory.T.etaleHomotopyInvariantTwists_of_ringEquiv q _ _ eIJ.symm hIJ)

theorem ringKrullDim_quot_sup_succ_le (R : Type) [CommRing R] (p J : Ideal R) [p.IsPrime]
    (hJ : ¬ J ≤ p) : ringKrullDim (R ⧸ (p ⊔ J)) + 1 ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨x, hxJ, hxp⟩ := Set.not_subset.mp hJ
  let g := Ideal.Quotient.mk p
  have hx0 : g x ≠ 0 := fun h => hxp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hnzd : g x ∈ nonZeroDivisors (R ⧸ p) := mem_nonZeroDivisors_of_ne_zero hx0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have hle : Ideal.span {g x} ≤ Ideal.map g (p ⊔ J) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem g (Ideal.mem_sup_right hxJ)
  have h2 : ringKrullDim ((R ⧸ p) ⧸ Ideal.map g (p ⊔ J)) ≤
      ringKrullDim ((R ⧸ p) ⧸ Ideal.span {g x}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
  have e : (R ⧸ p) ⧸ Ideal.map g (p ⊔ J) ≃+* R ⧸ (p ⊔ J) :=
    DoubleQuot.quotQuotEquivQuotOfLE le_sup_left
  have h3 : ringKrullDim (R ⧸ (p ⊔ J)) ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.map g (p ⊔ J)) :=
    ringKrullDim_le_of_surjective e.toRingHom e.surjective
  have h4 : ringKrullDim (R ⧸ (p ⊔ J)) + 1 ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.span {g x}) + 1 := by
    gcongr
    exact h3.trans h2
  exact h4.trans h1

theorem withBot_lt_of_add_one_le (a : WithBot ℕ∞) (d : ℕ) (h : a + 1 ≤ (d : WithBot ℕ∞)) :
    a < (d : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((d : ℕ∞)) : WithBot ℕ∞) := by exact_mod_cast h
      rw [WithBot.coe_le_coe] at h2
      simp at h2
    | coe n =>
      have h' : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast h
      have : n + 1 ≤ d := by exact_mod_cast h'
      have : n < d := by omega
      exact_mod_cast this

end GlobalTheory

namespace GlobalTheory

theorem hInv_of_domains_of_dim_lt : ∀ (q : ℕ) [NeZero q] (d : ℕ),
    (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) →
    (∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D) →
    ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R ≤ d → HInv q R := by
  intro q _ d hlt hdom R _ _ hq hd
  have key : ∀ s : Finset (Ideal R), (∀ p ∈ s, p.IsPrime) → HInv q (R ⧸ s.inf id) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      haveI : Subsingleton (R ⧸ (∅ : Finset (Ideal R)).inf id) :=
        Ideal.Quotient.subsingleton_iff.mpr (by simp)
      exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton q _ inferInstance
    | insert p s hps ih =>
      intro hs
      have hp : p.IsPrime := hs p (Finset.mem_insert_self p s)
      have ihs := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
      rw [Finset.inf_insert, id]
      by_cases hJ : s.inf id ≤ p
      · rw [inf_eq_right.mpr hJ]; exact ihs
      · haveI : @Algebra.FiniteType ℤ (R ⧸ p) _ _ (Ring.toIntAlgebra _) := by
          convert (inferInstance : Algebra.FiniteType ℤ (R ⧸ p))
          all_goals first | rfl | exact Subsingleton.elim _ _
        haveI : @Algebra.FiniteType ℤ (R ⧸ (p ⊔ s.inf id)) _ _ (Ring.toIntAlgebra _) := by
          convert (inferInstance : Algebra.FiniteType ℤ (R ⧸ (p ⊔ s.inf id)))
          all_goals first | rfl | exact Subsingleton.elim _ _
        refine hInv_quot_inf q R p (s.inf id) hq ?_ ihs ?_
        · exact hdom (R ⧸ p) (by simpa using hq.map (Ideal.Quotient.mk p))
            ((ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective).trans hd)
        · refine hlt (R ⧸ (p ⊔ s.inf id)) (by simpa using hq.map (Ideal.Quotient.mk (p ⊔ s.inf id))) ?_
          refine withBot_lt_of_add_one_le _ d ?_
          exact (ringKrullDim_quot_sup_succ_le R p (s.inf id) hJ).trans
            ((ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective).trans hd)
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hfin := minimalPrimes.finite_of_isNoetherianRing R
  have hN : hfin.toFinset.inf id = nilradical R := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset, minimalPrimes, Ideal.sInf_minimalPrimes]
    rfl
  have hred : HInv q (R ⧸ nilradical R) := by
    rw [← hN]
    refine key _ (fun p hp => ?_)
    rw [Set.Finite.mem_toFinset] at hp
    exact hp.1.1
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q R (nilradical R) (nilradical R) (by simp) hq hred hred (by rwa [sup_idem])

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfDomainsOfDimLtStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_domains_of_dim_lt : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → (∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R ≤ d → HInv q R := by
  first | (exact @GlobalTheory.hInv_of_domains_of_dim_lt) | (exact GlobalTheory.hInv_of_domains_of_dim_lt) | (intros; apply GlobalTheory.hInv_of_domains_of_dim_lt  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceTateTwistStrictlyHenselian
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem GlobalTheory.homotopyInvariance_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
  classical
  intro q _ A _ _ hq
  have hfg : ∀ d : ℕ, ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R := by
    intro d
    induction d with
    | zero =>
      intro R _ _ _ hd
      apply GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact absurd hd (not_lt.mpr (by exact_mod_cast ringKrullDim_nonneg_of_nontrivial))
    | succ d ih =>
      intro R _ _ hR hd
      have hdom : ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D := by
        intro D _ _ _ hD hDd
        refine GlobalTheory.T.etaleHomotopyInvariance_cechDescent_integral q D (integralClosure D (AlgebraicClosure (FractionRing D))) inferInstance ?_ hD (GlobalTheory.T.etale_homotopy_invariance_tensor_power_integral_closure q d ih D hD hDd)
        intro x hx
        have hinj : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D))) := by
          rw [IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]
          exact (algebraMap (FractionRing D) _).injective.comp (IsFractionRing.injective D (FractionRing D))
        have h0 : x = 0 := by
          apply hinj
          have := congrArg Subtype.val (RingHom.mem_ker.mp hx)
          simpa using this
        rw [h0]; exact zero_mem _
      refine GlobalTheory.T.etaleHomotopyInvariantTwists_of_domains_of_dim_lt q d ih hdom R hR ?_
      revert hd
      induction ringKrullDim R with
      | bot => intro _; exact bot_le
      | coe n =>
        intro h
        have h' : n < ((d + 1 : ℕ) : ℕ∞) := WithBot.coe_lt_coe.mp h
        exact WithBot.coe_le_coe.mpr (Order.le_of_lt_add_one (by simpa using h'))
  let S : Finset A → Subalgebra ℤ A := fun s => Algebra.adjoin ℤ (insert (↑(hq.unit⁻¹) : A) (s : Set A))
  have hmono : Monotone S := fun s t hst => Algebra.adjoin_mono (Set.insert_subset_insert (by exact_mod_cast hst))
  have hcov : ∀ a, ∃ s, a ∈ S s := fun a => ⟨{a}, Algebra.subset_adjoin (by simp)⟩
  have hunit : ∀ s, IsUnit (q : S s) := by
    intro s
    have hm : (↑(hq.unit⁻¹) : A) ∈ S s := Algebra.subset_adjoin (Set.mem_insert _ _)
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hm⟩, ?_⟩
    apply Subtype.ext
    simp
  have hinv : ∀ s, HInv q (S s) := by
    intro s
    have : Algebra.FiniteType ℤ (S s) := by
      have hfg' : (S s).FG := by
        have : (insert (↑(hq.unit⁻¹) : A) (s : Set A)) = ((insert (↑(hq.unit⁻¹) : A) s : Finset A) : Set A) := by simp
        rw [show S s = Algebra.adjoin ℤ (insert (↑(hq.unit⁻¹) : A) (s : Set A)) from rfl, this]
        exact Subalgebra.fg_adjoin_finset _
      exact Subalgebra.fg_iff_finiteType _ |>.mp hfg'
    have hlt := GlobalTheory.ringKrullDim_lt_top_of_essFiniteType (S s)
    obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (S s) ≤ d := by
      revert hlt
      induction ringKrullDim (S s) with
      | bot => intro _; exact ⟨0, bot_le⟩
      | coe n =>
        intro h
        induction n with
        | top => exact absurd h (lt_irrefl _)
        | coe m => exact ⟨m, le_rfl⟩
    exact hfg (d + 1) (S s) (hunit s) (lt_of_le_of_lt hd (by exact_mod_cast Nat.lt_succ_self d))
  intro i
  exact GlobalTheory.T.hInv_of_directed_union_subalgebras q A (Finset A) S hmono hcov hunit hinv i
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceTateTwistStrictlyHenselianStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homotopyInvariance_tateTwist_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
  first | (exact @GlobalTheory.homotopyInvariance_strictlyHenselian) | (exact GlobalTheory.homotopyInvariance_strictlyHenselian) | (intros; apply GlobalTheory.homotopyInvariance_strictlyHenselian  <;> assumption)
end
