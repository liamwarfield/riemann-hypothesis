module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanForm
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterOrthogonalIsRational
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterOrthogonalIsRational
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann

section Core

open GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.SelfDual Topology

variable {F : Type} [Field F] [NumberField F]

theorem fin_eq_zero (ψf : AddChar (A F) ℂ) (hψ : GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf) {y : A F}
    (hy : ∀ t : F, ψf (algebraMap F (A F) t * y) = 1) : y = 0 := by
  obtain ⟨hlc, hsc, ht2, hOc, hOo, hden, hint, hnb, hcp, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hall : ∀ z : A F, ψf (z * y) = 1 := by
    intro z
    have hcl : IsClosed {z : A F | ψf (z * y) = 1} :=
      isClosed_eq (hψ.1.comp (continuous_id.mul continuous_const)) continuous_const
    exact hden.induction_on (p := fun z => ψf (z * y) = 1) z hcl hy
  have hMc : IsCompact (MG ψf : Set (A F)) := by
    refine isCompact_of_relIndex (ohG_le_MG hψ) ?_ hOc
    rw [relIndex_MG hψ]
    exact Int.natAbs_ne_zero.2 (discr_ne_zero F)
  obtain ⟨N, hN, hNK⟩ := hcp _ hMc
  have hinv : ∀ m : ℕ, 0 < m → (m : A F) * algebraMap F (A F) (m : F)⁻¹ = 1 := by
    intro m hm
    have hm' : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [← map_natCast (algebraMap F (A F)), ← map_mul, mul_inv_cancel₀ hm', map_one]
  have hmul : ∀ m : ℕ, 0 < m → algebraMap F (A F) (m : F)⁻¹ * ((N : A F) * y) ∈ Oh F := by
    intro m hm
    have h1 : algebraMap F (A F) (m : F)⁻¹ * y ∈ MG ψf := by
      intro z _
      show ψf (z * _) = 1
      rw [← mul_assoc]
      exact hall _
    have h2 := hNK _ h1
    rwa [mul_left_comm] at h2
  have hw : (N : A F) * y = 0 := by
    by_contra hne
    have hU : ({(N : A F) * y}ᶜ : Set (A F)) ∈ 𝓝 (0 : A F) :=
      isOpen_compl_singleton.mem_nhds (fun h => hne (Eq.symm h))
    obtain ⟨m, hm, hmU⟩ := hnb _ hU
    apply hmU _ (hmul m hm)
    rw [← mul_assoc, hinv m hm, one_mul]
    rfl
  calc y = algebraMap F (A F) (N : F)⁻¹ * ((N : A F) * y) := by
        rw [← mul_assoc, mul_comm (algebraMap F (A F) _), hinv N hN, one_mul]
    _ = 0 := by rw [hw, mul_zero]

theorem coeff_eq_zero (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (D : InfinitePlace F → ℝ)
    (h : ∀ t : F, ∑ w, ρ w t * D w = 0) : ∀ w, D w = 0 := by
  have hinj : Function.Injective (fun w => ((ρ w : F →+* ℝ) : F →* ℝ)) := by
    intro w w' hww
    have h1 : w.embedding = w'.embedding := by
      ext x
      rw [← hρ, ← hρ]
      have : ρ w x = ρ w' x := DFunLike.congr_fun hww x
      rw [this]
    rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', h1]
  have hli := (linearIndependent_monoidHom F ℝ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  refine hli D ?_
  ext t
  simpa [mul_comm] using h t

theorem real_eq_of_int (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (X : InfinitePlace F → ℝ)
    (hX : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, ρ w (r : F) * X w = n) : ∃ c : F, ∀ w, X w = ρ w c := by
  classical
  set e := integralBasis F with he
  have hXe : ∀ i, ∃ n : ℤ, ∑ w, ρ w (e i) * X w = n := by
    intro i
    obtain ⟨n, hn⟩ := hX (RingOfIntegers.basis F i)
    refine ⟨n, ?_⟩
    rw [← hn, he, integralBasis_apply]
  choose n hn using hXe
  set c : F := e.traceDual.equivFun.symm (fun i => (n i : ℚ)) with hc
  have hrepr : ∀ i, Algebra.trace ℚ F (c * e i) = n i := by
    intro i
    have h1 := Module.Basis.traceDual_repr_apply e c i
    rw [Algebra.traceForm_apply] at h1
    rw [← h1, ← Module.Basis.equivFun_apply, hc, LinearEquiv.apply_symm_apply]
  refine ⟨c, fun w => ?_⟩
  have hz : ∀ t : F, ∑ w, ρ w t * (ρ w c - X w) = 0 := by
    let Lf : F →ₗ[ℚ] ℝ := ∑ w, (ρ w c - X w) • (ρ w).toRatAlgHom.toLinearMap
    have hL : Lf = 0 := by
      refine e.ext fun i => ?_
      have h2 := GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ (c * e i)
      rw [hrepr] at h2
      simp only [Lf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul,
        AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply]
      simp only [map_mul] at h2
      have h3 : ∑ w, (ρ w c - X w) * ρ w (e i) = ∑ w, ρ w c * ρ w (e i) - ∑ w, ρ w (e i) * X w := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun w _ => by ring
      rw [h3, h2, hn]
      simp
    intro t
    have := LinearMap.congr_fun hL t
    simp only [Lf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply, smul_eq_mul,
      AlgHom.toLinearMap_apply, RingHom.toRatAlgHom_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  have := coeff_eq_zero ρ hρ _ hz w
  linarith

def eR (s : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))

theorem eR_add (s u : ℝ) : eR (s + u) = eR s * eR u := by
  simp only [eR, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem eR_zero : eR 0 = 1 := by simp [eR]

theorem eR_int {s : ℝ} (h : eR s = 1) : ∃ n : ℤ, s = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have h1 : (s : ℂ) = n := by
    refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
    rw [hn]
    ring
  exact_mod_cast h1

theorem sub_field (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (ψf : AddChar (A F) ℂ)
    (hstd : GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf) {X : InfinitePlace F → ℝ} {y : A F}
    (H : ∀ t : F, eR (∑ w, ρ w t * X w) * ψf (algebraMap F (A F) t * y) = 1) (c : F) (t : F) :
    eR (∑ w, ρ w t * (X w - ρ w c)) * ψf (algebraMap F (A F) t * (y - algebraMap F (A F) c)) = 1 := by
  have hT : eR (∑ w, ρ w (t * c)) * ψf (algebraMap F (A F) (t * c)) = 1 := by
    rw [GlobalTheory.CompanionTheory.SW.CoefEis.sum_places_eq_trace F hF ρ hρ, hstd.2, eR, ← Complex.exp_add]
    have h0 : 2 * (Real.pi : ℂ) * Complex.I * (((Algebra.trace ℚ F (t * c) : ℚ) : ℝ) : ℂ) +
        -(2 * (Real.pi : ℂ) * Complex.I) * ((Algebra.trace ℚ F (t * c) : ℚ) : ℂ) = 0 := by
      push_cast
      ring
    rw [h0, Complex.exp_zero]
  have e1 : ∑ w, ρ w t * X w = ∑ w, ρ w t * (X w - ρ w c) + ∑ w, ρ w (t * c) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by rw [map_mul]; ring
  have e2 : algebraMap F (A F) t * y =
      algebraMap F (A F) t * (y - algebraMap F (A F) c) + algebraMap F (A F) (t * c) := by
    rw [map_mul]
    ring
  have h := H t
  rw [e1, e2, eR_add, AddChar.map_add_eq_mul] at h
  have key : ∀ p q r s : ℂ, (p * q) * (r * s) = 1 → q * s = 1 → p * r = 1 :=
    fun p q r s h1 h2 => by linear_combination h1 - p * r * h2
  exact key _ _ _ _ h hT

theorem core (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (ψf : AddChar (A F) ℂ)
    (hstd : GlobalTheory.CompanionTheory.SW.Core.IsStdChar F ψf) (X : InfinitePlace F → ℝ) (y : A F)
    (H : ∀ t : F, eR (∑ w, ρ w t * X w) * ψf (algebraMap F (A F) t * y) = 1) :
    ∃ c : F, (∀ w, X w = ρ w c) ∧ y = algebraMap F (A F) c := by
  obtain ⟨-, -, -, -, hOo, hden, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hopen : IsOpen {z : A F | y - z ∈ Oh F} := hOo.preimage (continuous_const.sub continuous_id)
  obtain ⟨c1, hc1⟩ := hden.exists_mem_open hopen ⟨y, by
    show y - y ∈ Oh F
    rw [sub_self]
    exact (ohG F).zero_mem⟩
  have hc1' : y - algebraMap F (A F) c1 ∈ Oh F := hc1
  have H1 := sub_field hF ρ hρ ψf hstd H c1
  have hXint : ∀ r : 𝓞 F, ∃ n : ℤ, ∑ w, ρ w (r : F) * (X w - ρ w c1) = n := by
    intro r
    have h1 := H1 r
    rw [((GlobalTheory.T.standard_adelic_character F).2 ψf hstd).2.1 _ (oh_mul ((hint _).2 ⟨r, rfl⟩) hc1'), mul_one] at h1
    exact eR_int h1
  obtain ⟨c2, hc2⟩ := real_eq_of_int hF ρ hρ _ hXint
  have H2 := sub_field hF ρ hρ ψf hstd H1 c2
  have hy0 : y - algebraMap F (A F) c1 - algebraMap F (A F) c2 = 0 := fin_eq_zero ψf hstd fun t => by
    have h1 := H2 t
    have h0 : ∑ w, ρ w t * ((X w - ρ w c1) - ρ w c2) = 0 :=
      Finset.sum_eq_zero fun w _ => by rw [← hc2 w, sub_self, mul_zero]
    rwa [h0, eR_zero, one_mul] at h1
  refine ⟨c1 + c2, fun w => ?_, ?_⟩
  · have := hc2 w
    rw [map_add (f := _)]
    linarith
  · rw [map_add (f := _)]
    linear_combination hy0

end Core

theorem annihilator_eq : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ x : AF F, (∀ t : F, ψ (algebraMap F (AF F) t * x) = 1) → ∃ c : F, x = algebraMap F (AF F) c := by
  intro F _ _ hF ψ hψ x hx
  obtain ⟨ρ, e, hρ, he, heρ, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hF
  obtain ⟨a, ha, hinf, ψf, hstd, hfin⟩ := GlobalTheory.T.adelic_character_archimedean_form F hF ρ e hρ he heρ ψ hψ
  have hsplit : ∀ (u : Ainf F) (v : Af F),
      ψ (u, v) = eR (∑ w, ρ w a * e u w) * ψf (algebraMap F (Af F) a * v) := by
    intro u v
    have h : ((u, v) : AF F) = pairA F u 0 + pairA F 0 v := by
      show ((u, v) : Ainf F × Af F) = ((u, 0) : Ainf F × Af F) + ((0, v) : Ainf F × Af F)
      rw [Prod.mk_add_mk, add_zero, zero_add]
    rw [h, AddChar.map_add_eq_mul, hinf, hfin]
    rfl
  have H : ∀ t : F, eR (∑ w, ρ w t * (ρ w a * e x.1 w)) *
      ψf (algebraMap F (Af F) t * (algebraMap F (Af F) a * x.2)) = 1 := by
    intro t
    have h := hx t
    have hm : algebraMap F (AF F) t * x =
        (algebraMap F (Ainf F) t * x.1, algebraMap F (Af F) t * x.2) := rfl
    rw [hm, hsplit] at h
    have e1 : ∑ w, ρ w a * e (algebraMap F (Ainf F) t * x.1) w = ∑ w, ρ w t * (ρ w a * e x.1 w) :=
      Finset.sum_congr rfl fun w _ => by rw [map_mul, Pi.mul_apply, heρ]; ring
    have e2 : algebraMap F (Af F) a * (algebraMap F (Af F) t * x.2) =
        algebraMap F (Af F) t * (algebraMap F (Af F) a * x.2) := mul_left_comm _ _ _
    rw [e1, e2] at h
    exact h
  obtain ⟨c, hc1, hc2⟩ := core hF ρ hρ ψf hstd _ _ H
  refine ⟨a⁻¹ * c, ?_⟩
  have hx1 : x.1 = algebraMap F (Ainf F) (a⁻¹ * c) := by
    apply e.injective
    funext w
    rw [heρ, map_mul, map_inv₀]
    have hne : ρ w a ≠ 0 := (map_ne_zero _).2 ha
    have h1 := hc1 w
    rw [← h1]
    field_simp
  have hx2 : x.2 = algebraMap F (Af F) (a⁻¹ * c) := by
    rw [map_mul, ← hc2, ← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  exact Prod.ext hx1 hx2

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterOrthogonalIsRationalStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_character_orthogonal_is_rational : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ x : AF F, (∀ t : F, ψ (algebraMap F (AF F) t * x) = 1) → ∃ c : F, x = algebraMap F (AF F) c := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq <;> assumption)
end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.FourierComplete

open scoped Pointwise

section Gen

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem exists_descent (Λ : AddSubgroup V) (f : V → ℂ) (hf : Continuous f)
    (hp : ∀ x, ∀ l ∈ Λ, f (x + l) = f x) :
    ∃ h : C(V ⧸ Λ, ℂ), ∀ x, h (QuotientAddGroup.mk x) = f x := by
  let p : C(V, V ⧸ Λ) := ⟨QuotientAddGroup.mk, continuous_quotient_mk'⟩
  have hq : Topology.IsQuotientMap p := QuotientAddGroup.isQuotientMap_mk Λ
  have hfac : Function.FactorsThrough (⟨f, hf⟩ : C(V, ℂ)) p := by
    intro a b hab
    have h1 : -a + b ∈ Λ := QuotientAddGroup.eq.1 hab
    have h2 := hp a _ h1
    simpa using h2.symm
  refine ⟨hq.lift ⟨f, hf⟩ hfac, fun x => ?_⟩
  exact DFunLike.congr_fun (hq.lift_comp ⟨f, hf⟩ hfac) x

theorem compactSpace_quotient (Λ : AddSubgroup V) {K : Set V} (hK : IsCompact K)
    (hc : ∀ x, ∃ l ∈ Λ, x - l ∈ K) : CompactSpace (V ⧸ Λ) := by
  refine ⟨?_⟩
  have himg : (QuotientAddGroup.mk '' K : Set (V ⧸ Λ)) = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨l, hl, hx⟩ := hc x
    refine ⟨x - l, hx, ?_⟩
    rw [QuotientAddGroup.eq]
    have h1 : -(x - l) + x = l := by abel
    rwa [h1]
  rw [← himg]
  exact hK.image continuous_quotient_mk'

theorem mem_closure_span {X : Type*} [TopologicalSpace X] [CompactSpace X] {T : Type*} [AddCommGroup T]
    (c : T → C(X, ℂ)) (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t)
    (hstar : ∀ t, star (c t) = c (-t)) (hsep : ∀ x y, x ≠ y → ∃ t, c t x ≠ c t y) (f : C(X, ℂ)) :
    f ∈ closure ((Submodule.span ℂ (Set.range c) : Submodule ℂ C(X, ℂ)) : Set C(X, ℂ)) := by
  set S : Submodule ℂ C(X, ℂ) := Submodule.span ℂ (Set.range c) with hS
  have hcS : ∀ t, c t ∈ S := fun t => Submodule.subset_span ⟨t, rfl⟩
  have h1 : (1 : C(X, ℂ)) ∈ S := h0 ▸ hcS 0
  have hmul : ∀ x y, x ∈ S → y ∈ S → x * y ∈ S := by
    intro x y hx hy
    have hle : S * S ≤ S := by
      rw [hS, Submodule.span_mul_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
      show c s * c t ∈ _
      rw [← hadd]
      exact hcS _
    exact hle (Submodule.mul_mem_mul hx hy)
  have hst : ∀ x ∈ S, star x ∈ S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h => obtain ⟨t, rfl⟩ := h; rw [hstar]; exact hcS _
    | zero => simp
    | add x y _ _ hx hy => rw [star_add]; exact S.add_mem hx hy
    | smul a x _ hx => rw [star_smul]; exact S.smul_mem _ hx
  let A : StarSubalgebra ℂ C(X, ℂ) :=
    { toSubalgebra := S.toSubalgebra h1 hmul, star_mem' := fun {a} ha => hst a ha }
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨t, ht⟩ := hsep x y hxy
    exact ⟨c t, ⟨c t, hcS t, rfl⟩, ht⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  have hf : f ∈ (A.topologicalClosure : Set C(X, ℂ)) := by
    rw [htop]
    trivial
  rwa [StarSubalgebra.topologicalClosure_coe] at hf

theorem eq_zero_of_coeffs_vanish [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (Λ : AddSubgroup V) [Countable Λ] (μ : Measure V) [μ.IsAddHaarMeasure] {D : Set V}
    (hD : IsAddFundamentalDomain Λ D μ) {K : Set V} (hK : IsCompact K)
    (hc : ∀ x, ∃ l ∈ Λ, x - l ∈ K) {T : Type*} [AddCommGroup T] (χ : T → V → ℂ)
    (hχc : ∀ t, Continuous (χ t)) (hχp : ∀ t x, ∀ l ∈ Λ, χ t (x + l) = χ t x)
    (h0 : ∀ x, χ 0 x = 1) (hadd : ∀ s t x, χ (s + t) x = χ s x * χ t x)
    (hconj : ∀ t x, star (χ t x) = χ (-t) x)
    (hsep : ∀ x y, (∀ t, χ t x = χ t y) → -x + y ∈ Λ)
    (g : V → ℂ) (hg : Continuous g) (hgp : ∀ x, ∀ l ∈ Λ, g (x + l) = g x)
    (hF : ∀ t, ∫ b in D, g b * χ (-t) b ∂μ = 0) (x : V) : g x = 0 := by
  haveI : CompactSpace (V ⧸ Λ) := compactSpace_quotient Λ hK hc
  choose c hcχ using fun t => exists_descent Λ (χ t) (hχc t) (hχp t)
  obtain ⟨gb, hgb⟩ := exists_descent Λ g hg hgp
  have hext : ∀ a b : C(V ⧸ Λ, ℂ),
      (∀ x : V, a (QuotientAddGroup.mk x) = b (QuotientAddGroup.mk x)) → a = b := by
    intro a b h
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact h x
  have hc0 : c 0 = 1 := hext _ _ fun x => by
    rw [hcχ, h0]; rfl
  have hcadd : ∀ s t, c (s + t) = c s * c t := fun s t => hext _ _ fun x => by
    rw [hcχ, hadd, ContinuousMap.mul_apply, hcχ, hcχ]
  have hcstar : ∀ t, star (c t) = c (-t) := fun t => hext _ _ fun x => by
    rw [ContinuousMap.star_apply, hcχ, hcχ, hconj]
  have hsepc : ∀ p q : V ⧸ Λ, p ≠ q → ∃ t, c t p ≠ c t q := by
    intro p q hpq
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective q
    by_contra hcon
    push Not at hcon
    apply hpq
    rw [QuotientAddGroup.eq]
    exact hsep a b fun t => by simpa [hcχ] using hcon t
  have hfin : μ D < ⊤ := Formalism.IndefR.Tow.fd_measure_lt_top hD hK (fun y => by
    obtain ⟨l, hl, hy⟩ := hc y
    refine ⟨-l, Λ.neg_mem hl, ?_⟩
    have h1 : -l + y = y - l := by abel
    rwa [h1])
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by simpa using hfin⟩
  let L : C(V ⧸ Λ, ℂ) → ℂ := fun s => ∫ b in D, g b * s (QuotientAddGroup.mk b) ∂μ
  have hbd : ∀ (s : C(V ⧸ Λ, ℂ)) (b : V), ‖g b * s (QuotientAddGroup.mk b)‖ ≤ ‖gb‖ * ‖s‖ := by
    intro s b
    rw [norm_mul, ← hgb b]
    exact mul_le_mul (gb.norm_coe_le_norm _) (s.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  have hint : ∀ s : C(V ⧸ Λ, ℂ),
      Integrable (fun b => g b * s (QuotientAddGroup.mk b)) (μ.restrict D) := by
    intro s
    have hcont : Continuous fun b => g b * s (QuotientAddGroup.mk b) :=
      hg.mul (s.continuous.comp continuous_quotient_mk')
    exact Integrable.of_bound hcont.aestronglyMeasurable (‖gb‖ * ‖s‖) (ae_of_all _ (hbd s))
  have hLc : Continuous L := by
    have hl : LipschitzWith (Real.toNNReal (‖gb‖ * (μ.restrict D).real Set.univ)) L := by
      refine LipschitzWith.of_dist_le' fun s s' => ?_
      rw [dist_eq_norm, dist_eq_norm]
      have h1 : L s - L s' = ∫ b in D, g b * (s - s') (QuotientAddGroup.mk b) ∂μ := by
        show (∫ b in D, _ ∂μ) - (∫ b in D, _ ∂μ) = _
        rw [← integral_sub (hint s) (hint s')]
        refine integral_congr_ae (ae_of_all _ fun b => ?_)
        simp [mul_sub]
      rw [h1]
      have h2 := norm_integral_le_of_norm_le_const (μ := μ.restrict D)
        (ae_of_all _ (hbd (s - s')))
      calc _ ≤ _ := h2
        _ = _ := by ring
    exact hl.continuous
  have hz : ∀ s ∈ Submodule.span ℂ (Set.range c), L s = 0 := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem s h =>
      obtain ⟨t, rfl⟩ := h
      have h1 := hF (-t)
      rw [neg_neg] at h1
      show ∫ b in D, g b * c t (QuotientAddGroup.mk b) ∂μ = 0
      simpa only [hcχ] using h1
    | zero => simp [L]
    | add s s' _ _ hs hs' =>
      have h1 : L (s + s') = L s + L s' := by
        show _ = (∫ b in D, _ ∂μ) + (∫ b in D, _ ∂μ)
        rw [← integral_add (hint s) (hint s')]
        refine integral_congr_ae (ae_of_all _ fun b => ?_)
        simp [mul_add]
      rw [h1, hs, hs', add_zero]
    | smul a s _ hs =>
      have h1 : L (a • s) = a * L s := by
        show _ = a * ∫ b in D, _ ∂μ
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun b => ?_)
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        ring
      rw [h1, hs, mul_zero]
  have hL0 : L (star gb) = 0 := by
    have hsub : ((Submodule.span ℂ (Set.range c) : Submodule ℂ C(V ⧸ Λ, ℂ)) : Set C(V ⧸ Λ, ℂ)) ⊆
        {s | L s = 0} := fun s hs => hz s hs
    exact closure_minimal hsub (isClosed_eq hLc continuous_const)
      (mem_closure_span c hc0 hcadd hcstar hsepc (star gb))
  have hpt : ∀ b, g b * (star gb) (QuotientAddGroup.mk b) = ((‖g b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    rw [ContinuousMap.star_apply, hgb]
    simpa using Complex.mul_conj' (g b)
  have hR : ∫ b in D, ‖g b‖ ^ 2 ∂μ = 0 := by
    have h1 : ((∫ b in D, ‖g b‖ ^ 2 ∂μ : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal, ← hL0]
      exact integral_congr_ae (ae_of_all _ fun b => (hpt b).symm)
    exact_mod_cast h1
  have hRint : Integrable (fun b => ‖g b‖ ^ 2) (μ.restrict D) := by
    have hcont : Continuous fun b => ‖g b‖ ^ 2 := hg.norm.pow 2
    refine Integrable.of_bound hcont.aestronglyMeasurable (‖gb‖ ^ 2) (ae_of_all _ fun b => ?_)
    rw [Real.norm_of_nonneg (by positivity), ← hgb b]
    exact pow_le_pow_left₀ (norm_nonneg _) (gb.norm_coe_le_norm _) 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun b => by positivity) hRint).1 hR
  let Z : Set V := {y | g y ≠ 0}
  have hZo : IsOpen Z := isOpen_ne_fun hg continuous_const
  have hZD : μ (Z ∩ D) = 0 := by
    rw [← Measure.restrict_apply hZo.measurableSet]
    refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hae)
    have hy' : g y ≠ 0 := hy
    simpa using hy'
  have hZinv : ∀ l : Λ, l +ᵥ Z = Z := by
    intro l
    ext y
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have h1 : g (-l +ᵥ y) = g y := by
      have h2 := hgp y (-(l : V)) (Λ.neg_mem l.2)
      rw [← h2, add_comm]
      rfl
    show g (-l +ᵥ y) ≠ 0 ↔ g y ≠ 0
    rw [h1]
  have hZ0 := hD.measure_zero_of_invariant Z hZinv hZD
  have hZe : Z = ∅ := (hZo.measure_eq_zero_iff μ).1 hZ0
  by_contra hx
  have hxZ : x ∈ Z := hx
  rw [hZe] at hxZ
  exact hxZ

end Gen

theorem countable_numberField (F : Type) [Field F] [NumberField F] : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

end GlobalTheory.CompanionTheory.FourierComplete
