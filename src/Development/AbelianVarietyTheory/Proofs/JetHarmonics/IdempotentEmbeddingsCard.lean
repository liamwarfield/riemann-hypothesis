module

public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCSteps
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffAddFirstSecond

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EmbCount

theorem exists_equiv (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) :
    ∃ Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O), ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E) := by
  have hinj := hv.hom_inj
  have h1 : ∀ (σ : E →ₐ[ℚ] C) (y : 𝓞 E), ∃ o : O, algebraMap O C o = σ (y : E) := by
    intro σ y
    have hi : IsIntegral ℤ (σ (y : E)) := (y.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)
    have hi' : IsIntegral O (σ (y : E)) := hi.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral hi')
  choose f hf using h1
  let Ψ : (E →ₐ[ℚ] C) → (𝓞 E →+* O) := fun σ =>
    { toFun := f σ
      map_one' := hinj (by simp [hf])
      map_mul' := fun a b => hinj (by simp [hf])
      map_zero' := hinj (by simp [hf])
      map_add' := fun a b => hinj (by simp [hf]) }
  have hΨ : ∀ σ (y : 𝓞 E), algebraMap O C (Ψ σ y) = σ (y : E) := hf
  refine ⟨Equiv.ofBijective Ψ ⟨?_, ?_⟩, hΨ⟩
  · intro σ σ' h
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext y
    have := hΨ σ y
    rw [h, hΨ] at this
    exact this.symm
  · intro τ
    have hu : ∀ y : Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ),
        IsUnit (((algebraMap O C).comp τ) y) := by
      rintro ⟨_, n, hn, rfl⟩
      have : (n : C) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hn
      simpa using this
    refine ⟨(IsLocalization.lift (S := E) hu).toRatAlgHom, ?_⟩
    ext y
    apply hinj
    rw [hΨ]
    exact IsLocalization.lift_eq hu y

theorem trace_eq_sum (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type)
    [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C]
    [Algebra ℤ_[p] O] (Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O))
    (hΦ : ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E)) (x : ℤ_[p] ⊗[ℤ] 𝓞 E) :
    algebraMap O C (algebraMap ℤ_[p] O (LinearMap.trace ℤ_[p] _ (LinearMap.mulLeft ℤ_[p] x))) =
      ∑ σ : E →ₐ[ℚ] C, algebraMap O C (tauExt (Φ σ) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    have : LinearMap.mulLeft ℤ_[p] (x + y) =
        LinearMap.mulLeft ℤ_[p] x + LinearMap.mulLeft ℤ_[p] y := by
      apply LinearMap.ext; intro z; simp [add_mul]
    simp only [this, map_add (f := _), hx, hy, Finset.sum_add_distrib]
  | tmul a y =>
    have h1 : LinearMap.mulLeft ℤ_[p] (a ⊗ₜ[ℤ] y) =
        a • (LinearMap.mulLeft ℤ y).baseChange ℤ_[p] := by
      ext z
      simp [TensorProduct.smul_tmul']
    have h2 : ((Algebra.trace ℤ (𝓞 E) y : ℤ) : ℚ) = Algebra.trace ℚ E (y : E) :=
      Algebra.coe_trace_int y
    have h3 := trace_eq_sum_embeddings C (K := ℚ) (L := E) (x := (y : E))
    have h4 : LinearMap.trace ℤ _ (LinearMap.mulLeft ℤ y) = Algebra.trace ℤ (𝓞 E) y := rfl
    rw [h1, map_smul, LinearMap.trace_baseChange, h4]
    rw [← h2] at h3
    simp only [tauExt, Algebra.TensorProduct.lift_tmul, map_mul, smul_eq_mul, Algebra.ofId_apply]
    rw [← Finset.mul_sum]
    congr 1
    simp only [RingHom.toIntAlgHom_apply, hΦ]
    rw [← h3]
    simp

theorem card_emb : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Algebra ℤ_[p] O] (e : ℤ_[p] ⊗[ℤ] 𝓞 E), e * e = e → Nonempty (Fin (Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] e))) ≃ Emb (O := O) e) ∧ Nat.card (𝓞 E →+* O) = Module.finrank ℚ E := by
  intro E _ _ p _ C _ _ _ v O _ _ hv _ e he
  classical
  obtain ⟨Φ, hΦ⟩ := exists_equiv E C v O hv
  have hinj := hv.hom_inj
  refine ⟨?_, ?_⟩
  · have ht := trace_eq_sum E p C O Φ hΦ e
    have hproj : LinearMap.IsProj (LinearMap.range (LinearMap.mulLeft ℤ_[p] e))
        (LinearMap.mulLeft ℤ_[p] e) :=
      ⟨fun x => ⟨x, rfl⟩, by
        rintro _ ⟨x, rfl⟩
        simp [← mul_assoc, he]⟩
    haveI : Module.Free ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) := inferInstance
    haveI : Module.Finite ℤ_[p] (ℤ_[p] ⊗[ℤ] 𝓞 E) := inferInstance
    rw [hproj.trace] at ht
    have hterm : ∀ σ : E →ₐ[ℚ] C, algebraMap O C (tauExt (Φ σ) e) =
        if Φ σ ∈ Emb (O := O) e then 1 else 0 := by
      intro σ
      split_ifs with h
      · have h' : tauExt (Φ σ) e = 1 := h
        rw [h', map_one]
      · have hid : IsIdempotentElem (algebraMap O C (tauExt (Φ σ) e)) := by
          unfold IsIdempotentElem
          rw [← map_mul, ← map_mul, he]
        rcases IsIdempotentElem.iff_eq_zero_or_one.mp hid with h0 | h1
        · exact h0
        · exact absurd (hinj (h1.trans (map_one _).symm)) h
    simp only [hterm, map_natCast, Finset.sum_boole, Nat.cast_inj] at ht
    rw [ht]
    refine ⟨(Finset.equivFin _).symm.trans (Φ.subtypeEquiv ?_)⟩
    intro σ
    simp
  · rw [← Nat.card_congr Φ, Nat.card_eq_fintype_card, AlgHom.card]

end GlobalTheory.EmbCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCompletedIsometryInducingHalfLevelAutomorp
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCompletedIsometryInducingHalfLevelAutomorp
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevelIsometry

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Host Sim)
open GlobalTheory.SimLift GlobalTheory.SimAlg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem bar_bar (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem modN_smul_of_mem (l : Level H) {c : 𝓞 E} (hc : c ∈ Ideal.span {(l.M : 𝓞 E)}) (x : D.La) :
    D.ModN l.M (c • x) := by
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  exact ⟨d • x, by rw [_root_.mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]⟩

theorem modN_smul_of_mem_smul (l : Level H) {c : 𝓞 E} (hc : c ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) {x : D.La}
    (hx : x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : D.ModN l.M (c • x) := by
  refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) fun y z hy hz => ?_
  · rw [← mul_smul]
    refine modN_smul_of_mem D l ?_ y
    rw [← l.prod, _root_.mul_comm c]
    exact Ideal.mul_mem_mul hr hc
  · rw [smul_add]; exact modN_add hy hz

theorem mem_of_modN (l : Level H) {x : D.La} (hx : D.ModN l.M x) :
    x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨b, rfl⟩ := hx
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  have h1 : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  have h2 : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_inf.trans inf_le_left
  exact h2 h1

theorem dvd_form_right {n : ℕ} (a : D.La) {x : D.La} (hx : D.ModN n x) : (n : ℤ) ∣ D.EF a x := by
  obtain ⟨b, rfl⟩ := hx
  exact ⟨D.EF a b, by rw [map_nsmul, nsmul_eq_mul]⟩

theorem exists_isometry_mod (l : Level H) (γ : LaMod D l ≃ₗ[𝓞 E] LaMod D l) :
    ∃ F : D.La →ₗ[𝓞 E] D.La, IsSimMod D l.M F 1 ∧
      ∀ x, F x - liftLa γ x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  obtain ⟨e', he', e, he, hee⟩ := Submodule.mem_sup.1
    (show (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) by rw [l.coprime]; trivial)
  have hbe' : H.bar e' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) he'
  have hbe : H.bar e ∈ l.Mb := by
    have h2 := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) he
    have h3 : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ := RingHom.ext bar_bar
    rwa [Ideal.map_map, h3, Ideal.map_id] at h2
  have hb1 : H.bar e' + H.bar e = 1 := by rw [← map_add (f := _), hee, map_one]
  have m1 : H.bar e * e ∈ Ideal.span {(l.M : 𝓞 E)} := by
    rw [← l.prod]; exact Ideal.mul_mem_mul hbe he
  have m2 : H.bar e' * e' ∈ Ideal.span {(l.M : 𝓞 E)} := by
    rw [← l.prod, _root_.mul_comm (H.bar e')]; exact Ideal.mul_mem_mul he' hbe'
  set f := liftLa γ with hf
  set g := liftLa γ.symm with hg
  have hgf : ∀ b, g (f b) - b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := fun b =>
    (Submodule.Quotient.eq _).1 (by
      have h1 := liftLa_spec γ.symm (f b)
      rw [hf, liftLa_spec γ b, LinearEquiv.symm_apply_apply] at h1
      exact h1)
  obtain ⟨h, hh⟩ := exists_rep D (fun a b => D.EF a (g b)) (fun a a' b => by simp)
    (fun a b b' => by simp) (fun c a b => by rw [g.map_smul, D.adj])
  have key : ∀ a b, (l.M : ℤ) ∣ D.EF (e' • h a) (e • f b) - D.EF a ((H.bar e' * e) • b) := fun a b => by
    rw [D.adj, hh, g.map_smul, g.map_smul, ← map_sub, mul_smul, ← smul_sub, ← smul_sub, smul_comm]
    exact dvd_form_right D a (modN_smul_of_mem_smul D l he (Submodule.smul_mem _ _ (hgf b)))
  refine ⟨e • f + e' • h, ⟨isCoprime_one_left, fun a b => ?_⟩, fun x => ?_⟩
  · have k1 := key a b
    have k2 := key b a
    rw [form_skew D (e' • h b), form_skew D b, D.adj (H.bar e' * e), map_mul, bar_bar] at k2
    have k3 : (l.M : ℤ) ∣ D.EF (e • f a) (e • f b) := by
      rw [D.adj, ← mul_smul]; exact dvd_form_right D _ (modN_smul_of_mem D l m1 _)
    have k4 : (l.M : ℤ) ∣ D.EF (e' • h a) (e' • h b) := by
      rw [D.adj, ← mul_smul]; exact dvd_form_right D _ (modN_smul_of_mem D l m2 _)
    have k5 := dvd_form_right D a (modN_smul_of_mem D l (Ideal.add_mem _ m1 m2) b)
    have k6 : D.EF a b = D.EF a ((H.bar e * e + H.bar e' * e') • b) + D.EF a ((H.bar e' * e) • b) +
        D.EF a ((e' * H.bar e) • b) := by
      rw [← map_add (f := _), ← map_add (f := _), ← add_smul, ← add_smul]
      have : H.bar e * e + H.bar e' * e' + H.bar e' * e + e' * H.bar e = 1 := by
        linear_combination (e' + e) * hb1 + hee
      rw [this, one_smul]
    obtain ⟨c, hc⟩ := dvd_sub (dvd_add (dvd_add (dvd_sub k1 k2) k3) k4) k5
    refine ⟨c, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _)]
    linear_combination hc - k6
  · have : (e • f + e' • h) x - f x = e' • (h x - f x) := by
      have h1 : e = 1 - e' := by linear_combination hee
      simp only [LinearMap.add_apply, LinearMap.smul_apply]
      rw [h1, sub_smul, one_smul, smul_sub]; abel
    rw [this]
    exact Submodule.smul_mem_smul he' Submodule.mem_top

theorem exists_tower {M : ℕ} (hM : 0 < M) {F : D.La →ₗ[𝓞 E] D.La} (hF : IsSimMod D M F 1) :
    ∃ s : ℕ → D.La →ₗ[𝓞 E] D.La, s 0 = F ∧ (∀ k, IsSimMod D (M ^ (k + 1)) (s k) 1) ∧
      ∀ a i j, a ∣ M ^ (i + 1) → a ∣ M ^ (j + 1) → ∀ x, D.ModN a (s i x - s j x) := by
  let T : ℕ → Type := fun k => {x : D.La →ₗ[𝓞 E] D.La // IsSimMod D (M ^ (k + 1)) x 1}
  have hstep : ∀ k (x : T k), ∃ y : T (k + 1), ∀ a, D.ModN (M ^ (k + 1)) (y.1 a - x.1 a) := by
    intro k x
    obtain ⟨f', h1, h2⟩ := step_sq D (pow_pos hM (k + 1)) x.2
    refine ⟨⟨f', h1.of_dvd D ?_⟩, h2⟩
    rw [← pow_add]
    exact pow_dvd_pow M (by omega)
  choose nx hnx using hstep
  let s : ∀ k, T k := fun k => Nat.rec (⟨F, by simpa using hF⟩ : T 0) nx k
  have hs : ∀ k j, k ≤ j → ∀ a, D.ModN (M ^ (k + 1)) ((s j).1 a - (s k).1 a) := by
    intro k j hkj
    induction j, hkj using Nat.le_induction with
    | base => exact fun a => ⟨0, by simp⟩
    | succ j hkj ih =>
      exact fun a => modN_trans D (modN_of_dvd_modulus D (pow_dvd_pow M (by omega)) (hnx j (s j) a)) (ih a)
  refine ⟨fun k => (s k).1, rfl, fun k => (s k).2, fun a i j hi hj x => ?_⟩
  rcases le_total i j with h | h
  · have := modN_neg (modN_of_dvd_modulus D hi (hs i j h x))
    rwa [neg_sub] at this
  · exact modN_of_dvd_modulus D hj (hs j i h x)

theorem exists_split (M n : ℕ) : ∃ a b k : ℕ, 0 < n → n = a * b ∧ a ∣ M ^ (k + 1) ∧ Nat.Coprime b M := by
  induction n using induction_on_primes with
  | zero => exact ⟨0, 0, 0, fun h => absurd h (lt_irrefl 0)⟩
  | one => exact ⟨1, 1, 0, fun _ => by simp⟩
  | prime_mul p n hp ih =>
    obtain ⟨a, b, k, h⟩ := ih
    by_cases hpM : p ∣ M
    · refine ⟨p * a, b, k + 1, fun hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := h (Nat.pos_of_mul_pos_left hn)
      refine ⟨by rw [h1, Nat.mul_assoc], ?_, h3⟩
      rw [pow_succ' M (k + 1)]
      exact Nat.mul_dvd_mul hpM h2
    · refine ⟨a, p * b, k, fun hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := h (Nat.pos_of_mul_pos_left hn)
      exact ⟨by rw [h1]; ring, h2, Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM) h3⟩

theorem modN_mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) {x : D.La} (ha : D.ModN a x) (hb : D.ModN b x) :
    D.ModN (a * b) x := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  obtain ⟨y, hy⟩ := ha
  obtain ⟨z, hz⟩ := hb
  refine ⟨u • z + v • y, ?_⟩
  have h1 : x = (u * a) • x + (v * b) • x := by rw [← add_smul, huv, one_smul]
  rw [h1]
  nth_rewrite 1 [hz]
  nth_rewrite 1 [hy]
  simp only [← natCast_zsmul, smul_add, smul_smul]
  push_cast
  congr 2 <;> ring

theorem exists_glue {a b : ℕ} (hab : Nat.Coprime a b) (s : D.La →ₗ[𝓞 E] D.La) :
    ∃ F : D.La →ₗ[𝓞 E] D.La, (∀ x, D.ModN a (F x - s x)) ∧ ∀ x, D.ModN b (F x - x) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
  refine ⟨(v * b) • s + (u * a) • LinearMap.id, fun x => ⟨u • (x - s x), ?_⟩, fun x => ⟨v • (s x - x), ?_⟩⟩
  · have h : v * (b : ℤ) = 1 - a * u := by linear_combination huv
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [h, ← natCast_zsmul, ← mul_smul, _root_.mul_comm u, sub_smul, smul_sub, one_smul]; abel
  · have h : u * (a : ℤ) = 1 - b * v := by linear_combination huv
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [h, ← natCast_zsmul, ← mul_smul, _root_.mul_comm v, sub_smul, smul_sub, one_smul]; abel

theorem exists_sim_trivial_away {M : ℕ} (hM : 0 < M) {F : D.La →ₗ[𝓞 E] D.La} (hF : IsSimMod D M F 1) :
    ∃ g : Sim D, (∀ n, g.ν n = 1) ∧ (∀ x, D.ModN M (g.f M x - F x)) ∧
      ∀ N : ℕ, 0 < N → Nat.Coprime N M → ∀ x, D.ModN N (g.f N x - x) := by
  obtain ⟨s, hs0, hs1, hs2⟩ := exists_tower D hM hF
  choose a b k habk using exists_split M
  have hcop : ∀ {x y j : ℕ}, x ∣ M ^ (j + 1) → Nat.Coprime y M → Nat.Coprime x y := fun h1 h2 =>
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left _ h2.symm)
  have hex : ∀ n, ∃ G : D.La →ₗ[𝓞 E] D.La, 0 < n →
      (∀ x, D.ModN (a n) (G x - s (k n) x)) ∧ ∀ x, D.ModN (b n) (G x - x) := fun n => by
    by_cases hn : 0 < n
    · obtain ⟨G, hG⟩ := exists_glue D (hcop (habk n hn).2.1 (habk n hn).2.2) (s (k n))
      exact ⟨G, fun _ => hG⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose G hG using hex
  have hA : ∀ n, 0 < n → ∀ d j, d ∣ n → d ∣ M ^ (j + 1) → ∀ x, D.ModN d (G n x - s j x) := by
    intro n hn d j hd hdj x
    obtain ⟨h1, h2, h3⟩ := habk n hn
    have hda : d ∣ a n := (hcop hdj h3).dvd_of_dvd_mul_right (h1 ▸ hd)
    exact modN_trans D (modN_of_dvd_modulus D hda ((hG n hn).1 x)) (hs2 d _ _ (hda.trans h2) hdj x)
  have hB : ∀ n, 0 < n → ∀ d, d ∣ n → Nat.Coprime d M → ∀ x, D.ModN d (G n x - x) := by
    intro n hn d hd hdM x
    obtain ⟨h1, h2, h3⟩ := habk n hn
    have hdb : d ∣ b n := (hcop h2 hdM).symm.dvd_of_dvd_mul_left (h1 ▸ hd)
    exact modN_of_dvd_modulus D hdb ((hG n hn).2 x)
  have hsim : ∀ n, 0 < n → IsSimMod D n (G n) 1 := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := habk n hn
    refine ⟨isCoprime_one_left, fun x y => ?_⟩
    have hn' : (n : ℤ) = a n * b n := by exact_mod_cast h1
    rw [hn']
    refine (Nat.isCoprime_iff_coprime.2 (hcop h2 h3)).mul_dvd ?_ ?_
    · have e1 := dvd_form_sub ((hG n hn).1 x) ((hG n hn).1 y)
      have e2 := ((hs1 (k n)).of_dvd D h2).2 x y
      have := dvd_add e1 e2
      rwa [sub_add_sub_cancel] at this
    · rw [_root_.one_mul]
      exact dvd_form_sub ((hG n hn).2 x) ((hG n hn).2 y)
  refine ⟨⟨G, fun _ => 1, fun n m hn hm x => ?_, fun n hn => SimLift.exists_inv D hn (hsim n hn),
    fun n hn => (hsim n hn).2⟩, fun _ => rfl, fun x => ?_, fun N hN hNM x => hB N hN N dvd_rfl hNM x⟩
  · obtain ⟨h1, h2, h3⟩ := habk n hn
    have hnm := Nat.mul_pos hn hm
    have ha : a n ∣ n := Dvd.intro _ h1.symm
    have hb : b n ∣ n := Dvd.intro_left _ h1.symm
    have e1 := modN_add (hA _ hnm _ _ (ha.mul_right m) h2 x) (modN_neg ((hG n hn).1 x))
    have e2 := modN_add (hB _ hnm _ (hb.mul_right m) h3 x) (modN_neg ((hG n hn).2 x))
    rw [neg_sub, sub_add_sub_cancel] at e1 e2
    have := modN_mul_of_coprime D (hcop h2 h3) e1 e2
    rwa [← h1] at this
  · rw [← hs0]
    exact hA M hM M 0 dvd_rfl (by simp) x

theorem exists_isometry_inducing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l), ∃ g : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim Dw, (∀ n, g.ν n = 1) ∧ (∀ x, (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ (g.f l.M x) = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ x)) ∧ ∀ N : ℕ, 0 < N → Nat.Coprime N l.M → ∀ x, Dw.ModN N (g.f N x - x) := by
  intro E _ _ _ H D l γ
  obtain ⟨F, hF, hFγ⟩ := exists_isometry_mod D l γ
  obtain ⟨g, h1, h2, h3⟩ := exists_sim_trivial_away D (by have := l.three_le; omega) hF
  refine ⟨g, h1, fun x => ?_, h3⟩
  rw [← liftLa_spec γ x]
  refine (Submodule.Quotient.eq _).2 ?_
  have := Submodule.add_mem _ (mem_of_modN D l (h2 x)) (hFγ x)
  rwa [sub_add_sub_cancel] at this

end GlobalTheory.LevelIsometry
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCompletedIsometryInducingHalfLevelAutomorpStatement
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completed_isometry_inducing_half_level_automorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l), ∃ g : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim Dw, (∀ n, g.ν n = 1) ∧ (∀ x, (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ (g.f l.M x) = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ x)) ∧ ∀ N : ℕ, 0 < N → Nat.Coprime N l.M → ∀ x, Dw.ModN N (g.f N x - x) := by
  first | exact @GlobalTheory.LevelIsometry.exists_isometry_inducing | exact GlobalTheory.LevelIsometry.exists_isometry_inducing | (intros; apply GlobalTheory.LevelIsometry.exists_isometry_inducing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegAtOfSabMap
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AlphaPair

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

set_option autoImplicit false in
attribute [local instance] Over.cartesianMonoidalCategory in
omit [IsCommMonObj G] [IsCommMonObj G'] in
theorem _root_.GlobalTheory.AlphaPair.exists_ptEquiv {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (gp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f F) {Z : Scheme.{0}}
    (a : Z ⟶ S') (b : Z ⟶ S) (hb : b = a ≫ f) :
    ∃ ρ : (Over.mk a ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (ρ x).left = x.left ≫ F := by
  subst hb
  have hpb : IsPullback F G'.hom G.hom f := gp.1
  let φ : (Over.mk a ⟶ G') → (Over.mk (a ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ F) (by
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w x]
      rfl)
  let ψ : (Over.mk (a ≫ f) ⟶ G) → (Over.mk a ⟶ G') := fun y =>
    Over.homMk (hpb.lift y.left a (by simpa using Over.w y)) (by simp)
  refine ⟨{ toFun := φ, invFun := ψ, left_inv := ?_, right_inv := ?_, map_mul' := ?_ },
    fun x => rfl⟩
  · intro x
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · simp [φ, ψ]
    · simp [φ, ψ]
  · intro y
    apply Over.OverMorphism.ext
    simp [φ, ψ]
  · intro x y
    apply Over.OverMorphism.ext
    exact (gp.2 (Over.mk a) x y (φ x) (φ y) rfl rfl).symm

end GlobalTheory.AlphaPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasTrivialKernelIff
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KerPow
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistCompare

section Basis

variable {A : Type} [CommRing A] {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

end Basis

section Hyp

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

end Hyp

section Conclusion

variable {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R)

end Conclusion

theorem cube : Out.CubeSt :=
  GlobalTheory.AbLaw.Cube.cube_of_gen GlobalTheory.laws_without_cohomology.1 (GlobalTheory.AbLaw.exists_gen_theta
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
    GlobalTheory.laws_without_cohomology.1 GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy
    (GlobalTheory.AbLaw.polAV_veryAmpleBy GlobalTheory.laws_without_cohomology.2.2.1)
    GlobalTheory.AbLaw.isProjBy_tensor GlobalTheory.TrivLocus.isClosed_trivLocus
    (GlobalTheory.AbLaw.CubeOpen.triv_basicOpen_of_triv_fibre GlobalTheory.laws_without_cohomology.1 GlobalTheory.AbLaw.Seesaw.seesaw
      (GlobalTheory.SmallExtLift.exists_gen_of_small_extension GlobalTheory.laws_without_cohomology.1
        GlobalTheory.KuennethOne.kuenneth_injective)))

theorem exists_degPre {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Out.PolAV (Spec (CommRingCat.of R))) (c : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A) :
    ∃ (D : Out.DegPre R) (α : D.X) (e : D.P = P), e ▸ D.c α = c := by
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (cube _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := SelfUnif.exists_sym P
  choose psi hpsi using fun n : ℤ => DVR.exists_gen_of_local (V := FractionRing R) P.L P.isLB (K := PUnit)
    (fun _ => Out.ptK (c ^ n)) (fun _ => -1)
  exact ⟨{ P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := ℤ
           c := fun n => c ^ n, c_add := fun a b => zpow_add c a b, psi := psi, psi_gen := hpsi },
    (1 : ℤ), rfl, zpow_one c⟩

end GlobalTheory.TwistCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalBiextensionIntegralChartValuedExtens
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalBiextensionIntegralChartValuedExtens
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharDepth

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ in
theorem isCanonGauge_mapFB_tower {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type}
    [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) {h : PS k 2 d} {R' : Type} [CommRing R'] [Algebra R' k]
    (φ : R →+* R') (hφ : ∀ x, algebraMap R' k (φ x) = algebraMap R k x) (hh : B.IsCanonGauge k h) :
    (FBMap.mapFB φ B).IsCanonGauge k h := by
  have hK : ∀ {n : ℕ} (f : PS R n d), FB.toK k (MvPowerSeries.map φ f) = FB.toK k f := by
    intro n f
    ext mo
    simp only [MvPowerSeries.coeff_map, hφ]
  have hF : (FBMap.mapFB φ B).FK k = B.FK k := funext fun _ => hK _
  have hA : (FBMap.mapFB φ B).actK k = B.actK k := funext fun _ => funext fun _ => hK _
  refine ⟨hh.ax0, hh.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hF]; exact (hK _).trans hh.ph1
  · rw [hF]; exact (hK _).trans hh.ph2
  · exact (hK _).trans hh.sy
  · rw [hA]; exact (hK _).trans (hh.ad a)

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_formalBiext_valExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime]
      (X : ValExt T p), ∃ B : FB X.O (chD Ch.ch) (𝓞 E), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) ∧
      (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) ∧
      B.IsCanonGauge X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X
  letI := io.toAlgebra
  obtain ⟨BT, e1, e2, -, -, -, -, e7⟩ := integralChart_formalBiext E H Dw l Xo c T io y Ch
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  letI : Algebra T.V X.C := (X.ιF.comp (algebraMap T.V T.Fr)).toAlgebra
  haveI : IsScalarTower T.V T.Fr X.C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨-, -, h3, h4⟩ := e7 X.C
  refine ⟨FBMap.mapFB X.ι BT, ?_, fun a => ?_,
    isCanonGauge_mapFB_tower BT X.ι (fun x => (X.comp x).symm) ((h3 _).2 h4)⟩
  · rw [← e1]; rfl
  · rw [← e2]; rfl

end GlobalTheory.CharDepth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalBiextensionIntegralChartValuedExtensStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalBiextension_integral_chart_valuedExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p), ∃ B : FB X.O (chD Ch.ch) (𝓞 E), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) ∧ (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) ∧ B.IsCanonGauge X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) := by
  first | exact @GlobalTheory.CharDepth.exists_formalBiext_valExt | exact GlobalTheory.CharDepth.exists_formalBiext_valExt | (intros; apply GlobalTheory.CharDepth.exists_formalBiext_valExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsConjLevelMapByLevelMoves
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsConjLevelMapByLevelMoves
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ConjLevelMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_inv {S : Scheme.{0}} {t : SAB H S} (e : S ≅ S) (n : SABMap t t e.hom) :
    ∃ n' : SABMap t t e.inv, n.φ ≫ n'.φ = 𝟙 _ := by
  obtain ⟨i, hi⟩ := ObjMaps.exists_sab_id t
  obtain ⟨i', hi'⟩ := LevelFibre.sab_cast e.inv_hom_id.symm i
  obtain ⟨n', hn'⟩ := ObjMaps.exists_sab_cancel n i'
  have h : n'.φ ≫ n.φ = 𝟙 _ := hn'.symm.trans (hi'.trans hi)
  have pn : IsPullback n.φ t.G.hom t.G.hom e.hom := n.cart.1
  have : IsIso n.φ := pn.isIso_fst_of_isIso
  refine ⟨n', ?_⟩
  rw [← cancel_mono n.φ, Category.assoc, h, Category.comp_id, Category.id_comp]

theorem conj_sec {S S₂ : Scheme.{0}} {t : SAB H S} {t₂ : SAB H S₂} {r r' : S₂ ⟶ S} {ρ : S ⟶ S} {ρ₂ : S₂ ≅ S₂}
    (m : SABMap t₂ t r) (m' : SABMap t₂ t r') (ν : SABMap t t ρ) (ν₂ : SABMap t₂ t₂ ρ₂.hom)
    (hr : ρ₂.hom ≫ r' = r ≫ ρ) (hφ : ν₂.φ ≫ m'.φ = m.φ ≫ ν.φ)
    {σ σ' : 𝟙_ (Over S₂) ⟶ t₂.G} {τ τ' : 𝟙_ (Over S) ⟶ t.G} (k : ℕ)
    (h₂ : σ'.left ≫ ν₂.φ = ρ₂.hom ≫ σ.left) (hm : (σ' ^ k).left ≫ m.φ = r ≫ τ'.left)
    (h : τ'.left ≫ ν.φ = ρ ≫ τ.left) : (σ ^ k).left ≫ m'.φ = r' ≫ τ.left := by
  have e := OverMove.pow_left_comp ν₂ h₂ k
  have a₁ : ρ₂.hom ≫ (σ ^ k).left ≫ m'.φ = ((σ' ^ k).left ≫ m.φ) ≫ ν.φ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m'.φ) e.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg ((σ' ^ k).left ≫ ·) hφ).trans (Category.assoc _ _ _).symm)))
  have a₂ : (r ≫ τ'.left) ≫ ν.φ = ρ₂.hom ≫ r' ≫ τ.left :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ τ.left) hr.symm).trans (Category.assoc _ _ _))))
  exact (cancel_epi ρ₂.hom).1 (a₁.trans ((congrArg (· ≫ ν.φ) hm).trans a₂))

end ConjLevelMap

open ConjLevelMap in
theorem exists_conj_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.EtaOK → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ≅ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂.hom) (gM gA gM₂ gA₂ : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA → IsLevMove ρ₂.hom ν₂ gM₂ gA₂ → (∀ a, gM₂ a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA₂ a - gA a)) → ∃ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂.hom ≫ r' = d.r ≫ ρ ∧ ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ ∧ DeltaDat.EtaOK { d with r := r', m := m' } := by
  intro E _ _ _ H Dw l Xo c n d hE ρ ν ρ₂ ν₂ gM gA gM₂ gA₂ h h₂ hM hA
  obtain ⟨i, hi⟩ := exists_inv ρ₂ ν₂
  obtain ⟨q, hq⟩ := ObjMaps.exists_sab_comp ν d.m
  obtain ⟨m', hm'⟩ := ObjMaps.exists_sab_comp q i
  have hr : ρ₂.hom ≫ ρ₂.inv ≫ d.r ≫ ρ = d.r ≫ ρ := ρ₂.hom_inv_id_assoc _
  have hφ : ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ := by
    rw [hm', hq, ← Category.assoc, hi, Category.id_comp]
  have eM : ∀ a, Xo.univ.eta (gM₂ a) = Xo.univ.eta (gM a) := fun a => by
    rw [← sub_add_cancel (gM₂ a) (gM a), Xo.univ.eta_add, Xo.univ.eta_ker _ (hM a), _root_.one_mul]
  have eA : ∀ a, Xo.univ.etaA (gA₂ a) = Xo.univ.etaA (gA a) := fun a => by
    obtain ⟨x, hx⟩ := hA a
    rw [← sub_add_cancel (gA₂ a) (gA a), Xo.univ.etaA_add, hx, Xo.univ.etaA_ker, _root_.one_mul]
  refine ⟨_, m', hr, hφ, fun a => ?_, fun a => ?_⟩
  · exact conj_sec d.m m' ν ν₂ hr hφ d.pd (h₂.2.1 a) (hE.1 (gM₂ a)) (by rw [eM]; exact h.2.1 a)
  · exact conj_sec d.m m' ν ν₂ hr hφ (d.l₂.A / l.A) (h₂.2.2 a) (hE.2 (gA₂ a)) (by rw [eA]; exact h.2.2 a)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsConjLevelMapByLevelMovesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_levelMap_by_levelMoves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.EtaOK → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ≅ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂.hom) (gM gA gM₂ gA₂ : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA → IsLevMove ρ₂.hom ν₂ gM₂ gA₂ → (∀ a, gM₂ a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA₂ a - gA a)) → ∃ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂.hom ≫ r' = d.r ≫ ρ ∧ ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ ∧ DeltaDat.EtaOK { d with r := r', m := m' } := by
  first | exact @GlobalTheory.exists_conj_levelMap | exact GlobalTheory.exists_conj_levelMap | (intros; apply GlobalTheory.exists_conj_levelMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenMoveBack
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Jets

open TopologicalSpace in
theorem exists_gen_move_back : ∀ (Y Y' X₁ X₂ W : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂), L₁.IsLB → L₂.IsLB → ∀ (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)), w.IsGen → ∀ (K : Type) [Fintype K] (m : K → (Y' ⟶ Y)) (ε : K → ℤ) (φ₁ : K → (Y' ⟶ X₁)), (∀ k, φ₁ k = m k ≫ f₁) → ∀ (φ₂ : K → (W ⟶ X₂)) (h : Y' ⟶ W), (∀ k, h ≫ φ₂ k = m k ≫ f₂) → ∀ t : LB.Gen (LB.LinComb L₂ φ₂ ε), t.IsGen → ∃ a : LB.Gen (LB.LinComb L₁ φ₁ ε), a.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J₂ : (Z ⟶ X₂) → L₂.ι) (J₁ : (Z ⟶ X₁) → L₁.ι), Good L₂ z J₂ → Good L₁ z J₁ → val t (r ≫ h) z J₂ = (∏ k, isoVal w (r ≫ m k) z (J₂ ((r ≫ m k) ≫ f₂)) (J₁ ((r ≫ m k) ≫ f₁)) ^ ε k) * val a r z J₁ := by
  intro Y Y' X₁ X₂ W L₁ L₂ hL₁ hL₂ f₁ f₂ w hw K _ m ε φ₁ e₁ φ₂ h hc t ht
  classical
  obtain rfl : φ₁ = fun k => m k ≫ f₁ := funext e₁
  let O : (K → L₁.ι) → (K → L₂.ι) → Y'.Opens := fun q p =>
    LB.wchart L₁ (fun k => m k ≫ f₁) q ⊓ LB.wchart L₂ (fun k => m k ≫ f₂) p
  have pt : ∀ k y, φ₂ k (h y) = f₂ (m k y) := fun k y => congrArg (fun q : Y' ⟶ X₂ => q y) (hc k)
  have le1 : ∀ q p k, O q p ≤ m k ⁻¹ᵁ ((L₂.pull f₂).U (fun _ => p k) ⊓ (L₁.pull f₁).U (fun _ => q k)) :=
    fun q p k y hy => ⟨mem_pull.2 (Set.mem_iInter.1 hy.2 k), mem_pull.2 (Set.mem_iInter.1 hy.1 k)⟩
  have le2 : ∀ q p, O q p ≤ h ⁻¹ᵁ LB.wchart L₂ φ₂ p := fun q p y hy => Set.mem_iInter.2 fun k => by
    show φ₂ k (h y) ∈ L₂.U (p k)
    rw [pt]; exact Set.mem_iInter.1 hy.2 k
  let v : ∀ q p, Γ(Y', O q p)ˣ := fun q p =>
    (∏ k, res (le1 q p k) (pullU (m k) _ (w.s (fun _ => p k, fun _ => q k))) ^ ε k)⁻¹ *
      res (le2 q p) (pullU h _ (t.s p))
  have germ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (O q p) (v q p) =
        (∏ k, isoVal w (r ≫ m k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L₂ φ₂ p) (t.s p) := by
    intro Z r z q p hz
    have m2 := le2 q p hz
    show gm r z (O q p) ((∏ k, _)⁻¹ * _) = _
    rw [map_mul, map_inv, map_prod]
    refine congrArg₂ (· * ·) (congrArg (·⁻¹) (Finset.prod_congr rfl fun k _ => ?_))
      ((gm_res r z (le2 q p) hz _).trans (gm_pull r h z _ m2 _))
    have m1 := le1 q p k hz
    exact (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z (le1 q p k) hz _).trans
      (gm_pull r (m k) z _ m1 _)))
  have memO : ∀ q (y : Y'), y ∈ LB.wchart L₁ (fun k => m k ≫ f₁) q → ∃ p, y ∈ O q p := fun q y hy => by
    choose p hp using fun k => exists_chart hL₂ (f₂ (m k y))
    exact ⟨p, hy, Set.mem_iInter.2 fun k => hp k⟩
  have glue : ∀ q, ∃ s : Γ(Y', LB.wchart L₁ (fun k => m k ≫ f₁) q)ˣ,
      ∀ p, res (inf_le_left : O q p ≤ _) s = v q p := by
    intro q
    refine glue_unit _ (O q) (fun p => inf_le_left) (fun y hy => ?_) (v q) fun p p' y hy => ?_
    · obtain ⟨p, hp⟩ := memO q y hy
      exact Opens.mem_iSup.2 ⟨p, hp⟩
    · rw [germ _ _ y q p hy.1, germ _ _ y q p' hy.2]
      have hp : ∀ k, f₂ (m k y) ∈ L₂.U (p k) := fun k => Set.mem_iInter.1 hy.1.2 k
      have hp' : ∀ k, f₂ (m k y) ∈ L₂.U (p' k) := fun k => Set.mem_iInter.1 hy.2.2 k
      have hq : ∀ k, f₁ (m k y) ∈ L₁.U (q k) := fun k => Set.mem_iInter.1 hy.1.1 k
      have e1 : ∀ k, isoVal w (𝟙 Y' ≫ m k) y (p k) (q k) =
          gm (m k ≫ f₂) y _ (L₂.g (p k) (p' k)) * isoVal w (𝟙 Y' ≫ m k) y (p' k) (q k) := fun k => by
        rw [Category.id_comp, GlobalTheory.FieldBaseChange.isoVal_trans hw (m k) y (hp k) (hp' k) (hq k) (hq k),
          gm_self hL₁ (m k ≫ f₁) y (hq k), inv_one, _root_.mul_one]
      have e2 : trF φ₂ ε (𝟙 Y' ≫ h) y p p' = ∏ k, gm (m k ≫ f₂) y _ (L₂.g (p k) (p' k)) ^ ε k :=
        Finset.prod_congr rfl fun k _ => by rw [Category.id_comp, hc k]
      rw [gen_trans ht (𝟙 Y' ≫ h) y (le2 q p hy.1) (le2 q p' hy.2), e2]
      simp only [e1, mul_zpow, Finset.prod_mul_distrib, mul_inv_rev]
      rw [_root_.mul_assoc, inv_mul_cancel_left]
  choose s hs using glue
  have vals : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) q p, r z ∈ O q p →
      gm r z (LB.wchart L₁ (fun k => m k ≫ f₁) q) (s q) =
        (∏ k, isoVal w (r ≫ m k) z (p k) (q k) ^ ε k)⁻¹ * gm (r ≫ h) z (LB.wchart L₂ φ₂ p) (t.s p) := by
    intro Z r z q p hz
    rw [← gm_res r z (inf_le_left : O q p ≤ _) hz, hs q p, germ Z r z q p hz]
  refine ⟨⟨s⟩, fun q q' => unit_ext fun y hy => ?_, fun Z r z J₂ J₁ hJ₂ hJ₁ => ?_⟩
  · have hq : ∀ k, f₁ (m k y) ∈ L₁.U (q k) := fun k => Set.mem_iInter.1 hy.1 k
    have hq' : ∀ k, f₁ (m k y) ∈ L₁.U (q' k) := fun k => Set.mem_iInter.1 hy.2 k
    choose p hp using fun k => exists_chart hL₂ (f₂ (m k y))
    have m0 : y ∈ O q p := ⟨hy.1, Set.mem_iInter.2 fun k => hp k⟩
    have m' : y ∈ O q' p := ⟨hy.2, Set.mem_iInter.2 fun k => hp k⟩
    rw [gm_res _ y _ hy, map_mul, gm_res _ y _ hy]
    show gm (𝟙 Y') y (LB.wchart L₁ (fun k => m k ≫ f₁) q) (s q) =
      gm (𝟙 Y') y (LB.wchart L₁ (fun k => m k ≫ f₁) q ⊓ LB.wchart L₁ (fun k => m k ≫ f₁) q')
      ((LB.LinComb L₁ (fun k => m k ≫ f₁) ε).g q q') * gm (𝟙 Y') y (LB.wchart L₁ (fun k => m k ≫ f₁) q') (s q')
    rw [gm_linComb L₁ (fun k => m k ≫ f₁) ε (𝟙 Y') y q q' hy.1 hy.2, vals _ _ y q p m0, vals _ _ y q' p m']
    have e3 : ∀ k, isoVal w (𝟙 Y' ≫ m k) y (p k) (q k) =
        (gm (𝟙 Y' ≫ m k ≫ f₁) y _ (L₁.g (q k) (q' k)))⁻¹ * isoVal w (𝟙 Y' ≫ m k) y (p k) (q' k) := fun k => by
      rw [Category.id_comp, Category.id_comp,
        GlobalTheory.FieldBaseChange.isoVal_trans hw (m k) y (hp k) (hp k) (hq k) (hq' k),
        gm_self hL₂ (m k ≫ f₂) y (hp k), _root_.one_mul]
    simp only [e3, mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, mul_inv_rev, inv_inv]
    exact (congrArg (· * _) (mul_comm _ _)).trans (_root_.mul_assoc _ _ _)
  · have m0 : r z ∈ O (fun k => J₁ ((r ≫ m k) ≫ f₁)) (fun k => J₂ ((r ≫ m k) ≫ f₂)) :=
      ⟨Set.mem_iInter.2 fun k => hJ₁ ((r ≫ m k) ≫ f₁), Set.mem_iInter.2 fun k => hJ₂ ((r ≫ m k) ≫ f₂)⟩
    rw [val_of t (r ≫ h) z J₂ (fun k => J₂ ((r ≫ m k) ≫ f₂))
        (fun k => by rw [Category.assoc, hc k, Category.assoc]),
      val_of _ r z J₁ (fun k => J₁ ((r ≫ m k) ≫ f₁)) (fun k => by rw [Category.assoc])]
    show _ = _ * gm r z (LB.wchart L₁ (fun k => m k ≫ f₁) _) (s _)
    rw [vals Z r z _ _ m0, mul_inv_cancel_left]

end GlobalTheory.Jets
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSepDiscr
open NumberField TensorProduct

namespace GlobalTheory.IntSepElement

variable (E : Type) [Field E] [NumberField E]

open scoped Classical in
noncomputable def dualB : Module.Basis (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (integralBasis E)

theorem sum_dualB (z : E) :
    ∑ i, Algebra.trace ℚ E (z * integralBasis E i) • dualB E i = z := by
  classical
  conv_rhs => rw [← (dualB E).sum_repr z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dualB, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]

theorem repr_eq_trace (z : E) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (integralBasis E).repr z i = Algebra.trace ℚ E (dualB E i * z) := by
  classical
  have h : ∀ j, Algebra.trace ℚ E (dualB E i * integralBasis E j) = if j = i then 1 else 0 := by
    intro j
    have h := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ E)
      (integralBasis E) i j
    rw [Algebra.traceForm_apply] at h
    convert h
    rfl
  conv_rhs => rw [← (integralBasis E).sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  simp_rw [mul_smul_comm, LinearMap.map_smul, h, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

theorem trace_dualB_int (c : 𝓞 E) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (dualB E i * (c : E)) = ((RingOfIntegers.basis E).repr c i : ℚ) := by
  rw [← repr_eq_trace]
  exact integralBasis_repr_apply E c i

theorem sum_mul_dualB : ∑ i, integralBasis E i * dualB E i = 1 := by
  classical
  have key : ∀ z : E, Algebra.trace ℚ E ((∑ i, integralBasis E i * dualB E i) * z) = Algebra.trace ℚ E z := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum, Algebra.trace_eq_matrix_trace (integralBasis E) z, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, repr_eq_trace]
    congr 1
    ring
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate ℚ E).1 _ fun z => ?_
  rw [Algebra.traceForm_apply, sub_mul, map_sub, key, one_mul, sub_self]

theorem discr_mul_dualB (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∃ y : 𝓞 E, (y : E) = ((discr E : ℤ) : E) * dualB E i := by
  classical
  have hmem : dualB E i ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    rw [Submodule.mem_one] at ha
    obtain ⟨a, rfl⟩ := ha
    refine ⟨(RingOfIntegers.basis E).repr a i, ?_⟩
    rw [Algebra.traceForm_apply]
    exact (trace_dualB_int E a i).symm
  have := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) (b := integralBasis E) (fun i => by
      rw [integralBasis_apply]; exact (RingOfIntegers.isIntegral_coe _)) (Submodule.one_le.mp le_rfl) hmem
  rw [← coe_discr, Algebra.smul_def, mul_one, map_intCast] at this
  exact ⟨⟨_, this⟩, rfl⟩

theorem exists_sep_discr :
    ∃ x y : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → 𝓞 E, ∑ i, x i * y i = ((discr E : ℤ) : 𝓞 E) ∧
      ∀ a : 𝓞 E, (∑ i, (a * x i) ⊗ₜ[ℤ] y i : 𝓞 E ⊗[ℤ] 𝓞 E) = ∑ i, x i ⊗ₜ[ℤ] (a * y i) := by
  choose y hy using discr_mul_dualB E
  have hy' : ∀ i, algebraMap (𝓞 E) E (y i) = ((discr E : ℤ) : E) * dualB E i := hy
  refine ⟨RingOfIntegers.basis E, y, ?_, fun a => ?_⟩
  · apply RingOfIntegers.coe_injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_intCast]
    simp only [map_mul, hy', ← integralBasis_apply]
    calc ∑ i, integralBasis E i * (((discr E : ℤ) : E) * dualB E i)
        = ((discr E : ℤ) : E) * ∑ i, integralBasis E i * dualB E i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by rw [sum_mul_dualB, mul_one]
  · have h1 : ∀ k, ∑ i, (RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E i) k • y i = a * y k := by
      intro k
      apply RingOfIntegers.coe_injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_mul, hy']
      have h2 := sum_dualB E (dualB E k * algebraMap (𝓞 E) E a)
      calc ∑ i, algebraMap (𝓞 E) E ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E i) k • y i)
          = ((discr E : ℤ) : E) * ∑ i, Algebra.trace ℚ E
              (dualB E k * algebraMap (𝓞 E) E a * integralBasis E i) • dualB E i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            have h3 := trace_dualB_int E (a * RingOfIntegers.basis E i) k
            have h4 : ((a * RingOfIntegers.basis E i : 𝓞 E) : E) = algebraMap (𝓞 E) E a * integralBasis E i := by
              rw [integralBasis_apply, ← map_mul]
            rw [h4, ← mul_assoc] at h3
            rw [h3, map_zsmul, hy', Int.cast_smul_eq_zsmul, mul_smul_comm]
        _ = _ := by rw [h2]; ring
    calc (∑ i, (a * RingOfIntegers.basis E i) ⊗ₜ[ℤ] y i : 𝓞 E ⊗[ℤ] 𝓞 E)
        = ∑ i, ∑ k, RingOfIntegers.basis E k ⊗ₜ[ℤ]
            ((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E i) k • y i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E i)]
          rw [TensorProduct.sum_tmul]
          exact Finset.sum_congr rfl fun k _ => TensorProduct.smul_tmul _ _ _
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => by rw [← TensorProduct.tmul_sum, h1]

end GlobalTheory.IntSepElement
end
