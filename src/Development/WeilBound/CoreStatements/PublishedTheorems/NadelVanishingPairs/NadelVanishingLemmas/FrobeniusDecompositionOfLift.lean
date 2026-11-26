module

public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SplittingLocalIntegrality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowNormMulSeminormSliceRLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryOfISupIntertwinerRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MemChartFormsIff
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierProjectionProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSymplecticHomOfIndefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionModuleStructure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFrobeniusLiftSmulLogCoordinateWedge
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFrobeniusLiftSmulLogCoordinateWedge
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem cartierMap_smul_logWedge : ∀ (K : Type) [Field K] (p : ℕ) (n : ℕ) (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K),
    IsCartierMap p x γ → ∀ (c : K) (I : Finset (Fin n)), γ (c • logWedge x I) = c ^ p • logWedge x I := by
  intro K _ p n x γ hγ c I
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hγ.1]
  congr 1
  unfold logWedge
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact hγ.2 i

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFrobeniusLiftSmulLogCoordinateWedgeStatement
open GlobalTheory GlobalTheory.LogDR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logFrobeniusLift_smul_logCoordinateWedge : ∀ (K : Type) [Field K] (p : ℕ) (n : ℕ) (x : Fin n → Kˣ) (γ : abelian₂ K →+* abelian₂ K), IsCartierMap p x γ → ∀ (c : K) (I : Finset (Fin n)), γ (c • logWedge x I) = c ^ p • logWedge x I := by
  first | exact @GlobalTheory.cartierMap_smul_logWedge | exact GlobalTheory.cartierMap_smul_logWedge | (intros; apply GlobalTheory.cartierMap_smul_logWedge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGamma
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

namespace FrobTwist

def Tw (K V : Type) [CommRing K] [AddCommGroup V] [Module K V] : Type := ExteriorAlgebra K V

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

instance : Ring (Tw K V) := inferInstanceAs (Ring (ExteriorAlgebra K V))

abbrev twAlg (p : ℕ) [Fact p.Prime] [CharP K p] : Algebra K (Tw K V) :=
  RingHom.toAlgebra' ((algebraMap K (ExteriorAlgebra K V)).comp (frobenius K p))
    (fun c x => Algebra.commutes (R := K) (A := ExteriorAlgebra K V) _ x)

end FrobTwist


open FrobTwist in
theorem exists_isGamma {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] (p : ℕ)
    [Fact p.Prime] [CharP K p] (f : V →+ V) (hf : ∀ (c : K) v, f (c • v) = c ^ p • f v) :
    ∃ γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V, IsGamma p f γ := by
  letI : Algebra K (Tw K V) := twAlg p
  let g : V →ₗ[K] Tw K V :=
    { toFun := fun v => (ExteriorAlgebra.ι K (f v) : ExteriorAlgebra K V)
      map_add' := fun v w => by
        show ExteriorAlgebra.ι K (f (v + w)) = ExteriorAlgebra.ι K (f v) + ExteriorAlgebra.ι K (f w)
        rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun c v => by
        have h1 : ExteriorAlgebra.ι K (f (c • v)) =
            algebraMap K (ExteriorAlgebra K V) (c ^ p) * ExteriorAlgebra.ι K (f v) := by
          rw [hf, map_smul, Algebra.smul_def]
        exact h1 }
  have hg : ∀ v, g v * g v = 0 := fun v => ExteriorAlgebra.ι_sq_zero (R := K) (f v)
  let Γ : ExteriorAlgebra K V →ₐ[K] Tw K V := ExteriorAlgebra.lift K ⟨g, hg⟩
  refine ⟨(Γ.toRingHom : ExteriorAlgebra K V →+* ExteriorAlgebra K V), ?_, ?_⟩
  · intro c
    have := Γ.commutes c
    exact this
  · intro v
    have := ExteriorAlgebra.lift_ι_apply K (A := Tw K V) g hg v
    exact this

end GlobalTheory.DI
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedFrobLogForm
set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem divided_frob_logForm : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (f : ι → Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (h : ι → ι → Ω[K⁄ℤ] →+ K) (s : Finset ι) (A : Subring K) (g : K), (∀ i, IsF p π (F i) (f i)) → (∀ i j, IsH p π (F i) (F j) (h i j)) → LogLift p π F s (A : Set K) g → (∀ i ∈ s, ∃ w ∈ A, g ≠ 0 → f i (g⁻¹ • KaehlerDifferential.D ℤ K g) = g⁻¹ • KaehlerDifferential.D ℤ K g + KaehlerDifferential.D ℤ K w) ∧ ∀ i ∈ s, ∀ j ∈ s, h i j (g⁻¹ • KaehlerDifferential.D ℤ K g) ∈ A := by
  intro K Kt _ _ p hp _ π ι F f h s A g hF hH hL
  obtain ⟨z, hz, hw⟩ := hL
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hDp : KaehlerDifferential.D ℤ K (g ^ p) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  have e2 : ∀ hg : g ≠ 0, g⁻¹ ^ p * g ^ p = 1 := fun hg => by
    rw [← mul_pow, inv_mul_cancel₀ hg, one_pow]
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · obtain ⟨w, hwA, hFw⟩ := hw i hi
    refine ⟨π w, hwA, fun hg => ?_⟩
    have key := (hF i).2 z (z ^ p * w) (by rw [hFw]; ring)
    rw [map_mul, map_pow, hz] at key
    have e1 : g⁻¹ ^ p * g ^ (p - 1) = g⁻¹ := by
      obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm (g⁻¹ ^ n), mul_assoc, ← mul_pow, inv_mul_cancel₀ hg,
        one_pow, mul_one]
    rw [(hF i).1, key, Derivation.leibniz, hDp, smul_zero, add_zero, smul_add, smul_smul, smul_smul, e1,
      e2 hg, one_smul]
  · obtain ⟨wi, hwiA, hFi⟩ := hw i hi
    obtain ⟨wj, hwjA, hFj⟩ := hw j hj
    have key := (hH i j).2 z (z ^ p * (wj - wi)) (by rw [hFj, hFi]; ring)
    rw [map_mul, map_pow, map_sub, hz] at key
    rw [(hH i j).1, key]
    by_cases hg : g = 0
    · subst hg
      simp [hp0]
    · rw [← mul_assoc, e2 hg, one_mul]
      exact A.sub_mem hwjA hwiA

end GlobalTheory.DI
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierOperatorLogSections
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogCartierRoundingFamily
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EulerContractionChartForms
open GlobalTheory GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.euler_contraction_chart_forms : ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K), (∀ j, (x j : K) ∈ A) → IsEulerContraction x i θ → (∀ q, ∀ η ∈ chartForms A x J t (q + 1), θ η ∈ chartForms A x J t q) ∧ ∀ η ∈ chartForms A x J t 0, θ η = 0 := by
  first | exact @_root_.GlobalTheory.LogDR.chartForms_stable_euler | exact _root_.GlobalTheory.LogDR.chartForms_stable_euler | (intros; apply _root_.GlobalTheory.LogDR.chartForms_stable_euler <;> assumption)
end

set_option autoImplicit false

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem logCartier_rounding_family : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ)
    (x : Fin n → Kˣ) (J : Finset (Fin n)) (γ : abelian₂ K →+* abelian₂ K) (Y : Type) [Nonempty Y] (A : Y → Subring K)
    (t : Y → Kˣ) (r : Y → Fin n → ℕ), (∀ y, GlobalTheory.LogDR.AlgChart (A y) x) → (∀ y j, r y j < p) → IsCartierMap p x γ →
    ∀ (a : ℕ) (η : abelian₂ K), (∀ y, η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) a) →
    extD K η = 0 → ∃ ζ ξ : abelian₂ K, (∀ y, ζ ∈ chartForms (A y) x J (t y) a) ∧
      (∀ y q, q + 1 = a → ξ ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q) ∧
      (a = 0 → ξ = 0) ∧ η = γ ζ + extD K ξ := by
  intro K _ p _ _ n x J γ Y _ A t r hA hr hγ a η hη hd
  obtain ⟨y0⟩ := ‹Nonempty Y›
  have hc : IsCoord x := (hA y0).coord
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨h, Q, π, hhom, hQw, hπ, -, -, hstab⟩ := GlobalTheory.T.cartier_projection_properties K p n x hc
  have hT : ∀ y, (∀ q, ∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) (q + 1),
        h η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q) ∧
      (∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) 0, h η = 0) ∧
      ∀ q, ∀ η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q,
        Q η ∈ chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q := by
    intro y
    exact hstab (fun q => chartForms (A y) x J (t y ^ p * ∏ j ∈ J, x j ^ r y j) q)
      (GlobalTheory.T.chart_forms_differential_closed K p (A y) n x J (t y) (r y) (hA y))
      (fun i θ hθ => GlobalTheory.T.euler_contraction_chart_forms K (A y) n x J _ i θ (hA y).mem hθ)
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.logCoordinateWedge_linearIndependent_span_eq_top K n x hc
  obtain ⟨c, hcη⟩ : ∃ c : Finset (Fin n) → K, ∑ I, c I • logWedge x I = η :=
    (Submodule.mem_span_range_iff_exists_fun K).mp (hsp ▸ Submodule.mem_top)
  choose g hg using fun I => hπ (c I)
  have hQη : Q η = ∑ I, g I ^ p • logWedge x I := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hcη, map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hQw, hg]
  refine ⟨∑ I, g I • logWedge x I, h η, ?_, ?_, ?_, ?_⟩
  · intro y
    have hm := (hT y).2.2 a η (hη y)
    rw [GlobalTheory.T.mem_chart_forms_iff] at hm
    obtain ⟨c', hc'0, hc'A, hc'eq⟩ := hm
    have heq : ∀ I, c' I = g I ^ p := by
      have h0 : ∑ I, (c' I - g I ^ p) • logWedge x I = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hc'eq, ← hQη, sub_self]
      intro I
      exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 I)
    rw [GlobalTheory.T.mem_chart_forms_iff]
    refine ⟨g, ?_, ?_, rfl⟩
    · intro I hI
      have h1 := hc'0 I hI
      rw [heq] at h1
      exact (pow_eq_zero_iff hp.ne').mp h1
    · intro I
      have h1 := hc'A I
      rw [heq] at h1
      exact GlobalTheory.T.mem_subring_of_pthPower_twisted_monomial_mem K p (A y) n x I J (t y) (r y) (g I) hp (hA y) (hr y) h1
  · intro y q hq
    subst hq
    exact (hT y).1 q η (hη y)
  · intro ha
    subst ha
    exact (hT y0).2.1 η (hη y0)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [GlobalTheory.T.logFrobeniusLift_smul_logCoordinateWedge K p n x γ hγ]
    rw [← hQη]
    have h2 := hhom η
    rw [hd, map_zero, add_zero] at h2
    exact sub_eq_iff_eq_add'.mp h2

end GlobalTheory
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierMapEqExtDImpEqZero
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem cartierMap_eq_extD_imp_eq_zero :
    ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) (x : Fin n → Kˣ)
      (γ : abelian₂ K →+* abelian₂ K), IsCoord x → IsCartierMap p x γ → ∀ ζ ξ : abelian₂ K, γ ζ = extD K ξ → ζ = 0 := by
  intro K _ p _ _ n x γ hx hγ ζ ξ hζ
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.logCoordinateWedge_linearIndependent_span_eq_top K n x hx
  have hmem : ζ ∈ Submodule.span K (Set.range (logWedge x)) := hsp ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  obtain ⟨-, Q, π, -, hQ, -, hπ, hQd, -⟩ := GlobalTheory.T.cartier_projection_properties K p n x hx
  have hγs : γ (∑ I, c I • logWedge x I) = ∑ I, (c I ^ p) • logWedge x I := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun I _ => GlobalTheory.T.logFrobeniusLift_smul_logCoordinateWedge K p n x γ hγ (c I) I
  have hfix : Q (γ (∑ I, c I • logWedge x I)) = γ (∑ I, c I • logWedge x I) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hγs, map_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hQ, hπ]
  have h0 : ∑ I, (c I ^ p) • logWedge x I = 0 := by
    rw [← hγs, ← hfix, hζ, hQd]
  have hc : ∀ I, c I ^ p = 0 := fun I =>
    (Fintype.linearIndependent_iff.1 hli) (fun I => c I ^ p) h0 I
  have hc' : ∀ I, c I = 0 := fun I =>
    (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).1 (hc I)
  simp [hc']

end GlobalTheory
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierOperatorLogSections
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

namespace GlobalTheory

theorem mem_logSec_iff {X : Scheme.{0}} [IsIntegral X] {Z : Set X} {G : CartierDiv X} {a : ℕ}
    {U : X.Opens} {η : abelian₂ X.functionField} : η ∈ logSec Z G a U ↔ ∀ y ∈ U, η ∈ logAt Z G a y := by
  simp only [logSec, latSec, AddSubgroup.mem_iInf]

theorem mem_inter_of_forall {X : Scheme.{0}} [IsIntegral X] {ι : Type} (U : ι → X.Opens) (s : Finset ι)
    (y : X) (h : ∀ i ∈ s, y ∈ U i) : y ∈ inter U s := by
  classical
  unfold inter
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.inf_insert]
    exact ⟨h i (Finset.mem_insert_self i s), ih fun k hk => h k (Finset.mem_insert_of_mem hk)⟩

private theorem spanForms_le_of_mem_closure_smul {K : Type} [Field K] (M : Set K) (A : Subring K)
    (hM : ∀ c ∈ M, ∀ b ∈ A, c * b ∈ M) (H H' : Set Ω[K⁄ℤ])
    (hH : ∀ h ∈ H, h ∈ AddSubgroup.closure {w | ∃ b ∈ A, ∃ h' ∈ H', w = b • h'}) :
    ∀ a, spanForms M H a ≤ spanForms M H' a := by
  have key : ∀ a (c : K), c ∈ M → ∀ v : Fin a → Ω[K⁄ℤ],
      (∀ i, v i ∈ AddSubgroup.closure {w | ∃ b ∈ A, ∃ h' ∈ H', w = b • h'}) →
      c • ExteriorAlgebra.ιMulti K a v ∈ spanForms M H' a := by
    intro a
    induction a with
    | zero =>
      intro c hc v _
      exact AddSubgroup.subset_closure ⟨c, hc, v, fun i => i.elim0, rfl⟩
    | succ a ih =>
      intro c hc v hv
      have hpre : ∀ h' ∈ H', ∀ z ∈ spanForms M H' a,
          ExteriorAlgebra.ι K h' * z ∈ spanForms M H' (a + 1) := by
        intro h' hh' z hz
        induction hz using AddSubgroup.closure_induction with
        | mem z hz =>
          obtain ⟨c', hc', v', hv', rfl⟩ := hz
          apply AddSubgroup.subset_closure
          refine ⟨c', hc', Fin.cons h' v', ?_, ?_⟩
          · intro i
            refine Fin.cases hh' (fun k => ?_) i
            simpa using hv' k
          · rw [ExteriorAlgebra.ιMulti_succ_apply, mul_smul_comm]
            rfl
        | zero => simp
        | add z1 z2 _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
        | neg z _ h1 => rw [mul_neg]; exact neg_mem h1
      have claim : ∀ w ∈ AddSubgroup.closure {w | ∃ b ∈ A, ∃ h' ∈ H', w = b • h'}, ∀ c ∈ M,
          c • (ExteriorAlgebra.ι K w * ExteriorAlgebra.ιMulti K a (Matrix.vecTail v)) ∈
            spanForms M H' (a + 1) := by
        intro w hw
        induction hw using AddSubgroup.closure_induction with
        | mem w hw =>
          obtain ⟨b, hb, h', hh', rfl⟩ := hw
          intro c hc
          rw [map_smul, smul_mul_assoc, smul_smul, ← mul_smul_comm]
          exact hpre h' hh' _ (ih (c * b) (hM c hc b hb) _ (fun i => hv i.succ))
        | zero => intro c _; simp
        | add w1 w2 _ _ h1 h2 =>
          intro c hc
          rw [map_add (f := _), add_mul, smul_add]
          exact add_mem (h1 c hc) (h2 c hc)
        | neg w _ h1 =>
          intro c hc
          rw [map_neg, neg_mul, smul_neg]
          exact neg_mem (h1 c hc)
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      exact claim _ (hv 0) c hc
  intro a
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨c, hc, v, hv, rfl⟩
  exact key a c hc v (fun i => hH _ (hv i))

private theorem dlog_mul' {K : Type} [Field K] (u v : Kˣ) : dlog (u * v) = dlog u + dlog v := by
  simp only [dlog, dK, Units.val_mul, Derivation.leibniz, smul_add, smul_smul]
  rw [add_comm]
  congr 1 <;> congr 1 <;> simp only [Units.val_inv_eq_inv_val, Units.val_mul, mul_inv_rev] <;> field_simp

private theorem dlog_one' {K : Type} [Field K] : dlog (1 : Kˣ) = 0 := by
  simp [dlog, dK]

private theorem dlog_pow' {K : Type} [Field K] (u : Kˣ) (k : ℕ) : dlog (u ^ k) = k • dlog u := by
  induction k with
  | zero => simp [dlog_one']
  | succ k ih => rw [pow_succ, dlog_mul', ih, succ_nsmul]

private theorem dlog_inv' {K : Type} [Field K] (u : Kˣ) : dlog u⁻¹ = - dlog u := by
  have h := dlog_mul' u u⁻¹
  rw [mul_inv_cancel, dlog_one'] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

private theorem dlog_zpow' {K : Type} [Field K] (u : Kˣ) (m : ℤ) : dlog (u ^ m) = m • dlog u := by
  cases m with
  | ofNat k => rw [Int.ofNat_eq_coe, zpow_natCast, dlog_pow', natCast_zsmul]
  | negSucc k => rw [zpow_negSucc, dlog_inv', dlog_pow', negSucc_zsmul]

private theorem dlog_prod_zpow {K : Type} [Field K] {n : ℕ} (s : Finset (Fin n)) (x : Fin n → Kˣ) (m : Fin n → ℤ) :
    dlog (∏ j ∈ s, x j ^ m j) = ∑ j ∈ s, m j • dlog (x j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dlog_one']
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, dlog_mul', dlog_zpow', ih]

private theorem dK_units_eq_smul_dlog {K : Type} [Field K] (u : Kˣ) : dK (u : K) = (u : K) • dlog u := by
  simp [dlog, smul_smul]

private theorem logUnit_of_unitAt {X : Scheme.{0}} [IsIntegral X] (Z : Set X) {y : X}
    {g : X.functionFieldˣ} (h : UnitAt y (g : X.functionField)) : LogUnit Z y g := by
  obtain ⟨V, hyV, hV⟩ := h.exists_nhds
  intro z hz _
  exact hV z (hz.mem_open V.isOpen hyV)

private theorem exists_unitAt_dK_eq_smul_dlog_of_regAt {X : Scheme.{0}} [IsIntegral X] {y : X} {a : X.functionField} (ha : RegAt y a) :
    ∃ u : X.functionFieldˣ, UnitAt y (u : X.functionField) ∧ ∃ b, RegAt y b ∧ dK a = b • dlog u := by
  obtain ⟨s, rfl⟩ := ha
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self s with hs | hs
  · refine ⟨(hs.map (algebraMap _ X.functionField)).unit, ⟨s, hs, rfl⟩, _, ⟨s, rfl⟩, ?_⟩
    have h := dK_units_eq_smul_dlog (hs.map (algebraMap _ X.functionField)).unit
    rw [IsUnit.unit_spec] at h
    exact h
  · refine ⟨(hs.map (algebraMap _ X.functionField)).unit, ⟨1 - s, hs, rfl⟩, _, ⟨-(1 - s), rfl⟩, ?_⟩
    have h := dK_units_eq_smul_dlog (hs.map (algebraMap _ X.functionField)).unit
    rw [IsUnit.unit_spec] at h
    rw [map_neg, neg_smul, ← h]
    simp [dK, map_sub]

private theorem logAt_le_chartForms_of_isLogChart {X : Scheme.{0}} [IsIntegral X] {Z : Set X} {U : X.Opens} {n : ℕ}
    {x : Fin n → X.functionFieldˣ} {J : Finset (Fin n)} (hc : IsLogChart Z U x J) {y : X} (hy : y ∈ U)
    {D : CartierDiv X} {t : X.functionFieldˣ} (ht : D.IsEqn y t) (a : ℕ) :
    logAt Z D a y ≤ chartForms (locRing y) x J t a := by
  have hM : {c : X.functionField | D.RegularAt y c} = {c | c * (t : X.functionField) ∈ locRing y} :=
    Set.ext fun c => (ht.regularAt_iff).trans mem_locRing.symm
  show spanForms {c | D.RegularAt y c} _ a ≤ spanForms {c | c * (t : X.functionField) ∈ locRing y} _ a
  rw [hM]
  refine spanForms_le_of_mem_closure_smul _ (locRing y) (fun c hc b hb => ?_) _ _ ?_ a
  · show c * b * (t : X.functionField) ∈ locRing y
    rw [mul_right_comm]
    exact (locRing y).mul_mem hc hb
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨u, m, hu, rfl⟩ := (hc.logUnit y hy g).1 hg
  have hch := hc.chart y hy
  have hfr : ∀ k, ∀ b ∈ locRing y, b • frame x J k ∈ AddSubgroup.closure
      {w : Ω[X.functionField⁄ℤ] | ∃ b ∈ locRing y, ∃ h' ∈ Set.range (frame x J), w = b • h'} :=
    fun k b hb => AddSubgroup.subset_closure ⟨b, hb, _, ⟨k, rfl⟩, rfl⟩
  have hdK : ∀ k, ∀ b ∈ locRing y, b • dK (x k : X.functionField) ∈ AddSubgroup.closure
      {w : Ω[X.functionField⁄ℤ] | ∃ b ∈ locRing y, ∃ h' ∈ Set.range (frame x J), w = b • h'} := by
    intro k b hb
    by_cases hk : k ∈ J
    · have h1 : dK (x k : X.functionField) = (x k : X.functionField) • frame x J k := by
        rw [frame, if_pos hk, dK_units_eq_smul_dlog]
      rw [h1, smul_smul]
      exact hfr k _ ((locRing y).mul_mem hb (hch.mem k))
    · have h1 : dK (x k : X.functionField) = frame x J k := by rw [frame, if_neg hk]
      rw [h1]
      exact hfr k b hb
  rw [dlog_mul', dlog_prod_zpow]
  refine add_mem ?_ (sum_mem fun k hk => zsmul_mem ?_ _)
  · obtain ⟨a1, _, ha1⟩ := hu.inv
    obtain ⟨a0, _, ha0⟩ := hu
    have huA : (u : X.functionField) ∈ locRing y := mem_locRing.2 ⟨a0, ha0⟩
    have huiA : ((u⁻¹ : X.functionFieldˣ) : X.functionField) ∈ locRing y := by
      rw [Units.val_inv_eq_inv_val]
      exact mem_locRing.2 ⟨a1, ha1⟩
    obtain ⟨cf, hcf, hdu⟩ := hch.deriv _ huA
    rw [dlog, hdu, Finset.smul_sum]
    exact sum_mem fun k _ => by
      rw [smul_smul]
      exact hdK k _ ((locRing y).mul_mem huiA (hcf k))
  · have h1 : dlog (x k) = (1 : X.functionField) • frame x J k := by rw [frame, if_pos hk, one_smul]
    rw [h1]
    exact hfr k 1 (locRing y).one_mem

private theorem chartForms_le_logAt_of_isLogChart {X : Scheme.{0}} [IsIntegral X] {Z : Set X} {U : X.Opens} {n : ℕ}
    {x : Fin n → X.functionFieldˣ} {J : Finset (Fin n)} (hc : IsLogChart Z U x J) {y : X} (hy : y ∈ U)
    {D : CartierDiv X} {t : X.functionFieldˣ} (ht : D.IsEqn y t) (a : ℕ) :
    chartForms (locRing y) x J t a ≤ logAt Z D a y := by
  classical
  have hM : {c : X.functionField | D.RegularAt y c} = {c | c * (t : X.functionField) ∈ locRing y} :=
    Set.ext fun c => (ht.regularAt_iff).trans mem_locRing.symm
  show spanForms {c | c * (t : X.functionField) ∈ locRing y} _ a ≤ spanForms {c | D.RegularAt y c} _ a
  rw [hM]
  refine spanForms_le_of_mem_closure_smul _ (locRing y) (fun c hc b hb => ?_) _ _ ?_ a
  · show c * b * (t : X.functionField) ∈ locRing y
    rw [mul_right_comm]
    exact (locRing y).mul_mem hc hb
  rintro _ ⟨k, rfl⟩
  by_cases hk : k ∈ J
  · have hlu : LogUnit Z y (x k) := by
      refine (hc.logUnit y hy (x k)).2 ⟨1, fun i => if i = k then 1 else 0, ⟨1, isUnit_one, by simp⟩, ?_⟩
      rw [one_mul, Finset.prod_eq_single k (fun b _ hb => by simp [hb]) (fun h => absurd hk h)]
      simp
    rw [frame, if_pos hk, ← one_smul X.functionField (dlog (x k))]
    exact AddSubgroup.subset_closure ⟨1, (locRing y).one_mem, _, ⟨x k, hlu, rfl⟩, rfl⟩
  · rw [frame, if_neg hk]
    obtain ⟨u, hu, b, hb, hd⟩ := exists_unitAt_dK_eq_smul_dlog_of_regAt (mem_locRing.1 ((hc.chart y hy).mem k))
    rw [hd]
    exact AddSubgroup.subset_closure ⟨b, mem_locRing.2 hb, _, ⟨u, logUnit_of_unitAt Z hu, rfl⟩, rfl⟩

private theorem isEqn_smul_add_sum_smul {X : Scheme.{0}} [IsIntegral X] {C : Type} [Fintype C] (E : C → CartierDiv X)
    (G : CartierDiv X) (r : C → ℕ) (p : ℕ) {n : ℕ} (x : Fin n → X.functionFieldˣ) (J : Finset (Fin n))
    (e : C → Option (Fin n)) (hJ : ∀ j, j ∈ J ↔ ∃ c, e c = some j) (y : X) (t : X.functionFieldˣ)
    (ht : G.IsEqn y t) (hE : ∀ c, (E c).IsEqn y ((e c).elim 1 x)) :
    (p • G + ∑ c, r c • E c).IsEqn y
      (t ^ p * ∏ j ∈ J, x j ^ (∑ c ∈ Finset.univ.filter (fun c => e c = some j), r c)) := by
  classical
  have hs : ∀ s : Finset C, (∑ c ∈ s, r c • E c).IsEqn y (∏ c ∈ s, ((e c).elim 1 x) ^ r c) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero y
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact ((hE a).nsmul (r a)).add ih
  have hprod : ∏ j ∈ J, x j ^ (∑ c ∈ Finset.univ.filter (fun c => e c = some j), r c) =
      ∏ c, ((e c).elim 1 x) ^ r c := by
    have h1 : ∀ j, x j ^ (∑ c ∈ Finset.univ.filter (fun c => e c = some j), r c) =
        ∏ c, (if e c = some j then x j ^ r c else 1) := by
      intro j
      rw [← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
    simp_rw [h1]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun c _ => ?_
    rcases hc : e c with _ | j0
    · simp
    · have hj0 : j0 ∈ J := (hJ j0).2 ⟨c, hc⟩
      simp only [Option.some.injEq, Option.elim_some]
      rw [Finset.prod_ite_eq J j0 (fun j => x j ^ r c), if_pos hj0]
  rw [hprod]
  exact (ht.nsmul p).add (hs _)

theorem cartierAt_atlas_inter : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X]
    [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type}
    [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) →
    ∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (𝒜.x j) γ →
    CartierAt (extD _) γ (fun a => logSec (suppAll E) G a (inter 𝒜.U s))
      (fun a => logSec (suppAll E) (p • G + ∑ c, r c • E c) a (inter 𝒜.U s)) := by
  intro p _ X _ _ C _ E n ι _ 𝒜 G r hr s j hj γ hγ
  classical
  obtain ⟨e, he_inj, hJ, heqn⟩ := 𝒜.snc j
  have hW : ∀ w ∈ inter 𝒜.U s, w ∈ 𝒜.U j := fun w hw => (Finset.inf_le hj : inter 𝒜.U s ≤ 𝒜.U j) hw
  have hcoord : IsCoord (𝒜.x j) := ((𝒜.chart j).chart _ (𝒜.gen j)).coord
  have hR : ∀ j', (∑ c ∈ Finset.univ.filter (fun c => e c = some j'), r c) < p := by
    intro j'
    by_cases hne : ∃ c, e c = some j'
    · obtain ⟨c0, hc0⟩ := hne
      have h1 : Finset.univ.filter (fun c => e c = some j') = {c0} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => he_inj c c0 j' h hc0, fun h => h ▸ hc0⟩
      rw [h1, Finset.sum_singleton]
      exact hr c0
    · have h1 : Finset.univ.filter (fun c => e c = some j') = ∅ := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        exact fun h => hne ⟨c, h⟩
      rw [h1, Finset.sum_empty]
      exact (Fact.out : p.Prime).pos
  choose tG htG using fun w : X => G.exists_isEqn w
  have hLe : ∀ (D : CartierDiv X) (w : X), w ∈ 𝒜.U j → ∀ (t : X.functionFieldˣ), D.IsEqn w t → ∀ a,
      logAt (suppAll E) D a w = chartForms (locRing w) (𝒜.x j) (𝒜.J j) t a :=
    fun D w hw t ht a => le_antisymm (logAt_le_chartForms_of_isLogChart (𝒜.chart j) hw ht a) (chartForms_le_logAt_of_isLogChart (𝒜.chart j) hw ht a)
  have hG' : ∀ w ∈ 𝒜.U j, (p • G + ∑ c, r c • E c).IsEqn w
      (tG w ^ p * ∏ j' ∈ 𝒜.J j, 𝒜.x j j' ^ (∑ c ∈ Finset.univ.filter (fun c => e c = some j'), r c)) :=
    fun w hw => isEqn_smul_add_sum_smul E G r p (𝒜.x j) (𝒜.J j) e hJ w (tG w) (htG w) (fun c => heqn c w hw)
  haveI hY : Nonempty {w : X // w ∈ inter 𝒜.U s} :=
    ⟨⟨genericPoint X, mem_inter_of_forall _ _ _ (fun i _ => 𝒜.gen i)⟩⟩
  have hfam := fun a η => logCartier_rounding_family X.functionField p n (𝒜.x j) (𝒜.J j) γ
    {w : X // w ∈ inter 𝒜.U s} (fun w => locRing w.1) (fun w => tG w.1)
    (fun _ j' => ∑ c ∈ Finset.univ.filter (fun c => e c = some j'), r c)
    (fun w => (𝒜.chart j).chart w.1 (hW _ w.2)) (fun _ => hR) hγ a η
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _ h0
    exact cartierMap_eq_extD_imp_eq_zero _ p n (𝒜.x j) γ hcoord hγ x 0 (by rw [h0, map_zero])
  · intro a x _ z _ h
    exact cartierMap_eq_extD_imp_eq_zero _ p n (𝒜.x j) γ hcoord hγ x z h
  · intro y hy hd
    obtain ⟨ζ, ξ, hζ, _, h0, hyeq⟩ := hfam 0 y (fun w => by
      rw [← hLe _ _ (hW _ w.2) _ (hG' _ (hW _ w.2))]
      exact (mem_logSec_iff.1 hy) w.1 w.2) hd
    refine ⟨ζ, mem_logSec_iff.2 fun w hw => ?_, ?_⟩
    · rw [hLe _ _ (hW _ hw) _ (htG w)]
      exact hζ ⟨w, hw⟩
    · rw [hyeq, h0 rfl, map_zero, add_zero]
  · intro a y hy hd
    obtain ⟨ζ, ξ, hζ, hξ, _, hyeq⟩ := hfam (a + 1) y (fun w => by
      rw [← hLe _ _ (hW _ w.2) _ (hG' _ (hW _ w.2))]
      exact (mem_logSec_iff.1 hy) w.1 w.2) hd
    refine ⟨ζ, mem_logSec_iff.2 fun w hw => ?_, ξ, mem_logSec_iff.2 fun w hw => ?_, hyeq⟩
    · rw [hLe _ _ (hW _ hw) _ (htG w)]
      exact hζ ⟨w, hw⟩
    · rw [hLe _ _ (hW _ hw) _ (hG' _ (hW _ hw))]
      exact hξ ⟨w, hw⟩ a rfl

end GlobalTheory
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierOperatorLogSectionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
theorem _root_.GlobalTheory.T.cartier_operator_log_sections : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (𝒜.x j) γ → CartierAt (extD _) γ (fun a => logSec (suppAll E) G a (inter 𝒜.U s)) (fun a => logSec (suppAll E) (p • G + ∑ c, r c • E c) a (inter 𝒜.U s)) := by
  first | exact @_root_.GlobalTheory.cartierAt_atlas_inter | exact _root_.GlobalTheory.cartierAt_atlas_inter | (intros; apply _root_.GlobalTheory.cartierAt_atlas_inter <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLogFormsFrobeniusLift
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RegularFunctionsPthPowerTwist
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.regular_functions_pth_power_twist : ∀ {X : Scheme.{0}} [IsIntegral X] (p : ℕ) (G H : CartierDiv X) (y : X), (H - p • G).Eff → {z : X.functionField | ∃ c ∈ {c : X.functionField | G.RegularAt y c}, ∃ b ∈ locRing y, z = c ^ p * b} ⊆ {c | H.RegularAt y c} := by
  first | exact @_root_.GlobalTheory.DI.pow_mul_locRing_subset_regularAt | exact _root_.GlobalTheory.DI.pow_mul_locRing_subset_regularAt | (intros; apply _root_.GlobalTheory.DI.pow_mul_locRing_subset_regularAt <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogFormsGeneratedDlog
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.log_forms_generated_dlog : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (y : X), (∀ w ∈ locRing y, ExteriorAlgebra.ι X.functionField (dK w) ∈ forms (locRing y : Set X.functionField) (dlog '' {g | LogUnit Z y g}) 1) ∧ ∀ g, LogUnit Z y g → ExteriorAlgebra.ι X.functionField (dlog g) ∈ forms (locRing y : Set X.functionField) (dlog '' {g | LogUnit Z y g}) 1 := by
  first | exact @_root_.GlobalTheory.DI.dK_dlog_mem_forms_one | exact _root_.GlobalTheory.DI.dK_dlog_mem_forms_one | (intros; apply _root_.GlobalTheory.DI.dK_dlog_mem_forms_one <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExteriorDerivativeIsDifferential
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.exterior_derivative_is_differential : ∀ (K : Type) [Field K], IsExtD ℤ K (extD K) := by
  first | exact @_root_.GlobalTheory.LogDR.isExtD_extD | exact _root_.GlobalTheory.LogDR.isExtD_extD | (intros; apply _root_.GlobalTheory.LogDR.isExtD_extD <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobLiftPsiNatCastMul
set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.DI

section FrobDiff

variable {K : Type} [CommRing K]

theorem kaehlerD_aeval_fin_two (x : Fin 2 → K) (P : MvPolynomial (Fin 2) ℤ) :
    KaehlerDifferential.D ℤ K (aeval x P) =
      ∑ i, aeval x (pderiv i P) • KaehlerDifferential.D ℤ K (x i) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ, add_smul, Finset.sum_add_distrib]
  | mul_X P i hP =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hP, Finset.smul_sum, smul_smul,
      Derivation.leibniz, pderiv_X, Fin.sum_univ_two]
    fin_cases i <;> simp [add_smul, mul_comm, smul_smul, Pi.single_apply] <;> abel

theorem ringHom_aeval_fin_two {Kt : Type} [CommRing Kt] (π : Kt →+* K) (x : Fin 2 → Kt)
    (P : MvPolynomial (Fin 2) ℤ) : π (aeval x P) = aeval (fun i => π (x i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP => simp [hP]

variable {Kt : Type} [CommRing Kt] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (π : Kt →+* K) (F : Kt →+* Kt)

theorem frobLift_exists_w (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) :
    ∃ w, F z = z ^ p + p * w := by
  obtain ⟨w, hw⟩ := (hL.ker (F z - z ^ p)).1 (by rw [map_sub, hF, map_pow, sub_self])
  exact ⟨w, by rw [← hw]; ring⟩

theorem frobLift_w_unique (hL : IsFlatLift p π) {z w w' : Kt} (h : F z = z ^ p + p * w)
    (h' : F z = z ^ p + p * w') : π w = π w' := by
  have e : (p : Kt) * (w - w') = 0 := by
    have := h.symm.trans h'
    rw [mul_sub, sub_eq_zero]
    exact add_left_cancel this
  have e2 := (hL.ann _).mp e
  rwa [map_sub, sub_eq_zero] at e2

theorem kaehlerD_pow_char (x : K) : KaehlerDifferential.D ℤ K (x ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

def frobLiftPsi (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) : Ω[K⁄ℤ] :=
  π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) +
    KaehlerDifferential.D ℤ K (π (frobLift_exists_w p π F hL hF z).choose)

variable {p π F}

theorem frobLiftPsi_spec (hL : IsFlatLift p π) (hF : IsFrob p π F) {z w : Kt}
    (h : F z = z ^ p + p * w) :
    frobLiftPsi p π F hL hF z = π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) +
      KaehlerDifferential.D ℤ K (π w) := by
  unfold frobLiftPsi
  rw [frobLift_w_unique p π F hL (frobLift_exists_w p π F hL hF z).choose_spec h]

theorem frobLiftPsi_add (hL : IsFlatLift p π) (hF : IsFrob p π F) (z z' : Kt) :
    frobLiftPsi p π F hL hF (z + z') = frobLiftPsi p π F hL hF z + frobLiftPsi p π F hL hF z' := by
  obtain ⟨w, hw⟩ := frobLift_exists_w p π F hL hF z
  obtain ⟨w', hw'⟩ := frobLift_exists_w p π F hL hF z'
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (X 0 : MvPolynomial (Fin 2) ℤ) (X 1)
  have hp0 : (p : MvPolynomial (Fin 2) ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨C, hC0⟩ : ∃ C : MvPolynomial (Fin 2) ℤ,
      (p : MvPolynomial (Fin 2) ℤ) * C = (X 0 + X 1) ^ p - X 0 ^ p - X 1 ^ p :=
    ⟨X 0 * X 1 * r, by rw [hr]; ring⟩
  have hpd0 : pderiv 0 C = (X 0 + X 1) ^ (p - 1) - X 0 ^ (p - 1) := by
    have := congrArg (pderiv 0) hC0
    simp [Derivation.leibniz_pow] at this
    exact mul_left_cancel₀ hp0 (by rw [this]; ring)
  have hpd1 : pderiv 1 C = (X 0 + X 1) ^ (p - 1) - X 1 ^ (p - 1) := by
    have := congrArg (pderiv 1) hC0
    simp [Derivation.leibniz_pow] at this
    exact mul_left_cancel₀ hp0 (by rw [this]; ring)
  have hc : (z + z') ^ p = z ^ p + z' ^ p + p * aeval ![z, z'] C := by
    have := congrArg (aeval ![z, z']) hC0
    simp at this
    rw [this]
    ring
  rw [frobLiftPsi_spec hL hF hw, frobLiftPsi_spec hL hF hw',
    frobLiftPsi_spec hL hF (w := w + w' - aeval ![z, z'] C) (by rw [map_add (f := _), hw, hw', hc]; ring)]
  have hD : KaehlerDifferential.D ℤ K (π (aeval ![z, z'] C)) =
      ((π z + π z') ^ (p - 1) - π z ^ (p - 1)) • KaehlerDifferential.D ℤ K (π z) +
      ((π z + π z') ^ (p - 1) - π z' ^ (p - 1)) • KaehlerDifferential.D ℤ K (π z') := by
    rw [ringHom_aeval_fin_two, kaehlerD_aeval_fin_two, Fin.sum_univ_two, hpd0, hpd1]
    simp
  simp only [map_add (f := _), map_sub, hD, smul_add, sub_smul]
  abel

theorem frobLiftPsi_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (z z' : Kt) :
    frobLiftPsi p π F hL hF (z * z') =
      π z ^ p • frobLiftPsi p π F hL hF z' + π z' ^ p • frobLiftPsi p π F hL hF z := by
  obtain ⟨w, hw⟩ := frobLift_exists_w p π F hL hF z
  obtain ⟨w', hw'⟩ := frobLift_exists_w p π F hL hF z'
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  rw [frobLiftPsi_spec hL hF hw, frobLiftPsi_spec hL hF hw',
    frobLiftPsi_spec hL hF (w := w * z' ^ p + z ^ p * w' + p * w * w')
      (by rw [map_mul, hw, hw']; ring)]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast, hpK, zero_mul, add_zero, Derivation.leibniz,
    kaehlerD_pow_char p, smul_zero, zero_add]
  have e1 : (π z * π z') ^ (p - 1) * π z = π z ^ p * π z' ^ (p - 1) := by
    rw [mul_pow, mul_right_comm, ← pow_succ, Nat.sub_add_cancel hp1]
  have e2 : (π z * π z') ^ (p - 1) * π z' = π z' ^ p * π z ^ (p - 1) := by
    rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hp1, mul_comm]
  simp only [smul_add, smul_smul, e1, e2]
  abel

theorem frobLiftPsi_natCast_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (y : Kt) :
    frobLiftPsi p π F hL hF ((p : Kt) * y) = 0 := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hp2 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have e : (p : Kt) * (p : Kt) ^ (p - 1) = (p : Kt) ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp1]
  rw [frobLiftPsi_spec hL hF (w := F y - (p : Kt) ^ (p - 1) * y ^ p)
    (by rw [map_mul, map_natCast, mul_pow]; linear_combination (y ^ p) * e)]
  simp [hpK, hF y, kaehlerD_pow_char p, zero_pow hp2]

theorem frobLiftPsi_congr (hL : IsFlatLift p π) (hF : IsFrob p π F) {z z' : Kt} (h : π z = π z') :
    frobLiftPsi p π F hL hF z = frobLiftPsi p π F hL hF z' := by
  obtain ⟨y, hy⟩ := (hL.ker (z - z')).1 (by rw [map_sub, h, sub_self])
  rw [show z = z' + (p : Kt) * y by rw [← hy]; ring, frobLiftPsi_add, frobLiftPsi_natCast_mul, add_zero]

def frobLiftPhi (hL : IsFlatLift p π) (hF : IsFrob p π F) : K →+ Ω[K⁄ℤ] where
  toFun a := frobLiftPsi p π F hL hF (Function.surjInv hL.surj a)
  map_zero' := by
    have h0 : frobLiftPsi p π F hL hF 0 = 0 := by
      have := frobLiftPsi_add hL hF (0 : Kt) 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    rw [frobLiftPsi_congr hL hF (z' := 0) (by rw [Function.surjInv_eq hL.surj, map_zero]), h0]
  map_add' a b := by
    rw [← frobLiftPsi_add, frobLiftPsi_congr hL hF (z' := Function.surjInv hL.surj a + Function.surjInv hL.surj b)
      (by rw [map_add (f := _), Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj])]

theorem frobLiftPhi_apply (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) :
    frobLiftPhi hL hF (π z) = frobLiftPsi p π F hL hF z :=
  frobLiftPsi_congr hL hF (Function.surjInv_eq hL.surj _)

theorem frobLiftPhi_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (a b : K) :
    frobLiftPhi hL hF (a * b) = a ^ p • frobLiftPhi hL hF b + b ^ p • frobLiftPhi hL hF a := by
  obtain ⟨z, rfl⟩ := hL.surj a
  obtain ⟨z', rfl⟩ := hL.surj b
  rw [← map_mul, frobLiftPhi_apply, frobLiftPhi_apply, frobLiftPhi_apply, frobLiftPsi_mul]

theorem exists_isF_of_flatLift : ∀ {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F : Kt →+* Kt), IsFlatLift p π → IsFrob p π F → ∃ f, IsF p π F f := by
  intro K Kt _ _ p _ _ π F hL hF
  have univ : ∀ (M : Type) [AddCommGroup M] [Module K M] (D' : K →+ M),
      (∀ a b, D' (a * b) = a • D' b + b • D' a) →
      ∃ g : Ω[K⁄ℤ] →+ M, (∀ a, g (KaehlerDifferential.D ℤ K a) = D' a) ∧
        ∀ (c : K) (v : Ω[K⁄ℤ]), g (c • v) = c • g v := by
    intro M _ _ D' hD'
    let Dv : Derivation ℤ K M := Derivation.mk' D'.toIntLinearMap hD'
    exact ⟨Dv.liftKaehlerDifferential.toAddMonoidHom,
      fun a => Dv.liftKaehlerDifferential_comp_D a,
      fun c v => Dv.liftKaehlerDifferential.map_smul c v⟩
  have hmul : ∀ a b : K, frobLiftPhi hL hF (a * b) =
      frobenius K p a • frobLiftPhi hL hF b + frobenius K p b • frobLiftPhi hL hF a := by
    intro a b
    rw [frobenius_def p a, frobenius_def p b]
    exact frobLiftPhi_mul hL hF a b
  obtain ⟨g, hg, hsm⟩ :=
    @univ (Ω[K⁄ℤ]) _ (Module.compHom _ (frobenius K p)) (frobLiftPhi hL hF) hmul
  refine ⟨g, ?_, ?_⟩
  · intro c v
    have h0 : g (c • v) = frobenius K p c • g v := hsm c v
    rw [frobenius_def p c] at h0
    exact h0
  · intro z w hzw
    have := hg (π z)
    rw [frobLiftPhi_apply, frobLiftPsi_spec hL hF hzw] at this
    exact this

end FrobDiff

end GlobalTheory.DI
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLogFormsFrobeniusLift
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

theorem mem_latSec_iff {X : Scheme.{0}} {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) (U : X.Opens)
    (v : V) : v ∈ latSec M U ↔ ∀ y ∈ U, v ∈ M y := by
  simp only [latSec, AddSubgroup.mem_iInf]

theorem latSec_anti {X : Scheme.{0}} {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) {U U' : X.Opens}
    (h : U' ≤ U) : latSec M U ≤ latSec M U' := fun v hv =>
  (mem_latSec_iff M U' v).2 fun y hy => (mem_latSec_iff M U v).1 hv y (h hy)

theorem forms_le_of_subset_of_subset {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {B B' : Set K}
    {L L' : Set V} (q : ℕ) (hB : B ⊆ B') (hL : L ⊆ L') : forms B L q ≤ forms B' L' q :=
  AddSubgroup.closure_mono fun _ ⟨b, hb, v, hv, e⟩ => ⟨b, hB hb, v, fun k => hL (hv k), e⟩

theorem f_dlog_of_frob {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F : Kt →+* Kt) (f : Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (hf : IsF p π F f) (g : Kˣ) (z : Kt)
    (hz : π z = g) (hF : F z = z ^ p) : f (dlog g) = dlog g := by
  have key := hf.2 z 0 (by rw [hF]; ring)
  rw [map_zero, map_zero, add_zero, hz] at key
  have hp := (Fact.out : p.Prime)
  have e1 : ((g : K)⁻¹) ^ p * (g : K) ^ (p - 1) = (g : K)⁻¹ := by
    have hg : (g : K) ≠ 0 := g.ne_zero
    obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm ((g : K)⁻¹ ^ n), mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hg, one_pow, mul_one]
  simp only [dlog, dK, Units.val_inv_eq_inv_val]
  rw [hf.1, key, smul_smul, e1]

end GlobalTheory.DI

namespace GlobalTheory.DI

theorem decomp_of_isLifted : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] (Z : Set X) {ι : Type} [LinearOrder ι] (U : ι → X.Opens) {n : ℕ} (x : ι → Fin n → X.functionFieldˣ) (W : Finset ι → X.Opens) (G H : CartierDiv X), n < p → (∀ i, genericPoint X ∈ U i) → (∀ i, IsCoord (x i)) → (∀ s : Finset ι, s.Nonempty → ∀ y, y ∈ W s ↔ ∀ i ∈ s, y ∈ U i) → IsLifted p Z U x → (H - p • G).Eff → (∀ q (s : Finset ι) η, η ∈ logSec Z H q (W s) → extD _ η ∈ logSec Z H (q + 1) (W s)) → (∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (x j) γ → CartierAt (extD _) γ (fun a => logSec Z G a (W s)) (fun a => logSec Z H a (W s))) → ∀ a b, HypZero (extD _) (fun q s => logSec Z H q (W s)) (a + b) → CechZero (fun s => logSec Z G a (W s)) b := by
  intro p _ X _ _ Z ι _ U n x W G H hnp hgen hcoord hW hlift hEff hdT hCart a b hHyp
  obtain ⟨Kt, _, π, F, hπ, hF, hz, hlog⟩ := hlift
  choose f hf using fun i => exists_isF_of_flatLift p π (F i) hπ (hF i)
  choose h hh using fun i j => exists_isH_of_isFrob p π (F i) (F j) hπ (hF i) (hF j)
  have hd := GlobalTheory.T.exterior_derivative_is_differential X.functionField
  have hdat := isDatum_of_frobenius_lifts p π F (extD X.functionField) f h hπ hF hd hf hh
  choose γ hγ using fun i => exists_isGamma p (f i) (hf i).1

  have hWmono : ∀ s t : Finset ι, s.Nonempty → s ⊆ t → W t ≤ W s := by
    intro s t hs hst y hy
    exact (hW s hs y).2 fun i hi => (hW t (hs.mono hst) y).1 hy i (hst hi)
  have hgenW : ∀ s : Finset ι, s.Nonempty → genericPoint X ∈ W s := fun s hs =>
    (hW s hs _).2 fun i _ => hgen i
  have hNuniv : ∀ a' (s : Finset ι), s.Nonempty →
      logSec Z G a' (W s) ≤ forms (Set.univ : Set X.functionField) (Set.univ : Set Ω[X.functionField⁄ℤ]) a' := by
    intro a' s hs v hv
    have := (mem_latSec_iff _ _ v).1 hv _ (hgenW s hs)
    exact forms_le_of_subset_of_subset a' (Set.subset_univ _) (Set.subset_univ _) this
  refine GlobalTheory.T.splitting_local_integrality (K := X.functionField) (V := Ω[X.functionField⁄ℤ]) p (extD X.functionField) f h γ
    (P := X) (fun s => {y | ∀ i ∈ s, y ∈ U i}) (fun y => locRing y) (fun y => {c | G.RegularAt y c})
    (fun y => dlog '' {g | LogUnit Z y g}) (fun q s => logSec Z G q (W s)) (fun q s => logSec Z H q (W s))
    hd.toIsOddDer hdat hγ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b hHyp
  · intro q s t hs hst
    exact latSec_anti _ (hWmono s t hs hst)
  · intro q s t hs hst
    exact latSec_anti _ (hWmono s t hs hst)
  · intro q s v hv
    exact hdT q s v hv
  · intro a' s hs
    exact hNuniv a' s hs
  · intro a' s hs hpa
    obtain ⟨i, -⟩ := id hs
    rw [eq_bot_iff]
    refine (hNuniv a' s hs).trans (le_of_eq ?_)
    exact spanForms_eq_bot_of_lt_card X.functionField n (x i) _ _ a' (hcoord i) (by omega)
  · intro a' s hs y hy v hv
    exact (mem_latSec_iff _ _ v).1 hv y ((hW s hs y).2 hy)
  · intro q s v hs _ hv
    refine (mem_latSec_iff _ _ v).2 fun y hy => ?_
    exact forms_le_of_subset_of_subset q (GlobalTheory.T.regular_functions_pth_power_twist p G H y hEff) subset_rfl (hv y ((hW s hs y).1 hy))
  · rintro s y hy i hi _ ⟨g, hg, rfl⟩
    obtain ⟨hfi, -⟩ := divided_frob_logForm p π F f h s (locRing y) (g : X.functionField) hf hh
      (hlog y s hy g hg)
    obtain ⟨w, hwA, hw⟩ := hfi i hi
    have e : dlog g = ((g : X.functionField))⁻¹ • KaehlerDifferential.D ℤ X.functionField g := by
      simp only [dlog, dK, Units.val_inv_eq_inv_val]
    rw [e, hw g.ne_zero, map_add (f := _), ← e]
    exact AddSubgroup.add_mem _ ((GlobalTheory.T.log_forms_generated_dlog Z y).2 g hg) ((GlobalTheory.T.log_forms_generated_dlog Z y).1 w hwA)
  · rintro s y hy i hi j hj _ ⟨g, hg, rfl⟩
    obtain ⟨-, hhij⟩ := divided_frob_logForm p π F f h s (locRing y) (g : X.functionField) hf hh
      (hlog y s hy g hg)
    have e : dlog g = ((g : X.functionField))⁻¹ • KaehlerDifferential.D ℤ X.functionField g := by
      simp only [dlog, dK, Units.val_inv_eq_inv_val]
    rw [e]
    exact hhij i hi j hj
  · intro s j hj
    refine hCart s j hj (γ j) ⟨(hγ j).1, fun l => ?_⟩
    obtain ⟨z, hzx, hzF⟩ := hz j l
    rw [(hγ j).2, f_dlog_of_frob p π (F j) (f j) (hf j) (x j l) z hzx hzF]

end GlobalTheory.DI
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLogFormsFrobeniusLiftStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.cech_log_forms_frobenius_lift : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] (Z : Set X) {ι : Type} [LinearOrder ι] (U : ι → X.Opens) {n : ℕ} (x : ι → Fin n → X.functionFieldˣ) (W : Finset ι → X.Opens) (G H : CartierDiv X), n < p → (∀ i, genericPoint X ∈ U i) → (∀ i, IsCoord (x i)) → (∀ s : Finset ι, s.Nonempty → ∀ y, y ∈ W s ↔ ∀ i ∈ s, y ∈ U i) → IsLifted p Z U x → (H - p • G).Eff → (∀ q (s : Finset ι) η, η ∈ logSec Z H q (W s) → extD _ η ∈ logSec Z H (q + 1) (W s)) → (∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (x j) γ → CartierAt (extD _) γ (fun a => logSec Z G a (W s)) (fun a => logSec Z H a (W s))) → ∀ a b, HypZero (extD _) (fun q s => logSec Z H q (W s)) (a + b) → CechZero (fun s => logSec Z G a (W s)) b := by
  first | exact @_root_.GlobalTheory.DI.decomp_of_isLifted | exact _root_.GlobalTheory.DI.decomp_of_isLifted | (intros; apply _root_.GlobalTheory.DI.decomp_of_isLifted <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusDecompositionOfLift
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem mem_inter_iff {X : Scheme.{0}} [IsIntegral X] {ι : Type} (U : ι → X.Opens) (s : Finset ι) (y : X) :
    y ∈ inter U s ↔ ∀ i ∈ s, y ∈ U i := by
  classical
  unfold inter
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp]
    rw [← ih]
    exact Iff.rfl

theorem decomp_of_isLifted (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p]
    {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι)
    (hn : n < p) (hL : IsLifted p (suppAll E) 𝒜.U 𝒜.x) : Decomp p 𝒜 := by
  intro G r hr a b hH
  exact GlobalTheory.T.cech_log_forms_frobenius_lift p (suppAll E) 𝒜.U 𝒜.x (inter 𝒜.U) G (p • G + ∑ c, r c • E c) hn 𝒜.gen
    (fun i => ((𝒜.chart i).chart _ (𝒜.gen i)).coord)
    (fun s _ y => mem_inter_iff 𝒜.U s y) hL
    (GlobalTheory.T.roundedTwist_localEquation_chart p 𝒜 G r hr).1
    (fun q s η hη => GlobalTheory.T.log_sections_differential_closed p 𝒜 G r hr q (inter 𝒜.U s) η hη)
    (fun s j hj γ hγ => GlobalTheory.T.cartier_operator_log_sections p 𝒜 G r hr s j hj γ hγ)
    a b hH

end GlobalTheory.LogDR
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FrobeniusDecompositionOfLiftStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier
theorem _root_.GlobalTheory.T.frobenius_decomposition_of_lift : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι), n < p → IsLifted p (suppAll E) 𝒜.U 𝒜.x → Decomp p 𝒜 := by
  first | exact @_root_.GlobalTheory.LogDR.decomp_of_isLifted | exact _root_.GlobalTheory.LogDR.decomp_of_isLifted | (intros; apply _root_.GlobalTheory.LogDR.decomp_of_isLifted <;> assumption)
end
