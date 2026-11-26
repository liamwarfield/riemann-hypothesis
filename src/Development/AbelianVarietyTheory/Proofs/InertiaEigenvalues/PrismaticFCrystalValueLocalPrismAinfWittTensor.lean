module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefinite
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalValueLocalPrismAinfWittTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalValueLocalPrismAinfWittTensor
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism

namespace GlobalTheory.Prism.LocalValue

theorem exists_basis {A B M N ι : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [Fintype ι] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (b : Module.Basis ι A M) : ∃ c : Module.Basis ι B N, ∀ i, c i = u (b i) := by
  classical
  let v : M →ₛₗ[f] (ι → B) :=
    { toFun := fun x i => f (b.equivFun x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  let Q : (ι → B) →ₗ[B] N := Fintype.linearCombination B fun i => u (b i)
  have hQ : Q.comp S = LinearMap.id := h.hom_ext fun x => by
    rw [LinearMap.comp_apply, hS, LinearMap.id_apply, Fintype.linearCombination_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← b.sum_equivFun x, map_sum]
    exact Finset.sum_congr rfl fun i _ => (u.map_smulₛₗ _ _).symm
  have hQ1 : ∀ i, Q (Pi.single i 1) = u (b i) := fun i => by
    simp [Q]
  have hS' : S.comp Q = LinearMap.id := by
    refine (Pi.basisFun B ι).ext fun i => ?_
    rw [LinearMap.comp_apply, Pi.basisFun_apply, hQ1, hS, LinearMap.id_apply]
    ext k
    change f (b.equivFun (b i) k) = _
    rw [b.equivFun_self, Pi.single_apply]
    by_cases hik : i = k
    · simp [hik]
    · simp [hik, Ne.symm hik]
  refine ⟨(Pi.basisFun B ι).map (LinearEquiv.ofLinear Q S hQ hS'), fun i => ?_⟩
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  exact hQ1 i

theorem exists_pow_smul_eq_sum {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]
    {d : A} {f : A →+* Localization.Away d} {Φ : M →ₛₗ[f] LocalizedModule (Submonoid.powers d) M}
    (h : SemiBC Φ) (b : Module.Basis ι A M) (m : ι → M) (k : ι → ℕ)
    (hm : ∀ i, IsFrac d (Φ (b i)) (m i) (k i)) (x : M) :
    ∃ (r : ℕ) (s : ι → A), d ^ r • x = ∑ i, s i • m i := by
  obtain ⟨c, hc⟩ := exists_basis h b
  have h1 : (LocalizedModule.mk x 1 : LocalizedModule (Submonoid.powers d) M) ∈
      Submodule.span (Localization.Away d)
        (Set.range fun i => (LocalizedModule.mk (m i) 1 : LocalizedModule (Submonoid.powers d) M)) := by
    refine (?_ : (⊤ : Submodule (Localization.Away d) _) ≤ _) Submodule.mem_top
    rw [← c.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h2 : c i = (Localization.mk 1 ⟨d ^ k i, (Submonoid.mem_powers_iff _ _).2 ⟨k i, rfl⟩⟩ :
        Localization.Away d) • (LocalizedModule.mk (m i) 1 : LocalizedModule (Submonoid.powers d) M) := by
      rw [hc, hm i, LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨⟨_, t, rfl⟩, ht⟩ := multiple_mem_span_of_mem_localization_span (Submonoid.powers d)
    (Localization.Away d) _ _ h1
  obtain ⟨s, hs⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 ht
  have h3 : LocalizedModule.mkLinearMap (Submonoid.powers d) M (∑ i, s i • m i) =
      LocalizedModule.mkLinearMap (Submonoid.powers d) M (d ^ t • x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smul]
    simp only [map_smul]
    exact hs
  rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_eq] at h3
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := h3
  simp only [one_smul, Submonoid.smul_def] at ha
  refine ⟨a + t, fun i => d ^ a * s i, ?_⟩
  rw [pow_add, mul_smul, ← ha, Finset.smul_sum]
  simp only [mul_smul]

theorem exists_eq_smul {A B M N ι : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [Fintype ι] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u)
    (b : Module.Basis ι A M) {π : A} (hπ : RingHom.ker f = Ideal.span {π}) (x : M) (hx : u x = 0) :
    ∃ y, x = π • y := by
  obtain ⟨c, hc⟩ := exists_basis h b
  have h1 : ∑ i, f (b.equivFun x i) • c i = 0 := by
    rw [← hx]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← b.sum_equivFun x, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hc, u.map_smulₛₗ]
  have h2 := Fintype.linearIndependent_iff.1 c.linearIndependent _ h1
  have h3 : ∀ i, ∃ a, a * π = b.equivFun x i := fun i =>
    Ideal.mem_span_singleton'.1 (hπ ▸ (RingHom.mem_ker).2 (h2 i))
  choose a ha using h3
  refine ⟨∑ i, a i • b i, ?_⟩
  conv_lhs => rw [← b.sum_equivFun x]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [← ha, smul_smul, mul_comm]

theorem ennreal_volume_ratio_step_cancel {A B M N : Type} [CommRing A] [CommRing B] [IsDomain B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] [Module.Free B N] {f : A →+* B} (u : M →ₛₗ[f] N) {e : A}
    (he : f e ≠ 0) {m n : M} {k i r : ℕ} (h : (e * e) ^ r • (e ^ i • m - e ^ k • n) = 0) {y : N}
    (hy : f e ^ i • y = u n) : f e ^ k • y = u m := by
  have h2 := congrArg u h
  rw [u.map_smulₛₗ, map_sub, u.map_smulₛₗ, u.map_smulₛₗ, map_zero, map_pow, map_pow, map_pow, map_mul,
    ← hy, smul_comm (f e ^ k), ← smul_sub, smul_eq_zero, smul_eq_zero] at h2
  rcases h2 with h2 | h2 | h2
  · exact absurd h2 (pow_ne_zero _ (mul_ne_zero he he))
  · exact absurd h2 (pow_ne_zero _ he)
  · exact (sub_eq_zero.1 h2).symm

theorem general {l : ℕ} {R : Type} [CommRing R] {PS PA : Obj l R} [IsLocalRing PS.A] (io : Hom PS PA)
    {B N : Type} [CommRing B] [IsDomain B] [AddCommGroup N] [Module B N] {f : PA.A →+* B}
    (E : FCrys l R) {j : E.M PA →ₛₗ[f] N} (hj : SemiBC j) (F : N → N)
    (hF : ∀ (d : ↥PA.I), (d : PA.A) ≠ 0 → ∀ (x m : E.M PA) (k : ℕ), IsFrac (d : PA.A) (E.Φ PA d x) m k →
      f d ^ k • F (j x) = j m)
    {Q : PS.A} (hQ : Q ∈ PS.I) (ψ : PS.A →+* B) (hψ : ∀ x, ψ x = f (io.f x)) (hQ0 : ψ Q ≠ 0) :
    ∃ (q : ℕ) (b : Module.Basis (Fin q) PS.A (E.M PS)) (c : Module.Basis (Fin q) B N),
      (∀ i, c i = j (E.tr io (b i))) ∧
      (∀ x, ∃ (k : ℕ) (m : E.M PS), ψ Q ^ k • F (j (E.tr io x)) = j (E.tr io m)) ∧
      (∀ x, ∃ (k : ℕ) (s : Fin q → PS.A), ψ Q ^ k • j (E.tr io x) = ∑ i, ψ (s i) • F (c i)) := by
  have := E.fin PS
  have := E.proj PS
  have : Module.Free PS.A (E.M PS) := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis PS.A (E.M PS)
  obtain ⟨c', hc'⟩ := exists_basis (E.tr_bc io) b
  obtain ⟨c, hc⟩ := exists_basis hj c'
  have hcb : ∀ i, c i = j (E.tr io (b i)) := fun i => by rw [hc, hc']
  have : Module.Free B N := Module.Free.of_basis c
  have hsm : ∀ (s : PS.A) (x : E.M PS), j (E.tr io (s • x)) = ψ s • j (E.tr io x) := fun s x => by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hψ]
  have key : ∀ (x m : E.M PS) (k : ℕ), IsFrac Q (E.Φ PS ⟨Q, hQ⟩ x) m k →
      ψ Q ^ k • F (j (E.tr io x)) = j (E.tr io m) := by
    intro x m k h
    have h0 : io.f Q ≠ 0 := fun h0 => hQ0 (by rw [hψ, h0, map_zero])
    obtain ⟨n, i, hn⟩ := exists_isFrac (io.f Q) (E.Φ PA ⟨io.f Q, io.f_I Q hQ⟩ (E.tr io x))
    obtain ⟨r, hr⟩ := E.Φ_nat io ⟨Q, hQ⟩ ⟨io.f Q, io.f_I Q hQ⟩ x m k n i h hn
    have h1 := hF ⟨io.f Q, io.f_I Q hQ⟩ h0 _ n i hn
    rw [hψ] at hQ0 ⊢
    exact ennreal_volume_ratio_step_cancel j hQ0 hr h1
  refine ⟨_, b, c, hcb, fun x => ?_, fun x => ?_⟩
  · obtain ⟨m, k, h⟩ := exists_isFrac Q (E.Φ PS ⟨Q, hQ⟩ x)
    exact ⟨k, m, key x m k h⟩
  · choose m k hm using fun i => exists_isFrac Q (E.Φ PS ⟨Q, hQ⟩ (b i))
    obtain ⟨r, s, hs⟩ := exists_pow_smul_eq_sum (E.Φ_bc PS ⟨Q, hQ⟩) b m k hm x
    refine ⟨r, fun i => s i * Q ^ k i, ?_⟩
    have hs' : Q ^ r • x = ∑ i, s i • m i := hs
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_pow, ← hsm, hs', map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsm, ← key _ _ _ (hm i), hcb, smul_smul, map_mul, map_pow]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (PS PW : Obj l ↥(OL K)) (ev : Hom PS PW) (ioH : Hom PS (ainfObj K)) (gH : ↥(GK K) → Hom PS PS) (π Q : PS.A) (ψ : PS.A →+* WCb l), (∀ x, ψ x = inclW l (ainfId K (ioH.f x))) → (∀ g, ioH.comp (gH g) = (ainfHom K g).comp ioH) → (∀ g, ev.comp (gH g) = ev) → RingHom.ker ev.f = Ideal.span {π} → Q ∈ PS.I → IsLocalRing PS.A → ψ Q ≠ 0 → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (E : FCrys l ↥(OL K)) (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K E (ainfObj K) (ainfId K) T ρ j → ∃ (q : ℕ) (b : Module.Basis (Fin q) PS.A (E.M PS)) (c : Module.Basis (Fin q) (WCb l) (WCb l ⊗[ℤ_[l]] T)), (∀ i, c i = j (E.tr ioH (b i))) ∧ (∀ x, ∃ (k : ℕ) (m : E.M PS), ψ Q ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (E.tr ioH x)) = j (E.tr ioH m)) ∧ (∀ x, ∃ (k : ℕ) (s : Fin q → PS.A), ψ Q ^ k • j (E.tr ioH x) = ∑ i, ψ (s i) • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c i)) ∧ (∀ (g : ↥(GK K)) x, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (j (E.tr ioH x)) = j (E.tr ioH (E.tr (gH g) x))) ∧ (∀ g x, ∃ y, E.tr (gH g) x - x = π • y) := by
  intro l _ K PS PW ev ioH gH π Q ψ hψ hg hev hker hQ hloc hQ0 T _ _ ρ E j H
  obtain ⟨q, b, c, h1, h2, h3⟩ := general ioH E H.bc
    (fun y => TensorProduct.map (frobW l).toLinearMap LinearMap.id y) H.j_φ hQ ψ hψ hQ0
  refine ⟨q, b, c, h1, h2, h3, fun g x => ?_, fun g x => ?_⟩
  · have h4 : E.tr ioH (E.tr (gH g) x) = E.tr (ainfHom K g) (E.tr ioH x) :=
      ((E.tr_comp ioH (gH g) x).symm.trans (congrArg (fun f => E.tr f x) (hg g))).trans
        (E.tr_comp (ainfHom K g) ioH x)
    exact (H.j_act g (E.tr ioH x)).symm.trans (congrArg j h4.symm)
  · refine exists_eq_smul (E.tr_bc ev) b hker _ ?_
    rw [map_sub, ← E.tr_comp, hev, sub_self]

end GlobalTheory.Prism.LocalValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalValueLocalPrismAinfWittTensorStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismaticFCrystal_value_localPrism_ainf_wittTensor : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (PS PW : Obj l ↥(OL K)) (ev : Hom PS PW) (ioH : Hom PS (ainfObj K)) (gH : ↥(GK K) → Hom PS PS) (π Q : PS.A) (ψ : PS.A →+* WCb l), (∀ x, ψ x = inclW l (ainfId K (ioH.f x))) → (∀ g, ioH.comp (gH g) = (ainfHom K g).comp ioH) → (∀ g, ev.comp (gH g) = ev) → RingHom.ker ev.f = Ideal.span {π} → Q ∈ PS.I → IsLocalRing PS.A → ψ Q ≠ 0 → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (E : FCrys l ↥(OL K)) (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K E (ainfObj K) (ainfId K) T ρ j → ∃ (q : ℕ) (b : Module.Basis (Fin q) PS.A (E.M PS)) (c : Module.Basis (Fin q) (WCb l) (WCb l ⊗[ℤ_[l]] T)), (∀ i, c i = j (E.tr ioH (b i))) ∧ (∀ x, ∃ (k : ℕ) (m : E.M PS), ψ Q ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (E.tr ioH x)) = j (E.tr ioH m)) ∧ (∀ x, ∃ (k : ℕ) (s : Fin q → PS.A), ψ Q ^ k • j (E.tr ioH x) = ∑ i, ψ (s i) • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c i)) ∧ (∀ (g : ↥(GK K)) x, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (j (E.tr ioH x)) = j (E.tr ioH (E.tr (gH g) x))) ∧ (∀ g x, ∃ y, E.tr (gH g) x - x = π • y) := by
  first | exact @GlobalTheory.Prism.LocalValue.main | exact GlobalTheory.Prism.LocalValue.main | (intros; apply GlobalTheory.Prism.LocalValue.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisLocallyMonomial
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisLocallyMonomial
noncomputable section

open Filter Topology
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.GaussMono

theorem eventually_iSup_eq_monomial_left (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hG : (⨆ n, c n * ρ ^ n) ≠ 0) :
    ∃ i, ∀ᶠ r in 𝓝[≤] ρ, (⨆ n, c n * r ^ n) = c i * r ^ i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < c j := by
    by_contra h
    push_neg at h
    apply hG
    have : ∀ n, c n = 0 := fun n => le_antisymm (h n) (h0 n)
    simp [this]
  have hσ0 : 0 < ρ / 2 := by positivity
  have hσρ : ρ / 2 < ρ := by linarith
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (mul_pos hj (pow_pos hσ0 j)) hρ1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (insert j (Finset.range M))
    (fun n => toLex (c n * ρ ^ n, OrderDual.toDual n)) ⟨j, Finset.mem_insert_self _ _⟩
  have hpos : ∀ᶠ r in 𝓝[≤] ρ, ρ / 2 < r := (eventually_gt_nhds hσρ).filter_mono nhdsWithin_le_nhds
  have key : ∀ n ∈ insert j (Finset.range M), ∀ᶠ r in 𝓝[≤] ρ, c n * r ^ n ≤ c i * r ^ i := by
    intro n hn
    rcases Prod.Lex.toLex_le_toLex.1 (hi n hn) with h | ⟨h, h'⟩
    · have : ∀ᶠ r in 𝓝 ρ, c n * r ^ n < c i * r ^ i :=
        ContinuousAt.eventually_lt (f := fun r : ℝ => c n * r ^ n) (g := fun r : ℝ => c i * r ^ i)
          (by fun_prop) (by fun_prop) h
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
    · filter_upwards [self_mem_nhdsWithin, hpos] with r hr hr0
      have hr : r ≤ ρ := hr
      have hr0 : 0 ≤ r := hσ0.le.trans hr0.le
      simp only at h h'
      have hin : i ≤ n := OrderDual.toDual_le_toDual.1 h'
      have e : ∀ m, c m * r ^ m = c m * ρ ^ m * (r / ρ) ^ m := fun m => by
        rw [div_pow]; field_simp
      rw [e n, e i, h]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (div_nonneg hr0 hρ.le) ((div_le_one hρ).2 hr) hin)
        (mul_nonneg (h0 _) (pow_nonneg hρ.le _))
  refine ⟨i, ?_⟩
  filter_upwards [(eventually_all_finset _).2 key, hpos, self_mem_nhdsWithin] with r hk hrσ hr
  have hr : r ≤ ρ := hr
  have hr0 : 0 ≤ r := hσ0.le.trans hrσ.le
  have hall : ∀ n, c n * r ^ n ≤ c i * r ^ i := by
    intro n
    by_cases hn : n < M
    · exact hk n (Finset.mem_insert_of_mem (Finset.mem_range.2 hn))
    · refine le_trans ?_ (hk j (Finset.mem_insert_self _ _))
      calc c n * r ^ n ≤ 1 * ρ ^ n := by gcongr; exact h1 n
        _ ≤ ρ ^ M := by rw [one_mul]; exact pow_le_pow_of_le_one hρ.le hρ1.le (not_lt.1 hn)
        _ ≤ c j * (ρ / 2) ^ j := hM.le
        _ ≤ c j * r ^ j := by gcongr
  exact le_antisymm (ciSup_le hall) (le_ciSup (f := fun n => c n * r ^ n) ⟨_, Set.forall_mem_range.2 hall⟩ i)

theorem eventually_monomial {R : Type} [CommRing R] (p : R) {L ρ : ℝ} (hL : 0 < L) (hLρ : L ≤ ρ) (hρ1 : ρ < 1)
    (N : ℝ → R → ℝ)
    (hN : ∀ r, L ≤ r → r < 1 → (∀ x, N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧
      (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ N r p = r)
    (b : R) (hb : 0 < N ρ b)
    (hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : R) (c : ℕ → ℝ), p ^ k * b = a + p ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, L ≤ r → r < 1 → N r a = ⨆ n, c n * r ^ n)
    (f : Filter ℝ) (hf : f ≤ 𝓝 ρ) (hf0 : pure ρ ≤ f) (hfL : ∀ᶠ r in f, L ≤ r ∧ r < 1)
    (hmono : ∀ c : ℕ → ℝ, (∀ n, 0 ≤ c n) → (∀ n, c n ≤ 1) → (⨆ n, c n * ρ ^ n) ≠ 0 →
      ∃ i, ∀ᶠ r in f, (⨆ n, c n * r ^ n) = c i * r ^ i) :
    ∃ (c : ℝ) (k : ℤ), 0 < c ∧ ∀ᶠ r in f, N r b = c * r ^ k := by
  have hρ : 0 < ρ := hL.trans_le hLρ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb hρ1
  obtain ⟨k, a, z, c, hab, h0, h1, hc⟩ := hd n
  have hz : ∀ r, L ≤ r → r < 1 → N r (p ^ (k + n) * z) ≤ r ^ (k + n) := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [GlobalTheory.GaussSlope.map_pow_mul _ e4, e5]
    exact mul_le_of_le_one_right (pow_nonneg (hL.le.trans hr) _) (e1 z)
  have hbb : ∀ r, L ≤ r → r < 1 → N r (p ^ k * b) = r ^ k * N r b := by
    intro r hr hr1
    obtain ⟨-, -, -, e4, e5⟩ := hN r hr hr1
    rw [GlobalTheory.GaussSlope.map_pow_mul _ e4, e5]
  have ha : ρ ^ (k + n) < N ρ a := by
    obtain ⟨-, e2, e3, -, -⟩ := hN ρ hLρ hρ1
    have h2 : ρ ^ (k + n) < N ρ (p ^ k * b) := by
      rw [hbb ρ hLρ hρ1, pow_add]
      exact mul_lt_mul_of_pos_left hn (pow_pos hρ _)
    have h3 : a = p ^ k * b + -(p ^ (k + n) * z) := by rw [hab]; ring
    rw [h3, GlobalTheory.GaussSlope.add_eq_of_lt _ e2 e3 (by rw [e3]; exact (hz ρ hLρ hρ1).trans_lt h2)]
    exact h2
  rw [hc ρ hLρ hρ1] at ha
  obtain ⟨i, hi⟩ := hmono c h0 h1 ((pow_pos hρ _).trans ha).ne'
  have hiρ : (⨆ n, c n * ρ ^ n) = c i * ρ ^ i := Filter.mem_pure.1 (hf0 hi)
  rw [hiρ] at ha
  have hci : 0 < c i := (mul_pos_iff_of_pos_right (pow_pos hρ i)).1 ((pow_pos hρ _).trans ha)
  have h4 : ∀ᶠ r in 𝓝 ρ, r ^ (k + n) < c i * r ^ i :=
    ContinuousAt.eventually_lt (f := fun r : ℝ => r ^ (k + n)) (g := fun r : ℝ => c i * r ^ i)
      (by fun_prop) (by fun_prop) ha
  refine ⟨c i, (i : ℤ) - k, hci, ?_⟩
  filter_upwards [hi, hf h4, hfL] with r hr1 hr2 hr
  obtain ⟨hr, hr3⟩ := hr
  have hr0 : 0 < r := hL.trans_le hr
  obtain ⟨-, e2, e3, -, -⟩ := hN r hr hr3
  have h6 := hbb r hr hr3
  have h7 : N r a = c i * r ^ i := by rw [hc r hr hr3, hr1]
  rw [hab, GlobalTheory.GaussSlope.add_eq_of_lt _ e2 e3 (by rw [h7]; exact (hz r hr hr3).trans_lt hr2), h7] at h6
  rw [zpow_sub₀ hr0.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc, h6]
  field_simp

end GlobalTheory.GaussMono

namespace GlobalTheory.PMon.Gauss

theorem gC_monomial_near : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ₀ : ℝ, (l : ℝ)⁻¹ ≤ ρ₀ →
    ρ₀ < 1 → (∃ (c : ℝ) (k : ℤ) (ρ₂ : ℝ), 0 < c ∧ ρ₀ < ρ₂ ∧ ρ₂ < 1 ∧
      ∀ ρ ∈ Set.Icc ρ₀ ρ₂, gC l ρ x = c * ρ ^ k) ∧
    ((l : ℝ)⁻¹ < ρ₀ → ∃ (c : ℝ) (k : ℤ) (ρ₁ : ℝ), 0 < c ∧ (l : ℝ)⁻¹ ≤ ρ₁ ∧ ρ₁ < ρ₀ ∧
      ∀ ρ ∈ Set.Icc ρ₁ ρ₀, gC l ρ x = c * ρ ^ k) := by
  intro l _ x hx ρ₀ hρl hρ1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hL : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hρ0 : 0 < ρ₀ := hL.trans_le hρl
  have hN : ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ y, gC l r y ≤ 1) ∧
      (∀ y z, gC l r (y + z) ≤ max (gC l r y) (gC l r z)) ∧ (∀ y, gC l r (-y) = gC l r y) ∧
      (∀ y z, gC l r (y * z) = gC l r y * gC l r z) ∧ gC l r (l : Formalism.Per.Acris l) = r := by
    intro r hr hr1
    obtain ⟨e1, e2, e3, e4, e5⟩ := isGauss_gC_target l r hr hr1
    refine ⟨fun y => (e1 y).2, e2, e3, e4, ?_⟩
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, e5]
    exact GlobalTheory.GaussSlope.gauss_l l (hL.le.trans hr)
  have hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : Formalism.Per.Acris l) (c : ℕ → ℝ),
      (l : Formalism.Per.Acris l) ^ k * x = a + (l : Formalism.Per.Acris l) ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → gC l r a = ⨆ n, c n * r ^ n := by
    intro n
    obtain ⟨s, z, h⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x n
    obtain ⟨k, a, ha⟩ := GlobalTheory.GaussSlope.exists_pow_mul_eq l s
    refine ⟨k, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a, z,
      fun n => ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n), ?_,
      fun n => by positivity, fun n => ?_, fun r hr hr1 => (isGauss_gC_target l r hr hr1).2.2.2.2 a⟩
    · rw [h, mul_add, ha, pow_add, mul_assoc]
    · exact Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity)
  have hb : 0 < gC l ρ₀ x := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx ρ₀ hρl hρ1
  constructor
  · have hfL : ∀ᶠ r in 𝓝[≥] ρ₀, (l : ℝ)⁻¹ ≤ r ∧ r < 1 := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hρ1).filter_mono nhdsWithin_le_nhds] with r hr hr1
      exact ⟨hρl.trans hr, hr1⟩
    obtain ⟨c, k, hc, hev⟩ := GlobalTheory.GaussMono.eventually_monomial (l : Formalism.Per.Acris l) hL hρl hρ1 (gC l) hN x hb
      hd (𝓝[≥] ρ₀) nhdsWithin_le_nhds (pure_le_nhdsWithin (Set.mem_Ici.2 le_rfl)) hfL
      (fun c h0 h1 hG => GlobalTheory.GaussSlope.eventually_iSup_eq_monomial c h0 h1 hρ0 hρ1 hG)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
    have hu : ρ₀ < u := hu
    obtain ⟨ρ₂, h2a, h2b⟩ := exists_between (lt_min hu hρ1)
    exact ⟨c, k, ρ₂, hc, h2a, h2b.trans_le (min_le_right _ _),
      fun r hr => hsub ⟨hr.1, hr.2.trans_lt (h2b.trans_le (min_le_left _ _))⟩⟩
  · intro hlt
    have hfL : ∀ᶠ r in 𝓝[≤] ρ₀, (l : ℝ)⁻¹ ≤ r ∧ r < 1 := by
      filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hlt).filter_mono nhdsWithin_le_nhds] with r hr hr1
      exact ⟨(hr1 : (l : ℝ)⁻¹ < r).le, (hr : r ≤ ρ₀).trans_lt hρ1⟩
    obtain ⟨c, k, hc, hev⟩ := GlobalTheory.GaussMono.eventually_monomial (l : Formalism.Per.Acris l) hL hρl hρ1 (gC l) hN x hb
      hd (𝓝[≤] ρ₀) nhdsWithin_le_nhds (pure_le_nhdsWithin (Set.mem_Iic.2 le_rfl)) hfL
      (fun c h0 h1 hG => GlobalTheory.GaussMono.eventually_iSup_eq_monomial_left c h0 h1 hρ0 hρ1 hG)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsLE_iff_exists_Ioc_subset.1 hev
    have hu : u < ρ₀ := hu
    obtain ⟨ρ₁, h1a, h1b⟩ := exists_between (max_lt hu hlt)
    exact ⟨c, k, ρ₁, hc, (le_max_right _ _).trans h1a.le, h1b,
      fun r hr => hsub ⟨(le_max_left _ _).trans_lt (h1a.trans_le hr.1), hr.2⟩⟩

end GlobalTheory.PMon.Gauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisLocallyMonomialStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_locally_monomial : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ₀ : ℝ, (l : ℝ)⁻¹ ≤ ρ₀ → ρ₀ < 1 → (∃ (c : ℝ) (k : ℤ) (ρ₂ : ℝ), 0 < c ∧ ρ₀ < ρ₂ ∧ ρ₂ < 1 ∧ ∀ ρ ∈ Set.Icc ρ₀ ρ₂, gC l ρ x = c * ρ ^ k) ∧ ((l : ℝ)⁻¹ < ρ₀ → ∃ (c : ℝ) (k : ℤ) (ρ₁ : ℝ), 0 < c ∧ (l : ℝ)⁻¹ ≤ ρ₁ ∧ ρ₁ < ρ₀ ∧ ∀ ρ ∈ Set.Icc ρ₁ ρ₀, gC l ρ x = c * ρ ^ k) := by
  first | exact @GlobalTheory.PMon.Gauss.gC_monomial_near | exact GlobalTheory.PMon.Gauss.gC_monomial_near | (intros; apply GlobalTheory.PMon.Gauss.gC_monomial_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisedGlobalCocyclesInLocalSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisedGlobalCocyclesInLocalSpan
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.LocCoc

theorem factor {O K Γ X W : Type} [CommRing O] [IsNoetherianRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) [Group Γ] [Fintype X] [AddCommGroup W] [Module O W] {n : ℕ}
    (P : X → Prop) (A : X → (Γ →* Matrix (Fin n) (Fin n) O)) (E : X → Matrix (Fin n) (Fin n) O)
    (y : Γ → X → Matrix (Fin n) (Fin n) O) (hy : ∀ γ x, y γ x = (A x γ - 1) * E x)
    (φ : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] W) (ρ : Γ → W →ₗ[O] W)
    (h1 : ∀ γ δ, φ ((fun x => A x γ) * y δ) = ρ γ (φ (y δ)))
    (h0 : ∀ z ∈ Submodule.span O (Set.range y), (∀ x, P x → z x = 0) → φ z = 0) :
    ∃ (a : ℕ) (q : Fin a → X) (_ : ∀ j, P (q j)) (E' : Fin a → Fin n → K)
      (Y : Submodule O (Fin a → Fin n → K)) (_ : Y.FG)
      (hst : ∀ γ : Γ, ∀ z ∈ Y, (fun j => (mapM (algebraMap O K) (A (q j)) γ).mulVec (z j)) ∈ Y)
      (hE : ∀ γ : Γ, (fun j => (mapM (algebraMap O K) (A (q j)) γ).mulVec (E' j) - E' j) ∈ Y)
      (φ' : ↥Y →ₗ[O] W),
      (∀ (γ : Γ) (z : ↥Y), φ' ⟨_, hst γ z.1 z.2⟩ = ρ γ (φ' z)) ∧ ∀ γ, φ' ⟨_, hE γ⟩ = φ (y γ) := by
  classical
  let e := (Fintype.equivFin ({x // P x} × Fin n)).symm
  let L : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] (Fin (Fintype.card ({x // P x} × Fin n)) → Fin n → K) :=
    { toFun := fun z j s => algebraMap O K (z (e j).1.1 s (e j).2)
      map_add' := fun a b => by funext j s; simp
      map_smul' := fun c a => by funext j s; simp [Algebra.smul_def] }
  have key : ∀ (γ : Γ) (z : X → Matrix (Fin n) (Fin n) O),
      (fun j => (mapM (algebraMap O K) (A (e j).1.1) γ).mulVec (L z j)) = L ((fun x => A x γ) * z) := by
    intro γ z
    funext j s
    show ∑ t, algebraMap O K (A (e j).1.1 γ s t) * algebraMap O K (z (e j).1.1 t (e j).2) =
      algebraMap O K (∑ t, A (e j).1.1 γ s t * z (e j).1.1 t (e j).2)
    simp
  let Y0 := Submodule.span O (Set.range y)
  have hmul : ∀ γ δ, (fun x => A x γ) * y δ = y (γ * δ) - y γ := by
    intro γ δ
    funext x
    simp only [Pi.mul_apply, Pi.sub_apply, hy, map_mul]
    noncomm_ring
  have hst0 : ∀ γ, ∀ z ∈ Y0, (fun x => A x γ) * z ∈ Y0 ∧ φ ((fun x => A x γ) * z) = ρ γ (φ z) := by
    intro γ z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨δ, rfl⟩ := hz
      refine ⟨?_, h1 γ δ⟩
      rw [hmul]
      exact Y0.sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb =>
      rw [mul_add, map_add (f := _), map_add (f := _), map_add (f := _), ha.2, hb.2]
      exact ⟨Y0.add_mem ha.1 hb.1, rfl⟩
    | smul c a _ ha =>
      rw [mul_smul_comm, map_smul, map_smul, map_smul, ha.2]
      exact ⟨Y0.smul_mem c ha.1, rfl⟩
  have hLE : ∀ γ, (fun j => (mapM (algebraMap O K) (A (e j).1.1) γ).mulVec (L E j) - L E j) = L (y γ) := by
    intro γ
    have : y γ = (fun x => A x γ) * E - E := by
      funext x
      simp [hy, sub_mul]
    rw [this, map_sub, ← key]
    rfl
  let L0 := L.domRestrict Y0
  have hker : LinearMap.ker L0 ≤ LinearMap.ker (φ.domRestrict Y0) := by
    intro z hz
    refine h0 z.1 z.2 fun x hx => ?_
    ext s t
    apply hinj
    have := congrFun (congrFun (LinearMap.mem_ker.mp hz) (e.symm (⟨x, hx⟩, t))) s
    simpa [L0, L] using this
  let φ' : ↥(LinearMap.range L0) →ₗ[O] W :=
    ((LinearMap.ker L0).liftQ (φ.domRestrict Y0) hker) ∘ₗ (L0.quotKerEquivRange.symm : _ →ₗ[O] _)
  have hφ' : ∀ (z : Y0) (h : L z.1 ∈ LinearMap.range L0), φ' ⟨L z.1, h⟩ = φ z.1 := by
    intro z h
    have : L0.quotKerEquivRange.symm ⟨L z.1, h⟩ = (LinearMap.ker L0).mkQ z :=
      L0.quotKerEquivRange_symm_apply_image z h
    simp only [φ', LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  refine ⟨_, fun j => (e j).1.1, fun j => (e j).1.2, L E, LinearMap.range L0, ?_, ?_, ?_, φ', ?_, ?_⟩
  · rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  · rintro γ _ ⟨z, rfl⟩
    exact ⟨⟨_, (hst0 γ z.1 z.2).1⟩, (key γ z.1).symm⟩
  · intro γ
    exact ⟨⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩, (hLE γ).symm⟩
  · rintro γ ⟨_, z, rfl⟩
    have h2 := hφ' ⟨_, (hst0 γ z.1 z.2).1⟩ ⟨⟨_, (hst0 γ z.1 z.2).1⟩, rfl⟩
    have h3 := hφ' z ⟨z, rfl⟩
    refine Eq.trans (Eq.trans (congrArg φ' (Subtype.ext ?_)) h2) ?_
    · exact key γ z.1
    rw [(hst0 γ z.1 z.2).2, ← h3]
    rfl
  · intro γ
    have h2 := hφ' ⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩ ⟨⟨y γ, Submodule.subset_span ⟨_, rfl⟩⟩, rfl⟩
    exact Eq.trans (congrArg φ' (Subtype.ext (hLE γ))) h2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (S : IdempotentChoiceData D.nd i)

theorem inR'_tw (γ : GE D.nd) : InR' D.nd r S fun x' => rTwO D.nd i r (S.p x') γ := by
  refine ⟨1, fun _ => algebraMap (D.nd.O i) _ (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i), fun _ => γ,
    fun _ => S.T'.algebraMap_mem _, ?_⟩
  funext x'
  simp [rTwO, twistM]

theorem inR'_one : InR' D.nd r S 1 := by
  refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, ?_⟩
  funext x'
  simp

theorem inY_yg (γ : GE D.nd) : InY D.nd r S (yg D.nd r S γ) :=
  ⟨1, fun _ => 1, fun _ => γ, fun _ => inR'_one i r S, by simp⟩

theorem inY_of_span (z : S.X' → MatN D.nd i)
    (hz : z ∈ Submodule.span (D.nd.O i) (Set.range (yg D.nd r S))) : InY D.nd r S z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨δ, rfl⟩ := hz
    exact inY_yg i r S δ
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, fun k => k.elim0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, a, γ, ha, rfl⟩ := ha
    obtain ⟨m', a', γ', ha', rfl⟩ := hb
    refine ⟨m + m', Fin.append a a', Fin.append γ γ', fun k => ?_, ?_⟩
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) k
      · simpa using ha k
      · simpa using ha' k
    · rw [Fin.sum_univ_add]
      simp
  | smul c a _ ha =>
    obtain ⟨m, a, γ, ha, rfl⟩ := ha
    refine ⟨m, fun k => c • a k, γ, fun k => ?_, ?_⟩
    · obtain ⟨m', f, g, hf, h⟩ := ha k
      refine ⟨m', fun j => c • f j, g, fun j => S.T'.smul_mem (hf j) c, ?_⟩
      funext x'
      simp [h, Finset.smul_sum, mul_smul]
    · simp [Finset.smul_sum]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem inCut_of_cocW (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i))
    (hψ : ∀ γ, ψ (fun x' => rTwO D.nd i r (S.p x') γ) = M γ)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (f : GE D.nd → KOG (D.nd.O i) k) (hf : f ∈ cocW i r S Xs ψ) : InCut i r Xs M w hw f := by
  unfold cocW at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, h1, h0, rfl⟩ := hf
    obtain ⟨a, q, hq, E', Y, hY, hst, hE, φ', h2, h3⟩ :=
      factor (K := KK D.nd i) (IsFractionRing.injective _ _) (fun x' => S.p x' ∈ Xs)
        (fun x' => rTwO D.nd i r (S.p x')) (Eel D.nd S) (yg D.nd r S)
        (fun γ x' => by simp [yg, rTwO, twistM, sub_mul]) φ (fun γ => WKG M γ)
        (fun γ δ => by
          rw [h1 _ (inR'_tw i r S γ) _ (inY_yg i r S δ), hψ]
          obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (φ (yg D.nd r S δ))
          rw [← hu]
          rfl)
        (fun z hz => h0 z (inY_of_span i r S z hz))
    apply Submodule.subset_span
    refine ⟨a, fun j => S.p (q j), hq, E', Y, hY, hst, hE, φ', h2, ?_⟩
    funext g
    exact congrArg (Br.phi (D.nbr i w hw) k) (h3 _).symm
  | zero =>
    have e : locFun i M w hw 0 = 0 := by
      funext g
      exact (Br.phi (D.nbr i w hw) k).map_zero
    unfold InCut
    rw [e]
    exact Submodule.zero_mem _
  | add f f' _ _ h h' =>
    have e : locFun i M w hw (f + f') = locFun i M w hw f + locFun i M w hw f' := by
      funext g
      exact (Br.phi (D.nbr i w hw) k).map_add _ _
    unfold InCut at *
    rw [e]
    exact Submodule.add_mem _ h h'
  | smul c f _ h =>
    have e : locFun i M w hw (c • f) =
        ((D.nbr i w hw).eO c : Br.OLL D.nbr i w hw) • locFun i M w hw f := by
      funext g
      exact (Br.phi (D.nbr i w hw) k).map_smulₛₗ c _
    unfold InCut at *
    rw [e]
    exact Submodule.smul_mem _ _ h

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ cocRho i r S Xs, InCut i r Xs (WpO D.nd i ρ π) w hw f) ∧ ∀ c : Fin D.R.t, ∀ f ∈ cocChi i r S Xs c, InCut i r Xs (chiRatO D.nd i ((c : ℕ) + 1)) w hw f := by
  intro D i r ρ π Xs S _ hG _ w hw
  obtain ⟨-, hdec, hψ, -, -, -, -, -, -, ⟨hπ, -⟩, -⟩ := hG
  have key : ∀ γ u, (((S.ψρ fun x' => rTwO D.nd i r (S.p x') γ).map (toK D.nd i)).mulVec (S.e u).1,
      fun c : Fin D.R.t => toK D.nd i (S.ψχ c fun x' => rTwO D.nd i r (S.p x') γ) * (S.e u).2 c) =
      toK D.nd i (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        ((mapM (toK D.nd i) (rhoO D.nd i ρ π) γ).mulVec (S.e u).1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) γ : (D.nd.O i)ˣ) : D.nd.O i) * (S.e u).2 c) := by
    intro γ u
    rw [← hψ _ (inR'_tw i r S γ) u, ← hdec, ← map_smul, hπ, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [mapM, rTwO, twistM]
  refine ⟨fun f hf => inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf,
    fun c f hf => inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf⟩
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.1 p) (key γ (S.e.symm (Pi.single q 1, 0)))
    simpa [mapM, WpO, twistM] using h
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.2 c) (key γ (S.e.symm (0, Pi.single c 1)))
    obtain rfl : p = q := Subsingleton.elim _ _
    simpa [chiRatO, twistM, mul_comm] using h

end GlobalTheory.Cut.LocCoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisedGlobalCocyclesInLocalSpanStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localised_global_cocycles_in_local_span : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ cocRho i r S Xs, InCut i r Xs (WpO D.nd i ρ π) w hw f) ∧ ∀ c : Fin D.R.t, ∀ f ∈ cocChi i r S Xs c, InCut i r Xs (chiRatO D.nd i ((c : ℕ) + 1)) w hw f := by
  first | exact @GlobalTheory.Cut.LocCoc.main | exact GlobalTheory.Cut.LocCoc.main | (intros; apply GlobalTheory.Cut.LocCoc.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfPowEqOneOfValLt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRootEqOne
namespace GlobalTheory.RootValuationOne

open Finset

theorem sub_pow_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {x y : Ω}
    (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1) (hd : A.valuation (x - y) < 1) (i : ℕ) :
    A.valuation (x ^ i - y ^ i) < 1 := by
  rw [← geom_sum₂_mul, map_mul]
  have hs : A.valuation (∑ j ∈ range i, x ^ j * y ^ (i - 1 - j)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro j _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one' hx _) (pow_le_one' hy _)
  calc _ ≤ 1 * A.valuation (x - y) := by gcongr
    _ < 1 := by rw [one_mul]; exact hd

theorem val_root_eq_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ} (hn0 : n ≠ 0)
    {x : Ω} (hx : x ^ n = 1) : A.valuation x = 1 := by
  have h : A.valuation x ^ n = 1 := by rw [← map_pow, hx, map_one]
  rcases lt_trichotomy (A.valuation x) 1 with h' | h' | h'
  · exact absurd h (pow_lt_one₀ zero_le' h' hn0).ne
  · exact h'
  · exact absurd h (one_lt_pow₀ h' hn0).ne'

theorem main : ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) (n : ℕ),
    ¬(ValuationSubring.valuation A : Ω → ValuationSubring.ValueGroup A) (↑n : Ω) < (1 : ValuationSubring.ValueGroup A) →
    ∀ {ξ ξ' : Ω}, ξ ^ n = (1 : Ω) → ξ' ^ n = (1 : Ω) →
    (ValuationSubring.valuation A : Ω → ValuationSubring.ValueGroup A) (ξ - ξ') < (1 : ValuationSubring.ValueGroup A) → ξ = ξ' := by
  intro Ω _ A n hn ξ ξ' h1 h2 hd
  have hn0 : n ≠ 0 := by rintro rfl; apply hn; simp
  have hv1 := val_root_eq_one A hn0 h1
  have hv2 := val_root_eq_one A hn0 h2
  by_contra hne
  have hs : ∑ i ∈ range n, ξ ^ i * ξ' ^ (n - 1 - i) = 0 := by
    have := geom_sum₂_mul ξ ξ' n
    rw [h1, h2, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hlt : A.valuation (∑ i ∈ range n, (ξ ^ i * ξ' ^ (n - 1 - i) - ξ' ^ (n - 1))) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro i hi
    have hi' : i + (n - 1 - i) = n - 1 := by
      have := mem_range.mp hi; omega
    have e : ξ ^ i * ξ' ^ (n - 1 - i) - ξ' ^ (n - 1) = (ξ ^ i - ξ' ^ i) * ξ' ^ (n - 1 - i) := by
      rw [sub_mul, ← pow_add, hi']
    rw [e, map_mul, map_pow, hv2, one_pow, mul_one]
    exact sub_pow_lt_one A hv1.le hv2.le hd i
  rw [sum_sub_distrib, hs, sum_const, card_range, zero_sub, Valuation.map_neg, nsmul_eq_mul,
    map_mul, map_pow, hv2, one_pow, mul_one] at hlt
  exact hn hlt

end GlobalTheory.RootValuationOne
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.TameCharDet

open scoped Pointwise

theorem eq_of_pow_eq_one_of_val_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ)
    (hn : ¬ A.valuation (n : Ω) < 1) {ξ ξ' : Ω} (h : ξ ^ n = 1) (h' : ξ' ^ n = 1)
    (hlt : A.valuation (ξ - ξ') < 1) : ξ = ξ' := by
  first
  | exact @_root_.GlobalTheory.RootValuationOne.main
  | exact _root_.GlobalTheory.RootValuationOne.main
  | (apply _root_.GlobalTheory.RootValuationOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootValuationOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootValuationOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootValuationOne.main ..)

theorem eq_of_tameChar : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ γ : Formalism.ConjugateSelfDual.G E Ω, TameGenAt A γ → ∀ (K : Type) [Field K] [TopologicalSpace K] [T2Space K] (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ), Continuous r → ∀ n : ℕ, 0 < n → ((n : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ σ ∈ Ine (F := E) A, r σ ^ n = 1) → ∀ (π : Ω) (e : E), π ≠ 0 → π ^ n = algebraMap E Ω e → orderOf (γ π / π) = n → ∀ σ ∈ Ine (F := E) A, A.valuation (σ π / π - γ π / π) < 1 → r σ = r γ := by
  intro E Ω _ _ _ _ _ v A hA γ hγ K _ _ _ r hr n hn hnv hI π e hπ he hord σ hσ hσv
  have hn0 : n ≠ 0 := hn.ne'
  have hnA : ¬ A.valuation (n : Ω) < 1 := by
    intro h
    apply hnv
    rw [← hA]
    simpa using h
  set ζ := γ π / π with hζ
  have hζn : ζ ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one ζ
  have hγn : r γ ^ n = 1 := hI γ hγ.1
  have hred : ∀ {M : Type} [Monoid M] (x : M), x ^ n = 1 → ∀ a : ℕ, x ^ a = x ^ (a % n) := by
    intro M _ x hx a
    conv_lhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hx, one_pow, one_mul]
  have hvζ : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ n = 1 := by rw [← map_pow, hζn, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with hl | he | hg
    · exact absurd hp (pow_lt_one₀ zero_le' hl hn0).ne
    · exact he
    · exact absurd hp (one_lt_pow₀ hg hn0).ne'

  have hfixζ : ∀ τ ∈ Ine (F := E) A, τ ζ = ζ := by
    intro τ hτ
    refine eq_of_pow_eq_one_of_val_lt A n hnA ?_ hζn (hτ.2 ζ hvζ.le)
    rw [← map_pow, hζn, map_one]

  have hfixπ : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → τ π = π := by
    intro τ hτ
    have h1 : (τ π / π) ^ n = 1 := by
      rw [div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
      rw [← he]; exact pow_ne_zero _ hπ
    have h2 := eq_of_pow_eq_one_of_val_lt A n hnA h1 (one_pow n) (hτ π hπ)
    rwa [div_eq_one_iff_eq hπ] at h2

  have hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → r τ = 1 := by
    intro τ hτ
    by_contra hne
    have hd : orderOf (r τ) ∣ n := orderOf_dvd_of_pow_eq_one (hI τ (GlobalTheory.TameGenPowers.wild_mem_Ine hτ))
    have hne1 : orderOf (r τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
    have hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := by
      intro h
      apply hnv
      obtain ⟨c, hc⟩ := hd
      rw [hc, hk]
      push_cast
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)
    have h1 : r (τ ^ k) = 1 := by
      refine GlobalTheory.TameGenPowers.eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _
        (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
      rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
    rw [map_pow] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    have ho : orderOf (r τ) ≠ 0 := fun h => hn0 (by simpa [h] using hd)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact ho (by simpa using hk)
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
    rw [hk] at h3
    have := hl.two_le
    have := Nat.pos_of_ne_zero hk0
    nlinarith

  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  haveI : FiniteDimensional E (IntermediateField.adjoin E {π}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hHo : IsOpen ((IntermediateField.adjoin E {π}).fixingSubgroup : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hfixH : ∀ τ g : Formalism.ConjugateSelfDual.G E Ω, g ∈ (IntermediateField.adjoin E {π}).fixingSubgroup →
      (τ * g) π = τ π := by
    intro τ g hg
    rw [AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg π
      (IntermediateField.mem_adjoin_simple_self E π)]
  have hopen : ∀ U : Set (Formalism.ConjugateSelfDual.G E Ω), (∀ τ ∈ U, ∀ g ∈ (IntermediateField.adjoin E {π}).fixingSubgroup,
      τ * g ∈ U) → IsOpen U := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    rw [← map_mul_left_nhds_one τ]
    exact Filter.mem_map.2 (Filter.mem_of_superset (hHo.mem_nhds (one_mem _)) fun g hg => hU τ hτ g hg)
  have hloc : ∀ c : Ω, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | τ π = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopen _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [hfixH τ g hg]
  let T : Set (Formalism.ConjugateSelfDual.G E Ω) := ⋃ a ∈ Finset.range n, {τ | r τ = r γ ^ a ∧ τ π = ζ ^ a * π}
  have hTc : IsClosed T := by
    refine isClosed_biUnion_finset fun a _ => ?_
    exact (isClosed_singleton.preimage hr).inter (hloc _)

  let P : Formalism.ConjugateSelfDual.G E Ω → Prop := fun τ =>
    τ ∈ Ine (F := E) A ∧ ∃ a : ℕ, r τ = r γ ^ a ∧ τ π = ζ ^ a * π
  have hP : ∀ τ ∈ Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}), P τ := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hγ.1, 1, (pow_one _).symm, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ]⟩
      · exact ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hx, 0, by rw [hw x hx, pow_zero],
          by rw [hfixπ x hx, pow_zero, one_mul]⟩
    | one => exact ⟨one_mem _, 0, by rw [map_one, pow_zero], by rw [pow_zero, one_mul]; rfl⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      obtain ⟨hyI, b, hb, hbπ⟩ := ihy
      refine ⟨mul_mem hxI hyI, a + b, by rw [map_mul, ha, hb, pow_add], ?_⟩
      rw [AlgEquiv.mul_apply, hbπ, map_mul, map_pow, hfixζ x hxI, haπ, pow_add]
      ring
    | inv x _ ihx =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      have hiI : x⁻¹ ∈ Ine (F := E) A := inv_mem hxI
      have hex : a * (n - 1) + a = a * n := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      refine ⟨hiI, a * (n - 1), ?_, ?_⟩
      · rw [map_inv, ha]
        symm
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_add, hex, pow_mul', hγn, one_pow]
      · have hxx : (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) (x π) = π := by
          rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
        have h1 : π = ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
          have h2 := congrArg (fun y => (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) y) haπ
          rw [hxx, map_mul, map_pow, hfixζ _ hiI] at h2
          exact h2
        calc (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π = ζ ^ (a * (n - 1) + a) * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
              rw [hex, pow_mul', hζn, one_pow, one_mul]
          _ = ζ ^ (a * (n - 1)) * (ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π) := by ring
          _ = ζ ^ (a * (n - 1)) * π := by rw [← h1]
  have hST : ((Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
        Set (Formalism.ConjugateSelfDual.G E Ω)) ⊆ T := by
    intro τ hτ
    obtain ⟨-, a, ha, haπ⟩ := hP τ hτ
    refine Set.mem_biUnion (x := a % n) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hn))) ?_
    exact ⟨by rw [ha, hred _ hγn a], by rw [haπ, hred _ hζn a]⟩
  have hσT : σ ∈ T := closure_minimal hST hTc (hγ.2 hσ)
  obtain ⟨a, ha, haπ⟩ : ∃ a : ℕ, r σ = r γ ^ a ∧ σ π = ζ ^ a * π := by
    simp only [T, Set.mem_iUnion] at hσT
    obtain ⟨a, -, h⟩ := hσT
    exact ⟨a, h⟩
  have hq : σ π / π = ζ ^ a := by rw [haπ, mul_div_assoc, div_self hπ, mul_one]
  rw [hq] at hσv
  have hζa : ζ ^ a = ζ := by
    refine eq_of_pow_eq_one_of_val_lt A n hnA ?_ hζn hσv
    rw [← pow_mul, mul_comm, pow_mul, hζn, one_pow]
  have hmod : a ≡ 1 [MOD n] := by
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · have h1 : orderOf ζ = 1 := orderOf_eq_one_iff.2 (by rw [← hζa, pow_zero])
      rw [← hord, h1]; exact Nat.modEq_one
    · have hζ0 : ζ ≠ 0 := by
        intro h; rw [h, zero_pow hn0] at hζn; exact zero_ne_one hζn
      have h1 : ζ ^ (a - 1) = 1 := by
        have h3 : ζ ^ (a - 1) * ζ = 1 * ζ := by
          rw [← pow_succ, Nat.sub_add_cancel ha0, hζa, one_mul]
        exact mul_right_cancel₀ hζ0 h3
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at h2
      exact ((Nat.modEq_iff_dvd' ha0).2 h2).symm
  rw [ha]
  conv_rhs => rw [← pow_one (r γ)]
  exact (pow_eq_pow_iff_modEq).2 (hmod.of_dvd (orderOf_dvd_of_pow_eq_one hγn))

end GlobalTheory.TameCharDet
end
