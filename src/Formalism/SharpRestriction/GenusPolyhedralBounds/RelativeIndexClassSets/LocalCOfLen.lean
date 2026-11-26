module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ReductionUniformizerSmulMem
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsIrreducibleLocToCompl
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IteratedWeightAtVanishingOrder
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HasseJidPow

@[expose] public section

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.JWMggWMem
section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.GeneratorsLeRestrictedSpan
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO))

def In64 : Prop :=
  ∀ x ∈ Submodule.span (Kp X la G.N) (sectionMonomialGenerators G la), rhoK X la G.w wF (a0 D j T) T x = 0 → x = 0

theorem rhoK_Zg (hDT : WeightFamilies.dimY D j ≤ T) (hal : ∀ k, ∑ i, G.alz k i = a0 D j T)
    {f : ↥(Vw X la G.N (addL wF wL T))} (hf : f ∈ Zg G la) : rhoK X la G.w wF (a0 D j T) T f = 0 := by
  obtain ⟨k, hk⟩ := hf
  rw [rhoK_eq_zero_iff, mem_Fil]
  refine ⟨f.2, a0 D j T, le_rfl, ?_⟩
  rw [hk, zK, mul_left_comm, Nat.sub_self]
  refine secPow_mul_mem_Mon X la G.w (hal k) ?_
  rw [addL_zero]
  have h0 : emb X la G.N (X.inc _ (G.th0 k)) ∈ Vw X la G.N (addL wF wL (WeightFamilies.dimY D j)) :=
    emb_mem_Vw X la G.N _ (G.th0 k)
  have h1 := sec_pow_mul_mem X la G.w 0 wF (WeightFamilies.dimY D j) (a0 D j T) h0
  have h2 : WeightFamilies.dimY D j + a0 D j T = T := by unfold a0; omega
  rwa [h2] at h1

theorem ZK_le_ker (hDT : WeightFamilies.dimY D j ≤ T) (hal : ∀ k, ∑ i, G.alz k i = a0 D j T) :
    ZK G la ≤ LinearMap.ker (rhoK X la G.w wF (a0 D j T) T) :=
  Submodule.span_le.2 fun _ hf => rhoK_Zg G la hDT hal hf

theorem NovK_eq : NovK G la = Submodule.span (Kp X la G.N) (sectionMonomialGenerators G la) ⊔ ZK G la := by
  unfold NovK N1 Zl ZK
  rw [← Submodule.span_union, Submodule.span_span_of_tower, Submodule.span_union]

theorem generators_le_restricted_span : N1 G la ≤ (NovK G la).restrictScalars (Op X la G.N) :=
  fun _ hx => Submodule.subset_span (Submodule.mem_sup_left hx)

theorem ZK_le_NovK : ZK G la ≤ NovK G la := by
  rw [NovK_eq]; exact le_sup_right

theorem generators_le_poleSpan (e : ℕ) : N1 G la ≤ Np G la e := le_sup_of_le_left le_sup_right

theorem Zm_le_Np (e : ℕ) : Zm G la ≤ Np G la e := le_sup_right

theorem Np_le_NovK (e : ℕ) : Np G la e ≤ (NovK G la).restrictScalars (Op X la G.N) :=
  sup_le (sup_le inf_le_right (generators_le_restricted_span G la)) (fun _ hx => ZK_le_NovK G la hx.2)

theorem poleSpan_le_integralForms (e : ℕ) (h : N1 G la ≤ M1 X la G.N (addL wF wL T)) : Np G la e ≤ M1 X la G.N (addL wF wL T) := by
  refine sup_le (sup_le (inf_le_left.trans ?_) h) inf_le_left
  rintro _ ⟨y, hy, rfl⟩
  exact Submodule.smul_mem _ _ hy

theorem Zl_le_Zm (h : Zl G la ≤ M1 X la G.N (addL wF wL T)) : Zl G la ≤ Zm G la :=
  le_inf h (Submodule.span_le.2 fun _ hx => Submodule.subset_span hx)

theorem ker_rhoN (e : ℕ) (h64 : In64 G la) (hN : N1 G la ≤ M1 X la G.N (addL wF wL T)) (hDT : WeightFamilies.dimY D j ≤ T)
    (hal : ∀ k, ∑ i, G.alz k i = a0 D j T) :
    LinearMap.ker (rhoN G la e) = (Zm G la).comap (Np G la e).subtype := by
  ext ⟨x, hx⟩
  rw [LinearMap.mem_ker, Submodule.mem_comap]
  show rhoK X la G.w wF (a0 D j T) T x = 0 ↔ x ∈ Zm G la
  constructor
  · intro h
    refine ⟨poleSpan_le_integralForms G la e hN hx, ?_⟩
    have hx' : x ∈ NovK G la := Np_le_NovK G la e hx
    rw [NovK_eq] at hx'
    obtain ⟨n, hn, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    have hz0 : rhoK X la G.w wF (a0 D j T) T z = 0 := ZK_le_ker G la hDT hal hz
    rw [map_add (f := _), hz0, add_zero] at h
    rw [h64 n hn h, zero_add]
    exact hz
  · intro h
    exact ZK_le_ker G la hDT hal h.2

theorem map_reduction_generators_eq (e : ℕ) : ((N1 G la).comap (Np G la e).subtype).map (rhoN G la e) = firstLength_le_prime_bound G la T := by
  rw [reducedGenerators_eq_map]
  ext y
  constructor
  · rintro ⟨⟨x, hx⟩, hx1, rfl⟩; exact ⟨x, hx1, rfl⟩
  · rintro ⟨x, hx1, rfl⟩; exact ⟨⟨x, generators_le_poleSpan G la e hx1⟩, hx1, rfl⟩

theorem rhoN_mem {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (S : Scal B) (e : ℕ) (hC : Q.InCurve) (hT : Q.InTie S)
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (hth : ∀ i, G.th' i ∈ B.Mlat j wF) (hDT : WeightFamilies.dimY D j ≤ T)
    (hal : ∀ k, ∑ i, G.alz k i = a0 D j T) (x : ↥(Np G la e)) : rhoN G la e x ∈ Q.AAp T (Q.mm S T e) := by
  have h : Np G la e ≤ (Q.AAp T (Q.mm S T e)).comap (rhoO G la) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact fun y hy => reduction_uniformizer_smul_mem Q S hC hT hw e hy.1
    · intro y hy
      refine AA_le_AAp Q _ (reduced_generators_le Q S hC hT hw hth ?_)
      rw [reducedGenerators_eq_map]
      exact ⟨y, hy, rfl⟩
    · intro y hy
      have h0 : rhoK X la G.w wF (a0 D j T) T y = 0 := ZK_le_ker G la hDT hal hy.2
      show rhoK X la G.w wF (a0 D j T) T y ∈ Q.AAp T (Q.mm S T e)
      rw [h0]
      exact Submodule.zero_mem _
  exact h x.2

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsCoeffOfMemSpan
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

section Abstract

open MvPolynomial

variable {k K L : Type*} [CommRing k] [Field K] [CommRing L] [Algebra k L] [Algebra K L]
  {n δ : ℕ} (y : Fin n → L) (θ : Fin δ → L) (J : ℕ → Submodule K L) (Δ : Fin n → Derivation k L L)

theorem ind_mono (hy : ∀ l l', Δ l (y l') = if l = l' then 1 else 0) (l : Fin n) (m : Fin n →₀ ℕ) :
    Δ l (aeval y (monomial m (1 : K))) = aeval y (pderiv l (monomial m (1 : K))) := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [show monomial (f + g) (1 : K) = monomial f 1 * monomial g 1 by rw [monomial_mul, one_mul], map_mul,
      Derivation.leibniz, Derivation.leibniz, hf, hg, map_add, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
      map_mul, map_mul]
  | single i a =>
    rw [← X_pow_eq_monomial, map_pow, aeval_X, Derivation.leibniz_pow, Derivation.leibniz_pow, hy, pderiv_X,
      map_nsmul, smul_eq_mul, smul_eq_mul, map_mul, map_pow, aeval_X]
    by_cases h : l = i
    · subst h; simp
    · rw [if_neg h, Pi.single_eq_of_ne (Ne.symm h), map_zero]

theorem aeval_monomial_eq_smul (m : Fin n →₀ ℕ) (c : K) :
    aeval y (monomial m c) = c • aeval y (monomial m (1 : K)) := by
  rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]

theorem ind_hom_mem (hY : ∀ (m : Fin n →₀ ℕ) i, aeval y (monomial m (1 : K)) * θ i ∈ J m.degree) {a : ℕ}
    {p : MvPolynomial (Fin n) K} (hp : p.IsHomogeneous a) (i : Fin δ) : aeval y p * θ i ∈ J a := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← support_sum_monomial_coeff p, map_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hd : m.degree = a := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero h)
  rw [aeval_monomial_eq_smul, smul_mul_assoc, ← hd]
  exact Submodule.smul_mem _ _ (hY m i)

theorem ind_der_mem (hy : ∀ l l', Δ l (y l') = if l = l' then 1 else 0) (hθ : ∀ l i, Δ l (θ i) = 0)
    (hK : ∀ l (c : K), ∃ c' : K, Δ l (algebraMap K L c) = algebraMap K L c')
    (hY : ∀ (m : Fin n →₀ ℕ) i, aeval y (monomial m (1 : K)) * θ i ∈ J m.degree) {a : ℕ}
    {p : MvPolynomial (Fin n) K} (hp : p.IsHomogeneous a) (l : Fin n) (i : Fin δ) :
    Δ l (aeval y p * θ i) - aeval y (pderiv l p) * θ i ∈ J a := by
  rw [← support_sum_monomial_coeff p]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hd : m.degree = a := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero h)
  obtain ⟨c', hc'⟩ := hK l (AddMonoidAlgebra.coeff p m)
  have e1 : Δ l (aeval y (monomial m (AddMonoidAlgebra.coeff p m)) * θ i) =
      c' • (aeval y (monomial m (1 : K)) * θ i) + aeval y (pderiv l (monomial m (AddMonoidAlgebra.coeff p m))) * θ i := by
    have e2 : pderiv l (monomial m (AddMonoidAlgebra.coeff p m)) = AddMonoidAlgebra.coeff p m • pderiv l (monomial m (1 : K)) := by
      rw [← Derivation.map_smul, smul_monomial, smul_eq_mul, mul_one]
    rw [e2, map_smul, aeval_monomial_eq_smul, Algebra.smul_def, Derivation.leibniz, hθ, smul_zero, zero_add,
      Derivation.leibniz, hc', ind_mono y Δ hy]
    simp only [smul_eq_mul, Algebra.smul_def]
    ring
  rw [e1, add_sub_cancel_right, ← hd]
  exact Submodule.smul_mem _ _ (hY m i)

variable [CharZero K]

theorem ind_claim (hy : ∀ l l', Δ l (y l') = if l = l' then 1 else 0) (hθ : ∀ l i, Δ l (θ i) = 0)
    (hK : ∀ l (c : K), ∃ c' : K, Δ l (algebraMap K L c) = algebraMap K L c')
    (hJ : ∀ l a x, x ∈ J (a + 1) → Δ l x ∈ J a) (hanti : ∀ a, J (a + 1) ≤ J a)
    (hY : ∀ (m : Fin n →₀ ℕ) i, aeval y (monomial m (1 : K)) * θ i ∈ J m.degree)
    (hbase : ∀ c : Fin δ → K, ∑ i, c i • θ i ∈ J 1 → c = 0) (a : ℕ) :
    ∀ c : Fin δ → MvPolynomial (Fin n) K, (∀ i, ∀ m ∈ (c i).support, m.degree < a) →
      ∑ i, aeval y (c i) * θ i ∈ J a → c = 0 := by
  induction a with
  | zero =>
    intro c hc _
    funext i
    rw [Pi.zero_apply, ← MvPolynomial.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
    intro m hm
    exact absurd (hc i m hm) (Nat.not_lt_zero _)
  | succ a ih =>
    intro c hc hmem
    rcases Nat.eq_zero_or_pos a with rfl | ha
    ·
      have hC : ∀ i, c i = C (AddMonoidAlgebra.coeff (c i) 0) := by
        intro i
        ext m
        rw [coeff_C]
        split_ifs with h
        · rw [← h]
        · by_contra h'
          have := hc i m (MvPolynomial.mem_support_iff.mpr h')
          exact h ((Finsupp.degree_eq_zero_iff m).mp (by omega)).symm
      have h0 := hbase (fun i => AddMonoidAlgebra.coeff (c i) 0) (by
        have e : ∑ i, aeval y (c i) * θ i = ∑ i, AddMonoidAlgebra.coeff (c i) 0 • θ i :=
          Finset.sum_congr rfl fun i _ => by
            conv_lhs => rw [hC i]
            rw [aeval_C, Algebra.smul_def]
        rw [← e]; exact hmem)
      funext i
      have h0i : AddMonoidAlgebra.coeff (c i) 0 = 0 := congrFun h0 i
      rw [hC i, h0i, map_zero]
      rfl
    ·
      have hlow : (fun i => c i - homogeneousComponent a (c i)) = 0 := by
        apply ih
        · intro i m hm
          rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hm
          by_cases hd : m.degree = a
          · rw [if_pos hd, sub_self] at hm; exact absurd rfl hm
          · rw [if_neg hd, sub_zero] at hm
            have := hc i m (MvPolynomial.mem_support_iff.mpr hm)
            omega
        · have e : ∑ i, aeval y (c i - homogeneousComponent a (c i)) * θ i =
              ∑ i, aeval y (c i) * θ i - ∑ i, aeval y (homogeneousComponent a (c i)) * θ i := by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by rw [map_sub, sub_mul]
          rw [e]
          exact Submodule.sub_mem _ (hanti a hmem)
            (Submodule.sum_mem _ fun i _ => ind_hom_mem y θ J hY (homogeneousComponent_isHomogeneous a (c i)) i)
      have hhom : ∀ i, (c i).IsHomogeneous a := by
        intro i
        have := congrFun hlow i
        rw [Pi.zero_apply, sub_eq_zero] at this
        rw [this]; exact homogeneousComponent_isHomogeneous a (c i)

      have hpd : ∀ l, (fun i => pderiv l (c i)) = 0 := by
        intro l
        apply ih
        · intro i m hm
          have hd : m.degree = a - 1 := by
            by_contra h
            exact (MvPolynomial.mem_support_iff.mp hm) ((hhom i).pderiv.coeff_eq_zero h)
          omega
        · have h1 := hJ l a _ hmem
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum] at h1
          have h2 : ∑ i, (Δ l (aeval y (c i) * θ i) - aeval y (pderiv l (c i)) * θ i) ∈ J a :=
            Submodule.sum_mem _ fun i _ => ind_der_mem y θ J Δ hy hθ hK hY (hhom i) l i
          rw [Finset.sum_sub_distrib] at h2
          have := Submodule.sub_mem _ h1 h2
          rwa [sub_sub_cancel] at this
      funext i
      have hE := (hhom i).sum_X_mul_pderiv
      have h0 : ∑ l, X l * pderiv l (c i) = 0 :=
        Finset.sum_eq_zero fun l _ => by rw [congrFun (hpd l) i, Pi.zero_apply, mul_zero]
      rw [h0] at hE
      rw [Pi.zero_apply]
      exact (smul_eq_zero.mp hE.symm).resolve_left (by omega)

end Abstract

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem der_sum_apply {k L ι : Type*} [CommRing k] [CommRing L] [Algebra k L] (s : Finset ι)
    (f : ι → Derivation k L L) (x : L) : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

section Concrete

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

@[instance_reducible] def LwAlgKl : Algebra (X.Kl la) (Lw X la w) := inferInstanceAs (Algebra (X.Kl la) (Localization.Away (sec X la w 0)))

attribute [local instance] LwAlgKl

def pdLw (p : Idx D j N) : Derivation (X.Kl la) (Lw X la w) (Lw X la w) := pdLc X la w p

theorem pdLw_algebraMap (p : Idx D j N) (x : Rp X la N) :
    pdLw X la w p (algebraMap (Rp X la N) (Lw X la w) x) = algebraMap (Rp X la N) (Lw X la w) (pdRp X la N p x) :=
  pdLc_algebraMap X la w p x

theorem pdLw_algebraMap_Kp (p : Idx D j N) (c : Kp X la N) :
    pdLw X la w p (algebraMap (Kp X la N) (Lw X la w) c) = algebraMap (Kp X la N) (Lw X la w) (pdKp X la N p c) := by
  rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), pdLw_algebraMap, pdRp_algebraMap,
    ← IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w)]

theorem pdLw_mem (p : Idx D j N) (u : WeightFamilies.Wt D j) (a : ℕ) {x : Lw X la w} (hx : x ∈ JHfr X la w u (a + 1)) :
    pdLw X la w p x ∈ JHfr X la w u a := by
  have h := hasse_jid_power X la w u (Finsupp.single p 1) (a + 1) x hx
  rw [Finsupp.sum_single_index rfl, Nat.add_sub_cancel] at h
  exact h

theorem pdLw_w0inv (p : Idx D j N) (hp : p.1 ≠ 0) : pdLw X la w p (w0inv X la w) = 0 := by
  have h := congrArg (pdLw X la w p) (section_mul_inverse_eq_one X la w)
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, pdLw_algebraMap, pdRp_sec, if_neg hp, map_zero, smul_zero,
    add_zero, smul_eq_mul] at h
  calc pdLw X la w p (w0inv X la w)
      = (algebraMap (Rp X la N) (Lw X la w) (sec X la w 0) * w0inv X la w) * pdLw X la w p (w0inv X la w) := by
        rw [section_mul_inverse_eq_one, one_mul]
    _ = w0inv X la w * (algebraMap (Rp X la N) (Lw X la w) (sec X la w 0) * pdLw X la w p (w0inv X la w)) := by ring
    _ = 0 := by rw [h, mul_zero]

def t0 (κ : Fin N) : Kp X la N := @algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (0, κ))

def dSec (l : Fin (WeightFamilies.dimY D j)) : Derivation (X.Kl la) (Lw X la w) (Lw X la w) :=
  ∑ κ, algebraMap (Kp X la N) (Lw X la w) (t0 X la κ) • pdLw X la w (l.succ, κ)

theorem dSec_apply (l : Fin (WeightFamilies.dimY D j)) (x : Lw X la w) :
    dSec X la w l x = ∑ κ, t0 X la κ • pdLw X la w (l.succ, κ) x := by
  unfold dSec
  rw [der_sum_apply]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Derivation.smul_apply, smul_eq_mul, Algebra.smul_def]

def ySec (l : Fin (WeightFamilies.dimY D j)) : Lw X la w := (sfr X la w l.succ : Lw X la w)

theorem dSec_ySec (l l' : Fin (WeightFamilies.dimY D j)) : dSec X la w l (ySec X la w l') = if l = l' then 1 else 0 := by
  have h1 : ∀ κ, pdLw X la w (l.succ, κ) (ySec X la w l') =
      if l = l' then algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wL (w κ))) * w0inv X la w else 0 := by
    intro κ
    unfold ySec
    rw [coe_sfr, frac_apply, pow_one, Derivation.leibniz, pdLw_w0inv X la w _ (Fin.succ_ne_zero l), smul_zero, zero_add,
      pdLw_algebraMap, pdRp_sec, smul_eq_mul]
    by_cases h : l = l'
    · rw [if_pos h, if_pos (by rw [h]), mul_comm]
    · rw [if_neg h, if_neg (fun e => h (Fin.succ_injective _ e)), map_zero, mul_zero]
  rw [dSec_apply]
  simp only [h1]
  by_cases h : l = l'
  · simp only [if_pos h]
    rw [← section_mul_inverse_eq_one X la w]
    unfold sec
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [← smul_mul_assoc]
    congr 1
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w)]
    rfl
  · simp only [if_neg h, smul_zero, Finset.sum_const_zero]

theorem dSec_emb (l : Fin (WeightFamilies.dimY D j)) (F : X.Forms) :
    dSec X la w l (algebraMap (Rp X la N) (Lw X la w) (emb X la N F)) = 0 := by
  rw [dSec_apply]
  refine Finset.sum_eq_zero fun κ _ => ?_
  rw [pdLw_algebraMap, pdRp_emb, map_zero, smul_zero]

theorem dSec_algebraMap_Kp (l : Fin (WeightFamilies.dimY D j)) (c : Kp X la N) :
    ∃ c' : Kp X la N, dSec X la w l (algebraMap (Kp X la N) (Lw X la w) c) = algebraMap (Kp X la N) (Lw X la w) c' := by
  refine ⟨∑ κ, t0 X la κ * pdKp X la N (l.succ, κ) c, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dSec_apply, map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [pdLw_algebraMap_Kp, Algebra.smul_def, map_mul]

theorem dSec_mem (l : Fin (WeightFamilies.dimY D j)) (u : WeightFamilies.Wt D j) (a : ℕ) (x : Lw X la w) (hx : x ∈ JHfr X la w u (a + 1)) :
    dSec X la w l x ∈ JHfr X la w u a := by
  rw [dSec_apply]
  exact Submodule.sum_mem _ fun κ _ => Submodule.smul_mem _ _ (pdLw_mem X la w _ u a hx)

theorem JHfr_succ_le (u : WeightFamilies.Wt D j) (a : ℕ) : JHfr X la w u (a + 1) ≤ JHfr X la w u a := by
  intro x hx
  have h1 : x ∈ JHs X la w u (a + 1) := hx
  rw [← Jid_pow_smul_HK] at h1
  have h2 : x ∈ Jid X la w ^ a • HK X la w u := Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ a)) le_rfl h1
  rw [Jid_pow_smul_HK] at h2
  exact h2

open MvPolynomial in
theorem aeval_ySec_monomial (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) :
    aeval (ySec X la w) (monomial m (1 : Kp X la N)) = frac X la w m.degree (secPow X la w m) := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.degree_eq_sum,
    ← coe_prod_sfr]
  show _ = (Frac0 X la w).val (∏ i, sfr X la w i.succ ^ m i)
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow]
  rfl

open MvPolynomial in
theorem ySec_monomial_mul_mem (u : WeightFamilies.Wt D j) (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) (F : B.Cusp j u) :
    aeval (ySec X la w) (monomial m (1 : Kp X la N)) * algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc u F)) ∈
      JHfr X la w u m.degree := by
  rw [aeval_ySec_monomial, ← frac_zero, frac_mul, mem_JHfr]
  refine ⟨0, _, secPow_mul_mem_Mon X la w (Finsupp.degree_eq_sum m).symm ?_, by rw [add_comm]⟩
  rw [addL_zero]
  exact emb_mem_Vw X la N u F

end Concrete

section Final

open MvPolynomial

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
  (wF : WeightFamilies.Wt D j) (T : ℕ)

theorem Kp_charZero' : CharZero (Kp X la N) :=
  have := Kl_charZero X la
  charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective

def gN (θ : B.Cusp j wF) (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) : Rp X la N :=
  secPow X la w m * sec X la w 0 ^ (T - m.degree) * emb X la N (X.inc wF θ)

def phiN (θ : B.Cusp j wF) : MvPolynomial (Fin (WeightFamilies.dimY D j)) (Kp X la N) →ₗ[Kp X la N] Rp X la N :=
  (basisMonomials (Fin (WeightFamilies.dimY D j)) (Kp X la N)).constr (Kp X la N) (gN X la w wF T θ)

theorem phiN_monomial (θ : B.Cusp j wF) (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) (c : Kp X la N) :
    phiN X la w wF T θ (monomial m c) = c • gN X la w wF T θ m := by
  have e : monomial m c = c • basisMonomials (Fin (WeightFamilies.dimY D j)) (Kp X la N) m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  unfold phiN
  rw [e, map_smul, Module.Basis.constr_basis]

theorem frac_gN (θ : B.Cusp j wF) (m : Fin (WeightFamilies.dimY D j) →₀ ℕ) (hm : m.degree ≤ T) :
    frac X la w T (gN X la w wF T θ m) = aeval (ySec X la w) (monomial m (1 : Kp X la N)) *
      algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wF θ)) := by
  rw [aeval_ySec_monomial, ← frac_zero, frac_mul, ← frac_pow_mul X la w (m.degree + 0) (T - m.degree)]
  unfold gN
  rw [show m.degree + 0 + (T - m.degree) = T by omega]
  congr 1
  ring

theorem frac_phiN (θ : B.Cusp j wF) (p : MvPolynomial (Fin (WeightFamilies.dimY D j)) (Kp X la N))
    (hp : ∀ m ∈ p.support, m.degree ≤ T) :
    frac X la w T (phiN X la w wF T θ p) =
      aeval (ySec X la w) p * algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wF θ)) := by
  have key : ∀ (s : Finset (Fin (WeightFamilies.dimY D j) →₀ ℕ)) (f : (Fin (WeightFamilies.dimY D j) →₀ ℕ) → Kp X la N),
      (∀ m ∈ s, m.degree ≤ T) → frac X la w T (phiN X la w wF T θ (∑ m ∈ s, monomial m (f m))) =
        aeval (ySec X la w) (∑ m ∈ s, monomial m (f m)) *
          algebraMap (Rp X la N) (Lw X la w) (emb X la N (X.inc wF θ)) := by
    intro s f hs
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [phiN_monomial, map_smul, frac_gN X la w wF T θ m (hs m hm), aeval_monomial_eq_smul (ySec X la w) m (f m),
      smul_mul_assoc]
  have := key p.support (fun m => AddMonoidAlgebra.coeff p m) hp
  rwa [support_sum_monomial_coeff] at this

end Final

section Main

open MvPolynomial

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO))

theorem exists_coeff_of_mem_span {x : ↥(Vw X la G.N (addL wF wL T))}
    (hx : x ∈ Submodule.span (Kp X la G.N) (sectionMonomialGenerators G la)) :
    ∃ c : Fin G.del → MvPolynomial (Fin (WeightFamilies.dimY D j)) (Kp X la G.N),
      (∀ i, ∀ m ∈ (c i).support, m.degree < a0 D j T) ∧
        (x : Rp X la G.N) = ∑ i, phiN X la G.w wF T (G.th' i) (c i) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨al, i, hal, hx⟩ := hx
    refine ⟨fun i' => if i' = i then monomial (Finsupp.equivFunOnFinite.symm al) 1 else 0, ?_, ?_⟩
    · intro i' m hm
      dsimp only at hm
      by_cases h : i' = i
      · rw [if_pos h] at hm
        have := Finset.mem_singleton.mp (support_monomial_subset hm)
        rw [this, Finsupp.degree_eq_sum]
        exact hal
      · rw [if_neg h, support_zero] at hm
        exact absurd hm (Finset.notMem_empty _)
    · rw [Finset.sum_eq_single i]
      · dsimp only
        rw [if_pos rfl, phiN_monomial, one_smul, hx]
        unfold gN
        rw [Finsupp.degree_eq_sum]
        rfl
      · intro i' _ h
        dsimp only
        rw [if_neg h, map_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  | zero => exact ⟨0, fun i m hm => by simp at hm, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hxc⟩ := hx
    obtain ⟨c', hc', hyc⟩ := hy
    refine ⟨c + c', fun i m hm => ?_, ?_⟩
    · rcases Finset.mem_union.mp (support_add hm) with h | h
      · exact hc i m h
      · exact hc' i m h
    · rw [Submodule.coe_add, hxc, hyc, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, map_add (f := _)]
  | smul a x _ hx =>
    obtain ⟨c, hc, hxc⟩ := hx
    refine ⟨a • c, fun i m hm => hc i m (support_smul hm), ?_⟩
    rw [Submodule.coe_smul, hxc, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, map_smul]

attribute [local instance] LwAlgKl

theorem in64 (hB : InBasis G la) : ∀ x ∈ Submodule.span (Kp X la G.N) (sectionMonomialGenerators G la),
    rhoK X la G.w wF (a0 D j T) T x = 0 → x = 0 := by
  intro x hx h0
  have := Kp_charZero' X la (N := G.N)
  obtain ⟨c, hc, hxc⟩ := exists_coeff_of_mem_span G la hx

  have hbase : ∀ b : Fin G.del → Kp X la G.N,
      ∑ i, b i • algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) ∈ JHfr X la G.w wF 1 →
        b = 0 := by
    intro b hb
    have hlin : ∑ i, b i • tL G la i = 0 := by
      have e : ∑ i, b i • tL G la i = rho0 X la G.w wF
          (∑ i, b i • (⟨emb X la G.N (X.inc wF (G.th' i)), emb_mem_Vw X la G.N wF (G.th' i)⟩ : ↥(Vw X la G.N wF))) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
      rw [e, restriction_apply_eq_reduction, reduction_eq_zero_iff_mem_ideal_smul, ← pow_one (Jid X la G.w), mem_Jid_pow_smul_top, ← mem_JHfr, coe_toHK0]
      have e2 : algebraMap (Rp X la G.N) (Lw X la G.w) ((∑ i, b i • (⟨emb X la G.N (X.inc wF (G.th' i)),
          emb_mem_Vw X la G.N wF (G.th' i)⟩ : ↥(Vw X la G.N wF)) : ↥(Vw X la G.N wF)) : Rp X la G.N) =
          ∑ i, b i • algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [AddSubmonoidClass.coe_finsetSum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, Algebra.smul_def, map_mul,
          ← IsScalarTower.algebraMap_apply (Kp X la G.N) (Rp X la G.N) (Lw X la G.w), ← Algebra.smul_def]
      rw [e2]
      exact hb
    funext i
    exact Fintype.linearIndependent_iff.mp hB.1 b hlin i
  have hmem : ∑ i, aeval (ySec X la G.w) (c i) *
      algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) ∈ JHfr X la G.w wF (a0 D j T) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [rhoK_apply, toWK_eq_zero_iff, mem_Jid_pow_smul_top, ← mem_JHfr, coe_toHK, hxc, map_sum] at h0
    have e : ∀ i, frac X la G.w T (phiN X la G.w wF T (G.th' i) (c i)) = aeval (ySec X la G.w) (c i) *
        algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i))) := fun i =>
      frac_phiN X la G.w wF T (G.th' i) (c i) fun m hm => ((hc i m hm).le.trans (Nat.sub_le _ _))
    simp only [e] at h0
    exact h0
  have hc0 := ind_claim (ySec X la G.w)
    (fun i => algebraMap (Rp X la G.N) (Lw X la G.w) (emb X la G.N (X.inc wF (G.th' i)))) (JHfr X la G.w wF)
    (dSec X la G.w) (dSec_ySec X la G.w) (fun l i => dSec_emb X la G.w l _) (dSec_algebraMap_Kp X la G.w)
    (fun l a x hx => dSec_mem X la G.w l wF a x hx) (JHfr_succ_le X la G.w wF)
    (fun m i => ySec_monomial_mul_mem X la G.w wF m (G.th' i)) hbase (a0 D j T) c hc hmem
  apply Subtype.ext
  rw [hxc, hc0]
  simp

end Main

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem upO_Msup_le {X : PJ D B P j} (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (ka : WeightFamilies.Wt D j) :
    upO X la N (X.Msup ka) ≤ (Vw X la N ka).restrictScalars (Op X la N) := by
  rw [upO, Submodule.span_le]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨F, -, rfl⟩ := hy
  exact Submodule.subset_span ⟨F, rfl⟩

section

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO))

theorem jW_MggW_mem (S : Scal B) (CRm c : ℝ)
    (hΘM : X.Theta S (addL wF wL T) wL wF T ≤ X.Msup (addL wF wL T))
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (hth' : ∀ i, G.th' i ∈ X.Thc S.sF wF)
    (hth0 : ∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF)) (hal : ∀ k, ∑ i, G.alz k i = a0 D j T)
    (hCM : Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc (addL wF wL T) F)) ''
        (WeightFamilies.MggK B CRm T c j (addL wF wL T) : Set (B.Cusp j (addL wF wL T)))) ≤
      Submodule.span (Kp X la G.N)
        ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
            v = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
         Set.range (zK G la)))
    (x : ↥(T0.WL X (addL wF wL T) la)) (hx : x ∈ MggW X la (addL wF wL T) CRm T c) :
    jW X la G.N (addL wF wL T) x ∈ NovK G la := by
  have hle : X.emb (addL wF wL T) (MggO B CRm T c j (addL wF wL T)) ≤ X.Msup (addL wF wL T) :=
    T0.emb_mono X _ inf_le_left
  have h1 : jW X la G.N (addL wF wL T) x ∈ Submodule.span (Op X la G.N) (jW X la G.N (addL wF wL T) ''
      (MggW X la (addL wF wL T) CRm T c : Set ↥(T0.WL X (addL wF wL T) la))) := Submodule.subset_span ⟨x, hx, rfl⟩
  unfold MggW at h1
  rw [span_jW_inW X la G.N _ _ hle] at h1
  have h2 : Submodule.span (Op X la G.N) {f : ↥(Vw X la G.N (addL wF wL T)) |
      ∃ F ∈ X.emb (addL wF wL T) (MggO B CRm T c j (addL wF wL T)), (f : Rp X la G.N) = emb X la G.N F} ≤
      (NovK G la).restrictScalars (Op X la G.N) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨_, ⟨F, hF, rfl⟩, hf⟩
    show f ∈ NovK G la
    rw [NovK_eq, ZK, ← Submodule.span_union, mem_span_subtype_iff (R := Kp X la G.N) (Vw X la G.N (addL wF wL T))]
    have h3 : (f : Rp X la G.N) ∈ Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc (addL wF wL T) F)) ''
        (WeightFamilies.MggK B CRm T c j (addL wF wL T) : Set (B.Cusp j (addL wF wL T)))) :=
      Submodule.subset_span ⟨F, hF.2, hf.symm⟩
    refine Submodule.span_mono ?_ (hCM h3)
    rintro v (⟨al, i, hal', rfl⟩ | ⟨k, rfl⟩)
    · have hle' : ∑ i, al i ≤ T := le_trans hal'.le (Nat.sub_le _ _)
      have hm := upO_Msup_le la G.N (addL wF wL T) (upO_mono la G.N hΘM (upO_mono la G.N (le_sup_of_le_left le_sup_left)
        (secPow_mul_mem_upO la G.w hw al hle' (A := X.emb wF (X.Thc S.sF wF)) ⟨G.th' i, hth' i, rfl⟩)))
      exact ⟨⟨_, hm⟩, Or.inl ⟨al, i, hal', rfl⟩, rfl⟩
    · have h := secPow_mul_mem_upO la G.w hw (G.alz k) (n := a0 D j T) (hal k).le
        (A := X.emb (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF))) ⟨G.th0 k, hth0 k, rfl⟩
      rw [hal k, Nat.sub_self, pow_zero, mul_one] at h
      have hm := upO_Msup_le la G.N (addL wF wL T) (upO_mono la G.N hΘM
        (upO_mono la G.N (le_sup_of_le_left le_sup_right) h))
      exact ⟨⟨_, hm⟩, Or.inr ⟨k, rfl⟩, rfl⟩
  exact h2 h1

theorem localIdx (Q : LocalPointData G la) (S : Scal B) (CRm c : ℝ) (e : ℕ) (νs cp : ℝ) (v : PtsG G la → ℝ) [Fintype (PtsG G la)]
    (hM : Submodule.IsLattice B.KO (B.Mlat j (addL wF wL T)))
    (hΘM : X.Theta S (addL wF wL T) wL wF T ≤ X.Msup (addL wF wL T))
    (hspK : Submodule.span B.KO (X.Thc S.sK (addL wF wL T) : Set (B.Cusp j (addL wF wL T))) = ⊤)
    (hT1 : 1 ≤ T) (hDT : WeightFamilies.dimY D j ≤ T)
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (hwM : ∀ k, G.w k ∈ B.Mlat j wL)
    (hth' : ∀ i, G.th' i ∈ X.Thc S.sF wF) (hth'M : ∀ i, G.th' i ∈ B.Mlat j wF)
    (hth0 : ∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF)) (hth0M : ∀ k, G.th0 k ∈ B.Mlat j (X.wF0 wL wF))
    (hal : ∀ k, ∑ i, G.alz k i = a0 D j T)
    (hzc : ∀ k β, X.inc _ (G.zc k β) = (Formalism.MainNotions.Gaps.SizeBoundsAlt.zPoly X G.w (G.alz k) (G.th0 k)).coeff β)
    (hdet : ∃ φ : Fin G.rz → B.Cusp j (addL wF wL T) →ₗ[B.KO] B.KO, Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly φ G.zc ≠ 0)
    (hthK : ∀ i, ((G.th i : B.Mlat j (addL wF wL T)) : B.Cusp j (addL wF wL T)) ∈ X.Thc S.sK (addL wF wL T))
    (hsp : Submodule.span B.KO (Set.range fun i => ((G.th i : B.Mlat j (addL wF wL T)) : B.Cusp j (addL wF wL T))) ⊔
      WeightFamilies.MggK B CRm T c j (addL wF wL T) = ⊤)
    (hB : InBasis G la) (hC : Q.InCurve) (hTie : Q.InTie S)
    (hCM : Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc (addL wF wL T) F)) ''
        (WeightFamilies.MggK B CRm T c j (addL wF wL T) : Set (B.Cusp j (addL wF wL T)))) ≤
      Submodule.span (Kp X la G.N)
        ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
            v = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
         Set.range (zK G la)))
    (hcp : 0 ≤ cp) (hv : ∀ ζ, 0 ≤ v ζ) (hν : ∀ ζ, Q.nu S ζ ≤ νs + cp * v ζ) (he : (T : ℝ) * νs ≤ (e : ℝ))
    (hLB : Module.length (Op X la G.N) (↥(Q.AA T) ⧸ (firstLength_le_prime_bound G la T).comap (Q.AA T).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * Q.Ila.toNat : ℕ) : ℕ∞))
    (hLP : Module.length (Op X la G.N) (↥(Q.AAp T (Q.mm S T e)) ⧸ (Q.AA T).comap (Q.AAp T (Q.mm S T e)).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ᶠ ζ, Q.mm S T e ζ * fdeg ζ : ℕ) : ℕ∞))
    (U : Submodule (X.Kl la) ↥(T0.WL X (addL wF wL T) la)) :
    (Formalism.LatticeIndexTer.idx (X.Ol la) ↥(T0.WL X (addL wF wL T) la) (T0.MW X (addL wF wL T) la ⊓ U.restrictScalars (X.Ol la))
              (T0.ThW X S (addL wF wL T) wL wF T la ⊓ U.restrictScalars (X.Ol la)) : ℝ) ≤
      (e : ℝ) * (finrank (X.Kl la) U : ℝ) +
        (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) *
          ((T : ℝ) * cp * ∑ ζ, ((ep (unifO X la G.N) ζ : ℝ) * (fdeg ζ : ℝ)) * v ζ) +
        (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * (Q.Ila.toNat : ℝ) +
        (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j (addL wF wL T)) G.zc la : ℝ) +
        ((WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j (addL wF wL T) ⧸ Submodule.span (𝓞 B.KO)
          (Set.range fun i : Fin G.rq => (Submodule.Quotient.mk (G.th i) : WeightFamilies.Qm B CRm T c j (addL wF wL T))))).toNat : ℝ) := by
  have hLat := inLat_of X S (addL wF wL T) wL wF T la hM hΘM hspK
  have : FiniteDimensional (X.Kl la) ↥(T0.WL X (addL wF wL T) la) := T0.finDim_of_isLat _ hLat.1
  have hN1 := generators_le_thetaSpan G la S hΘM hw hth'
  have hZ1 := zeroGenerators_le_thetaSpan G la S hΘM hw hth0 hal
  have hTM := thetaSpan_le_integralForms G la S hΘM
  have hZlen := len_Zm_le G la hM.fg hDT hwM hth0M hal hzc hdet
  have hqne := quot_len_ne_top la (addL wF wL T) CRm T c G.th hM hsp
  have hLP' : Module.length (Op X la G.N) (↥(Q.AAp T (Q.mm S T e)) ⧸ (Q.AA T).comap (Q.AAp T (Q.mm S T e)).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ ζ, (max 0 ⌈(ep (unifO X la G.N) ζ : ℝ) *
        ((T : ℝ) * Q.nu S ζ - (e : ℝ))⌉).toNat * fdeg ζ : ℕ) : ℕ∞) := by
    rw [finsum_eq_sum_of_fintype] at hLP
    exact hLP
  have hthΘ : ∀ i, toW X la (addL wF wL T) (G.th i) ∈ T0.ThW X S (addL wF wL T) wL wF T la := fun i => by
    show X.bc la (X.inc (addL wF wL T) (G.th i)) ∈ X.loc la (X.Theta S (addL wF wL T) wL wF T)
    exact Submodule.subset_span ⟨X.inc (addL wF wL T) (G.th i),
      (show X.emb _ (X.Thc S.sK (addL wF wL T)) ≤ X.Theta S (addL wF wL T) wL wF T from le_sup_right)
        ⟨_, hthK i, rfl⟩, rfl⟩
  have hThM : X.Thc S.sK (addL wF wL T) ≤ B.Mlat j (addL wF wL T) := by
    intro f hf
    have hf' : X.inc (addL wF wL T) f ∈ X.Msup (addL wF wL T) :=
      hΘM ((show X.emb _ (X.Thc S.sK _) ≤ X.Theta S _ wL wF T from le_sup_right) ⟨f, hf, rfl⟩)
    obtain ⟨g, hg, heq⟩ := hf'
    exact (X.inc_inj _ heq) ▸ hg
  have hMspan : Submodule.span B.KO (B.Mlat j (addL wF wL T) : Set (B.Cusp j (addL wF wL T))) = ⊤ :=
    eq_top_iff.mpr (hspK ▸ Submodule.span_mono (SetLike.coe_subset_coe.mpr hThM))
  have key := levelsQDesc (PtsG G la) (ep (unifO X la G.N)) fdeg (Q.nu S) v νs cp T
    (Nat.choose (T - 1) (WeightFamilies.dimY D j)) Q.Ila.toNat (fun ζ => one_le_ep_of_curve Q hC ζ) hT1 hcp hv hν
    (X.Ol la) (Op X la G.N) (X.Kl la) (Kp X la G.N) ↥(T0.WL X (addL wF wL T) la) ↥(Vw X la G.N (addL wF wL T))
    (WK X la G.w wF (a0 D j T)) (jW X la G.N (addL wF wL T)) (jW_isBaseChange X la G.N _ hMspan)
    (unif X la) (unif_irreducible X la) (unifO_irreducible X la G.N)
    (T0.MW X (addL wF wL T) la) (T0.ThW X S (addL wF wL T) wL wF T la) (MggW X la (addL wF wL T) CRm T c)
    (N1 G la) (Zl G la) (Zm G la) (Np G la e) e G.rq
    (WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j (addL wF wL T) ⧸ Submodule.span (𝓞 B.KO)
      (Set.range fun i : Fin G.rq => (Submodule.Quotient.mk (G.th i) : WeightFamilies.Qm B CRm T c j (addL wF wL T))))).toNat
    (fun i => toW X la (addL wF wL T) (G.th i)) (Q.AA T) (Q.AAp T (Q.mm S T e)) (firstLength_le_prime_bound G la T) (rhoN G la e)
    hLat.1 hLat.2 (sup_le hN1 hZ1) (fun i => toW_mem_MW X la _ (G.th i))
    hthΘ
    (Submodule.comap_mono (Submodule.span_mono (Set.image_mono (T0.emb_mono X _ inf_le_left))))
    (fun x hx => jW_MggW_mem G la S CRm c hΘM hw hth' hth0 hal hCM x hx)
    ((quot_len_le X la (addL wF wL T) CRm T c G.th).trans (le_of_eq (ENat.natCast_toNat hqne).symm))
    (le_sup_of_le_left le_sup_left) (generators_le_poleSpan G la e) (Zl_le_Zm G la (hZ1.trans hTM)) (Zm_le_Np G la e)
    (rhoN_mem G Q S e hC hTie hw hth'M hDT hal) (ker_rhoN G la e (in64 G la hB) (hN1.trans hTM) hDT hal)
    (map_reduction_generators_eq G la e) (reduced_generators_le Q S hC hTie hw hth'M) (AA_le_AAp Q _)
    (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hZlen) (Or.inl ⟨he, fun ζ => ep_nu_int Q hTie ζ⟩) hLP' hLB U
  have hZn : ((Module.length (Op X la G.N) (↥(Zm G la) ⧸ (Zl G la).comap (Zm G la).subtype)).toNat : ℝ) ≤
      (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j (addL wF wL T)) G.zc la : ℝ) := by
    exact_mod_cast ENat.toNat_le_of_le_natCast hZlen
  linarith

end

theorem localBound {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X ka wL wF)
    (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm c : ℝ) (e : ℕ) (νs : ℝ)
    (hka : ka = addL wF wL T)
    (hM : Submodule.IsLattice B.KO (B.Mlat j ka)) (hΘM : X.Theta S ka wL wF T ≤ X.Msup ka)
    (hspK : Submodule.span B.KO (X.Thc S.sK ka : Set (B.Cusp j ka)) = ⊤)
    (hT1 : 1 ≤ T) (hDT : WeightFamilies.dimY D j ≤ T)
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (hwM : ∀ k, G.w k ∈ B.Mlat j wL)
    (hth' : ∀ i, G.th' i ∈ X.Thc S.sF wF) (hth'M : ∀ i, G.th' i ∈ B.Mlat j wF)
    (hth0 : ∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF)) (hth0M : ∀ k, G.th0 k ∈ B.Mlat j (X.wF0 wL wF))
    (hal : ∀ k, ∑ i, G.alz k i = a0 D j T)
    (hzc : ∀ k β, X.inc ka (G.zc k β) = (Formalism.MainNotions.Gaps.SizeBoundsAlt.zPoly X G.w (G.alz k) (G.th0 k)).coeff β)
    (hdet : ∃ φ : Fin G.rz → B.Cusp j ka →ₗ[B.KO] B.KO, Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly φ G.zc ≠ 0)
    (hthK : ∀ i, ((G.th i : B.Mlat j ka) : B.Cusp j ka) ∈ X.Thc S.sK ka)
    (hsp : Submodule.span B.KO (Set.range fun i => ((G.th i : B.Mlat j ka) : B.Cusp j ka)) ⊔
      WeightFamilies.MggK B CRm T c j ka = ⊤)
    (hB : InBasis G la) (hC : Q.InCurve) (hTie : Q.InTie S)
    (hCM : Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc ka F)) ''
        (WeightFamilies.MggK B CRm T c j ka : Set (B.Cusp j ka))) ≤
      Submodule.span (Kp X la G.N)
        ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
            v = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
         Set.range (zK G la)))
    (hv : ∀ ζ, 0 ≤ vEt Q ζ) (hν : ∀ ζ, Q.nu S ζ ≤ νs + max 0 c * vEt Q ζ) (he : (T : ℝ) * νs ≤ (e : ℝ))
    (hLB : Module.length (Op X la G.N) (↥(Q.AA T) ⧸ (firstLength_le_prime_bound G la T).comap (Q.AA T).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * Q.Ila.toNat : ℕ) : ℕ∞))
    (hLP : Module.length (Op X la G.N) (↥(Q.AAp T (Q.mm S T e)) ⧸ (Q.AA T).comap (Q.AAp T (Q.mm S T e)).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ᶠ ζ, Q.mm S T e ζ * fdeg ζ : ℕ) : ℕ∞))
    (V' : Submodule (X.Kl la) (X.Vl la)) (hV' : V' ≤ X.locK la (X.Msup ka)) :
    X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
        (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
          (e : ℝ) * (finrank (X.Kl la) V' : ℝ) + rLa Q CRm T c := by
  subst hka
  have := (finite_pts_of_curve Q hC).1
  letI := Fintype.ofFinite (PtsG G la)
  refine qlen_of_idx X S _ wL wF T la (inLat_of X S _ wL wF T la hM hΘM hspK) hΘM e (rLa Q CRm T c) (fun U => ?_) V' hV'
  have h := localIdx G la Q S CRm c e νs (max 0 c) (vEt Q) hM hΘM hspK hT1 hDT hw hwM hth' hth'M hth0 hth0M hal hzc hdet
    hthK hsp hB hC hTie hCM (le_max_left _ _) hv hν he hLB hLP U
  rw [levels_eq Q T c] at h
  unfold rLa
  linarith

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

def LenPoleL {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} : Prop :=
  ∀ (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T e : ℕ) (c : ℝ),
    Q.Ok S CRm T c → Q.InLift T → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    Module.length (Op X la G.N) (↥(Q.AAp T (Q.mm S T e)) ⧸ (Q.AA T).comap (Q.AAp T (Q.mm S T e)).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ᶠ ζ, Q.mm S T e ζ * fdeg ζ : ℕ) : ℕ∞)

theorem localC_of_len
    (hLB : ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j), LenBase (X := X) (ka := ka) (wL := wL) (wF := wF))
    (hLP : ∀ (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j), LenPoleL (X := X) (ka := ka) (wL := wL) (wF := wF)) :
    LocalC D B P := by
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hHyp hLat hSup hLAM hQ
    G Gc PH Prw Pet Pd hTW hTTh hTZ hTQ hTEt hDH hDS hDL hPG hSRd hSRho hSRhoP hPD hCB
    la Q hB hC hTie hLift hCZ hCM hIla e he V' hV'
  have hΘ := theta_le_msup_of_hypC (X j h1 h2) S hHyp
  have hspK := (span_Thc_of_hypC hHyp).2.2
  obtain ⟨-, hSet, -, -, hH2, -⟩ := hHyp
  have hka := ka_eq_addL_of_setC hSet
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hT0, hDT, -⟩ := hSet
  have hok : Q.Ok S K.CRm T (cc D large₂ C2 A2 CR wL) := ⟨hB, hC, hTie, hCZ, hCM⟩
  have hw : ∀ k, G.w k ∈ (X j h1 h2).WWc S.sW wL := by
    intro k
    rw [← hTW.1]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hth'M : ∀ i, G.th' i ∈ B.Mlat j wF := fun i => hH2.2.1 (hTTh i).1
  exact localBound G la Q S K.CRm (cc D large₂ C2 A2 CR wL) e (nus la) hka hLat.toIsLattice hΘ hspK hT0 hDT hw hTW.2.1
    (fun i => (hTTh i).1) hth'M
    (fun k => (hTZ.1 k).1) (fun k => (hTZ.1 k).2.1) (fun k => (hTZ.1 k).2.2.2) hTZ.2.1 hTZ.2.2
    hTQ.2.1 hTQ.2.2.1 hB hC hTie hCM
    (fun ζ => vEt_nonneg_comb hCB Q ζ) (fun ζ => nu_le_comb hCB Q hTie ζ) he
    (hLB j (X j h1 h2) ka wL wF G la Q S K.CRm T (cc D large₂ C2 A2 CR wL) hok hth'M hw hIla)
    (hLP j (X j h1 h2) ka wL wF G la Q S K.CRm T e (cc D large₂ C2 A2 CR wL) hok hLift hw)
    V' hV'

end Formalism.MainNotions.Gaps.EtaleWeightGaps
