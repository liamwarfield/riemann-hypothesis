module

public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKIntMem
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.TwistValues

section General

variable {L : Type} [Field L] [NumberField L]

theorem locK_int_mem (χ : HChar L) (Λ : Subgroup ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 L))) (ht : ∀ v, χ.TameAt v)
    (hi : ∀ k, χ.inf k = 1) (hu : ∀ v, v ∉ S → χ.UnrAt v) (hv : ∀ v, v ∉ S → χ.val v ∈ Λ)
    {P : HeightOneSpectrum (𝓞 L)} (hP : P ∈ S) (b : 𝓞 L) (k : Lˣ) (hk : (k : L) = b) : χ.locK P k ∈ Λ := by
  classical
  have hb : b ≠ 0 := by
    rintro rfl
    exact k.ne_zero hk
  have h0 : P.intValuation b ≠ 0 := P.intValuation_ne_zero b hb
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.intValuation b = WithZero.exp (-(n : ℤ)) := by
    have h1 := P.intValuation_le_one b
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    refine ⟨(-WithZero.log (P.intValuation b)).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun _ => n + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then b else 1)
  have h1 : P.intValuation (a - b) ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
    have h1 := ha P hP
    rw [if_pos rfl] at h1
    exact (P.intValuation_le_pow_iff_mem _ _).2 h1
  have h2 : P.intValuation a = P.intValuation b := by
    refine Valuation.map_eq_of_sub_lt _ (h1.trans_lt ?_)
    rw [hn, WithZero.exp_lt_exp]
    push_cast
    omega
  have ha0 : (a : L) ≠ 0 := by
    intro h
    have h3 : a = 0 := by exact_mod_cast h
    rw [h3, map_zero] at h2
    exact h0 h2.symm
  have hmem : χ.locK P (Units.mk0 _ ha0) ∈ Λ := by
    have h := TypeValues.productRule χ S hu (Units.mk0 _ ha0)
    rw [hi, one_mul, Finset.prod_eq_single_of_mem P hP (fun v hvS hvP => TypeValues.locK_eq_one (ht v) _ a rfl (by
      have h1 := ha v hvS
      rw [if_neg hvP] at h1
      exact Ideal.pow_le_self (Nat.succ_ne_zero n) h1))] at h
    rw [eq_inv_of_mul_eq_one_left h]
    refine Λ.inv_mem (finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun v => ?_)
    exact finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun hvS => Λ.zpow_mem (hv v hvS) _
  have hval : ∀ z : L, Valued.v (algebraMap L (P.adicCompletion L) z) = P.valuation L z :=
    fun z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P z
  have hint : ∀ z : 𝓞 L, P.valuation L (z : L) = P.intValuation z := fun z => P.valuation_of_algebraMap z
  have h4 : χ.locK P (Units.mk0 _ ha0 * k⁻¹) = 1 := by
    have e : ((atFin P (Units.mk0 _ ha0 * k⁻¹) : (P.adicCompletion L)ˣ) : P.adicCompletion L) =
        algebraMap L (P.adicCompletion L) ((a : L) * (b : L)⁻¹) := by
      rw [← hk, ← Units.val_inv_eq_inv_val]
      rfl
    refine ht P _ ?_ ?_
    · unfold IsUnitAt
      rw [e, hval, map_mul, map_inv₀, hint, hint, h2, mul_inv_cancel₀ h0]
    · have e' : (a : L) * (b : L)⁻¹ - 1 = ((a - b : 𝓞 L) : L) * (b : L)⁻¹ := by
        have : (b : L) ≠ 0 := hk ▸ k.ne_zero
        push_cast
        field_simp
      rw [e, ← map_one (algebraMap L (P.adicCompletion L)), ← map_sub, hval, e', map_mul, map_inv₀, hint, hint, hn]
      refine (mul_le_mul_left h1 _).trans (le_of_eq ?_)
      rw [← WithZero.exp_neg, ← WithZero.exp_add]
      congr 1
      push_cast
      ring
  rw [map_mul, map_inv, mul_inv_eq_one] at h4
  exact h4 ▸ hmem

theorem locK_mem (χ : HChar L) (Λ : Subgroup ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 L))) (ht : ∀ v, χ.TameAt v)
    (hi : ∀ k, χ.inf k = 1) (hu : ∀ v, v ∉ S → χ.UnrAt v) (hv : ∀ v, v ∉ S → χ.val v ∈ Λ)
    (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : χ.locK P k ∈ Λ := by
  by_cases hP : P ∈ S
  · obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (k : L)
    have hb0 : (b : L) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb
    have h1 := locK_int_mem χ Λ S ht hi hu hv hP b (Units.mk0 _ hb0) rfl
    have h2 := locK_int_mem χ Λ S ht hi hu hv hP a (k * Units.mk0 _ hb0) (by
      rw [Units.val_mul, ← e]
      exact div_mul_cancel₀ _ hb0)
    rw [map_mul] at h2
    exact (mul_mem_cancel_right h1).1 h2
  · have h : χ.locK P k = χ.val P ^ ordF P k := GlobalTheory.Mem.Chr.CharModel.locK_unr (F := L) ⟨χ.1, χ.2⟩ (hu P hP) k
    rw [h]
    exact Λ.zpow_mem (hv P hP) _

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
  Formalism.L2.Col GlobalTheory.RationalValues
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem char_mem {D : D7} (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ) {n : ℕ} (hn : 0 < n)
    (ho : χ.OrderDvd n) (M : Subfield ℂ) (hM : ∀ P k, ((χ.locK P k : ℂˣ) : ℂ) ∈ M) (x : (AE D)ˣ) : ((c x : Circle) : ℂ) ∈ M := by
  have h1 : ∀ x, c x ^ n = 1 := HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  obtain ⟨y, hy⟩ := IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn (a x) (ha x).2
  rw [hab x, map_mul, ← hy, map_pow, h1, one_mul]
  obtain ⟨j, j1, j2, j3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j j1 j2 (PlaceIdem.exists_isPlIdem D j j1 j2 j3) c χ h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom (b x))
  rw [hprod (b x) (hb x).1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact prod_mem fun P _ => hM P _

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem xiH_locK_mem (hL : R.toLevCh.Is A.μ0) (hon : R.fam_pl_onto) (hmu : R.fam_muVal)
    (hok : ∀ t P, P ∈ A.ok t ↔ Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E))))
    (i : Fin D.R.m) (t : T0) (PP : Pl D.host.E) (k : D.host.Eˣ) :
    (((R.xiH t).locK PP k : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
  classical
  have : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  let T : Finset (Pl D.host.E) := R.Sb ∪ R.Q t ∪ R.Q A.μ0
  have hQ : ∀ v ∈ R.Q t, v ∈ T := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hu : ∀ v, v ∉ T ∪ T.image conjPrime₂ → (R.xiH t).UnrAt v := fun v hv => by
    by_contra hn
    rcases (hL.Q_ram t v).1 hn with h | ⟨w, hw, h⟩
    · exact hv (Finset.mem_union_left _ (hQ v h))
    · refine hv (Finset.mem_union_right _ (Finset.mem_image.2 ⟨w, hQ w hw, ?_⟩))
      have h1 : w = conjPrime₂ v := HeightOneSpectrum.ext (w.isMaximal.eq_of_le (conjPrime₂ v).isPrime.ne_top fun c hc => by
        obtain ⟨c', hc', e⟩ := h c hc
        rw [mem_conjP, show cO D.host.E c = c' from RingOfIntegers.ext e.symm]
        exact hc')
      rw [h1, conjP_conjP]
  have hv : ∀ v, v ∉ T ∪ T.image conjPrime₂ → (R.xiH t).val v ∈ unitsIn D.what₂.embLL.fieldRange := fun v hv => by
    by_cases hc : conjPrime₂ v = v
    · have h1 : (((R.xiH t).val v : ℂˣ) : ℂ) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, TypeValues.val_sq_eq_one D.sp.cm (hL.xi_triv t) (hu v hv) hc, Units.val_one]
      show (((R.xiH t).val v : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange
      rcases sq_eq_one_iff.1 h1 with h2 | h2
      · rw [h2]; exact one_mem _
      · rw [h2]; exact neg_mem (one_mem _)
    · have hs : ∀ S : Set (Pl D.host.E), (∀ w ∈ S, w ∈ T) → Bridge.SplitOff v S := fun S hS =>
        ⟨fun h => hc (HeightOneSpectrum.ext ((conjIdeal_asIdeal v).symm.trans h)),
          fun h => hv (Finset.mem_union_left _ (hS v h)), fun w hw h => hv (Finset.mem_union_right _ (Finset.mem_image.2
            ⟨w, hS w hw, by rw [show w = conjPrime₂ v from HeightOneSpectrum.ext (h.trans (conjIdeal_asIdeal v)), conjP_conjP]⟩))⟩
      have hS : ∀ w ∈ R.Sb, w ∈ T := fun w hw => Finset.mem_union_left _ (Finset.mem_union_left _ hw)
      obtain ⟨P, rfl⟩ := hon v (hs _ hS)
      have h1 : (R.C.mu0 i * R.xiH t).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange :=
        ⟨_, hmu i t P ((hok t P).2 (hs _ fun w hw => hw.elim (hS w) (hQ w)))⟩
      have h2 : (R.C.mu0 i * R.xiH A.μ0).val (R.pl P) ∈ unitsIn D.what₂.embLL.fieldRange :=
        ⟨_, hmu i A.μ0 P ((hok A.μ0 P).2 (hs _ fun w hw => hw.elim (hS w) fun h => Finset.mem_union_right _ h))⟩
      rw [hL.xi_base, mul_one] at h2
      rw [HChar.val_mul] at h1
      exact (mul_mem_cancel_left h2).1 h1
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  exact locK_mem (R.xiH t) _ (T ∪ T.image conjPrime₂) (hL.xi_tame t) (TypeValues.inf_eq_one _ hn ho) hu hv PP k

theorem xiVal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → GlobalTheory.TwistField.XiVal R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF t x
  obtain ⟨_, _, _, hT⟩ := hF.tie
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  exact char_mem _ _ (hL.xi t) hn ho _
    (xiH_locK_mem R hL hF.pl_onto hF.muVal hT.ok ⟨0, lt_of_lt_of_le two_pos D.R.two_le_m⟩ t) x

end GlobalTheory.TwistValues
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoFinitePlaceTruncationAdeleE
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoFinitePlaceTruncationAdeleE
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecInv

open Filter Topology

theorem tendsto_sum_placeIdem {F : Type} [Field F] [NumberField F]
    (α : HeightOneSpectrum (𝓞 F) → GlobalTheoryTheory.GenusMassVolumes.Af F) (h1 : ∀ v, evalV F v (α v) = 1)
    (h0 : ∀ v v', v' ≠ v → evalV F v' (α v) = 0) :
    Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∑ v ∈ s, α v) atTop (𝓝 1) := by
  classical
  have hv : ∀ (s : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)),
      evalV F w (1 - ∑ v ∈ s, α v) = if w ∈ s then 0 else 1 := by
    intro s w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_one, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single_of_mem w hw (fun v _ hvw => h0 v w (Ne.symm hvw)), h1, sub_self]
    · rw [Finset.sum_eq_zero (fun v hvs => h0 v w (by rintro rfl; exact hw hvs)), sub_zero]

  let y : Finset (HeightOneSpectrum (𝓞 F)) → (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletionIntegers F :=
    fun s w => if w ∈ s then 0 else 1
  have hy : Tendsto y atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop {w}] with s hs
    have hws : w ∈ s := Finset.singleton_subset_iff.mp hs
    simp [y, hws]
  let g : ((w : HeightOneSpectrum (𝓞 F)) → w.adicCompletionIntegers F) → GlobalTheoryTheory.GenusMassVolumes.Af F :=
    RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) Filter.cofinite
  have hg : Continuous g := RestrictedProduct.isEmbedding_structureMap.continuous
  have hgy : ∀ s, g (y s) = 1 - ∑ v ∈ s, α v := by
    intro s
    refine FiniteAdeleRing.ext (R := 𝓞 F) (K := F) (fun w => ?_)
    have e1 : (g (y s)) w = ((y s w : w.adicCompletionIntegers F) : w.adicCompletion F) := rfl
    have e2 : (1 - ∑ v ∈ s, α v) w = evalV F w (1 - ∑ v ∈ s, α v) := rfl
    rw [e1, e2, hv]
    by_cases hw : w ∈ s <;> simp [y, hw]
  have hg0 : g 0 = 0 := FiniteAdeleRing.ext (R := 𝓞 F) (K := F) (fun w => rfl)
  have hlim : Tendsto (fun s => 1 - ∑ v ∈ s, α v) atTop (𝓝 (0 : GlobalTheoryTheory.GenusMassVolumes.Af F)) := by
    have h := (hg.tendsto 0).comp hy
    rw [hg0] at h
    exact h.congr (fun s => hgy s)
  simpa using (tendsto_const_nhds (x := (1 : GlobalTheoryTheory.GenusMassVolumes.Af F))).sub hlim

theorem tendsto_truncation : ∀ (D : D7) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ a : AE D, infPart D a = 0 → Filter.Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 D.host.F)) => algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v) * a) Filter.atTop (nhds a) := by
  intro D ε hε a ha
  simp only [IsPlaceIdem] at hε
  choose α hαε hα1 hα0 using hε
  have hsum : ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      ∑ v ∈ s, ε v = pairA D.host.F 0 (∑ v ∈ s, α v) := by
    intro s
    simp only [hαε]
    exact (map_sum (AddMonoidHom.inr (InfiniteAdeleRing D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) α s).symm
  have hpair : Continuous (pairA D.host.F 0) := by
    show Continuous fun y : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => ((0 : InfiniteAdeleRing D.host.F), y)
    exact continuous_const.prodMk continuous_id
  have hlimF : Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 D.host.F)) => ∑ v ∈ s, ε v) atTop
      (𝓝 (pairA D.host.F 0 1)) := by
    simp_rw [hsum]
    exact (hpair.tendsto 1).comp (tendsto_sum_placeIdem α hα1 hα0)

  have hidem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1) * a = a := by
    have hsplit : pairA D.host.F 0 1 = 1 - pairA D.host.F 1 0 := by
      rw [eq_sub_iff_add_eq]
      show ((0 + 1, 1 + 0) : InfiniteAdeleRing D.host.F × FiniteAdeleRing (𝓞 D.host.F) D.host.F) = 1
      rw [zero_add, add_zero]
      rfl
    have hr : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) = GlobalTheory.SplitScalar.realIdem D := by
      rw [GlobalTheory.SplitScalar.realIdem, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsplit, map_sub, map_one, hr, sub_mul, one_mul, GlobalTheory.SplitScalar.realIdem_mul_of_fin ha, sub_zero]
  have hT := hlimF.smul_const a
  rw [Algebra.smul_def, hidem] at hT
  exact hT.congr (fun s => Algebra.smul_def _ _)

end GlobalTheory.VecInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoFinitePlaceTruncationAdeleEStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_finitePlaceTruncation_adeleE : ∀ (D : D7) (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ a : AE D, infPart D a = 0 → Filter.Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 D.host.F)) => algebraMap (AF D.host.F) (AE D) (∑ v ∈ s, ε v) * a) Filter.atTop (nhds a) := by
  first | exact @GlobalTheory.VecInv.tendsto_truncation | exact GlobalTheory.VecInv.tendsto_truncation | (intros; apply GlobalTheory.VecInv.tendsto_truncation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameInteg
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameInteg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SplitFrameColumn

theorem intAE_mul {D : D7} {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, c, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, d, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, c * d, ?_⟩
      · rw [map_mul]; exact mul_mem (ha w) (hb w)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]; push_cast; rfl
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem comm_mem_intAf_iff {D : D7} (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      z ∈ intAE D := by
  constructor
  · intro hs
    have hs' : Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z ∈
        Subring.closure (Set.range (fun x : Formalism.UG.intOE D.host.E => (x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∪
        Set.range (fun y : Formalism.UG.intAd D.host.F => (1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F))) := hs
    suffices h : ∀ s ∈ Subring.closure (Set.range (fun x : Formalism.UG.intOE D.host.E => (x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) ∪
        Set.range (fun y : Formalism.UG.intAd D.host.F => (1 : D.host.E) ⊗ₜ[D.host.F] (y : Af D.host.F))),
        (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm s ∈ intAE D by
      simpa using h _ hs'
    have hone : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by rw [map_one]; exact one_mem _
    intro s hs
    induction hs using Subring.closure_induction with
    | mem s hs =>
      rcases hs with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
      · exact AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩
      · refine AddSubgroup.subset_closure ⟨a, fun w => ha w, 1, ?_⟩
        simp
    | zero => rw [map_zero]; exact zero_mem _
    | one => rw [map_one]; exact AddSubgroup.subset_closure ⟨1, hone, 1, by simp [Algebra.TensorProduct.one_def]⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
    | mul x y _ _ hx hy => rw [map_mul]; exact intAE_mul hx hy
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      rw [Algebra.TensorProduct.comm_tmul]
      have hx : (x : D.host.E) ⊗ₜ[D.host.F] a =
          ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hx]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨(x : D.host.E), ⟨x, rfl⟩⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem toEAf_finEmb {D : D7} (t : EAf D) : toEAf D (GlobalTheory.AdelicLatMove.finEmb D t) = t := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | tmul x α => rfl

theorem latHat_iff_hatL {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) ↔
      (fun i => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact GlobalTheory.AdelicLatMove.pure_mem_hatL Λ a (fun w => ha w) x hx
    | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
    | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx
  · intro hz
    have key : ∀ w ∈ AddSubgroup.closure (GlobalTheory.AdelicLatMove.pureSet (D := D) Λ),
        (fun i => (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm (w i)) ∈
          Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin n → D.host.E)) := by
      intro w hw
      induction hw using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨α, hα, x, hx, rfl⟩ := hw
        exact AddSubgroup.subset_closure ⟨α, fun u => hα u, x, hx, rfl⟩
      | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
      | add x y _ _ hx hy => simp only [Pi.add_apply, map_add (f := _)]; exact add_mem hx hy
      | neg x _ hx => simp only [Pi.neg_apply, map_neg]; exact neg_mem hx
    have := key _ (GlobalTheory.AdelicLatMove.mem_closure_of_mem_hatL Λ _ hz)
    simpa only [AlgEquiv.symm_apply_apply] using this

theorem frame_column : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (EAf D)), IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ ∀ i, Valued.v ((((frCo φ β)⁻¹ : GL (Fin V.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdA φ (y k)) i) ≤ 1 := by
  intro D V Λ β _ hβ v φ e he y
  obtain ⟨hπ, hE, -, -, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v φ e he
  set u : Fin V.rank → EAf D := (β⁻¹).1 *ᵥ fun k => toEAf D (y k) with hu
  have hsw : (fun k => Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (e * y k))) =
      toEAf D e • fun k => toEAf D (y k) := funext fun k => (toEAf D).map_mul e (y k)
  have hfe : ∀ t : EAf D, toEAf D (GlobalTheory.AdelicLatMove.finEmb D t) = t := toEAf_finEmb
  rw [latHat_iff_hatL, hβ, hsw, Matrix.mulVec_smul]
  refine forall_congr' fun i => ?_
  have h1 : (toEAf D e • u) i = toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (u i)) := by
    rw [map_mul, hfe]; rfl
  have h2 : rdA φ (GlobalTheory.AdelicLatMove.finEmb D (u i)) =
      ((((frCo φ β)⁻¹ : GL (Fin V.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdA φ (y k)) i) := by
    rw [← hE, hfe, hu, RingHom.map_mulVec]
    unfold frCo
    rw [← map_inv]
    congr 1
    funext k
    exact hE (y k)
  rw [h1, show toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (u i)) =
      Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (e * GlobalTheory.AdelicLatMove.finEmb D (u i))) from rfl,
    comm_mem_intAf_iff, hπ.2.2.2, GlobalTheory.SplitHecke.isInt_Ov, HeightOneSpectrum.mem_adicCompletionIntegers, h2]

end GlobalTheory.SplitFrameColumn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceColumnMemCompletedLatticeIffFrameIntegStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_column_mem_completedLattice_iff_frame_integral : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (β : GL (Fin V.rank) (EAf D)), IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ y : Fin V.rank → AE D, (fun i => finPart D (e * y i)) ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ ∀ i, Valued.v ((((frCo φ β)⁻¹ : GL (Fin V.rank) (Fv D.host.F v)).1 *ᵥ fun k => rdA φ (y k)) i) ≤ 1 := by
  first | exact @GlobalTheory.SplitFrameColumn.frame_column | exact GlobalTheory.SplitFrameColumn.frame_column | (intros; apply GlobalTheory.SplitFrameColumn.frame_column <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphism
noncomputable section

namespace GlobalTheory.UnitaryIdemCut

section Gen

open Matrix Formalism.UG

variable {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

def cutM (b : A) (hb : b * b = b) : Matrix n n A →* Matrix n n A where
  toFun M := b • M + (1 - b) • 1
  map_one' := by rw [← add_smul]; simp
  map_mul' M N := by
    have h1 : b * (1 - b) = 0 := by linear_combination -hb
    have h2 : (1 - b) * b = 0 := by linear_combination -hb
    have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
    simp only [add_mul, mul_add, smul_mul_smul_comm, hb, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one]

def cutGL (b : A) (hb : b * b = b) : GL n A →* GL n A := Units.map (cutM b hb)

theorem cutGL_val (b : A) (hb : b * b = b) (g : GL n A) :
    (cutGL b hb g).val = b • g.val + (1 - b) • 1 := rfl

theorem map_cut (φ : A →+* B) (b : A) (M : Matrix n n A) :
    (b • M + (1 - b) • (1 : Matrix n n A)).map φ = φ b • M.map φ + (1 - φ b) • (1 : Matrix n n B) := by
  ext i j
  by_cases h : i = j <;> simp [h]

theorem bc_cutGL (φ : A →+* B) (b : A) (hb : b * b = b) (b' : B) (hb' : b' * b' = b') (e : φ b = b')
    (g : GL n A) : bc φ (cutGL b hb g) = cutGL b' hb' (bc φ g) := by
  subst e
  exact Units.ext (map_cut φ b g.val)

theorem bc_cutGL_eq_one (φ : A →+* B) (b : A) (hb : b * b = b) {g : GL n A} (hg : bc φ g = 1) :
    bc φ (cutGL b hb g) = 1 := by
  rw [bc_cutGL φ b hb _ (by rw [← map_mul, hb]) rfl, hg, map_one]

theorem cutGL_conj (b : A) (hb : b * b = b) (β g : GL n A) :
    cutGL b hb (β * g * β⁻¹) = β * cutGL b hb g * β⁻¹ := by
  apply Units.ext
  simp only [cutGL_val, Units.val_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]

theorem cutGL_mem_UJ (σ : A →+* A) (J : Matrix n n A) (b : A) (hb : b * b = b) (hσ : σ b = b) {g : GL n A}
    (hg : g ∈ UJ σ J) : cutGL b hb g ∈ UJ σ J := by
  have hg' : cT σ g.val * J * g.val = J := hg
  show cT σ (b • g.val + (1 - b) • 1) * J * (b • g.val + (1 - b) • 1) = J
  have e : cT σ (b • g.val + (1 - b) • (1 : Matrix n n A)) = b • cT σ g.val + (1 - b) • 1 := by
    unfold cT
    rw [map_cut, hσ, transpose_add, transpose_smul, transpose_smul, transpose_one]
  have h1 : b * (1 - b) = 0 := by linear_combination -hb
  have h2 : (1 - b) * b = 0 := by linear_combination -hb
  have h3 : (1 - b) * (1 - b) = 1 - b := by linear_combination hb
  rw [e]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, hb, h1, h2, h3, zero_smul, add_zero,
    zero_add, mul_one, one_mul, hg']
  rw [← add_smul]; simp

def cutUJ (σ : A →+* A) (J : Matrix n n A) (b : A) (hb : b * b = b) (hσ : σ b = b) : UJ σ J →* UJ σ J :=
  ((cutGL b hb).comp (UJ σ J).subtype).codRestrict _ fun g => cutGL_mem_UJ σ J b hb hσ g.2

end Gen

section Ad

open NumberField IsDedekindDomain Formalism.UG Formalism.L2.DIV
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem idem_mem_intAd (a : FiniteAdeleRing (𝓞 F) F) (ha : a * a = a) : a ∈ intAd F := by
  intro v
  have h : a v * a v = a v := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) ha
  rcases eq_or_ne (a v) 0 with h0 | h0
  · rw [h0]; exact zero_mem _
  · rw [mul_left_cancel₀ h0 (h.trans (mul_one _).symm)]; exact one_mem _

theorem cutGL_mem_St (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (b : E ⊗[F] Formalism.L2.Herm.Af F) (hb : b * b = b)
    (hi : b ∈ Formalism.L2.Herm.intAf F E) {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hg : g ∈ St β) :
    cutGL b hb g ∈ St β := by
  obtain ⟨y, rfl⟩ := hg
  refine ⟨cutGL (⟨b, hi⟩ : Formalism.L2.Herm.intAf F E) (Subtype.ext hb) y, ?_⟩
  show β * intGL F E n _ * β⁻¹ = cutGL b hb (β * intGL F E n y * β⁻¹)
  rw [cutGL_conj]
  unfold intGL
  rw [bc_cutGL _ _ _ b hb rfl]

theorem bc_cutGL_mem_St {A : Type} [CommRing A] (φ : A →+* E ⊗[F] Formalism.L2.Herm.Af F)
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (b : A) (hb : b * b = b)
    (hi : φ b ∈ Formalism.L2.Herm.intAf F E) {g : GL (Fin n) A} (hg : bc φ g ∈ St β) :
    bc φ (cutGL b hb g) ∈ St β := by
  have hb' : φ b * φ b = φ b := by rw [← map_mul, hb]
  rw [bc_cutGL φ b hb _ hb' rfl]
  exact cutGL_mem_St β _ hb' hi hg

end Ad

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sigR_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem exists_cutHA {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (r : R)
    (hb : algebraMap R (R ⊗[F] E) r * algebraMap R (R ⊗[F] E) r = algebraMap R (R ⊗[F] E) r) :
    ∃ κ : HA R σ J →* HA R σ J, ∀ g, HA.mat R σ J (κ g) = cutGL _ hb (HA.mat R σ J g) :=
  ⟨cutUJ (sigR R σ) (JR R J) _ hb (sigR_algebraMap R σ r), fun _ => rfl⟩

theorem mem_GfC_iff {D : D7} (V : HSp D) (g : GA D V) :
    g ∈ GfC V ↔ Formalism.UG.bc (infPart D) (matHom V g) = 1 := Iff.rfl

theorem finE_eq {D : D7} (V : HSp D) (g : GA D V) : finE V g = Formalism.UG.bc (toEAf D) (matHom V g) :=
  Units.ext (finE_val V g)

theorem exists_cut : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (ε : AF D.host.F), ε * ε = ε → ∃ κ : GA D V →* GA D V, ∀ g, Formalism.L2.Theta.mt V (κ g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ (Stab V β g → Stab V β (κ g)) := by
  intro D V β ε hε
  have hb : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε = algebraMap (AF D.host.F) (AE D) ε := by
    rw [← map_mul, hε]
  obtain ⟨κ, hκ⟩ := exists_cutHA (AF D.host.F) D.sp.cm.sig V.gram ε hb
  have hκ' : ∀ g, matHom V (κ g) = cutGL _ hb (matHom V g) := hκ
  refine ⟨κ, fun g => ⟨congrArg Units.val (hκ' g), fun h => ⟨?_, ?_⟩⟩⟩
  · have h1 := (mem_GfC_iff V g).1 h.1
    rw [mem_GfC_iff, hκ']
    exact bc_cutGL_eq_one (infPart D) _ hb h1
  · have h1 := h.2
    rw [finE_eq] at h1
    have hi : toEAf D (algebraMap (AF D.host.F) (AE D) ε) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨sndA D.host.F ε, idem_mem_intAd _ (by rw [← map_mul, hε])⟩, rfl⟩)
    rw [finE_eq, hκ']
    exact bc_cutGL_mem_St (toEAf D) β _ hb hi h1

end GlobalTheory.UnitaryIdemCut

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentTwistedGroupEndomorphismStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_twisted_group_endomorphism : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (ε : AF D.host.F), ε * ε = ε → ∃ κ : GA D V →* GA D V, ∀ g, Formalism.L2.Theta.mt V (κ g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) ∧ (Stab V β g → Stab V β (κ g)) := by
  first | exact @GlobalTheory.UnitaryIdemCut.exists_cut | exact GlobalTheory.UnitaryIdemCut.exists_cut | (intros; apply GlobalTheory.UnitaryIdemCut.exists_cut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedAutomorphicRightTranslationUnitarisableBo
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedAutomorphicRightTranslationUnitarisableBo
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct

namespace GlobalTheory.FinZeta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {V : HSp D} {ν : Measure (GA D V)} {𝓕 : Set (GA D V)}

private theorem zero_one_mem_gammaSet_one (f : bddAut V) : Continuous (f : GA D V → ℂ) ∧
    (∀ γ ∈ GQ V, ∀ g, (f : GA D V → ℂ) (γ * g) = (f : GA D V → ℂ) g) ∧
    ∃ C : ℝ, ∀ g, ‖(f : GA D V → ℂ) g‖ ≤ C := f.2

private theorem integrableOn_fundamentalDomain_of_bounded {E : Type} [NormedAddCommGroup E] (hν : ν.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) {φ : GA D V → E} (hφ : Continuous φ) (C : ℝ)
    (hC : ∀ g, ‖φ g‖ ≤ C) : IntegrableOn φ 𝓕 ν := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.1
  haveI := hT.2.2.2.1
  exact Measure.integrableOn_of_bounded
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓕 hν h𝓕).ne hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

theorem integrableOn_mul_conj_bddAut (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (f f₂ : bddAut V) :
    IntegrableOn (fun g => (f : GA D V → ℂ) g * starRingEnd ℂ ((f₂ : GA D V → ℂ) g)) 𝓕 ν := by
  obtain ⟨hc, -, C, hC⟩ := zero_one_mem_gammaSet_one f
  obtain ⟨hc₂, -, C₂, hC₂⟩ := zero_one_mem_gammaSet_one f₂
  refine integrableOn_fundamentalDomain_of_bounded hν h𝓕 (hc.mul (Complex.continuous_conj.comp hc₂)) (C * C₂) fun g => ?_
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC g) (hC₂ g) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

theorem exists_form_bddAut (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) :
    ∃ B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ, ∀ f f₂, B f f₂ = l2 ν 𝓕 (f : GA D V → ℂ) f₂ := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f f₂ : bddAut V => l2 ν 𝓕 (f : GA D V → ℂ) f₂) ?_ ?_ ?_ ?_, fun f f₂ => rfl⟩
  · intro a b c
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (integrableOn_mul_conj_bddAut hν h𝓕 a c) (integrableOn_mul_conj_bddAut hν h𝓕 b c)
  · intro c a b
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc]
    exact integral_const_mul c _
  · intro a b c
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_add, Pi.add_apply, map_add (f := _), mul_add]
    exact integral_add (integrableOn_mul_conj_bddAut hν h𝓕 a b) (integrableOn_mul_conj_bddAut hν h𝓕 a c)
  · intro c a b
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring

theorem petersson_self_re_pos_of_ne_zero (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (f : bddAut V) (hf : f ≠ 0) :
    0 < (l2 ν 𝓕 (f : GA D V → ℂ) f).re := by
  haveI := hν
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  obtain ⟨hc, hi, C, hC⟩ := zero_one_mem_gammaSet_one f
  have key : l2 ν 𝓕 (f : GA D V → ℂ) f =
      ((∫ x in 𝓕, Complex.normSq ((f : GA D V → ℂ) x) ∂ν : ℝ) : ℂ) := by
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, Complex.mul_conj]
    exact integral_ofReal
  rw [key, Complex.ofReal_re]
  have hint : IntegrableOn (fun x => Complex.normSq ((f : GA D V → ℂ) x)) 𝓕 ν :=
    integrableOn_fundamentalDomain_of_bounded hν h𝓕 (Complex.continuous_normSq.comp hc) (C * C) fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, sq]
      exact mul_le_mul (hC g) (hC g) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => Complex.normSq_nonneg _) hint]
  set U : Set (GA D V) := {x | (f : GA D V → ℂ) x ≠ 0} with hUdef
  have hsupp : Function.support (fun x => Complex.normSq ((f : GA D V → ℂ) x)) = U := by
    ext x
    simp [U, Complex.normSq_eq_zero]
  rw [hsupp]
  have hU : IsOpen U := isOpen_ne_fun hc continuous_const
  have hne : U.Nonempty := by
    by_contra hE
    rw [Set.not_nonempty_iff_eq_empty] at hE
    apply hf
    apply Subtype.ext
    funext x
    by_contra hx
    have hx' : x ∈ U := hx
    rw [hE] at hx'
    exact hx'
  refine pos_iff_ne_zero.2 fun h0 => (hU.measure_pos ν hne).ne' ?_
  have hsub : U ⊆ {x | ¬ ∃ γ : GQ V, γ • x ∈ 𝓕} ∪
      ⋃ γ : GQ V, (fun x => (γ : GA D V) * x) ⁻¹' (U ∩ 𝓕) := by
    intro x hx
    by_cases hx' : ∃ γ : GQ V, γ • x ∈ 𝓕
    · obtain ⟨γ, hγ⟩ := hx'
      refine Or.inr (Set.mem_iUnion.2 ⟨γ, ?_, hγ⟩)
      show (f : GA D V → ℂ) ((γ : GA D V) * x) ≠ 0
      rw [hi γ γ.2]
      exact hx
    · exact Or.inl hx'
  refine measure_mono_null hsub (measure_union_null (ae_iff.1 h𝓕.ae_covers) ?_)
  refine measure_iUnion_null fun γ => ?_
  rw [measure_preimage_mul]
  exact h0

theorem petersson_bounded_automorphic_right_translation_invariant (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 ν) (g : GA D V) (f f₂ : bddAut V) :
    l2 ν 𝓕 (bddRep V g f : GA D V → ℂ) (bddRep V g f₂ : GA D V → ℂ) = l2 ν 𝓕 (f : GA D V → ℂ) f₂ := by
  haveI := hν
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := hT.2.2.2.2.2.2
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V ν hν).1
  obtain ⟨-, hi, -⟩ := zero_one_mem_gammaSet_one f
  obtain ⟨-, hi₂, -⟩ := zero_one_mem_gammaSet_one f₂
  rw [coe_bddRep, coe_bddRep]
  simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, rTr]
  exact GlobalTheory.setIntegral_fundamentalDomain_mul_right h𝓕 g
    (fun x => (f : GA D V → ℂ) x * starRingEnd ℂ ((f₂ : GA D V → ℂ) x))
    fun γ hγ x => by simp only [hi γ hγ, hi₂ γ hγ]

end

theorem bddRep_unitarisable_and_bounded : ∀ (D : D7) (V : HSp D), IsUnitarisable (bddRep V) ∧ ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∀ f₂ : bddAut V, ∃ ℓ : bddAut V →ₗ[ℂ] ℂ, (∀ f : bddAut V, ℓ f = l2 ν 𝓕 (f : GA D V → ℂ) f₂) ∧ ∀ f : bddAut V, ∃ C : ℝ, ∀ g, ‖ℓ (bddRep V g f)‖ ≤ C := by
  intro D V
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  refine ⟨?_, fun ν 𝓕 hν h𝓕 f₂ => ?_⟩
  · have hH : (Measure.haar : Measure (GA D V)).IsHaarMeasure := inferInstance
    obtain ⟨𝓕, h𝓕⟩ :=
      (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V Measure.haar hH).2
    obtain ⟨B, hB⟩ := exists_form_bddAut hH h𝓕
    unfold IsUnitarisable
    refine ⟨B, fun v w => ?_, fun v hv => ?_, fun g v w => ?_⟩
    · rw [hB, hB]
      simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet]
      rw [← integral_conj]
      congr 1
      funext x
      rw [map_mul, Complex.conj_conj, mul_comm]
    · rw [hB]
      exact petersson_self_re_pos_of_ne_zero hH h𝓕 v hv
    · rw [hB, hB]
      exact petersson_bounded_automorphic_right_translation_invariant hH h𝓕 g v w
  · obtain ⟨B, hB⟩ := exists_form_bddAut hν h𝓕
    refine ⟨{ toFun := fun f => B f f₂, map_add' := fun a b => by simp, map_smul' := fun c a => by simp },
      fun f => hB f f₂, fun f => ?_⟩
    obtain ⟨-, -, C, hC⟩ := zero_one_mem_gammaSet_one f
    obtain ⟨-, -, C₂, hC₂⟩ := zero_one_mem_gammaSet_one f₂
    have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓕 hν h𝓕
    refine ⟨C * C₂ * (ν 𝓕).toReal, fun g => ?_⟩
    show ‖B (bddRep V g f) f₂‖ ≤ _
    rw [hB, coe_bddRep]
    simp only [GlobalTheory.AdelicScalar.l2, Formalism.IndefR.Lift.pet, rTr]
    refine norm_setIntegral_le_of_norm_le_const hfin fun x _ => ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC _) (hC₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))

end GlobalTheory.FinZeta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedAutomorphicRightTranslationUnitarisableBoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedAutomorphicRightTranslation_unitarisable_bounded : ∀ (D : D7) (V : HSp D), IsUnitarisable (bddRep V) ∧ ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν → ∀ f₂ : bddAut V, ∃ ℓ : bddAut V →ₗ[ℂ] ℂ, (∀ f : bddAut V, ℓ f = l2 ν 𝓕 (f : GA D V → ℂ) f₂) ∧ ∀ f : bddAut V, ∃ C : ℝ, ∀ g, ‖ℓ (bddRep V g f)‖ ≤ C := by
  first | exact @GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded | exact GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded | (intros; apply GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvalInjective
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvalAtUnitVector

theorem eval_injective : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S), ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) (d : ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), (∀ x y, inner ℂ x y = d * ipM M μ 𝓕 (e x) (e y)) → ∀ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) → Function.Injective (fun h : H => e h v) := by
  intro D V S M H _ _ e d μ 𝓕 hip v hv x y hxy
  have h0 : e (x - y) v = 0 := by
    rw [map_sub]
    exact sub_eq_zero.2 hxy
  have h1 := hip (x - y) (x - y)
  rw [ipM_self_eq_zero M μ 𝓕 _ v hv h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

end GlobalTheory.EvalAtUnitVector
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteThetaDatumNeZeroFrameAdjointSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteThetaDatumNeZeroFrameAdjointSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

theorem levDatum_ne_zero_spec {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) (x : WO S T) :
    levDatum S T βS βT LT Q m e x ≠ 0 → IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ (∀ PP, PP ∈ LT.Pg ∨ PP ∈ Q → IsUnit (topL T.rank (redM PP (frMapAdj S T βS βT x))).det) ∧ ∃ a : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1), (∀ PP : ↥LT.Pg, ((a PP : GL (Fin T.rank) (kP PP.1)) : Matrix (Fin T.rank) (Fin T.rank) (kP PP.1)) = topL T.rank (redM PP.1 (frMapAdj S T βS βT x))) ∧ (∀ PP : ↥LT.Pg, a PP ∈ blockTri (blkOf LT.r LT.t)) ∧ (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H := by
  intro hne
  unfold levDatum at hne
  split_ifs at hne with h0
  · refine ⟨h0.1, h0.2, ?_⟩
    have hG : omegaG LT m (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := left_ne_zero_of_mul hne
    have hQ : omegaQ Q T.rank m (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := right_ne_zero_of_mul hne
    unfold omegaG at hG
    unfold omegaQ at hQ
    split_ifs at hG with hg
    · split_ifs at hQ with hq
      · obtain ⟨a, ha1, ha2, ha3⟩ := hg.2
        refine ⟨?_, a, ha1, ha2, ha3⟩
        rintro PP (hP | hP)
        · rw [← ha1 ⟨PP, hP⟩]
          exact (a ⟨PP, hP⟩).isUnit.map Matrix.detMonoidHom
        · exact (hq PP hP).2
      · exact absurd rfl hQ
    · exact absurd rfl hG
  · exact absurd rfl hne

end GlobalTheory.FinZeta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFiniteThetaDatumNeZeroFrameAdjointSpecStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFiniteThetaDatum_ne_zero_frameAdjoint_spec : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D) (x : WO S T), levDatum S T βS βT LT Q m e x ≠ 0 → IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ (∀ PP, PP ∈ LT.Pg ∨ PP ∈ Q → IsUnit (topL T.rank (redM PP (frMapAdj S T βS βT x))).det) ∧ ∃ a : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1), (∀ PP : ↥LT.Pg, ((a PP : GL (Fin T.rank) (kP PP.1)) : Matrix (Fin T.rank) (Fin T.rank) (kP PP.1)) = topL T.rank (redM PP.1 (frMapAdj S T βS βT x))) ∧ (∀ PP : ↥LT.Pg, a PP ∈ blockTri (blkOf LT.r LT.t)) ∧ (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H := by
  first | exact @GlobalTheory.FinZeta.levDatum_ne_zero_spec | exact GlobalTheory.FinZeta.levDatum_ne_zero_spec | (intros; apply GlobalTheory.FinZeta.levDatum_ne_zero_spec <;> assumption)
end
end
