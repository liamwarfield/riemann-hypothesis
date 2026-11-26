module

public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.NonemptyThetaLOfTied
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.FilQuot

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.CrystallinePeriodRings.AwayExistsSelf
noncomputable section

namespace PositivityTheory.LocInh

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per6

section Abstract

theorem onto_eigen {A C : Type} [CommRing A] [CommRing C] {k : A →+* C}
    (hk : Function.Injective k) {G : C →+* C} {g : A →+* A} (hG : ∀ x, G (k x) = k (g x))
    {p m n : ℕ} {a : A} {y : C} (ha : k a = k (p : A) ^ m * y) (hy : G y = (p : C) ^ n * y) :
    g a = (p : A) ^ n * a := by
  apply hk
  rw [← hG, map_mul, map_pow, ha, map_mul, map_pow, map_natCast, map_natCast, hy]
  ring

theorem onto_fixed {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} {F : B →+* B}
    {g : A →+* A} (hF : ∀ x, F (f x) = f (g x)) {p t a : A} (hf : IsFrac f p t) (hp : g p = p)
    (ht : g t = p * t) (m : ℕ) {n : ℕ} (ha : g a = p ^ n * a) :
    ∃ x : B, F x = x ∧ f p ^ m * f t ^ n * x = f a := by
  obtain ⟨x, hx⟩ := ((hf.1.pow m).mul (hf.2.1.pow n)).exists_right_inv
  have e : f p ^ m * f t ^ n * (x * f a) = f a := by rw [← mul_assoc, hx, one_mul]
  refine ⟨x * f a, ?_, e⟩
  have h1 := congrArg F e
  rw [map_mul, map_mul, map_pow, map_pow, hF, hF, hF, hp, ht, ha, map_mul f, map_mul f,
    map_pow f] at h1
  refine ((hf.1.pow m).mul ((hf.1.mul hf.2.1).pow n)).mul_left_cancel (h1.trans ?_)
  conv_lhs => rw [← e]
  ring

theorem onto_cancel {A C E : Type} [CommRing A] [CommRing C] [Field E] {k : A →+* C}
    {I : C →+* E} {c : A →+* E} (hI : ∀ x, I (k x) = c x) {p a : A} (hp : c p ≠ 0) {m : ℕ}
    {y : C} (ha : k a = k p ^ m * y) {z : E} (h : c a = c p ^ m * z) : z = I y := by
  have h1 := congrArg I ha
  rw [map_mul, map_pow, hI, hI, h] at h1
  exact mul_left_cancel₀ (pow_ne_zero m hp) h1

theorem onto_injective {A C E : Type} [CommRing A] [CommRing C] [Field E] {k : A →+* C}
    {I : C →+* E} {c : A →+* E} (hI : ∀ x, I (k x) = c x) (hc : Function.Injective c) :
    Function.Injective k := fun x y e => hc (by rw [← hI, ← hI, e])

theorem away_exists_self {A : Type} [CommRing A] {a : A} (y : Localization.Away a) :
    ∃ (k : ℕ) (x : A), algebraMap A (Localization.Away a) x =
      algebraMap A (Localization.Away a) a ^ k * y :=
  away_exists (RingHom.id _) _ (fun _ => rfl) y

end Abstract

section Concrete

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem onto_plus {y : ACris.BCrisPlus ℂ_[l] l} {n : ℕ}
    (hy : ACris.phiPlus ℂ_[l] l y = (l : ACris.BCrisPlus ℂ_[l] l) ^ n * y) :
    ∃ x : Per6.Bcris l, Per6.φB l x = x ∧ cD l (Per6.tA l) ^ n * ιCD l x = invPlusD l y := by
  obtain ⟨m, a, ha⟩ := away_exists_self y
  have h1 := onto_eigen (onto_injective invPlusD_algebraMap (cD_injective l))
    ACris.phiPlus_algebraMap ha hy
  obtain ⟨x, hx, e⟩ := onto_fixed φB_cB (cB_isFrac l) (map_natCast _ l) frob_phi_tA m h1
  exact ⟨x, hx, onto_cancel invPlusD_algebraMap (cD_l_ne_zero l) ha (inv_map_frac (ιCD_fac l) e)⟩

theorem cD_tA_eq : cD l (Per6.tA l) =
    algebraMap (Per6.BdRp l) (Per6.BdR l) (fontaineT (epsilon l) untilt_epsilon) :=
  congrArg (algebraMap (Per6.BdRp l) (Per6.BdR l)) (ACris.iota_periodT (untilt_epsilon (p := l)))

theorem fund_onto (z : Per6.BdR l) : ∃ x : Per6.Bcris l, Per6.φB l x = x ∧
    ∃ c : Per6.BdRp l, ιCD l x - z = algebraMap (Per6.BdRp l) (Per6.BdR l) c := by
  obtain ⟨n, w, hs⟩ := ACris.exists_mul_pow_fontaineT_eq (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one z
  obtain ⟨y, hy, hyw⟩ := ACris.exists_phiPlus_eq_pow_iotaPlus_sub_mem (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one (m := n) (n := n) le_rfl w
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyw
  obtain ⟨x, hx, e⟩ := onto_plus hy
  rw [cD_tA_eq] at e
  exact ⟨x, hx, c, ACris.sub_eq_map_of_pow_mul (algebraMap (Per6.BdRp l) (Per6.BdR l))
    (cD_tA_eq (l := l) ▸ cD_tA_ne_zero l) e hs hc⟩

section Eps

variable {ε : PreTilt (normInteger ℂ_[l]) l} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[l]) l) l).symm ε) ≠ 1)




end Eps


end Concrete

end PositivityTheory.LocInh
end
end

section -- merged from Development.WeilBound.CoreStatements.CrystallinePeriodRings.FundIotaTANeZero
noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

section Abstract

theorem fund_eigen {A B : Type} [CommRing A] [CommRing B] {f : A →+* B}
    (hi : Function.Injective f) {F : B →+* B} {g : A →+* A} (hF : ∀ x, F (f x) = f (g x))
    {a t y : A} (ha : g a = a) (ht : g t = a * t) {b : B} (hb : F b = b) {m n : ℕ}
    (h : f a ^ m * f t ^ n * b = f y) : g y = a ^ n * y := by
  apply hi
  have h1 := congrArg F h
  rw [map_mul, map_mul, map_pow, map_pow, hF, hF, hF, ha, ht, hb, map_mul] at h1
  rw [← h1, map_mul, map_pow, ← h]
  ring

theorem fund_read {A B R E : Type} [CommRing A] [CommRing B] [CommRing R] [Field E]
    {f : A →+* B} {ι : B →+* E} {c : A →+* E} (hc : Fac ι f c) {i : A →+* R} {j : R →+* E}
    (hj : Function.Injective j) (e : ∀ x, c x = j (i x)) {a t y : A} {b : B} {z : R}
    (hz : ι b = j z) {m n : ℕ} (h : f a ^ m * f t ^ n * b = f y) :
    i y = i a ^ m * i t ^ n * z := by
  apply hj
  have h1 := congrArg ι h
  rw [map_mul, map_mul, map_pow, map_pow, hc, hc, hc, e, e, e, hz] at h1
  rw [← h1, map_mul, map_mul, map_pow, map_pow]

theorem fund_map_eigen {A C : Type} [CommRing A] [CommRing C] {k : A →+* C} {G : C →+* C}
    {g : A →+* A} (hG : ∀ x, G (k x) = k (g x)) {p n : ℕ} {y : A} (h : g y = (p : A) ^ n * y) :
    G (k y) = (p : C) ^ n * k y := by
  rw [hG, h, map_mul, map_pow, map_natCast]

theorem fund_mem_span {R : Type} [CommRing R] {w u T T' z : R} {m n : ℕ} (hT : T' = T)
    (h : w = u ^ m * T' ^ n * z) : w ∈ Ideal.span {T ^ n} :=
  Ideal.mem_span_singleton'.2 ⟨u ^ m * z, by rw [h, hT]; ring⟩

theorem fund_cancel {A C R Q : Type} [CommRing A] [CommRing C] [CommRing R] [IsDomain R] [Field Q]
    {k : A →+* C} {i : A →+* R} {I : C →+* R} (hI : ∀ x, I (k x) = i x) {r : Q →+* C}
    {s : Q →+* R} (hr : ∀ q, I (r q) = s q) {p m n : ℕ} (hp : (p : Q) ≠ 0) {t y : A}
    (ht : i t ≠ 0) {z : R} (h : i y = i (p : A) ^ m * i t ^ n * z) {q : Q}
    (hq : k y = r q * k t ^ n) : z = s (q / (p : Q) ^ m) := by
  have h1 := congrArg I hq
  rw [map_mul, map_pow, hI, hI, hr, h, map_natCast, mul_right_comm] at h1
  have h2 := mul_right_cancel₀ (pow_ne_zero n ht) h1
  have h3 : s (((p : Q) ^ m)⁻¹) * (p : R) ^ m = 1 := by
    rw [← map_natCast s, ← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero m hp), map_one]
  rw [div_eq_inv_mul, map_mul, ← h2, ← mul_assoc, h3, one_mul]

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem fund_iota_tA : ACris.iota ℂ_[l] l (Per6.tA l) = fontaineT (epsilon l) untilt_epsilon :=
  ACris.iota_periodT (untilt_epsilon (p := l))

theorem fund_iota_tA_ne_zero : ACris.iota ℂ_[l] l (Per6.tA l) ≠ 0 :=
  fund_iota_tA (l := l) ▸ fontaineT_ne_zero untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one

theorem fund_core {y : ACris.ACris ℂ_[l] l} {m n : ℕ} {z : Per6.BdRp l}
    (hy : ACris.phi (K := ℂ_[l]) (p := l) y = (l : ACris.ACris ℂ_[l] l) ^ n * y)
    (hz : ACris.iota ℂ_[l] l y = ACris.iota ℂ_[l] l (l : ACris.ACris ℂ_[l] l) ^ m *
      ACris.iota ℂ_[l] l (Per6.tA l) ^ n * z) :
    ∃ q : ℚ_[l], z = algebraMap ℚ_[l] (Per6.BdRp l) q := by
  obtain ⟨q, hq⟩ := ACris.exists_eq_algebraMap_mul_pow_of_phiPlus_eq (untilt_epsilon (p := l))
    untilt_frobeniusEquiv_symm_epsilon_ne_one n
    (fund_map_eigen ACris.phiPlus_algebraMap hy)
    (fund_mem_span fund_iota_tA ((ACris.iotaPlus_algebraMap y).trans hz))
  exact ⟨_, fund_cancel ACris.iotaPlus_algebraMap ACris.iotaPlus_algebraMap_padic
    (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) fund_iota_tA_ne_zero hz hq⟩

theorem fund_ιCD_qB (q : ℚ_[l]) : ιCD l (qB l q) =
    algebraMap (Per6.BdRp l) (Per6.BdR l) (algebraMap ℚ_[l] (Per6.BdRp l) q) := by
  refine (ιCD_qB q).trans ?_
  rw [frob_oD_apply, AlgHom.commutes]

theorem fund (b : Per6.Bcris l) (hφ : Per6.φB l b = b) (hb : ιCD l b ∈ Per6.FilD l 0) :
    ∃ q : ℚ_[l], qB l q = b := by
  obtain ⟨m, n, y, h⟩ := bcris_surj b
  obtain ⟨z, hz⟩ := (IsPerfectoidField.mem_fil_zero_iff ℂ_[l] l).1 hb
  obtain ⟨q, hq⟩ := fund_core
    (fund_eigen frob_cB_injective φB_cB (map_natCast _ l) frob_phi_tA hφ h)
    (fund_read (ιCD_fac l)
      (IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)) cD_apply hz h)
  exact ⟨q, ιCD_injective ((fund_ιCD_qB q).trans
    ((congrArg (algebraMap (Per6.BdRp l) (Per6.BdR l)) hq).symm.trans hz.symm))⟩

end PositivityTheory.LocInh
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace period_ring_base

open Formalism.Per6 hiding σB aB
open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst Matrix

namespace BaseA

variable (l : ℕ) [Fact l.Prime]

theorem isCrisDR_ι : IsCrisDR l (ι l) := fun x => Loc2.lift_mk₀ _ _ _ x

theorem ι_eq : ι l = PositivityTheory.LocInh.ιCD l := (PositivityTheory.LocInh.isCrisDR_iff _).1 (isCrisDR_ι l)

theorem qB_eq : qB l = PositivityTheory.LocInh.qB l :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext fun z => by
    rw [RingHom.comp_apply, RingHom.comp_apply, qB, IsLocalization.lift_eq]
    exact (PositivityTheory.LocInh.qB_coe z).symm)

theorem ι_cB (y : ACris.ACris ℂ_[l] l) : ι l (cB l y) = iC l y := Loc2.lift_mk₀ _ _ _ y

end BaseA

open BaseA

theorem base_ι_inj (l : ℕ) [Fact l.Prime] : Function.Injective (ι l) := by
  rw [ι_eq]; exact PositivityTheory.LocInh.ιCD_injective

theorem base_dom (l : ℕ) [Fact l.Prime] : IsDomain (B l) :=
  Function.Injective.isDomain (ι l) (base_ι_inj l)

theorem base_σ_one (l : ℕ) [Fact l.Prime] : σB (1 : GQ l) = RingHom.id _ :=
  RingHom.ext fun b => PositivityTheory.LocInh.σB_one b

theorem base_σ_mul (l : ℕ) [Fact l.Prime] : ∀ g h : GQ l, σB (g * h) = (σB g).comp (σB h) :=
  fun g h => RingHom.ext fun b => PositivityTheory.LocInh.σB_mul g h b

theorem base_φ_σ (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l) x, φ l (σB g x) = σB g (φ l x) :=
  fun g x => PositivityTheory.LocInh.φB_σB g x

theorem base_ι_σ (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l) x, ι l (σB g x) = σD g (ι l x) := by
  intro g x; rw [ι_eq]; exact PositivityTheory.LocInh.ιCD_σB g x

theorem base_φ_q (l : ℕ) [Fact l.Prime] : ∀ q, φ l (qB l q) = qB l q := by
  intro q; rw [qB_eq]; exact PositivityTheory.LocInh.φB_qB q

theorem base_σ_q (l : ℕ) [Fact l.Prime] : ∀ (g : GQ l) q, σB g (qB l q) = qB l q := by
  intro g q
  apply base_ι_inj l
  rw [base_ι_σ, ι_eq, qB_eq, PositivityTheory.LocInh.ιCD_qB, PositivityTheory.LocInh.σD_oD, AlgEquiv.commutes]

theorem base_ι_q (l : ℕ) [Fact l.Prime] : ∀ q, ι l (qB l q) = qQ l q := by
  intro q; rw [ι_eq, qB_eq]; exact PositivityTheory.LocInh.fund_ιCD_qB q

theorem period_image_eq (l : ℕ) [Fact l.Prime] : ι l (t l) = tQ l := ι_cB l (tA l)

theorem base_t_unit (l : ℕ) [Fact l.Prime] : IsUnit (t l) := Loc2.isUnit_right _ _

theorem frobenius_period_holds (l : ℕ) [Fact l.Prime] : φ l (t l) = (l : B l) * t l := PositivityTheory.LocInh.φB_tB

theorem galois_period_cyclotomic (l : ℕ) [Fact l.Prime] : ∀ g : GQ l, σB g (t l) = qB l (χ g) * t l := by
  intro g; rw [qB_eq]; exact PositivityTheory.LocInh.σB_tB g

theorem base_χ_cont (l : ℕ) [Fact l.Prime] : Continuous (χ : GQ l → ℚ_[l]) :=
  by
  have h1 : Continuous (fun g : GQ l => ((DeRhamTwist.Twist.chi0 l g : ℤ_[l]ˣ) : ℤ_[l])) :=
    Units.continuous_val.comp (DeRhamTwist.Twist.continuous_cyclotomic_character (l := l))
  have h2 : Continuous (fun x : ℤ_[l] => (x : ℚ_[l])) := by
    first
    | exact PadicInt.continuous_coe
    | exact continuous_subtype_val
    | exact (Isometry.of_dist_eq fun _ _ => rfl).continuous
  exact h2.comp h1

theorem base_ι_Bst (l : ℕ) [Fact l.Prime] : ∀ x, ι l x ∈ Bst l := by
  intro x
  obtain ⟨m, n, y, h⟩ := PositivityTheory.LocInh.bcris_surj x
  have h1 := congrArg (ι l) h
  have hl : ι l (cB l (l : ACris.ACris ℂ_[l] l)) = (l : BdR l) := by rw [map_natCast, map_natCast]
  rw [map_mul, map_mul, map_pow, map_pow, hl, ι_cB, ι_cB] at h1
  have htq : iC l (tA l) = tQ l := rfl
  rw [htq] at h1
  have hl0 : (l : BdR l) ≠ 0 := by
    have := (isUnit_l l).map (ι l)
    rw [map_natCast] at this
    exact this.ne_zero
  have ht0 : tQ l ≠ 0 := DeRhamTwist.Twist.tQ_ne
  have e : ι l x = iC l y * ((l : BdR l)⁻¹) ^ m * ((tQ l)⁻¹) ^ n := by
    rw [← h1, inv_pow, inv_pow]
    field_simp
  rw [e]
  have mem : ∀ z ∈ ({((l : BdR l))⁻¹, (tQ l)⁻¹, uQ l} : Set (BdR l)), z ∈ Bst l :=
    fun z hz => Subring.subset_closure (Or.inr hz)
  exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨y, rfl⟩))
    (Subring.pow_mem _ (mem _ (by simp)) _)) (Subring.pow_mem _ (mem _ (by simp)) _)

theorem base_u_Bst (l : ℕ) [Fact l.Prime] : uQ l ∈ Bst l :=
  Subring.subset_closure (Or.inr (by simp))

theorem base_fs_ker (l : ℕ) [Fact l.Prime] : ∀ x, φ l x = x → ι l x ∈ Plus l → ∃ q, x = qB l q := by
  intro x hφ hx
  obtain ⟨z, hz⟩ := RingHom.mem_range.1 hx
  rw [ι_eq] at hz
  obtain ⟨q, hq⟩ := PositivityTheory.LocInh.fund x hφ ((IsPerfectoidField.mem_fil_zero_iff ℂ_[l] l).2 ⟨z, hz.symm⟩)
  exact ⟨q, by rw [qB_eq]; exact hq.symm⟩

theorem base_fs_surj (l : ℕ) [Fact l.Prime] : ∀ z : BdR l, ∃ x, φ l x = x ∧ ι l x - z ∈ Plus l := by
  intro z
  obtain ⟨x, hφ, c, hc⟩ := PositivityTheory.LocInh.fund_onto z
  exact ⟨x, hφ, RingHom.mem_range.2 ⟨c, by rw [ι_eq]; exact hc.symm⟩⟩

end period_ring_base
