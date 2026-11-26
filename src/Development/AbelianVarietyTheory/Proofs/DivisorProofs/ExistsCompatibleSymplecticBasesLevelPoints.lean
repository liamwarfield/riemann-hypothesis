module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WpQTrivRight
noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex

namespace GlobalTheory.SympQ

variable {O : Type} [CommRing O] (N : NumD O)

def trivHom (k : ℕ) : Multiplicative N.X →* N.QT k where
  toFun z := N.qTriv k z.toAdd
  map_one' := Subtype.ext (Prod.ext (by simp [NumD.qTriv]) (by simp [NumD.qTriv, N.io_zero]))
  map_mul' a b := Subtype.ext (Prod.ext (by simp [NumD.qTriv, smul_add]) (by simp [NumD.qTriv, N.io_add]))

abbrev Qq (k : ℕ) : Type := N.QT k ⧸ (trivHom N k).range

theorem qEq_iff_mk_eq {k : ℕ} (p p' : N.QT k) : N.QEq p p' ↔ (QuotientGroup.mk p : Qq N k) = QuotientGroup.mk p' := by
  rw [N.qEq_iff, QuotientGroup.eq]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Multiplicative.ofAdd z, by simp [trivHom]⟩
  · rintro ⟨z, hz⟩
    refine ⟨z.toAdd, ?_⟩
    change N.qTriv k z.toAdd = p⁻¹ * p' at hz
    rw [hz, mul_inv_cancel_left]

def pushRep (M n : ℕ) : N.QT M →* N.QT n :=
  if h : n ∣ M then
    { toFun := fun p => ⟨(p.1.1, p.1.2 ^ (M / n)), by
        rw [NumD.mem_QT, ← pow_mul, Nat.div_mul_cancel h]
        exact p.2⟩
      map_one' := Subtype.ext (Prod.ext rfl (by simp))
      map_mul' := fun p q => Subtype.ext (Prod.ext rfl (by simp [mul_pow])) }
  else 1

theorem pushRep_fst {M n : ℕ} (h : n ∣ M) (p : N.QT M) : (pushRep N M n p).1.1 = p.1.1 := by
  simp [pushRep, h]

theorem pushRep_snd {M n : ℕ} (h : n ∣ M) (p : N.QT M) : (pushRep N M n p).1.2 = p.1.2 ^ (M / n) := by
  simp [pushRep, h]

theorem pushRep_triv (M n : ℕ) : (trivHom N M).range ≤ (trivHom N n).range.comap (pushRep N M n) := by
  rintro _ ⟨z, rfl⟩
  by_cases h : n ∣ M
  · refine ⟨Multiplicative.ofAdd ((M / n) • z.toAdd), Subtype.ext (Prod.ext ?_ ?_)⟩
    · simp only [trivHom, MonoidHom.coe_mk, OneHom.coe_mk, NumD.qTriv, toAdd_ofAdd]
      rw [pushRep_fst N h, smul_smul, Nat.mul_div_cancel' h]
    · simp only [trivHom, MonoidHom.coe_mk, OneHom.coe_mk, NumD.qTriv, toAdd_ofAdd]
      rw [pushRep_snd N h, N.io_nsmul]
  · simp [pushRep, h]

def pushQ (M n : ℕ) : Qq N M →* Qq N n := QuotientGroup.map _ _ (pushRep N M n) (pushRep_triv N M n)

theorem pushQ_mk (M n : ℕ) (p : N.QT M) :
    pushQ N M n (QuotientGroup.mk p) = QuotientGroup.mk (pushRep N M n p) := rfl

theorem wp_qTriv_right {k : ℕ} (p : N.QT k) (z : N.X) : N.wp p (N.qTriv k z) = 1 := by
  rw [← inv_inj, ← NumD.wp_swap, WpPairing.wp_qTriv, inv_one]

theorem wp_congr {k : ℕ} {p p' q q' : N.QT k} (hp : N.QEq p p') (hq : N.QEq q q') : N.wp p q = N.wp p' q' := by
  obtain ⟨z, rfl⟩ := (N.qEq_iff _ _).1 hp
  obtain ⟨w, rfl⟩ := (N.qEq_iff _ _).1 hq
  rw [WpPairing.wp_mul_left, WpPairing.wp_mul_right, WpPairing.wp_mul_right, WpPairing.wp_qTriv,
    WpPairing.wp_qTriv, wp_qTriv_right]
  simp

def wpQ (k : ℕ) (x y : Qq N k) : Oˣ :=
  Quotient.liftOn₂' x y (fun p q => N.wp p q) fun p q p' q' hp hq =>
    wp_congr N ((qEq_iff_mk_eq N _ _).2 (Quotient.sound' hp)) ((qEq_iff_mk_eq N _ _).2 (Quotient.sound' hq))

theorem wpQ_mk (k : ℕ) (p q : N.QT k) : wpQ N k (QuotientGroup.mk p) (QuotientGroup.mk q) = N.wp p q := rfl

end GlobalTheory.SympQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingNondegenerate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingNondegenerate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.SympQ

theorem qEq_one_of_wp {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ} (hk : (k : C) ≠ 0)
    (hdiv : ∀ x : N.A, ∃ y, y ^ k = x)
    (nd : ∀ b : N.A, b ^ k = 1 → (∀ b', b' ^ k = 1 → N.weil k b b' = 1) → b = 1) (p : N.QT k)
    (hp : ∀ p', N.wp p p' = 1) : N.QEq p 1 := by
  have hk0 : k ≠ 0 := fun h => hk (by rw [h, Nat.cast_zero])
  have h3 : ∀ y : N.X, ∃ p : N.QT k, p.1.1.toAdd = y := fun y => by
    obtain ⟨b, hb⟩ := hdiv (N.io y).b
    obtain ⟨g, -, h⟩ := QStr.root_over N hk0 (N.io y) b hb
    exact ⟨⟨(Multiplicative.ofAdd y, g), h⟩, rfl⟩
  obtain ⟨p₀, hq, h1, hb⟩ := (QStr.orth_iff N hk nd p).1 fun p' _ => hp p'
  have : p₀ = 1 := by
    refine Subtype.ext (Prod.ext h1 (NumD.Gt.ext hb (funext fun χ => ?_)))
    obtain ⟨p', rfl⟩ := h3 χ
    rw [← (WpPairing.wp_pairing C N _ p₀ p' p').2.2.2.2.2.1 h1 hb, ← WpPairing.wp_congr_left N hq p', hp p']
    rfl
  rwa [this] at hq

theorem wpQ_nondeg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → ∀ x : GlobalTheory.SympQ.Qq N n, (∀ y, GlobalTheory.SympQ.wpQ N n x y = 1) → x = 1 := by
  intro R _ _ _ hR D F _ _ _ N ν n hn x hx
  obtain ⟨⟨h1, h2, h3, h4⟩, hc⟩ := hR
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  have : CharZero F := by
    have : CharZero (FractionRing R) := inferInstance
    exact charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have h0 : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨hW, -⟩ := GlobalTheory.ThetaInValues.brUth_of_laws hL R D.toPre D.psi_even D.tau_bimult F N ν
  have tor : ∀ (b : N.A) (k : ℕ), ν.eA b ^ k = 1 ↔ b ^ k = 1 := fun b k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  induction x using QuotientGroup.induction_on with
  | H p =>
    have hq : N.QEq p 1 := by
      refine qEq_one_of_wp N h0 (fun a => ?_) (fun b hb h => ?_) p fun p' => hx (QuotientGroup.mk p')
      · obtain ⟨y, hy⟩ := GlobalTheory.ValuesTorsion.exists_pow_eq hL D.toPre.P (jFK (R := R) F ≫ jK R) (ν.eA a) hn
        exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
      · refine ν.eA.map_eq_one_iff.1 (GlobalTheory.ThetaRep.eq_one_of_weilIs hL D.toPre.P (jFK (R := R) F ≫ jK R) h0 _
          ((tor _ _).2 hb) fun y hy => ?_)
        obtain ⟨b', rfl⟩ := ν.eA.surjective y
        have hb' := (tor _ _).1 hy
        have := hW n hn b b' hb hb'
        rwa [h b' hb', show unitOn (1 : Fˣ) = 1 from map_one (Units.map _)] at this
    exact (qEq_iff_mk_eq N p 1).1 hq

end GlobalTheory.SympQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingNondegenerateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reprModTrivialQuotient_pairing_nondegenerate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → ∀ x : GlobalTheory.SympQ.Qq N n, (∀ y, GlobalTheory.SympQ.wpQ N n x y = 1) → x = 1 := by
  first | exact @GlobalTheory.SympQ.wpQ_nondeg | exact GlobalTheory.SympQ.wpQ_nondeg | (intros; apply GlobalTheory.SympQ.wpQ_nondeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingLevelPushEqPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingLevelPushEqPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SympQ.PushPow

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

theorem cubN_mul_iter (h : IsCub θ) (n m : ℕ) (b x : A) :
    cubN θ (n * m) 1 b x = cubN θ n 1 (b ^ m) x * cubN θ m 1 b x ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e : cubN θ ((n + 1) * m) 1 b x = cubN θ (n * m) 1 b x * cubN θ m (b ^ (n * m)) b x := by
      rw [Nat.succ_mul]
      simp only [cubN, Finset.prod_range_add]
      refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
      rw [_root_.one_mul, pow_add]
    have s1 : cubN θ (n + 1) 1 (b ^ m) x = cubN θ n 1 (b ^ m) x * θ ((b ^ m) ^ n) (b ^ m) x := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    rw [e, ih, h.N_split m (b ^ (n * m)) b x, s1, ← pow_mul' b n m, pow_succ (cubN θ m 1 b x) n]
    ac_rfl

theorem cubN_pow_right (h : IsCub θ) (k m : ℕ) (b x : A) :
    cubN θ k 1 b (x ^ m) * cubN θ m 1 x b ^ k = cubN θ k 1 b x ^ m * cubN θ m 1 x (b ^ k) := by
  induction m with
  | zero => simp [cubN, h.face₃]
  | succ m ih =>
    have e := h.N_add k 1 b (x ^ m) x
    rw [h.face, _root_.mul_one, _root_.one_mul] at e
    have s1 : cubN θ (m + 1) 1 x b = cubN θ m 1 x b * θ (x ^ m) x b := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have s2 : cubN θ (m + 1) 1 x (b ^ k) = cubN θ m 1 x (b ^ k) * θ (x ^ m) x (b ^ k) := by
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul]
    have t1 : θ b (x ^ m) x = θ (x ^ m) x b := by rw [h.s01, h.s12]
    have t2 : θ (b ^ k) (x ^ m) x = θ (x ^ m) x (b ^ k) := by rw [h.s01, h.s12]
    rw [t1, t2] at e
    rw [pow_succ x, s1, s2]
    apply Additive.ofMul.injective
    replace e := congrArg Additive.ofMul e
    replace ih := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow] at e ih ⊢
    linear_combination (norm := module) e + ih

variable {O : Type} [CommRing O] (N : NumD O)

theorem wp_pushRep (n m : ℕ) (hn : 0 < n) (p q : N.QT (n * m)) :
    N.wp (pushRep N (n * m) n p) (pushRep N (n * m) n q) = N.wp p q ^ m := by
  have hd : n ∣ n * m := dvd_mul_right n m
  have hM : n * m / n = m := Nat.mul_div_cancel_left m hn
  simp only [NumD.wp, NumD.tk, pushRep_fst N hd, pushRep_snd N hd, hM, NumD.Gt.pow_b]
  have ps1 := NumD.Gt.pow_s p.1.2 m q.1.1.toAdd
  have ps2 := NumD.Gt.pow_s q.1.2 m p.1.1.toAdd
  rw [← N.QT_pow_b q] at ps1
  rw [← N.QT_pow_b p] at ps2
  have i1 := cubN_mul_iter N.cub n m q.1.2.b p.1.2.b
  have i2 := cubN_mul_iter N.cub n m p.1.2.b q.1.2.b
  have a := cubN_pow_right N.cub n m (p.1.2.b ^ m) q.1.2.b
  have b := cubN_pow_right N.cub n m (q.1.2.b ^ m) p.1.2.b
  have c := cubN_pow_right N.cub m m q.1.2.b p.1.2.b
  rw [← pow_mul'] at a b
  apply Additive.ofMul.injective
  replace ps1 := congrArg Additive.ofMul ps1
  replace ps2 := congrArg Additive.ofMul ps2
  replace i1 := congrArg Additive.ofMul i1
  replace i2 := congrArg Additive.ofMul i2
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at ps1 ps2 i1 i2 a b c ⊢
  linear_combination (norm := module) ps1 - ps2 - (m : ℤ) • i1 + (m : ℤ) • i2 + b - a + (n : ℤ) • c

end GlobalTheory.SympQ.PushPow

theorem GlobalTheory.SympQ.wp_pushRep_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n m : ℕ), 0 < n → 0 < m → ∀ p q : N.QT (n * m), N.wp (GlobalTheory.SympQ.pushRep N (n * m) n p) (GlobalTheory.SympQ.pushRep N (n * m) n q) = N.wp p q ^ m := by
  intro R _ _ _ _ D F _ _ _ N ν n m hn hm p q
  exact GlobalTheory.SympQ.PushPow.wp_pushRep N n m hn p q
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingLevelPushEqPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reprModTrivialQuotient_pairing_levelPush_eq_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n m : ℕ), 0 < n → 0 < m → ∀ p q : N.QT (n * m), N.wp (GlobalTheory.SympQ.pushRep N (n * m) n p) (GlobalTheory.SympQ.pushRep N (n * m) n q) = N.wp p q ^ m := by
  first | exact @GlobalTheory.SympQ.wp_pushRep_pow | exact GlobalTheory.SympQ.wp_pushRep_pow | (intros; apply GlobalTheory.SympQ.wp_pushRep_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientFreeRankTwiceDimension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientFreeRankTwiceDimension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.SympQ
open GlobalTheory.Ex

theorem qq_free_of_torsion {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) {k : ℕ} (hk : (k : C) ≠ 0) (a : ℕ)
    (hdiv : ∀ x : N.A, ∃ y, y ^ k = x)
    (e : (powMonoidHom k : N.A →* N.A).ker ≃* Multiplicative (Fin a → ZMod k)) :
    Nonempty (Qq N k ≃* Multiplicative (Fin (Module.finrank ℤ N.X + (a + Module.finrank ℤ N.X)) → ZMod k)) := by
  haveI : NeZero k := ⟨by rintro rfl; simp at hk⟩
  have hk0 : k ≠ 0 := NeZero.ne k
  obtain ⟨f⟩ := QStr.ker_struct N hk a e
  let v := Module.finBasis ℤ N.X
  let i₀ : (powMonoidHom k : N.Gt →* N.Gt).ker →* N.QT k := MonoidHom.mk'
    (fun g => ⟨(1, g.1), (show g.1 ^ k = 1 from g.2).trans N.io_zero.symm⟩)
    fun g g' => Subtype.ext (Prod.ext (_root_.mul_one _).symm rfl)
  let π₀ : N.QT k →* Multiplicative (Fin (Module.finrank ℤ N.X) → ZMod k) := MonoidHom.mk'
    (fun p => Multiplicative.ofAdd fun i => (v.repr p.1.1.toAdd i : ZMod k)) fun p q => by
      refine Multiplicative.toAdd.injective (funext fun i => ?_)
      simp
  have hπ₀ : ∀ p, π₀ p = 1 ↔ ∃ z : N.X, p.1.1.toAdd = k • z := fun p => by
    constructor
    · intro h
      have hd : ∀ i, (k : ℤ) ∣ v.repr p.1.1.toAdd i := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (congrFun (congrArg Multiplicative.toAdd h) i)
      choose c hc using hd
      refine ⟨∑ i, c i • v i, ?_⟩
      conv_lhs => rw [← v.sum_repr p.1.1.toAdd]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc, mul_smul, natCast_zsmul]
    · rintro ⟨z, hz⟩
      refine Multiplicative.toAdd.injective (funext fun i => ?_)
      change ((v.repr p.1.1.toAdd i : ℤ) : ZMod k) = 0
      rw [hz]
      simp
  let π : Qq N k →* Multiplicative (Fin (Module.finrank ℤ N.X) → ZMod k) :=
    QuotientGroup.lift _ π₀ (by
      rintro _ ⟨z, rfl⟩
      exact (hπ₀ _).2 ⟨z.toAdd, rfl⟩)
  refine QStr.split_ext k _ _ ?_ (((QuotientGroup.mk' _).comp i₀).comp f.symm.toMonoidHom) π ?_ ?_ ?_
  · intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨p.1.1, Subtype.ext (Prod.ext rfl (N.mem_QT.1 p.2).symm)⟩
  · refine Function.Injective.comp (g := (QuotientGroup.mk' _).comp i₀) ?_ f.symm.injective
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨z, hz⟩ := (QuotientGroup.eq_one_iff _).1 hg
    have h1 : k • z.toAdd = 0 := congrArg (fun q : N.QT k => q.1.1.toAdd) hz
    have h2 : N.io z.toAdd = g.1 := congrArg (fun q : N.QT k => q.1.2) hz
    have h3 : z.toAdd = 0 := (smul_eq_zero.1 ((natCast_zsmul _ _).trans h1)).resolve_left (Nat.cast_ne_zero.2 hk0)
    exact Subtype.ext (by rw [← h2, h3, N.io_zero]; rfl)
  · intro c
    let y : N.X := ∑ i, ((c.toAdd i).val : ℤ) • v i
    obtain ⟨b, hb⟩ := hdiv (N.io y).b
    obtain ⟨u, -, hu⟩ := QStr.root_over N hk0 (N.io y) b hb
    refine ⟨QuotientGroup.mk ⟨(Multiplicative.ofAdd y, u), hu⟩, Multiplicative.toAdd.injective (funext fun i => ?_)⟩
    change ((v.repr y i : ℤ) : ZMod k) = c.toAdd i
    have : v.repr y i = ((c.toAdd i).val : ℤ) := congrFun (v.repr_sum_self _) i
    rw [this]
    simp
  · intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    constructor
    · intro h
      obtain ⟨z, hz⟩ := (hπ₀ p).1 h
      have hg : (p.1.2 * (N.io z)⁻¹) ^ k = 1 := by
        rw [mul_pow, inv_pow, N.mem_QT.1 p.2, hz, N.io_nsmul, mul_inv_cancel]
      refine ⟨f ⟨_, hg⟩, ?_⟩
      change QuotientGroup.mk (i₀ (f.symm (f ⟨_, hg⟩))) = _
      rw [f.symm_apply_apply, ← qEq_iff_mk_eq]
      exact ⟨z, hz.trans (zero_add _).symm, (inv_mul_cancel_right _ _).symm⟩
    · rintro ⟨y, hy⟩
      rw [← hy]
      exact (hπ₀ (i₀ (f.symm y))).2 ⟨0, (smul_zero _).symm⟩

theorem qq_free : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → Nonempty (Additive (GlobalTheory.SympQ.Qq N n) ≃+ (Fin (2 * (D.toPre.P.g + Module.finrank ℤ D.toPre.X)) → ZMod n)) := by
  intro R _ _ _ hR D F _ _ _ N ν n hn
  have hL : Laws := GlobalTheory.allSixLaws.1
  haveI : IsNoetherianRing R := hR.1.1
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  have hk : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have tor : ∀ (b : N.A) (k : ℕ), ν.eA b ^ k = 1 ↔ b ^ k = 1 := fun b k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have hdiv : ∀ x : N.A, ∃ y, y ^ n = x := fun x => by
    obtain ⟨y, hy⟩ := ValuesTorsion.exists_pow_eq hL D.toPre.P (jFK (R := R) F ≫ jK R) (ν.eA x) hn
    exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
  obtain ⟨e⟩ : Nonempty ((powMonoidHom n : N.A →* N.A).ker ≃* Multiplicative (Fin (2 * D.toPre.P.g) → ZMod n)) := by
    obtain ⟨v, hv, h⟩ := ValuesTorsion.exists_basis hL D.toPre.P (jFK (R := R) F ≫ jK R) hk
    refine ValuesTorsion.nonempty_equiv_of_basis hn.ne' (fun i => ν.eA.symm (v i))
      (fun i => by rw [← map_pow, hv, map_one]) fun y hy => ?_
    refine (existsUnique_congr fun c => ?_).1 (h (ν.eA y) ((tor _ _).2 hy))
    simp only [List.prod_ofFn, ← map_pow, ← map_prod, MulEquiv.symm_apply_eq]
  obtain ⟨f⟩ := qq_free_of_torsion N hk _ hdiv e
  have hr : Module.finrank ℤ N.X = Module.finrank ℤ D.toPre.X := ν.eX.toIntLinearEquiv.finrank_eq
  have h2 : Module.finrank ℤ N.X + (2 * D.toPre.P.g + Module.finrank ℤ N.X) =
      2 * (D.toPre.P.g + Module.finrank ℤ D.toPre.X) := by rw [hr]; ring
  rw [← h2]
  exact ⟨MulEquiv.toAdditiveLeft f⟩

end GlobalTheory.SympQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientFreeRankTwiceDimensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reprModTrivialQuotient_free_rank_twice_dimension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : GlobalTheory.Ex.NumD F) (ν : GlobalTheory.Ex.NumOf D.toPre F N) (n : ℕ), 0 < n → Nonempty (Additive (GlobalTheory.SympQ.Qq N n) ≃+ (Fin (2 * (D.toPre.P.g + Module.finrank ℤ D.toPre.X)) → ZMod n)) := by
  first | exact @GlobalTheory.SympQ.qq_free | exact GlobalTheory.SympQ.qq_free | (intros; apply GlobalTheory.SympQ.qq_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplectic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplectic
open Matrix

namespace GlobalTheory.SympTower

theorem rank_le_of_smul_sub_eq_zero {R : Type} [CommRing R] [Finite R] {r : ℕ} {ι : Type}
    [Fintype ι] (φ : (ι → R) →ₗ[R] (Fin r → R)) (ψ : (Fin r → R) →ₗ[R] (ι → R)) (c : R)
    (hc : c ≠ 0) (h : ∀ x, c • (x - φ (ψ x)) = 0) : r ≤ Fintype.card ι := by
  classical
  let S := {y : R // ∃ z, y = c * z}
  haveI : Fintype S := Fintype.ofFinite _
  haveI : Nontrivial S := ⟨⟨⟨c, 1, by simp⟩, ⟨0, 0, by simp⟩, fun h => hc (congrArg Subtype.val h)⟩⟩
  have key : ∀ s : Fin r → S, ∃ x : Fin r → R, (fun i => (s i).1) = c • x := by
    intro s
    choose z hz using fun i => (s i).2
    exact ⟨z, funext fun i => by simpa using hz i⟩
  let f : (Fin r → S) → (ι → S) := fun s j => ⟨ψ (fun i => (s i).1) j, by
    obtain ⟨x, hx⟩ := key s
    exact ⟨ψ x j, by rw [hx]; simp⟩⟩
  have hφ : ∀ s : Fin r → S, φ (ψ (fun i => (s i).1)) = fun i => (s i).1 := by
    intro s
    obtain ⟨x, hx⟩ := key s
    have := h x
    rw [smul_sub, sub_eq_zero] at this
    rw [hx, map_smul, map_smul, ← this]
  have hf : Function.Injective f := by
    intro s t hst
    have h1 : ψ (fun i => (s i).1) = ψ (fun i => (t i).1) :=
      funext fun j => congrArg Subtype.val (congrFun hst j)
    have h2 := hφ s
    rw [h1, hφ t] at h2
    exact funext fun i => Subtype.ext (congrFun h2 i).symm
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fun, Fintype.card_fin] at hcard
  exact (Nat.pow_le_pow_iff_right Fintype.one_lt_card).1 hcard

theorem exists_eq_one {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module (ZMod n) V]
    (f : V →ₗ[ZMod n] ZMod n) (h : ∀ c : ZMod n, (∀ y, c * f y = 0) → c = 0) : ∃ y, f y = 1 := by
  haveI : IsPrincipalIdealRing (ZMod n) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod n)) (ZMod.ringHom_surjective _)
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal (LinearMap.range f)).principal
  have hreg : d ∈ nonZeroDivisors (ZMod n) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    apply h
    intro y
    have : f y ∈ Submodule.span (ZMod n) {d} := hd ▸ LinearMap.mem_range_self f y
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    rw [← ha, smul_eq_mul, mul_left_comm, hc, mul_zero]
  have hu : IsUnit d := IsArtinianRing.isUnit_of_mem_nonZeroDivisors hreg
  have : (1 : ZMod n) ∈ LinearMap.range f := by
    rw [hd]
    obtain ⟨u, rfl⟩ := hu
    exact Submodule.mem_span_singleton.2 ⟨↑u⁻¹, by simp⟩
  exact this

theorem exists_faithful {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module (ZMod n) V]
    [Finite V] (h : ∀ c : ZMod n, (∀ y : V, c • y = 0) → c = 0) :
    ∃ x : V, ∀ c : ZMod n, c • x = 0 → c = 0 := by
  obtain ⟨x, hx⟩ := AddMonoid.exists_addOrderOf_eq_exponent (G := V) AddMonoid.ExponentExists.of_finite
  refine ⟨x, fun c hc => h c fun y => ?_⟩
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul] at hc ⊢
  obtain ⟨m, hm⟩ := addOrderOf_dvd_of_nsmul_eq_zero hc
  rw [hm, hx, mul_nsmul, AddMonoid.exponent_nsmul_eq_zero, nsmul_zero]

theorem exists_pairs {n : ℕ} [NeZero n] {g : ℕ}
    (ω : (Fin (2 * g) → ZMod n) →ₗ[ZMod n] (Fin (2 * g) → ZMod n) →ₗ[ZMod n] ZMod n)
    (halt : ∀ x, ω x x = 0) (hnd : ∀ x, (∀ y, ω x y = 0) → x = 0) (k : ℕ) (hk : k ≤ g) :
    ∃ v w : Fin k → (Fin (2 * g) → ZMod n), (∀ i j, ω (v i) (v j) = 0) ∧
      (∀ i j, ω (w i) (w j) = 0) ∧ ∀ i j, ω (v i) (w j) = if i = j then 1 else 0 := by
  classical
  have hsk : ∀ x y, ω x y = - ω y x := by
    intro x y
    have := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt] at this
    linear_combination this
  induction k with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨v, w, hv, hw, hvw⟩ := ih (by omega)
    let φ : (Fin k ⊕ Fin k → ZMod n) →ₗ[ZMod n] (Fin (2 * g) → ZMod n) :=
      Fintype.linearCombination (ZMod n) (Sum.elim v w)
    let ψ : (Fin (2 * g) → ZMod n) →ₗ[ZMod n] (Fin k ⊕ Fin k → ZMod n) :=
      LinearMap.pi (Sum.elim (fun i => ω.flip (w i)) (fun i => ω (v i)))
    have hφψ : ∀ x, φ (ψ x) = ∑ i, ω x (w i) • v i + ∑ i, ω (v i) x • w i := by
      intro x
      simp [φ, ψ, Fintype.linearCombination_apply, Fintype.sum_sum_type]
    let K : Submodule (ZMod n) (Fin (2 * g) → ZMod n) :=
      { carrier := {x | ∀ j, ω (v j) x = 0 ∧ ω x (w j) = 0}
        add_mem' := fun ha hb j => by simp [(ha j).1, (ha j).2, (hb j).1, (hb j).2]
        zero_mem' := fun j => by simp
        smul_mem' := fun c x hx j => by simp [(hx j).1, (hx j).2] }
    have hp : ∀ x, x - φ (ψ x) ∈ K := by
      intro x j
      rw [hφψ]
      constructor
      set_option synthInstance.maxHeartbeats 100000 in
        · simp [map_sum, hv, hvw]
      set_option synthInstance.maxHeartbeats 100000 in
        · simp [map_sum, LinearMap.sum_apply, hw, hvw]
    have hKp : ∀ x ∈ K, ∀ y, ω x (y - φ (ψ y)) = ω x y := by
      intro x hx y
      have h1 : ∀ j, ω x (v j) = 0 := fun j => by rw [hsk, (hx j).1, neg_zero]
      rw [hφψ]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, h1, fun j => (hx j).2]
    obtain ⟨x, hx⟩ := exists_faithful (n := n) (V := K) (by
      intro c hc
      by_contra hc0
      have := rank_le_of_smul_sub_eq_zero φ ψ c hc0
        (fun x => congrArg Subtype.val (hc ⟨_, hp x⟩))
      simp at this
      omega)
    obtain ⟨y, hy⟩ := exists_eq_one ((ω x.1).comp K.subtype) (by
      intro c hc
      apply hx
      apply Subtype.ext
      apply hnd
      intro y
      have := hc ⟨_, hp y⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, hKp x.1 x.2] at this
      simpa using this)
    have hxv : ∀ j, ω x.1 (v j) = 0 := fun j => by rw [hsk, (x.2 j).1, neg_zero]
    have hwy : ∀ j, ω (w j) y.1 = 0 := fun j => by rw [hsk, (y.2 j).2, neg_zero]
    refine ⟨Fin.cons x.1 v, Fin.cons y.1 w, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [halt, hxv, hv, (x.2 _).1]
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [halt, hwy, hw, (y.2 _).2]
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hy
      · simp [(x.2 _).2, (Fin.succ_ne_zero j).symm]
      · simp [(y.2 _).1]
      · simp [hvw]

theorem exists_level {F : Type} [Field F] {ζ : Fˣ} {n : ℕ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) {g : ℕ} {G : Type} [AddCommGroup G] (e : G → G → Fˣ)
    (Φ : G ≃+ (Fin (2 * g) → ZMod n)) (h1 : ∀ x y z, e (x + y) z = e x z * e y z)
    (h2 : ∀ x y z, e x (y + z) = e x y * e x z) (h3 : ∀ x, e x x = 1)
    (h4 : ∀ x, (∀ y, e x y = 1) → x = 0) :
    ∃ ev : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G,
      ∀ a b, e (ev a) (ev b) = ζ ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  let χ : ZMod n → Fˣ := fun a => ((Additive.toMul (hζ.zmodEquivZPowers a) : Subgroup.zpowers ζ) : Fˣ)
  have χadd : ∀ a b, χ (a + b) = χ a * χ b := by intro a b; simp [χ]
  have χinj : Function.Injective χ := by
    intro a b h
    exact hζ.zmodEquivZPowers.injective (Additive.toMul.injective (Subtype.ext h))
  have χint : ∀ i : ℤ, χ i = ζ ^ i := by
    intro i; simp only [χ, hζ.zmodEquivZPowers_apply_coe_int]; rfl
  have χ0 : χ 0 = 1 := by simpa using χint 0
  have hpow : ∀ x y, e x y ^ n = 1 := by
    intro x y
    let f : G →+ Additive Fˣ := AddMonoidHom.mk' (fun x => Additive.ofMul (e x y))
      (fun a b => by rw [h1]; rfl)
    have hx : n • x = 0 := Φ.injective (by
      rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul])
    have := map_nsmul f n x
    rw [hx, map_zero] at this
    exact (congrArg Additive.toMul this).symm
  have hex : ∀ x y, ∃ a, χ a = e (Φ.symm x) (Φ.symm y) := by
    intro x y
    have hm : e (Φ.symm x) (Φ.symm y) ∈ Subgroup.zpowers ζ := by
      rw [hζ.zpowers_eq, mem_rootsOfUnity]; exact hpow _ _
    obtain ⟨i, hi⟩ := hm
    exact ⟨i, by rw [χint]; exact hi⟩
  choose b hb using hex
  have b1 : ∀ x y z, b (x + y) z = b x z + b y z := fun x y z =>
    χinj (by rw [χadd, hb, hb, hb, map_add (f := _), h1])
  have b2 : ∀ x y z, b x (y + z) = b x y + b x z := fun x y z =>
    χinj (by rw [χadd, hb, hb, hb, map_add (f := _), h2])
  let ω : (Fin (2 * g) → ZMod n) →ₗ[ZMod n] (Fin (2 * g) → ZMod n) →ₗ[ZMod n] ZMod n :=
    LinearMap.mk₂ (ZMod n) b b1
      (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (fun x => b x y) (fun x z => b1 x z y)) c x)
      b2
      (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (fun y => b x y) (fun y z => b2 x y z)) c y)
  have hω : ∀ x y, χ (ω x y) = e (Φ.symm x) (Φ.symm y) := hb
  have halt : ∀ x, ω x x = 0 := fun x => χinj (by rw [hω, h3, χ0])
  have hsk : ∀ x y, ω x y = - ω y x := by
    intro x y
    have := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt] at this
    linear_combination this
  obtain ⟨v, w, hv, hw, hvw⟩ := exists_pairs ω halt (by
    intro x hx
    have := h4 (Φ.symm x) (fun y => by
      have := hω x (Φ y)
      rw [hx, χ0, Φ.symm_apply_apply] at this
      exact this.symm)
    exact Φ.symm.injective (by rw [this, map_zero])) g le_rfl
  have hwv : ∀ i j, ω (w i) (v j) = if j = i then -1 else 0 := by
    intro i j; rw [hsk, hvw]; split_ifs <;> simp
  let E : ((Fin g → ℤ) × (Fin g → ℤ)) →+ (Fin (2 * g) → ZMod n) :=
    AddMonoidHom.mk' (fun a => ∑ i, (a.1 i : ZMod n) • v i + ∑ i, (a.2 i : ZMod n) • w i)
      (fun a b => by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Int.cast_add, add_smul,
          Finset.sum_add_distrib]
        abel)
  refine ⟨Φ.symm.toAddMonoidHom.comp E, fun a c => ?_⟩
  change e (Φ.symm (E a)) (Φ.symm (E c)) = _
  rw [← hω, ← χint]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [E, map_sum, LinearMap.sum_apply, hv, hw, hvw, hwv, dotProduct, mul_comm]
  ring

theorem ker_and_surj {F : Type} [Field F] {ζ : Fˣ} {n : ℕ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) {g : ℕ} {G : Type} [AddCommGroup G] (e : G → G → Fˣ)
    (Φ : G ≃+ (Fin (2 * g) → ZMod n)) (h1 : ∀ x y z, e (x + y) z = e x z * e y z)
    (ev : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G)
    (hev : ∀ a b, e (ev a) (ev b) = ζ ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1)) :
    (∀ a b, ev a = ev b ↔ ∃ e', a = b + n • e') ∧ Function.Surjective ev := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  have hnx : ∀ x : G, n • x = 0 := fun x => Φ.injective (by
      rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul])
  have h0 : ∀ y, e 0 y = 1 := by
    intro y
    have := h1 0 0 y
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hker : ∀ a, ev a = 0 → (∀ i, (n : ℤ) ∣ a.1 i) ∧ ∀ i, (n : ℤ) ∣ a.2 i := by
    intro a ha
    constructor
    · intro i
      have := hev a (0, Pi.single i 1)
      rw [ha, h0, eq_comm, hζ.zpow_eq_one_iff_dvd] at this
      simpa using this
    · intro i
      have := hev a (Pi.single i 1, 0)
      rw [ha, h0, eq_comm, hζ.zpow_eq_one_iff_dvd] at this
      simpa using this
  refine ⟨fun a b => ⟨fun h => ?_, ?_⟩, ?_⟩
  · obtain ⟨ha, hb⟩ := hker (a - b) (by rw [map_sub, h, sub_self])
    choose c hc using ha
    choose d hd using hb
    refine ⟨(c, d), ?_⟩
    ext i
    · have := hc i
      simp at this ⊢
      linarith
    · have := hd i
      simp at this ⊢
      linarith
  · rintro ⟨c, rfl⟩
    rw [map_add (f := _), map_nsmul, hnx, add_zero]
  · let f : (Fin g → ZMod n) × (Fin g → ZMod n) → G :=
      fun a => ev (fun i => ((a.1 i).val : ℤ), fun i => ((a.2 i).val : ℤ))
    have hf : Function.Injective f := by
      intro a b h
      obtain ⟨ha, hb⟩ := hker (_ - _) (by rw [map_sub]; exact sub_eq_zero.2 h)
      ext i
      · have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).2 (ha i)
        simpa [sub_eq_zero] using this
      · have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).2 (hb i)
        simpa [sub_eq_zero] using this
    haveI : Fintype G := Fintype.ofEquiv _ Φ.symm.toEquiv
    have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by
      rw [Fintype.card_congr Φ.toEquiv]
      simp [two_mul, pow_add]⟩
    intro x
    obtain ⟨a, ha⟩ := hb.2 x
    exact ⟨_, ha⟩

theorem exists_compatible_symplectic : ∀ (F : Type) [Field F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ (g : ℕ) (G : ℕ → Type) [∀ n, AddCommGroup (G n)] (e : ∀ n, G n → G n → Fˣ) (π : ∀ M n, G M →+ G n), (∀ n, 0 < n → Nonempty (G n ≃+ (Fin (2 * g) → ZMod n))) → (∀ n x y z, e n (x + y) z = e n x z * e n y z) → (∀ n x y z, e n x (y + z) = e n x y * e n x z) → (∀ n x, e n x x = 1) → (∀ n, 0 < n → ∀ x, (∀ y, e n x y = 1) → x = 0) → (∀ n m, 0 < n → 0 < m → ∀ x y, e n (π (n * m) n x) (π (n * m) n y) = e (n * m) x y ^ m) → (∀ M n k, 0 < k → 0 < M → k ∣ n → n ∣ M → ∀ x, π n k (π M n x) = π M k x) → ∃ ev : ∀ n, ((Fin g → ℤ) × (Fin g → ℤ)) →+ G n, (∀ n, 0 < n → ∀ a b, ev n a = ev n b ↔ ∃ e', a = b + n • e') ∧ (∀ n, 0 < n → Function.Surjective (ev n)) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, π (n * m) n (ev (n * m) a) = ev n a) ∧ (∀ n, 0 < n → ∀ a b, e n (ev n a) (ev n b) = ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1)) := by
  intro F _ ζ hζ hζc g G _ e π hG h1 h2 h3 h4 hπ hcomp
  classical
  have hlev : ∀ M : ℕ, ∃ E : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G M.factorial,
      ∀ a b, e _ (E a) (E b) = ζ M.factorial ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) := fun M =>
    exists_level M.factorial_pos (hζ _ M.factorial_pos) (e _) (hG _ M.factorial_pos).some
      (h1 _) (h2 _) (h3 _) (h4 _ M.factorial_pos)
  choose E hE using hlev
  have hpush : ∀ n M, 0 < M → n ∣ M → ∀ (x y : G M) (i : ℤ), e M x y = ζ M ^ i →
      e n (π M n x) (π M n y) = ζ n ^ i := by
    rintro n _ hM ⟨m, rfl⟩ x y i h
    have hn : 0 < n := Nat.pos_of_mul_pos_right hM
    have hm : 0 < m := Nat.pos_of_mul_pos_left hM
    rw [hπ n m hn hm, h, ← hζc n m hn hm, ← _root_.zpow_natCast, ← _root_.zpow_natCast,
      ← _root_.zpow_mul, ← _root_.zpow_mul,
      mul_comm i]
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU : ∀ n, 0 < n → ∀ᶠ k in (U : Filter ℕ), n ∣ k.factorial := by
    intro n hn
    apply Filter.Eventually.filter_mono Filter.hyperfilter_le_cofinite
    rw [Nat.cofinite_eq_atTop]
    exact (Filter.eventually_ge_atTop n).mono fun k hk => Nat.dvd_factorial hn hk
  have hlim : ∀ n, ∃ f : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G n, 0 < n →
      ∀ a, ∀ᶠ k in (U : Filter ℕ), π k.factorial n (E k a) = f a := by
    intro n
    by_cases hn : 0 < n
    · haveI : NeZero n := ⟨hn.ne'⟩
      haveI : Finite (G n) := Finite.of_equiv _ (hG n hn).some.symm.toEquiv
      have : ∀ a, ∃ x, ∀ᶠ k in (U : Filter ℕ), π k.factorial n (E k a) = x := by
        intro a
        obtain ⟨x, hx⟩ := (U.map fun k => π k.factorial n (E k a)).eq_pure_of_finite
        refine ⟨x, ?_⟩
        have : {x} ∈ (U.map fun k => π k.factorial n (E k a)) := by rw [hx]; simp
        exact this
      choose f hf using this
      refine ⟨AddMonoidHom.mk' f fun a b => ?_, fun _ => hf⟩
      obtain ⟨k, hk1, hk2, hk3⟩ := ((hf a).and ((hf b).and (hf (a + b)))).exists
      rw [← hk1, ← hk2, ← hk3, map_add (f := _), map_add (f := _)]
    · exact ⟨0, fun h => absurd h hn⟩
  choose ev hev using hlim
  have hpair : ∀ n, 0 < n → ∀ a b, e n (ev n a) (ev n b) = ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) := by
    intro n hn a b
    obtain ⟨k, hk1, hk2, hk3⟩ := ((hev n hn a).and ((hev n hn b).and (hU n hn))).exists
    rw [← hk1, ← hk2]
    exact hpush n _ k.factorial_pos hk3 _ _ _ (hE k a b)
  have hks := fun n (hn : 0 < n) =>
    ker_and_surj hn (hζ n hn) (e n) (hG n hn).some (h1 n) (ev n) (hpair n hn)
  refine ⟨ev, fun n hn => (hks n hn).1, fun n hn => (hks n hn).2, ?_, hpair⟩
  intro n m hn hm a
  have hnm := Nat.mul_pos hn hm
  obtain ⟨k, hk1, hk2, hk3⟩ := ((hev n hn a).and ((hev _ hnm a).and (hU _ hnm))).exists
  rw [← hk1, ← hk2]
  exact hcomp _ _ _ hn k.factorial_pos (Dvd.intro _ rfl) hk3 _

end GlobalTheory.SympTower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplecticStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_symplectic_alt : ∀ (F : Type) [Field F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ (g : ℕ) (G : ℕ → Type) [∀ n, AddCommGroup (G n)] (e : ∀ n, G n → G n → Fˣ) (π : ∀ M n, G M →+ G n), (∀ n, 0 < n → Nonempty (G n ≃+ (Fin (2 * g) → ZMod n))) → (∀ n x y z, e n (x + y) z = e n x z * e n y z) → (∀ n x y z, e n x (y + z) = e n x y * e n x z) → (∀ n x, e n x x = 1) → (∀ n, 0 < n → ∀ x, (∀ y, e n x y = 1) → x = 0) → (∀ n m, 0 < n → 0 < m → ∀ x y, e n (π (n * m) n x) (π (n * m) n y) = e (n * m) x y ^ m) → (∀ M n k, 0 < k → 0 < M → k ∣ n → n ∣ M → ∀ x, π n k (π M n x) = π M k x) → ∃ ev : ∀ n, ((Fin g → ℤ) × (Fin g → ℤ)) →+ G n, (∀ n, 0 < n → ∀ a b, ev n a = ev n b ↔ ∃ e', a = b + n • e') ∧ (∀ n, 0 < n → Function.Surjective (ev n)) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, π (n * m) n (ev (n * m) a) = ev n a) ∧ (∀ n, 0 < n → ∀ a b, e n (ev n a) (ev n b) = ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1)) := by
  first | exact @GlobalTheory.SympTower.exists_compatible_symplectic | exact GlobalTheory.SympTower.exists_compatible_symplectic | (intros; apply GlobalTheory.SympTower.exists_compatible_symplectic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplecticBasesLevelPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.SympQ.compatible_symplectic_bases : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ g : ℕ, g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → ∃ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) ∧ (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) ∧ (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) ∧ ∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F) := by
  intro R _ _ _ hR D F _ _ _ ζ hζ hζc g hg
  subst hg
  have hL : Laws := GlobalTheory.allSixLaws.1
  have gt : GlobalTheory.Ex.BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  have wp : GlobalTheory.Ex.BrWpSt := GlobalTheory.WeilValues.weil_eq_values gt (GlobalTheory.Ex.brFam hL GlobalTheory.allSixLaws.2.1)
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, ν, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL R D.toPre D.psi_even D.tau_bimult F ⊤ (fun _ => trivial)
  obtain ⟨-, -, gAdd, -, gQ⟩ := gt R D.toPre D.psi_even D.tau_bimult F N ν
  have hW := wp R D.toPre D.psi_even D.tau_bimult F N ν
  have hcl : ∀ n (p p' : QkPt D.toPre F n) v v', ν.QPt p v → ν.QPt p' v' →
      (QkPt.Equiv D.toPre F p p' ↔ (QuotientGroup.mk v : GlobalTheory.SympQ.Qq N n) = QuotientGroup.mk v') :=
    fun n p p' v v' h h' => ((gQ n).2.2 p p' v v' h h').trans (GlobalTheory.SympQ.qEq_iff_mk_eq N v v')
  have h1 : ∀ n (x y z : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n (x + y).toMul z.toMul = GlobalTheory.SympQ.wpQ N n x.toMul z.toMul * GlobalTheory.SympQ.wpQ N n y.toMul z.toMul := by
    intro n x y z
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    obtain ⟨p'', hp''⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
    simp only [toMul_add]
    rw [← hp, ← hp', ← hp'', ← QuotientGroup.mk_mul, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk,
      GlobalTheory.Ex.WpPairing.wp_mul_left]
  have h2 : ∀ n (x y z : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n x.toMul (y + z).toMul = GlobalTheory.SympQ.wpQ N n x.toMul y.toMul * GlobalTheory.SympQ.wpQ N n x.toMul z.toMul := by
    intro n x y z
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    obtain ⟨p'', hp''⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
    simp only [toMul_add]
    rw [← hp, ← hp', ← hp'', ← QuotientGroup.mk_mul, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk,
      GlobalTheory.Ex.WpPairing.wp_mul_right]
  have h3 : ∀ n (x : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n x.toMul x.toMul = 1 := by
    intro n x
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    rw [← hp, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.Ex.NumD.wp_self]
  have h4 : ∀ n, 0 < n → ∀ x : Additive (GlobalTheory.SympQ.Qq N n), (∀ y : Additive (GlobalTheory.SympQ.Qq N n), GlobalTheory.SympQ.wpQ N n x.toMul y.toMul = 1) → x = 0 := by
    intro n hn x hx
    exact Additive.toMul.injective (GlobalTheory.T.reprModTrivialQuotient_pairing_nondegenerate R hR D F N ν n hn x.toMul fun y => hx (Additive.ofMul y))
  have h5 : ∀ n m, 0 < n → 0 < m → ∀ x y : Additive (GlobalTheory.SympQ.Qq N (n * m)), GlobalTheory.SympQ.wpQ N n ((GlobalTheory.SympQ.pushQ N (n * m) n).toAdditive x).toMul ((GlobalTheory.SympQ.pushQ N (n * m) n).toAdditive y).toMul = GlobalTheory.SympQ.wpQ N (n * m) x.toMul y.toMul ^ m := by
    intro n m hn hm x y
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    change GlobalTheory.SympQ.wpQ N n (GlobalTheory.SympQ.pushQ N (n * m) n x.toMul) (GlobalTheory.SympQ.pushQ N (n * m) n y.toMul) =
      GlobalTheory.SympQ.wpQ N (n * m) x.toMul y.toMul ^ m
    rw [← hp, ← hp', GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk]
    exact GlobalTheory.T.reprModTrivialQuotient_pairing_levelPush_eq_pow R hR D F N ν n m hn hm p p'
  have h6 : ∀ M n k, 0 < k → 0 < M → k ∣ n → n ∣ M → ∀ x : Additive (GlobalTheory.SympQ.Qq N M), (GlobalTheory.SympQ.pushQ N n k).toAdditive ((GlobalTheory.SympQ.pushQ N M n).toAdditive x) = (GlobalTheory.SympQ.pushQ N M k).toAdditive x := by
    intro M n k hk hM hkn hnM x
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    apply Additive.toMul.injective
    change GlobalTheory.SympQ.pushQ N n k (GlobalTheory.SympQ.pushQ N M n x.toMul) = GlobalTheory.SympQ.pushQ N M k x.toMul
    rw [← hp, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk]
    congr 1
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rw [GlobalTheory.SympQ.pushRep_fst N hkn, GlobalTheory.SympQ.pushRep_fst N hnM, GlobalTheory.SympQ.pushRep_fst N (hkn.trans hnM)]
    · have e : M / n * (n / k) = M / k := by
        obtain ⟨b, rfl⟩ := hkn
        obtain ⟨a, rfl⟩ := hnM
        have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
        rw [Nat.mul_div_cancel_left _ (Nat.mul_pos hk hb), Nat.mul_div_cancel_left _ hk, Nat.mul_assoc,
          Nat.mul_div_cancel_left _ hk, Nat.mul_comm]
      rw [GlobalTheory.SympQ.pushRep_snd N hkn, GlobalTheory.SympQ.pushRep_snd N hnM, GlobalTheory.SympQ.pushRep_snd N (hkn.trans hnM), ← pow_mul, e]
  obtain ⟨ev', hker, hsurj, htow, hweil⟩ := GlobalTheory.T.exists_compatible_symplectic_alt F ζ hζ hζc (D.toPre.P.g + Module.finrank ℤ D.toPre.X)
    (fun n => Additive (GlobalTheory.SympQ.Qq N n)) (fun n x y => GlobalTheory.SympQ.wpQ N n x.toMul y.toMul)
    (fun M n => (GlobalTheory.SympQ.pushQ N M n).toAdditive) (GlobalTheory.T.reprModTrivialQuotient_free_rank_twice_dimension R hR D F N ν) h1 h2 h3 h4 h5 h6
  have hrep : ∀ n a, ∃ q : N.QT n, (QuotientGroup.mk q : GlobalTheory.SympQ.Qq N n) = (ev' n a).toMul :=
    fun n a => QuotientGroup.mk_surjective _
  choose q hq using hrep
  choose P hP using fun n a => (gQ n).2.1 (q n a)
  refine ⟨P, fun n hn a b => ?_, fun n hn a b => ?_, fun n hn p => ?_, fun n m hn hm a => ?_, fun n hn a b => ?_⟩
  · obtain ⟨r, hr⟩ := (gQ n).2.1 (q n a * q n b)
    refine ⟨r, ?_, (gAdd _ _ _ _ _ _ (hP n a).2 (hP n b).2 hr.2).2 rfl, ?_⟩
    · rw [← hr.1, ← (hP n a).1, ← (hP n b).1, ← map_add (f := _)]
      rfl
    · rw [hcl n _ _ _ _ hr (hP n (a + b)), QuotientGroup.mk_mul, hq, hq, hq, map_add (f := _), toMul_add]
  · rw [hcl n _ _ _ _ (hP n a) (hP n b), hq, hq, Additive.toMul.injective.eq_iff]
    exact hker n hn a b
  · obtain ⟨v, hv⟩ := ((gQ n).1 p).exists
    obtain ⟨a, ha⟩ := hsurj n hn (Additive.ofMul (QuotientGroup.mk v))
    exact ⟨a, (hcl n _ _ _ _ (hP n a) hv).2 (by rw [hq, ha]; rfl)⟩
  · have hd : n ∣ n * m := dvd_mul_right n m
    obtain ⟨r, hr⟩ := (gQ n).2.1 (GlobalTheory.SympQ.pushRep N (n * m) n (q (n * m) a))
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [← hr.1, ← (hP (n * m) a).1, GlobalTheory.SympQ.pushRep_fst N hd]
    · refine (GlobalTheory.Ex.GtValues.isNsmul_val ν m (hP (n * m) a).2 hr.2).2 ?_
      rw [GlobalTheory.SympQ.pushRep_snd N hd, Nat.mul_div_cancel_left m hn]
    · rw [hcl n _ _ _ _ hr (hP n a), ← GlobalTheory.SympQ.pushQ_mk, hq, hq, ← htow n m hn hm a]
      rfl
  · refine (hW n hn (P n a) (P n b) (q n a) (q n b) _ (hP n a) (hP n b)).2 ?_
    rw [← GlobalTheory.SympQ.wpQ_mk, hq, hq]
    exact congrArg Units.val (hweil n hn a b).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplecticBasesLevelPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_symplectic_bases_levelPoints : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ g : ℕ, g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → ∃ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) ∧ (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) ∧ (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) ∧ ∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F) := by
  first | exact @GlobalTheory.SympQ.compatible_symplectic_bases | exact GlobalTheory.SympQ.compatible_symplectic_bases | (intros; apply GlobalTheory.SympQ.compatible_symplectic_bases <;> assumption)
end
