module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtIdMulSupNatCastConj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWtEqMulNuStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotalLeGeneric
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GenMass

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem pair_mem_cls (S : Frames L r k) (g g' : Fin (r + 1) → S.V) : (g, g') ∈ S.frameCls g g' := by
  have h1 : IsIntM L (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨1, 1, h1, h1, fun i j h => ?_, fun i => by simp, fun i j => ⟨0, zero_mem _, by simp⟩,
    fun j => ?_, fun j => ?_⟩
  · simp [Matrix.one_apply_ne h.ne']
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem sumCls_le (S : Frames L r k) (φ : Set S.FrP → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ C, S.IsCls C → φ C ≤ c) :
    S.sumCls φ ≤ (S.sumCls fun _ => 1) * c := by
  unfold Frames.sumCls
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun o => ?_
  split_ifs with ho
  · rw [mul_one]
    gcongr
    exact h _ ho.1
  · simp

theorem q_pow_le (S : Frames L r k) (e : ℤ) (he0 : 0 ≤ e) (he : e ≤ S.vth + S.a + S.vD) (m : ℕ) :
    (S.q : ℝ≥0∞) ^ (m * e.toNat) ≤ ENNReal.ofReal (S.Hp ^ m) := by
  have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
  have hq1 : (1 : ℝ) ≤ S.q := by exact_mod_cast (by omega : 1 ≤ S.q)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_comm, pow_mul]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [← zpow_natCast, Int.toNat_of_nonneg he0]
  exact zpow_le_zpow_right₀ hq1 he

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem vth_nonneg (S : Frames L r k) : 0 ≤ S.vth := by
  unfold Frames.vth
  split_ifs <;> norm_num

theorem total_weight_le (S : Frames L r k) (ha : 0 ≤ S.a) (hD : 0 ≤ S.vD) :
    (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (r * (r + 1))) := by
  have hv := vth_nonneg S
  exact ((GlobalTheory.HL.ClassCount.sumCls_le_encard L r k S).trans (GlobalTheory.IntClsCount.main L r k S hD)).trans
    (q_pow_le S _ (by omega) (by omega) _)

theorem sumCls_eq_single (S : Frames L r k) (h1 : (S.sumCls fun _ => 1) ≤ 1) (φ : Set S.FrP → ℝ≥0∞)
    (hφ : ∀ h ∈ S.St, ∀ C, φ (h • C) = φ C) (C : Set S.FrP) (hC : S.IsIntCls C) :
    S.sumCls φ = ENNReal.ofReal (S.wC C) * φ C := by
  let o' : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ C
  obtain ⟨h, hh⟩ : o'.out ∈ MulAction.orbit S.St C :=
    MulAction.orbitRel_apply.1 (Quotient.mk_out (s := MulAction.orbitRel S.St (Set S.FrP)) _)
  have hh' : h.1 • C = o'.out := hh
  have ho' : S.IsIntCls o'.out := hh' ▸ GlobalTheory.HL.ClassCount.isIntCls_smul S h.2 hC
  unfold Frames.sumCls at h1 ⊢
  rw [tsum_eq_single o', if_pos ho', ← hh', hφ _ h.2, ((GlobalTheory.HL.volSt L r k S).2 C hC.1).2.2.2 _ h.2]
  intro o hne
  refine if_neg fun ho => ?_
  have h2 := (ENNReal.sum_le_tsum {o, o'}).trans h1
  rw [Finset.sum_pair hne, if_pos ho, if_pos ho', mul_one, mul_one] at h2
  have h3 := ENNReal.one_le_ofReal.2 ((GlobalTheory.HL.volSt L r k S).2 _ ho.1).2.2.1
  have h4 := ENNReal.one_le_ofReal.2 ((GlobalTheory.HL.volSt L r k S).2 _ ho'.1).2.2.1
  have h5 := (add_le_add h3 h4).trans h2
  norm_num at h5

end GlobalTheory.HL.GenMass


open GlobalTheory.HL.GenMass in
theorem GlobalTheory.HL.GenMass.total_le_generic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ d₁ Λ₁, S.IsTerm d₁ Λ₁ → ∀ g : ℝ≥0∞, g = ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * (S.sumData fun d => S.nT d (S.Fr d₁ Λ₁) fun Λ => S.BBzero d Λ) → 0 < g ∧ g < ⊤ ∧ S.nn ≤ ENNReal.ofReal (8 * S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g ∧ (S.Hp = 1 → S.nn = g) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk d₁ Λ₁ hT g hg
  obtain ⟨hSD, -, hMs, -, -, -, hI, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d₁ Λ₁ hT
  obtain ⟨ha, hD, -, -, hH, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₁ Λ₁ hT
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.selfDualHermitianLattice_mass_of_trace L r k S (by omega) ⟨Λ₁, hSD⟩
  have hv := vth_nonneg S
  have hp : (S.fr d₁ Λ₁, S.fr' d₁ Λ₁) ∈ S.Fr d₁ Λ₁ := pair_mem_cls S _ _
  have hsw := GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses L r k S (fun _ _ => True) (fun _ _ _ _ _ _ => trivial)
  have hnn : S.nn = S.sumCls fun C => S.sumData fun d => S.nT d C fun _ => True := hsw.1
  have hM := hU _ hI.1 _ hp (S.M d₁ Λ₁) le_rfl (fun x hx => (hMs hx).2)
    (fun x hx y hy => (hSD.2 y).2 (hMs hy).1 x (hMs hx).1)
  have hM' : ENNReal.ofReal (κ / 2) ≤ S.massSig (S.M d₁ Λ₁) ∧
      S.massSig (S.M d₁ Λ₁) ≤ ENNReal.ofReal (2 * κ) := by
    simpa [Frames.M] using hM
  have hg' : g = ENNReal.ofReal (S.wC (S.Fr d₁ Λ₁)) * S.massSig (S.M d₁ Λ₁) := by
    rw [hg, (GlobalTheory.T.hermitianFrameClass_terms_le_overlattice_masses L r k S _ hI.1 _ hp).2]
    rfl
  have hw := ENNReal.one_le_ofReal.2 ((GlobalTheory.HL.volSt L r k S).2 _ hI.1).2.2.1
  have hlow : ENNReal.ofReal (κ / 2) ≤ g := by
    rw [hg', ← one_mul (ENNReal.ofReal (κ / 2))]
    exact mul_le_mul' hw hM'.1
  refine ⟨(ENNReal.ofReal_pos.2 (by positivity)).trans_le hlow, ?_, ?_, fun h1 => ?_⟩
  · rw [hg']
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hM'.2.trans_lt ENNReal.ofReal_lt_top)
  · have hφ : ∀ C, S.IsCls C → (S.sumData fun d => S.nT d C fun _ => True) ≤
        ENNReal.ofReal (S.Hp ^ (2 * (2 * r + 2))) * ENNReal.ofReal (2 * κ) := by
      intro C hC
      obtain ⟨p, hpC⟩ : ∃ p, p ∈ C := by
        obtain ⟨n, -, n', -, rfl⟩ := hC
        exact ⟨_, pair_mem_cls S _ _⟩
      refine ((GlobalTheory.T.hermitianFrameClass_terms_le_overlattice_masses L r k S C hC p hpC).1 fun _ => True).trans ?_
      refine (ENNReal.tsum_le_tsum (g := fun _ => ENNReal.ofReal (2 * κ)) fun Mh => ?_).trans ?_
      · refine (hU C hC p hpC Mh.1 Mh.2.1 Mh.2.2.1 Mh.2.2.2.1).2.trans (ENNReal.ofReal_le_ofReal ?_)
        refine mul_le_of_le_one_right (by positivity) ?_
        rw [← Nat.cast_pow]
        exact Nat.cast_inv_le_one _
      · have hc := GlobalTheory.FrameOver.encard_overlattices_le L r k S C hC p hpC ha
        have he : 2 * S.a.toNat * (2 * r + 2) = 2 * (2 * r + 2) * S.a.toNat := by ring
        rw [he] at hc
        have hc' := hc.trans (q_pow_le S _ ha (by omega) _)
        rw [ENNReal.tsum_const]
        refine mul_le_mul_left (le_trans (le_of_eq ?_) hc') _
        simp only [and_true]
        rfl
    rw [hnn]
    refine (sumCls_le S _ _ hφ).trans ?_
    refine (mul_le_mul_left (total_weight_le S ha hD) _).trans ?_
    refine le_trans ?_ (mul_le_mul_right hlow _)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : S.Hp ^ (r * (r + 1)) * S.Hp ^ (2 * (2 * r + 2)) ≤
        S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hH (by nlinarith)
    have h3 : 0 ≤ S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h2 hκ.le, mul_nonneg h3 hκ.le]
  · have hq : 2 ≤ S.q := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.2.2.2.1
    have hB : ∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ := fun d Λ h => by
      by_contra hc
      have h2 := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ h).2.2.2.2.2.2.2.1 hc
      rw [h1] at h2
      have : S.q ≤ 1 := by exact_mod_cast h2
      omega
    have htw := total_weight_le S ha hD
    rw [h1, one_pow, ENNReal.ofReal_one] at htw
    rw [hnn, sumCls_eq_single S htw _ (fun h hh C => by simp only [hsw.2 h hh]) _ hI, hg]
    congr 2
    funext d
    unfold Frames.nT
    congr 2
    ext Λ
    exact ⟨fun h => ⟨h.1, hB _ _ h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2.2⟩⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTotalMassLeGenericMass
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.AbsGenMass

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k}

theorem fr_eq (hM : M.OK) (c : Coord P S) (d : LocNG.Datum P) (t : Term V M r)
    (ht : LocNG.IsTermOver P d t) :
    S.Fr (c.dat d) (c.lat t.abelian₂) = S.frameCls (fun b => c.e (t.f b)) (fun b => c.e (t.f' b)) := by
  have := hM.loc
  have := hM.char0
  have ht0 := ht
  obtain ⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, -⟩ := ht
  have heq : (⟨t.abelian₂, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ : Term V M r) = t := by
    cases t with
    | mk Λ f f' T T' =>
      simp only at hT hT' hf hf'
      subst hf hf' hT hT'
      rfl
  have hW := (GlobalTheory.T.term_over_frame_coordinates M hM H r k P S c d n n' t.abelian₂).mp ⟨by rw [heq]; exact ht0, hn, hn', hΛ, hΛ'⟩
  rw [(GlobalTheory.HL.WitIndep.witness_independence M.L r k S _ _ _ _ hW).2.2.1]
  congr 1 <;> funext b
  · rw [c.f_eq b, GlobalTheory.HL.CoordUnip.grp_apply c, hf]
  · rw [c.f'_eq b, GlobalTheory.HL.CoordUnip.grp_apply c, hf']

theorem sum_eq_mass (hM : M.OK) (c : Coord P S) (R : LocNG.Reps P) (d : LocNG.Datum P)
    (C : Term V M r → Prop) (Q : Submodule M.L.O S.V → Prop)
    (hQ : ∀ s ∈ S.St, ∀ Λ, S.IsTerm (c.dat d) Λ → Q Λ → Q (s • Λ))
    (hC : ∀ t, LocNG.IsTermOver P d t → (C t ↔ Q (c.lat t.abelian₂))) :
    ∑' t : {t // t ∈ R.RT d ∧ C t}, ENNReal.ofReal (LocNG.mu P t.1) = S.mass (c.dat d) Q := by
  have := hM.loc
  have := hM.char0
  have T17 := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  have T22 := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  have TR := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hSt : ∀ g, g ∈ P.St ↔ c.grp g ∈ S.St := TR.2.2.2.1
  have hlat : ∀ g Λ, c.lat (LocNG.img g Λ) = c.grp g • c.lat Λ := T17.2.2.2.1
  have hinjlat : Function.Injective c.lat := T17.2.2.1.injective
  have hmu : ∀ t : Term V M r, LocNG.mu P t = S.mu (c.lat t.abelian₂) := T17.2.2.2.2.2
  have hT : ∀ g : S.St, ∀ Λ, (S.IsTerm (c.dat d) Λ ∧ Q Λ) → (S.IsTerm (c.dat d) (g • Λ) ∧ Q (g • Λ)) := by
    rintro ⟨g, hg⟩ Λ ⟨h1, h2⟩
    exact ⟨(GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ _ h1 g hg).1, hQ g hg Λ h1 h2⟩
  have hι : ∀ a : {t // t ∈ R.RT d ∧ C t}, S.IsTerm (c.dat d) (c.lat a.1.abelian₂) ∧ Q (c.lat a.1.abelian₂) := by
    rintro ⟨t, htR, hCt⟩
    have hto : LocNG.IsTermOver P d t := (R.hRT d).1 htR
    exact ⟨(T22.1 d t hto).1, (hC t hto).1 hCt⟩
  have hsurj : ∀ Λ, (S.IsTerm (c.dat d) Λ ∧ Q Λ) →
      ∃ a : {t // t ∈ R.RT d ∧ C t}, ∃ g : S.St, g • c.lat a.1.abelian₂ = Λ := by
    rintro Λ ⟨hΛ, hQΛ⟩
    obtain ⟨t, hto, rfl⟩ := T22.2.1 d Λ hΛ
    obtain ⟨y, hyR, s, hs, hts⟩ := (R.hRT d).2.1 t hto
    have hyo : LocNG.IsTermOver P d y := (R.hRT d).1 hyR
    have hsS : c.grp s ∈ S.St := (hSt s).mp hs
    have hΛeq : c.lat t.abelian₂ = c.grp s • c.lat y.abelian₂ := by rw [hts, hlat]
    have hQy : Q (c.lat y.abelian₂) := by
      have := hQ (c.grp s)⁻¹ (inv_mem hsS) _ hΛ hQΛ
      rwa [hΛeq, inv_smul_smul] at this
    exact ⟨⟨y, hyR, (hC y hyo).2 hQy⟩, ⟨c.grp s, hsS⟩, hΛeq.symm⟩
  have hinj : ∀ a b : {t // t ∈ R.RT d ∧ C t},
      (∃ g : S.St, g • c.lat a.1.abelian₂ = c.lat b.1.abelian₂) → a = b := by
    intro a b hex
    obtain ⟨g, hab⟩ := hex
    have hs : c.grp.symm g ∈ P.St := (hSt _).mpr (by simp only [MulEquiv.apply_symm_apply]; exact g.2)
    have hba : b.1.abelian₂ = LocNG.img (c.grp.symm g) a.1.abelian₂ := by
      apply hinjlat
      rw [hlat, MulEquiv.apply_symm_apply]
      exact Eq.symm hab
    exact Subtype.ext ((R.hRT d).2.2 a.1 a.2.1 b.1 b.2.1 ⟨_, hs, hba⟩)
  have hφ : ∀ g : S.St, ∀ Λ, (S.IsTerm (c.dat d) Λ ∧ Q Λ) →
      ENNReal.ofReal (S.mu (g • Λ)) = ENNReal.ofReal (S.mu Λ) := by
    rintro ⟨g, hg⟩ Λ ⟨hΛ, -⟩
    have hlatΛ : IsLat M.L Λ := (GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hΛ).1.1
    exact congrArg ENNReal.ofReal (((GlobalTheory.HL.volSt M.L r k S).1 Λ hlatΛ).2.2 g hg)
  have key := (GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient (G := S.St)
    (fun a : {t // t ∈ R.RT d ∧ C t} => c.lat a.1.abelian₂)
    (fun Λ => S.IsTerm (c.dat d) Λ ∧ Q Λ) hT hι hsurj hinj).2 (fun Λ => ENNReal.ofReal (S.mu Λ)) hφ
  simp only [hmu]
  unfold GlobalTheory.HL.Frames.mass
  convert key

theorem exists_wt_one (hM : M.OK) (c : Coord P S) (R : LocNG.Reps P) (d0 : LocNG.Datum P)
    (t : Term V M r) (ht : LocNG.IsTermOver P d0 t) :
    ∃ d ∈ R.RD, (∃ Λ, S.IsTerm (c.dat d) Λ) ∧ LocNG.Datum.wt d0 d = 1 := by
  have := hM.loc
  have := hM.char0
  obtain ⟨d, hdR, g, hg, hmv⟩ := R.hRD.2.1 d0 (Set.mem_univ _)
  have T20 := GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c
  have T17 := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  have T22 := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  have hdat : c.grp g • c.dat d = c.dat d0 := (T20.2.1 g hg d d0).mp hmv
  have hgH : c.grp g ∈ S.H0 := (T17.1 g).mp hg
  have hterm0 : S.IsTerm (c.dat d0) (c.lat t.abelian₂) := (T22.1 d0 t ht).1
  have hterm : S.IsTerm (c.dat d) ((c.grp g)⁻¹ • c.lat t.abelian₂) := by
    have := (GlobalTheory.HL.ComplAct.main M.L r k S (c.dat d0) (c.lat t.abelian₂) hterm0 (c.grp g)⁻¹ (inv_mem hgH)).1
    rwa [← hdat, inv_smul_smul] at this
  refine ⟨d, hdR, ⟨_, hterm⟩, ?_⟩
  obtain ⟨κ, -, hκ⟩ := GlobalTheory.T.exists_wt_eq_mul_nu' M hM H r k P S c d0
  have h1 := hκ d0 _ hterm0
  have h2 := hκ d _ hterm
  have hnu := (GlobalTheory.HL.Frames.nu_pos_and_smul M.L r k S (c.dat d) _ hterm).2 (c.grp g) hgH
  rw [hdat] at hnu
  have hself : LocNG.Datum.wt d0 d0 = 1 := by
    simp [LocNG.Datum.wt, LocNG.volRel, Subgroup.relIndex_self]
  rw [h2, ← hnu, ← h1, hself]

theorem total_le_generic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 d₁ : LocNG.Datum P) (t₁ : Term V M r), LocNG.IsTermOver P d₁ t₁ → ∀ Cl : Term V M r → Prop, (∀ t, Cl t ↔ ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, A i j ∈ M.L.O ∧ A' i j ∈ M.L.O ∧ ∃ c ∈ M.L.O, A' i j - A i j = algebraMap F E (LocNG.theta M) * c) ∧ (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧ (∀ j, t.f j = ∑ i, A i j • s (t₁.f i)) ∧ ∀ j, t.f' j = ∑ i, A' i j • s (t₁.f' i)) → ∀ g : ℝ≥0∞, g = ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : {t // t ∈ R.RT d.1 ∧ ¬ LocNG.BBne (H := H) t ∧ Cl t}, ENNReal.ofReal (LocNG.mu P t.1) → g ≠ ⊤ ∧ LocNG.nn R d0 ≤ ENNReal.ofReal (8 * P.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g ∧ (P.PrimeTo → LocNG.nn R d0 = g) ∧ ((∃ t', LocNG.IsTermOver P d0 t') → g ≠ 0) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hrank hrel R d0 d₁ t₁ ht₁ Cl hCl g hg
  have := hM.loc
  have := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hrank hrel
  have T22 := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  have T23 := GlobalTheory.T.hermitianFramePair_amplitude_mass_reps_eq_orbits M hM H r k P S c
  have T28 := GlobalTheory.T.framePairCoordinates_localHeight_eq_residueCard M hM H r k P S c
  have TR := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have h₁ : S.IsTerm (c.dat d₁) (c.lat t₁.abelian₂) := (T22.1 d₁ t₁ ht₁).1
  obtain ⟨κ, -, hκ⟩ := GlobalTheory.T.hermitianFramePair_tsum_reps_eq_const_mul_orbits M hM H r k P S c R d0
  obtain ⟨Qd, hQd⟩ : ∃ Qd : S.Datum → Submodule M.L.O S.V → Prop, Qd = fun δ Λ =>
      S.BBzero δ Λ ∧ ∃ s ∈ S.St, S.Fr δ Λ = s • S.Fr (c.dat d₁) (c.lat t₁.abelian₂) := ⟨_, rfl⟩
  have hvan : ∀ (δ : S.Datum) (Q : Submodule M.L.O S.V → Prop), (¬ ∃ Λ, S.IsTerm δ Λ) →
      S.mass δ Q = 0 := by
    intro δ Q hδ
    unfold GlobalTheory.HL.Frames.mass
    refine ENNReal.tsum_eq_zero.mpr fun o => ?_
    rw [if_neg]
    exact fun h => hδ ⟨_, h.1⟩
  have hQst : ∀ δ, ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ Λ → Qd δ Λ → Qd δ (s • Λ) := by
    intro δ s hs Λ hΛ hq
    rw [hQd] at hq ⊢
    obtain ⟨hB, s', hs', hF⟩ := hq
    have := GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S δ Λ hΛ s hs
    refine ⟨this.2.2.2.2.2.2.2.1.mpr hB, s * s', mul_mem hs hs', ?_⟩
    rw [this.2.2.2.2.1, hF, mul_smul]
  have hinv1 : ∀ h ∈ S.H0, ∀ δ, S.mass (h • δ) (Qd (h • δ)) = S.mass δ (Qd δ) := by
    intro h hh δ
    refine (GlobalTheory.InvH.amp_mass_smul M.L r k S h hh δ (Qd δ) (Qd (h • δ)) (hQst δ) ?_).2
    intro Λ hΛ
    have := GlobalTheory.HL.ComplAct.main M.L r k S δ Λ hΛ h hh
    simp only [hQd, GlobalTheory.HL.Frames.BBzero, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2]
  have hinv0 : ∀ h ∈ S.H0, ∀ δ, S.mass (h • δ) (fun _ => True) = S.mass δ (fun _ => True) :=
    fun h hh δ => (GlobalTheory.InvH.amp_mass_smul M.L r k S h hh δ _ _ (fun _ _ _ _ _ => trivial)
      (fun _ _ => Iff.rfl)).2
  have hnn : LocNG.nn R d0 = ENNReal.ofReal κ * S.nn := by
    rw [GlobalTheory.HL.Frames.nn, ← hκ (fun δ => S.mass δ (fun _ => True)) hinv0 (fun δ hδ => hvan δ _ hδ)]
    unfold LocNG.nn
    refine tsum_congr fun d => ?_
    rw [(T23 R d.1).2.2.2]
  have hCQ : ∀ d (t : Term V M r), LocNG.IsTermOver P d t →
      ((¬ LocNG.BBne (H := H) t ∧ Cl t) ↔ Qd (c.dat d) (c.lat t.abelian₂)) := by
    intro d t ht
    have hB := (T22.1 d t ht).2.2
    rw [hQd]
    simp only
    rw [fr_eq hM c d t ht, fr_eq hM c d₁ t₁ ht₁]
    refine and_congr (by rw [hB, not_not]) ?_
    rw [hCl t]
    constructor
    · rintro ⟨s, hs, A, A', hA, hlow, hdiag, hf, hf'⟩
      refine ⟨c.grp s, (TR.2.2.2.1 s).mp hs, ?_⟩
      rw [GlobalTheory.HL.FrameClass.smul_cls]
      have hmem : ((fun b => c.e (t.f b)), (fun b => c.e (t.f' b))) ∈
          S.frameCls (fun b => c.grp s (c.e (t₁.f b))) (fun b => c.grp s (c.e (t₁.f' b))) := by
        refine ⟨A, A', fun i j => (hA i j).1, fun i j => (hA i j).2.1, hlow, hdiag, fun i j => ?_,
          fun j => ?_, fun j => ?_⟩
        · obtain ⟨x, hx, hx'⟩ := (hA i j).2.2
          exact ⟨x, hx, by rw [hx', TR.1]⟩
        set_option synthInstance.maxHeartbeats 100000 in
          · simp only [hf j, map_sum, map_smul, GlobalTheory.HL.CoordUnip.grp_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          · simp only [hf' j, map_sum, map_smul, GlobalTheory.HL.CoordUnip.grp_apply]
      exact ((GlobalTheory.HL.FrameClass.frame_classes M.L r k S _ _).2.1 _ hmem).1
    · rintro ⟨s', hs', heq⟩
      obtain ⟨s, rfl⟩ := c.grp.surjective s'
      have hs : s ∈ P.St := (TR.2.2.2.1 s).mpr hs'
      rw [GlobalTheory.HL.FrameClass.smul_cls] at heq
      have hmem := (GlobalTheory.HL.FrameClass.frame_classes M.L r k S
        (fun b => c.e (t.f b)) (fun b => c.e (t.f' b))).1
      rw [heq] at hmem
      obtain ⟨A, A', hA, hA', hlow, hdiag, hcong, hf, hf'⟩ := hmem
      refine ⟨s, hs, A, A', fun i j => ⟨hA i j, hA' i j, ?_⟩, hlow, hdiag, fun j => ?_, fun j => ?_⟩
      · obtain ⟨x, hx, hx'⟩ := hcong i j
        exact ⟨x, hx, by rw [hx', TR.1]⟩
      · apply c.e.injective
        have := hf j
        simp only [GlobalTheory.HL.CoordUnip.grp_apply] at this
        set_option synthInstance.maxHeartbeats 100000 in
          rw [this, map_sum]
        simp only [map_smul]
      · apply c.e.injective
        have := hf' j
        simp only [GlobalTheory.HL.CoordUnip.grp_apply] at this
        set_option synthInstance.maxHeartbeats 100000 in
          rw [this, map_sum]
        simp only [map_smul]
  obtain ⟨G, hG⟩ : ∃ G : ℝ≥0∞, G = ENNReal.ofReal (S.wC (S.Fr (c.dat d₁) (c.lat t₁.abelian₂))) *
      (S.sumData fun δ => S.nT δ (S.Fr (c.dat d₁) (c.lat t₁.abelian₂)) fun Λ => S.BBzero δ Λ) := ⟨_, rfl⟩
  obtain ⟨hpos, hfin, hle, heq1⟩ :=
    GlobalTheory.HL.GenMass.total_le_generic M.L r k S hk (c.dat d₁) (c.lat t₁.abelian₂) h₁ G hG
  have hg' : g = ENNReal.ofReal κ * G := by
    rw [hg]
    have hsum : ∀ d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) *
        (∑' t : {t // t ∈ R.RT d.1 ∧ ¬ LocNG.BBne (H := H) t ∧ Cl t}, ENNReal.ofReal (LocNG.mu P t.1)) =
        ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * (fun δ => S.mass δ (Qd δ)) (c.dat d.1) := by
      intro d
      rw [sum_eq_mass hM c R d.1 _ (Qd (c.dat d.1)) (hQst _) (hCQ d.1)]
    rw [tsum_congr hsum, hκ (fun δ => S.mass δ (Qd δ)) hinv1 (fun δ hδ => hvan δ _ hδ), hG]
    congr 1
    have hφ : (fun δ => S.mass δ (Qd δ)) = fun δ => ENNReal.ofReal (S.wC (S.Fr (c.dat d₁) (c.lat t₁.abelian₂))) *
        S.nT δ (S.Fr (c.dat d₁) (c.lat t₁.abelian₂)) (fun Λ => S.BBzero δ Λ) := by
      funext δ
      rw [hQd]
      exact GlobalTheory.HL.MassOrbit.mass_orbit_class M.L r k S _ _ h₁ δ
    rw [hφ]
    unfold GlobalTheory.HL.Frames.sumData
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun o => ?_
    ring
  have hPS : P.Hp = S.Hp := T28.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hg']
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  · rw [hnn, hg', hPS]
    calc ENNReal.ofReal κ * S.nn
        ≤ ENNReal.ofReal κ * (ENNReal.ofReal (8 * S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * G) :=
          by gcongr
      _ = ENNReal.ofReal (8 * S.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * (ENNReal.ofReal κ * G) :=
          mul_left_comm _ _ _
  · intro hpt
    obtain ⟨hgg, hv, hD⟩ := T28.2.2 hpt
    have hHp : S.Hp = 1 := (GlobalTheory.HL.GoodPlace.equality M.L r k S hk hgg hv hD).2.1
    rw [hnn, hg', heq1 hHp]
  · rintro ⟨t', ht'⟩
    rw [hg']
    refine mul_ne_zero ?_ hpos.ne'
    obtain ⟨dd, hdd, hterm, hwt⟩ := exists_wt_one hM c R d0 t' ht'
    have hex : ∀ h ∈ S.H0, ∀ δ : S.Datum, (∃ Λ, S.IsTerm (h • δ) Λ) ↔ ∃ Λ, S.IsTerm δ Λ := by
      intro h hh δ
      constructor
      · rintro ⟨Λ, hΛ⟩
        have := (GlobalTheory.HL.ComplAct.main M.L r k S _ _ hΛ h⁻¹ (inv_mem hh)).1
        rw [inv_smul_smul] at this
        exact ⟨_, this⟩
      · rintro ⟨Λ, hΛ⟩
        exact ⟨_, (GlobalTheory.HL.ComplAct.main M.L r k S _ _ hΛ h hh).1⟩
    have hind := hκ (fun δ => if ∃ Λ, S.IsTerm δ Λ then (1 : ℝ≥0∞) else 0)
      (fun h hh δ => by simp only [hex h hh δ]) (fun δ hδ => by simp only [hδ, if_false])
    intro hκz
    have hle1 : (1 : ℝ≥0∞) ≤ ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) *
        (fun δ => if ∃ Λ, S.IsTerm δ Λ then (1 : ℝ≥0∞) else 0) (c.dat d.1) := by
      refine le_trans ?_ (ENNReal.le_tsum ⟨dd, hdd⟩)
      simp [hwt, hterm]
    rw [hind, hκz, zero_mul] at hle1
    exact absurd hle1 (by norm_num)

end GlobalTheory.HL.AbsGenMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTotalMassLeGenericMassStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_total_mass_le_generic_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 d₁ : LocNG.Datum P) (t₁ : Term V M r), LocNG.IsTermOver P d₁ t₁ → ∀ Cl : Term V M r → Prop, (∀ t, Cl t ↔ ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, A i j ∈ M.L.O ∧ A' i j ∈ M.L.O ∧ ∃ c ∈ M.L.O, A' i j - A i j = algebraMap F E (LocNG.theta M) * c) ∧ (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧ (∀ j, t.f j = ∑ i, A i j • s (t₁.f i)) ∧ ∀ j, t.f' j = ∑ i, A' i j • s (t₁.f' i)) → ∀ g : ℝ≥0∞, g = ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : {t // t ∈ R.RT d.1 ∧ ¬ LocNG.BBne (H := H) t ∧ Cl t}, ENNReal.ofReal (LocNG.mu P t.1) → g ≠ ⊤ ∧ LocNG.nn R d0 ≤ ENNReal.ofReal (8 * P.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g ∧ (P.PrimeTo → LocNG.nn R d0 = g) ∧ ((∃ t', LocNG.IsTermOver P d0 t') → g ≠ 0) := by
  first | exact @GlobalTheory.HL.AbsGenMass.total_le_generic | exact GlobalTheory.HL.AbsGenMass.total_le_generic | (intros; apply GlobalTheory.HL.AbsGenMass.total_le_generic <;> assumption)
end
