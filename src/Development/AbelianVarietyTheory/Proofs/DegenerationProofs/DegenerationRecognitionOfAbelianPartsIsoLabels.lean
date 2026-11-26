module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLatticeIsoAndTermsAgree
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoOnG
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReducedBasisOfLinearIndependent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionMatchedPartsDimEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionMatchedPartsDimEq
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.MatchParts

section Gen
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}

theorem qrefl {k : ℕ} (p : N.QT k) : N.QEq p p := by
  exact ⟨0, by simp, by simp⟩

theorem r_right (μ : Match N N' n) {k : ℕ} {p : N.QT k} {p' q' : N'.QT k} (h : μ.r k p p') :
    μ.r k p q' ↔ N'.QEq p' q' := μ.eqv k p p p' q' h (qrefl p)

theorem r_left (μ : Match N N' n) {k : ℕ} {p q : N.QT k} {p' : N'.QT k} (h : μ.r k p p') (e : N.QEq p q) :
    μ.r k q p' := (μ.eqv k p q p' p' h e).2 (qrefl p')

noncomputable def flip (μ : Match N N' n) : Match N' N n where
  r k p' p := μ.r k p p'
  tot := μ.cotot
  cotot := μ.tot
  mul k p q p' q' h h' := μ.mul k _ _ _ _ h h'
  eqv k p' q' p q h e :=
    ⟨fun h' => μ.inj k p q q' ((r_right μ h).2 e) h', fun e' => (μ.eqv k p q p' q' h e').2 e⟩
  inj k p' q' p h h' := (r_right μ h).1 h'
  incl k k' p' p q' q hk a b c d := μ.incl k k' p p' q q' hk c d a b
  wp k p' q' p q h h' := (μ.wp k p q p' q' h h').symm
  c₀ := μ.c₀⁻¹
  c₀_ne := inv_ne_zero μ.c₀_ne
  tx j p' p h := by rw [μ.tx j p p' h, ← mul_assoc, inv_mul_cancel₀ μ.c₀_ne, one_mul]

theorem tot' (μ : Match N N' n) {k : ℕ} (hk : ∃ j, k = n ^ j) (p : N.QT k) : ∃ p', μ.r k p p' := by
  obtain ⟨j, rfl⟩ := hk
  exact μ.tot j p

theorem qmul {k : ℕ} {p q : N.QT k} (a : N.QT k) (h : N.QEq p q) : N.QEq (a * p) (a * q) := by
  rw [N.qEq_iff] at h ⊢
  obtain ⟨z, rfl⟩ := h
  exact ⟨z, (mul_assoc _ _ _).symm⟩

theorem r_one (μ : Match N N' n) {k : ℕ} (hk : ∃ j, k = n ^ j) : μ.r k 1 1 := by
  obtain ⟨p', h⟩ := tot' μ hk 1
  have h2 := μ.mul k _ _ _ _ h h
  rw [mul_one] at h2
  have h3 := qmul p'⁻¹ ((r_right μ h).1 h2)
  rw [inv_mul_cancel, inv_mul_cancel_left] at h3
  apply (r_right μ h).2
  obtain ⟨z, hz, hz'⟩ := h3
  exact ⟨-z, by rw [hz, smul_neg, add_neg_cancel_right],
    by rw [hz', N'.io_neg, mul_inv_cancel_right]⟩

theorem r_pow (μ : Match N N' n) {k : ℕ} (hk : ∃ j, k = n ^ j) {p : N.QT k} {p' : N'.QT k} (h : μ.r k p p')
    (a : ℕ) : μ.r k (p ^ a) (p' ^ a) := by
  induction a with
  | zero => simpa using r_one μ hk
  | succ a ih => rw [pow_succ, pow_succ]; exact μ.mul k _ _ _ _ ih h

theorem r_inv (μ : Match N N' n) {k : ℕ} (hk : ∃ j, k = n ^ j) {p : N.QT k} {p' : N'.QT k} (h : μ.r k p p') :
    μ.r k p⁻¹ p'⁻¹ := by
  obtain ⟨q', hq⟩ := tot' μ hk p⁻¹
  have h2 := μ.mul k _ _ _ _ h hq
  rw [mul_inv_cancel] at h2
  have h3 := qmul p'⁻¹ ((r_right μ h2).1 (r_one μ hk))
  rw [inv_mul_cancel_left, mul_one] at h3
  exact (r_right μ hq).2 h3

def ofG {k : ℕ} (x : N.Gt) (hx : x ^ k = 1) : N.QT k := ⟨(1, x), by rw [N.mem_QT]; exact hx.trans N.io_zero.symm⟩

theorem pow_eq_one_of {k : ℕ} (p : N.QT k) (h : p.1.1 = 1) : p.1.2 ^ k = 1 := by
  have := N.mem_QT.1 p.2
  rw [this, h]; exact N.io_zero

theorem exists_rep {k : ℕ} {p : N.QT k} (h : N.InG p) : ∃ q, N.QEq p q ∧ q.1.1 = 1 := by
  obtain ⟨z, hz⟩ := h
  refine ⟨p * N.qTriv k (-z), (N.qEq_iff _ _).2 ⟨_, rfl⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  change p.1.1.toAdd + k • (-z) = 0
  rw [hz, smul_neg, add_neg_cancel]

theorem y_pow {k : ℕ} (p : N.QT k) (a : ℕ) : (p ^ a).1.1.toAdd = a • p.1.1.toAdd := by simp

theorem nsmul_cancel {a : ℕ} (ha : a ≠ 0) {x y : N.X} (h : a • x = a • y) : x = y := by
  have : (a : ℤ) • x = (a : ℤ) • y := by simpa using h
  exact smul_right_injective N.X (by exact_mod_cast ha) this

theorem half_div (μ : Match N N' n) (j : ℕ) (hj : 2 ≤ j) (hdiv : ∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ n = γ)
    (hc : ‖μ.c₀‖ = 1)
    (hcos : ∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧
      ‖N.tx (n ^ j) (p * h)‖ = 1)
    (hsup : ∀ p : N'.QT ((n ^ j) ^ 2), ‖N'.tx (n ^ j) p‖ = 1 → ∃ z, p.1.1.toAdd = n ^ j • z)
    (p : N.QT ((n ^ j) ^ 2)) (hp : p.1.1 = 1) :
    ∃ p', μ.r _ p p' ∧ ∃ z, p'.1.1.toAdd = n ^ j • z := by
  have hk : ∃ i, (n ^ j) ^ 2 = n ^ i := ⟨j * 2, (pow_mul _ _ _).symm⟩
  let P : N.QT ((n ^ j) ^ 2) → Prop := fun p => ∃ p', μ.r _ p p' ∧ ∃ z, p'.1.1.toAdd = n ^ j • z
  have Pmul : ∀ a b, P a → P b → P (a * b) := by
    rintro a b ⟨a', ha, z, hz⟩ ⟨b', hb, w, hw⟩
    refine ⟨a' * b', μ.mul _ _ _ _ _ ha hb, z + w, ?_⟩
    change a'.1.1.toAdd + b'.1.1.toAdd = _
    rw [hz, hw, smul_add]
  have Ppow : ∀ a (i : ℕ), P a → P (a ^ i) := by
    rintro a i ⟨a', ha, z, hz⟩
    exact ⟨a' ^ i, r_pow μ hk ha i, i • z, by rw [y_pow, hz, smul_comm]⟩
  have step : ∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ s d, P s ∧ d.1.1 = 1 ∧ p = s * d ^ n := by
    intro p hp
    obtain ⟨h, h1, h2, h3⟩ := hcos p hp
    obtain ⟨s', hs'⟩ := tot' μ hk (p * h)
    obtain ⟨δ, hδ⟩ := hdiv h.1.2⁻¹
    have hδ' : δ ^ (n ^ j) ^ 2 = 1 := by
      obtain ⟨i, hi⟩ : ∃ i, j * 2 = 1 + (j + 1) + i := ⟨j - 2, by omega⟩
      rw [← pow_mul, hi, pow_add, pow_add, pow_one, pow_mul, pow_mul, hδ, inv_pow, h2, inv_one, one_pow]
    refine ⟨p * h, ofG δ hδ', ⟨s', hs', hsup s' ?_⟩, rfl, ?_⟩
    · rw [μ.tx j _ _ hs', norm_mul, hc, h3, one_mul]
    · have : ofG δ hδ' ^ n = h⁻¹ := by
        refine Subtype.ext (Prod.ext ?_ ?_)
        · simp [ofG, h1]
        · simpa [ofG] using hδ
      rw [this, mul_inv_cancel_right]
  have iter : ∀ i : ℕ, ∃ s d, P s ∧ d.1.1 = 1 ∧ p = s * d ^ n ^ i := by
    intro i
    induction i with
    | zero => exact ⟨1, p, ⟨1, r_one μ hk, 0, by simp⟩, hp, by simp⟩
    | succ i ih =>
      obtain ⟨s, d, hs, hd, e⟩ := ih
      obtain ⟨s₂, d₂, hs₂, hd₂, e₂⟩ := step d hd
      refine ⟨s * s₂ ^ n ^ i, d₂, Pmul _ _ hs (Ppow _ _ hs₂), hd₂, ?_⟩
      rw [e, e₂, mul_pow, ← pow_mul d₂, mul_assoc s, pow_succ' n i]
  obtain ⟨s, d, hs, -, e⟩ := iter j
  rw [e]
  obtain ⟨d', hd'⟩ := tot' μ hk d
  exact Pmul _ _ hs ⟨_, r_pow μ hk hd' _, _, y_pow _ _⟩

theorem inG_of_half (μ : Match N N' n) {k k' K m : ℕ} (hK : K = k * k') (hm : K = m * m) (hkm : k ∣ m) (hm0 : m ≠ 0)
    (hlev : ∃ j, K = n ^ j) (hdiv : ∀ γ : N.Gt, ∃ γ' : N.Gt, γ' ^ m = γ)
    (H : ∀ p : N.QT K, p.1.1 = 1 → ∃ p', μ.r K p p' ∧ ∃ z, p'.1.1.toAdd = m • z)
    (p : N.QT k) (p' : N'.QT k) (h : μ.r k p p') (hp : N.InG p) : N'.InG p' := by
  subst hK
  have hk' : k' ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hm0 hm0 (hm.symm.trans (mul_zero _))
  obtain ⟨p₀, e, h0⟩ := exists_rep hp
  replace h := r_left μ h e
  have hx := pow_eq_one_of p₀ h0
  obtain ⟨ξ, hξ⟩ := hdiv p₀.1.2
  have hξ' : ξ ^ (k * k') = 1 := by
    obtain ⟨c, hc⟩ := hkm
    rw [hm, pow_mul, hξ, hc, pow_mul, hx, one_pow]
  obtain ⟨ξ', hr, z, hz⟩ := H (ofG ξ hξ') rfl
  let q' : N'.QT (k * k') := ⟨(p'.1.1 ^ k', p'.1.2), by
    rw [N'.mem_QT, pow_mul, N'.mem_QT.1 p'.2, toAdd_pow, N'.io_nsmul]⟩
  have hq : μ.r (k * k') (ofG ξ hξ' ^ m) q' :=
    (μ.incl k k' p₀ p' _ q' hk' (by simp [ofG, h0]) (by simpa [ofG] using hξ) rfl rfl).1 h
  obtain ⟨w, hw, -⟩ := (r_right μ (r_pow μ hlev hr m)).1 hq
  refine ⟨z + w, nsmul_cancel hk' ?_⟩
  rw [y_pow, hz, smul_smul, ← hm, ← smul_add] at hw
  rw [smul_smul, mul_comm, ← hw]
  rfl

theorem inT_of_inG (μ : Match N N' n) (j : ℕ)
    (hG : ∀ p p', μ.r (n ^ j) p p' → N'.InG p' → N.InG p)
    (hT : ∀ p : N.QT (n ^ j), N.InT p → ∀ p' : N.QT (n ^ j), p'.1.1 = 1 → N.wp p p' = 1)
    (hT' : ∀ p : N'.QT (n ^ j), (∀ p' : N'.QT (n ^ j), p'.1.1 = 1 → N'.wp p p' = 1) → N'.InT p)
    (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j)) (h : μ.r _ p p') (hp : N.InT p) : N'.InT p' := by
  refine hT' p' fun t' ht' => ?_
  obtain ⟨t, ht⟩ := μ.cotot j t'
  obtain ⟨t₀, e, h0⟩ := exists_rep (hG t t' ht ⟨0, by simp [ht']⟩)
  rw [μ.wp _ p t₀ p' t' h (r_left μ ht e)]
  exact hT p hp t₀ h0

theorem card_le_of_rel {α β : Type} [Finite β] (R : α → β → Prop) (h : ∀ a, ∃ b, R a b)
    (hi : ∀ a a' b, R a b → R a' b → a = a') : Nat.card α ≤ Nat.card β := by
  choose f hf using h
  exact Nat.card_le_card_of_injective f fun a a' e => hi a a' (f a) (hf a) (e ▸ hf a')

theorem rank_le (μ : Match N N' n) (hn : 1 < n) {k : ℕ} (hk : k = n ^ 1)
    (hG : ∀ p p', μ.r k p p' → N'.InG p' → N.InG p) (hy : ∀ y : N.X, ∃ p : N.QT k, p.1.1.toAdd = y) :
    Module.finrank ℤ N.X ≤ Module.finrank ℤ N'.X := by
  have hl : ∃ j, k = n ^ j := ⟨1, hk⟩
  have hk1 : 1 < k := by rw [hk, pow_one]; exact hn
  have h1 : Nat.card (N.X ⧸ (nsmulAddMonoidHom k : N.X →+ N.X).range) = k ^ Module.finrank ℤ N.X :=
    AddSubgroup.index_range_nsmul N.X k
  have h2 : Nat.card (N'.X ⧸ (nsmulAddMonoidHom k : N'.X →+ N'.X).range) = k ^ Module.finrank ℤ N'.X :=
    AddSubgroup.index_range_nsmul N'.X k
  haveI : Finite (N'.X ⧸ (nsmulAddMonoidHom k : N'.X →+ N'.X).range) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; positivity)
  rw [← Nat.pow_le_pow_iff_right hk1, ← h1, ← h2]
  refine card_le_of_rel (fun a b => ∃ p p', μ.r k p p' ∧ a = QuotientAddGroup.mk p.1.1.toAdd ∧
    b = QuotientAddGroup.mk p'.1.1.toAdd) (fun a => ?_) ?_
  · obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨p, rfl⟩ := hy y
    obtain ⟨p', h⟩ := tot' μ hl p
    exact ⟨_, p, p', h, rfl, rfl⟩
  · rintro _ _ _ ⟨p, p', h, rfl, rfl⟩ ⟨q, q', h', rfl, e⟩
    obtain ⟨z, hz⟩ := QuotientAddGroup.eq.1 e
    obtain ⟨w, hw⟩ := hG _ _ (μ.mul k _ _ _ _ (r_inv μ hl h) h') ⟨z, hz.symm⟩
    exact QuotientAddGroup.eq.2 ⟨w, hw.symm⟩

theorem tors_le (μ : Match N N' n) (hn : 1 < n) {k a a' : ℕ} (hk : k = n ^ 1)
    (hG : ∀ p p', μ.r k p p' → N.InG p → N'.InG p')
    (e : Nonempty ((powMonoidHom k : N.Gt →* N.Gt).ker ≃* Multiplicative (Fin a → ZMod k)))
    (e' : Nonempty ((powMonoidHom k : N'.Gt →* N'.Gt).ker ≃* Multiplicative (Fin a' → ZMod k))) : a ≤ a' := by
  have hl : ∃ j, k = n ^ j := ⟨1, hk⟩
  have hk1 : 1 < k := by rw [hk, pow_one]; exact hn
  obtain ⟨e⟩ := e
  obtain ⟨e'⟩ := e'
  have h1 : Nat.card (powMonoidHom k : N.Gt →* N.Gt).ker = k ^ a := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun]; simp
  have h2 : Nat.card (powMonoidHom k : N'.Gt →* N'.Gt).ker = k ^ a' := by
    rw [Nat.card_congr e'.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun]; simp
  haveI : Finite (powMonoidHom k : N'.Gt →* N'.Gt).ker :=
    Nat.finite_of_card_ne_zero (by rw [h2]; positivity)
  rw [← Nat.pow_le_pow_iff_right hk1, ← h1, ← h2]
  refine card_le_of_rel (fun x x' => μ.r k (ofG x.1 x.2) (ofG x'.1 x'.2)) (fun x => ?_) ?_
  · obtain ⟨p', h⟩ := tot' μ hl (ofG x.1 x.2)
    obtain ⟨q', e, h0⟩ := exists_rep (hG _ _ h ⟨0, by simp [ofG]⟩)
    refine ⟨⟨q'.1.2, pow_eq_one_of q' h0⟩, ?_⟩
    have : ofG q'.1.2 (pow_eq_one_of q' h0) = q' := Subtype.ext (Prod.ext h0.symm rfl)
    have h' := (r_right μ h).2 e
    rw [← this] at h'
    exact h'
  · intro x y b h h'
    obtain ⟨z, hz, hz'⟩ := μ.inj k _ _ _ h h'
    have : z = 0 := nsmul_cancel (a := k) (by omega) (by simpa [ofG] using hz.symm)
    rw [this, N.io_zero, mul_one] at hz'
    exact Subtype.ext hz'.symm

end Gen

section Main
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
  {N N' : NumD C} {q : QuadraticMap ℤ N.X ℝ} {q' : QuadraticMap ℤ N'.X ℝ} {n g g' : ℕ}

theorem norm_le (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hI : N.Int q) (hI' : N'.Int q')
    (hT : N.Tors n g) (hT' : N'.Tors n g') (μ : Match N N' n) : ‖μ.c₀‖ ≤ 1 := by
  obtain ⟨h, -, -, hh⟩ := (GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N q hI n g hn ho h1 hT 1 le_rfl).2.1 1 rfl
  obtain ⟨p', hp'⟩ := tot' μ ⟨1 * 2, (pow_mul n 1 2).symm⟩ (1 * h)
  have := ((GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N' q' hI' n g' hn ho h1 hT' 1 le_rfl).1 p').1
  rwa [μ.tx 1 _ _ hp', norm_mul, hh, mul_one] at this

theorem norm_eq (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hI : N.Int q) (hI' : N'.Int q')
    (hT : N.Tors n g) (hT' : N'.Tors n g') (μ : Match N N' n) : ‖μ.c₀‖ = 1 := by
  refine le_antisymm (norm_le hn ho h1 hI hI' hT hT' μ) ?_
  have : ‖μ.c₀⁻¹‖ ≤ 1 := norm_le hn ho h1 hI' hI hT' hT (flip μ)
  rwa [norm_inv, inv_le_one₀ (norm_pos_iff.2 μ.c₀_ne)] at this

theorem inG_imp (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hI : N.Int q) (hI' : N'.Int q')
    (hT : N.Tors n g) (hT' : N'.Tors n g') (μ : Match N N' n) (j : ℕ) (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j))
    (h : μ.r _ p p') (hp : N.InG p) : N'.InG p' := by
  have h0 : (n : C) ≠ 0 := fun e => by simp [e] at h1
  refine inG_of_half μ (k' := n ^ (j + 4)) (K := (n ^ (j + 2)) ^ 2) (m := n ^ (j + 2)) (by ring) (by ring)
    (pow_dvd_pow _ (by omega)) (pow_ne_zero _ hn.ne_zero) ⟨_, (pow_mul _ _ _).symm⟩
    (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g h0 hT (j + 2)).2.1 ?_ p p' h hp
  exact half_div μ (j + 2) (by omega) (by simpa using (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g h0 hT 1).2.1)
    (norm_eq hn ho h1 hI hI' hT hT' μ) (GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N q hI n g hn ho h1 hT (j + 2) (by omega)).2.1
    fun p => ((GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N' q' hI' n g' hn ho h1 hT' (j + 2) (by omega)).1 p).2

theorem inT_imp (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hI : N.Int q) (hI' : N'.Int q')
    (hT : N.Tors n g) (hT' : N'.Tors n g') (μ : Match N N' n) (j : ℕ) (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j))
    (h : μ.r _ p p') (hp : N.InT p) : N'.InT p' := by
  have h0 : (n : C) ≠ 0 := fun e => by simp [e] at h1
  exact inT_of_inG μ j (fun p p' h => inG_imp hn ho h1 hI' hI hT' hT (flip μ) j p' p h)
    (fun p => ((GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g h0 hT j).2.2.2.2.1 p).2)
    (fun p => ((GlobalTheory.T.degenerationData_torsion_structure_algClosed C N' n g' h0 hT' j).2.2.2.2.1 p).1) p p' h hp

theorem ranks_le (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hI : N.Int q) (hI' : N'.Int q')
    (hT : N.Tors n g) (hT' : N'.Tors n g') (μ : Match N N' n) :
    Module.finrank ℤ N.X ≤ Module.finrank ℤ N'.X ∧
      2 * g + Module.finrank ℤ N.X ≤ 2 * g' + Module.finrank ℤ N'.X := by
  have h0 : (n : C) ≠ 0 := fun e => by simp [e] at h1
  exact ⟨rank_le μ hn.one_lt rfl (fun p p' h => inG_imp hn ho h1 hI' hI hT' hT (flip μ) 1 p' p h)
      (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g h0 hT 1).2.2.1,
    tors_le μ hn.one_lt rfl (inG_imp hn ho h1 hI hI' hT hT' μ 1)
      (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g h0 hT 1).2.2.2.1 (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N' n g' h0 hT' 1).2.2.2.1⟩

end Main

theorem match_parts : AllMatch fun μ g g' => μ.A ∧ g = g' := by
  intro C _ _ _ _ N N' q q' n g g' hn ho h1 hI hI' hT hT' μ
  refine ⟨⟨norm_eq hn ho h1 hI hI' hT hT' μ, fun j p p' h =>
    ⟨⟨inG_imp hn ho h1 hI hI' hT hT' μ j p p' h, inG_imp hn ho h1 hI' hI hT' hT (flip μ) j p' p h⟩,
     ⟨inT_imp hn ho h1 hI hI' hT hT' μ j p p' h, inT_imp hn ho h1 hI' hI hT' hT (flip μ) j p' p h⟩⟩⟩, ?_⟩
  have a := ranks_le hn ho h1 hI hI' hT hT' μ
  have b := ranks_le hn ho h1 hI' hI hT' hT (flip μ)
  omega

end GlobalTheory.MatchParts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionMatchedPartsDimEqStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRecognition_matched_parts_dim_eq : AllMatch fun μ g g' => μ.A ∧ g = g' := by
  first | exact @GlobalTheory.MatchParts.match_parts | exact GlobalTheory.MatchParts.match_parts | (intros; apply GlobalTheory.MatchParts.match_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLabelsAgreeOfIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisUniqueMinPairSums
open Module

namespace GlobalTheory

theorem exists_basis_unique_min_pair_sums (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (d g N : ℕ) (hd : finrank ℤ X = d)
    (hg : d ≤ g) (hN : 1 + 4 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N) :
    ∃ e : Basis (Fin d) ℤ X, ∀ (i j : Fin d) (μ : X), μ ≠ 0 →
      q (e i) < q (e i + N • μ) ∧ q (e i + e j) < q (e i + e j + N • μ) := by
  have hq' := posDef_realExt_of_tendsto q hq
  obtain ⟨e, h1, -, -⟩ := exists_reduced_basis_unique_min_of_le hd hg q hq'
  have hp := posDef_of_posDef_realExt hq'
  set c := (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) with hc
  have hc0 : 0 ≤ c := by positivity
  have hN' : 1 + 4 * c < ((N : ℤ) : ℝ) := by
    rw [hc, ← mul_assoc]; exact_mod_cast hN
  refine ⟨e, fun i j μ hμ => ?_⟩
  rw [← natCast_zsmul]
  refine ⟨(lt_add_smul_of_abs_polar_le q hc0 (by linarith) (hp μ hμ) (h1 i μ)).1,
    (lt_add_smul_of_abs_polar_le q (c := 2 * c) (by positivity) (by linarith) (hp μ hμ) ?_).1⟩
  rw [QuadraticMap.polar_add_left]
  refine (abs_add_le _ _).trans ?_
  linarith [h1 i μ, h1 j μ]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmPairingEqOneOfOddOfDiag
open scoped BigOperators
open Matrix

namespace GlobalTheory

private lemma eq_one_of_pow_eq_one_of_dvd_two_mul_sub_one {U : Type} [CommGroup U] (k : ℕ) (b : ℤ) (hb : (k : ℤ) ∣ 2 * b - 1)
    (u : U) (hu : u ^ k = 1) (h : u ^ b * u ^ b = 1) : u = 1 := by
  obtain ⟨m, hm⟩ := hb
  have h2 : u ^ (2 * b) = 1 := by rw [two_mul, _root_.zpow_add]; exact h
  have hk : u ^ (k : ℤ) = 1 := by rw [zpow_natCast]; exact hu
  have hsplit : 2 * b = k * m + 1 := by linarith
  rw [hsplit, _root_.zpow_add, _root_.zpow_mul, hk, _root_.one_zpow, one_mul, _root_.zpow_one] at h2
  exact h2

private lemma eq_one_of_hom_eq_one_on_basis {X U : Type} [AddCommGroup X] [CommGroup U] {d : ℕ}
    (e : Module.Basis (Fin d) ℤ X) (f : X → U) (hf : ∀ x x', f (x + x') = f x * f x')
    (he : ∀ i, f (e i) = 1) (x : X) : f x = 1 := by
  have h0 : f 0 = 1 := by
    have h := hf 0 0
    rw [add_zero] at h
    simpa using h
  let g : X →+ Additive U :=
    { toFun := fun x => Additive.ofMul (f x)
      map_zero' := by simp [h0]
      map_add' := fun x x' => by simp [hf] }
  have hg : g.toIntLinearMap = 0 := e.ext fun i => by simp [g, he]
  have hx := LinearMap.congr_fun hg x
  simpa [g] using hx

theorem symm_pairing_eq_one_of_odd_of_diag :
    ∀ (X U : Type) [AddCommGroup X] [CommGroup U] (d k : ℕ) (e : Module.Basis (Fin d) ℤ X) (b : ℤ), Odd k → (k : ℤ) ∣ 2 * b - 1 → ∀ δ : X → X → U, (∀ x x' y, δ (x + x') y = δ x y * δ x' y) → (∀ x y, δ x y = δ y x) → (∀ x y, δ x y ^ k = 1) → (∀ i, δ (e i) (e i) ^ b = 1) → (∀ i j, δ (e i + e j) (e i + e j) ^ b = 1) → ∀ x y, δ x y = 1 := by
  intro X U _ _ d k e b _ hb δ hadd hsymm hk1 hdiag hdiag2
  have hadd2 : ∀ x y y', δ x (y + y') = δ x y * δ x y' := by
    intro x y y'
    rw [hsymm x, hadd, hsymm y, hsymm y']
  have hoff : ∀ i j, δ (e i) (e j) = 1 := by
    intro i j
    have h := hdiag2 i j
    rw [hadd, hadd2, hadd2, hsymm (e j) (e i), _root_.mul_zpow, _root_.mul_zpow, _root_.mul_zpow, hdiag i, hdiag j] at h
    apply eq_one_of_pow_eq_one_of_dvd_two_mul_sub_one k b hb _ (hk1 _ _)
    simpa using h
  have hrow : ∀ i y, δ (e i) y = 1 := fun i =>
    eq_one_of_hom_eq_one_on_basis e (δ (e i)) (hadd2 (e i)) (hoff i)
  intro x y
  exact eq_one_of_hom_eq_one_on_basis e (fun x => δ x y) (fun x x' => hadd x x' y) (fun i => hrow i y) x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLabelsAgreeOfIso
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.LabelsAgree

section Transport
variable {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N')

def toHom : NumD.Hom (RingHom.id O) N N' where
  φ := J.φ.toMonoidHom
  h := J.h
  h_one := J.h_one
  θ_eq := J.θ_eq
  σ_eq := J.σ_eq
  lam := J.lam
  th_eq := J.th_eq
  e := J.e
  c_eq := J.c_eq
  ψ_eq := J.ψ_eq

def TR {k : ℕ} (p : N.QT k) (p' : N'.QT k) : Prop :=
  p'.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 p'.1.2

theorem rel_unique {g : N.Gt} {a b : N'.Gt} (ha : J.Rel g a) (hb : J.Rel g b) : a = b :=
  ((GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).1 g).unique ha hb

theorem rel_mul {g h : N.Gt} {a b : N'.Gt} (ha : J.Rel g a) (hb : J.Rel h b) : J.Rel (g * h) (a * b) :=
  (GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).2.1 g h a b ha hb

theorem rel_pow {g : N.Gt} {a : N'.Gt} (ha : J.Rel g a) (k : ℕ) : J.Rel (g ^ k) (a ^ k) := by
  induction k with
  | zero => simpa using J.rel_one
  | succ k ih => rw [pow_succ, pow_succ]; exact rel_mul J ih ha

theorem tr_exists {k : ℕ} (p : N.QT k) : ∃ p', TR J p p' := by
  obtain ⟨g', hg'⟩ := ((GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).1 p.1.2).exists
  have h1 := rel_pow J hg' k
  rw [N.mem_QT.1 p.2] at h1
  have h2 : J.Rel (N.io p.1.1.toAdd) (N'.io (J.e p.1.1.toAdd)) := (GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).2.2.1 _
  exact ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g'), rel_unique J h1 h2⟩, rfl, hg'⟩

theorem tr_unique {k : ℕ} {p : N.QT k} {a b : N'.QT k} (ha : TR J p a) (hb : TR J p b) : a = b :=
  Subtype.ext (Prod.ext (ha.1.trans hb.1.symm) (rel_unique J ha.2 hb.2))

theorem tr_mul {k : ℕ} {p q : N.QT k} {a b : N'.QT k} (ha : TR J p a) (hb : TR J q b) :
    TR J (p * q) (a * b) := by
  refine ⟨?_, rel_mul J ha.2 hb.2⟩
  change a.1.1.toAdd + b.1.1.toAdd = J.e (p.1.1.toAdd + q.1.1.toAdd)
  rw [map_add (f := _), ha.1, hb.1]

theorem tr_wp {k : ℕ} {p q : N.QT k} {a b : N'.QT k} (ha : TR J p a) (hb : TR J q b) :
    N'.wp a b = N.wp p q :=
  (GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).2.2.2.1 k p q a b ha.1 ha.2 hb.1 hb.2

theorem tr_txT {m : ℕ} (hm : Odd m) {p : N.QT (m ^ 2)} {a : N'.QT (m ^ 2)} (ha : TR J p a) (χ : N.X) :
    N'.txT m a (J.e χ) = J.lam * N.txT m p χ :=
  ((GlobalTheory.T.hom_transport_alt _ _ _ _ _ (toHom J)).2.2.2.2 m hm p a ha.1 ha.2 χ).1

theorem eq_of_qEq {k : ℕ} (hk : k ≠ 0) {p q : N.QT k} (h : N.QEq p q) (hy : p.1.1 = q.1.1) : p = q := by
  obtain ⟨z, h1, h2⟩ := h
  have hz : k • z = 0 := by rw [hy] at h1; exact left_eq_add.1 h1
  have hz0 : z = 0 := by
    have := TorsionFourier.add_nsmul_injective (Nat.pos_of_ne_zero hk) (0 : N.X) (a₁ := z) (a₂ := 0)
      (by simp [hz])
    exact this
  rw [hz0, N.io_zero, mul_one] at h2
  exact Subtype.ext (Prod.ext hy h2.symm)

theorem wp_mul_left {k : ℕ} (p p' q : N.QT k) : N.wp (p * p') q = N.wp p q * N.wp p' q :=
  (GlobalTheory.T.degenerationWeilPairing_properties _ N k p p' q).1

theorem wp_mul_right {k : ℕ} (p q q' : N.QT k) : N.wp p (q * q') = N.wp p q * N.wp p q' := by
  rw [N.wp_swap, wp_mul_left, mul_inv, ← N.wp_swap, ← N.wp_swap]

theorem wp_tor {k : ℕ} {d : N.QT k} (h1 : d.1.1 = 1) (h2 : d.1.2.b = 1) (q : N.QT k) :
    N.wp d q = d.1.2.s q.1.1.toAdd :=
  (GlobalTheory.T.degenerationWeilPairing_properties _ N k d q q).2.2.2.2.2.1 h1 h2

end Transport

theorem exists_char_root {C X : Type} [Field C] [IsAlgClosed C] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (u : Multiplicative X →* Cˣ) {k : ℕ} (hk : k ≠ 0) : ∃ t : Multiplicative X →* Cˣ, t ^ k = u := by
  let b := Module.finBasis ℤ X
  have h : ∀ x : Cˣ, ∃ y : Cˣ, y ^ k = x := fun x => by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : C) (Nat.pos_of_ne_zero hk)
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hk] at hy
      exact x.ne_zero hy.symm
    exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩
  choose r hr using h
  refine ⟨TorsionFourier.charOfValues b fun i => r (u (Multiplicative.ofAdd (b i))), MonoidHom.ext fun x => ?_⟩
  change (∏ i, r (u (Multiplicative.ofAdd (b i))) ^ (b.repr x.toAdd i)) ^ k = u (Multiplicative.ofAdd x.toAdd)
  rw [TorsionFourier.char_apply_eq_prod b u, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hr]

section Level
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n) (J : NumD.Iso N N')

theorem exists_norm (hB : μ.B J.e) (j : ℕ) (p : N.QT (n ^ j)) :
    ∃ p', μ.r (n ^ j) p p' ∧ p'.1.1.toAdd = J.e p.1.1.toAdd := by
  obtain ⟨p', hp'⟩ := μ.tot j p
  obtain ⟨z, hz⟩ := hB j p p' hp'
  refine ⟨p' * N'.qTriv _ (-z), (μ.eqv _ p p p' _ hp' ((N.qEq_equivalence _).refl p)).2
    ((N'.qEq_iff _ _).2 ⟨-z, rfl⟩), ?_⟩
  change p'.1.1.toAdd + n ^ j • (-z) = _
  rw [hz, smul_neg, add_neg_cancel_right]

theorem r_unique {k : ℕ} (hk : k ≠ 0) {p : N.QT k} {a b : N'.QT k} (ha : μ.r k p a) (hb : μ.r k p b)
    (hy : a.1.1 = b.1.1) : a = b :=
  eq_of_qEq hk ((μ.eqv _ p p a b ha ((N.qEq_equivalence _).refl p)).1 hb) hy

theorem r_of_tr_zero (hB : μ.B J.e) (hG : μ.OnG J) {j : ℕ} {p : N.QT (n ^ j)} {a : N'.QT (n ^ j)}
    (hp : p.1.1 = 1) (ha : TR J p a) : μ.r (n ^ j) p a := by
  obtain ⟨p', h1, h2⟩ := exists_norm μ J hB j p
  have h3 : p'.1.1 = 1 := by
    rw [hp, toAdd_one, map_zero] at h2
    exact h2
  rw [tr_unique J ha ⟨h2, hG j p p' h1 hp h3⟩]
  exact h1

theorem exists_pre_zero (hA : μ.A) (hG : μ.OnG J) {j : ℕ} {a : N'.QT (n ^ j)} (ha : a.1.1 = 1) :
    ∃ p, μ.r (n ^ j) p a ∧ TR J p a := by
  obtain ⟨p₀, h₀⟩ := μ.cotot j a
  obtain ⟨z, hz⟩ := (hA.2 j p₀ a h₀).1.2 ⟨0, by rw [ha]; simp⟩
  have h1 : μ.r (n ^ j) (p₀ * N.qTriv _ (-z)) a :=
    (μ.eqv _ p₀ _ a a h₀ ((N.qEq_iff _ _).2 ⟨-z, rfl⟩)).2 ((N'.qEq_equivalence _).refl a)
  have h2 : (p₀ * N.qTriv _ (-z)).1.1 = 1 := by
    change p₀.1.1.toAdd + n ^ j • (-z) = 0
    rw [hz, smul_neg, add_neg_cancel]
  refine ⟨_, h1, ?_, hG j _ _ h1 h2 ha⟩
  rw [h2, ha, toAdd_one, toAdd_one, map_zero]

def Defect (k : ℕ) (x : N.X) (d : N'.QT k) : Prop :=
  d.1.1 = 1 ∧ d.1.2.b = 1 ∧ ∀ p a, p.1.1.toAdd = x → TR J p a → μ.r k p (a * d)

theorem exists_defect [IsAlgClosed C] {g g' : ℕ} (hn : (n : C) ≠ 0) (hT : N.Tors n g) (hT' : N'.Tors n g')
    (hA : μ.A) (hB : μ.B J.e) (hG : μ.OnG J) (j : ℕ) (x : N.X) : ∃ d, Defect μ J (n ^ j) x d := by
  have hn0 : n ^ j ≠ 0 := pow_ne_zero _ (by rintro rfl; simp at hn)
  obtain ⟨p₀, hp₀⟩ := (GlobalTheory.Ex.QStr.qStructure C N n g hn hT j).2.2.1 x
  obtain ⟨p', h1, h2⟩ := exists_norm μ J hB j p₀
  obtain ⟨a₀, ha₀⟩ := tr_exists J p₀
  have e : p' = a₀ * (p' / a₀) := by simp
  have hd : (p' / a₀).1.1 = 1 := by
    change p'.1.1.toAdd - a₀.1.1.toAdd = 0
    rw [h2, ha₀.1, sub_self]
  refine ⟨p' / a₀, hd, ?_, fun p a hp ha => ?_⟩
  · obtain ⟨d₀, q1, q2, q3⟩ := ((GlobalTheory.Ex.QStr.qStructure C N' n g' hn hT' j).2.2.2.2.1 (p' / a₀)).1 fun q' hq' => by
      obtain ⟨q, r1, r2⟩ := exists_pre_zero μ J hA hG hq'
      have w1 := μ.wp _ _ _ _ _ h1 r1
      rw [e, wp_mul_left, tr_wp J ha₀ r2] at w1
      exact mul_eq_left.1 w1
    rw [eq_of_qEq hn0 q1 (hd.trans q2.symm)]
    exact q3
  · obtain ⟨u, hu⟩ := tr_exists J (p / p₀)
    have h3 : (p / p₀).1.1 = 1 := by
      change p.1.1.toAdd - p₀.1.1.toAdd = 0
      rw [hp, hp₀, sub_self]
    have h4 := μ.mul _ _ _ _ _ h1 (r_of_tr_zero μ J hB hG h3 hu)
    have h5 := tr_mul J ha₀ hu
    rw [mul_div_cancel] at h4 h5
    rw [tr_unique J ha h5, mul_right_comm, ← e]
    exact h4

theorem defect_add {k : ℕ} (hk : k ≠ 0) {x x' : N.X} (p p' : N.QT k) (hp : p.1.1.toAdd = x)
    (hp' : p'.1.1.toAdd = x') {d d' d'' : N'.QT k}
    (h : Defect μ J k x d) (h' : Defect μ J k x' d') (h'' : Defect μ J k (x + x') d'') : d'' = d * d' := by
  obtain ⟨a, ha⟩ := tr_exists J p
  obtain ⟨a', ha'⟩ := tr_exists J p'
  have h1 := μ.mul _ _ _ _ _ (h.2.2 p a hp ha) (h'.2.2 p' a' hp' ha')
  rw [mul_mul_mul_comm] at h1
  have h2 := h''.2.2 (p * p') (a * a') (by rw [← hp, ← hp']; rfl) (tr_mul J ha ha')
  refine mul_left_cancel (r_unique μ hk h2 h1 ?_)
  change a.1.1 * a'.1.1 * d''.1.1 = a.1.1 * a'.1.1 * (d.1.1 * d'.1.1)
  rw [h.1, h'.1, h''.1, mul_one (1 : Multiplicative N'.X)]

theorem defect_symm {k : ℕ} {x x' : N.X} (p p' : N.QT k) (hp : p.1.1.toAdd = x)
    (hp' : p'.1.1.toAdd = x') {d d' : N'.QT k}
    (h : Defect μ J k x d) (h' : Defect μ J k x' d') : d.1.2.s (J.e x') = d'.1.2.s (J.e x) := by
  obtain ⟨a, ha⟩ := tr_exists J p
  obtain ⟨a', ha'⟩ := tr_exists J p'
  have h1 := μ.wp _ _ _ _ _ (h.2.2 p a hp ha) (h'.2.2 p' a' hp' ha')
  rw [wp_mul_left, wp_mul_right, tr_wp J ha ha', mul_assoc, mul_eq_left, N'.wp_swap, wp_tor h'.1 h'.2.1,
    wp_tor h.1 h.2.1, inv_mul_eq_one] at h1
  have e : (a' * d').1.1.toAdd = J.e x' := by
    change (a'.1.1 * d'.1.1).toAdd = _
    rw [h'.1, mul_one, ha'.1, hp']
  rw [← e, ← h1, ha.1, hp]

end Level

theorem exists_good {C : Type} [NormedField C] [IsAlgClosed C] {N : NumD C} {n g : ℕ} (hn : (n : C) ≠ 0)
    (hT : N.Tors n g) {j : ℕ} (hj : j ≠ 0) (x : N.X) :
    ∃ p : N.QT ((n ^ j) ^ 2), p.1.1.toAdd = x ∧ ‖N.th (p.1.2.b ^ n ^ j)‖ = 1 := by
  have hn0 : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (by rintro rfl; simp at hn))
  have root : ∀ (i : ℕ) (a : N.A), ∃ b, b ^ n ^ i = a := by
    intro i
    induction i with
    | zero => exact fun a => ⟨a, by simp⟩
    | succ i ih =>
      intro a
      obtain ⟨b, rfl⟩ := hT.div a
      obtain ⟨b', rfl⟩ := ih b
      exact ⟨b', by rw [pow_succ, pow_mul]⟩
  obtain ⟨a, ha⟩ := root j (N.c x)
  obtain ⟨t, ht, hth⟩ := hT.good a
  obtain ⟨b, hb⟩ := root j (a * t)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.Ex.QStr.qStructure C N n g hn hT j).1 b
  have ht' : t ^ n ^ j = 1 := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [pow_succ', pow_mul, ht, one_pow]
  obtain ⟨u, hu⟩ := (N.exists_tor_iff (N.io x * (γ ^ (n ^ j) ^ 2)⁻¹)).2 (by
    rw [NumD.Gt.mul_b, NumD.Gt.inv_b, NumD.Gt.pow_b, hγ, sq, pow_mul, hb, mul_pow, ht', ha, mul_one, N.io_b,
      mul_inv_cancel])
  obtain ⟨v, hv⟩ := exists_char_root u hn0
  refine ⟨⟨(Multiplicative.ofAdd x, N.tor v * γ), ?_⟩, rfl, ?_⟩
  · rw [N.mem_QT, mul_pow, ← N.tor_pow, hv, hu, inv_mul_cancel_right]
    rfl
  · change ‖N.th ((1 * γ.b) ^ n ^ j)‖ = 1
    rw [one_mul, hγ, hb, hth]

theorem tendsto_txT {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ} (hI : N.Int q) {m : ℕ}
    (hm : Odd m) (p : N.QT (m ^ 2)) : Filter.Tendsto (N.txT m p) Filter.cofinite (nhds 0) := by
  have hm0 : 0 < m := hm.pos
  have h1 := hI.pos.comp (TorsionFourier.add_nsmul_injective hm0 p.1.1.toAdd).tendsto_cofinite
  have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (h1.atTop_div_const (r := (m : ℝ) ^ 2) (by positivity))
  refine squeeze_zero_norm (fun χ => ?_) h2
  rw [(GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 m hm p χ]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hI.th _)

theorem norm_char {C X : Type} [NormedField C] [AddCommGroup X] {k : ℕ} (hk : k ≠ 0) {t : Multiplicative X →* Cˣ}
    (ht : t ^ k = 1) (x : Multiplicative X) : ‖(t x : C)‖ = 1 := by
  have h1 : ‖(t x : C)‖ ^ k = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, TorsionFourier.apply_pow_eq_one ht, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk).1 h1

theorem eq_one_of_sums {C X : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [IsAlgClosed C] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {m : ℕ} (hm : ‖(m : C)‖ = 1)
    (T : X → C) (hT : Filter.Tendsto T Filter.cofinite (nhds 0)) (h0 : T 0 ≠ 0)
    (hdom : ∀ z, z ≠ 0 → ‖T (m • z)‖ < ‖T 0‖) (w : C) (τ : Multiplicative X →* Cˣ) (hτ : τ ^ m = 1)
    (h : ∀ u : Multiplicative X →* Cˣ, u ^ m = 1 →
      ∑' χ, w * (τ (Multiplicative.ofAdd χ) : C) * T χ * (u (Multiplicative.ofAdd χ) : C) =
        ∑' χ, T χ * (u (Multiplicative.ofAdd χ) : C)) : w = 1 := by
  have hmC : (m : C) ≠ 0 := by
    intro h; rw [h, norm_zero] at hm; exact zero_ne_one hm
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmC
  haveI : NeZero (m : C) := ⟨hmC⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C m
  have hT' : Filter.Tendsto (fun χ => w * (τ (Multiplicative.ofAdd χ) : C) * T χ) Filter.cofinite (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hT ⊢
    simpa only [norm_mul, norm_char hm0 hτ, mul_one, mul_zero] using hT.const_mul ‖w‖
  obtain ⟨-, a1, a2⟩ := fourier_extraction_tsum_class C X m ζ (Nat.pos_of_ne_zero hm0) hm hζ T hT 0
  obtain ⟨-, b1, -⟩ := fourier_extraction_tsum_class C X m ζ (Nat.pos_of_ne_zero hm0) hm hζ _ hT' 0
  simp only [zero_add] at a1 a2 b1
  rw [finsum_congr fun u => by rw [h u.1 u.2], a1] at b1
  have e : ∀ z : X, (τ (Multiplicative.ofAdd (m • z)) : C) = 1 := fun z => by
    rw [ofAdd_nsmul, map_pow, TorsionFourier.apply_pow_eq_one hτ, Units.val_one]
  simp only [e, mul_one, tsum_mul_left] at b1
  have b2 := mul_left_cancel₀ (pow_ne_zero _ hmC) b1
  have hS : ∑' z, T (m • z) ≠ 0 := by
    rw [← norm_ne_zero_iff, a2 hdom, norm_ne_zero_iff]; exact h0
  exact (mul_eq_right₀ hS).1 b2.symm

theorem defect_diag {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    {N N' : NumD C} {q : QuadraticMap ℤ N.X ℝ} {n g : ℕ} (ho : Odd n) (hn : ‖(n : C)‖ = 1) (hI : N.Int q)
    (hT : N.Tors n g) (μ : Match N N' n) (J : NumD.Iso N N') (hl : (J.lam : C) = μ.c₀) {j : ℕ} (hj : j ≠ 0)
    {x : N.X} (hx : ∀ z, z ≠ 0 → q x < q (x + (n ^ j) ^ 2 • z)) {d : N'.QT ((n ^ j) ^ 2)}
    (hd : Defect μ J ((n ^ j) ^ 2) x d) : d.1.2.s (J.e x) ^ (((n ^ j) ^ 2 - 1) / 2 + 1) = 1 := by
  have hnC : (n : C) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  obtain ⟨p, hp, hth⟩ := exists_good hnC hT hj x
  have htx := μ.tx j
  have hmn : ‖((n ^ j : ℕ) : C)‖ = 1 := by rw [Nat.cast_pow, norm_pow, hn, one_pow]
  have hm : Odd (n ^ j) := ho.pow
  generalize n ^ j = m at *
  have hm0 : m ≠ 0 := hm.pos.ne'
  obtain ⟨t', ht'⟩ := (N'.exists_tor_iff d.1.2).2 hd.2.1
  have ht'k : t' ^ m ^ 2 = 1 := by
    apply N'.tor_injective
    rw [N'.tor_pow, ht', N'.mem_QT.1 d.2, hd.1, toAdd_one, N'.io_zero, N'.tor_one]
  let τ : Multiplicative N.X →* Cˣ := (t'.comp (AddMonoidHom.toMultiplicative J.e.toAddMonoidHom)) ^ m
  have hτ : ∀ χ, τ (Multiplicative.ofAdd χ) = t' (Multiplicative.ofAdd (J.e χ)) ^ m := fun _ => rfl
  have hτm : τ ^ m = 1 := MonoidHom.ext fun χ => by
    change (t' (Multiplicative.ofAdd (J.e χ.toAdd)) ^ m) ^ m = 1
    rw [← pow_mul, ← sq, TorsionFourier.apply_pow_eq_one ht'k]
  have hnorm := (GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 m hm p
  have h00 : ‖N.txT m p 0‖ = Real.exp (-(q x / (m : ℝ) ^ 2)) := by
    rw [hnorm, N.c_zero, one_mul, hth, mul_one, smul_zero, add_zero, hp]
  rw [← ht', NumD.torus_generator_apply]
  apply Units.ext
  rw [Units.val_one]
  refine eq_one_of_sums hmn (N.txT m p) (tendsto_txT hI hm p) ?_ (fun z hz => ?_) _ τ hτm fun u hu => ?_
  · rw [← norm_pos_iff, h00]; exact Real.exp_pos _
  · rw [h00, hnorm, hp, smul_smul, ← sq]
    refine (mul_le_of_le_one_right (Real.exp_pos _).le (hI.th _)).trans_lt (Real.exp_lt_exp.2 (neg_lt_neg ?_))
    exact div_lt_div_of_pos_right (hx z hz) (by positivity)
  · obtain ⟨t, rfl⟩ := exists_char_root u hm0
    have ht : t ^ m ^ 2 = 1 := by rw [sq, pow_mul, hu]
    obtain ⟨a, ha⟩ := tr_exists J (p * N.qTor t ht)
    have hpx : (p * N.qTor t ht).1.1 = p.1.1 := mul_one _
    have h1 := htx _ _ (hd.2.2 _ a (by rw [hpx, hp]) ha)
    have hay : a.1.1 = Multiplicative.ofAdd (J.e x) := by
      rw [← hp, ← hpx, ← ha.1]; rfl
    have hpy : p.1.1 = Multiplicative.ofAdd x := by rw [← hp]; rfl
    have h2 : ∀ χ, N.txT m (p * N.qTor t ht) χ = (t (Multiplicative.ofAdd x) ^ ((m ^ 2 - 1) / 2 + 1) : Cˣ) *
        (N.txT m p χ * ((t ^ m) (Multiplicative.ofAdd χ) : C)) := fun χ => by
      rw [(GlobalTheory.Ex.txT_shift C N m hm p (p * N.qTor t ht) χ).2 t hpx rfl, hpy, toAdd_ofAdd, ofAdd_add, ofAdd_nsmul,
        map_mul, map_pow, MonoidHom.pow_apply]
      push_cast
      ring
    have h3 : ∀ χ, N'.txT m (a * d) (J.e χ) = μ.c₀ * ((t (Multiplicative.ofAdd x) ^ ((m ^ 2 - 1) / 2 + 1) : Cˣ) *
        (((t' (Multiplicative.ofAdd (J.e x)) ^ ((m ^ 2 - 1) / 2 + 1) : Cˣ) : C) * (τ (Multiplicative.ofAdd χ) : C) *
          N.txT m p χ * ((t ^ m) (Multiplicative.ofAdd χ) : C))) := fun χ => by
      rw [(GlobalTheory.Ex.txT_shift C N' m hm a (a * d) (J.e χ)).2 t' (by change a.1.1 * d.1.1 = _; rw [hd.1, mul_one])
        (by rw [ht']; rfl), tr_txT J hm ha, h2, hl, hay, toAdd_ofAdd, ofAdd_add, ofAdd_nsmul,
        map_mul, map_pow, hτ]
      push_cast
      ring
    rw [NumD.tx, NumD.tx, ← J.e.toEquiv.tsum_eq] at h1
    simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, h2, h3, tsum_mul_left] at h1
    exact mul_left_cancel₀ (Units.ne_zero _) (mul_left_cancel₀ μ.c₀_ne h1)

theorem main : AllMatch fun {_} _ {N} {N'} {_} μ _ _ =>
    μ.A → ∀ J : NumD.Iso N N', μ.B J.e → μ.OnG J → (J.lam : _) = μ.c₀ → μ.OnQ J := by
  intro C _ _ _ _ N N' q q' n g g' hp ho hn hI _ hT hT' μ hA J hB hG hl i p p' h1 h2
  have hnC : (n : C) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  have hn0 : n ≠ 0 := hp.ne_zero
  obtain ⟨j₀, hj₀⟩ := pow_unbounded_of_one_lt
    (1 + 4 * (Module.finrank ℤ N.X : ℝ) * (2 : ℝ) ^ ((Module.finrank ℤ N.X : ℝ) / 2))
    (show (1 : ℝ) < n by exact_mod_cast hp.one_lt)
  set j := i + j₀ + 1 with hj
  have hk : (n ^ j) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hn0)
  obtain ⟨e, he⟩ := exists_basis_unique_min_pair_sums N.X q hI.pos _ _ ((n ^ j) ^ 2) rfl le_rfl
    (hj₀.trans_le (by
      rw [← pow_mul, Nat.cast_pow]
      exact pow_le_pow_right₀ (by exact_mod_cast hp.one_le) (by omega)))
  have hd : ∀ x, ∃ d, Defect μ J ((n ^ j) ^ 2) x d := by
    rw [← pow_mul]; exact exists_defect μ J hnC hT hT' hA hB hG _
  have hs : ∀ x, ∃ s : N.QT ((n ^ j) ^ 2), s.1.1.toAdd = x := fun x =>
    (exists_good hnC hT (Nat.succ_ne_zero _) x).imp fun _ h => h.1
  choose d hd using hd
  choose s hs using hs
  have hodd : Odd ((n ^ j) ^ 2) := ho.pow.pow
  have key := symm_pairing_eq_one_of_odd_of_diag N.X Cˣ _ ((n ^ j) ^ 2) e
    ((((n ^ j) ^ 2 - 1) / 2 + 1 : ℕ) : ℤ) hodd
    (by
      obtain ⟨c, hc⟩ := hodd
      rw [hc]
      exact ⟨1, by omega⟩)
    (fun x y => (d x).1.2.s (J.e y))
    (fun x x' y => by
      rw [defect_add μ J hk (s x) (s x') (hs x) (hs x') (hd x) (hd x') (hd (x + x'))]
      change ((d x).1.2 * (d x').1.2).s _ = _
      rw [NumD.Gt.mul_s, (hd x').2.1, N'.cub.face₃, div_one])
    (fun x y => defect_symm μ J (s x) (s y) (hs x) (hs y) (hd x) (hd y))
    (fun x y => by
      obtain ⟨a, ha⟩ := tr_exists J (s y)
      have := (GlobalTheory.T.degenerationWeilPairing_properties _ N' _ (d x) a a).2.2.2.1
      rwa [wp_tor (hd x).1 (hd x).2.1, ha.1, hs] at this)
    (fun a => by
      rw [zpow_natCast]
      exact defect_diag ho hn hI hT μ J hl (Nat.succ_ne_zero _) (fun z hz => (he a a z hz).1) (hd _))
    (fun a b => by
      rw [zpow_natCast]
      exact defect_diag ho hn hI hT μ J hl (Nat.succ_ne_zero _) (fun z hz => (he a b z hz).2) (hd _))
  have hd1 : ∀ x, d x = 1 := fun x =>
    Subtype.ext (Prod.ext (hd x).1 (NumD.Gt.ext (hd x).2.1 (funext fun χ => by
      have := key x (J.e.symm χ)
      rwa [AddEquiv.apply_symm_apply] at this)))
  have top : ∀ (a : N.QT ((n ^ j) ^ 2)) (a' : N'.QT ((n ^ j) ^ 2)), TR J a a' → μ.r _ a a' := fun a a' h => by
    have := (hd _).2.2 a a' rfl h
    rwa [hd1, mul_one] at this
  have hkk : (n ^ j) ^ 2 = n ^ i * n ^ (i + 2 * j₀ + 2) := by rw [hj]; ring
  rw [hkk] at top
  generalize hk' : n ^ (i + 2 * j₀ + 2) = k' at top
  have hk'0 : k' ≠ 0 := hk' ▸ pow_ne_zero _ hn0
  let a : N.QT (n ^ i * k') := ⟨(p.1.1 ^ k', p.1.2), by
    rw [N.mem_QT, pow_mul, N.mem_QT.1 p.2, toAdd_pow, N.io_nsmul]⟩
  let a' : N'.QT (n ^ i * k') := ⟨(p'.1.1 ^ k', p'.1.2), by
    rw [N'.mem_QT, pow_mul, N'.mem_QT.1 p'.2, toAdd_pow, N'.io_nsmul]⟩
  refine (μ.incl _ k' p p' a a' hk'0 rfl rfl rfl rfl).2 (top a a' ⟨?_, h2⟩)
  change (p'.1.1 ^ k').toAdd = J.e (p.1.1 ^ k').toAdd
  rw [toAdd_pow, toAdd_pow, map_nsmul, h1]

end GlobalTheory.LabelsAgree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLabelsAgreeOfIsoStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRecognition_labels_agree_of_iso : AllMatch fun {_} _ {N} {N'} {_} μ _ _ => μ.A → ∀ J : NumD.Iso N N', μ.B J.e → μ.OnG J → (J.lam : _) = μ.c₀ → μ.OnQ J := by
  first | exact @GlobalTheory.LabelsAgree.main | exact GlobalTheory.LabelsAgree.main | (intros; apply GlobalTheory.LabelsAgree.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationRecognitionOfAbelianPartsIsoLabels
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.Recognition

theorem urec_of_abelian : UrCSt → URecSt := by
  intro hC R _ _ D D' h1 h2 h3 h4 C _ _ _ _ _ N N' ν ν' q q' n hp ho hn hi hi' ht ht' mt
  obtain ⟨hA, hg⟩ := GlobalTheory.T.thetaRecognition_matched_parts_dim_eq C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt
  obtain ⟨e, hB, hT⟩ := GlobalTheory.T.thetaRecognition_lattice_iso_and_terms_agree C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt hA
  obtain ⟨I, hOB, hl, hG⟩ := hC R D D' h1 h2 h3 h4 C N N' ν ν' q q' n hp ho hn hi hi' ht ht' mt hA hg e hB hT
  obtain ⟨J, hJ, hJe, hOG⟩ := GlobalTheory.T.exists_numD_iso_onG_of_allMatch C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt hA e hB hT I hOB
  subst hJ hJe
  exact ⟨J, GlobalTheory.T.thetaRecognition_labels_agree_of_iso C N N' q q' n _ _ hp ho hn hi hi' ht ht' mt hA J hB hOG hl, hG⟩
end GlobalTheory.Ex.Recognition
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationRecognitionOfAbelianPartsIsoLabelsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationRecognition_of_abelianPartsIsoLabels : UrCSt → URecSt := by
  first | exact @GlobalTheory.Ex.Recognition.urec_of_abelian | exact GlobalTheory.Ex.Recognition.urec_of_abelian | (intros; apply GlobalTheory.Ex.Recognition.urec_of_abelian <;> assumption)
end
