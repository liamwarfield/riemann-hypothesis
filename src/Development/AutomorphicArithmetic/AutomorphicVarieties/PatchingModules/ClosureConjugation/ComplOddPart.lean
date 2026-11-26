module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.VrReduction
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.vr_reduction :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) {F : Type} [CommRing F] [Algebra B F] (r : E →ₐ[B] Matrix ι ι F) (p q : ι), (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (o i) i 1) → (∀ y i j, o i ≠ o j → r y i j = 0) → (∀ y i j, algebraMap B F (U.vr p q y i j).ev = r y i j) ∧ (o p = p → o q = q → p ≠ q → (U.oddForm p q).red ≤ RingHom.ker (algebraMap B F)) := by
  intro B E _ _ _ T ι _ _ o U F _ _ r p q hst hx hr
  obtain ⟨-, -, h3, h4, h5, -, h7⟩ := units_basic T o U
  have hep : ∀ k, r (U.ep (o k)) = Matrix.single (o k) (o k) 1 := by
    intro k
    rw [← U.x_base k, hx, U.o_o]
  have hz : ∀ w i j, r (U.x i * w * T.st (U.x j)) = Matrix.single (o i) (o j) (r w i j) := by
    intro w i j
    rw [map_mul, map_mul, hst, hx, hx, Matrix.transpose_single, Matrix.single_mul_mul_single, one_mul, mul_one]
  have key : ∀ w i j, algebraMap B F (T.tr (U.x i * w * T.st (U.x j))) = r w i j := by
    intro w i j
    by_cases hij : o i = o j
    · have e := congrArg (fun M => M (o i) (o j)) (hz w i j)
      simp only [Matrix.single_apply_same] at e
      rw [← e]
      conv_rhs => rw [h5 i j w hij, map_smul, hep i, ← hij]
      simp [Matrix.smul_apply, Algebra.smul_def]
    · rw [hr w i j hij, ← h7 i j w, h3 _ _ _ hij, map_zero]
  refine ⟨fun y i j => ?_, ?_⟩
  · show algebraMap B F (T.tr (U.x i * y * T.st (U.x j))) = _
    exact key y i j
  · intro hp hq hpq
    refine Ideal.span_le.mpr ?_
    rintro c ⟨b, b', rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show algebraMap B F (T.tr ((b : E) * T.st (b' : E))) = 0
    obtain ⟨z, hz'⟩ := b.2
    have hb : r (b : E) = 0 := by
      rw [← hz']
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, map_mul]
      have hpp := hep p
      rw [hp] at hpp
      have hqq := hep q
      rw [hq] at hqq
      rw [hpp, hqq, ← mul_assoc, Matrix.single_mul_mul_single, hr z p q (by rw [hp, hq]; exact hpq)]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h4, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [key, map_mul, hb, zero_mul, Matrix.zero_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.VrRange
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

section aux

variable {B E : Type} [CommRing B] [Ring E] [Algebra B E] {T : TrInv B E} {ι : Type} [Fintype ι] [DecidableEq ι]
  {o : ι → ι} (U : T.Units ι o) (p q : ι)

private noncomputable def vrEnt (w : E) : (U.oddForm p q).Ext :=
  (U.oddForm p q).el (T.tr w)
    (cornerProj B (U.ep p) (U.ep q) w + cornerProj B (U.ep p) (U.ep q) (T.st w))

private noncomputable def vrRec (a b : ι) (z : (U.oddForm p q).Ext) : E :=
  if a = b then z.ev • U.ep a else if a = p then z.od.1 else T.st z.od.1

omit [DecidableEq ι] in
private theorem vrEnt_od (w : E) :
    (vrEnt U p q w).od.1 = U.ep p * w * U.ep q + U.ep p * T.st w * U.ep q := by
  simp only [mul_assoc]; rfl

omit [DecidableEq ι] in
private theorem vrEnt_ev (w : E) : (vrEnt U p q w).ev = T.tr w := rfl

omit [DecidableEq ι] in
private theorem sand (a b c d : ι) (w : E) (hw : U.ep a * w * U.ep b = w) (h : c ≠ a ∨ b ≠ d) :
    U.ep c * w * U.ep d = 0 := by
  rw [← hw]
  simp only [mul_assoc]
  rcases h with h | h
  · rw [← mul_assoc (U.ep c), U.coi.ortho h, zero_mul]
  · rw [U.coi.ortho h, mul_zero, mul_zero, mul_zero]

omit [DecidableEq ι] in
private theorem sand_st (a b : ι) (w : E) (hw : U.ep a * w * U.ep b = w) :
    U.ep b * T.st w * U.ep a = T.st w := by
  conv_rhs => rw [← hw]
  rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]

private theorem ent_spec (hpq : p ≠ q) (a b : ι) (ha : a = p ∨ a = q) (hb : b = p ∨ b = q) (w : E)
    (hw : U.ep a * w * U.ep b = w) :
    ((a = b → (vrEnt U p q w).od = 0) ∧ (a ≠ b → (vrEnt U p q w).ev = 0)) ∧
      vrRec U p q a b (vrEnt U p q w) = w := by
  have hst := sand_st U a b w hw
  refine ⟨⟨fun hab => ?_, fun hab => ?_⟩, ?_⟩
  · rw [← hab] at hw hst
    have h1 : p ≠ a ∨ a ≠ q := by
      rcases ha with h | h
      · exact Or.inr (fun h' => hpq (h.symm.trans h'))
      · exact Or.inl (fun h' => hpq (h'.trans h))
    apply Subtype.ext
    rw [vrEnt_od, sand U a a p q w hw h1, sand U a a p q (T.st w) hst h1, add_zero]
    rfl
  · rw [vrEnt_ev, ← hw]
    exact (units_basic T o U).2.2.1 a b w hab
  · unfold vrRec
    split_ifs with h1 h2
    · rw [← h1] at hw
      rw [vrEnt_ev]
      conv_rhs => rw [← hw, U.corner_eq, hw]
    · have hb' : b = q := hb.resolve_left (fun h => h1 (h2.trans h.symm))
      rw [h2, hb'] at hw hst
      rw [vrEnt_od, hw, sand U q p p q (T.st w) hst (Or.inl hpq), add_zero]
    · have ha' : a = q := ha.resolve_left h2
      have hb' : b = p := hb.resolve_right (fun h => h1 (ha'.trans h.symm))
      rw [ha', hb'] at hw hst
      rw [vrEnt_od, sand U q p p q w hw (Or.inl hpq), zero_add, hst, T.st_st]

private theorem rec_spec (hpq : p ≠ q) (a b : ι) (ha : a = p ∨ a = q) (hb : b = p ∨ b = q)
    (z : (U.oddForm p q).Ext) (hz : (a = b → z.od = 0) ∧ (a ≠ b → z.ev = 0)) :
    U.ep a * vrRec U p q a b z * U.ep b = vrRec U p q a b z ∧ vrEnt U p q (vrRec U p q a b z) = z := by
  have hid : ∀ i, U.ep i * U.ep i = U.ep i := fun i => (U.coi.idem i).eq
  have hmem : U.ep p * (z.od : E) * U.ep q = z.od := by
    obtain ⟨y, hy⟩ := z.od.2
    rw [← hy]
    show U.ep p * (U.ep p * (y * U.ep q)) * U.ep q = U.ep p * (y * U.ep q)
    rw [← mul_assoc (U.ep p) (U.ep p), hid, mul_assoc, mul_assoc, hid]
  have hoff : U.ep p * T.st (z.od : E) * U.ep q = 0 :=
    sand U q p p q _ (sand_st U p q _ hmem) (Or.inl hpq)
  unfold vrRec
  split_ifs with h1 h2
  · have hod := hz.1 h1
    have hpa : U.ep p * U.ep a * U.ep q = 0 := by
      rcases ha with h | h
      · rw [h, hid, U.coi.ortho hpq]
      · rw [h, U.coi.ortho hpq, zero_mul]
    refine ⟨?_, ?_⟩
    · rw [← h1, mul_smul_comm, smul_mul_assoc, hid, hid]
    · apply Prod.ext
      · change (vrEnt U p q (z.ev • U.ep a)).ev = z.ev
        rw [vrEnt_ev, map_smul, U.tr_ep, smul_eq_mul, mul_one]
      · change (vrEnt U p q (z.ev • U.ep a)).od = z.od
        apply Subtype.ext
        rw [vrEnt_od, hod, map_smul, U.st_ep]
        simp only [mul_smul_comm, smul_mul_assoc, hpa, smul_zero, add_zero]
        rfl
  · have hb' : b = q := hb.resolve_left (fun h => h1 (h2.trans h.symm))
    have hev := hz.2 h1
    rw [h2, hb']
    refine ⟨hmem, ?_⟩
    apply Prod.ext
    · change (vrEnt U p q (z.od : E)).ev = z.ev
      rw [vrEnt_ev, hev, ← hmem]
      exact (units_basic T o U).2.2.1 p q _ hpq
    · change (vrEnt U p q (z.od : E)).od = z.od
      apply Subtype.ext
      rw [vrEnt_od, hmem, hoff, add_zero]
  · have ha' : a = q := ha.resolve_left h2
    have hb' : b = p := hb.resolve_right (fun h => h1 (ha'.trans h.symm))
    have hev := hz.2 h1
    rw [ha', hb']
    refine ⟨sand_st U p q _ hmem, ?_⟩
    apply Prod.ext
    · change (vrEnt U p q (T.st (z.od : E))).ev = z.ev
      rw [vrEnt_ev, T.tr_st, hev, ← hmem]
      exact (units_basic T o U).2.2.1 p q _ hpq
    · change (vrEnt U p q (T.st (z.od : E))).od = z.od
      apply Subtype.ext
      rw [vrEnt_od, T.st_st, hmem, hoff, zero_add]

end aux

theorem UpperTheory.V.AlgebraTools.vr_range :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p q : ι), p ≠ q → (∀ i, o i = p ∨ o i = q) → Function.Injective (U.vr p q) ∧ ∀ Y : Matrix ι ι (U.oddForm p q).Ext, Y ∈ Set.range (U.vr p q) ↔ ∀ i j, (o i = o j → (Y i j).od = 0) ∧ (o i ≠ o j → (Y i j).ev = 0) := by
  intro B E _ _ _ T ι _ _ o U p q hpq ho
  obtain ⟨hxx, -, -, -, -, hsum, hcor⟩ := units_basic T o U
  have hvr : ∀ w i j, U.vr p q w i j = vrEnt U p q (U.x i * w * T.st (U.x j)) :=
    fun _ _ _ => rfl
  have hrec : ∀ w i j, vrRec U p q (o i) (o j) (U.vr p q w i j) = U.x i * w * T.st (U.x j) := by
    intro w i j
    rw [hvr]
    exact (ent_spec U p q hpq (o i) (o j) (ho i) (ho j) _ (hcor i j w)).2
  have hx : ∀ i k, U.x i * T.st (U.x k) = if i = k then U.ep (o i) else 0 := by
    intro i k
    split_ifs with h
    · rw [h, U.x_st]
    · exact hxx i k h
  refine ⟨fun w w' h => ?_, fun Y => ⟨?_, ?_⟩⟩
  · rw [hsum w, hsum w']
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [← hrec w i j, ← hrec w' i j, h]
  · rintro ⟨w, rfl⟩ i j
    rw [hvr]
    exact (ent_spec U p q hpq (o i) (o j) (ho i) (ho j) _ (hcor i j w)).1
  · intro hY
    refine ⟨∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l, ?_⟩
    refine Matrix.ext (fun i j => ?_)
    rw [hvr]
    have hr := rec_spec U p q hpq (o i) (o j) (ho i) (ho j) (Y i j) (hY i j)
    have key : U.x i * (∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l) *
        T.st (U.x j) = vrRec U p q (o i) (o j) (Y i j) := by
      calc U.x i * (∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l) *
            T.st (U.x j)
          = ∑ k, ∑ l, (U.x i * T.st (U.x k)) * vrRec U p q (o k) (o l) (Y k l) *
              (U.x l * T.st (U.x j)) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        _ = U.ep (o i) * vrRec U p q (o i) (o j) (Y i j) * U.ep (o j) := by
            simp [hx]
        _ = vrRec U p q (o i) (o j) (Y i j) := hr.1
    rw [key]
    exact hr.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ThetaDiag
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

section

variable {B E : Type} [CommRing B] [Ring E] [Algebra B E] {T : TrInv B E} {ι : Type} [Fintype ι]
  {o : ι → ι} (U : T.Units ι o) (p q : ι)

private def theta : E →ₗ[B] (U.oddForm p q).Ext where
  toFun z := (U.oddForm p q).el (T.tr z)
    (cornerProj B (U.ep p) (U.ep q) z + cornerProj B (U.ep p) (U.ep q) (T.st z))
  map_add' z w := by
    apply OddForm.ext
    · simp only [OddForm.ev_add]
      simp only [OddForm.Ext.ev, OddForm.el, map_add]
    · simp only [OddForm.od_add]
      simp only [OddForm.Ext.od, OddForm.el, map_add]; abel
  map_smul' c z := by
    apply OddForm.ext
    · simp only [RingHom.id_apply, OddForm.ev_smul]
      simp only [OddForm.Ext.ev, OddForm.el, map_smul, smul_eq_mul]
    · simp only [RingHom.id_apply, OddForm.od_smul]
      simp only [OddForm.Ext.od, OddForm.el, map_smul, smul_add]

private theorem theta_ev (z : E) : (theta U p q z).ev = T.tr z := rfl

private theorem theta_od (z : E) :
    (theta U p q z).od.1 = U.ep p * (z * U.ep q) + U.ep p * (T.st z * U.ep q) := rfl

private theorem theta_st (z : E) : theta U p q (T.st z) = theta U p q z := by
  apply OddForm.ext
  · rw [theta_ev, theta_ev, T.tr_st]
  · apply Subtype.ext
    rw [theta_od, theta_od, T.st_st, add_comm]

variable {p q}

private theorem theta_ep (hpq : p ≠ q) {a : ι} (ha : a = p ∨ a = q) : theta U p q (U.ep a) = 1 := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  apply OddForm.ext
  · rw [theta_ev, OddForm.ev_one, U.tr_ep]
  · apply Subtype.ext
    rw [theta_od, U.st_ep, OddForm.od_one]
    rcases ha with h | h
    · rw [h, ← mul_assoc, (U.coi.idem p).eq, hpq0]
      simp
    · rw [h, (U.coi.idem q).eq, hpq0]
      simp

private theorem theta_diag (hpq : p ≠ q) {a : ι} (ha : a = p ∨ a = q) {u : E}
    (hu : U.ep a * u * U.ep a = u) : theta U p q u = T.tr u • 1 := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  have hsu : U.ep a * T.st u * U.ep a = T.st u := by
    conv_rhs => rw [← hu]
    rw [T.st_mul, T.st_mul, U.st_ep, mul_assoc]
  have L1 : ∀ w : E, U.ep p * w * U.ep p = w → U.ep p * (w * U.ep q) = 0 := by
    intro w hw
    rw [← hw]
    simp [mul_assoc, hpq0]
  have L2 : ∀ w : E, U.ep q * w * U.ep q = w → U.ep p * (w * U.ep q) = 0 := by
    intro w hw
    rw [← hw]
    simp only [mul_assoc]
    rw [← mul_assoc (U.ep p), hpq0, zero_mul]
  apply OddForm.ext
  · rw [theta_ev, OddForm.ev_smul, OddForm.ev_one, mul_one]
  · apply Subtype.ext
    rw [theta_od, OddForm.od_smul, OddForm.od_one, smul_zero]
    rcases ha with h | h
    · rw [h] at hu hsu
      rw [L1 u hu, L1 _ hsu]
      simp
    · rw [h] at hu hsu
      rw [L2 u hu, L2 _ hsu]
      simp

private theorem theta_pq (hpq : p ≠ q) {u : E} (hu : U.ep p * u * U.ep q = u) :
    (theta U p q u).ev = 0 ∧ (theta U p q u).od.1 = u := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  have hqp0 : U.ep q * U.ep p = 0 := U.coi.ortho hpq.symm
  have hsu : U.ep q * T.st u * U.ep p = T.st u := by
    conv_rhs => rw [← hu]
    rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [theta_ev, ← hu, T.tr_comm, ← mul_assoc, hqp0, zero_mul, map_zero]
  · have h0 : U.ep p * (T.st u * U.ep q) = 0 := by
      rw [← hsu]
      simp [mul_assoc, hpq0]
    rw [theta_od, h0, add_zero, ← mul_assoc, hu]

private theorem theta_qp (hpq : p ≠ q) {u : E} (hu : U.ep q * u * U.ep p = u) :
    (theta U p q u).ev = 0 ∧ (theta U p q u).od.1 = T.st u := by
  have hpq0 : U.ep p * U.ep q = 0 := U.coi.ortho hpq
  have hqp0 : U.ep q * U.ep p = 0 := U.coi.ortho hpq.symm
  have hsu : U.ep p * T.st u * U.ep q = T.st u := by
    conv_rhs => rw [← hu]
    rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [theta_ev, ← hu, T.tr_comm, ← mul_assoc, hpq0, zero_mul, map_zero]
  · have h0 : U.ep p * (u * U.ep q) = 0 := by
      rw [← hu]
      simp [mul_assoc, hpq0]
    rw [theta_od, h0, zero_add, ← mul_assoc, hsu]

private theorem theta_mul (hpq : p ≠ q) {a b c : ι} (ha : a = p ∨ a = q) (hb : b = p ∨ b = q)
    (hc : c = p ∨ c = q) {u v : E} (hu : U.ep a * u * U.ep b = u) (hv : U.ep b * v * U.ep c = v) :
    theta U p q (u * v) = theta U p q u * theta U p q v := by
  have hidem : ∀ i, U.ep i * U.ep i = U.ep i := fun i => (U.coi.idem i).eq
  have hL : ∀ {i j : ι} {w : E}, U.ep i * w * U.ep j = w → U.ep i * w = w := by
    intro i j w hw
    calc U.ep i * w = U.ep i * (U.ep i * w * U.ep j) := by rw [hw]
      _ = U.ep i * U.ep i * w * U.ep j := by simp only [mul_assoc]
      _ = w := by rw [hidem, hw]
  have hR : ∀ {i j : ι} {w : E}, U.ep i * w * U.ep j = w → w * U.ep j = w := by
    intro i j w hw
    calc w * U.ep j = U.ep i * w * U.ep j * U.ep j := by rw [hw]
      _ = U.ep i * w * (U.ep j * U.ep j) := by simp only [mul_assoc]
      _ = w := by rw [hidem, hw]
  have hsc : ∀ {i : ι} {w : E}, U.ep i * w * U.ep i = w → w = T.tr w • U.ep i := by
    intro i w hw
    have h := U.corner_eq i w
    rwa [hw] at h
  have hbe : ∀ x y, (U.oddForm p q).be x y = T.tr ((x : E) * T.st (y : E)) := fun x y => rfl
  have hleft : ∀ {i k : ι}, (i = p ∨ i = q) → U.ep i * u * U.ep i = u → U.ep i * v * U.ep k = v →
      theta U p q (u * v) = theta U p q u * theta U p q v := by
    intro i k hi hu' hv'
    have huv : u * v = T.tr u • v := by
      conv_lhs => rw [hsc hu', smul_mul_assoc, hL hv']
    rw [huv, map_smul, theta_diag U hpq hi hu', smul_mul_assoc, one_mul]
  have hright : ∀ {i k : ι}, (k = p ∨ k = q) → U.ep k * v * U.ep k = v → U.ep i * u * U.ep k = u →
      theta U p q (u * v) = theta U p q u * theta U p q v := by
    intro i k hk hv' hu'
    have huv : u * v = T.tr v • u := by
      conv_lhs => rw [hsc hv', mul_smul_comm, hR hu']
    rw [huv, map_smul, theta_diag U hpq hk hv', mul_smul_comm, mul_one]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    rw [ha, hb] at hu <;> rw [hb, hc] at hv
  · exact hleft (Or.inl rfl) hu hv
  · exact hleft (Or.inl rfl) hu hv
  · have huv : U.ep p * (u * v) * U.ep p = u * v := by
      rw [← mul_assoc, hL hu, mul_assoc, hR hv]
    rw [theta_diag U hpq (Or.inl rfl) huv]
    obtain ⟨h1, h2⟩ := theta_pq U hpq hu
    obtain ⟨h3, h4⟩ := theta_qp U hpq hv
    apply OddForm.ext
    · rw [OddForm.ev_smul, OddForm.ev_one, mul_one, OddForm.ev_mul, h1, h3, zero_mul, zero_add, hbe, h2, h4, T.st_st]
    · rw [OddForm.od_smul, OddForm.od_one, smul_zero, OddForm.od_mul, h1, h3, zero_smul, zero_smul, add_zero]
  · exact hright (Or.inr rfl) hv hu
  · exact hright (Or.inl rfl) hv hu
  · have huv : U.ep q * (u * v) * U.ep q = u * v := by
      rw [← mul_assoc, hL hu, mul_assoc, hR hv]
    rw [theta_diag U hpq (Or.inr rfl) huv]
    obtain ⟨h1, h2⟩ := theta_qp U hpq hu
    obtain ⟨h3, h4⟩ := theta_pq U hpq hv
    apply OddForm.ext
    · rw [OddForm.ev_smul, OddForm.ev_one, mul_one, OddForm.ev_mul, h1, h3, zero_mul, zero_add, hbe, h2, h4, ← T.st_mul, T.tr_st, T.tr_comm]
    · rw [OddForm.od_smul, OddForm.od_one, smul_zero, OddForm.od_mul, h1, h3, zero_smul, zero_smul, add_zero]
  · exact hleft (Or.inr rfl) hu hv
  · exact hleft (Or.inr rfl) hu hv

end

theorem UpperTheory.V.AlgebraTools.vr_hom :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p q : ι), p ≠ q → (∀ i, o i = p ∨ o i = q) → ∃ φ : E →ₐ[B] Matrix ι ι (U.oddForm p q).Ext, (∀ y, φ y = U.vr p q y) ∧ (∀ y, φ (T.st y) = (φ y)ᵀ) ∧ ∀ y, (φ y).trace = algebraMap B _ (T.tr y) := by
  intro B E _ _ _ T ι _ _ o U p q hpq ho
  obtain ⟨hA, hB, -, hD, -, -, hG⟩ := units_basic T o U
  have hvr : ∀ y i j, U.vr p q y i j = theta U p q (U.x i * y * T.st (U.x j)) := fun _ _ _ => rfl
  have hmul : ∀ y z, U.vr p q (y * z) = U.vr p q y * U.vr p q z := by
    intro y z
    refine Matrix.ext fun i j => ?_
    rw [Matrix.mul_apply]
    simp only [hvr]
    have hs : U.x i * (y * z) * T.st (U.x j) = ∑ k, (U.x i * y * T.st (U.x k)) * (U.x k * z * T.st (U.x j)) := by
      calc U.x i * (y * z) * T.st (U.x j) = U.x i * y * (∑ k, T.st (U.x k) * U.x k) * z * T.st (U.x j) := by
            rw [hB, mul_one, mul_assoc (U.x i) y z]
        _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact theta_mul U hpq (ho i) (ho k) (ho j) (hG i k y) (hG k j z)
  have hone : U.vr p q 1 = 1 := by
    refine Matrix.ext fun i j => ?_
    rw [hvr, mul_one, Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [U.x_st]
      exact theta_ep U hpq (ho i)
    · rw [hA i j h, map_zero]
  have hadd : ∀ y z, U.vr p q (y + z) = U.vr p q y + U.vr p q z := by
    intro y z
    refine Matrix.ext fun i j => ?_
    simp only [hvr, Matrix.add_apply, mul_add, add_mul, map_add (f := _)]
  have hzero : U.vr p q 0 = 0 := by
    refine Matrix.ext fun i j => ?_
    simp only [hvr, mul_zero, zero_mul, map_zero, Matrix.zero_apply]
  have hsmul : ∀ (r : B) y, U.vr p q (r • y) = r • U.vr p q y := by
    intro r y
    refine Matrix.ext fun i j => ?_
    simp only [hvr, Matrix.smul_apply, mul_smul_comm, smul_mul_assoc, map_smul]
  have hcomm : ∀ r : B, U.vr p q (algebraMap B E r) = algebraMap B (Matrix ι ι (U.oddForm p q).Ext) r := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hsmul, hone]
  have hst : ∀ y, U.vr p q (T.st y) = (U.vr p q y)ᵀ := by
    intro y
    refine Matrix.ext fun i j => ?_
    rw [Matrix.transpose_apply, hvr, hvr, ← theta_st U p q (U.x j * y * T.st (U.x i)), T.st_mul, T.st_mul, T.st_st, mul_assoc]
  have htr : ∀ y, (U.vr p q y).trace = algebraMap B _ (T.tr y) := by
    intro y
    rw [Matrix.trace, Algebra.algebraMap_eq_smul_one, hD y, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, hvr]
    exact theta_diag U hpq (ho i) (hG i i y)
  let φ : E →ₐ[B] Matrix ι ι (U.oddForm p q).Ext := { toFun := U.vr p q, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := hadd, commutes' := hcomm }
  exact ⟨φ, fun y => rfl, hst, htr⟩
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

section aux

variable {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] (Φ : OddForm B N)

private theorem ev_alg (b : B) : (algebraMap B Φ.Ext b).ev = b := by
  rw [Algebra.algebraMap_eq_smul_one, OddForm.ev_smul, OddForm.ev_one, mul_one]

private theorem od_alg (b : B) : (algebraMap B Φ.Ext b).od = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, OddForm.od_smul, OddForm.od_one, smul_zero]

private theorem mem_one_iff (z : Φ.Ext) : z ∈ (1 : Submodule B Φ.Ext) ↔ z.od = 0 := by
  rw [Submodule.mem_one]
  refine ⟨?_, fun h => ⟨z.ev, OddForm.ext (ev_alg Φ _) (by rw [od_alg, h])⟩⟩
  rintro ⟨b, rfl⟩
  exact od_alg Φ b

private def oddPart : Submodule B Φ.Ext where
  carrier := {z | z.ev = 0}
  add_mem' := fun {x y} (hx : x.ev = 0) (hy : y.ev = 0) => show (x + y).ev = 0 by
    rw [OddForm.ev_add, hx, hy, add_zero]
  zero_mem' := rfl
  smul_mem' := fun c x (hx : x.ev = 0) => show (c • x).ev = 0 by
    rw [OddForm.ev_smul, hx, mul_zero]

private theorem mem_oddPart (z : Φ.Ext) : z ∈ oddPart Φ ↔ z.ev = 0 := Iff.rfl

private theorem compl_oddPart : _root_.IsCompl (1 : Submodule B Φ.Ext) (oddPart Φ) := by
  refine ⟨Submodule.disjoint_def.2 fun z h1 h2 => ?_, codisjoint_iff.2 (eq_top_iff.2 fun z _ => ?_)⟩
  · exact OddForm.ext ((mem_oddPart Φ z).1 h2) ((mem_one_iff Φ z).1 h1)
  · refine Submodule.mem_sup.2 ⟨Φ.el z.ev 0, (mem_one_iff Φ _).2 rfl, Φ.el 0 z.od, rfl, ?_⟩
    apply OddForm.ext
    · change z.ev + 0 = z.ev
      simp
    · change 0 + z.od = z.od
      simp

end aux

private theorem oB_eq_iff {n a : ℕ} (h1 : 1 ≤ a) (h2 : a < n) (i j : Fin n) :
    oB n a i = oB n a j ↔ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) := by
  unfold oB
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] <;> omega

theorem UpperTheory.V.Pa.gr_E :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} [Module.Finite B E] (a : ℕ) (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F) (U : T.Units (Fin n) (oB n a)), 1 ≤ a → a < n → RingHom.ker (algebraMap B F) = maximalIdeal B → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (oB n a i) i 1) → (∀ y, r y ∈ Ev F F n a) → Nonempty (GrAlg T n a r U.ep) := by
  intro B E F _ _ _ _ _ _ n _ a T r U h1 h2 hker hst hx hev
  let p : Fin n := ⟨0, by omega⟩
  let q : Fin n := ⟨n - 1, by omega⟩
  have hpq : p ≠ q := fun h => by
    have := congrArg Fin.val h
    simp only [p, q] at this
    omega
  have ho : ∀ i, oB n a i = p ∨ oB n a i = q := fun i => by
    unfold oB
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hp : oB n a p = p := by
    unfold oB
    rw [if_pos (show 0 < a by omega)]
  have hq : oB n a q = q := by
    unfold oB
    rw [if_neg (show ¬ (n - 1 < a) by omega)]
  have h0 : ∀ y i j, oB n a i ≠ oB n a j → r y i j = 0 := fun y i j h =>
    (Submodule.mem_bot F).1 ((hev y i j).2 fun h' => h ((oB_eq_iff h1 h2 i j).2 h'))
  obtain ⟨φ, hφ, hφst, -⟩ := vr_hom T (oB n a) U p q hpq ho
  obtain ⟨hinj, hrange⟩ := vr_range T (oB n a) U p q hpq ho
  obtain ⟨hred, hle⟩ := vr_reduction T (oB n a) U r p q hst hx h0
  have hle' := hle hp hq hpq
  rw [hker] at hle'
  have hφe : (φ : E → _) = U.vr p q := funext hφ
  haveI : Module.Finite B (corner B (U.ep p) (U.ep q)) := Module.Finite.range _
  have hv : ∀ y y' k l, U.x k * y * T.st (U.x l) = U.x k * y' * T.st (U.x l) → φ y k l = φ y' k l :=
    fun y y' k l h => by
      rw [hφ, hφ]
      simp only [TrInv.Units.vr, Matrix.of_apply, h]
  have ha : ∀ i, U.x i * U.ep i = U.x i := fun i => by
    conv_lhs => rw [← U.x_mem i, mul_assoc, (U.coi.idem i).eq]
    exact U.x_mem i
  have hd : ∀ i, U.ep i * T.st (U.x i) = T.st (U.x i) := fun i => by
    rw [← U.st_ep i, ← T.st_mul, ha]
  refine ⟨{ AA := (U.oddForm p q).Ext
            fin := inferInstance
            inj := fun b b' h => ?_
            N := oddPart _
            compl := compl_oddPart _
            mul_mem := fun y hy z hz => ?_
            typeI := fun h => absurd h h2.ne
            φ := φ
            φ_inj := hφe ▸ hinj
            range := fun Y => ?_
            st := hφst
            φ_ep := fun i => ?_
            red := fun y i j b h => ?_ }⟩
  · rw [← ev_alg (U.oddForm p q) b, h, ev_alg]
  · rw [mem_oddPart] at hy hz
    refine ⟨(U.oddForm p q).be y.od z.od, hle' (Ideal.subset_span ⟨_, _, rfl⟩), OddForm.ext ?_ ?_⟩
    · rw [ev_alg, OddForm.ev_mul, hy, zero_mul, zero_add]
    · rw [od_alg, OddForm.od_mul, hy, hz, zero_smul, zero_smul, add_zero]
  · rw [hφe, hrange]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [mem_one_iff, mem_oddPart, Ne, oB_eq_iff h1 h2]
  · ext1 k l
    by_cases hk : k = i
    · subst hk
      by_cases hl : l = k
      · subst hl
        rw [hv (U.ep l) 1 l l (by rw [ha, mul_one]), map_one, one_apply_eq, single_apply_same]
      · have e : U.ep k * U.ep l = 0 := U.coi.ortho (Ne.symm hl)
        rw [hv (U.ep k) 0 k l (by rw [← hd l, mul_assoc, ← mul_assoc (U.ep k), e]; simp), map_zero,
          single_apply_of_col_ne _ _ (Ne.symm hl), Matrix.zero_apply]
    · have e : U.ep k * U.ep i = 0 := U.coi.ortho hk
      rw [hv (U.ep i) 0 k l (by rw [← ha k, mul_assoc (U.x k), e]; simp), map_zero,
        single_apply_of_row_ne (Ne.symm hk), Matrix.zero_apply]
  · rw [← hred y i j, ← hφ]
    have e : φ y i j = (φ y i j - algebraMap B _ b) + algebraMap B _ b := (sub_add_cancel _ _).symm
    rw [e, OddForm.ev_add, (mem_oddPart _ _).1 h, ev_alg, zero_add]
