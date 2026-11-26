module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMassLeAndFinite
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSymmInvariantKernelHermitianFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLeMassSecondTypeFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormOrbitSumLeOfSymmKernel
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem sum_eq_sum_of_symm_rel {ι : Type*} (Z : Finset ι) (r : ι → ι → Prop)
    (hr : ∀ p q, r p q → r q p) (hne : ∀ p ∈ Z, ∃ q ∈ Z, r p q) (F H : ι → ℂ)
    (hFH : ∀ p ∈ Z, ∀ q ∈ Z, r p q →
      F p * ((Z.filter (r q)).card : ℂ) = H q * ((Z.filter (r p)).card : ℂ)) :
    ∑ p ∈ Z, F p = ∑ p ∈ Z, H p := by
  have hd : ∀ p ∈ Z, ((Z.filter (r p)).card : ℂ) ≠ 0 := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := hne p hp
    exact_mod_cast (Finset.card_pos.2 ⟨q, Finset.mem_filter.2 ⟨hq, hpq⟩⟩).ne'
  have key : ∀ F : ι → ℂ, ∑ p ∈ Z, F p =
      ∑ p ∈ Z, ∑ q ∈ Z, if r p q then F p / ((Z.filter (r p)).card : ℂ) else 0 := by
    intro F
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ _ (hd p hp)]
  rw [key F, key H, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun p hp => ?_
  by_cases h : r p q
  · rw [if_pos h, if_pos (hr _ _ h), div_eq_div_iff (hd p hp) (hd q hq), hFH p hp q hq h]
  · rw [if_neg h, if_neg (fun h' => h (hr _ _ h'))]

section
variable {G X : Type} [Group G] [MulAction G X] (St : Subgroup G)

theorem ncard_stabilizer_orbit (y w : X) :
    {w' | ∃ h ∈ St, h • y = y ∧ h • w = w'}.ncard =
      (St ⊓ MulAction.stabilizer G w).relIndex (St ⊓ MulAction.stabilizer G y) := by
  have h1 : {w' | ∃ h ∈ St, h • y = y ∧ h • w = w'} =
      MulAction.orbit (St ⊓ MulAction.stabilizer G y : Subgroup G) w := by
    ext w'
    constructor
    · rintro ⟨h, h1, h2, h3⟩
      exact ⟨⟨h, h1, h2⟩, h3⟩
    · rintro ⟨⟨h, h1, h2⟩, h3⟩
      exact ⟨h, h1, h2, h3⟩
  rw [h1, ← MulAction.index_stabilizer, Subgroup.relIndex]
  congr 1
  ext ⟨h, h1, h2⟩
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h3 => ⟨h1, h3⟩, fun h3 => h3.2⟩

theorem relIndex_stabilizer_smul {g : G} (hg : g ∈ St) (y w : X) :
    (St ⊓ MulAction.stabilizer G (g • w)).relIndex (St ⊓ MulAction.stabilizer G (g • y)) =
      (St ⊓ MulAction.stabilizer G w).relIndex (St ⊓ MulAction.stabilizer G y) := by
  rw [← ncard_stabilizer_orbit, ← ncard_stabilizer_orbit,
    ← Set.ncard_image_of_injective {w' | ∃ h ∈ St, h • y = y ∧ h • w = w'} (MulAction.injective g)]
  congr 1
  ext w'
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨h, hh, h1, h2⟩
    refine ⟨_, ⟨g⁻¹ * h * g, St.mul_mem (St.mul_mem (St.inv_mem hg) hh) hg, ?_, rfl⟩, ?_⟩
    · rw [mul_smul, mul_smul, h1, inv_smul_smul]
    · rw [mul_smul, mul_smul, h2, smul_inv_smul]
  · rintro ⟨_, ⟨h, hh, h1, rfl⟩, rfl⟩
    refine ⟨g * h * g⁻¹, St.mul_mem (St.mul_mem hg hh) (St.inv_mem hg), ?_, ?_⟩
    · rw [mul_smul, mul_smul, inv_smul_smul, h1]
    · rw [mul_smul, mul_smul, inv_smul_smul]

theorem invVol_mul_relIndex_comm {G : Type} [Group G] (K0 A B : Subgroup G)
    (hA : K0.relIndex A ≠ 0) (hA' : A.relIndex K0 ≠ 0)
    (hB : K0.relIndex B ≠ 0) (hB' : B.relIndex K0 ≠ 0) :
    invVol K0 A * (B.relIndex A : ℝ) = invVol K0 B * (A.relIndex B : ℝ) := by
  have h1 : K0.relIndex (A ⊓ B) ≠ 0 := fun h =>
    hA (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  have h2 : (A ⊓ B).relIndex K0 ≠ 0 := Subgroup.relIndex_inf_ne_zero hA' hB'
  have e1 := (invVol_mul_pos_le_conj K0 A (A ⊓ B) hA hA' h1 h2).2.2.1 inf_le_left
  have e2 := (invVol_mul_pos_le_conj K0 B (A ⊓ B) hB hB' h1 h2).2.2.1 inf_le_right
  rw [Subgroup.inf_relIndex_left] at e1
  rw [Subgroup.inf_relIndex_right] at e2
  rw [← e1, ← e2]

end

theorem norm_orbit_sum_le_of_symm_kernel : ∀ {G X : Type} [Group G] [MulAction G X] (St K0 : Subgroup G) (P : X → Prop) (om : X → ℂ) (m : X → X → ℝ) (e : ℝ), K0 ≤ St → (∀ h ∈ St, ∀ x, P x → P (h • x) ∧ om (h • x) = om x ∧ invVol K0 (St ⊓ MulAction.stabilizer G (h • x)) = invVol K0 (St ⊓ MulAction.stabilizer G x) ∧ ∀ y, P y → m (h • x) (h • y) = m x y) → (∀ x, P x → K0.relIndex (St ⊓ MulAction.stabilizer G x) ≠ 0 ∧ (St ⊓ MulAction.stabilizer G x).relIndex K0 ≠ 0 ∧ ‖om x‖ = 1 ∧ {y | P y ∧ m x y ≠ 0}.Finite ∧ (∀ y, P y → 0 ≤ m x y ∧ m x y = m y x) ∧ |(∑ᶠ y : {y // P y}, m x y) - 1| ≤ e ∧ ‖∑ᶠ y : {y // P y}, (m x y : ℂ) * om y‖ ≤ e) → {o : MulAction.orbitRel.Quotient St X | P o.out}.Finite → ‖∑' o : MulAction.orbitRel.Quotient St X, if P o.out then ((invVol K0 (St ⊓ MulAction.stabilizer G o.out) : ℝ) : ℂ) * om o.out else 0‖ ≤ 2 * e * ∑' o : MulAction.orbitRel.Quotient St X, if P o.out then invVol K0 (St ⊓ MulAction.stabilizer G o.out) else 0 := by
  intro G X _ _ St K0 P om m e _ hinv hP hfin
  set mu : X → ℝ := fun x => invVol K0 (St ⊓ MulAction.stabilizer G x) with hmu
  have hN : ∀ x, ∃ s : Finset X, P x → ∀ y, y ∈ s ↔ P y ∧ m x y ≠ 0 := by
    intro x
    by_cases hx : P x
    · exact ⟨(hP x hx).2.2.2.1.toFinset, fun _ y => by simp⟩
    · exact ⟨∅, fun h => absurd h hx⟩
  choose N hN using hN
  have hO : ∀ o, o ∈ hfin.toFinset ↔ P o.out := fun o => by simp
  generalize hfin.toFinset = O at hO
  have hR : ∀ x, P x → |(∑ y ∈ N x, m x y) - 1| ≤ e := by
    intro x hx
    have := (hP x hx).2.2.2.2.2.1
    rwa [finsum_subtype_eq_finsum_cond (f := fun y => m x y),
      finsum_cond_eq_sum_of_cond_iff (f := fun y => m x y) (t := N x)] at this
    intro y hy
    rw [hN x hx]
    exact ⟨fun h => ⟨h, hy⟩, fun h => h.1⟩
  have hS : ∀ x, P x → ‖∑ y ∈ N x, (m x y : ℂ) * om y‖ ≤ e := by
    intro x hx
    have := (hP x hx).2.2.2.2.2.2
    rwa [finsum_subtype_eq_finsum_cond (f := fun y => (m x y : ℂ) * om y),
      finsum_cond_eq_sum_of_cond_iff (f := fun y => (m x y : ℂ) * om y) (t := N x)] at this
    intro y hy
    rw [hN x hx]
    refine ⟨fun h => ⟨h, fun h0 => hy ?_⟩, fun h => h.1⟩
    simp [h0]
  have hpos : ∀ x, P x → 0 < mu x := fun x hx =>
    (invVol_mul_pos_le_conj K0 _ _ (hP x hx).1 (hP x hx).2.1 (hP x hx).1 (hP x hx).2.1).2.1
  have t1 : (∑' o : MulAction.orbitRel.Quotient St X,
      if P o.out then ((mu o.out : ℝ) : ℂ) * om o.out else 0) =
      ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out := by
    rw [tsum_eq_sum (s := O) (fun o ho => if_neg (fun h => ho ((hO o).2 h)))]
    exact Finset.sum_congr rfl fun o ho => if_pos ((hO o).1 ho)
  have t2 : (∑' o : MulAction.orbitRel.Quotient St X, if P o.out then mu o.out else 0) =
      ∑ o ∈ O, mu o.out := by
    rw [tsum_eq_sum (s := O) (fun o ho => if_neg (fun h => ho ((hO o).2 h)))]
    exact Finset.sum_congr rfl fun o ho => if_pos ((hO o).1 ho)
  refine (congrArg norm t1).trans_le (le_of_le_of_eq ?_ (congrArg (2 * e * ·) t2.symm))
  have huniq : ∀ (o o' : MulAction.orbitRel.Quotient St X) (g : G), g ∈ St →
      g • o.out = o'.out → o = o' := by
    intro o o' g hg h
    rw [← Quotient.out_eq o, ← Quotient.out_eq o']
    exact (Quotient.sound (show MulAction.orbitRel St X o'.out o.out from ⟨⟨g, hg⟩, h⟩)).symm
  have hrep : ∀ z : X, ∃ o : MulAction.orbitRel.Quotient St X, ∃ g ∈ St, g • z = o.out := by
    intro z
    obtain ⟨⟨g, hg⟩, h⟩ : MulAction.orbitRel St X (Quotient.mk _ z).out z := Quotient.mk_out z
    exact ⟨_, g, hg, h⟩
  have unf : ∑ o ∈ O, ∑ z ∈ N o.out, ((mu o.out : ℝ) : ℂ) * ((m o.out z : ℂ) * om z) =
      ∑ o ∈ O, ∑ z ∈ N o.out, ((mu o.out : ℝ) : ℂ) * ((m o.out z : ℂ) * om o.out) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    set Z := O.sigma fun o => N o.out with hZ
    have mZ : ∀ p, p ∈ Z ↔ P p.1.out ∧ P p.2 ∧ m p.1.out p.2 ≠ 0 := by
      intro p
      rw [hZ, Finset.mem_sigma, hO]
      exact and_congr_right fun h => hN _ h _
    let r : (Σ _ : MulAction.orbitRel.Quotient St X, X) →
        (Σ _ : MulAction.orbitRel.Quotient St X, X) → Prop :=
      fun p q => ∃ g ∈ St, g • p.2 = q.1.out ∧ g • p.1.out = q.2
    have hr : ∀ p q, r p q → r q p := by
      rintro p q ⟨g, hg, h1, h2⟩
      exact ⟨g⁻¹, St.inv_mem hg, by rw [← h2, inv_smul_smul], by rw [← h1, inv_smul_smul]⟩
    have hm : ∀ p ∈ Z, ∀ q, r p q → m q.1.out q.2 = m p.1.out p.2 := by
      rintro p hp q ⟨g, hg, h1, h2⟩
      obtain ⟨a, b, -⟩ := (mZ p).1 hp
      rw [← h1, ← h2, (hinv g hg _ b).2.2.2 _ a, ((hP _ b).2.2.2.2.1 _ a).2]
    have hmem : ∀ p ∈ Z, ∀ q, r p q → q ∈ Z := by
      intro p hp q hpq
      have := hm p hp q hpq
      obtain ⟨g, hg, h1, h2⟩ := hpq
      obtain ⟨a, b, c⟩ := (mZ p).1 hp
      rw [mZ, this, ← h1, ← h2]
      exact ⟨(hinv g hg _ b).1, (hinv g hg _ a).1, c⟩
    have hdeg : ∀ p ∈ Z, ∀ q, r p q → (Z.filter (r p)).card =
        (St ⊓ MulAction.stabilizer G q.2).relIndex (St ⊓ MulAction.stabilizer G q.1.out) := by
      rintro p hp ⟨o, w⟩ ⟨g, hg, h1, h2⟩
      dsimp only at h1 h2 ⊢
      rw [← ncard_stabilizer_orbit, ← Set.ncard_coe_finset,
        ← Set.ncard_image_of_injective _ (sigma_mk_injective (β := fun _ => X) (i := o))]
      congr 1
      ext ⟨o', w'⟩
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨-, g', hg', h1', h2'⟩
        dsimp only at h1' h2'
        have e1 : (g' * g⁻¹) • o.out = o'.out := by
          rw [← h1, mul_smul, inv_smul_smul, h1']
        have hgg := St.mul_mem hg' (St.inv_mem hg)
        obtain rfl := huniq _ _ _ hgg e1
        refine ⟨w', ⟨_, hgg, e1, ?_⟩, rfl⟩
        rw [← h2, mul_smul, inv_smul_smul, h2']
      · rintro ⟨w'', ⟨h, hh, e1, e2⟩, e3⟩
        rw [← e3]
        have : r p ⟨o, w''⟩ :=
          ⟨h * g, St.mul_mem hh hg, by rw [mul_smul, h1, e1], by rw [mul_smul, h2, e2]⟩
        exact ⟨hmem p hp _ this, this⟩
    refine sum_eq_sum_of_symm_rel Z r hr ?_ _ _ ?_
    · intro p hp
      obtain ⟨o, g, hg, h⟩ := hrep p.2
      have : r p ⟨o, g • p.1.out⟩ := ⟨g, hg, h, rfl⟩
      exact ⟨_, hmem p hp _ this, this⟩
    · intro p hp q hq hpq
      rw [hdeg p hp q hpq, hdeg q hq p (hr _ _ hpq), hm p hp q hpq]
      obtain ⟨g, hg, h1, h2⟩ := hpq
      obtain ⟨a, b, c⟩ := (mZ p).1 hp
      have e1 := invVol_mul_relIndex_comm K0 _ _ (hP _ a).1 (hP _ a).2.1 (hP _ b).1 (hP _ b).2.1
      have e2 := congrArg (fun t : ℝ => (t : ℂ)) e1
      rw [← h1, ← h2, relIndex_stabilizer_smul St hg, (hinv g hg _ b).2.1]
      simp only [hmu]
      rw [(hinv g hg _ b).2.2.1]
      push_cast at e2
      linear_combination (m p.1.out p.2 : ℂ) * om p.2 * e2
  have dec : ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out =
      ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * (∑ z ∈ N o.out, (m o.out z : ℂ) * om z) -
      ∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out * (((∑ z ∈ N o.out, m o.out z) - 1 : ℝ) : ℂ) := by
    simp only [Finset.mul_sum]
    rw [unf, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    push_cast
    ring
  rw [dec]
  refine (norm_sub_le _ _).trans ?_
  have b1 : ‖∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * (∑ z ∈ N o.out, (m o.out z : ℂ) * om z)‖ ≤
      ∑ o ∈ O, e * mu o.out := by
    refine norm_sum_le_of_le _ fun o ho => ?_
    have h := (hO o).1 ho
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos _ h), mul_comm]
    exact mul_le_mul_of_nonneg_right (hS _ h) (hpos _ h).le
  have b2 : ‖∑ o ∈ O, ((mu o.out : ℝ) : ℂ) * om o.out *
      (((∑ z ∈ N o.out, m o.out z) - 1 : ℝ) : ℂ)‖ ≤ ∑ o ∈ O, e * mu o.out := by
    refine norm_sum_le_of_le _ fun o ho => ?_
    have h := (hO o).1 ho
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (hpos _ h), (hP _ h).2.2.1, mul_one, mul_comm]
    exact mul_le_mul_of_nonneg_right (hR _ h) (hpos _ h).le
  rw [← Finset.mul_sum] at b1 b2
  linarith

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLeMassSecondTypeFamily
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.AmpCancel

theorem ofReal_tsum_ite {ι : Type} (p : ι → Prop) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hfin : {i | p i}.Finite) :
    ENNReal.ofReal (∑' i, if p i then f i else 0) =
      ∑' i, if p i then ENNReal.ofReal (f i) else 0 := by
  have hs : ∀ i, i ∉ hfin.toFinset → ¬ p i := fun i hi h => hi (hfin.mem_toFinset.2 h)
  have hs' : ∀ i ∈ hfin.toFinset, p i := fun i hi => hfin.mem_toFinset.1 hi
  rw [tsum_eq_sum (s := hfin.toFinset) (fun i hi => if_neg (hs i hi)),
    tsum_eq_sum (s := hfin.toFinset) (fun i hi => if_neg (hs i hi)),
    Finset.sum_congr rfl (fun i hi => if_pos (hs' i hi)),
    Finset.sum_congr rfl (fun i hi => if_pos (hs' i hi)),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hf i)]

theorem amp_le_mass {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k)
    (β J βJ : ℕ) (d : S.Datum) :
    ENNReal.ofReal (‖S.amp d (S.InFF β J βJ d)‖) ≤
      ENNReal.ofReal (7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) * S.mass d (S.InFF β J βJ d) := by
  have hk1 : 1 ≤ k := by omega
  have hc0 : 0 ≤ (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := zpow_nonneg (Nat.cast_nonneg _) _
  have hvol : ∀ K : Subgroup S.GLV, 0 ≤ invVol S.K0 K := fun K =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨P, hP⟩ : ∃ P : Submodule L.O S.V → Prop, P = fun Λ => S.IsTerm d Λ ∧ S.InFF β J βJ d Λ :=
    ⟨_, rfl⟩
  have hPiff : ∀ Λ, P Λ ↔ S.IsTerm d Λ ∧ S.InFF β J βJ d Λ := fun Λ => by rw [hP]
  have hPfin : {o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) | P o.out}.Finite :=
    (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk1 d).2.subset fun o ho => ((hPiff _).1 ho).1
  have hmass : S.mass d (S.InFF β J βJ d) = ENNReal.ofReal (∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0) := by
    rw [ofReal_tsum_ite (ι := MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)) (fun o => P o.out)
      (fun o => invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out)) (fun o => hvol _) hPfin]
    subst hP
    unfold Frames.mass Frames.mu
    exact tsum_congr fun o => by congr
  have hsum0 : 0 ≤ ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0 :=
    tsum_nonneg fun o => by split_ifs <;> simp [hvol]
  have hamp : S.amp d (S.InFF β J βJ d) = ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
      if P o.out then ((invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) : ℝ) : ℂ) * S.om d o.out
      else 0 := by
    subst hP
    unfold Frames.amp Frames.mu
    exact tsum_congr fun o => by congr
  have key : ‖S.amp d (S.InFF β J βJ d)‖ ≤ 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) *
      ∑' o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
        if P o.out then invVol S.K0 (S.St ⊓ MulAction.stabilizer S.GLV o.out) else 0 := by
    by_cases hJ : 1 ≤ J ∧ J ≤ r
    · have hj : ((⟨J - 1, by omega⟩ : Fin r) : ℕ) + 1 = J := by simp only; omega
      obtain ⟨m, hm_inv, hm⟩ := GlobalTheory.T.exists_symm_invariant_kernel_hermitian_frames L r k S hk ⟨J - 1, by omega⟩ β βJ d P
        (fun Λ => by rw [hj]; exact hPiff Λ)
      have hK0 : S.K0 ≤ S.St := fun g hg => hg.1.1
      have bound := GlobalTheory.HL.norm_orbit_sum_le_of_symm_kernel S.St S.K0 P (S.om d) m
        (24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) hK0
        (fun h hh x hx => by
          obtain ⟨hT, hI⟩ := (hPiff x).1 hx
          have T := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d x hT h hh
          have hlat := (GlobalTheory.HL.TermBasic.term_basic L r k S d x hT).1.1
          exact ⟨(hPiff _).2 ⟨T.1, (T.2.2.2.2.2.2.2.2.2.1 β J βJ).2 hI⟩, T.2.1,
            ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 x hlat).2.2 h hh, fun y hy => hm_inv h hh x y hx hy⟩)
        (fun x hx => by
          have hb := GlobalTheory.HL.TermBasic.term_basic L r k S d x ((hPiff x).1 hx).1
          have A := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 x hb.1.1
          have W := (GlobalTheory.HL.WitIndep.witness_independence L r k S d x _ _ hb.2.1).2.2.2.2
          obtain ⟨h1, h2, h3, h4⟩ := hm x hx
          exact ⟨A.1, A.2.1, W, h1, h2, h3, h4⟩)
        hPfin
      rw [hamp]
      have h2 : 2 * (24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ≤
          7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by linarith
      exact bound.trans (mul_le_mul_of_nonneg_right h2 hsum0)
    · have hempty : ∀ Λ, ¬ P Λ := by
        intro Λ hΛ
        obtain ⟨hT, hTB, -, hle, ⟨y, hy, hyJ⟩, -⟩ := (hPiff Λ).1 hΛ
        by_cases hJr : r < J
        · have := hTB.2.1 y hy
          omega
        · have hJ0 : J = 0 := by omega
          apply hTB.1
          refine le_antisymm (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).2.2.1 fun z hz => ?_
          refine ((GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.2.2.2.2.1 z hz).1 ?_
          have := hle z hz
          omega
      rw [hamp]
      simp [hempty]
  rw [hmass, ← ENNReal.ofReal_mul (by linarith)]
  exact ENNReal.ofReal_le_ofReal key

end GlobalTheory.HL.AmpCancel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeLeMassSecondTypeFamilyStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_le_mass_secondType_family : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (β J βJ : ℕ) (d : S.Datum), ENNReal.ofReal (‖S.amp d (S.InFF β J βJ d)‖) ≤ ENNReal.ofReal (7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) * S.mass d (S.InFF β J βJ d) := by
  first | exact @GlobalTheory.HL.AmpCancel.amp_le_mass | exact GlobalTheory.HL.AmpCancel.amp_le_mass | (intros; apply GlobalTheory.HL.AmpCancel.amp_le_mass <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetSecondTypeFamilyAmpSqLe
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FamilyBound

theorem geom_le (x : ℝ) (hx : 2 ≤ x) (i : ℕ) : ∑ m ∈ Finset.range (i + 1), x ^ m ≤ 2 * x ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ]
    have h0 : 0 ≤ x ^ i := by positivity
    have : 2 * x ^ i ≤ x ^ (i + 1) := by rw [pow_succ]; nlinarith
    linarith

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mass_mono (d : S.Datum) (P Q : Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → Q Λ) : S.mass d P ≤ S.mass d Q := by
  unfold Frames.mass
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases ho : S.IsTerm d o.out ∧ P o.out
  · rw [if_pos ho, if_pos ⟨ho.1, h _ ho.1 ho.2⟩]
  · rw [if_neg ho]; exact bot_le

theorem mass_le_sum {ι : Type} (s : Finset ι) (d : S.Datum) (P : Submodule L.O S.V → Prop)
    (Q : ι → Submodule L.O S.V → Prop)
    (h : ∀ Λ, S.IsTerm d Λ → P Λ → ∃ m ∈ s, Q m Λ) : S.mass d P ≤ ∑ m ∈ s, S.mass d (Q m) := by
  unfold Frames.mass
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun o => ?_
  by_cases ho : S.IsTerm d o.out ∧ P o.out
  · obtain ⟨m, hm, hq⟩ := h _ ho.1 ho.2
    rw [if_pos ho]
    refine le_trans ?_ (Finset.single_le_sum (f := fun m =>
      if S.IsTerm d o.out ∧ Q m o.out then ENNReal.ofReal (S.mu o.out) else 0) (fun _ _ => bot_le) hm)
    rw [if_pos ⟨ho.1, hq⟩]
  · rw [if_neg ho]; exact bot_le

theorem sumData_mono (φ ψ : S.Datum → ℝ≥0∞) (h : ∀ d, φ d ≤ ψ d) : S.sumData φ ≤ S.sumData ψ := by
  unfold Frames.sumData
  exact ENNReal.tsum_le_tsum fun o => by gcongr; exact h _

end

theorem family_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β J βJ : ℕ, S.ampSq (S.InFF β J βJ) ≤ ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * ((S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2) * S.nn := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk β J βJ
  by_cases hex : ∃ d Λ, S.IsTerm d Λ ∧ S.InFF β J βJ d Λ
  swap
  · have h0 : ∀ d, S.amp d (S.InFF β J βJ d) = 0 := by
      intro d
      unfold Frames.amp
      have : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V),
          ¬ (S.IsTerm d o.out ∧ S.InFF β J βJ d o.out) := fun o ho => hex ⟨d, _, ho⟩
      simp [this]
    have : S.ampSq (S.InFF β J βJ) = 0 := by
      unfold Frames.ampSq Frames.sumData
      simp [h0]
    rw [this]; exact bot_le
  obtain ⟨d₀, Λ₀, ht, hF⟩ := hex
  obtain ⟨-, -, -, -, hH, ⟨i, -, hi⟩, hbz, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d₀ Λ₀ ht
  have hβ : β = S.q ^ i := by rw [← hF.2.1, hi]
  have hq0 : 0 < S.q := GlobalTheory.HL.SmallImage.resQ_pos S.ϖ S.ϖ_irr
  have hq1 : S.q ≠ 1 := by
    intro h
    exact hF.1.1 (hbz.2 (by rw [hi, h, one_pow]))
  have hq : 2 ≤ S.q := by omega
  have hβ1 : 1 ≤ β := by rw [hβ]; exact Nat.one_le_pow _ _ hq0
  have hk1 : 1 ≤ k := by omega
  set A0 : ℝ := S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) with hA0
  set A1 : ℝ := 4 * S.Hp ^ (4 * (r + 1)) with hA1
  set e : ℝ := (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) with he
  have hA0p : 0 ≤ A0 := by positivity
  have hA1p : 0 ≤ A1 := by positivity
  have hep : 0 ≤ e := by positivity
  have hmass : ∀ d, S.mass d (S.InFF β J βJ d) ≤ ENNReal.ofReal (2 * A0 * (β : ℝ) ^ (k - 1)) := by
    intro d
    refine (mass_le_sum S (Finset.range (i + 1)) d _ (fun m Λ => S.cardI d Λ = S.q ^ m) ?_).trans ?_
    · intro Λ hΛ hP
      obtain ⟨⟨m, hm⟩, hle, -⟩ := GlobalTheory.HL.SmallImage.small_image L r k S d Λ hΛ
      refine ⟨m, ?_, hm⟩
      rw [hm, hP.2.1, hβ] at hle
      have := (Nat.pow_le_pow_iff_right (by omega)).1 hle
      exact Finset.mem_range.2 (by omega)
    · refine (Finset.sum_le_sum fun m _ => (GlobalTheory.T.hermitianDoubleCoset_mass_le_and_finite L r k S hk1 d).1 (S.q ^ m)).trans ?_
      rw [← ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hx : (2 : ℝ) ≤ (S.q : ℝ) ^ (k - 1) := by
        have h2 : (2 : ℝ) ≤ S.q := by exact_mod_cast hq
        exact h2.trans (le_self_pow₀ (by linarith) (by omega))
      have hg := geom_le _ hx i
      have hc : ∀ m : ℕ, ((S.q ^ m : ℕ) : ℝ) ^ (k - 1) = ((S.q : ℝ) ^ (k - 1)) ^ m := by
        intro m; push_cast; rw [← pow_mul, ← pow_mul, mul_comm]
      rw [← Finset.mul_sum, hβ]
      simp only [hc]
      nlinarith [mul_le_mul_of_nonneg_left hg hA0p]
  have h1 := (GlobalTheory.HL.BasicIneq.basic_inequality L r k S hk1).2 (S.InFF β J βJ) _ (7 * e) (by positivity)
    hmass (fun d => GlobalTheory.T.amplitude_le_mass_secondType_family L r k S hk β J βJ d)
  have h2 : (S.sumData fun d => S.mass d (S.InFF β J βJ d)) ≤
      ENNReal.ofReal (A1 * ((β : ℝ) ^ (k - 1))⁻¹) * S.nn :=
    (sumData_mono S _ _ fun d => mass_mono S d _ _ fun Λ _ h => h.2.1).trans (GlobalTheory.T.sumData_mass_be_eq_le L r k S hk β hβ1)
  refine h1.trans ?_
  refine (mul_le_mul_right h2 _).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hb : (β : ℝ) ^ (k - 1) ≠ 0 := by
    have : (0 : ℝ) < β := by exact_mod_cast hβ1
    positivity
  have : (7 * e) ^ 2 * (2 * A0 * (β : ℝ) ^ (k - 1)) * (A1 * ((β : ℝ) ^ (k - 1))⁻¹) = 98 * A0 * A1 * e ^ 2 := by
    field_simp
    ring
  rw [this]

end GlobalTheory.HL.FamilyBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetSecondTypeFamilyAmpSqLeStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCoset_secondType_family_ampSq_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ β J βJ : ℕ, S.ampSq (S.InFF β J βJ) ≤ ENNReal.ofReal (98 * S.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1)) * (4 * S.Hp ^ (4 * (r + 1))) * ((S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3))) ^ 2) * S.nn := by
  first | exact @GlobalTheory.HL.FamilyBound.family_bound | exact GlobalTheory.HL.FamilyBound.family_bound | (intros; apply GlobalTheory.HL.FamilyBound.family_bound <;> assumption)
end
