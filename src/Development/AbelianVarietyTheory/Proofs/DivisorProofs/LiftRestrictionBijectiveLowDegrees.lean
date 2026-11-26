module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyComputedOnAffinePairs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormsRestrictionAffineLiftBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineForgetFormsBijectiveSiteAndPairs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerComplexLiftAndExtensionLemmas
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerComplexLiftAndExtensionLemmas
open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.TowerLift

theorem closed_lift (W A B : ℕ → Type 1) [∀ n, AddCommGroup (W n)] [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (c : ∀ n, W n →+ A n) (d : ∀ n, A n →+ B n) (r : ∀ n, W (n + 1) →+ W n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n)
    (hdc : ∀ n x, d n (c n x) = 0) (hsc : ∀ n x, s n (c (n + 1) x) = c n (r n x)) (htd : ∀ n x, t n (d (n + 1) x) = d n (s n x))
    (hr : ∀ n, Function.Surjective (r n)) (hcl : ∀ n a, d n a = 0 → ∃ a' w, d (n + 1) a' = 0 ∧ a = s n a' + c n w)
    (b : ∀ n, B n) (hb : ∀ n, t n (b (n + 1)) = b n) (hrg : ∀ n, ∃ a, d n a = b n) :
    ∃ a : ∀ n, A n, (∀ n, s n (a (n + 1)) = a n) ∧ ∀ n, d n (a n) = b n := by
  have step : ∀ n (x : {a : A n // d n a = b n}), ∃ y : {a : A (n + 1) // d (n + 1) a = b (n + 1)}, s n y.1 = x.1 := by
    intro n x
    obtain ⟨x', hx'⟩ := hrg (n + 1)
    have h0 : d n (x.1 - s n x') = 0 := by
      rw [map_sub, x.2, ← htd, hx', hb, sub_self]
    obtain ⟨a', w, ha', hw⟩ := hcl n _ h0
    obtain ⟨w', rfl⟩ := hr n w
    refine ⟨⟨x' + a' + c (n + 1) w', ?_⟩, ?_⟩
    · rw [map_add (f := _), map_add (f := _), hx', ha', hdc, add_zero, add_zero]
    · show s n (x' + a' + c (n + 1) w') = x.1
      rw [map_add (f := _), map_add (f := _), hsc, add_assoc, ← hw, add_sub_cancel]
  choose f hf using step
  obtain ⟨a₀, ha₀⟩ := hrg 0
  let g : ∀ n, {a : A n // d n a = b n} := fun n => Nat.rec ⟨a₀, ha₀⟩ (fun n x => f n x) n
  exact ⟨fun n => (g n).1, fun n => hf n (g n), fun n => (g n).2⟩

theorem closed_extend (A B : ℕ → Type 1) [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (Z : ∀ n, AddSubgroup (B n)) (d : ∀ n, A n →+ B n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n)
    (hd : ∀ n x, d n x ∈ Z n) (htd : ∀ n x, t n (d (n + 1) x) = d n (s n x)) (hs : ∀ n, Function.Surjective (s n))
    (hZ : ∀ n, ∀ x ∈ Z (n + 1), t n x ∈ Z n) (hl : ∀ n, ∀ b ∈ Z n, ∃ b' ∈ Z (n + 1), ∃ a, b = t n b' + d n a) :
    ∀ b₀ ∈ Z 0, ∃ b : ∀ n, B n, b 0 = b₀ ∧ (∀ n, b n ∈ Z n) ∧ ∀ n, t n (b (n + 1)) = b n := by
  intro b₀ hb₀
  have step : ∀ n (x : Z n), ∃ y : Z (n + 1), t n y.1 = x.1 := by
    intro n x
    obtain ⟨b', hb', a, ha⟩ := hl n x.1 x.2
    obtain ⟨a'', rfl⟩ := hs n a
    refine ⟨⟨b' + d (n + 1) a'', (Z (n + 1)).add_mem hb' (hd _ _)⟩, ?_⟩
    show t n (b' + d (n + 1) a'') = x.1
    rw [map_add (f := _), htd, ha]
  choose f hf using step
  let g : ∀ n, Z n := fun n => Nat.rec ⟨b₀, hb₀⟩ (fun n x => f n x) n
  exact ⟨fun n => (g n).1, rfl, fun n => (g n).2, fun n => hf n (g n)⟩

theorem tower_lemmas : (∀ (W A B : ℕ → Type 1) [∀ n, AddCommGroup (W n)] [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (c : ∀ n, W n →+ A n) (d : ∀ n, A n →+ B n) (r : ∀ n, W (n + 1) →+ W n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n (c n x) = 0) → (∀ n x, s n (c (n + 1) x) = c n (r n x)) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (r n)) → (∀ n a, d n a = 0 → ∃ a' w, d (n + 1) a' = 0 ∧ a = s n a' + c n w) → ∀ b : ∀ n, B n, (∀ n, t n (b (n + 1)) = b n) → (∀ n, ∃ a, d n a = b n) → ∃ a : ∀ n, A n, (∀ n, s n (a (n + 1)) = a n) ∧ ∀ n, d n (a n) = b n) ∧ ∀ (A B : ℕ → Type 1) [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (Z : ∀ n, AddSubgroup (B n)) (d : ∀ n, A n →+ B n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n x ∈ Z n) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (s n)) → (∀ n, ∀ x ∈ Z (n + 1), t n x ∈ Z n) → (∀ n, ∀ b ∈ Z n, ∃ b' ∈ Z (n + 1), ∃ a, b = t n b' + d n a) → ∀ b₀ ∈ Z 0, ∃ b : ∀ n, B n, b 0 = b₀ ∧ (∀ n, b n ∈ Z n) ∧ ∀ n, t n (b (n + 1)) = b n :=
  ⟨closed_lift, closed_extend⟩

end GlobalTheory.TowerLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerComplexLiftAndExtensionLemmasStatement
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_complex_lift_and_extension_lemmas : (∀ (W A B : ℕ → Type 1) [∀ n, AddCommGroup (W n)] [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (c : ∀ n, W n →+ A n) (d : ∀ n, A n →+ B n) (r : ∀ n, W (n + 1) →+ W n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n (c n x) = 0) → (∀ n x, s n (c (n + 1) x) = c n (r n x)) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (r n)) → (∀ n a, d n a = 0 → ∃ a' w, d (n + 1) a' = 0 ∧ a = s n a' + c n w) → ∀ b : ∀ n, B n, (∀ n, t n (b (n + 1)) = b n) → (∀ n, ∃ a, d n a = b n) → ∃ a : ∀ n, A n, (∀ n, s n (a (n + 1)) = a n) ∧ ∀ n, d n (a n) = b n) ∧ ∀ (A B : ℕ → Type 1) [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] (Z : ∀ n, AddSubgroup (B n)) (d : ∀ n, A n →+ B n) (s : ∀ n, A (n + 1) →+ A n) (t : ∀ n, B (n + 1) →+ B n), (∀ n x, d n x ∈ Z n) → (∀ n x, t n (d (n + 1) x) = d n (s n x)) → (∀ n, Function.Surjective (s n)) → (∀ n, ∀ x ∈ Z (n + 1), t n x ∈ Z n) → (∀ n, ∀ b ∈ Z n, ∃ b' ∈ Z (n + 1), ∃ a, b = t n b' + d n a) → ∀ b₀ ∈ Z 0, ∃ b : ∀ n, B n, b 0 = b₀ ∧ (∀ n, b n ∈ Z n) ∧ ∀ n, t n (b (n + 1)) = b n := by
  first | exact @GlobalTheory.TowerLift.tower_lemmas | exact GlobalTheory.TowerLift.tower_lemmas | (intros; apply GlobalTheory.TowerLift.tower_lemmas <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRestrictionFourTermComplexOfExhaustion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRestrictionFourTermComplexOfExhaustion
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxTowerTwo

universe u u'

section Gen

variable {C₁ : Type u} [Category.{0} C₁] {C₂ : Type u'} [Category.{0} C₂]

theorem cx_D1_D0_eq_zero (K : Cx C₁) (g : K.M0.c0) : K.D1 (K.D0 g) = 0 := by
  refine Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_)
    (Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun φ ↦ ?_) (funext fun T ↦ ?_))
  · simp [Cx.D0, Cx.D1, Coef.map_comp, map_sub]
  · simp [Cx.D0, Cx.D1, Cx.diffZero_natural, map_sub]
  · simp [Cx.D0, Cx.D1, Cx.diffOne_diffZero]

theorem first_diagonal_phase_mem_unitary (K : Cx C₁) (c : K.T1) : K.D1 c ∈ K.Z2 := by
  refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · simp [Cx.D1, Coef.map_comp, map_sub, map_add (f := _)]; abel
  · simp [Cx.D1, Coef.map_comp, map_sub, map_add (f := _), Cx.diffZero_natural]; abel
  · simp [Cx.D1, map_sub, Cx.diffOne_natural, Cx.diffOne_diffZero]
  · simp [Cx.D1, Cx.diffTwo_comp_diffOne]

variable {K : Cx C₁} {K' : Cx C₂} (m : CxMap K K')

theorem h1_mk (c : K.Z1) : m.h1 (QuotientAddGroup.mk c) = QuotientAddGroup.mk (m.z1 c) := rfl
theorem h2_mk (c : K.Z2) : m.h2 (QuotientAddGroup.mk c) = QuotientAddGroup.mk (m.z2 c) := rfl

theorem h1_mk_eq_zero_iff_exists_d0 {K : Cx C₁} (c : K.Z1) : (QuotientAddGroup.mk c : K.H1) = 0 ↔ ∃ w, K.D0 w = c := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

theorem h2_mk_eq_zero_iff_exists_d1 {K : Cx C₁} (c : K.Z2) : (QuotientAddGroup.mk c : K.H2) = 0 ↔ ∃ w, K.D1 w = c := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

theorem inj1 (h : Function.Injective m.h1) (x : K.T1) (hx : x ∈ K.Z1) (w : K'.M0.c0)
    (hw : m.p1 x = K'.D0 w) : ∃ v, K.D0 v = x := by
  have e : m.h1 (QuotientAddGroup.mk ⟨x, hx⟩) = m.h1 0 := by
    rw [map_zero, h1_mk, h1_mk_eq_zero_iff_exists_d0]; exact ⟨w, hw.symm⟩
  exact (h1_mk_eq_zero_iff_exists_d0 _).1 (h e)

theorem inj2 (h : Function.Injective m.h2) (x : K.T2) (hx : x ∈ K.Z2) (w : K'.T1)
    (hw : m.p2 x = K'.D1 w) : ∃ v, K.D1 v = x := by
  have e : m.h2 (QuotientAddGroup.mk ⟨x, hx⟩) = m.h2 0 := by
    rw [map_zero, h2_mk, h2_mk_eq_zero_iff_exists_d1]; exact ⟨w, hw.symm⟩
  exact (h2_mk_eq_zero_iff_exists_d1 _).1 (h e)

theorem surj1 (h : Function.Surjective m.h1) (y : K'.T1) (hy : y ∈ K'.Z1) :
    ∃ x ∈ K.Z1, ∃ w, y = m.p1 x + K'.D0 w := by
  obtain ⟨q, hq⟩ := h (QuotientAddGroup.mk ⟨y, hy⟩)
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [h1_mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at hq
  obtain ⟨w, hw⟩ := hq
  refine ⟨x, hx, w, ?_⟩
  have e : K'.D0 w = -m.p1 x + y := hw
  rw [e]; abel

theorem surj2 (h : Function.Surjective m.h2) (y : K'.T2) (hy : y ∈ K'.Z2) :
    ∃ x ∈ K.Z2, ∃ w, y = m.p2 x + K'.D1 w := by
  obtain ⟨q, hq⟩ := h (QuotientAddGroup.mk ⟨y, hy⟩)
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [h2_mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at hq
  obtain ⟨w, hw⟩ := hq
  refine ⟨x, hx, w, ?_⟩
  have e : K'.D1 w = -m.p2 x + y := hw
  rw [e]; abel

theorem h2_bijective_of_surj_of_inj_on_cocycles (hs : ∀ y ∈ K'.Z2, ∃ x ∈ K.Z2, ∃ w, y = m.p2 x + K'.D1 w)
    (hi : ∀ x ∈ K.Z2, ∀ w, m.p2 x = K'.D1 w → ∃ v, K.D1 v = x) : Function.Bijective m.h2 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [h2_mk, h2_mk_eq_zero_iff_exists_d1] at hq
    obtain ⟨w, hw⟩ := hq
    exact (h2_mk_eq_zero_iff_exists_d1 _).2 (hi x hx w hw.symm)
  · intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨x, hx, w, hxw⟩ := hs y hy
    refine ⟨QuotientAddGroup.mk ⟨x, hx⟩, ?_⟩
    rw [h2_mk, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    refine ⟨w, ?_⟩
    show K'.D1 w = -m.p2 x + y
    rw [hxw]; abel

end Gen

section Lvl

variable {C : Type u} [Category.{0} C]

def lvl (K : Cx C) {P P' : ObjectProperty C} (h : P ≤ P') : CxMap (K.res P'.ι) (K.res P.ι) where
  G := ObjectProperty.ιOfLE h
  a0 _ := AddMonoidHom.id _
  a1 _ := AddMonoidHom.id _
  a2 _ := AddMonoidHom.id _
  a3 _ := AddMonoidHom.id _
  compDegreeZero_natural _ _ := rfl
  compDegreeOne_natural _ _ := rfl
  compDegreeTwo_natural _ _ := rfl
  comp_commutes_diffZero _ _ := rfl
  comp_commutes_diffOne _ _ := rfl
  comp_commutes_diffTwo _ _ := rfl

theorem level_p0_surjective (K : Cx C) {P P' : ObjectProperty C} (h : P ≤ P') :
    Function.Surjective (lvl K h).p0 := by
  classical
  intro g
  refine ⟨fun T ↦ if hT : P T.obj then g ⟨T.obj, hT⟩ else 0, ?_⟩
  funext T
  show (if hT : P T.obj then g ⟨T.obj, hT⟩ else 0) = g T
  rw [dite_eq_left T.property]

theorem level_p1_surjective (K : Cx C) {P P' : ObjectProperty C} (h : P ≤ P') :
    Function.Surjective (lvl K h).p1 := by
  classical
  intro c
  refine ⟨(fun T T' φ ↦ if hT : P T.obj ∧ P T'.obj then
      c.1 ⟨T.obj, hT.1⟩ ⟨T'.obj, hT.2⟩ (ObjectProperty.homMk φ.hom) else 0,
    fun T ↦ if hT : P T.obj then c.2 ⟨T.obj, hT⟩ else 0), ?_⟩
  refine Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun φ ↦ ?_) (funext fun T ↦ ?_)
  · show (if hT : P T.obj ∧ P T'.obj then
      c.1 ⟨T.obj, hT.1⟩ ⟨T'.obj, hT.2⟩ (ObjectProperty.homMk φ.hom) else 0) = c.1 T T' φ
    rw [dite_eq_left ⟨T.property, T'.property⟩]; rfl
  · show (if hT : P T.obj then c.2 ⟨T.obj, hT⟩ else 0) = c.2 T
    rw [dite_eq_left T.property]

end Lvl

section Glue

variable {C : Type u} [Category.{0} C] {Q : ℕ → ObjectProperty C}

theorem ex2 (hQ : ∀ m n T, m ≤ n → Q m T → Q n T) (hex : ∀ T, ∃ n, Q n T) (T T' : C) :
    ∃ n, Q n T ∧ Q n T' := by
  obtain ⟨a, ha⟩ := hex T
  obtain ⟨b, hb⟩ := hex T'
  exact ⟨max a b, hQ _ _ _ (le_max_left _ _) ha, hQ _ _ _ (le_max_right _ _) hb⟩

theorem ex3 (hQ : ∀ m n T, m ≤ n → Q m T → Q n T) (hex : ∀ T, ∃ n, Q n T) (T T' T'' : C) :
    ∃ n, Q n T ∧ Q n T' ∧ Q n T'' := by
  obtain ⟨a, ha, ha'⟩ := ex2 hQ hex T T'
  obtain ⟨b, hb⟩ := hex T''
  exact ⟨max a b, hQ _ _ _ (le_max_left _ _) ha, hQ _ _ _ (le_max_left _ _) ha',
    hQ _ _ _ (le_max_right _ _) hb⟩

theorem ex4 (hQ : ∀ m n T, m ≤ n → Q m T → Q n T) (hex : ∀ T, ∃ n, Q n T) (T T' T'' T''' : C) :
    ∃ n, Q n T ∧ Q n T' ∧ Q n T'' ∧ Q n T''' := by
  obtain ⟨a, ha, ha', ha''⟩ := ex3 hQ hex T T' T''
  obtain ⟨b, hb⟩ := hex T'''
  exact ⟨max a b, hQ _ _ _ (le_max_left _ _) ha, hQ _ _ _ (le_max_left _ _) ha',
    hQ _ _ _ (le_max_left _ _) ha'', hQ _ _ _ (le_max_right _ _) hb⟩

variable (hQ : ∀ m n T, m ≤ n → Q m T → Q n T) (hex : ∀ T, ∃ n, Q n T) (M : Coef C)

def glue0 (g : ∀ n, (M.res (Q n).ι).c0) : M.c0 := fun T ↦
  g (hex T).choose ⟨T, (hex T).choose_spec⟩

def glue1 (g : ∀ n, (M.res (Q n).ι).c1) : M.c1 := fun T T' φ ↦
  g (ex2 hQ hex T T').choose ⟨T, (ex2 hQ hex T T').choose_spec.1⟩
    ⟨T', (ex2 hQ hex T T').choose_spec.2⟩ (ObjectProperty.homMk φ)

def glue2 (g : ∀ n, (M.res (Q n).ι).c2) : M.c2 := fun T T' T'' φ ψ ↦
  g (ex3 hQ hex T T' T'').choose ⟨T, (ex3 hQ hex T T' T'').choose_spec.1⟩
    ⟨T', (ex3 hQ hex T T' T'').choose_spec.2.1⟩ ⟨T'', (ex3 hQ hex T T' T'').choose_spec.2.2⟩
    (ObjectProperty.homMk φ) (ObjectProperty.homMk ψ)

include hQ in
theorem glueZeroCochain_apply_of_tower (g : ∀ n, (M.res (Q n).ι).c0)
    (hc : ∀ n (T : C) (h : Q n T) (k : Q (n + 1) T), g (n + 1) ⟨T, k⟩ = g n ⟨T, h⟩)
    (m : ℕ) (T : C) (h : Q m T) : glue0 hex M g T = g m ⟨T, h⟩ := by
  have mono : ∀ n m, n ≤ m → ∀ (T : C) (h : Q n T) (k : Q m T), g m ⟨T, k⟩ = g n ⟨T, h⟩ := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intros; rfl
    | succ m hnm ih =>
      intro T h k
      rw [hc m T (hQ _ _ _ hnm h) k]
      exact ih T h _
  have hn := (hex T).choose_spec
  exact (mono _ (max (hex T).choose m) (le_max_left _ _) T hn (hQ _ _ _ (le_max_right _ _) h)).symm.trans
    (mono m _ (le_max_right _ _) T h _)

theorem glueOneCochain_apply_of_tower (g : ∀ n, (M.res (Q n).ι).c1)
    (hc : ∀ n (T T' : C) (φ : T ⟶ T') (h : Q n T) (h' : Q n T') (k : Q (n + 1) T) (k' : Q (n + 1) T'),
      g (n + 1) ⟨T, k⟩ ⟨T', k'⟩ (ObjectProperty.homMk φ) = g n ⟨T, h⟩ ⟨T', h'⟩ (ObjectProperty.homMk φ))
    (m : ℕ) (T T' : C) (φ : T ⟶ T') (h : Q m T) (h' : Q m T') :
    glue1 hQ hex M g T T' φ = g m ⟨T, h⟩ ⟨T', h'⟩ (ObjectProperty.homMk φ) := by
  have mono : ∀ n m, n ≤ m → ∀ (T T' : C) (φ : T ⟶ T') (h : Q n T) (h' : Q n T') (k : Q m T) (k' : Q m T'),
      g m ⟨T, k⟩ ⟨T', k'⟩ (ObjectProperty.homMk φ) = g n ⟨T, h⟩ ⟨T', h'⟩ (ObjectProperty.homMk φ) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intros; rfl
    | succ m hnm ih =>
      intro T T' φ h h' k k'
      rw [hc m T T' φ (hQ _ _ _ hnm h) (hQ _ _ _ hnm h') k k']
      exact ih T T' φ h h' _ _
  have hn := (ex2 hQ hex T T').choose_spec
  exact (mono _ (max (ex2 hQ hex T T').choose m) (le_max_left _ _) T T' φ hn.1 hn.2
    (hQ _ _ _ (le_max_right _ _) h) (hQ _ _ _ (le_max_right _ _) h')).symm.trans
    (mono m _ (le_max_right _ _) T T' φ h h' _ _)

theorem glueTwoCochain_apply_of_tower (g : ∀ n, (M.res (Q n).ι).c2)
    (hc : ∀ n (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : Q n T) (h' : Q n T') (h'' : Q n T'')
      (k : Q (n + 1) T) (k' : Q (n + 1) T') (k'' : Q (n + 1) T''),
      g (n + 1) ⟨T, k⟩ ⟨T', k'⟩ ⟨T'', k''⟩ (ObjectProperty.homMk φ) (ObjectProperty.homMk ψ) =
        g n ⟨T, h⟩ ⟨T', h'⟩ ⟨T'', h''⟩ (ObjectProperty.homMk φ) (ObjectProperty.homMk ψ))
    (m : ℕ) (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : Q m T) (h' : Q m T') (h'' : Q m T'') :
    glue2 hQ hex M g T T' T'' φ ψ =
      g m ⟨T, h⟩ ⟨T', h'⟩ ⟨T'', h''⟩ (ObjectProperty.homMk φ) (ObjectProperty.homMk ψ) := by
  have mono : ∀ n m, n ≤ m → ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : Q n T) (h' : Q n T')
      (h'' : Q n T'') (k : Q m T) (k' : Q m T') (k'' : Q m T''),
      g m ⟨T, k⟩ ⟨T', k'⟩ ⟨T'', k''⟩ (ObjectProperty.homMk φ) (ObjectProperty.homMk ψ) =
        g n ⟨T, h⟩ ⟨T', h'⟩ ⟨T'', h''⟩ (ObjectProperty.homMk φ) (ObjectProperty.homMk ψ) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intros; rfl
    | succ m hnm ih =>
      intro T T' T'' φ ψ h h' h'' k k' k''
      rw [hc m T T' T'' φ ψ (hQ _ _ _ hnm h) (hQ _ _ _ hnm h') (hQ _ _ _ hnm h'') k k' k'']
      exact ih T T' T'' φ ψ h h' h'' _ _ _
  have hn := (ex3 hQ hex T T' T'').choose_spec
  exact (mono _ (max (ex3 hQ hex T T' T'').choose m) (le_max_left _ _) T T' T'' φ ψ hn.1 hn.2.1 hn.2.2
    (hQ _ _ _ (le_max_right _ _) h) (hQ _ _ _ (le_max_right _ _) h')
    (hQ _ _ _ (le_max_right _ _) h'')).symm.trans
    (mono m _ (le_max_right _ _) T T' T'' φ ψ h h' h'' _ _ _)

end Glue


open ObjectProperty in
theorem tower_two : ∀ (C : Type 1) [Category.{0} C] (D : Type) [Category.{0} D] (K : Cx C)
    (P : ℕ → ObjectProperty C) (ℓ : D ⥤ C) (N₀ : ℕ), (∀ m n T, m ≤ n → P m T → P n T) →
    (∀ T, ∃ n, P n T) → (∀ N, N₀ ≤ N → ∃ h : ∀ U, P N (ℓ.obj U),
      ((K.res (P N).ι).resMap ((P N).lift ℓ h)).Bij) → Function.Bijective (K.resMap ℓ).h2 := by
  intro C _ D _ K P ℓ N₀ hP hPex hB
  let Q : ℕ → ObjectProperty C := fun n ↦ P (N₀ + n)
  have hQ : ∀ m n T, m ≤ n → Q m T → Q n T := fun m n T h ↦ hP _ _ T (by omega)
  have hQex : ∀ T, ∃ n, Q n T := fun T ↦
    let ⟨n, hn⟩ := hPex T; ⟨n, hP _ _ _ (by omega) hn⟩
  have hB' : ∀ n, ∃ h : ∀ U, Q n (ℓ.obj U), ((K.res (Q n).ι).resMap ((Q n).lift ℓ h)).Bij :=
    fun n ↦ hB _ (by omega)
  choose hl hbij using hB'
  let μ : ∀ n, CxMap (K.res (Q n).ι) (K.res ℓ) := fun n ↦ (K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))
  have hμ : ∀ n, (Function.Injective (μ n).h1 ∧ Function.Surjective (μ n).h1) ∧
      (Function.Injective (μ n).h2 ∧ Function.Surjective (μ n).h2) := fun n ↦ (hbij n).2
  let ρ : ∀ n, CxMap (K.res (Q (n + 1)).ι) (K.res (Q n).ι) := fun n ↦
    lvl K (P := Q n) (P' := Q (n + 1)) (fun T hT ↦ hQ n (n + 1) T (Nat.le_succ n) hT)
  have hμρ1 : ∀ n x, (μ n).p1 ((ρ n).p1 x) = (μ (n + 1)).p1 x := fun n x ↦ rfl
  have hμρ2 : ∀ n x, (μ n).p2 ((ρ n).p2 x) = (μ (n + 1)).p2 x := fun n x ↦ rfl
  have hS2 : ∀ n, ∀ b ∈ (K.res (Q n).ι).Z2, ∃ b' ∈ (K.res (Q (n + 1)).ι).Z2, ∃ a,
      b = (ρ n).p2 b' + (K.res (Q n).ι).D1 a := by
    intro n b hb
    obtain ⟨b', hb', w, hw⟩ := surj2 (μ (n + 1)) (hμ (n + 1)).2.2 ((μ n).p2 b) ((μ n).p2_mem_Z2_of_mem_Z2 hb)
    have hz : (μ n).p2 (b - (ρ n).p2 b') = (K.res ℓ).D1 w := by
      rw [map_sub, hμρ2, hw]; abel
    obtain ⟨v, hv⟩ := inj2 (μ n) (hμ n).2.1 _ (sub_mem hb ((ρ n).p2_mem_Z2_of_mem_Z2 hb')) w hz
    exact ⟨b', hb', v, by rw [hv]; abel⟩
  have hS1 : ∀ n (a : (K.res (Q n).ι).T1), (K.res (Q n).ι).D1 a = 0 → ∃ a' w,
      (K.res (Q (n + 1)).ι).D1 a' = 0 ∧ a = (ρ n).p1 a' + (K.res (Q n).ι).D0 w := by
    intro n a ha
    obtain ⟨a', ha', w, hw⟩ := surj1 (μ (n + 1)) (hμ (n + 1)).1.2 ((μ n).p1 a) ((μ n).z1 ⟨a, ha⟩).2
    have hz : (μ n).p1 (a - (ρ n).p1 a') = (K.res ℓ).D0 w := by
      rw [map_sub, hμρ1, hw]; abel
    have hmem : a - (ρ n).p1 a' ∈ (K.res (Q n).ι).Z1 := sub_mem ha ((ρ n).z1 ⟨a', ha'⟩).2
    obtain ⟨v, hv⟩ := inj1 (μ n) (hμ n).1.1 _ hmem w hz
    exact ⟨a', v, ha', by rw [hv]; abel⟩
  apply h2_bijective_of_surj_of_inj_on_cocycles (K.resMap ℓ)
  · intro y hy
    obtain ⟨x, hx, w, hw⟩ := surj2 (μ 0) (hμ 0).2.2 y hy
    obtain ⟨b, hb0, hbZ, hbc⟩ := GlobalTheory.T.tower_complex_lift_and_extension_lemmas.2 (fun n ↦ (K.res (Q n).ι).T1)
      (fun n ↦ (K.res (Q n).ι).T2) (fun n ↦ (K.res (Q n).ι).Z2) (fun n ↦ (K.res (Q n).ι).D1)
      (fun n ↦ (ρ n).p1) (fun n ↦ (ρ n).p2) (fun n x ↦ first_diagonal_phase_mem_unitary _ x) (fun n x ↦ (ρ n).pullback_secondDifferential x)
      (fun n ↦ level_p1_surjective K _) (fun n x hx ↦ (ρ n).p2_mem_Z2_of_mem_Z2 hx) hS2 x hx
    have hc2 := fun (n : ℕ) (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') (h : Q n T) (h' : Q n T') (h'' : Q n T'') (_ : Q (n + 1) T) (_ : Q (n + 1) T') (_ : Q (n + 1) T'') ↦
      congrArg (fun q : (K.res (Q n).ι).T2 ↦ q.1 ⟨T, h⟩ ⟨T', h'⟩ ⟨T'', h''⟩ (homMk φ) (homMk ψ)) (hbc n)
    have hc1 := fun (n : ℕ) (T T' : C) (φ : T ⟶ T') (h : Q n T) (h' : Q n T') (_ : Q (n + 1) T) (_ : Q (n + 1) T') ↦
      congrArg (fun q : (K.res (Q n).ι).T2 ↦ q.2.1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ)) (hbc n)
    have hc0 := fun (n : ℕ) (T : C) (h : Q n T) (_ : Q (n + 1) T) ↦
      congrArg (fun q : (K.res (Q n).ι).T2 ↦ q.2.2 ⟨T, h⟩) (hbc n)
    have e2 := glueTwoCochain_apply_of_tower hQ hQex K.M0 (fun n ↦ (b n).1) hc2
    have e1 := glueOneCochain_apply_of_tower hQ hQex K.M1 (fun n ↦ (b n).2.1) hc1
    have e0 := glueZeroCochain_apply_of_tower hQ hQex K.M2 (fun n ↦ (b n).2.2) hc0
    refine ⟨(glue2 hQ hQex K.M0 (fun n ↦ (b n).1), glue1 hQ hQex K.M1 (fun n ↦ (b n).2.1),
      glue0 hQex K.M2 (fun n ↦ (b n).2.2)), ?_, w, ?_⟩
    · refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
      · obtain ⟨m, h1, h2, h3, h4⟩ := ex4 hQ hQex T T' T'' T'''
        dsimp only
        rw [e2 m T T' T'' φ ψ h1 h2 h3, e2 m T T'' T''' (φ ≫ ψ) χ h1 h3 h4, e2 m T T' T''' φ (ψ ≫ χ) h1 h2 h4,
          e2 m T' T'' T''' ψ χ h2 h3 h4]
        exact (hbZ m).1 ⟨T, h1⟩ ⟨T', h2⟩ ⟨T'', h3⟩ ⟨T''', h4⟩ (homMk φ) (homMk ψ) (homMk χ)
      · obtain ⟨m, h1, h2, h3⟩ := ex3 hQ hQex T T' T''
        dsimp only
        rw [e1 m T T'' (φ ≫ ψ) h1 h3, e1 m T T' φ h1 h2, e1 m T' T'' ψ h2 h3, e2 m T T' T'' φ ψ h1 h2 h3]
        exact (hbZ m).2.1 ⟨T, h1⟩ ⟨T', h2⟩ ⟨T'', h3⟩ (homMk φ) (homMk ψ)
      · obtain ⟨m, h1, h2⟩ := ex2 hQ hQex T T'
        dsimp only
        rw [e0 m T' h2, e0 m T h1, e1 m T T' φ h1 h2]
        exact (hbZ m).2.2.1 ⟨T, h1⟩ ⟨T', h2⟩ (homMk φ)
      · obtain ⟨m, h1⟩ := hQex T
        dsimp only
        rw [e0 m T h1]
        exact (hbZ m).2.2.2 ⟨T, h1⟩
    · have hp : (K.resMap ℓ).p2 (glue2 hQ hQex K.M0 (fun n ↦ (b n).1), glue1 hQ hQex K.M1 (fun n ↦ (b n).2.1),
          glue0 hQex K.M2 (fun n ↦ (b n).2.2)) = (μ 0).p2 (b 0) := by
        refine Prod.ext (funext fun U ↦ funext fun U' ↦ funext fun U'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_)
          (Prod.ext (funext fun U ↦ funext fun U' ↦ funext fun φ ↦ ?_) (funext fun U ↦ ?_))
        · exact e2 0 _ _ _ (ℓ.map φ) (ℓ.map ψ) (hl 0 U) (hl 0 U') (hl 0 U'')
        · exact e1 0 _ _ (ℓ.map φ) (hl 0 U) (hl 0 U')
        · exact e0 0 _ (hl 0 U)
      rw [hp, hb0]; exact hw
  · intro x hx w hw
    let bx : ∀ n, (K.res (Q n).ι).T2 := fun n ↦ (K.resMap (Q n).ι).p2 x
    have hbx : ∀ n, ∃ a, (K.res (Q n).ι).D1 a = bx n := fun n ↦
      inj2 (μ n) (hμ n).2.1 (bx n) ((K.resMap (Q n).ι).p2_mem_Z2_of_mem_Z2 hx) w hw
    obtain ⟨a, hac, had⟩ := GlobalTheory.T.tower_complex_lift_and_extension_lemmas.1 (fun n ↦ (K.res (Q n).ι).M0.c0) (fun n ↦ (K.res (Q n).ι).T1)
      (fun n ↦ (K.res (Q n).ι).T2) (fun n ↦ (K.res (Q n).ι).D0) (fun n ↦ (K.res (Q n).ι).D1)
      (fun n ↦ (ρ n).p0) (fun n ↦ (ρ n).p1) (fun n ↦ (ρ n).p2) (fun n x ↦ cx_D1_D0_eq_zero _ x)
      (fun n x ↦ (ρ n).pullback_firstDifferential x) (fun n x ↦ (ρ n).pullback_secondDifferential x) (fun n ↦ level_p0_surjective K _) hS1 bx
      (fun n ↦ rfl) (fun n ↦ hbx n)
    have hc1 := fun (n : ℕ) (T T' : C) (φ : T ⟶ T') (h : Q n T) (h' : Q n T') (_ : Q (n + 1) T) (_ : Q (n + 1) T') ↦
      congrArg (fun q : (K.res (Q n).ι).T1 ↦ q.1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ)) (hac n)
    have hc0 := fun (n : ℕ) (T : C) (h : Q n T) (_ : Q (n + 1) T) ↦
      congrArg (fun q : (K.res (Q n).ι).T1 ↦ q.2 ⟨T, h⟩) (hac n)
    have e1 := glueOneCochain_apply_of_tower hQ hQex K.M0 (fun n ↦ (a n).1) hc1
    have e0 := glueZeroCochain_apply_of_tower hQ hQex K.M1 (fun n ↦ (a n).2) hc0
    refine ⟨(glue1 hQ hQex K.M0 (fun n ↦ (a n).1), glue0 hQex K.M1 (fun n ↦ (a n).2)), ?_⟩
    refine Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_)
      (Prod.ext (funext fun T ↦ funext fun T' ↦ funext fun φ ↦ ?_) (funext fun T ↦ ?_))
    · obtain ⟨m, h1, h2, h3⟩ := ex3 hQ hQex T T' T''
      simp only [Cx.D1, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [e1 m T T' φ h1 h2, e1 m T T'' (φ ≫ ψ) h1 h3, e1 m T' T'' ψ h2 h3]
      exact congrArg (fun q : (K.res (Q m).ι).T2 ↦ q.1 ⟨T, h1⟩ ⟨T', h2⟩ ⟨T'', h3⟩ (homMk φ) (homMk ψ)) (had m)
    · obtain ⟨m, h1, h2⟩ := ex2 hQ hQex T T'
      simp only [Cx.D1, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [e0 m T' h2, e0 m T h1, e1 m T T' φ h1 h2]
      exact congrArg (fun q : (K.res (Q m).ι).T2 ↦ q.2.1 ⟨T, h1⟩ ⟨T', h2⟩ (homMk φ)) (had m)
    · obtain ⟨m, h1⟩ := hQex T
      simp only [Cx.D1, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [e0 m T h1]
      exact congrArg (fun q : (K.res (Q m).ι).T2 ↦ q.2.2 ⟨T, h1⟩) (had m)

end GlobalTheory.CxTowerTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRestrictionFourTermComplexOfExhaustionStatement
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_restriction_fourTermComplex_of_exhaustion : ∀ (C : Type 1) [Category.{0} C] (D : Type) [Category.{0} D] (K : Cx C) (P : ℕ → ObjectProperty C) (ℓ : D ⥤ C) (N₀ : ℕ), (∀ m n T, m ≤ n → P m T → P n T) → (∀ T, ∃ n, P n T) → (∀ N, N₀ ≤ N → ∃ h : ∀ U, P N (ℓ.obj U), ((K.res (P N).ι).resMap ((P N).lift ℓ h)).Bij) → Function.Bijective (K.resMap ℓ).h2 := by
  first | exact @GlobalTheory.CxTowerTwo.tower_two | exact GlobalTheory.CxTowerTwo.tower_two | (intros; apply GlobalTheory.CxTowerTwo.tower_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1BijectiveOfExhaustingFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1BijectiveOfExhaustingFiltration
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.TowerOne

universe u u'

variable {C : Type u} [Category.{0} C] {C' : Type u'} [Category.{0} C'] {K : Cx C} {K' : Cx C'}

theorem exists_cocycle_of_h0_surjective (m : CxMap K K') (hm : Function.Surjective m.h0) (g' : K'.M0.c0)
    (hg : K'.D0 g' = 0) : ∃ g, K.D0 g = 0 ∧ m.p0 g = g' := by
  obtain ⟨⟨g, hg0⟩, h⟩ := hm ⟨g', hg⟩
  exact ⟨g, hg0, congrArg Subtype.val h⟩

theorem exists_primitive_of_h1_injective (m : CxMap K K') (hm : Function.Injective m.h1) (z : K.T1) (hz : z ∈ K.Z1)
    (g : K'.M0.c0) (h : m.p1 z = K'.D0 g) : ∃ g', K.D0 g' = z := by
  have h0 : m.h1 (QuotientAddGroup.mk ⟨z, hz⟩ : K.H1) = 0 := by
    change (QuotientAddGroup.mk (m.z1 ⟨z, hz⟩) : K'.H1) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨g, h.symm⟩
  have h1 := hm (h0.trans (map_zero m.h1).symm)
  rw [QuotientAddGroup.eq_zero_iff] at h1
  exact h1

theorem exists_cocycle_of_h1_surjective (m : CxMap K K') (hm : Function.Surjective m.h1) (z' : K'.T1)
    (hz : z' ∈ K'.Z1) : ∃ z ∈ K.Z1, ∃ g, z' = m.p1 z + K'.D0 g := by
  obtain ⟨x, hx⟩ := hm (QuotientAddGroup.mk ⟨z', hz⟩)
  obtain ⟨⟨z, hz1⟩, rfl⟩ := QuotientAddGroup.mk_surjective x
  change (QuotientAddGroup.mk (m.z1 ⟨z, hz1⟩) : K'.H1) = _ at hx
  rw [QuotientAddGroup.eq] at hx
  obtain ⟨g, hg⟩ := hx
  refine ⟨z, hz1, g, ?_⟩
  have e : K'.D0 g = -m.p1 z + z' := hg
  rw [e]; abel

theorem cx_D1_D0_eq_zero (K : Cx C) (g : K.M0.c0) : K.D1 (K.D0 g) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ
    simp only [Cx.D1, Cx.D0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sub, K.M0.map_comp,
      Prod.fst_zero, Pi.zero_apply]
    abel
  · funext T T' φ
    simp only [Cx.D1, Cx.D0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sub, K.diffZero_natural,
      Prod.snd_zero, Prod.fst_zero, Pi.zero_apply]
    abel
  · funext T
    simp only [Cx.D1, Cx.D0, AddMonoidHom.coe_mk, ZeroHom.coe_mk, K.diffOne_diffZero, Prod.snd_zero, Pi.zero_apply]

end GlobalTheory.CxCoh.TowerOne

namespace GlobalTheory.CxCoh.TowerOne

open ObjectProperty

variable {C : Type 1} [Category.{0} C]

theorem tower (K : Cx C) (Q : ℕ → ObjectProperty C) (hQ : ∀ n, Q n ≤ Q (n + 1))
    (hex : ∀ T, ∃ n, Q n T)
    (h0s : ∀ n, Function.Surjective ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).h0)
    (h1b : ∀ n, Function.Bijective ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).h1) :
    Function.Bijective (K.resMap (Q 0).ι).h1 := by
  have ml := GlobalTheory.T.tower_complex_lift_and_extension_lemmas
  have hle : ∀ n k T, Q n T → Q (n + k) T := by
    intro n k T h
    induction k with
    | zero => exact h
    | succ k ih => exact hQ (n + k) T ih
  have hle' : ∀ n m, n ≤ m → ∀ T, Q n T → Q m T := by
    intro n m hnm T h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact hle n k T h
  have hex2 : ∀ T T', ∃ n, Q n T ∧ Q n T' := by
    intro T T'
    obtain ⟨n, h⟩ := hex T
    obtain ⟨n', h'⟩ := hex T'
    exact ⟨max n n', hle' _ _ (le_max_left _ _) _ h, hle' _ _ (le_max_right _ _) _ h'⟩
  have hex3 : ∀ T T' T'', ∃ n, Q n T ∧ Q n T' ∧ Q n T'' := by
    intro T T' T''
    obtain ⟨n, h, h'⟩ := hex2 T T'
    obtain ⟨n', h''⟩ := hex T''
    exact ⟨max n n', hle' _ _ (le_max_left _ _) _ h, hle' _ _ (le_max_left _ _) _ h',
      hle' _ _ (le_max_right _ _) _ h''⟩
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hx' : (K.resMap (Q 0).ι).p1 z ∈ (K.res (Q 0).ι).D0.range := by
      change (QuotientAddGroup.mk ((K.resMap (Q 0).ι).z1 ⟨z, hz⟩) : (K.res (Q 0).ι).H1) = 0 at hx
      rw [QuotientAddGroup.eq_zero_iff] at hx
      exact hx
    have hb : ∀ n, ∃ a, (K.res (Q n).ι).D0 a = (K.resMap (Q n).ι).p1 z := by
      intro n
      induction n with
      | zero => exact hx'
      | succ n ih =>
        obtain ⟨g, hg⟩ := ih
        exact exists_primitive_of_h1_injective _ (h1b n).1 ((K.resMap (Q (n + 1)).ι).p1 z)
          ((K.resMap (Q (n + 1)).ι).z1 ⟨z, hz⟩).2 g hg.symm
    obtain ⟨a, has, had⟩ := ml.1 (fun _ ↦ PUnit) (fun n ↦ (K.res (Q n).ι).M0.c0)
      (fun n ↦ (K.res (Q n).ι).T1) (fun _ ↦ 0) (fun n ↦ (K.res (Q n).ι).D0) (fun _ ↦ 0)
      (fun n ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).p0)
      (fun n ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).p1)
      (fun n x ↦ by simp) (fun n x ↦ by simp)
      (fun n x ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).pullback_firstDifferential x)
      (fun n x ↦ ⟨PUnit.unit, Subsingleton.elim _ _⟩)
      (fun n a ha ↦ by
        obtain ⟨g, hg0, hg⟩ := exists_cocycle_of_h0_surjective _ (h0s n) a ha
        exact ⟨g, 0, hg0, by simpa using hg.symm⟩)
      (fun n ↦ (K.resMap (Q n).ι).p1 z) (fun n ↦ rfl) hb
    have hs : ∀ j (X : (Q j).FullSubcategory), a (j + 1) ⟨X.obj, hQ j _ X.property⟩ = a j X :=
      fun j X ↦ congrFun (has j) X
    have ha_le : ∀ n k T (h : Q n T) (h' : Q (n + k) T), a (n + k) ⟨T, h'⟩ = a n ⟨T, h⟩ := by
      intro n k T h h'
      induction k with
      | zero => rfl
      | succ k ih => exact (hs (n + k) ⟨T, hle n k T h⟩).trans (ih _)
    have ha_any : ∀ n m T (h : Q n T) (h' : Q m T), a n ⟨T, h⟩ = a m ⟨T, h'⟩ := by
      intro n m T h h'
      rcases le_total n m with hnm | hmn
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
        exact (ha_le n k T h h').symm
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        exact ha_le m k T h' h
    let g : K.M0.c0 := fun T ↦ a (Classical.choose (hex T)) ⟨T, Classical.choose_spec (hex T)⟩
    have hg : ∀ n T (h : Q n T), g T = a n ⟨T, h⟩ := fun n T h ↦ ha_any _ _ _ _ _
    have hgz : K.D0 g = z := by
      refine Prod.ext ?_ ?_
      · funext T T' φ
        obtain ⟨n, h, h'⟩ := hex2 T T'
        have e := congrArg (fun w ↦ w.1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ)) (had n)
        show g T' - K.M0.map φ (g T) = z.1 T T' φ
        rw [hg n T h, hg n T' h']
        exact e
      · funext T
        obtain ⟨n, h⟩ := hex T
        have e := congrArg (fun w ↦ w.2 ⟨T, h⟩) (had n)
        show K.d0 T (g T) = z.2 T
        rw [hg n T h]
        exact e
    change (QuotientAddGroup.mk ⟨z, hz⟩ : K.H1) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨g, hgz⟩
  · intro y
    obtain ⟨⟨z0, hz0⟩, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨b, hb0, hbZ, hbt⟩ := ml.2 (fun n ↦ (K.res (Q n).ι).M0.c0) (fun n ↦ (K.res (Q n).ι).T1)
      (fun n ↦ (K.res (Q n).ι).Z1) (fun n ↦ (K.res (Q n).ι).D0)
      (fun n ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).p0)
      (fun n ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).p1)
      (fun n x ↦ cx_D1_D0_eq_zero _ x)
      (fun n x ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).pullback_firstDifferential x)
      (fun n g ↦ by
        classical
        refine ⟨fun X ↦ if h : Q n X.obj then g ⟨X.obj, h⟩ else 0, ?_⟩
        funext X
        show (if h : Q n X.obj then g ⟨X.obj, h⟩ else 0) = g X
        rw [dite_eq_left X.property])
      (fun n x hx ↦ (((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).z1 ⟨x, hx⟩).2)
      (fun n b hb ↦ by
        obtain ⟨z, hz, g, e⟩ := exists_cocycle_of_h1_surjective _ (h1b n).2 b hb
        exact ⟨z, hz, g, e⟩)
      z0 hz0
    have hb1 : ∀ j (X Y : (Q j).FullSubcategory) (f : X ⟶ Y),
        (b (j + 1)).1 ⟨X.obj, hQ j _ X.property⟩ ⟨Y.obj, hQ j _ Y.property⟩ (homMk f.hom) = (b j).1 X Y f :=
      fun j X Y f ↦ congrArg (fun w ↦ w.1 X Y f) (hbt j)
    have hb2 : ∀ j (X : (Q j).FullSubcategory), (b (j + 1)).2 ⟨X.obj, hQ j _ X.property⟩ = (b j).2 X :=
      fun j X ↦ congrArg (fun w ↦ w.2 X) (hbt j)
    have hb1_le : ∀ n k T T' (h : Q n T) (h' : Q n T') (h2 : Q (n + k) T) (h2' : Q (n + k) T') (φ : T ⟶ T'),
        (b (n + k)).1 ⟨T, h2⟩ ⟨T', h2'⟩ (homMk φ) = (b n).1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ) := by
      intro n k T T' h h' h2 h2' φ
      induction k with
      | zero => rfl
      | succ k ih => exact (hb1 (n + k) ⟨T, hle n k T h⟩ ⟨T', hle n k T' h'⟩ (homMk φ)).trans (ih _ _)
    have hb2_le : ∀ n k T (h : Q n T) (h2 : Q (n + k) T), (b (n + k)).2 ⟨T, h2⟩ = (b n).2 ⟨T, h⟩ := by
      intro n k T h h2
      induction k with
      | zero => rfl
      | succ k ih => exact (hb2 (n + k) ⟨T, hle n k T h⟩).trans (ih _)
    have hb1_any : ∀ n m T T' (h : Q n T) (h' : Q n T') (h2 : Q m T) (h2' : Q m T') (φ : T ⟶ T'),
        (b n).1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ) = (b m).1 ⟨T, h2⟩ ⟨T', h2'⟩ (homMk φ) := by
      intro n m T T' h h' h2 h2' φ
      rcases le_total n m with hnm | hmn
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
        exact (hb1_le n k T T' h h' h2 h2' φ).symm
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        exact hb1_le m k T T' h2 h2' h h' φ
    have hb2_any : ∀ n m T (h : Q n T) (h2 : Q m T), (b n).2 ⟨T, h⟩ = (b m).2 ⟨T, h2⟩ := by
      intro n m T h h2
      rcases le_total n m with hnm | hmn
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
        exact (hb2_le n k T h h2).symm
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        exact hb2_le m k T h2 h
    let c : K.T1 := (fun T T' φ ↦ (b (Classical.choose (hex2 T T'))).1
        ⟨T, (Classical.choose_spec (hex2 T T')).1⟩ ⟨T', (Classical.choose_spec (hex2 T T')).2⟩ (homMk φ),
      fun T ↦ (b (Classical.choose (hex T))).2 ⟨T, Classical.choose_spec (hex T)⟩)
    have hc1 : ∀ n T T' (h : Q n T) (h' : Q n T') (φ : T ⟶ T'),
        c.1 T T' φ = (b n).1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ) := fun n T T' h h' φ ↦ hb1_any _ _ _ _ _ _ _ _ _
    have hc2 : ∀ n T (h : Q n T), c.2 T = (b n).2 ⟨T, h⟩ := fun n T h ↦ hb2_any _ _ _ _ _
    have hc : c ∈ K.Z1 := by
      show K.D1 c = 0
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · funext T T' T'' φ ψ
        obtain ⟨n, h, h', h''⟩ := hex3 T T' T''
        have e := congrArg (fun w ↦ w.1 ⟨T, h⟩ ⟨T', h'⟩ ⟨T'', h''⟩ (homMk φ) (homMk ψ))
          (hbZ n : (K.res (Q n).ι).D1 (b n) = 0)
        show K.M0.map ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ = 0
        rw [hc1 n T T' h h', hc1 n T T'' h h'', hc1 n T' T'' h' h'']
        exact e
      · funext T T' φ
        obtain ⟨n, h, h'⟩ := hex2 T T'
        have e := congrArg (fun w ↦ w.2.1 ⟨T, h⟩ ⟨T', h'⟩ (homMk φ))
          (hbZ n : (K.res (Q n).ι).D1 (b n) = 0)
        show c.2 T' - K.M1.map φ (c.2 T) - K.d0 T' (c.1 T T' φ) = 0
        rw [hc1 n T T' h h', hc2 n T h, hc2 n T' h']
        exact e
      · funext T
        obtain ⟨n, h⟩ := hex T
        have e := congrArg (fun w ↦ w.2.2 ⟨T, h⟩) (hbZ n : (K.res (Q n).ι).D1 (b n) = 0)
        show K.d1 T (c.2 T) = 0
        rw [hc2 n T h]
        exact e
    refine ⟨QuotientAddGroup.mk ⟨c, hc⟩, ?_⟩
    change (QuotientAddGroup.mk ((K.resMap (Q 0).ι).z1 ⟨c, hc⟩) : (K.res (Q 0).ι).H1) = _
    congr 1
    apply Subtype.ext
    show (K.resMap (Q 0).ι).p1 c = z0
    rw [← hb0]
    refine Prod.ext ?_ ?_
    · funext X Y f
      exact hc1 0 X.obj Y.obj X.property Y.property f.hom
    · funext X
      exact hc2 0 X.obj X.property

end GlobalTheory.CxCoh.TowerOne

namespace GlobalTheory.CxCoh

open ObjectProperty

theorem restriction_h1_bijective_of_exhaustion : ∀ (C : Type 1) [Category.{0} C] (D : Type) [Category.{0} D] (K : Cx C)
    (P : ℕ → ObjectProperty C) (ℓ : D ⥤ C) (N₀ : ℕ), (∀ m n T, m ≤ n → P m T → P n T) →
    (∀ T, ∃ n, P n T) →
    (∀ N, N₀ ≤ N → ∃ h : ∀ U, P N (ℓ.obj U), ((K.res (P N).ι).resMap ((P N).lift ℓ h)).Bij) →
    Function.Bijective (K.resMap ℓ).h1 := by
  intro C _ D _ K P ℓ N₀ hmono hex hB
  let Q : ℕ → ObjectProperty C := fun n ↦ P (N₀ + n)
  have hQ : ∀ n, Q n ≤ Q (n + 1) := fun n T h ↦ hmono _ _ T (Nat.le_succ _) h
  have hex' : ∀ T, ∃ n, Q n T := fun T ↦
    let ⟨n, h⟩ := hex T
    ⟨n, hmono _ _ T (Nat.le_add_left n N₀) h⟩
  have hB' : ∀ n, ∃ h : ∀ U, Q n (ℓ.obj U), ((K.res (Q n).ι).resMap ((Q n).lift ℓ h)).Bij :=
    fun n ↦ hB (N₀ + n) (Nat.le_add_right _ _)
  choose hl hbij using hB'
  have key : ∀ n, Function.Surjective ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).h0 ∧
      Function.Bijective ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).h1 := by
    intro n
    have e0 : ∀ c, ((K.res (Q (n + 1)).ι).resMap ((Q (n + 1)).lift ℓ (hl (n + 1)))).h0 c =
        ((K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))).h0
          (((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).h0 c) :=
      fun c ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).cohomZero_pullback_comp
        ((K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))) c
    have e1 : ∀ c, ((K.res (Q (n + 1)).ι).resMap ((Q (n + 1)).lift ℓ (hl (n + 1)))).h1 c =
        ((K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))).h1
          (((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).h1 c) :=
      fun c ↦ ((K.res (Q (n + 1)).ι).resMap (ιOfLE (hQ n))).cohomOne_pullback_comp
        ((K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))) c
    have A0 := (hbij (n + 1)).1
    have B0 := (hbij n).1
    have A1 := (hbij (n + 1)).2.1
    have B1 := (hbij n).2.1
    refine ⟨fun y ↦ ?_, fun a b hab ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨c, hc⟩ := A0.2 (((K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))).h0 y)
      exact ⟨c, B0.1 ((e0 c).symm.trans hc)⟩
    · apply A1.1
      rw [e1, e1, hab]
    · obtain ⟨c, hc⟩ := A1.2 (((K.res (Q n).ι).resMap ((Q n).lift ℓ (hl n))).h1 y)
      exact ⟨c, B1.1 ((e1 c).symm.trans hc)⟩
  have e : ⇑(K.resMap ℓ).h1 =
      ((K.res (Q 0).ι).resMap ((Q 0).lift ℓ (hl 0))).h1 ∘ (K.resMap (Q 0).ι).h1 :=
    funext fun c ↦ (K.resMap (Q 0).ι).cohomOne_pullback_comp ((K.res (Q 0).ι).resMap ((Q 0).lift ℓ (hl 0))) c
  rw [e]
  exact (hbij 0).2.1.comp
    (TowerOne.tower K Q hQ hex' (fun n ↦ (key n).1) (fun n ↦ (key n).2))

end GlobalTheory.CxCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1BijectiveOfExhaustingFiltrationStatement
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1_resMap_bijective_of_exhausting_properties : ∀ (C : Type 1) [Category.{0} C] (D : Type) [Category.{0} D] (K : Cx C) (P : ℕ → ObjectProperty C) (ℓ : D ⥤ C) (N₀ : ℕ), (∀ m n T, m ≤ n → P m T → P n T) → (∀ T, ∃ n, P n T) → (∀ N, N₀ ≤ N → ∃ h : ∀ U, P N (ℓ.obj U), ((K.res (P N).ι).resMap ((P N).lift ℓ h)).Bij) → Function.Bijective (K.resMap ℓ).h1 := by
  first | exact @GlobalTheory.CxCoh.restriction_h1_bijective_of_exhaustion | exact GlobalTheory.CxCoh.restriction_h1_bijective_of_exhaustion | (intros; apply GlobalTheory.CxCoh.restriction_h1_bijective_of_exhaustion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRestrictionBijectiveLowDegrees
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem resMap_bij12_of_fnMap {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (K : Cx C) (G : C' ⥤ C)
    (h : K.fnMap.PullbackBijectiveDegreesOneTwo) (h' : (K.res G).fnMap.PullbackBijectiveDegreesOneTwo) (h₀ : ((Cx.single K.M0).resMap G).PullbackBijectiveDegreesOneTwo) :
    (K.resMap G).PullbackBijectiveDegreesOneTwo := by
  constructor
  · have e : (K.res G).fnMap.h1 ∘ (K.resMap G).h1 = ((Cx.single K.M0).resMap G).h1 ∘ K.fnMap.h1 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact (Function.Bijective.of_comp_iff' h'.1 _).1 (e ▸ h₀.1.comp h.1)
  · have e : (K.res G).fnMap.h2 ∘ (K.resMap G).h2 = ((Cx.single K.M0).resMap G).h2 ∘ K.fnMap.h2 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact (Function.Bijective.of_comp_iff' h'.2 _).1 (e ▸ h₀.2.comp h.2)

theorem resMap_comp_bij12 {C C' : Type 1} {C'' : Type} [Category.{0} C] [Category.{0} C'] [Category.{0} C'']
    (K : Cx C) (G : C' ⥤ C) (H : C'' ⥤ C') (h : (K.resMap G).PullbackBijectiveDegreesOneTwo) (h' : ((K.res G).resMap H).PullbackBijectiveDegreesOneTwo) :
    (K.resMap (H ⋙ G)).PullbackBijectiveDegreesOneTwo := by
  constructor
  · have e : ⇑(K.resMap (H ⋙ G)).h1 = ((K.res G).resMap H).h1 ∘ (K.resMap G).h1 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact e ▸ h'.1.comp h.1
  · have e : ⇑(K.resMap (H ⋙ G)).h2 = ((K.res G).resMap H).h2 ∘ (K.resMap G).h2 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact e ▸ h'.2.comp h.2

theorem Lift.resMap_toE_pullbackBijectiveDegreesOneTwo (D : Data) (Λ : Lift D) :
    (((KK D.κ D.t).res (pE D.κ D.t D.i)).resMap Λ.toE).PullbackBijectiveDegreesOneTwo := by
  obtain ⟨N₀, hN₀⟩ := (GlobalTheory.T.hom_spec_points_levels D Λ).2.2.2
  have mono : ∀ m n T, m ≤ n → LevE D.κ D.t D.i m T → LevE D.κ D.t D.i n T := fun m n T hmn hT ↦
    le_bot_iff.1 (((fil_properties _ _ T.obj.T.δ).2.2.1 m n hmn).trans (le_of_eq hT))
  have exh : ∀ T, ∃ n, LevE D.κ D.t D.i n T := fun T ↦ (isDPNilpotent_iff_exists_isLevel T.obj.T.δ).1 T.obj.T.nil
  have lev : ∀ N, N₀ + 1 ≤ N → ∃ h : ∀ U, LevE D.κ D.t D.i N (Λ.toE.obj U),
      ((((KK D.κ D.t).res (pE D.κ D.t D.i)).res (LevE D.κ D.t D.i N).ι).resMap
        ((LevE D.κ D.t D.i N).lift Λ.toE h)).Bij := by
    intro N hN
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    exact ⟨fun U ↦ hN₀ _ (by omega) U, GlobalTheory.T.crystallineForms_restriction_affineLift_bijective D Λ n _⟩
  exact ⟨GlobalTheory.T.h1_resMap_bijective_of_exhausting_properties _ _ _ _ Λ.toE (N₀ + 1) mono exh lev, GlobalTheory.T.bijective_restriction_fourTermComplex_of_exhaustion _ _ _ _ Λ.toE (N₀ + 1) mono exh lev⟩

theorem Lift.resMap_lift_pullbackBijectiveDegreesOneTwo : ∀ (D : Data) (Λ : Lift D), ((KK D.κ D.t).resMap Λ.L).PullbackBijectiveDegreesOneTwo := by
  intro D Λ
  have hp := GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res D.R D.I D.κ _ D.t _ D.i
  have hg := GlobalTheory.T.pullbackBijective12_resMap_of_affine_inter D.R D.I D.κ _ D.t _ D.i D.smooth_mono_inf.2.2
  exact resMap_comp_bij12 (KK D.κ D.t) (pE D.κ D.t D.i) Λ.toE
    (resMap_bij12_of_fnMap _ _ hp.1 hp.2 hg) (Lift.resMap_toE_pullbackBijectiveDegreesOneTwo D Λ)

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRestrictionBijectiveLowDegreesStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_restriction_bijective_low_degrees : ∀ (D : Data) (Λ : Lift D), ((KK D.κ D.t).resMap Λ.L).PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.PDForm.Lift.resMap_lift_pullbackBijectiveDegreesOneTwo | exact GlobalTheory.PDForm.Lift.resMap_lift_pullbackBijectiveDegreesOneTwo | (intros; apply GlobalTheory.PDForm.Lift.resMap_lift_pullbackBijectiveDegreesOneTwo <;> assumption)
end
