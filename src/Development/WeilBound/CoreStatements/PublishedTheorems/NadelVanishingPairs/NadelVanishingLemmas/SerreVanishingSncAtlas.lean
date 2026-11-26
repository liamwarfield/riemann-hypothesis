module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MemChartFormsIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemSpanFormsOfMulMem
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

namespace GlobalTheory.LogDR

theorem smul_mem_spanForms_of_mul_mem {K : Type} [Field K] {M M' : Set K} {H : Set Ω[K⁄ℤ]} {a : ℕ} (g : K)
    (hg : ∀ c ∈ M, g * c ∈ M') {η : abelian₂ K} (hη : η ∈ spanForms M H a) :
    g • η ∈ spanForms M' H a := by
  induction hη using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [smul_smul]
    exact AddSubgroup.subset_closure ⟨g * c, hg c hc, v, hv, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_logAt_add_iff {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (G D : CartierDiv X) (a : ℕ)
    (y : X) (g : X.functionFieldˣ) (η : abelian₂ X.functionField) (hD : D.IsEqn y g) :
    η ∈ logAt Z (G + D) a y ↔ (g : X.functionField) • η ∈ logAt Z G a y := by
  obtain ⟨e, hG⟩ := G.exists_isEqn y
  have hGD := hG.add hD
  constructor
  · intro h
    refine smul_mem_spanForms_of_mul_mem _ (fun c hc => ?_) h
    change G.RegularAt y _
    change (G + D).RegularAt y c at hc
    rw [hG.regularAt_iff]
    rw [hGD.regularAt_iff, Units.val_mul] at hc
    convert hc using 1
    ring
  · intro h
    have h' := smul_mem_spanForms_of_mul_mem (M' := {c | (G + D).RegularAt y c}) (g : X.functionField)⁻¹
      (fun c hc => ?_) h
    · rwa [inv_smul_smul₀ g.ne_zero] at h'
    · change (G + D).RegularAt y _
      change G.RegularAt y c at hc
      rw [hGD.regularAt_iff, Units.val_mul]
      rw [hG.regularAt_iff] at hc
      convert hc using 1
      field_simp

theorem logtwist : ∀ (X : Scheme.{0}) [IsIntegral X] (Z : Set X) (G D : CartierDiv X) (a : ℕ) (y : X)
    (g : X.functionFieldˣ) (η : abelian₂ X.functionField), D.IsEqn y g →
    (η ∈ logAt Z (G + D) a y ↔ (g : X.functionField) • η ∈ logAt Z G a y) :=
  fun X _ Z G D a y g η hD => mem_logAt_add_iff Z G D a y g η hD

end GlobalTheory.LogDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLatModelTwist
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

namespace LatTwist

open GlobalTheory.Twist

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M M' : X → AddSubgroup V} {F : X.Modules} {L : LB X} {r : L.ι → X.functionFieldˣ}

theorem sec_eq_of_not_gen {W : X.Opens} (hW : genericPoint X ∉ W) (s t : Γ(F, W)) : s = t :=
  sec_ext_of_cover (ι := PEmpty.{1}) (fun k => k.elim) (fun k => k.elim)
    (by intro x hx; exact (hW (gen_mem hx)).elim) (fun k => k.elim)

theorem val_resM (hM : LatModel M F) {U W : X.Opens} (e : W ≤ U) (h : genericPoint X ∈ W)
    (s : Γ(F, U)) : hM.val W h (resM F e s) = hM.val U (e h) s :=
  hM.res U W e h s


variable (r) in
def tval (hM : LatModel M F) (i : L.ι) (hi : genericPoint X ∈ L.U i) (U : X.Opens)
    (h : genericPoint X ∈ U) : Γ(twist F L, U) →+ V where
  toFun s := (r i)⁻¹ • hM.val (U ⊓ L.U i) (memInf h hi) (coord s i)
  map_zero' := by rw [coord_zero, map_zero, smul_zero]
  map_add' s t := by rw [coord_add, map_add (f := _), smul_add]

theorem tval_apply (hM : LatModel M F) (i : L.ι) (hi : genericPoint X ∈ L.U i) (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(twist F L, U)) :
    tval r hM i hi U h s = (r i)⁻¹ • hM.val (U ⊓ L.U i) (memInf h hi) (coord s i) := rfl

theorem val_coord_rel (hM : LatModel M F) {U : X.Opens} (s : Γ(twist F L, U)) (i j : L.ι)
    (hU : genericPoint X ∈ U) (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j) :
    hM.val (U ⊓ L.U i) (memInf hU hi) (coord s i) =
      fnOf (L.U i ⊓ L.U j) (memInf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) •
        hM.val (U ⊓ L.U j) (memInf hU hj) (coord s j) := by
  have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j := memInf (memInf hU hi) hj
  have e := coord_rel s i j (W := U ⊓ L.U i ⊓ L.U j) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (inf_le_inf_right _ inf_le_right)
  have e1 := val_resM hM (inf_le_left : U ⊓ L.U i ⊓ L.U j ≤ U ⊓ L.U i) hW (coord s i)
  have e2 := val_resM hM (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    U ⊓ L.U i ⊓ L.U j ≤ U ⊓ L.U j) hW (coord s j)
  rw [← e1, ← e2, e, hM.smul, fnOf_resG]

theorem tval_eq (hM : LatModel M F) (hr : IsRatSec L r) {U : X.Opens} (h : genericPoint X ∈ U)
    (i j : L.ι) (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j)
    (s : Γ(twist F L, U)) : tval r hM i hi U h s = tval r hM j hj U h s := by
  rw [tval_apply, tval_apply, val_coord_rel hM s i j h hi hj, Units.smul_def, Units.smul_def,
    smul_smul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hr i j (memInf hi hj)]
  congr 1
  have hg : fnOf (L.U i ⊓ L.U j) (memInf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) ≠ 0 :=
    ((L.g i j).isUnit.map (fnOf (L.U i ⊓ L.U j) (memInf hi hj))).ne_zero
  have hrj : (r j : X.functionField) ≠ 0 := (r j).ne_zero
  field_simp

end LatTwist

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR

namespace LatTwist

open GlobalTheory.Twist

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M M' : X → AddSubgroup V} {F : X.Modules} {D : CartierDiv X} {L : LB X}
  {r : L.ι → X.functionFieldˣ}

theorem mem_of_mem_latSec {N : X → AddSubgroup V} {U : X.Opens} {v : V} (hv : v ∈ latSec N U)
    {y : X} (hy : y ∈ U) : v ∈ N y :=
  AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv y) hy

theorem mem_latSec {N : X → AddSubgroup V} {U : X.Opens} {v : V} (hv : ∀ y ∈ U, v ∈ N y) :
    v ∈ latSec N U :=
  AddSubgroup.mem_iInf.2 fun y => AddSubgroup.mem_iInf.2 fun hy => hv y hy

def twistModel (hP : Presents D L r)
    (hE : ∀ y (g : X.functionFieldˣ) (v : V), D.IsEqn y g → (v ∈ M' y ↔ (g : X.functionField) • v ∈ M y))
    (hM : LatModel M F) (i₀ : L.ι) (hi₀ : genericPoint X ∈ L.U i₀) :
    LatModel M' (twist F L) where
  val U h := tval r hM i₀ hi₀ U h
  inj U h := by
    intro s t e
    refine sec_ext fun i => ?_
    by_cases hi : genericPoint X ∈ L.U i
    · have e' : tval r hM i hi U h s = tval r hM i hi U h t := by
        rw [← tval_eq hM hP.isRatSec h i₀ i hi₀ hi, ← tval_eq hM hP.isRatSec h i₀ i hi₀ hi]
        exact e
      rw [tval_apply, tval_apply] at e'
      exact hM.inj (U ⊓ L.U i) (memInf h hi) (MulAction.injective _ e')
    · exact sec_eq_of_not_gen (fun hh : genericPoint X ∈ U ⊓ L.U i => hi hh.2) _ _
  range U h := by
    ext v
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨s, rfl⟩
      refine mem_latSec fun y hy => ?_
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (by rw [hP.isLB.cover]; exact Set.mem_univ y)
      have hgi : genericPoint X ∈ L.U i := gen_mem hi
      rw [tval_eq hM hP.isRatSec h i₀ i hi₀ hgi, hE y (r i) _ (hP.isEqn i y hi), tval_apply,
        ← Units.smul_def, smul_inv_smul]
      have hw : hM.val (U ⊓ L.U i) (memInf h hgi) (coord s i) ∈ (hM.val (U ⊓ L.U i) (memInf h hgi)).range :=
        AddMonoidHom.mem_range.2 ⟨_, rfl⟩
      rw [hM.range] at hw
      exact mem_of_mem_latSec hw (memInf hy hi)
    · intro hv
      have key : ∀ i, ∃ t : Γ(F, U ⊓ L.U i),
          ∀ hi : genericPoint X ∈ L.U i, hM.val (U ⊓ L.U i) (memInf h hi) t = r i • v := by
        intro i
        by_cases hi : genericPoint X ∈ L.U i
        · have hm : r i • v ∈ latSec M (U ⊓ L.U i) := mem_latSec fun y hy => by
            rw [Units.smul_def, ← hE y (r i) v (hP.isEqn i y hy.2)]
            exact mem_of_mem_latSec hv hy.1
          rw [← hM.range (U ⊓ L.U i) (memInf h hi)] at hm
          obtain ⟨t, ht⟩ := hm
          exact ⟨t, fun _ => ht⟩
        · exact ⟨0, fun h' => (hi h').elim⟩
      choose t ht using key
      have hmem : t ∈ Twist.secGroup F L U := by
        intro i j
        by_cases hij : genericPoint X ∈ L.U i ⊓ L.U j
        · have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j := (memInf (memInf h hij.1) hij.2)
          apply hM.inj (U ⊓ L.U i ⊓ L.U j) hW
          rw [hM.smul, val_resM, val_resM, fnOf_resG, ht i hij.1, ht j hij.2, Units.smul_def,
            Units.smul_def, smul_smul, hP.isRatSec i j hij]
        · exact sec_eq_of_not_gen (fun hh : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j => hij (memInf hh.1.2 hh.2)) _ _
      exact ⟨mkSec t hmem, by rw [tval_apply, coord_mkSec, ht i₀ hi₀, inv_smul_smul]⟩
  res U W e h s := by
    change tval r hM i₀ hi₀ W h (resM (twist F L) e s) = tval r hM i₀ hi₀ U (e h) s
    rw [tval_apply, tval_apply, coord_resM, val_resM]
  smul U h a s := by
    change tval r hM i₀ hi₀ U h (a • s) = fnOf U h a • tval r hM i₀ hi₀ U h s
    rw [tval_apply, tval_apply, coord_smul, hM.smul, fnOf_resG, Units.smul_def, Units.smul_def,
      smul_smul, smul_smul, mul_comm]

end LatTwist

theorem nonempty_latModel_twist : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V]
    [Module X.functionField V] (M M' : X → AddSubgroup V) (F : X.Modules) (D : CartierDiv X)
    (L : LB X) (r : L.ι → X.functionFieldˣ), Presents D L r →
    (∀ y (g : X.functionFieldˣ) (v : V), D.IsEqn y g → (v ∈ M' y ↔ (g : X.functionField) • v ∈ M y)) →
    LatModel M F → Nonempty (LatModel M' (twist F L)) := by
  intro X _ V _ _ M M' F D L r hP hE hM
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (by rw [hP.isLB.cover]; exact Set.mem_univ (genericPoint X))
  exact ⟨LatTwist.twistModel hP hE hM i₀ hi₀⟩

end GlobalTheory.LogDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelFiniteQuasicoherent
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.LatFinite

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M : X → AddSubgroup V} {F : X.Modules}

theorem val_linearCombination (L : LatModel M F) {U W : X.Opens} (h : W ≤ U)
    (hW : genericPoint X ∈ W) {m : ℕ} (e : Fin m → Γ(F, U)) (a : Fin m → Γ(X, W)) :
    L.val W hW (Fintype.linearCombination Γ(X, W) (fun i => Twist.resM F h (e i)) a) =
      ∑ i, fnOf W hW (a i) • L.val U (h hW) (e i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Fintype.linearCombination_apply, map_sum, L.smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← L.res U W h hW (e i)]

theorem val_mem (L : LatModel M F) {W : X.Opens} (hW : genericPoint X ∈ W) (s : Γ(F, W))
    {z : X} (hz : z ∈ W) : L.val W hW s ∈ M z := by
  have h : L.val W hW s ∈ latSec M W := L.range W hW ▸ ⟨s, rfl⟩
  simp only [latSec, AddSubgroup.mem_iInf] at h
  exact h z hz

theorem isFrame (L : LatModel M F) {U : X.Opens} (hU : genericPoint X ∈ U) {m : ℕ}
    {v : Fin m → V} (hv : LinearIndependent X.functionField v)
    (hM : ∀ z ∈ U, ∀ w, w ∈ M z ↔
      ∃ c : Fin m → X.functionField, (∀ i, RegAt z (c i)) ∧ w = ∑ i, c i • v i)
    (e : Fin m → Γ(F, U)) (he : ∀ i, L.val U hU (e i) = v i) : VB.IsFrame e := by
  refine VB.isFrame_of_forall_exists fun W h x hx => ⟨W, le_rfl, hx, ?_⟩
  have hW : genericPoint X ∈ W := gen_mem hx
  have key : ∀ a : Fin m → Γ(X, W), L.val W hW (Fintype.linearCombination Γ(X, W)
      (fun i => Twist.resM F (le_rfl.trans h) (e i)) a) = ∑ i, fnOf W hW (a i) • v i := fun a => by
    rw [val_linearCombination L]
    simp only [he]
  constructor
  · intro a b hab
    have := congrArg (L.val W hW) hab
    rw [key, key] at this
    funext i
    exact fnOf_injective W hW (Fintype.linearIndependent_iffₛ.1 hv _ _ this i)
  · intro s
    obtain ⟨c, -, hc⟩ := (hM _ (h hW) _).1 (val_mem L hW s hW)
    have hreg : ∀ i, ∀ z ∈ W, RegAt z (c i) := by
      intro i z hz
      obtain ⟨c', hc', e'⟩ := (hM z (h hz) _).1 (val_mem L hW s hz)
      rw [Fintype.linearIndependent_iffₛ.1 hv _ _ (hc.symm.trans e') i]
      exact hc' i
    choose a ha using fun i => exists_fnOf_eq hW (hreg i)
    refine ⟨a, L.inj W hW ?_⟩
    rw [key, hc]
    simp only [ha]

theorem isFiniteQC_of_latModel : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V]
    [Module X.functionField V] (M : X → AddSubgroup V) (F : X.Modules), LatModel M F →
    (∀ y : X, ∃ (U : X.Opens) (m : ℕ) (v : Fin m → V), y ∈ U ∧ IsAffineOpen U ∧
      LinearIndependent X.functionField v ∧ ∀ z ∈ U, ∀ w, w ∈ M z ↔
        ∃ c : Fin m → X.functionField, (∀ i, RegAt z (c i)) ∧ w = ∑ i, c i • v i) →
    GlobalTheory.QCoh.IsFiniteQC F := by
  intro X _ V _ _ M F L H
  choose U m v hy _ hv hM using H
  have frame : ∀ y, ∃ e : Fin (m y) → Γ(F, U y), VB.IsFrame e := by
    intro y
    have hU : genericPoint X ∈ U y := gen_mem (hy y)
    have hmem : ∀ i, v y i ∈ latSec M (U y) := by
      intro i
      simp only [latSec, AddSubgroup.mem_iInf]
      intro z hz
      classical
      refine (hM y z hz _).2 ⟨Pi.single i 1, fun j => ?_, ?_⟩
      · by_cases hj : j = i
        · subst hj; simpa using (unitAt_one z).regAt
        · simpa [Pi.single_apply, hj] using regAt_zero z
      · simp [Pi.single_apply]
    choose e he using fun i => (L.range (U y) hU).ge (hmem i)
    exact ⟨e, isFrame L hU (hv y) (hM y) e he⟩
  choose e he using frame
  refine QCoh.IsFiniteQC.of_restrict (fun y => (U y).ι) (fun x => ⟨x, by simpa using hy x⟩)
    fun y => ?_
  have hf := (VB.isFrame_restrict_iff (U y).ι _).2 ((he y).res ((U y).ι_image_le ⊤))
  exact (VB.IsFrame.isVB hf).isFiniteQC

end GlobalTheory.LogDR.LatFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeModel
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.LatSheaf

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]

def secGrp (M : X → AddSubgroup V) (U : X.Opens) : AddSubgroup V where
  carrier := {v | (∀ y ∈ U, v ∈ M y) ∧ (genericPoint X ∉ U → v = 0)}
  add_mem' := fun {a b} ha hb =>
    ⟨fun y hy => add_mem (ha.1 y hy) (hb.1 y hy), fun h => by rw [ha.2 h, hb.2 h, add_zero]⟩
  zero_mem' := ⟨fun y _ => zero_mem _, fun _ => rfl⟩
  neg_mem' := fun {a} ha => ⟨fun y hy => neg_mem (ha.1 y hy), fun h => by rw [ha.2 h, neg_zero]⟩

variable (M : X → AddSubgroup V)

theorem val_eq_zero {U : X.Opens} (h : genericPoint X ∉ U) (s : secGrp M U) : (s : V) = 0 := s.2.2 h


open Classical in
def resHom {U W : X.Opens} (e : W ≤ U) : secGrp M U →+ secGrp M W where
  toFun s := if h : genericPoint X ∈ W then ⟨(s : V), fun y hy => s.2.1 y (e hy), fun h' => (h' h).elim⟩
    else 0
  map_zero' := by split_ifs <;> rfl
  map_add' s t := by split_ifs <;> first | rfl | simp

open Classical in
theorem val_resHom {U W : X.Opens} (e : W ≤ U) (s : secGrp M U) :
    ((resHom M e s : secGrp M W) : V) = if genericPoint X ∈ W then (s : V) else 0 := by
  unfold resHom; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]; split_ifs <;> rfl

theorem val_resHom_of_mem {U W : X.Opens} (e : W ≤ U) (h : genericPoint X ∈ W) (s : secGrp M U) :
    ((resHom M e s : secGrp M W) : V) = s := by rw [val_resHom, if_pos h]

def pre : TopCat.Presheaf Ab.{0} X where
  obj U := AddCommGrpCat.of (secGrp M U.unop)
  map f := AddCommGrpCat.ofHom (resHom M (leOfHom f.unop))
  map_id U := by
    ext s
    change ((resHom M le_rfl s : secGrp M U.unop) : V) = s
    rw [val_resHom]; split_ifs with h
    · rfl
    · exact (val_eq_zero M h s).symm
  map_comp f g := by
    ext s
    change ((resHom M (leOfHom (f ≫ g).unop) s : secGrp M _) : V) =
      ((resHom M (leOfHom g.unop) (resHom M (leOfHom f.unop) s) : secGrp M _) : V)
    rw [val_resHom, val_resHom, val_resHom]
    split_ifs with h1 h2 <;> first | rfl | exact (h2 (leOfHom g.unop h1)).elim

theorem sec_ext {U : X.Opens} {s t : secGrp M U} (h : genericPoint X ∈ U → (s : V) = t) : s = t := by
  by_cases hU : genericPoint X ∈ U
  · exact Subtype.ext (h hU)
  · exact Subtype.ext ((val_eq_zero M hU s).trans (val_eq_zero M hU t).symm)

def sv (U : (X.Opens)ᵒᵖ) (s : (pre M).obj U) : V := @Subtype.val V (· ∈ secGrp M U.unop) s

theorem sv_mem (U : (X.Opens)ᵒᵖ) (s : (pre M).obj U) : sv M U s ∈ secGrp M U.unop :=
  @Subtype.property V (· ∈ secGrp M U.unop) s

theorem sv_ext {U : (X.Opens)ᵒᵖ} {s t : (pre M).obj U} (h : genericPoint X ∈ U.unop → sv M U s = sv M U t) :
    s = t :=
  sec_ext M (U := U.unop) (s := s) (t := t) h

def mk (U : (X.Opens)ᵒᵖ) (v : V) (h : v ∈ secGrp M U.unop) : (pre M).obj U :=
  (⟨v, h⟩ : secGrp M U.unop)

@[simp] theorem sv_mk (U : (X.Opens)ᵒᵖ) (v : V) (h : v ∈ secGrp M U.unop) : sv M U (mk M U v h) = v := rfl

open Classical in
theorem sv_map {U W : (X.Opens)ᵒᵖ} (f : U ⟶ W) (s : (pre M).obj U) :
    sv M W ((pre M).map f s) = if genericPoint X ∈ W.unop then sv M U s else 0 :=
  val_resHom M (leOfHom f.unop) s

theorem isSheaf_pre : (pre M).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have key : ∀ k l, genericPoint X ∈ W k → genericPoint X ∈ W l →
      sv M _ (sf k) = sv M _ (sf l) := fun k l hk hl => by
    have := congrArg (sv M _) (hsf k l)
    rw [sv_map, sv_map, if_pos (show genericPoint X ∈ W k ⊓ W l from ⟨hk, hl⟩),
      if_pos (show genericPoint X ∈ W k ⊓ W l from ⟨hk, hl⟩)] at this
    exact this
  by_cases hg : genericPoint X ∈ iSup W
  · obtain ⟨k₀, hk₀⟩ := Opens.mem_iSup.1 hg
    have mem : sv M _ (sf k₀) ∈ secGrp M (iSup W) := by
      refine ⟨fun y hy => ?_, fun h => (h hg).elim⟩
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hy
      rw [key k₀ k hk₀ (gen_mem hk)]
      exact (sv_mem M _ (sf k)).1 y hk
    refine ⟨mk M (Opposite.op (iSup W)) _ mem, fun k => ?_, fun t ht => ?_⟩
    · refine sv_ext M fun hk => ?_
      rw [sv_map, if_pos hk, sv_mk]
      exact key k₀ k hk₀ hk
    · refine sv_ext M fun _ => ?_
      have := congrArg (sv M _) (ht k₀)
      rw [sv_map, if_pos hk₀] at this
      rw [sv_mk]
      exact this
  · refine ⟨mk M (Opposite.op (iSup W)) 0 (zero_mem _), fun k => ?_, fun t _ => ?_⟩
    · exact sv_ext M fun hk => (hg (Opens.mem_iSup.2 ⟨k, hk⟩)).elim
    · exact sv_ext M fun h => (hg h).elim

variable {M}
variable (hM : ∀ y (f : X.functionField) (v : V), RegAt y f → v ∈ M y → f • v ∈ M y)


open Classical in
def smulSec (U : X.Opens) (r : Γ(X, U)) (s : secGrp M U) : secGrp M U :=
  if h : genericPoint X ∈ U then
    ⟨fnOf U h r • (s : V), fun y hy => hM y _ _ (regAt_fnOf hy h r) (s.2.1 y hy), fun h' => (h' h).elim⟩
  else 0

theorem val_smulSec {U : X.Opens} (h : genericPoint X ∈ U) (r : Γ(X, U)) (s : secGrp M U) :
    (smulSec hM U r s : V) = fnOf U h r • (s : V) := by
  rw [smulSec, dite_eq_left h]

def secModule (U : X.Opens) : Module Γ(X, U) (secGrp M U) where
  smul := smulSec hM U
  one_smul s := sec_ext M fun h => by
    change (smulSec hM U 1 s : V) = s
    rw [val_smulSec hM h, map_one, one_smul]
  mul_smul a b s := sec_ext M fun h => by
    change (smulSec hM U (a * b) s : V) = smulSec hM U a (smulSec hM U b s)
    rw [val_smulSec hM h, val_smulSec hM h, val_smulSec hM h, map_mul, mul_smul]
  smul_zero a := sec_ext M fun h => by
    change (smulSec hM U a 0 : V) = ((0 : secGrp M U) : V)
    rw [val_smulSec hM h, ZeroMemClass.coe_zero, smul_zero]
  smul_add a s t := sec_ext M fun h => by
    change (smulSec hM U a (s + t) : V) = ((smulSec hM U a s + smulSec hM U a t : secGrp M U) : V)
    rw [AddSubgroup.coe_add, val_smulSec hM h, val_smulSec hM h, val_smulSec hM h, AddSubgroup.coe_add,
      smul_add]
  add_smul a b s := sec_ext M fun h => by
    change (smulSec hM U (a + b) s : V) = ((smulSec hM U a s + smulSec hM U b s : secGrp M U) : V)
    rw [AddSubgroup.coe_add, val_smulSec hM h, val_smulSec hM h, val_smulSec hM h, map_add (f := _), add_smul]
  zero_smul s := sec_ext M fun h => by
    change (smulSec hM U 0 s : V) = ((0 : secGrp M U) : V)
    rw [val_smulSec hM h, map_zero, zero_smul, ZeroMemClass.coe_zero]

theorem resHom_smulSec {U W : X.Opens} (e : W ≤ U) (r : Γ(X, U)) (s : secGrp M U) :
    resHom M e (smulSec hM U r s) = smulSec hM W (resG X e r) (resHom M e s) :=
  sec_ext M fun h => by
    rw [val_resHom_of_mem M e h, val_smulSec hM h, val_smulSec hM (e h), fnOf_resG,
      val_resHom_of_mem M e h]

def toMod : X.Modules :=
  letI : ∀ U, Module (X.ringCatSheaf.obj.obj U) ((pre M).obj U) := fun U => secModule hM U.unop
  { val := PresheafOfModules.ofPresheaf (pre M) fun _ _ f r m => resHom_smulSec hM (leOfHom f.unop) r m
    isSheaf := isSheaf_pre M }

def latModel : LatModel M (toMod hM) where
  val U _ := { toFun := fun s => sv M (Opposite.op U) s, map_zero' := rfl, map_add' := fun _ _ => rfl }
  inj U _ s t e := sv_ext M fun _ => e
  range U h := by
    ext v
    simp only [AddMonoidHom.mem_range, AddMonoidHom.coe_mk, ZeroHom.coe_mk, latSec,
      AddSubgroup.mem_iInf]
    constructor
    · rintro ⟨s, rfl⟩ y hy
      exact (sv_mem M _ s).1 y hy
    · intro hv
      exact ⟨mk M (Opposite.op U) v ⟨hv, fun h' => (h' h).elim⟩, rfl⟩
  res U W e h s := by
    exact (sv_map M (homOfLE e).op s).trans (if_pos h)
  smul U h r s := val_smulSec hM h r s

end GlobalTheory.LogDR.LatSheaf

theorem GlobalTheory.LogDR.exists_latModel : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V]
    [Module X.functionField V] (M : X → AddSubgroup V),
    (∀ y (f : X.functionField) (v : V), RegAt y f → v ∈ M y → f • v ∈ M y) →
      ∃ F : X.Modules, Nonempty (LatModel M F) :=
  fun _ _ _ _ _ _ hM => ⟨LatSheaf.toMod hM, ⟨LatSheaf.latModel hM⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAtSmulMem
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

namespace GlobalTheory.LogDR

theorem logAt_smul_mem : ∀ (X : Scheme.{0}) [IsIntegral X] (Z : Set X) (G : CartierDiv X) (a : ℕ) (y : X)
    (f : X.functionField) (η : abelian₂ X.functionField), RegAt y f → η ∈ logAt Z G a y → f • η ∈ logAt Z G a y := by
  intro X _ Z G a y f η hf hη
  unfold logAt spanForms at hη ⊢
  induction hη using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    refine ⟨f * c, ?_, v, hv, ?_⟩
    · exact (show G.RegularAt y c from hc).regAt_mul hf
    · rw [smul_smul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

end GlobalTheory.LogDR
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogFormsLatticeFinite
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LatticeModelFiniteQuasicoherent
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.lattice_model_finite_quasicoherent : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V) (F : X.Modules), LatModel M F → (∀ y : X, ∃ (U : X.Opens) (m : ℕ) (v : Fin m → V), y ∈ U ∧ IsAffineOpen U ∧ LinearIndependent X.functionField v ∧ ∀ z ∈ U, ∀ w, w ∈ M z ↔ ∃ c : Fin m → X.functionField, (∀ i, RegAt z (c i)) ∧ w = ∑ i, c i • v i) → GlobalTheory.QCoh.IsFiniteQC F := by
  first | exact @_root_.GlobalTheory.LogDR.LatFinite.isFiniteQC_of_latModel | exact _root_.GlobalTheory.LogDR.LatFinite.isFiniteQC_of_latModel | (intros; apply _root_.GlobalTheory.LogDR.LatFinite.isFiniteQC_of_latModel <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogFormsLatticeFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

theorem mem_chartForms_iff_sum_card {K : Type} [Field K] (A : Subring K) {n : ℕ} (x : Fin n → Kˣ)
    (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) (η : abelian₂ K) :
    η ∈ chartForms A x J t a ↔ ∃ d : {I : Finset (Fin n) // I.card = a} → K, (∀ I, d I ∈ A) ∧
      η = ∑ I, d I • (((t⁻¹ * ∏ j ∈ I.1 \ J, x j : Kˣ) : K) • logWedge x I.1) := by
  classical
  rw [GlobalTheory.T.mem_chart_forms_iff K A n x J t a η]
  have ht : (t : K) ≠ 0 := t.ne_zero
  have hP : ∀ I : Finset (Fin n), ∏ j ∈ I \ J, (x j : K) ≠ 0 := fun I =>
    Finset.prod_ne_zero_iff.2 fun j _ => (x j).ne_zero
  have hsplit : ∀ f : Finset (Fin n) → abelian₂ K, (∀ I, I.card ≠ a → f I = 0) →
      ∑ I, f I = ∑ I : {I : Finset (Fin n) // I.card = a}, f I.1 := by
    intro f hf
    rw [← Fintype.sum_subtype_add_sum_subtype (fun I : Finset (Fin n) => I.card = a) f,
      Finset.sum_eq_zero (s := (Finset.univ : Finset {I : Finset (Fin n) // ¬ I.card = a}))
        (fun I _ => hf I.1 I.2), add_zero]
  constructor
  · rintro ⟨c, hc0, hcA, rfl⟩
    refine ⟨fun I => c I.1 * t / ∏ j ∈ I.1 \ J, (x j : K), fun I => hcA I.1, ?_⟩
    rw [hsplit (fun I => c I • logWedge x I) (fun I hI => by simp only [hc0 I hI, zero_smul])]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [smul_smul]
    congr 1
    have := hP I.1
    push_cast
    field_simp
  · rintro ⟨d, hdA, rfl⟩
    refine ⟨fun I => if h : I.card = a then d ⟨I, h⟩ * ((t⁻¹ * ∏ j ∈ I \ J, x j : Kˣ) : K) else 0,
      ?_, ?_, ?_⟩
    · intro I hI
      simp [hI]
    · intro I
      by_cases hI : I.card = a
      · dsimp only
        rw [dite_eq_left hI]
        have e : d ⟨I, hI⟩ * ((t⁻¹ * ∏ j ∈ I \ J, x j : Kˣ) : K) * t / ∏ j ∈ I \ J, (x j : K) =
            d ⟨I, hI⟩ := by
          have := hP I
          push_cast
          field_simp
        rw [e]
        exact hdA _
      · dsimp only
        rw [dif_neg hI, zero_mul, zero_div]
        exact zero_mem A
    · rw [hsplit (fun I => (if h : I.card = a then d ⟨I, h⟩ * ((t⁻¹ * ∏ j ∈ I \ J, x j : Kˣ) : K)
          else 0) • logWedge x I) (fun I hI => by simp only [dif_neg hI, zero_smul])]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [dite_eq_left I.2, smul_smul]

theorem latModel_logAt_isFiniteQC : ∀ (X : Scheme.{0}) [IsIntegral X] {C : Type} [Fintype C]
    (E : C → CartierDiv X) {n : ℕ} {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (a : ℕ)
    (F : X.Modules), LatModel (logAt (suppAll E) G a) F → GlobalTheory.QCoh.IsFiniteQC F := by
  intro X _ C _ E n ι 𝒜 G a F hF
  refine GlobalTheory.T.lattice_model_finite_quasicoherent X _ F hF fun y => ?_
  obtain ⟨i, hi⟩ : ∃ i, y ∈ 𝒜.U i := by
    have : y ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
    simpa [Opens.mem_iSup] using this
  obtain ⟨t, ht⟩ := G.exists_isEqn y
  obtain ⟨W, hyW, hW⟩ := ht.exists_nhds
  obtain ⟨f, hfW, hyf⟩ := (𝒜.affine i).exists_basicOpen_le (V := W) ⟨y, hyW⟩ hi
  let S := {I : Finset (Fin n) // I.card = a}
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let u : S → X.functionFieldˣ := fun I => t⁻¹ * ∏ j ∈ I.1 \ 𝒜.J i, 𝒜.x i j
  let g : S → abelian₂ X.functionField := fun I => ((u I : X.functionFieldˣ) : X.functionField) • logWedge (𝒜.x i) I.1
  refine ⟨X.basicOpen f, Fintype.card S, fun k => g (e k), hyf, (𝒜.affine i).basicOpen f, ?_, ?_⟩
  · have hc : IsCoord (𝒜.x i) := ((𝒜.chart i).chart _ (𝒜.gen i)).coord
    have h1 := (GlobalTheory.LogDR.logWedge_basis _ n (𝒜.x i) hc).1.comp (fun k => (e k).1)
      (Subtype.val_injective.comp e.injective)
    exact h1.units_smul (fun k => u (e k))
  · intro z hz w
    have hzU : z ∈ 𝒜.U i := X.basicOpen_le f hz
    have hzt : G.IsEqn z t := hW z (hfW hz)
    rw [GlobalTheory.T.log_forms_eq_chart_forms (suppAll E) (𝒜.U i) (𝒜.x i) (𝒜.J i) G z t a (𝒜.chart i) hzU hzt,
      mem_chartForms_iff_sum_card]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨fun k => d (e k), fun k => hd _, (e.sum_comp fun I => d I • g I).symm⟩
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun I => c (e.symm I), fun I => hc _, ?_⟩
      rw [← e.sum_comp]
      simp only [Equiv.symm_apply_apply]
      rfl

end GlobalTheory.LogDR
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogFormsLatticeFiniteStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.log_forms_lattice_finite : ∀ (X : Scheme.{0}) [IsIntegral X] {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (a : ℕ) (F : X.Modules), LatModel (logAt (suppAll E) G a) F → GlobalTheory.QCoh.IsFiniteQC F := by
  first | exact @_root_.GlobalTheory.LogDR.latModel_logAt_isFiniteQC | exact _root_.GlobalTheory.LogDR.latModel_logAt_isFiniteQC | (intros; apply _root_.GlobalTheory.LogDR.latModel_logAt_isFiniteQC <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLatticeModel
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.exists_lattice_model : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V), (∀ y (f : X.functionField) (v : V), RegAt y f → v ∈ M y → f • v ∈ M y) → ∃ F : X.Modules, Nonempty (LatModel M F) := by
  first | exact @_root_.GlobalTheory.LogDR.exists_latModel | exact _root_.GlobalTheory.LogDR.exists_latModel | (intros; apply _root_.GlobalTheory.LogDR.exists_latModel <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SerreVanishingSncAtlas
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.LogDR

open GlobalTheory.Twist GlobalTheory.LB GlobalTheory.QCoh

theorem spanForms_eq_bot_of_isCoord {K : Type} [Field K] {n : ℕ} {x : Fin n → Kˣ} (hx : IsCoord x)
    (M : Set K) (H : Set Ω[K⁄ℤ]) {a : ℕ} (ha : n < a) : spanForms M H a = ⊥ := by
  let bs : Module.Basis (Fin n) K Ω[K⁄ℤ] := Module.Basis.mk hx.1 hx.2.ge
  haveI : Module.Finite K Ω[K⁄ℤ] := Module.Finite.of_basis bs
  have hfr : Module.finrank K Ω[K⁄ℤ] = n := by
    rw [Module.finrank_eq_card_basis bs, Fintype.card_fin]
  refine eq_bot_iff.2 ((AddSubgroup.closure_le _).2 ?_)
  rintro η ⟨c, -, v, -, rfl⟩
  have hv : ¬ LinearIndependent K v := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin, hfr] at this
    omega
  rw [AlternatingMap.map_linearDependent _ v hv, smul_zero]
  exact AddSubgroup.zero_mem _

theorem logAt_eq_bot_of_lt {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (Z : Set X) (G : CartierDiv X) {a : ℕ} (ha : n < a) (y : X) :
    logAt Z G a y = ⊥ := by
  have hg : genericPoint X ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
  obtain ⟨i, -⟩ := (Opens.mem_iSup).1 hg
  exact spanForms_eq_bot_of_isCoord ((𝒜.chart i).chart _ (𝒜.gen i)).coord _ _ ha

theorem cechFam_eq_of_lt {X : Scheme.{0}} [IsIntegral X] {C : Type} {E : C → CartierDiv X} {n : ℕ}
    {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) {a : ℕ} (ha : n < a) :
    cechFam 𝒜 G a = cechFam 𝒜 G (n + 1) := by
  funext s
  simp only [cechFam, logSec, latSec, logAt_eq_bot_of_lt 𝒜 _ G ha,
    logAt_eq_bot_of_lt 𝒜 _ G (Nat.lt_succ_self n)]

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR

open GlobalTheory.Twist GlobalTheory.LB GlobalTheory.QCoh

theorem exists_cechZero_cechFam_nsmul_add : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k), IsProjOver f → ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] (𝒜 : SncAtlas E n ι) (H : CartierDiv X) (B : ℕ) (R : Fin B → CartierDiv X), IsAmpleLB (toLB H) → ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ (j : Fin B) (a b : ℕ), 0 < b → DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
  intro k _ X _ f hf C _ E n ι _ _ 𝒜 H B R hH
  haveI : IsProper f := (isProper_and_exists_isAmpleLB_of_isProjOver hf).1
  haveI : X.IsSeparated := by
    constructor
    rw [show terminal.from X = f ≫ terminal.from _ from Subsingleton.elim _ _]
    infer_instance
  letI := algebraΓOfHom f
  have key : ∀ (j : Fin B) (a : Fin (n + 2)), ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ b : ℕ, 0 < b →
      DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
    intro j a
    obtain ⟨F, ⟨lm⟩⟩ := GlobalTheory.T.exists_lattice_model X (logAt (suppAll E) (R j) a)
      (fun y g v hg hv => logAt_smul_mem X _ _ _ y g v hg hv)
    haveI : IsFiniteQC F := GlobalTheory.T.log_forms_lattice_finite X E 𝒜 (R j) a F lm
    have hev := eventually_subsingleton_coh_twistZ_of_isProjOver (f := f) (fun _ => rfl) F hf hH
    obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hev)
    refine ⟨q₀, fun q hq b hb => ?_⟩
    obtain ⟨lm'⟩ := nonempty_latModel_twist X (logAt (suppAll E) (R j) a)
      (logAt (suppAll E) (q • H + R j) a) F (q • H) (toLB (q • H)) _ (presents_toLB _)
      (fun y g v hD => by rw [add_comm]; exact logtwist X _ _ _ _ y g v hD) lm
    haveI : IsFiniteQC (twist F (toLB (q • H))) := isFiniteQC_twist (isLB_toLB _)
    have hc := GlobalTheory.T.cech_lattice_cohomology_vanish X (logAt (suppAll E) (q • H + R j) a) (twist F (toLB (q • H))) 𝒜.U lm'
      𝒜.affine 𝒜.gen 𝒜.cover b hb
    refine hc.2 ?_
    haveI hs : Subsingleton (coh (twist F (lbZPow (toLB H) (q : ℤ))) b) := hq₀ q hq b hb
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq F (isLB_toLB (q • H)) (isLB_lbZPow (isLB_toLB H) q)
      (by rw [cls_lbZPow (isLB_toLB H), ← toPic_apply, ← toPic_apply, map_nsmul, natCast_zsmul])
    exact (cohOn.mapIso k ⊤ b e).injective.subsingleton
  choose q₁ hq₁ using key
  obtain ⟨Q, hQ⟩ := Finite.exists_le (fun p : Fin B × Fin (n + 2) => q₁ p.1 p.2)
  refine ⟨Q, fun q hq j a b hb => ?_⟩
  by_cases ha : a ≤ n + 1
  · exact hq₁ j ⟨a, by omega⟩ q ((hQ (j, ⟨a, by omega⟩)).trans hq) b hb
  · rw [cechFam_eq_of_lt 𝒜 _ (by omega : n < a)]
    exact hq₁ j ⟨n + 1, by omega⟩ q ((hQ (j, ⟨n + 1, by omega⟩)).trans hq) b hb

end GlobalTheory.LogDR
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SerreVanishingSncAtlasStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.serre_vanishing_snc_atlas : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k), IsProjOver f → ∀ {C : Type} [Fintype C] (E : C → CartierDiv X) {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] (𝒜 : SncAtlas E n ι) (H : CartierDiv X) (B : ℕ) (R : Fin B → CartierDiv X), IsAmpleLB (toLB H) → ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ (j : Fin B) (a b : ℕ), 0 < b → DI.CechZero (cechFam 𝒜 (q • H + R j) a) b := by
  first | exact @_root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add | exact _root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add | (intros; apply _root_.GlobalTheory.LogDR.exists_cechZero_cechFam_nsmul_add <;> assumption)
end
