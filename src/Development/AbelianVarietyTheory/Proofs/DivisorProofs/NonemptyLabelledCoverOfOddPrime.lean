module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsIffPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationThetaSeriesAlgebraicOverFractionFiel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfLabelledCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RecognitionDegDataLabelsAtEveryTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantTorsionValuesUltrametric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerRecognition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recog

open GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.SeriesCompare GlobalTheory.IndefiniteRowSideFullHecke.ThetaTowerRecognition

section Nest
variable {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O)

theorem tx_nest {n m M : ℕ} (hn : Odd n) (hm : Odd m) (hM : M = n * m) (Q : N.QT (M ^ 2)) (q : N.QT (m ^ 2))
    (h₁ : Q.1.1 = q.1.1 ^ n) (h₂ : q.1.2 = Q.1.2 ^ n) : N.tx M Q = N.tx m q := by
  subst hM
  exact tsum_congr fun χ => GlobalTheory.T.degenerationSeriesTerms_nest O N n m hn hm Q q h₁ h₂ χ

end Nest

section Scalar
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}

theorem io_one (w : TowerIso N N' n) (j : ℕ) : N'.QEq (w.io j 1) 1 := by
  have := w.mul j 1 1
  rw [_root_.mul_one (1 : N.QT ((n ^ j) ^ 2))] at this
  obtain ⟨z, hz⟩ := (N'.qEq_iff _ _).1 this
  refine (N'.qEq_equivalence _).symm ((N'.qEq_iff _ _).2 ⟨z, ?_⟩)
  rw [_root_.one_mul]
  exact mul_left_cancel hz

theorem io_pow (w : TowerIso N N' n) (j : ℕ) (p : N.QT ((n ^ j) ^ 2)) (m : ℕ) :
    N'.QEq (w.io j (p ^ m)) (w.io j p ^ m) := by
  have E := N'.qEq_equivalence ((n ^ j) ^ 2)
  induction m with
  | zero => rw [pow_zero p, pow_zero (w.io j p)]; exact io_one w j
  | succ m ih =>
    rw [pow_succ p m, pow_succ (w.io j p) m]
    exact E.trans (w.mul j _ _) (GlobalTheory.Ex.TateInh.qEq_mul N' ih (E.refl _))

theorem addCommGroup_nsmul_identity {X : Type} [AddCommGroup X] (n k : ℕ) (Y Y' U z : X) (y₁ : U = n • Y' + (n * (n * k)) • z)
    (a : U = (n * n) • Y) : n • Y' = n • (n • (Y + k • -z)) := by
  have h := eq_sub_of_add_eq (y₁.symm.trans a)
  rw [h, mul_smul, mul_smul, mul_smul]
  simp only [smul_add, smul_neg]
  abel

theorem scalar_const (hn : Odd n) (w : TowerIso N N' n) (hX : ∀ (z z' : N'.X), n • z = n • z' → z = z')
    (hd : ∀ g : N.Gt, ∃ g', g' ^ n = g)
    (hc : ∀ j, ∃ c : Cˣ, ∀ q, N'.tx (n ^ j) (w.io j q) = c * N.tx (n ^ j) q)
    (h0 : ∃ q : N.QT ((n ^ 1) ^ 2), N.tx (n ^ 1) q ≠ 0) :
    ∃ c₀ : C, c₀ ≠ 0 ∧ ∀ j q, N'.tx (n ^ j) (w.io j q) = c₀ * N.tx (n ^ j) q := by
  have down : ∀ (c : C) (j : ℕ), (∀ q, N'.tx (n ^ (j + 1)) (w.io (j + 1) q) = c * N.tx (n ^ (j + 1)) q) →
      ∀ q, N'.tx (n ^ j) (w.io j q) = c * N.tx (n ^ j) q := by
    intro c j H q
    have hK : (n ^ (j + 1)) ^ 2 = n * ((n ^ j) ^ 2 * n) := by ring
    have hK' : (n ^ (j + 1)) ^ 2 = (n ^ j) ^ 2 * n ^ 2 := by ring
    obtain ⟨g, hg⟩ := hd q.1.2
    have hq := N.mem_QT.1 q.2
    let Q : N.QT ((n ^ (j + 1)) ^ 2) := ⟨(q.1.1 ^ n, g), by
      refine N.mem_QT.2 ?_
      show g ^ (n ^ (j + 1)) ^ 2 = N.io (Multiplicative.toAdd (q.1.1 ^ n))
      rw [hK, pow_mul g n, hg, pow_mul q.1.2, hq, toAdd_pow, N.io_nsmul]⟩
    have t₁ : N.tx (n ^ (j + 1)) Q = N.tx (n ^ j) q := tx_nest N hn hn.pow (pow_succ' n j) Q q rfl hg.symm
    let upq : N.QT ((n ^ (j + 1)) ^ 2) := ⟨(q.1.1 ^ n ^ 2, q.1.2), by
      refine N.mem_QT.2 ?_
      show q.1.2 ^ (n ^ (j + 1)) ^ 2 = N.io (Multiplicative.toAdd (q.1.1 ^ n ^ 2))
      rw [hK', pow_mul q.1.2, hq, toAdd_pow, N.io_nsmul]⟩
    have eQ : Q ^ n = upq := Subtype.ext (Prod.ext (by
      show (q.1.1 ^ n) ^ n = q.1.1 ^ n ^ 2
      rw [← pow_mul, ← sq]) hg)
    have hio := N'.mem_QT.1 (w.io j q).2
    let upio : N'.QT ((n ^ (j + 1)) ^ 2) := ⟨((w.io j q).1.1 ^ n ^ 2, (w.io j q).1.2), by
      refine N'.mem_QT.2 ?_
      show (w.io j q).1.2 ^ (n ^ (j + 1)) ^ 2 = N'.io (Multiplicative.toAdd ((w.io j q).1.1 ^ n ^ 2))
      rw [hK', pow_mul (w.io j q).1.2, hio, toAdd_pow, N'.io_nsmul]⟩
    have E := N'.qEq_equivalence ((n ^ (j + 1)) ^ 2)
    have r₁ : N'.QEq (w.io (j + 1) upq) upio :=
      w.incl j q upq upio (toAdd_pow _ _) rfl (toAdd_pow _ _) rfl
    have r₂ : N'.QEq (w.io (j + 1) Q ^ n) upio := E.trans (E.symm (io_pow w (j + 1) Q n)) (eQ ▸ r₁)
    obtain ⟨z, hz⟩ := (N'.qEq_iff _ _).1 r₂
    set Q' := w.io (j + 1) Q with hQ'
    let q₁ : N'.QT ((n ^ j) ^ 2) := w.io j q * N'.qTriv _ (-z)
    have y₁ : upio.1.1.toAdd = n • Q'.1.1.toAdd + (n * (n * (n ^ j) ^ 2)) • z := by
      rw [hz]
      show n • Q'.1.1.toAdd + (n ^ (j + 1)) ^ 2 • z = _
      exact congrArg (n • Q'.1.1.toAdd + · • z) (by ring)
    have a : upio.1.1.toAdd = (n * n) • (w.io j q).1.1.toAdd := by
      show Multiplicative.toAdd ((w.io j q).1.1 ^ n ^ 2) = _
      rw [toAdd_pow, sq]
    have ey : Q'.1.1 = q₁.1.1 ^ n := by
      apply Multiplicative.toAdd.injective
      refine hX _ _ ?_
      rw [toAdd_pow]
      exact addCommGroup_nsmul_identity n ((n ^ j) ^ 2) _ _ _ z y₁ a
    have eg : q₁.1.2 = Q'.1.2 ^ n := by
      have g₁ : upio.1.2 = Q'.1.2 ^ n * N'.io z := by rw [hz]; rfl
      show (w.io j q).1.2 * N'.io (-z) = _
      rw [N'.io_neg]
      exact (eq_mul_inv_of_mul_eq g₁.symm).symm
    have t₂ : N'.tx (n ^ (j + 1)) Q' = N'.tx (n ^ j) q₁ := tx_nest N' hn hn.pow (pow_succ' n j) Q' q₁ ey eg
    have t₃ : N'.tx (n ^ j) q₁ = N'.tx (n ^ j) (w.io j q) :=
      (GlobalTheory.ModelData.Scalar.tx_congr N' hn.pow ((N'.qEq_iff _ _).2 ⟨-z, rfl⟩)).symm
    rw [← t₃, ← t₂, H Q, t₁]
  have exists_smul_pow_eq_sum_of_inFNc : ∀ (c : C) (j : ℕ), (∀ q, N'.tx (n ^ (j + 1)) (w.io (j + 1) q) = c * N.tx (n ^ (j + 1)) q) →
      ∀ q, N'.tx (n ^ 1) (w.io 1 q) = c * N.tx (n ^ 1) q := fun c j => by
    induction j with
    | zero => exact id
    | succ j ih => exact fun H => ih (down c _ H)
  obtain ⟨q₀, hq₀⟩ := h0
  obtain ⟨c₁, h₁⟩ := hc 1
  refine ⟨c₁, c₁.ne_zero, fun j => ?_⟩
  obtain ⟨c, hj⟩ := hc (j + 1)
  have e : (c : C) = c₁ := mul_right_cancel₀ hq₀ ((exists_smul_pow_eq_sum_of_inFNc c j hj q₀).symm.trans (h₁ q₀))
  rw [← e]
  exact down c j hj

end Scalar

section Tower
attribute [local instance] gtGroup

variable {W : Type} [CommRing W] [IsDomain W] {D D' : DegPre W} (he : D.PsiEven) (hb : D.TauBimult)
  (he' : D'.PsiEven) (hb' : D'.TauBimult) {A : PolAV (Sp (FractionRing W))} {C : Type} [Field C] [IsAlgClosed C]
  [Algebra (FractionRing W) C] {N N' : NumD C} (ν : NumOf D C N) (ν' : NumOf D' C N')

include he in
theorem qPt_add {k : ℕ} {p p' : QkPt D C k} {q q' : N.QT k} (h : ν.QPt p q) (h' : ν.QPt p' q') :
    ν.QPt (qkAdd hb p p') (q * q') := by
  have H := GlobalTheory.Ex.GtValues.points_correspond W D he hb C N ν
  refine ⟨?_, ?_⟩
  · show ν.eX (q.1.1.toAdd + q'.1.1.toAdd) = p.y + p'.y
    rw [map_add (f := _), h.1, h'.1]
  · obtain ⟨c, hc⟩ := (H.1 (qkAdd hb p p').g).exists
    have := (H.2.2.1 p.g p'.g _ _ _ _ h.2 h'.2 hc).1 ((isAdd_iff_eq _ _ _).2 rfl)
    rw [this] at hc
    exact hc


include he hb he' hb' in
theorem exists_tower {f : ∀ k, QkPt D C k → (TFK (R := W) C ⟶ A.A)} {f' : ∀ k, QkPt D' C k → (TFK (R := W) C ⟶ A.A)}
    (G : GoodLab D A C f) (G' : GoodLab D' A C f') (n : ℕ) (hn : 1 ≤ n) :
    ∃ w : TowerIso N N' n, ∀ j p p' q q', ν.QPt p q → ν'.QPt p' q' →
      (N'.QEq (w.io j q) q' ↔ f ((n ^ j) ^ 2) p = f' ((n ^ j) ^ 2) p') := by
  have hk : ∀ j, 1 ≤ (n ^ j) ^ 2 := fun j => Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn)
  have BG := GlobalTheory.Ex.GtValues.points_correspond W D he hb C N ν
  have BG' := GlobalTheory.Ex.GtValues.points_correspond W D' he' hb' C N' ν'
  have BW := GlobalTheory.WeilValues.weil_eq_values GlobalTheory.Ex.GtValues.points_correspond
    (GlobalTheory.Ex.brFam GlobalTheory.firstFiveLaws.1 GlobalTheory.firstFiveLaws.2.1)
  choose P hP using fun k (q : N.QT k) => exists_pt he hb ν q
  choose V hV using fun k (p : QkPt D' C k) => exists_val he' hb' ν' p
  choose S hS using fun j (p : QkPt D C ((n ^ j) ^ 2)) => G'.onto _ (hk j) (f _ p) (G.pow _ (hk j) p)
  have key : ∀ j p p' q q', ν.QPt p q → ν'.QPt p' q' →
      (N'.QEq (V _ (S j (P _ q))) q' ↔ f ((n ^ j) ^ 2) p = f' ((n ^ j) ^ 2) p') := by
    intro j p p' q q' h h'
    rw [← (BG'.2.2.2.2 _).2.2 _ _ _ _ (hV _ _) h', ← G'.eqv _ (hk j), hS, pt_unique he hb ν (hP _ q) h]
  have gpt : ∀ {k l} (p : QkPt D C k) (p₀ : QkPt D C l) (q : N.QT k) (q₀ : N.QT l), ν.QPt p q → ν.QPt p₀ q₀ →
      q.1.2 = q₀.1.2 → p.g = p₀.g := fun p p₀ q q₀ h h₀ e => (BG.2.1 q.1.2).unique h.2 (e ▸ h₀.2)
  have gpt' : ∀ {k l} (p : QkPt D' C k) (p₀ : QkPt D' C l) (q : N'.QT k) (q₀ : N'.QT l), ν'.QPt p q →
      ν'.QPt p₀ q₀ → q.1.2 = q₀.1.2 → p.g = p₀.g := fun p p₀ q q₀ h h₀ e => (BG'.2.1 q.1.2).unique h.2 (e ▸ h₀.2)
  refine ⟨⟨fun j q => V _ (S j (P _ q)), ?_, ?_, ?_, ?_, ?_⟩, key⟩
  · intro j p q
    rw [key j (P _ p) (S j (P _ q)) p _ (hP _ p) (hV _ _), hS, G.eqv _ (hk j)]
    exact (BG.2.2.2.2 _).2.2 _ _ _ _ (hP _ p) (hP _ q)
  · intro j p'
    obtain ⟨p₀', hp₀'⟩ := exists_pt he' hb' ν' p'
    obtain ⟨p, hp⟩ := G.onto _ (hk j) (f' _ p₀') (G'.pow _ (hk j) p₀')
    obtain ⟨q, hq⟩ := exists_val he hb ν p
    exact ⟨q, (key j p p₀' q p' hq hp₀').2 hp⟩
  · intro j p q
    refine (key j (qkAdd hb (P _ p) (P _ q)) (qkAdd hb' (S j (P _ p)) (S j (P _ q))) (p * q) _
      (qPt_add he hb ν (hP _ p) (hP _ q)) (qPt_add he' hb' ν' (hV _ _) (hV _ _))).2 ?_
    rw [G.add _ (hk j) _ _ _ (qkAdd_qkAdd hb _ _), G'.add _ (hk j) _ _ _ (qkAdd_qkAdd hb' _ _), hS, hS]
  · intro j p q q' a b c d
    have hN : (n ^ (j + 1)) ^ 2 = (n ^ j) ^ 2 * n ^ 2 := by ring
    obtain ⟨P'', hP''⟩ := exists_pt he' hb' ν' q'
    refine (key (j + 1) (P _ q) P'' q q' (hP _ q) hP'').2 ?_
    have l₁ : f _ (P _ q) = f _ (P _ p) := G.level _ (n ^ 2) _ (hk j) (Nat.one_le_pow _ _ hn) hN _ _
      (by rw [← (hP _ q).1, ← (hP _ p).1, a, map_nsmul]) (gpt _ _ _ _ (hP _ q) (hP _ p) b)
    have l₂ : f' _ P'' = f' _ (S j (P _ p)) := G'.level _ (n ^ 2) _ (hk j) (Nat.one_le_pow _ _ hn) hN _ _
      (by rw [← hP''.1, ← (hV _ _).1, c, map_nsmul]) (gpt' _ _ _ _ hP'' (hV _ _) d)
    rw [l₁, l₂, hS]
  · intro j p q
    have w₁ := G.weil _ (hk j) _ _ (N.wp p q) ((BW W D he hb C N ν _ (hk j) _ _ _ _ _ (hP _ p) (hP _ q)).2 rfl)
    have w₂ := G'.weil _ (hk j) _ _ (N'.wp (V _ (S j (P _ p))) (V _ (S j (P _ q))))
      ((BW W D' he' hb' C N' ν' _ (hk j) _ _ _ _ _ (hV _ _) (hV _ _)).2 rfl)
    rw [hS, hS] at w₂
    exact Units.ext (congrArg Units.val (unitOn_inj ((GlobalTheory.LevelCompare.weil_existsUnique A _ _ _
      (G.pow _ (hk j) _) (G.pow _ (hk j) _)).unique w₂ w₁)))

end Tower

section Rec
attribute [local instance] gtGroup

theorem recognitionSt : RecognitionSt :=
  recognition_iff.2 (uRecDvr_of_uRec (GlobalTheory.T.degenerationRecognition_of_abelianPartsIsoLabels (GlobalTheory.T.abelianPartsIsoLabels_of_thetaPoint_and_values GlobalTheory.firstFiveLaws.1
    GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion.1 (GlobalTheory.T.abelianPartValues_of_expansionLaws GlobalTheory.firstFiveLaws.1))))

def upQ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    (hb : D.TauBimult) {k : ℕ} (p : QkPt D F k) : QkPt D F (k ^ 2) :=
  qkMk hb (k • p.y) p.g (by rw [sq, mul_nsmul, qk_nsmul hb p, map_nsmul])

theorem rec_trait {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V)
    {D D' : DegData V (maximalIdeal V)} {A : PolAV (Sp (FractionRing V))}
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [Algebra (FractionRing V) C] (hC : CExt V (maximalIdeal V) C) {N N' : NumD C} (ν : NumOf D.toPre C N)
    (ν' : NumOf D'.toPre C N') {f : ∀ k, QkPt D.toPre C k → (TFK (R := V) C ⟶ A.A)}
    {f' : ∀ k, QkPt D'.toPre C k → (TFK (R := V) C ⟶ A.A)} (G : GoodLab D.toPre A C f) (G' : GoodLab D'.toPre A C f')
    {n : ℕ} (hn : n.Prime) (ho : Odd n) (hu : IsUnit (n : V)) (hd : ∀ g : N.Gt, ∃ g', g' ^ n = g)
    (gal : ∀ (σ : C ≃ₐ[FractionRing V] C) (p pσ : QkPt D.toPre C ((n ^ 1) ^ 2)) (p' pσ' : QkPt D'.toPre C ((n ^ 1) ^ 2)),
      QkExt (σ : C →+* C) p pσ → QkExt (σ : C →+* C) p' pσ' → f _ p = f' _ p' → f _ pσ = f' _ pσ')
    (hc : ∀ j, ∃ c : Cˣ, ∀ p p' q q', ν.QPt p q → ν'.QPt p' q' → f ((n ^ j) ^ 2) p = f' _ p' →
      N'.tx (n ^ j) q' = c * N.tx (n ^ j) q)
    (h0 : ∃ q : N.QT ((n ^ 1) ^ 2), N.tx (n ^ 1) q ≠ 0) :
    ∃ e : IsPullDeg (RingHom.id V) D.toPre D'.toPre, ∀ j (p : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)),
      p'.y = e.xe.symm p.y → IsPullGtF (RingHom.id V) e C p.g p'.g → f _ p = f' _ p' := by
  have he := D.psi_even
  have hb := D.tau_bimult
  have he' := D'.psi_even
  have hb' := D'.tau_bimult
  obtain ⟨w, hw⟩ := exists_tower he hb he' hb' ν ν' G G' n hn.one_lt.le
  have hX : ∀ z z' : N'.X, n • z = n • z' → z = z' := fun z z' h => ν'.eX.injective (by
    have h' := congrArg ν'.eX h
    rw [map_nsmul, map_nsmul, ← natCast_zsmul, ← natCast_zsmul] at h'
    exact smul_right_injective _ (Int.natCast_ne_zero.2 hn.ne_zero) h')
  have hc' : ∀ j, ∃ c : Cˣ, ∀ q, N'.tx (n ^ j) (w.io j q) = c * N.tx (n ^ j) q := fun j => by
    obtain ⟨c, hc⟩ := hc j
    refine ⟨c, fun q => ?_⟩
    obtain ⟨p, hp⟩ := exists_pt he hb ν q
    obtain ⟨p', hp'⟩ := exists_pt he' hb' ν' (w.io j q)
    exact hc p p' q _ hp hp' ((hw j p p' q _ hp hp').1 ((N'.qEq_equivalence _).refl _))
  obtain ⟨c₀, -, h₀⟩ := scalar_const ho w hX hd hc' h0
  have hprop : w.Proportional c₀ := fun j q => ⟨N.tx (n ^ j) q, (summable_of_data hV D hC ν ho.pow q).1.hasSum, by
    rw [← h₀ j q]; exact (summable_of_data hV D' hC ν' ho.pow _).1.hasSum⟩
  have hrat : w.RationalAt ν ν' 1 := fun σ p pσ p' pσ' q qσ q' qσ' e₁ e₂ e₃ e₄ e₅ e₆ e₇ =>
    (hw 1 pσ pσ' qσ qσ' e₄ e₆).2 (gal σ p pσ p' pσ' e₁ e₂ ((hw 1 p p' q q' e₃ e₅).1 e₇))
  obtain ⟨e, hI⟩ := recognitionSt V hV D D' n hn ho hu C hC N N' ν ν' w c₀ hprop ⟨1, le_rfl, hrat⟩
  have cC : ArcPull.Compat (RingHom.id V) C := fun _ => rfl
  refine ⟨e, fun j p p' hy hg => ?_⟩
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  have l₁ : f _ (upQ hb p) = f _ p := G.level _ (n ^ j) _ hk hk (sq _) p (upQ hb p) rfl rfl
  have l₂ : f' _ (upQ hb' p') = f' _ p' := G'.level _ (n ^ j) _ hk hk (sq _) p' (upQ hb' p') rfl rfl
  rw [← l₁, ← l₂]
  obtain ⟨q, hq⟩ := exists_val he hb ν (upQ hb p)
  obtain ⟨p₀, p₀', q', h₁, h₂, h₃, h₄⟩ := hI j q
  obtain rfl := pt_unique he hb ν h₁ hq
  have hp₀ : p₀' = upQ hb' p' := by
    refine qk_ext ?_ ?_
    · show p₀'.y = n ^ j • p'.y
      rw [hy, ← map_nsmul]
      exact (e.xe.symm_apply_eq.2 h₃.1.symm).symm
    · have g₁ : IsPullGtF (RingHom.id V) e C (upQ hb p).g p₀'.g := (GlobalTheory.ArcPull.isPullGtF_iff e cC _ _).2 fun z => by
        have := h₃.2 (e.xe.symm z)
        rw [AddEquiv.apply_symm_apply] at this
        simpa using this
      exact GlobalTheory.ArcPull.pullGt_unique e cC g₁ hg
  rw [← hp₀]
  exact (hw j _ _ q q' hq h₂).1 h₄

end Rec

end GlobalTheory.Mum.Recog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantTorsionValuesUltrametric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recog

open GlobalTheory GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.LabTrans GlobalTheory.SeriesCompare GlobalTheory.ArcPull

theorem recognition_core : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → (∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p))) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧ ∀ j : ℕ, ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x' := by
  intro R _ _ _ hR D A lab n hn ho hu hT hgal htheta W _ _ _ hW φ iφ lφ G' _ _ D' A' U' a hG' hfib
  have hV := GlobalTheory.lawsAndExpansions
  have hL : Laws := hV.1.1
  have hL₂ : Laws2 := hV.1.2.1
  have hGF := hL.globalFns
  have := hR.2
  have := hR.1.1
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩

  obtain ⟨W₀, _, _, _, φ₀, G₀, _, _, D₀, A₀, U₀, h₀, a₀, _, em₀, hW₀, i₀, l₀, hG₀, fib₀, c₀, H₀⟩ := hT
  have := hW₀.1
  have := hW₀.2.2
  have b₀ : AdmBase W₀ (maximalIdeal W₀) := ⟨inferInstance, inferInstance, inferInstance, hW₀.2.1⟩
  obtain ⟨g₀, hg₀, hg₀'⟩ := exists_goodLab b₀ hG₀ U₀ (Kb W₀)
  have Glab : GoodLab D.toPre A (Kb R) lab := by
    refine (goodLab_move h₀ c₀ em₀ D₀.tau_bimult fib₀ lab g₀ fun k hk p => ?_).2 hg₀
    obtain ⟨ga₀, hga₀, gp₀, -⟩ := fib₀
    obtain ⟨x, hx⟩ := exists_lift_pt gp₀.1 em₀.toRingHom
      (em₀.comp_algebraMap.trans (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c₀ r).trans
        (congrArg (algebraMap (FractionRing W₀) (Kb W₀)) (hga₀ r).symm)))) (lab k p)
    obtain ⟨p₁, t₁, t₂, t₃⟩ := (lies_iff h₀ c₀ em₀ D₀.tau_bimult p _).2 rfl
    rw [← (hg₀' k hk _ x).1 (H₀ k hk p p₁ _ x t₁ t₂ t₃ hx)]
    exact hx

  haveI := lφ
  obtain ⟨DW, ⟨hWp⟩⟩ := GlobalTheory.MumPull.exists_pull R W φ iφ lφ D
  have hBW := DW.tau_bimult
  obtain ⟨C, _, _, _, _, _, gam, hgam, hC⟩ := GlobalTheory.T.exists_complete_isAlgClosed_cExt' W (Kb W)
  have : CharZero C := (RingHom.charZero_iff (algebraMap (FractionRing W) C).injective).1 inferInstance
  letI : Algebra (FractionRing R) C := ((algebraMap (FractionRing W) C).comp (fracMap iφ)).toAlgebra
  have cC : Compat φ C := fun r => congrArg (algebraMap (FractionRing W) C) (fracMap_algebraMap iφ r)
  obtain ⟨em⟩ := nonempty_lift (FractionRing R) C

  obtain ⟨ε, hε, -, -, -⟩ := exists_ptHom hfib cC em
  let fW : ∀ k, QkPt DW.toPre C k → (TFK (R := W) C ⟶ A'.A) := fun k q =>
    if hk : 1 ≤ k then ε (lab k ((Equiv.ofBijective _ (tr_bij hWp cC em hBW hk)).symm q)) else 1
  have hfW : ∀ k (hk : 1 ≤ k) p, fW k (tr hWp cC em hBW p) = ε (lab k p) := fun k hk p => by
    simp only [fW, dif_pos hk, Equiv.ofBijective_symm_apply_apply]
  have GW : GoodLab DW.toPre A' C fW := (goodLab_move hWp cC em hBW hfib lab fW fun k hk p => by
    rw [hfW k hk p]; exact (hε _ _).1 rfl).1 Glab
  obtain ⟨f', G'', hf'⟩ := exists_goodLab bW hG' U' C

  have hO : CExt W ⊥ C := ⟨hC.1, fun r hr => hC.2 r (bot_le (a := maximalIdeal W) hr)⟩
  have huW : IsUnit (n : W) := by simpa using hu.map φ
  have h1 : ‖(n : C)‖ = 1 := (isUnit_iff_norm hC n).1 huW
  have hnC : (n : C) ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
  obtain ⟨N₁, ν₁, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL W DW.toPre DW.psi_even hBW C ⊤ fun _ => trivial
  obtain ⟨N, ν, q₀, -, hIν, hq₀, -⟩ := exists_integral hW DW hC ν₁
  have hT := GlobalTheory.ValuesTorsion.tors_of_integral hL hL₂ (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) W DW.toPre DW.psi_even hBW C hO N ν hIν n hn
    ho h1
  have hd : ∀ g : N.Gt, ∃ g', g' ^ n = g := fun g => by
    obtain ⟨g', hg'⟩ := (GlobalTheory.Ex.QStr.qStructure C N n _ hnC hT 1).2.1 g
    exact ⟨g', by rw [← hg', pow_one]⟩
  have h0 : ∃ q : N.QT ((n ^ 1) ^ 2), N.tx (n ^ 1) q ≠ 0 := by
    obtain ⟨h, -, -, hh⟩ := (GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N q₀ hq₀ n _ hn ho h1 hT 1 le_rfl).2.2 1
    exact ⟨_, hh⟩
  obtain ⟨N', ν', -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL W D'.toPre D'.psi_even D'.tau_bimult C ⊤ fun _ => trivial

  have galW : ∀ k, (∃ j, k = n ^ j) → ∀ (σ : C ≃ₐ[FractionRing W] C) (p pσ : QkPt DW.toPre C k),
      QkExt (σ : C →+* C) p pσ → (fW k pσ).left = spMap (σ : C →+* C) ≫ (fW k p).left := by
    rintro k ⟨j, rfl⟩ σ p pσ hp
    have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
    obtain ⟨p₀, rfl⟩ := (tr_bij hWp cC em hBW hk).2 p
    let σR : C →ₐ[FractionRing R] C := ⟨(σ : C →+* C), fun t => σ.commutes (fracMap iφ t)⟩
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Kb R →ₐ[FractionRing R] Kb R, em.toRingHom.comp ρ.toRingHom = (σR.comp em).toRingHom := by
      letI : Algebra (Kb R) C := em.toRingHom.toAlgebra
      haveI : IsScalarTower (FractionRing R) (Kb R) C := IsScalarTower.of_algebraMap_eq fun x => (em.commutes x).symm
      exact ⟨(σR.comp em).restrictNormal (Kb R), RingHom.ext fun x => (σR.comp em).restrictNormal_commutes (Kb R) x⟩
    obtain ⟨p₀ρ, hρp⟩ := exists_ext hB ρ p₀
    obtain ⟨p₁, t₁, t₂, t₃⟩ := (lies_iff hWp cC em hBW p₀ _).2 rfl
    obtain ⟨r, hr⟩ := exists_ext hB σR p₁
    have u₁ := qkExt_trans t₁ hr
    obtain ⟨r', hr'⟩ := exists_ext hB em p₀ρ
    have u₂ := qkExt_trans hρp hr'
    rw [hρ] at u₂
    obtain rfl := ext_unique hB (σR.comp em) u₁ u₂
    have e₁ : pσ = tr hWp cC em hBW p₀ρ := (lies_iff hWp cC em hBW p₀ρ pσ).1 ⟨r, hr', by
      rw [hp.1, t₂, hr.1], isPullGtF_ext hWp cC (σ : C →+* C) σ.toAlgHom.comp_algebraMap t₃ hr hp⟩
    rw [e₁, hfW _ hk, hfW _ hk]
    obtain ⟨ga, -, gpa, -⟩ := hfib
    apply gpa.1.hom_ext
    · rw [(hε _ _).1 rfl, Category.assoc, (hε _ _).1 rfl, hgal ρ j p₀ p₀ρ hρp, ← Category.assoc,
        ← Category.assoc, ← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, hρ]
      rfl
    · rw [Category.assoc, Over.w (ε (lab _ p₀ρ)), Over.w (ε (lab _ p₀))]
      exact ((Geo.Tor.spMap_comp _ _).symm.trans (congrArg spMap σ.toAlgHom.comp_algebraMap)).symm
  have gal' : ∀ k, 1 ≤ k → ∀ (σ : C ≃ₐ[FractionRing W] C) (p pσ : QkPt D'.toPre C k),
      QkExt (σ : C →+* C) p pσ → (f' k pσ).left = spMap (σ : C →+* C) ≫ (f' k p).left := by
    intro k hk σ p pσ hp
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds W _ bW D' A' G' hG' U' C C σ.toAlgHom k hk p
    obtain ⟨x', hx'⟩ := hx (f' k p)
    rw [← (hf' k hk pσ x').1 ((hiff pσ (f' k p) x' hp hx').1 ((hf' k hk p _).2 rfl))]
    exact hx'
  have gal : ∀ (σ : C ≃ₐ[FractionRing W] C) (p pσ : QkPt DW.toPre C ((n ^ 1) ^ 2))
      (p' pσ' : QkPt D'.toPre C ((n ^ 1) ^ 2)), QkExt (σ : C →+* C) p pσ → QkExt (σ : C →+* C) p' pσ' →
      fW _ p = f' _ p' → fW _ pσ = f' _ pσ' := fun σ p pσ p' pσ' h₁ h₂ h₃ =>
    Over.OverMorphism.ext (by
      rw [galW _ ⟨2, by ring⟩ σ p pσ h₁, h₃, gal' _ (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn.pos)) σ p' pσ' h₂])

  have BG' := GlobalTheory.Ex.GtValues.points_correspond W D'.toPre D'.psi_even D'.tau_bimult C N' ν'
  have hc : ∀ j, ∃ c : Cˣ, ∀ p p' q q', ν.QPt p q → ν'.QPt p' q' → fW ((n ^ j) ^ 2) p = f' _ p' →
      N'.tx (n ^ j) q' = c * N.tx (n ^ j) q := by
    intro j
    have hm : Odd (n ^ j) := ho.pow
    have hk : 1 ≤ (n ^ j) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn.pos)
    have hum : IsUnit ((n ^ j : ℕ) : R) := by rw [Nat.cast_pow]; exact hu.pow j
    obtain ⟨v, hv⟩ := GlobalTheory.T.degenerationThetaSeries_algebraic_over_fractionField R hR D (n ^ j) hm hum _ id
    have Θ := htheta j v hv
    have hCR : CExt R (maximalIdeal R) C :=
      ⟨fun r => (cC r).symm ▸ hC.1 _, fun r hr => (cC r).symm ▸ hC.2 _ (map_nonunit φ r hr)⟩
    obtain ⟨N₀, ν₀, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL R D.toPre D.psi_even hB C ⊤ fun _ => trivial
    obtain ⟨J, hJX, hJ⟩ := GlobalTheory.Mum.OneTraitTheta.exists_values_iso hL hWp cC ν₀ ν
    choose q₀ hq₀ using fun i : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) =>
      exists_val D.psi_even hB ν₀ (qkExt hB em.toRingHom em.comp_algebraMap i)
    obtain ⟨s, hs⟩ := hv C hCR em N₀ ν₀ (fun i => qkExt hB em.toRingHom em.comp_algebraMap i) q₀
      (fun i => (qkExt_iff hB _ em.comp_algebraMap _ _).2 rfl) hq₀
    choose pp hpp using fun i => G''.onto _ hk (fW _ (tr hWp cC em hBW i)) (GW.pow _ hk _)
    choose qq hqq using fun i => exists_val D'.psi_even D'.tau_bimult ν' (pp i)
    have Q := GlobalTheory.T.theta_constants_eq_degeneration_series hV GlobalTheory.T.torus_torsion_points_correspond_values (GlobalTheory.T.families_values_correspond hL hL₂) W _ hW rfl D' A' G' hG' U' C hC N' ν' (n ^ j) hm _ pp qq
      (fun i => fW _ (tr hWp cC em hBW i)) (fun i => (hf' _ hk _ _).2 (hpp i).symm) hqq
    obtain ⟨c₃, hc₃⟩ := theta_prop hfib cC em hm (x := lab _) (x' := fun i => fW _ (tr hWp cC em hBW i))
      (fun i => by rw [hfW _ hk]; exact (hε _ _).1 rfl) (fun i => GW.pow _ hk _) Θ Q
    refine ⟨c₃ * s * J.lam, fun p p' q q' hp hp' hpp' => ?_⟩
    obtain ⟨i, rfl⟩ := (tr_bij hWp cC em hBW hk).2 p
    obtain ⟨p₁, t₁, t₂, t₃⟩ := (lies_iff hWp cC em hBW i _).2 rfl
    obtain rfl := (qkExt_iff hB _ em.comp_algebraMap _ _).1 t₁
    have e₁ : N'.tx (n ^ j) (qq i) = N'.tx (n ^ j) q' :=
      GlobalTheory.ModelData.Scalar.tx_congr N' hm (((BG'.2.2.2.2 _).2.2 _ _ _ _ (hqq i) hp').1
        ((G''.eqv _ hk _ _).1 ((hpp i).trans hpp')))
    have e₂ := (GlobalTheory.RelabelCoords.series_iso J hm (p := q) (p' := q₀ i) (ν₀.eX.injective (by
      rw [hJX, hp.1, t₂, AddEquiv.apply_symm_apply]; exact (hq₀ i).1)) (hJ _ _ _ _ (hq₀ i).2 hp.2 t₃)).1
    rw [← e₁, hc₃ i, hs i, e₂, Units.val_mul, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc,
      Units.mul_inv_cancel_left]

  obtain ⟨e, he⟩ := rec_trait hW hC ν ν' GW G'' hn ho huW hd gal hc h0
  obtain ⟨hD, T⟩ := GlobalTheory.LabTrans.exists_comp iφ Function.injective_id hWp e
  refine ⟨hD, C, inferInstance, inferInstance, inferInstance, inferInstance, em, cC, fun j p p₁ p'' x' h₁ h₂ h₃ h₄ => ?_⟩
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  refine (hf' _ hk p'' x').2 ?_
  obtain rfl := (qkExt_iff hB _ em.comp_algebraMap _ _).1 h₁
  rw [(hε _ _).2 h₄, ← hfW _ hk p]
  obtain ⟨p₁', t₁, t₂, t₃⟩ := (lies_iff hWp cC em hBW p _).2 rfl
  obtain rfl := (qkExt_iff hB _ em.comp_algebraMap _ _).1 t₁
  have cI : Compat (RingHom.id W) C := fun _ => rfl
  have g₁ := T.isPullGtF cC t₃ (isPullGtF_pullGt e hGF cI (tr hWp cC em hBW p).g)
  have g₂ := pullGt_unique hD cC g₁ h₃
  refine he j _ _ ?_ ?_
  · apply hD.xe.injective
    rw [h₂, AddEquiv.apply_symm_apply, ← T.xe_eq, AddEquiv.apply_symm_apply, t₂, AddEquiv.apply_symm_apply]
  · rw [← g₂]
    exact isPullGtF_pullGt e hGF cI _

end GlobalTheory.Mum.Recog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantTorsionValuesUltrametricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_equivariant_torsion_values_ultrametric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → (∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p))) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧ ∀ j : ℕ, ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x' := by
  first | exact @GlobalTheory.Mum.Recog.recognition_core | exact GlobalTheory.Mum.Recog.recognition_core | (intros; apply GlobalTheory.Mum.Recog.recognition_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RecognitionDegDataLabelsAtEveryTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recognition

theorem pullDeg_induces : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∀ j : ℕ, Induces lab φ U' hD a (n ^ j) := by
  intro R _ _ _ hR D A lab n hn ho hu hOT hGal W _ _ _ hW φ hφ hloc G' _ _ D' A' U' a hG hF
  obtain ⟨hD, C, i1, i2, i3, i4, em, hc, hP⟩ := GlobalTheory.T.galois_equivariant_torsion_values_ultrametric R hR D A lab n hn ho hu hOT hGal
    (GlobalTheory.T.isThetaPoint_of_algebraic_series_one_trait R hR D A lab n hn ho hu hOT) W hW φ hφ hloc G' D' A' U' a hG hF
  exact ⟨hD, fun j => GlobalTheory.T.labels_induced_all_embeddings_of_galois R hR D A lab n hn ho hu hGal W hW φ hφ hloc G' D' A' U' a hG hF hD j
    ⟨C, i1, i2, i3, i4, em, hc, hP j⟩⟩

end GlobalTheory.Mum.Recognition
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RecognitionDegDataLabelsAtEveryTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recognition_degData_labels_at_every_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∀ j : ℕ, Induces lab φ U' hD a (n ^ j) := by
  first | exact @GlobalTheory.Mum.Recognition.pullDeg_induces | exact GlobalTheory.Mum.Recognition.pullDeg_induces | (intros; apply GlobalTheory.Mum.Recognition.pullDeg_induces <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLabelledCoverOfOddPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.UCoverLab

theorem jK_mono (R : Type) [CommRing R] [IsDomain R] : Mono (jK R) := by
  haveI : Scheme.Spec.IsRightAdjoint := ΓSpec.adjunction.isRightAdjoint
  have : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))).op) := inferInstance
  exact this

theorem gp_mono {R : Type} [CommRing R] [IsDomain R] (M : Modif R) : Mono M.gp := by
  have : Mono (M.gp ≫ M.π) := by rw [M.gp_π]; exact jK_mono R
  exact mono_of_mono M.gp M.π

theorem mono_α {R : Type} [CommRing R] [IsDomain R] {M : Modif R} {X : Over M.S} [GrpObj X]
    {A : Over (Sp (FractionRing R))} [GrpObj A] {α : A.left ⟶ X.left} (h : IsGrpPullback A X M.gp α) : Mono α := by
  haveI := gp_mono M
  refine ⟨fun u v huv => h.1.hom_ext huv ?_⟩
  apply (cancel_mono M.gp).1
  rw [Category.assoc, Category.assoc, ← h.1.w, ← Category.assoc, huv, Category.assoc]

end GlobalTheory.Mum.UCoverLab


open GlobalTheory.Mum.UCoverLab GlobalTheory.Mum.CoverFin in
theorem GlobalTheory.Mum.UCover.labCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : UCover R) (lab : Labels D.toPre C.A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre C.A lab → GalEqN n lab → Nonempty (LabCover D) := by
  intro R _ _ _ hB D C lab n hn ho hu hone hgal
  refine ⟨{ toModif := C.toModif
            G := C.G
            semi := C.semi
            P := C.P
            A := C.A
            α := C.α
            α_cart := C.α_cart
            α_lb := C.α_lb
            n := n
            n_prime := hn
            n_odd := ho
            n_unit := hu
            lab := fun j => lab (n ^ j)
            trait := ?_ }⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G', _, _, β, D', A', U', hW', hio, hfin, hcart, hlb⟩ := C.trait W hW φ ξ hφ hξ
  haveI : IsLocalHom io := hfin.to_isIntegral.isLocalHom hio
  have hsemi : IsSemiAbelian G' := semiAbelian_of_pull hcart C.semi
  have hγ : IsGrpPullback A'.A G' (jK W') (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) :=
    GlobalTheory.ThetaBaseChange.grp_generic U'.toUnifPre
  have hinj : Function.Injective ((algebraMap W' (FractionRing W')).comp (io.comp φ)) :=
    (IsFractionRing.injective W' _).comp (hio.comp hφ)
  obtain ⟨ga, hga, hy⟩ := GlobalTheory.T.exists_factor_field_point_through_generic_point R C.toModif (FractionRing W') _ (jK W' ≫ spMap io ≫ ξ) hinj (by
    rw [Category.assoc, Category.assoc, hξ]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl)
  have hcomp : IsGrpPullback A'.A C.G (spMap ga ≫ C.gp) ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β) :=
    (hγ.comp hcart).congr hy rfl
  let a : A'.A.left ⟶ C.A.A.left := C.α_cart.1.lift ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)
    (A'.A.hom ≫ spMap ga) (by rw [hcomp.1.w, Category.assoc])
  have ha : a ≫ C.α = (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β := C.α_cart.1.lift_fst _ _ _
  have ha2 : a ≫ C.A.A.hom = A'.A.hom ≫ spMap ga := C.α_cart.1.lift_snd _ _ _
  have hcart' : IsGrpPullback A'.A C.A.A (spMap ga) a := IsGrpPullback.cancel C.α_cart (hcomp.congr rfl ha.symm) ha2
  have hgi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hA' : LBIso A'.L (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W'))) :=
    LBIso.chartPull (h := U'.gen.inv.left) (chartPullSec A'.L _ _ hgi)
      (chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK W')) _ _ fun _ => rfl) U'.ext
  have h2 : LBIso (U'.LG.L.pull (U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')))
      (C.P.L.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)) :=
    LBIso.chartPull (chartPullPull U'.LG.L _) (chartPullSame C.P.L.L _ _ _ _ fun _ => rfl) hlb
  have h3 : LBIso A'.L (C.P.L.L.pull ((U'.gen.inv.left ≫ pullback.fst G'.hom (jK W')) ≫ β)) :=
    LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB C.P.L.isLB _) hA' h2
  have hfib : IsFib (io.comp φ) C.A A' a :=
    ⟨ga, fun r => hga r, hcart', lbIso_factor C.P.L.isLB C.A.isLB A'.isLB ha C.α_lb h3⟩
  obtain ⟨hD, hind⟩ := GlobalTheory.T.recognition_degData_labels_at_every_trait R hB D C.A lab n hn ho hu hone hgal W' hW' (io.comp φ) (hio.comp hφ)
    inferInstance G' D' A' U' a hsemi hfib
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G', inferInstance, inferInstance, β, D', A', U', hD, hW',
    hio, hfin, hcart, hlb, ?_⟩
  intro F _ _ _ _ em hF j p p₁ p' x' h₁ h₂ h₃ h₄
  refine hind j F em hF p p₁ p' x' h₁ h₂ h₃ ?_
  haveI := mono_α C.α_cart
  rw [← cancel_mono C.α, Category.assoc, ha]
  simpa only [Category.assoc] using h₄
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLabelledCoverOfOddPrimeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_labelled_cover_of_odd_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : UCover R) (lab : Labels D.toPre C.A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre C.A lab → GalEqN n lab → Nonempty (LabCover D) := by
  first | exact @GlobalTheory.Mum.UCover.labCover | exact GlobalTheory.Mum.UCover.labCover | (intros; apply GlobalTheory.Mum.UCover.labCover <;> assumption)
end
