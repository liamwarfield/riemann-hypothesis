module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverFrameCoordinates
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RmulMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumClsLeEncard

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespond
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespond
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.CoordTermWt
open GlobalTheory.HL.CoordTerm

lemma unitri_mem {E W : Type} [CommRing E] [AddCommGroup W] [Module E W] {m : ℕ} (g g' : Fin m → W)
    (s : Matrix (Fin m) (Fin m) E) (h0 : ∀ i j, j < i → s i j = 0) (h1 : ∀ i, s i i = 1)
    (hs : ∀ j, g' j = ∑ i, s i j • g i) (A : Submodule E W) :
    (∀ b, g' b ∈ A) ↔ ∀ b, g b ∈ A := by
  constructor
  · intro h j
    induction j using WellFoundedLT.induction with
    | ind j ih =>
      have h2 : g j = g' j - ∑ i ∈ Finset.univ.erase j, s i j • g i := by
        rw [hs, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), h1, one_smul, add_sub_cancel_right]
      rw [h2]
      refine sub_mem (h j) (Submodule.sum_mem _ fun i hi => ?_)
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h3 | h3
      · exact A.smul_mem _ (ih i h3)
      · rw [h0 i j h3, zero_smul]; exact zero_mem _
  · intro h j
    rw [hs]
    exact Submodule.sum_mem _ fun i _ => A.smul_mem _ (h i)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)

lemma fam_mem {R : Type} [Ring R] [Module R V] (t : Term V M r) (A : Submodule R V) :
    (∀ i, H.MMfam t i ∈ A) ↔ (∀ b, t.f b ∈ A) ∧
      ∀ b, algebraMap F E (LocNG.theta M)⁻¹ • (t.f' b - t.f b) ∈ A := by
  unfold HermSp.MMfam LocNG.theta
  cases M.split with
  | none =>
    simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, inv_one, map_one, one_smul]
    refine and_congr_right fun h => forall_congr' fun b => ?_
    exact (A.sub_mem_iff_left (h b)).symm
  | some g => simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr]

lemma th_ne (S : Frames M.L r k) : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h
    exact S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

lemma lat_span (t : Term V M r) :
    c.lat (Submodule.span M.L.O (Set.range (H.MMfam t))) =
      S.Mof (fun b => c.e (t.f b)) (fun b => c.e (t.f' b)) := by
  refine eq_of_forall_ge_iff fun A => ?_
  unfold Coord.lat Frames.Mof
  rw [Submodule.map_le_iff_le_comap, Submodule.span_le, Submodule.span_le, Set.range_subset_iff,
    Set.union_subset_iff, Set.range_subset_iff, Set.range_subset_iff]
  refine (fam_mem t _).trans ?_
  rw [CoordUnip.theta_eq c]
  simp [Submodule.mem_comap]

lemma map_span (t : Term V M r) (A : Submodule E S.V) :
    (Submodule.span E (Set.range (H.MMfam t))).map (c.e : V →ₗ[E] S.V) ≤ A ↔
      (∀ b, c.e (t.f b) ∈ A) ∧ ∀ b, c.e (t.f' b) ∈ A := by
  rw [Submodule.map_le_iff_le_comap, Submodule.span_le, Set.range_subset_iff]
  refine (fam_mem t _).trans ?_
  rw [CoordUnip.theta_eq c]
  refine and_congr_right fun h => forall_congr' fun b => ?_
  have hu : IsUnit (algebraMap F E S.th⁻¹) := (IsUnit.mk0 _ (inv_ne_zero (th_ne S))).map _
  rw [Submodule.smul_mem_iff_of_isUnit _ hu, Submodule.sub_mem_iff_left _ (h b)]
  rfl

lemma ME_le (S : Frames M.L r k) (A : Submodule E S.V) :
    S.ME ≤ A ↔ (∀ b, S.f b ∈ A) ∧ ∀ b, S.f' b ∈ A := by
  unfold Frames.ME Frames.spanTo
  have h : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
    exact Set.eq_univ_of_forall fun i => i.2
  rw [sup_le_iff, Submodule.span_le, Submodule.span_le, h, Set.image_univ, Set.image_univ,
    Set.range_subset_iff, Set.range_subset_iff]
  rfl

theorem terms_correspond : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → ∃ t, LocNG.IsTermOver P d t ∧ c.lat t.abelian₂ = Λ) ∧ ∀ δ Λ, S.IsTerm δ Λ → ∃ d : LocNG.Datum P, δ = c.dat d := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨hth, hN, hN', -, hpsi, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  obtain ⟨-, iA, oA, sA⟩ := GlobalTheory.T.hermitianFrameCoordinates_transport_innerLattices M hM H r k P S c
  obtain ⟨-, iB, oB, sB⟩ := GlobalTheory.T.framePairCoordinates_transport_innerLattices M hM H r k P S c
  have T1 := isTermW_iff M hM H r k P S c
  have hsurj : ∀ Λ : Submodule M.L.O S.V, ∃ Λ₀, c.lat Λ₀ = Λ := by
    intro B
    refine ⟨B.comap ((c.e : V →ₗ[E] S.V).restrictScalars M.L.O), ?_⟩
    ext v
    obtain ⟨v, rfl⟩ := c.e.surjective v
    rw [mem_lat]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rintro d ⟨Λ, f, f', T, T'⟩ ht
    obtain ⟨hT, hT', ⟨n, hn, hf, h1⟩, ⟨n', hn', hf', h2⟩, -⟩ := id ht
    dsimp only at hT hT' hf hf' h1 h2
    subst hT hT' hf hf'
    have hW := (T1 d n n' Λ).1 ⟨ht, hn, hn', h1, h2⟩
    have hI : S.IsTerm (c.dat d) (c.lat Λ) := ⟨(c.grp n, c.grp n'), hW⟩
    obtain ⟨w1, w2, -⟩ := GlobalTheory.HL.WitIndep.witness_independence M.L r k S _ _ _ _ hW
    obtain ⟨-, -, hle, -⟩ := GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hI
    refine ⟨hI, ?_, ?_⟩
    · dsimp only
      rw [w1, ← (hpsi n).1, ← (hpsi n').2]
      rfl
    · dsimp only
      set t : Term V M r := ⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ with htd
      have e1 : ∀ b, c.e (t.f b) = c.grp n (S.f b) := fun b => by rw [c.f_eq, grp_e]
      have e2 : ∀ b, c.e (t.f' b) = c.grp n' (S.f' b) := fun b => by rw [c.f'_eq, grp_e]
      have hO : c.lat (Submodule.span M.L.O (Set.range (H.MMfam t))) = S.M (c.dat d) (c.lat Λ) := by
        rw [lat_span, w2]
        simp only [e1, e2]
      obtain ⟨o1, o2, -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto M.L r k S
      obtain ⟨s, ⟨s0, s1⟩, hs⟩ := o1 _ hW.2.2.1
      obtain ⟨s', ⟨s0', s1'⟩, hs'⟩ := o2 _ hW.2.2.2.1
      have hE : (Submodule.span E (Set.range (H.MMfam t))).map (c.e : V →ₗ[E] S.V) = S.ME := by
        refine eq_of_forall_ge_iff fun A => ?_
        rw [map_span, ME_le]
        simp only [e1, e2]
        exact and_congr (unitri_mem _ _ s s0 s1 hs A) (unitri_mem _ _ s' s0' s1' hs' A)
      have hE' : ∀ v, c.e v ∈ S.ME ↔ v ∈ Submodule.span E (Set.range (H.MMfam t)) := by
        intro v
        rw [← hE]
        constructor
        · rintro ⟨y, hy, h⟩
          have : y = v := c.e.injective h
          exact this ▸ hy
        · intro h; exact ⟨v, h, rfl⟩
      have hsat : ∀ v, c.e v ∈ S.sat (c.lat Λ) ↔
          v ∈ Λ ∧ v ∈ Submodule.span E (Set.range (H.MMfam t)) := by
        intro v
        rw [← hE', ← mem_lat c]
        rfl
      unfold Frames.BBzero
      constructor
      · rintro ⟨v, hv, hv1, hv2⟩ h
        apply hv2
        rw [← mem_lat c, hO, h, hsat]
        exact ⟨hv, hv1⟩
      · intro h
        by_contra hc
        apply h
        refine le_antisymm hle fun y hy => ?_
        obtain ⟨v, rfl⟩ := c.e.surjective y
        rw [hsat] at hy
        rw [← hO, mem_lat]
        by_contra hv
        exact hc ⟨v, hy.1, hy.2, hv⟩
  · rintro d Λ ⟨⟨n, n'⟩, hW⟩
    obtain ⟨Λ, rfl⟩ := hsurj Λ
    obtain ⟨n, rfl⟩ := c.grp.surjective n
    obtain ⟨n', rfl⟩ := c.grp.surjective n'
    exact ⟨_, ((T1 d n n' Λ).2 hW).1, rfl⟩
  · rintro δ Λ hI
    obtain ⟨⟨n, n'⟩, hA, hB, hn, hn', h1, h2, hc, -⟩ := id hI
    dsimp only at hn hn' h1 h2 hc
    obtain ⟨Λ, rfl⟩ := hsurj Λ
    obtain ⟨n, rfl⟩ := c.grp.surjective n
    obtain ⟨n', rfl⟩ := c.grp.surjective n'
    obtain ⟨L, hL⟩ := oA _ hA
    obtain ⟨L', hL'⟩ := oB _ hB
    rw [hL, ← iA] at hA
    rw [hL', ← iB] at hB
    rw [hL, ← sA, ← lat_img, lat_inj] at h1
    rw [hL', ← sB, ← lat_img, lat_inj] at h2
    rw [← hN] at hn
    rw [← hN'] at hn'
    let d : LocNG.Datum P :=
      { L := L, L' := L', hL := hA, hL' := hB
        io := {q | ∃ g, M.split = some g ∧ q ∈ H.iotaGraph g ⟨Λ, P.A.f, P.B.f, P.A.T, P.B.T⟩}
        io_L := fun h => by simp [h] }
    have hW := (T1 d n n' Λ).1 ⟨⟨rfl, rfl, ⟨n, hn, rfl, h1⟩, ⟨n', hn', rfl, h2⟩, fun g hg => ⟨?_, ?_⟩⟩,
      hn, hn', h1, h2⟩
    · obtain ⟨-, -, -, -, -, -, -, hu⟩ := GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hI
      exact ⟨d, (hu _ ⟨(c.grp n, c.grp n'), hW⟩).symm⟩
    · intro b
      have hq : S.th = (g.q : F) := by rw [← hth, LocNG.theta, hg]
      have h := hc b
      rwa [c.f_eq, c.f'_eq, grp_e, grp_e, ← map_sub, inTh_iff, hq] at h
    · ext q
      simp [d, hg]

end GlobalTheory.HL.CoordTermWt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespondStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → ∃ t, LocNG.IsTermOver P d t ∧ c.lat t.abelian₂ = Λ) ∧ ∀ δ Λ, S.IsTerm δ Λ → ∃ d : LocNG.Datum P, δ = c.dat d := by
  first | exact @GlobalTheory.HL.CoordTermWt.terms_correspond | exact GlobalTheory.HL.CoordTermWt.terms_correspond | (intros; apply GlobalTheory.HL.CoordTermWt.terms_correspond <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

theorem _root_.GlobalTheory.RowLev.intAf_approx_inter_unit_conj : ∀ (I : _root_.Formalism.MainNotions.S.AutInst) (g : ℕ), 1 ≤ g →
    (∀ z ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E, ∃ a : 𝓞 I.E, ∃ z' ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E,
      z = _root_.Formalism.UG.inclE (F := I.F) (_root_.Formalism.MainNotions.S.Af I.F) (a : I.E) + (g : (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F)) * z') ∧
    (∀ a : I.E, _root_.Formalism.UG.inclE (F := I.F) (_root_.Formalism.MainNotions.S.Af I.F) a ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E ↔
      a ∈ (algebraMap (𝓞 I.E) I.E).range) ∧
    IsUnit (g : (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F)) ∧
    ∀ z ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E, _root_.Formalism.UG.sigR I.cm.sig (_root_.Formalism.MainNotions.S.Af I.F) z ∈ _root_.Formalism.MainNotions.S.IntAf I.F I.E := by
  intro I g hg
  have hg0 : g ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨b, t, hbt⟩ := _root_.GlobalTheory.RowLev.Inhab.exists_approx (F := I.F) (E := I.E) hg0 ⟨z, hz⟩
    refine ⟨b, t, t.2, ?_⟩
    have h := congrArg Subtype.val hbt
    simpa [_root_.GlobalTheory.RowLev.Inhab.psi] using h
  · intro a
    constructor
    · intro ha
      have hint : IsIntegral ℤ a := _root_.Formalism.UG.P.csGlob_int a ha
      exact ⟨⟨a, hint⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact _root_.Formalism.UG.CS.incl_int b
  · have hF : IsUnit (g : I.F) := isUnit_iff_ne_zero.mpr (by exact_mod_cast hg0)
    simpa using hF.map (algebraMap I.F (I.E ⊗[I.F] _root_.Formalism.MainNotions.S.Af I.F))
  · intro z hz
    exact _root_.Formalism.UG.P.csDual_sig_mem _ hz

end GlobalTheory.RowLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Equality
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GoodPlace

theorem equality : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → S.gg = false → vE L S.ϖ S.G = 0 → (∀ l, S.D l ≠ 0 → vE L S.ϖ (S.D l * L.cj (S.D l)) = 0) → (∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ) ∧ S.Hp = 1 ∧ (S.ampSq fun _ _ => True) = S.nn ∧ ∀ d, (S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ hgg hG hD
  have hvth : S.vth = 0 := by simp [Frames.vth, hgg]
  have ha : S.a = 0 := by simp [Frames.a, hvth, hG]
  have hvD : S.vD = 0 := Finset.sum_eq_zero fun l _ => by
    split_ifs with h
    · exact hD l h.2
    · rfl
  have huniq := fun d Λ h => GlobalTheory.HL.UnimodTerm.term_unique L r k S d Λ h ha
  have key : ∀ d, ((S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1) ∧
      ENNReal.ofReal (‖S.amp d fun _ => True‖ ^ 2) = S.mass d fun _ => True := by
    intro d
    by_cases hex : ∃ Λ, S.IsTerm d Λ
    swap
    · have h0 : ∀ Λ, ¬ S.IsTerm d Λ := fun Λ h => hex ⟨Λ, h⟩
      simp [Frames.mass, Frames.amp, h0]
    obtain ⟨Λ₀, h₀⟩ := hex
    obtain ⟨-, -, hDO, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ₀ h₀
    obtain ⟨-, -, -, -, hDu, -⟩ := GlobalTheory.FrameBasic.main L r k S
    obtain ⟨-, -, -, hvu⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
    have hunit : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1 := by
      intro l hl
      refine ⟨hDO l, ?_⟩
      obtain ⟨e, he⟩ := GlobalTheory.UnramOrder.exists_norm L (hDO l)
      have he0 : (e : F) ≠ 0 := fun h0 => by
        rw [h0, map_zero] at he
        apply hl
        rw [← L.cj_cj (S.D l), (hDu l hl).mul_right_eq_zero.1 he, map_zero]
      obtain ⟨u, hu⟩ := hvu _ he0
      rw [← he, hD l hl, zpow_zero, one_mul] at hu
      refine ⟨L.cj (S.D l) * algebraMap F E (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F),
        L.O.mul_mem (GlobalTheory.UnramOrder.cj_mem L (hDO l))
          ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subtype.property _)), ?_⟩
      rw [← mul_assoc, he, ← map_mul, hu, ← Subring.coe_mul, Units.mul_inv]
      simp
    obtain ⟨hC0, hw0, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hgg hunit
    set C0 := S.frameCls S.f S.f' with hC0def
    have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d
    have hint : ∀ Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun Λ h =>
      (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1

    have hm : (S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1 := by
      rw [mass_eq_sumCls L r k S d _ (fun _ _ _ _ _ => trivial)]
      unfold Frames.sumCls
      let o₀ : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ C0
      rw [tsum_eq_single o₀ (fun o ho => if_neg fun hI => ho (by
        obtain ⟨h, hh, e⟩ := hall _ hI
        rw [← Quotient.out_eq o]
        exact Quotient.sound ⟨⟨h, hh⟩, e.symm⟩))]
      split_ifs with hI
      swap
      · exact Or.inl rfl
      obtain ⟨h, hh, e⟩ := hall _ hI
      have hw : S.wC o₀.out = 1 := by
        rw [e, ((volSt L r k S).2 C0 hC0.1).2.2.2 h hh, hw0]
      rw [hw, ENNReal.ofReal_one, one_mul]
      have hs : ({Λ | S.IsTerm d Λ ∧ True ∧ S.Fr d Λ = o₀.out} : Set (Submodule L.O S.V)).Subsingleton :=
        fun Λ hΛ Λ' hΛ' => (huniq d Λ' hΛ'.1).2 Λ hΛ.1 (hΛ.2.2.trans hΛ'.2.2.symm)
      unfold Frames.nT
      beta_reduce
      rcases hs.eq_empty_or_singleton with h1 | ⟨x, h1⟩
      · left; rw [h1]; simp
      · right; rw [h1]; simp
    refine ⟨hm, ?_⟩

    let o₁ : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) := Quotient.mk _ Λ₀
    have hone : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o ≠ o₁ →
        ¬ (S.IsTerm d o.out ∧ True) := by
      intro o ho hT
      apply ho
      obtain ⟨h, hh, e⟩ := hall _ (hint _ hT.1)
      obtain ⟨h', hh', e'⟩ := hall _ (hint _ h₀)
      have hmem : h * h'⁻¹ ∈ S.St := S.St.mul_mem hh (S.St.inv_mem hh')
      have hA := hact Λ₀ h₀ _ hmem
      have e2 : (h * h'⁻¹) • Λ₀ = o.out := (huniq d _ hT.1).2 _ hA.1 (by
        rw [hA.2.2.2.2.1, e', e, smul_smul, inv_mul_cancel_right])
      rw [← Quotient.out_eq o]
      exact Quotient.sound ⟨⟨_, hmem⟩, e2⟩
    have e1 : (S.mass d fun _ => True) =
        if S.IsTerm d o₁.out ∧ True then ENNReal.ofReal (S.mu o₁.out) else 0 := by
      unfold Frames.mass
      rw [tsum_eq_single o₁]
      · congr
      · exact fun o ho => if_neg (hone o ho)
    have e2 : (S.amp d fun _ => True) =
        if S.IsTerm d o₁.out ∧ True then (S.mu o₁.out : ℂ) * S.om d o₁.out else 0 := by
      unfold Frames.amp
      rw [tsum_eq_single o₁]
      · congr
      · exact fun o ho => if_neg (hone o ho)
    rw [e1] at hm ⊢
    rw [e2]
    by_cases hT : S.IsTerm d o₁.out ∧ True
    swap
    · simp only [if_neg hT]; simp
    simp only [if_pos hT] at hm ⊢
    have hom : ‖S.om d o₁.out‖ = 1 := by
      obtain ⟨p, hp⟩ := hT.1
      exact (WitIndep.witness_independence L r k S d _ _ _ hp).2.2.2.2
    have hmu : 0 ≤ S.mu o₁.out := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    rw [norm_mul, hom, mul_one, Complex.norm_real, Real.norm_of_nonneg hmu]
    rcases hm with h | h
    · rw [le_antisymm (ENNReal.ofReal_eq_zero.1 h) hmu]; simp
    · rw [ENNReal.ofReal_eq_one.1 h]; simp
  refine ⟨fun d Λ h => (huniq d Λ h).1, by simp [Frames.Hp, hvth, ha, hvD], ?_, fun d => (key d).1⟩
  unfold Frames.ampSq Frames.nn
  congr 1
  funext d
  exact (key d).2

end GlobalTheory.HL.GoodPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesLocalTermsWithData
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesLocalTermsWithData
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.LocalMove

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ h ∈ P.UW0, ∀ (d d' : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Moves h d d' → LocNG.IsTermOver P d' ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ∧ (LocNG.BBne (H := H) ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ↔ LocNG.BBne (H := H) τ) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP h hh d d' τ hτ hmv
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hrk hP
  obtain ⟨hH0, -, -, hlat, -⟩ := GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  obtain ⟨-, hmov, -⟩ := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  obtain ⟨-, hNA, hNB, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hh0 : c.grp h ∈ S.H0 := (hH0 h).1 hh
  have ge : ∀ (g : V ≃ₗ[E] V) (x : V), c.grp g (c.e x) = c.e (g x) := GlobalTheory.HL.CoordTerm.grp_e c
  obtain ⟨Λ, f, f', T, T'⟩ := τ
  obtain ⟨hT, hT', ⟨n, hn, hf, hΛ⟩, ⟨n', hn', hf', hΛ'⟩, hG⟩ := hτ
  dsimp only at hT hT' hf hΛ hf' hΛ' hG ⊢
  subst hT hT' hf hf'

  have fixA : ∀ b, h (n (P.A.f b)) = n (P.A.f b) := by
    intro b
    apply c.e.injective
    rw [← ge, ← ge, ← c.f_eq]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh0 _ (Submodule.mem_sup_left
      (GlobalTheory.HL.ComplAct.nof_mem S (Or.inl ⟨rfl, rfl⟩) ((hNA n).1 hn) (GlobalTheory.HL.ComplAct.mem_spanTo S _ b)))
  have fixB : ∀ b, h (n' (P.B.f b)) = n' (P.B.f b) := by
    intro b
    apply c.e.injective
    rw [← ge, ← ge, ← c.f'_eq]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh0 _ (Submodule.mem_sup_right
      (GlobalTheory.HL.ComplAct.nof_mem S (Or.inr ⟨rfl, rfl⟩) ((hNB n').1 hn') (GlobalTheory.HL.ComplAct.mem_spanTo S _ b)))
  simp only [fixA, fixB]
  refine ⟨?_, ?_⟩
  · have hW := (GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d n n' Λ).1
      ⟨⟨rfl, rfl, ⟨n, hn, rfl, hΛ⟩, ⟨n', hn', rfl, hΛ'⟩, hG⟩, hn, hn', hΛ, hΛ'⟩
    obtain ⟨m, m', hW', hm, hm'⟩ := GlobalTheory.HL.ComplAct.termW S hW hh0
    rw [(hmov h hh d d').1 hmv, ← hlat] at hW'
    obtain ⟨m0, rfl⟩ := c.grp.surjective m
    obtain ⟨m0', rfl⟩ := c.grp.surjective m'
    have e1 : (fun b => m0 (P.A.f b)) = fun b => n (P.A.f b) := by
      funext b; apply c.e.injective; rw [← ge, ← ge, ← c.f_eq]; exact hm b
    have e2 : (fun b => m0' (P.B.f b)) = fun b => n' (P.B.f b) := by
      funext b; apply c.e.injective; rw [← ge, ← ge, ← c.f'_eq]; exact hm' b
    have := ((GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d' m0 m0' (LocNG.img h Λ)).2 hW').1
    rw [e1, e2] at this
    exact this
  ·
    set t : Term V M r := ⟨Λ, fun b => n (P.A.f b), fun b => n' (P.B.f b), P.A.T, P.B.T⟩ with ht
    have fam : ∀ i, h (H.MMfam t i) = H.MMfam t i := by
      intro i
      unfold HermSp.MMfam
      cases M.split with
      | none => rcases i with b | b <;> simp [ht, fixA, fixB]
      | some g => rcases i with b | b <;> simp [ht, fixA, fixB, map_sub]
    have fixS : ∀ x ∈ Submodule.span E (Set.range (H.MMfam t)), h x = x := by
      intro x hx
      have := LinearMap.eqOn_span' (f := (h : V →ₗ[E] V)) (g := LinearMap.id)
        (s := Set.range (H.MMfam t)) (by rintro _ ⟨i, rfl⟩; exact fam i) hx
      simpa using this
    change (∃ v ∈ LocNG.img h Λ, _) ↔ ∃ v ∈ Λ, _
    constructor
    · rintro ⟨v, hv, hE, hO⟩
      obtain ⟨w, hw, rfl⟩ := hv
      have hw' : h w = w := by
        have := fixS _ hE
        exact h.injective (by simpa using this)
      simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hE hO ⊢
      rw [hw'] at hE hO
      exact ⟨w, hw, hE, hO⟩
    · rintro ⟨v, hv, hE, hO⟩
      exact ⟨v, ⟨v, hv, fixS v hE⟩, hE, hO⟩

end GlobalTheory.HL.LocalMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesLocalTermsWithDataStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryComplement_moves_local_terms_with_data : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ h ∈ P.UW0, ∀ (d d' : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Moves h d d' → LocNG.IsTermOver P d' ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ∧ (LocNG.BBne (H := H) ⟨LocNG.img h τ.abelian₂, fun b => h (τ.f b), fun b => h (τ.f' b), τ.T, τ.T'⟩ ↔ LocNG.BBne (H := H) τ) := by
  first | exact @GlobalTheory.HL.LocalMove.main | exact GlobalTheory.HL.LocalMove.main | (intros; apply GlobalTheory.HL.LocalMove.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProdLeOfIsRadical
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev.SqfCrt

theorem mem_mul_smul_of_coprime {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M] (N : Submodule S M)
    {A B : Ideal S} (h : IsCoprime A B) {y : M} (hA : y ∈ A • N) (hB : y ∈ B • N) : y ∈ (A * B) • N := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  have hsplit : y = a • y + b • y := by rw [← add_smul, hab, one_smul]
  rw [hsplit]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul ha hB
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hb hA

theorem mem_prod_smul_of_coprime {S M ι : Type*} [CommRing S] [AddCommGroup M] [Module S M] (N : Submodule S M)
    (J : ι → Ideal S) (hJ : ∀ i j, i ≠ j → IsCoprime (J i) (J j)) {y : M} (hy : y ∈ N) (T : Finset ι)
    (h : ∀ i ∈ T, y ∈ J i • N) : y ∈ (∏ i ∈ T, J i) • N := by
  induction T using Finset.induction_on with
  | empty => simpa [Ideal.one_eq_top, Submodule.top_smul] using hy
  | @insert a T haT ih =>
    rw [Finset.prod_insert haT]
    refine mem_mul_smul_of_coprime N ?_ (h a (Finset.mem_insert_self a T))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact IsCoprime.prod_right fun i hi => hJ a i fun hai => haT (hai ▸ hi)

theorem exists_prod_le_of_isRadical {R : Type*} [CommRing R] [IsDedekindDomain R] {𝔞 : Ideal R} (h0 : 𝔞 ≠ ⊥)
    (hr : 𝔞.IsRadical) : ∃ T : Finset (HeightOneSpectrum R), (∀ u ∈ T, 𝔞 ≤ u.asIdeal) ∧
      ∏ u ∈ T, u.asIdeal ≤ 𝔞 := by
  have hfin := Ideal.finite_factors h0
  refine ⟨hfin.toFinset, fun u hu => Ideal.le_of_dvd ((Set.Finite.mem_toFinset hfin).1 hu), ?_⟩
  intro x hx
  apply hr
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hle, hP⟩
  have hP0 : P ≠ ⊥ := fun hb => h0 (le_bot_iff.1 (hb ▸ hle))
  let v : HeightOneSpectrum R := ⟨P, hP, hP0⟩
  have hv : v ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 (Ideal.dvd_iff_le.2 hle)
  exact (Ideal.prod_le_inf.trans (Finset.inf_le hv)) hx

theorem extId_eq_image (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by
  unfold extId
  rw [Ideal.map]
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, hz⟩
    exact ⟨a, ha, Subtype.ext hz.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

private theorem isCoprime_map_of_ne {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    (f : R →+* S) {u v : HeightOneSpectrum R} (huv : u ≠ v) :
    IsCoprime (u.asIdeal.map f) (v.asIdeal.map f) := by
  have hmax : u.asIdeal ⊔ v.asIdeal = ⊤ :=
    u.isMaximal.coprime_of_ne v.isMaximal fun e => huv (HeightOneSpectrum.ext e)
  rw [Ideal.isCoprime_iff_sup_eq, ← Ideal.map_sup, hmax, Ideal.map_top]

private theorem prod_map_le_map_of_prod_le {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (T : Finset (HeightOneSpectrum R)) {𝔞 : Ideal R} (hle : ∏ u ∈ T, u.asIdeal ≤ 𝔞) :
    ∏ u ∈ T, u.asIdeal.map f ≤ 𝔞.map f := by
  have hprod : ∀ T' : Finset (HeightOneSpectrum R),
      ∏ u ∈ T', u.asIdeal.map f = (∏ u ∈ T', u.asIdeal).map f := by
    intro T'
    induction T' using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top, Ideal.one_eq_top, Ideal.map_top]
    | @insert a T' haT ih => rw [Finset.prod_insert haT, Finset.prod_insert haT, Ideal.map_mul, ih]
  rw [hprod]
  exact Ideal.map_mono hle

private theorem mem_map_smul_of_forall_mem_map_smul {R S M : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    [AddCommGroup M] [Module S M] (f : R →+* S) (N : Submodule S M) {𝔞 : Ideal R} (h0 : 𝔞 ≠ ⊥)
    (hr : 𝔞.IsRadical) {y : M} (hy : y ∈ N)
    (h : ∀ u : HeightOneSpectrum R, 𝔞 ≤ u.asIdeal → y ∈ u.asIdeal.map f • N) : y ∈ 𝔞.map f • N := by
  obtain ⟨T, hT, hle⟩ := exists_prod_le_of_isRadical h0 hr
  have hmem : y ∈ (∏ u ∈ T, u.asIdeal.map f) • N :=
    mem_prod_smul_of_coprime (ι := HeightOneSpectrum R) N (fun u => u.asIdeal.map f)
      (fun _ _ huv => isCoprime_map_of_ne f huv) hy T fun u hu => h u (hT u hu)
  exact Submodule.smul_mono_left (prod_map_le_map_of_prod_le f T hle) hmem

theorem mem_extId_smul_forall_iff : ∀ (I : AutInst) (m : ℕ), 1 ≤ m → (Ideal.span {(m : 𝓞 I.E)}).IsRadical →
    ∀ y ∈ I.Lf, (∀ u : HeightOneSpectrum (𝓞 I.E), (m : 𝓞 I.E) ∈ u.asIdeal → y ∈ extId I u.asIdeal • I.Lf) ↔
      ∃ z ∈ I.Lf, y = (m : (I.E ⊗[I.F] Af I.F)) • z := by
  intro I m hm hrad y hy
  constructor
  · intro h
    have h0 : Ideal.span {(m : 𝓞 I.E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (by omega)
    have key : y ∈ (Ideal.span {(m : 𝓞 I.E)}).map (Inhab.psi I.F I.E) • I.Lf :=
      mem_map_smul_of_forall_mem_map_smul (Inhab.psi I.F I.E) I.Lf h0 hrad hy fun u hu => by
        rw [← extId_eq_image I]
        exact h u (hu (Ideal.mem_span_singleton_self _))
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at key
    obtain ⟨z, hz, hzy⟩ := key
    refine ⟨z, hz, ?_⟩
    rw [← hzy, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  · rintro ⟨z, hz, rfl⟩ u hu
    have hm' : (m : IntAf I.F I.E) ∈ extId I u.asIdeal := by
      rw [extId_eq_image, ← map_natCast (Inhab.psi I.F I.E)]
      exact Ideal.mem_map_of_mem _ hu
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (IntAf I.F I.E)]
    exact Submodule.smul_mem_smul hm' hz

end GlobalTheory.RowLev.SqfCrt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesHermitianTerms
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesHermitianTerms
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ComplMove

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

lemma bbne_img (g : V ≃ₗ[E] V) (f f' : Fin (r + 1) → V) (hfix : ∀ b, g (f b) = f b ∧ g (f' b) = f' b)
    (Λ : Submodule M.L.O V) (T T' : F) :
    LocNG.BBne (H := H) (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) ↔
      LocNG.BBne (H := H) (⟨Λ, f, f', T, T'⟩ : Term V M r) := by
  have hfam : ∀ i, g (H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) i) = H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) i := by
    intro i
    unfold HermSp.MMfam
    rcases hs : M.split with _ | gg <;> rcases i with i | i <;>
      simp [map_smul, map_sub, (hfix i).1, (hfix i).2]
  have hspan : ∀ v ∈ Submodule.span E (Set.range (H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r))), g v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hfam i
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul s x _ hx => rw [map_smul, hx]
  have e : H.MMfam (⟨LocNG.img g Λ, f, f', T, T'⟩ : Term V M r) = H.MMfam (⟨Λ, f, f', T, T'⟩ : Term V M r) := rfl
  unfold LocNG.BBne
  simp only [e]
  constructor
  · rintro ⟨v, hv, hs, hns⟩
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hv
    have ew : g w = w := g.injective (hspan _ hs)
    change g w ∈ _ at hs
    change g w ∉ _ at hns
    rw [ew] at hs hns
    exact ⟨w, hw, hs, hns⟩
  · rintro ⟨v, hv, hs, hns⟩
    exact ⟨v, Submodule.mem_map.2 ⟨v, hv, hspan v hs⟩, hs, hns⟩

lemma fwd (hM : M.OK) (P : LocNG.FPair H r) (S : Frames M.L r k) (c : Coord P S) (g : V ≃ₗ[E] V)
    (hg : c.grp g ∈ S.H0) (d d' : LocNG.Datum P) (hmv : c.grp g • c.dat d = c.dat d')
    (f f' : Fin (r + 1) → V) (Λ : Submodule M.L.O V)
    (hT : LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) :
    LocNG.IsTermOver P d' (⟨LocNG.img g Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) := by
  letI := hM.loc
  haveI := hM.char0
  have hT0 := hT
  obtain ⟨-, -, ⟨n, hn, hf, hΛn⟩, ⟨n', hn', hf', hΛn'⟩, -⟩ := hT
  change f = _ at hf
  change f' = _ at hf'
  change Λ = _ at hΛn
  change Λ = _ at hΛn'
  subst hf hf'
  have hW := (GlobalTheory.T.term_over_frame_coordinates M hM H r k P S c d n n' Λ).1 ⟨hT0, hn, hn', hΛn, hΛn'⟩
  obtain ⟨m, m', hW', hm, hm'⟩ := GlobalTheory.HL.ComplAct.termW S hW hg
  rw [hmv, ← GlobalTheory.HL.CoordTerm.lat_img c] at hW'
  have e1 : c.grp (c.grp.symm m) = m := c.grp.apply_symm_apply m
  have e2 : c.grp (c.grp.symm m') = m' := c.grp.apply_symm_apply m'
  rw [← e1, ← e2] at hW'
  have hR := ((GlobalTheory.T.term_over_frame_coordinates M hM H r k P S c d' (c.grp.symm m) (c.grp.symm m') (LocNG.img g Λ)).2 hW').1
  have k1 : (fun b => c.grp.symm m (P.A.f b)) = fun b => n (P.A.f b) := by
    funext b
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f_eq, e1, hm b]
  have k2 : (fun b => c.grp.symm m' (P.B.f b)) = fun b => n' (P.B.f b) := by
    funext b
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f'_eq, e2, hm' b]
  rw [k1, k2] at hR
  exact hR

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ g ∈ P.UW0, ∀ d d' : LocNG.Datum P, LocNG.Datum.Moves g d d' → (∀ b, g (f b) = f b ∧ g (f' b) = f' b) ∧ LocNG.img g '' {Λ | LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} = {Λ | LocNG.IsTermOver P d' (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hP f f' ⟨n, hn, hf⟩ ⟨n', hn', hf'⟩ g hg d d' hmv
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hP
  obtain ⟨hU, -⟩ := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  obtain ⟨-, hMv, -⟩ := GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c
  obtain ⟨-, hNA, hNB, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  have hh := (hU g).1 hg
  have hmv' := (hMv g hg d d').1 hmv
  have fixv : ∀ x : V, c.e x ∈ S.ME → g x = x := by
    intro x hx
    apply c.e.injective
    rw [← GlobalTheory.HL.CoordTerm.grp_e c]
    exact GlobalTheory.HL.ComplAct.hermitianFrames_complementUnitary_fixes_ME S hh _ hx
  have hfix : ∀ b, g (f b) = f b ∧ g (f' b) = f' b := by
    intro b
    subst hf hf'
    refine ⟨fixv _ ?_, fixv _ ?_⟩
    · rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f_eq]
      exact Submodule.mem_sup_left (GlobalTheory.HL.ComplAct.nof_mem S (Or.inl ⟨rfl, rfl⟩) ((hNA n).1 hn)
        (GlobalTheory.HL.ComplAct.mem_spanTo S S.f b))
    · rw [← GlobalTheory.HL.CoordTerm.grp_e c, ← c.f'_eq]
      exact Submodule.mem_sup_right (GlobalTheory.HL.ComplAct.nof_mem S (Or.inr ⟨rfl, rfl⟩) ((hNB n').1 hn')
        (GlobalTheory.HL.ComplAct.mem_spanTo S S.f' b))
  have hginv : c.grp g⁻¹ ∈ S.H0 := by rw [map_inv]; exact S.H0.inv_mem hh
  have hmvinv : c.grp g⁻¹ • c.dat d' = c.dat d := by
    rw [← hmv', map_inv, inv_smul_smul]
  have hback : ∀ Λ : Submodule M.L.O V, LocNG.img g (LocNG.img g⁻¹ Λ) = Λ := by
    intro Λ
    rw [← GlobalTheory.HL.CoordTerm.lat_inj c, GlobalTheory.HL.CoordTerm.lat_img, GlobalTheory.HL.CoordTerm.lat_img, map_inv,
      smul_inv_smul]
  refine ⟨hfix, ?_⟩
  ext Λ
  constructor
  · rintro ⟨Λ0, ⟨hT, hB⟩, rfl⟩
    exact ⟨fwd hM P S c g hh d d' hmv' f f' Λ0 hT, by rwa [bbne_img g f f' hfix]⟩
  · rintro ⟨hT, hB⟩
    refine ⟨LocNG.img g⁻¹ Λ, ⟨fwd hM P S c g⁻¹ hginv d' d hmvinv f f' Λ hT, ?_⟩, hback Λ⟩
    rw [← bbne_img g f f' hfix, hback Λ]
    exact hB

end GlobalTheory.HL.ComplMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesHermitianTermsStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryComplement_moves_hermitianTerms : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ g ∈ P.UW0, ∀ d d' : LocNG.Datum P, LocNG.Datum.Moves g d d' → (∀ b, g (f b) = f b ∧ g (f' b) = f' b) ∧ LocNG.img g '' {Λ | LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} = {Λ | LocNG.IsTermOver P d' (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} := by
  first | exact @GlobalTheory.HL.ComplMove.main | exact GlobalTheory.HL.ComplMove.main | (intros; apply GlobalTheory.HL.ComplMove.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataMassEqSumFrameClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataMassEqSumFrameClasses
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem sumData_mass_eq_sumCls : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ P : S.Datum → Submodule L.O S.V → Prop, (∀ h ∈ S.St, ∀ d Λ, S.IsTerm d Λ → P d Λ → P d (h • Λ)) → (S.sumData fun d => S.mass d (P d)) = (S.sumCls fun C => S.sumData fun d => S.nT d C (P d)) ∧ ∀ h ∈ S.St, ∀ d C, S.nT d (h • C) (P d) = S.nT d C (P d) := by
  intro F _ _ _ _ _ E _ _ _ L r k S P hP
  refine ⟨?_, fun h hh d C => ?_⟩
  · have e : (fun d => S.mass d (P d)) = fun d => S.sumCls fun C => S.nT d C (P d) :=
      funext fun d => mass_eq_sumCls L r k S d (P d) fun h hh Λ => hP h hh d Λ
    rw [e]
    unfold Frames.sumData Frames.sumCls
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun c => ?_
    split_ifs
    · exact tsum_congr fun o => mul_left_comm _ _ _
    · simp
  · unfold Frames.nT
    have e : ({Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = h • C} : Set (Submodule L.O S.V)) =
        (fun Λ => h • Λ) '' {Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = C} := by
      ext Λ
      constructor
      · rintro ⟨h1, h2, h3⟩
        have A := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h⁻¹ (S.St.inv_mem hh)
        refine ⟨h⁻¹ • Λ, ⟨A.1, hP _ (S.St.inv_mem hh) d Λ h1 h2, ?_⟩, smul_inv_smul h Λ⟩
        rw [A.2.2.2.2.1, h3, inv_smul_smul]
      · rintro ⟨Λ, ⟨h1, h2, h3⟩, rfl⟩
        have A := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h hh
        refine ⟨A.1, hP _ hh d Λ h1 h2, ?_⟩
        rw [A.2.2.2.2.1, h3]
    rw [e, (MulAction.injective h).encard_image]

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataMassEqSumFrameClassesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ P : S.Datum → Submodule L.O S.V → Prop, (∀ h ∈ S.St, ∀ d Λ, S.IsTerm d Λ → P d Λ → P d (h • Λ)) → (S.sumData fun d => S.mass d (P d)) = (S.sumCls fun C => S.sumData fun d => S.nT d C (P d)) ∧ ∀ h ∈ S.St, ∀ d C, S.nT d (h • C) (P d) = S.nT d C (P d) := by
  first | exact @GlobalTheory.HL.sumData_mass_eq_sumCls | exact GlobalTheory.HL.sumData_mass_eq_sumCls | (intros; apply GlobalTheory.HL.sumData_mass_eq_sumCls <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassesTotalWeightLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassesTotalWeightLe
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TotalWeight

theorem natCast_pow_le_pow_of_exponent_le (q m a e e' : ℕ) (he : e ≤ e') (h1 : (1 : ℝ) ≤ (q : ℝ) ^ (m + a)) :
    (q : ℝ) ^ (e * m) ≤ ((q : ℝ) ^ (m + a)) ^ e' := by
  have h2 : (q : ℝ) ^ m ≤ (q : ℝ) ^ (m + a) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simpa using h1
      · simp [hm.ne']
    · exact pow_le_pow_right₀ (by exact_mod_cast hq) (Nat.le_add_right _ _)
  calc (q : ℝ) ^ (e * m) = ((q : ℝ) ^ m) ^ e := by rw [mul_comm, pow_mul]
    _ ≤ ((q : ℝ) ^ (m + a)) ^ e := pow_le_pow_left₀ (by positivity) h2 e
    _ ≤ _ := pow_le_pow_right₀ h1 he

theorem sumCls_one_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k)
    (h : ∃ d Λ, S.IsTerm d Λ) :
    (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (3 * (r + 1) ^ 2)) := by
  obtain ⟨d, Λ, hT⟩ := h
  obtain ⟨ha, hD, -, -, h1, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT
  have hth : 0 ≤ S.vth := by
    unfold Frames.vth
    split_ifs <;> norm_num
  have hHp : S.Hp = (S.q : ℝ) ^ ((S.vth + S.vD).toNat + S.a.toNat) := by
    unfold Frames.Hp
    rw [← zpow_natCast]
    congr 1
    push_cast
    rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg (add_nonneg hth hD)]
    ring
  refine (GlobalTheory.HL.ClassCount.sumCls_le_encard L r k S).trans
    ((GlobalTheory.IntClsCount.main L r k S hD).trans ?_)
  have he : r * (r + 1) ≤ 3 * (r + 1) ^ 2 := by nlinarith
  rw [hHp] at h1 ⊢
  have key := ENNReal.ofReal_le_ofReal (natCast_pow_le_pow_of_exponent_le S.q _ _ _ _ he h1)
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at key
  exact key

end GlobalTheory.HL.TotalWeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassesTotalWeightLeStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrameClasses_total_weight_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∃ d Λ, S.IsTerm d Λ) → (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (3 * (r + 1) ^ 2)) := by
  first | exact @GlobalTheory.HL.TotalWeight.sumCls_one_le | exact GlobalTheory.HL.TotalWeight.sumCls_one_le | (intros; apply GlobalTheory.HL.TotalWeight.sumCls_one_le <;> assumption)
end
end
