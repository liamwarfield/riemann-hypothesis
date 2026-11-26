module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
public import Formalism.HermitianLattices.StatementMass
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ComplAct

open GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_smul (h : S.GLV) (Λ : Submodule L.O S.V) (x : S.V) : x ∈ h • Λ ↔ h⁻¹ x ∈ Λ := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : h⁻¹ (h • y) = y := h.symm_apply_apply y
    rwa [this]
  · intro hx
    exact ⟨_, hx, h.apply_symm_apply x⟩

theorem isSD_smul {h : S.GLV} (hh : h ∈ isomG L S.Hm) {Λ : Submodule L.O S.V} (hΛ : IsSD L S.Hm Λ) :
    IsSD L S.Hm (h • Λ) := by
  refine ⟨⟨hΛ.1.1.map _, ?_⟩, fun y => ?_⟩
  · rw [eq_top_iff]
    rintro x -
    have h1 : h⁻¹ x ∈ Submodule.span E (Λ : Set S.V) := by rw [hΛ.1.2]; trivial
    have h2 := Submodule.mem_map_of_mem (f := h.toLinearMap) h1
    rw [Submodule.map_span] at h2
    have h3 : h.toLinearMap (h⁻¹ x) = x := h.apply_symm_apply x
    rw [h3] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.smul_mem_pointwise_smul y h Λ hy
  · rw [mem_smul, ← hΛ.2]
    have hi := (isomG L S.Hm).inv_mem hh
    constructor
    · intro H x hx
      have := H (h x) (Submodule.smul_mem_pointwise_smul x h Λ hx)
      rw [← hi] at this
      have h3 : h⁻¹ (h x) = x := h.symm_apply_apply x
      rwa [h3] at this
    · intro H x hx
      rw [← hi]
      exact H _ ((mem_smul S h Λ x).1 hx)

theorem spanTo_mono (g : Fin (r + 1) → S.V) : S.spanTo g r ≤ S.spanTo g (r + 1) :=
  Submodule.span_mono (Set.image_mono fun _ hi => Nat.lt_succ_of_lt hi)

theorem mem_spanTo (g : Fin (r + 1) → S.V) (b : Fin (r + 1)) : g b ∈ S.spanTo g (r + 1) :=
  Submodule.subset_span ⟨b, b.2, rfl⟩

theorem spanTo_le_perp {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) :
    S.spanTo g (r + 1) ≤ perp L S.Hm (S.spanTo g r) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, -, rfl⟩
  rw [Frames.spanTo, image_lt, SetLike.mem_coe, mem_perp_span]
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · intro j; simp [S.gram, Fin.castSucc_ne_last]
  · intro j; simp [S.gram', Fin.castSucc_ne_last]

theorem nof_mem {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) {n : S.GLV} (hn : n ∈ S.Nof g)
    {x : S.V} (hx : x ∈ S.spanTo g (r + 1)) : n x ∈ S.spanTo g (r + 1) := by
  have := spanTo_mono S g (hn.2.2 x (spanTo_le_perp S hg hx))
  simpa using Submodule.add_mem _ this hx

theorem perp_map {h : S.GLV} (hh : h ∈ isomG L S.Hm) {Y : Submodule E S.V} (hY : ∀ y ∈ Y, h y = y)
    {x : S.V} (hx : x ∈ perp L S.Hm Y) : h x ∈ perp L S.Hm Y := fun y hy => by
  rw [← hY y hy, hh x y]; exact hx y hy

theorem inv_fix {h : S.GLV} {x : S.V} (hx : h x = x) : h⁻¹ x = x := by
  conv_lhs => rw [← hx]
  exact h.symm_apply_apply x

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem inner_iff {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) {A : Submodule L.O S.V}
    (hA : S.IsInner g gs A) {n : S.GLV} (hn : n ∈ S.Nof g) (x : S.V) :
    x ∈ A ↔ ∃ y ∈ n • S.stdLat g gs A, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  rw [(stdLat_spec L r k S g gs hg A hA).2.2 x]
  have hi := (S.Nof g).inv_mem hn
  constructor
  · rintro ⟨y, hy, h1, h2⟩
    refine ⟨n y, Submodule.smul_mem_pointwise_smul y n _ hy, (hn.2.1 y).2 h1, ?_⟩
    simpa using Submodule.add_mem _ (hn.2.2 y h1) h2
  · rintro ⟨y, hy, h1, h2⟩
    refine ⟨n⁻¹ y, (mem_smul S n _ y).1 hy, (hi.2.1 y).2 h1, ?_⟩
    simpa using Submodule.add_mem _ (hi.2.2 y h1) h2

theorem side {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (hg : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) {A : Submodule L.O S.V}
    (hA : S.IsInner g gs A) {n : S.GLV} (hn : n ∈ S.Nof g) {h : S.GLV} (hh : h ∈ isomG L S.Hm)
    (hfix : ∀ x ∈ S.spanTo g (r + 1), h x = x) :
    S.IsInner g gs (h • A) ∧ ∃ m ∈ S.Nof g, (∀ b, m (g b) = n (g b)) ∧
      h • n • S.stdLat g gs A = m • S.stdLat g gs (h • A) := by
  have hs := stdLat_spec L r k S g gs hg A hA
  have hi := (S.Nof g).inv_mem hn
  have hhi := (isomG L S.Hm).inv_mem hh
  have hfi : ∀ x ∈ S.spanTo g (r + 1), h⁻¹ x = x := fun x hx => inv_fix S (hfix x hx)
  have hsp : n • Submodule.span L.O (g '' {i | (i : ℕ) < r + 1}) =
      Submodule.span L.O (Set.range fun b => n (g b)) := by
    have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
      ext i; simpa using i.2
    rw [Submodule.smul_span, hs, Set.image_univ, Set.smul_set_range]
    rfl
  obtain ⟨B, hB, m, hm, hmn, hL⟩ := GlobalTheory.T.selfDual_lattice_unipotent_translate_standard L r k S g gs hg (h • n • S.stdLat g gs A)
    (isSD_smul S hh (isSD_smul S hn.1.1 hs.1)) n hn (fun x => by
      rw [← hsp, mem_smul S n, ← hs.2.1 _ le_rfl, mem_smul, mem_smul]
      constructor
      · rintro ⟨h1, h2⟩
        rw [hfi x h2] at h1
        exact ⟨h1, nof_mem S hg hi h2⟩
      · rintro ⟨h1, h2⟩
        have h3 := nof_mem S hg hn h2
        have h4 : n (n⁻¹ x) = x := n.apply_symm_apply x
        rw [h4] at h3
        exact ⟨by rwa [hfi x h3], h3⟩)
  have hBA : B = h • A := by
    ext x
    rw [inner_iff S hg hB hm, ← hL, mem_smul, inner_iff S hg hA hn]
    constructor
    · rintro ⟨y, hy, h1, h2⟩
      refine ⟨h⁻¹ y, (mem_smul S h _ y).1 hy,
        perp_map S hhi (fun y hy => hfi y (spanTo_mono S g hy)) h1, ?_⟩
      rw [← map_sub, hfi _ (spanTo_mono S g h2)]; exact h2
    · rintro ⟨y, hy, h1, h2⟩
      refine ⟨h y, Submodule.smul_mem_pointwise_smul y h _ hy,
        perp_map S hh (fun y hy => hfix y (spanTo_mono S g hy)) h1, ?_⟩
      have h4 : h (h⁻¹ x) = x := h.apply_symm_apply x
      have h5 := hfix _ (spanTo_mono S g h2)
      rw [map_sub, h4] at h5
      rw [h5]; exact h2
  subst hBA
  exact ⟨hB, m, hm, hmn, hL⟩

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem hermitianFrames_complementUnitary_fixes_ME {h : S.GLV} (hh : h ∈ S.H0) : ∀ x ∈ S.ME, h x = x := fun x hx =>
  sub_eq_zero.1 ((Submodule.mem_bot E).1 (hh.2.2 x hx))

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem graph_mem {h : S.GLV} (hh : h ∈ S.H0) {Λ : Submodule L.O S.V} {p : S.V × S.V}
    (hp : p ∈ S.graphOf Λ) : h • p ∈ S.graphOf (h • Λ) := by
  have hX : ∀ x ∈ S.X, h x = x := fun x hx =>
    hermitianFrames_complementUnitary_fixes_ME S hh x (Submodule.mem_sup_left (spanTo_mono S _ hx))
  have hX' : ∀ x ∈ S.X', h x = x := fun x hx =>
    hermitianFrames_complementUnitary_fixes_ME S hh x (Submodule.mem_sup_right (spanTo_mono S _ hx))
  obtain ⟨y', hy', y, hy, h1, h2, h3, h4, z, hz, h5⟩ := hp
  refine ⟨h y', Submodule.smul_mem_pointwise_smul y' h _ hy', h y,
    Submodule.smul_mem_pointwise_smul y h _ hy, perp_map S hh.1 hX' h1, perp_map S hh.1 hX h2, ?_, ?_,
    h z, Submodule.smul_mem_pointwise_smul z h _ hz, ?_⟩
  · change h y' - h p.1 ∈ _
    rw [← map_sub, hX' _ h3]; exact h3
  · change h y - h p.2 ∈ _
    rw [← map_sub, hX _ h4]; exact h4
  · rw [← map_sub, h5, map_smul]

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem graph_smul {h : S.GLV} (hh : h ∈ S.H0) (Λ : Submodule L.O S.V) :
    h • S.graphOf Λ = S.graphOf (h • Λ) := by
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro hp
    simpa using graph_mem S hh hp
  · intro hp
    simpa using graph_mem S (S.H0.inv_mem hh) hp

theorem comm {h s : S.GLV} (hh : h ∈ S.H0) (hs : s ∈ S.St) : s * h = h * s := by
  obtain ⟨hli, hco, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hdis := (linearIndependent_sum.1 hli).2.2
  have hle : ∀ g : Fin (r + 1) → S.V, S.spanTo g r ≤ Submodule.span E (Set.range g) := fun g =>
    Submodule.span_mono (Set.image_subset_range _ _)
  have hW : ∀ w ∈ S.W0, s w = w := fun w hw => by
    have h1 := hs.1.2.2 w fun y hy => hw y (Submodule.mem_sup_left (spanTo_mono S _ hy))
    have h2 := hs.2.2.2 w fun y hy => hw y (Submodule.mem_sup_right (spanTo_mono S _ hy))
    exact sub_eq_zero.1 (Submodule.disjoint_def.1 hdis _ (hle _ h1) (hle _ h2))
  have hM : ∀ x ∈ S.ME, s x ∈ S.ME := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (nof_mem S (Or.inl ⟨rfl, rfl⟩) hs.1 ha)
      (nof_mem S (Or.inr ⟨rfl, rfl⟩) hs.2 hb)
  ext1 v
  have hv : v ∈ S.ME ⊔ S.W0 := by rw [hco.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  change s (h (a + b)) = h (s (a + b))
  rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hermitianFrames_complementUnitary_fixes_ME S hh a ha, hermitianFrames_complementUnitary_fixes_ME S hh _ (hM a ha), hW b hb,
    hW _ (perp_map S hh.1 (hermitianFrames_complementUnitary_fixes_ME S hh) hb)]

theorem termW {d : S.Datum} {Λ : Submodule L.O S.V} {n n' : S.GLV} (H : S.IsTermW d Λ n n')
    {h : S.GLV} (hh : h ∈ S.H0) :
    ∃ m m', S.IsTermW (h • d) (h • Λ) m m' ∧ (∀ b, m (S.f b) = n (S.f b)) ∧
      ∀ b, m' (S.f' b) = n' (S.f' b) := by
  obtain ⟨hA, hA', hn, hn', h1, h2, h3, h4⟩ := H
  obtain ⟨hB, m, hm, hmn, hL⟩ := side S (Or.inl ⟨rfl, rfl⟩) hA hn hh.1
    fun x hx => hermitianFrames_complementUnitary_fixes_ME S hh x (Submodule.mem_sup_left hx)
  obtain ⟨hB', m', hm', hmn', hL'⟩ := side S (Or.inr ⟨rfl, rfl⟩) hA' hn' hh.1
    fun x hx => hermitianFrames_complementUnitary_fixes_ME S hh x (Submodule.mem_sup_right hx)
  refine ⟨m, m', ⟨hB, hB', hm, hm', by rw [← h1] at hL; exact hL, by rw [← h2] at hL'; exact hL',
    fun b => ?_, ?_⟩, hmn, hmn'⟩
  · obtain ⟨z, hz, h5⟩ := h3 b
    refine ⟨h z, Submodule.smul_mem_pointwise_smul z h _ hz, ?_⟩
    rw [hmn, hmn', ← map_smul, ← h5, hermitianFrames_complementUnitary_fixes_ME S hh]
    exact Submodule.sub_mem _
      (Submodule.mem_sup_right (nof_mem S (Or.inr ⟨rfl, rfl⟩) hn' (mem_spanTo S _ b)))
      (Submodule.mem_sup_left (nof_mem S (Or.inl ⟨rfl, rfl⟩) hn (mem_spanTo S _ b)))
  · rw [← graph_smul S hh, ← h4]; rfl

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ h ∈ S.H0, S.IsTerm (h • d) (h • Λ) ∧ S.om (h • d) (h • Λ) = S.om d Λ ∧ S.mu (h • Λ) = S.mu Λ ∧ S.M (h • d) (h • Λ) = S.M d Λ ∧ S.sat (h • Λ) = S.sat Λ ∧ S.Fr (h • d) (h • Λ) = S.Fr d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ ⟨⟨n, n'⟩, H⟩ h hh
  obtain ⟨m, m', H', hm, hm'⟩ := termW S H hh
  obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.T.term_invariants_independent_of_witnesses L r k S _ _ _ _ H
  obtain ⟨b1, b2, b3, -⟩ := GlobalTheory.T.term_invariants_independent_of_witnesses L r k S _ _ _ _ H'
  refine ⟨⟨(m, m'), H'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a1, b1]
    simp only [Frames.psi, Frames.psi', Frames.psiOf, Frames.coef, hm, hm']
  · unfold Frames.mu
    congr 1
    ext s
    simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    refine and_congr_right fun hs => ?_
    rw [smul_smul, comm S hh hs, ← smul_smul, smul_left_cancel_iff]
  · rw [a2, b2]; simp only [hm, hm']
  · ext x
    simp only [Frames.sat, Submodule.mem_inf, Submodule.restrictScalars_mem]
    refine and_congr_left fun hx => ?_
    rw [mem_smul, inv_fix S (hermitianFrames_complementUnitary_fixes_ME S hh x hx)]
  · rw [a3, b3]; simp only [hm, hm']

end GlobalTheory.HL.ComplAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTermsStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrames_complementUnitary_acts_on_terms : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ h ∈ S.H0, S.IsTerm (h • d) (h • Λ) ∧ S.om (h • d) (h • Λ) = S.om d Λ ∧ S.mu (h • Λ) = S.mu Λ ∧ S.M (h • d) (h • Λ) = S.M d Λ ∧ S.sat (h • Λ) = S.sat Λ ∧ S.Fr (h • d) (h • Λ) = S.Fr d Λ := by
  first | exact @GlobalTheory.HL.ComplAct.main | exact GlobalTheory.HL.ComplAct.main | (intros; apply GlobalTheory.HL.ComplAct.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesLocalHeightEqResidueCard
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesLocalHeightEqResidueCard
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordHeight

section Val

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
  (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
include hϖ

theorem vE_one : vE L ϖ (algebraMap F E 1) = 0 := by
  have h := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

theorem vE_unit (x : F) (hx : x ≠ 0) (h1 : algebraMap F E x ∈ L.O)
    (h2 : ∃ y ∈ L.O, algebraMap F E x * y = 1) : vE L ϖ (algebraMap F E x) = 0 := by
  obtain ⟨hadd, -, hint, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨-, -, -, -, hO, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨y, hy, hxy⟩ := h2
  have e : y = algebraMap F E x⁻¹ := by
    calc y = algebraMap F E (x⁻¹ * x) * y := by rw [inv_mul_cancel₀ hx, map_one, one_mul]
      _ = algebraMap F E x⁻¹ := by rw [map_mul, mul_assoc, hxy, mul_one]
  have a1 := (hint x hx).2 ((hO x).1 h1)
  have a2 := (hint x⁻¹ (inv_ne_zero hx)).2 ((hO _).1 (e ▸ hy))
  have a3 := hadd x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, vE_one L ϖ hϖ] at a3
  omega

theorem vE_pow (x : F) (hx : x ≠ 0) (n : ℕ) :
    vE L ϖ (algebraMap F E (x ^ n)) = n * vE L ϖ (algebraMap F E x) := by
  induction n with
  | zero => simpa using vE_one L ϖ hϖ
  | succ n ih =>
    rw [pow_succ, (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1 _ _ (pow_ne_zero n hx) hx, ih]
    push_cast
    ring

theorem vE_neg_one : vE L ϖ (algebraMap F E (-1)) = 0 := by
  have h := vE_pow L ϖ hϖ (-1) (by simp) 2
  rw [neg_one_sq, vE_one L ϖ hϖ] at h
  omega

omit [IsNonarchimedeanLocalField F] [CharZero F] hϖ in
theorem norm_mem (x : E) (hx : IsUnit x) : ∃ c : F, c ≠ 0 ∧ x * L.cj x = algebraMap F E c := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  obtain ⟨c, hc⟩ := (L.cj_fix (x * L.cj x)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  rw [map_zero] at hc
  exact (hx.mul (hx.map L.cj)).ne_zero hc.symm

end Val

section Transport

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
include c

theorem Dm_eq (l : Fin (r + 2)) : P.Dm l = S.D l := by
  have hZ : H.Zhat P.A.f P.B.f = S.Zh := by
    ext a b
    simp only [HermSp.Zhat, Frames.Zh, Matrix.of_apply, c.f_eq, c.f'_eq, c.h_eq]
  unfold LocNG.FPair.Dm HermSp.Dl Frames.D lead
  rw [dite_eq_left (Nat.lt_succ_iff.mp l.2), hZ]

theorem Gv_eq : P.Gv = S.G := by
  have h1 := Dm_eq c (Fin.last (r + 1))
  have h2 := Dm_eq c (Fin.last r).castSucc
  unfold LocNG.FPair.Gv HermSp.Gdet HermSp.normE Frames.G
  rw [← h1, ← h2, c.T_eq, c.T'_eq]
  rfl

theorem theta_eq : LocNG.theta M = S.th := by
  unfold LocNG.theta Frames.th
  cases h : M.split with
  | none => simp [c.gg_none h]
  | some g =>
    obtain ⟨h1, h2⟩ := c.gg_some g h
    simp [h1, h2]

end Transport

theorem height_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), P.Hp = S.Hp ∧ LocNG.qF F = S.q ∧ (P.PrimeTo → S.gg = false ∧ vE M.L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE M.L S.ϖ (S.D l * M.L.cj (S.D l)) = 0) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  have := hM.loc
  have := hM.char0
  obtain ⟨hq, hmod⟩ := GlobalTheory.BaseModule.modK_algebraMap M hM S.ϖ S.ϖ_irr
  obtain ⟨-, -, ⟨g, hg0, hg⟩, -, hD, hth, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  obtain ⟨hadd, hvp, -, -⟩ := GlobalTheory.UnramVal.vE_valuation M.L S.ϖ S.ϖ_irr
  obtain ⟨-, hcj, -, -, -, -, hq2, -⟩ := GlobalTheory.UnramOrder.order_facts M.L S.ϖ S.ϖ_irr
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
  have hgram := GlobalTheory.det_gram_frame_generators M hM H r k P
  rw [theta_eq c, Gv_eq c, hg] at hgram
  have hvth : vE M.L S.ϖ (algebraMap F E S.th) = S.vth := by
    unfold Frames.th Frames.vth
    split_ifs
    · exact hvp
    · exact vE_one M.L S.ϖ S.ϖ_irr
  have hends : ∀ l : Fin (r + 2), (l : ℕ) ∈ P.ends ↔ l ≠ 0 ∧ S.D l ≠ 0 := by
    intro l
    unfold LocNG.FPair.ends
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [Dm_eq c]
    constructor
    · rintro ⟨-, h1, h2⟩
      refine ⟨?_, h2.ne_zero⟩
      rintro rfl
      simp at h1
    · rintro ⟨h1, h2⟩
      refine ⟨l.2, ?_, hD l h2⟩
      exact Nat.one_le_iff_ne_zero.mpr fun h => h1 (Fin.ext h)
  refine ⟨?_, hq, ?_⟩
  · have hq0 : (0 : ℝ) < (resQ S.ϖ : ℝ) := by
      have : 0 < resQ S.ϖ := by omega
      exact_mod_cast this
    set d : F := (-1) ^ (r + 1) * g * (S.th ^ (2 * (r + 1)))⁻¹ with hd
    have hp0 : S.th ^ (2 * (r + 1)) ≠ 0 := pow_ne_zero _ hth
    have hs0 : ((-1 : F) ^ (r + 1)) ≠ 0 := pow_ne_zero _ (by simp)
    have hd0 : d ≠ 0 := mul_ne_zero (mul_ne_zero hs0 hg0) (inv_ne_zero hp0)
    have hdet : (H.gram P.MMgen).det = algebraMap F E d := by
      calc (H.gram P.MMgen).det
          = (H.gram P.MMgen).det * algebraMap F E (S.th ^ (2 * (r + 1)) * (S.th ^ (2 * (r + 1)))⁻¹) := by
            rw [mul_inv_cancel₀ hp0, map_one, mul_one]
        _ = algebraMap F E d := by
            rw [map_mul, ← mul_assoc, map_pow, hgram, hd]
            simp only [map_mul, map_pow, map_neg, map_one]
    have hva : vE M.L S.ϖ (algebraMap F E d) = S.a := by
      have e : d * S.th ^ (2 * (r + 1)) = (-1) ^ (r + 1) * g := by
        rw [hd, mul_assoc, inv_mul_cancel₀ hp0, mul_one]
      have h1 := hadd _ _ hd0 hp0
      rw [e, hadd _ _ hs0 hg0, vE_pow M.L S.ϖ S.ϖ_irr _ hth, vE_pow M.L S.ϖ S.ϖ_irr _ (by simp),
        vE_neg_one M.L S.ϖ S.ϖ_irr, hvth] at h1
      unfold Frames.a
      rw [hg]
      push_cast at h1
      linarith
    have hprod : ∏ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) = (resQ S.ϖ : ℝ) ^ (-(2 * S.vD)) := by
      have hsub : P.ends ⊆ Finset.range (r + 2) := by
        unfold LocNG.FPair.ends
        exact @Finset.filter_subset _ _ (_) _
      rw [← Finset.inter_eq_right.mpr hsub, ← Finset.prod_ite_mem, Finset.prod_range]
      unfold Frames.vD
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      have hz : ∀ (s : Finset (Fin (r + 2))) (f : Fin (r + 2) → ℤ),
          (resQ S.ϖ : ℝ) ^ (∑ i ∈ s, f i) = ∏ i ∈ s, (resQ S.ϖ : ℝ) ^ f i := by
        intro s f
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hq0.ne', ih]
      rw [hz]
      refine Finset.prod_congr rfl fun l _ => ?_
      by_cases hl : l ≠ 0 ∧ S.D l ≠ 0
      · rw [if_pos ((hends l).2 hl), if_pos hl, Dm_eq c]
        obtain ⟨n, hn0, hn⟩ := norm_mem M.L _ (hD l hl.2)
        rw [hn, hmod n hn0]
      · rw [if_neg (fun h => hl ((hends l).1 h)), if_neg hl]
        simp
    unfold LocNG.FPair.Hp Frames.Hp Frames.q
    rw [hprod, hdet, theta_eq c, hmod _ hth, hmod _ hd0, hvth, hva, ← zpow_add₀ hq0.ne',
      ← zpow_add₀ hq0.ne', ← Real.rpow_intCast, ← Real.rpow_mul hq0.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨c.gg_none h1, ?_, fun l hl => ?_⟩
    · rw [Gv_eq c, hg] at h2
      rw [hg]
      exact vE_unit M.L S.ϖ S.ϖ_irr g hg0 h2.1 h2.2
    · have hu : LocNG.IsUnitO M (S.D l) := by
        by_cases h0 : l = 0
        · have : S.D l = 1 := by
            subst h0
            unfold Frames.D lead
            exact Matrix.det_isEmpty (n := Fin 0)
          rw [this]
          exact ⟨M.L.O.one_mem, 1, M.L.O.one_mem, mul_one 1⟩
        · have := h3 l ((hends l).2 ⟨h0, hl⟩)
          rwa [Dm_eq c] at this
      obtain ⟨n, hn0, hn⟩ := norm_mem M.L _ (hD l hl)
      obtain ⟨hm, y, hy, hxy⟩ := hu
      rw [hn]
      refine vE_unit M.L S.ϖ S.ϖ_irr n hn0 ?_ ⟨y * M.L.cj y, M.L.O.mul_mem hy (hcj y hy).1, ?_⟩
      · rw [← hn]
        exact M.L.O.mul_mem hm (hcj _ hm).1
      · rw [← hn, mul_mul_mul_comm, ← map_mul, hxy, map_one, mul_one]

end GlobalTheory.HL.CoordHeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesLocalHeightEqResidueCardStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePairCoordinates_localHeight_eq_residueCard : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), P.Hp = S.Hp ∧ LocNG.qF F = S.q ∧ (P.PrimeTo → S.gg = false ∧ vE M.L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE M.L S.ϖ (S.D l * M.L.cj (S.D l)) = 0) := by
  first | exact @GlobalTheory.HL.CoordHeight.height_eq | exact GlobalTheory.HL.CoordHeight.height_eq | (intros; apply GlobalTheory.HL.CoordHeight.height_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootDiscrGeThreeHalvesOfIsTotallyComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootDiscrGeThreeHalvesOfIsTotallyComplex
open MeasureTheory NumberField Finset

namespace GlobalTheory


open MeasureTheory NumberField Finset in
theorem _root_.GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex :
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
      Module.finrank ℚ K = 2 * _root_.Formalism.HermitianLatticesTheory.fDeg K ∧ 1 ≤ _root_.Formalism.HermitianLatticesTheory.fDeg K ∧
      (3 / 2 : ℝ) ≤ 2 * _root_.Formalism.HermitianLatticesTheory.vInv K ∧
      Real.sqrt |(discr K : ℝ)| = (2 * _root_.Formalism.HermitianLatticesTheory.vInv K) ^ _root_.Formalism.HermitianLatticesTheory.fDeg K := by
  intro K _ _ hK
  have hf : _root_.Formalism.HermitianLatticesTheory.fDeg K = InfinitePlace.nrComplexPlaces K := by
    unfold _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hn : Module.finrank ℚ K = 2 * _root_.Formalism.HermitianLatticesTheory.fDeg K := by
    rw [hf]; exact IsTotallyComplex.finrank K
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h1 : 1 ≤ _root_.Formalism.HermitianLatticesTheory.fDeg K := by omega
  have hv : 2 * _root_.Formalism.HermitianLatticesTheory.vInv K = |(discr K : ℝ)| ^ (1 / (2 * (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ))) := by
    unfold _root_.Formalism.HermitianLatticesTheory.vInv; ring
  have hD0 : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  have hbound : (3 / 2 : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K) ≤ |(discr K : ℝ)| := by
    have hd := abs_discr_ge (K := K) (by omega)
    rw [hn, Int.cast_abs] at hd
    refine le_trans ?_ hd
    obtain ⟨m, hm⟩ : ∃ m, _root_.Formalism.HermitianLatticesTheory.fDeg K = m + 1 := ⟨_root_.Formalism.HermitianLatticesTheory.fDeg K - 1, by omega⟩
    rw [hm, pow_mul, pow_mul, pow_succ ((3 / 2 : ℝ) ^ 2), pow_succ ((3 * Real.pi / 4) ^ 2)]
    have hpi := Real.pi_gt_d2
    have hc : (11 / 2 : ℝ) ≤ (3 * Real.pi / 4) ^ 2 := by nlinarith
    have hm' : ((3 / 2 : ℝ) ^ 2) ^ m ≤ ((3 * Real.pi / 4) ^ 2) ^ m :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) m
    have hc' : (3 / 2 : ℝ) ^ 2 ≤ 4 / 9 * (3 * Real.pi / 4) ^ 2 := by nlinarith
    have := mul_le_mul hm' hc' (by positivity) (by positivity)
    linarith
  have hne : (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K) ≠ 0 := by omega
  have hexp : (1 / (2 * (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ))) = (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ := by
    push_cast; rw [one_div]
  refine ⟨hn, h1, ?_, ?_⟩
  · rw [hv, hexp]
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (2 * _root_.Formalism.HermitianLatticesTheory.fDeg K)) ^ (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ :=
          (Real.pow_rpow_inv_natCast (by norm_num) hne).symm
      _ ≤ |(discr K : ℝ)| ^ (((2 * _root_.Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ))⁻¹ :=
          Real.rpow_le_rpow (by positivity) hbound (by positivity)
  · rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hD0, Real.sqrt_eq_rpow]
    congr 1
    have : (_root_.Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0 := by exact_mod_cast (by omega : _root_.Formalism.HermitianLatticesTheory.fDeg K ≠ 0)
    field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootDiscrGeThreeHalvesOfIsTotallyComplexStatement
open MeasureTheory NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootDiscr_ge_three_halves_of_isTotallyComplex : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → Module.finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K ∧ 1 ≤ Formalism.HermitianLatticesTheory.fDeg K ∧ (3 / 2 : ℝ) ≤ 2 * Formalism.HermitianLatticesTheory.vInv K ∧ Real.sqrt |(discr K : ℝ)| = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K := by
  first | exact @GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex | exact GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex | (intros; apply GlobalTheory.rootDiscr_ge_three_halves_of_totallyComplex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContDiffExtensionOfIsClosed
open Formalism.REAL
open scoped ContDiff Manifold Topology

namespace GlobalTheory


open scoped ContDiff Manifold Topology in
theorem _root_.GlobalTheory.exists_contDiff_extension_of_isClosed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hS : IsClosed S) (f : E → ℂ)
    (hf : ∀ x ∈ S, ∃ (U : Set E) (F : E → ℂ), IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ y ∈ U, y ∈ S → f y = F y) :
    ∃ F : E → ℂ, ContDiff ℝ ∞ F ∧ ∀ y ∈ S, F y = f y := by
  classical
  let t : E → Set ℂ := fun y => if y ∈ S then {f y} else Set.univ
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    by_cases hy : y ∈ S
    · simp only [t, if_pos hy]; exact convex_singleton _
    · simp only [t, if_neg hy]; exact convex_univ
  have hloc : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ g : E → ℂ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) g U ∧ ∀ y ∈ U, g y ∈ t y := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hf x hx
      refine ⟨U, hU.mem_nhds hxU, F, hF.contMDiffOn, fun y hy => ?_⟩
      by_cases hyS : y ∈ S
      · simp only [t, if_pos hyS, Set.mem_singleton_iff]; exact (hfF y hy hyS).symm
      · simp only [t, if_neg hyS, Set.mem_univ]
    · refine ⟨Sᶜ, hS.isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, fun y hy => ?_⟩
      simp only [t, if_neg (show y ∉ S from hy), Set.mem_univ]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ, E) (n := ⊤) ht hloc
  refine ⟨g, g.contMDiff.contDiff, fun y hy => ?_⟩
  have hgy := hg y
  simpa only [t, if_pos hy, Set.mem_singleton_iff] using hgy


open scoped ContDiff Manifold Topology in
theorem _root_.GlobalTheory.smoothOnG_exists_contDiff_extension :
    ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), _root_.Formalism.REAL.SmoothOnG ε f →
      ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧
        ∀ g : Matrix (Fin n) (Fin n) ℂ, _root_.Formalism.REAL.inUJ ε g → F (fun i j => g i j) = f g := by
  intro n ε f hf
  let S : Set (Fin n → Fin n → ℂ) := {x | _root_.Formalism.REAL.inUJ ε (Matrix.of x)}
  have hS : IsClosed S := by
    have h0 : Continuous (fun x : Fin n → Fin n → ℂ => Matrix.of x) := continuous_id
    have hc : Continuous
        (fun x : Fin n → Fin n → ℂ => Matrix.conjTranspose (Matrix.of x) * _root_.Formalism.REAL.Jm ε * Matrix.of x) :=
      (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
    exact isClosed_eq hc continuous_const
  obtain ⟨F, hF, hFS⟩ := _root_.GlobalTheory.exists_contDiff_extension_of_isClosed hS
    (fun x => f (Matrix.of x)) (by
      intro x hx
      unfold _root_.Formalism.REAL.SmoothOnG at hf
      obtain ⟨U, G, hU, hxU, hG, hfG⟩ := hf (Matrix.of x) hx
      let U' : Set (Fin n → Fin n → ℂ) := U
      let G' : (Fin n → Fin n → ℂ) → ℂ := G
      have hU' : IsOpen U' := hU
      have hG' : ContDiffOn ℝ ∞ G' U' := hG
      exact ⟨U', G', hU', hxU, hG', fun y hy hyS => hfG (Matrix.of y) hy hyS⟩)
  exact ⟨F, hF, fun g hg => hFS (fun i j => g i j) hg⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemCoord
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.SAN

def hq {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E := ∑ i, ∑ j, x i * Hm i j * sig (y j)

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.hq_add_l {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    _root_.GlobalTheory.HL.SAN.hq sig Hm (a + b) y = _root_.GlobalTheory.HL.SAN.hq sig Hm a y + _root_.GlobalTheory.HL.SAN.hq sig Hm b y := by
  simp only [_root_.GlobalTheory.HL.SAN.hq, Pi.add_apply, add_mul, Finset.sum_add_distrib]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.hq_smul_l {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    _root_.GlobalTheory.HL.SAN.hq sig Hm (c • a) y = c * _root_.GlobalTheory.HL.SAN.hq sig Hm a y := by
  simp only [_root_.GlobalTheory.HL.SAN.hq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

def eQ {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (s : E) : (Fin n → E) →ₗ[E] (Fin n → E) where
  toFun v := v + hq sig Hm v u • x - hq sig Hm v x • (u + s • x)
  map_add' a b := by
    simp only [hq_add_l]; module
  map_smul' c a := by
    simp only [hq_smul_l, RingHom.id_apply]; module

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.mem_coord {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {N : ℕ} (x : Fin N → E) :
    x ∈ Submodule.span L.O (Set.range fun i => (Pi.single i 1 : Fin N → E)) ↔ ∀ j, x j ∈ L.O := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro j
      by_cases h : j = i
      · subst h; simp [L.O.one_mem]
      · simp [Pi.single_apply, h, L.O.zero_mem]
    | zero => intro j; exact L.O.zero_mem
    | add y z _ _ hy hz => intro j; exact add_mem (hy j) (hz j)
    | smul c y _ hy =>
      intro j
      simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      exact mul_mem c.2 (hy j)
  · intro hx
    have hsum : x = ∑ j, (⟨x j, hx j⟩ : L.O) • (Pi.single j 1 : Fin N → E) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem hf_int {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) {x y : Fin N → E} (hx : ∀ j, x j ∈ L.O) (hy : ∀ j, y j ∈ L.O) :
    hf L Hm x y ∈ L.O :=
  L.O.sum_mem fun i _ => L.O.sum_mem fun j _ =>
    L.O.mul_mem (L.O.mul_mem (hx i) (hI i j)) (GlobalTheory.UnramOrder.cj_mem L (hy j))

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private theorem hf_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (hI : ∀ i j, H i j ∈ L.O) (x y : Fin n → E) (hx : ∀ j, x j ∈ L.O) (hy : ∀ j, y j ∈ L.O) :
    _root_.GlobalTheory.HL.hf L H x y ∈ L.O := by
  unfold _root_.GlobalTheory.HL.hf
  exact sum_mem fun i _ => sum_mem fun j _ =>
    mul_mem (mul_mem (hx i) (hI i j)) (_root_.GlobalTheory.UnramOrder.cj_mem L (hy j))

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
private theorem eich_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} {H : Matrix (Fin n) (Fin n) E}
    (hI : ∀ i j, H i j ∈ L.O) {x u : Fin n → E} {s : E} (hx : ∀ j, x j ∈ L.O)
    (hu : ∀ j, u j ∈ L.O) (hs : s ∈ L.O) {v : Fin n → E} (hv : ∀ j, v j ∈ L.O) (j : Fin n) :
    _root_.GlobalTheory.HL.eich L H x u s v j ∈ L.O := by
  unfold _root_.GlobalTheory.HL.eich
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact sub_mem (add_mem (hv j) (mul_mem (hf_mem_O L hI v u hv hu) (hx j)))
    (mul_mem (hf_mem_O L hI v x hv hx) (add_mem (hu j) (mul_mem hs (hx j))))

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.int_prod {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) : ∀ (m : ℕ) (X u : Fin m → Fin N → E) (s : Fin m → E)
    (e : Fin m → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i j, X i j ∈ L.O) → (∀ i j, u i j ∈ L.O) →
    (∀ i, s i ∈ L.O) → (∀ i v, e i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v) →
    ∀ x : Fin N → E, (∀ j, x j ∈ L.O) → ∀ j, (List.ofFn e).prod x j ∈ L.O := by
  intro m
  induction m with
  | zero =>
    intro X u s e _ _ _ _ x hx j
    simpa using hx j
  | succ m ih =>
    intro X u s e hX hu hs he x hx j
    rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply, he 0]
    exact eich_mem_O L hI (hX 0) (hu 0) (hs 0)
      (fun j' => ih (fun i => X i.succ) (fun i => u i.succ) (fun i => s i.succ) (fun i => e i.succ)
        (fun i => hX i.succ) (fun i => hu i.succ) (fun i => hs i.succ) (fun i => he i.succ) x hx j') j

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.ext_prod {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ} : ∀ (m : ℕ)
    (a : Fin m → (Fin N → E) ≃ₗ[E] (Fin N → E))
    (b : Fin m → (Fin N → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin N → (A.loc p).Ep)),
    (∀ i, A.Ext p (a i) (b i)) →
      A.Ext p (List.ofFn a).prod (List.ofFn b).prod := by
  intro m
  induction m with
  | zero =>
    intro a b _
    simp only [_root_.GlobalTheory.HL.Places.Ext]
    intro x
    simp
  | succ m ih =>
    intro a b h
    have ih' := ih (fun i => a i.succ) (fun i => b i.succ) (fun i => h i.succ)
    simp only [_root_.GlobalTheory.HL.Places.Ext] at h ih' ⊢
    intro x
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, ih', h 0]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.bc_eQ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (x u : Fin N → E) (s : E) (v : Fin N → E) :
    A.bc p (_root_.GlobalTheory.HL.SAN.eQ sig Hm x u s v) =
      _root_.GlobalTheory.HL.eich (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p u) ((A.loc p).ιE s) (A.bc p v) := by
  have h5 := (_root_.GlobalTheory.HL.RatExt.rational_extend A N p).2.2.2.2.1 Hm
  have hu := h5 v u
  have hx := h5 v x
  unfold _root_.GlobalTheory.HL.eich
  rw [hu, hx]
  funext i
  simp [_root_.GlobalTheory.HL.Places.bc, _root_.GlobalTheory.HL.SAN.eQ, _root_.GlobalTheory.HL.SAN.hq]

open ValuativeRel NumberField IsDedekindDomain in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.HL.SAN.exists_place (F : Type) [Field F] [NumberField F] : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, (Ideal.bot_lt_of_maximal M (NumberField.RingOfIntegers.not_isField F)).ne'⟩⟩

end GlobalTheory.HL.SAN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringOHolds
namespace GlobalTheory

theorem coveringO_holds : Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO := by
  apply Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.coveringO_of_transference
  intro E _ _ _ Λ _ _ lam hlam hdual x
  exact transferenceCover_holds E Λ lam hlam hdual x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasicInequality
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.BasicIneq

theorem amp_le_mass {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) (d : S.Datum) (P : Submodule L.O S.V → Prop) :
    ENNReal.ofReal (‖S.amp d P‖) ≤ S.mass d P := by
  rw [ofReal_norm_eq_enorm]
  unfold Frames.amp Frames.mass
  refine enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun o => ?_)
  split_ifs with h
  · obtain ⟨p, hp⟩ := h.1
    have h1 : ‖S.om d o.out‖ = 1 := (WitIndep.witness_independence L r k S d _ _ _ hp).2.2.2.2
    have h2 : 0 ≤ S.mu o.out := by
      unfold Frames.mu invVol
      positivity
    rw [← ofReal_norm_eq_enorm, norm_mul, h1, mul_one, Complex.norm_real, Real.norm_of_nonneg h2]
  · simp

theorem basic_inequality : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 1 ≤ k → (∀ d P, ENNReal.ofReal (‖S.amp d P‖) ≤ S.mass d P) ∧ ∀ (P : S.Datum → Submodule L.O S.V → Prop) (B ε : ℝ), 0 ≤ ε → (∀ d, S.mass d (P d) ≤ ENNReal.ofReal (B)) → (∀ d, ENNReal.ofReal (‖S.amp d (P d)‖) ≤ ENNReal.ofReal (ε) * S.mass d (P d)) → S.ampSq P ≤ ENNReal.ofReal (ε ^ 2 * B) * S.sumData fun d => S.mass d (P d) := by
  intro F _ _ _ _ _ E _ _ _ L r k S _
  refine ⟨amp_le_mass L r k S, fun P B ε hε hB hA => ?_⟩
  unfold Frames.ampSq Frames.sumData
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o => ?_
  rw [mul_left_comm]
  refine mul_le_mul_right ?_ _
  beta_reduce
  rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul (sq_nonneg ε), ENNReal.ofReal_pow hε]
  calc ENNReal.ofReal ‖S.amp o.out (P o.out)‖ ^ 2
      ≤ (ENNReal.ofReal ε * S.mass o.out (P o.out)) ^ 2 := by
        gcongr
        exact hA _
    _ = ENNReal.ofReal ε ^ 2 * S.mass o.out (P o.out) * S.mass o.out (P o.out) := by ring
    _ ≤ ENNReal.ofReal ε ^ 2 * ENNReal.ofReal B * S.mass o.out (P o.out) := by
        gcongr
        exact hB _

end GlobalTheory.HL.BasicIneq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntCastIsUnitCompletionAlmostAllPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntCastIsUnitCompletionAlmostAllPlaces
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PlacesInt

theorem intCast_isUnit_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (D : ℤ), D ≠ 0 → {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (D : (A.loc p).Fp)}.Finite := by
  intro F E _ _ _ _ _ sig A D hD
  have hDF : (D : F) ≠ 0 := Int.cast_ne_zero.2 hD
  refine (HeightOneSpectrum.Support.finite (𝓞 F) ((D : F)⁻¹)).subset fun p hp => ?_
  by_contra hs
  apply hp
  have hs' : p.valuation F ((D : F)⁻¹) ≤ 1 := by
    have := hs
    simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at this
    exact this
  have h1 : p.valuation F (D : F) ≤ 1 := by
    have := p.valuation_le_one (K := F) (D : 𝓞 F)
    simpa using this
  have m1 := ((integers_local A).2.2.1 (D : F) p).2 h1
  have m2 := ((integers_local A).2.2.1 ((D : F)⁻¹) p).2 hs'
  have hne : (A.loc p).ιF (D : F) ≠ 0 := by
    rw [map_ne_zero]; exact hDF
  refine ⟨⟨⟨_, m1⟩, ⟨_, m2⟩, ?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    change (A.loc p).ιF (D : F) * (A.loc p).ιF ((D : F)⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ hDF, map_one]
  · apply Subtype.ext
    change (A.loc p).ιF ((D : F)⁻¹) * (A.loc p).ιF (D : F) = 1
    rw [← map_mul, inv_mul_cancel₀ hDF, map_one]
  · change (A.loc p).ιF (D : F) = _
    exact map_intCast _ D

end GlobalTheory.HL.PlacesInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntCastIsUnitCompletionAlmostAllPlacesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intCast_isUnit_completion_almost_all_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (D : ℤ), D ≠ 0 → {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (D : (A.loc p).Fp)}.Finite := by
  first | exact @GlobalTheory.HL.PlacesInt.intCast_isUnit_almost_all | exact GlobalTheory.HL.PlacesInt.intCast_isUnit_almost_all | (intros; apply GlobalTheory.HL.PlacesInt.intCast_isUnit_almost_all <;> assumption)
end
end
