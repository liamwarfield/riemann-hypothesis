module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsExpSmulA

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LevNOsmul
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PchainDN
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

section Lin

variable {O : Type} [CommRing O] {A M : Type} [AddCommGroup A] [Module O A] [AddCommGroup M]
  [Module O M]

theorem linLift (K : Submodule O M) (R : A → M → Prop) (hex : ∀ a, ∃ x, R a x)
    (hadd : ∀ a a' x x', R a x → R a' x' → R (a + a') (x + x'))
    (hsmul : ∀ (o : O) a x, R a x → R (o • a) (o • x))
    (huniq : ∀ a x x', R a x → R a x' → x - x' ∈ K) :
    ∃ ψ : A →ₗ[O] M ⧸ K, ∀ a, ∃ x, R a x ∧ ψ a = K.mkQ x := by
  choose g hg using hex
  refine ⟨{ toFun := fun a => K.mkQ (g a), map_add' := ?_, map_smul' := ?_ }, fun a => ⟨g a, hg a, rfl⟩⟩
  · intro a a'
    rw [← map_add (f := _)]
    exact (Submodule.Quotient.eq K).2 (huniq _ _ _ (hg (a + a')) (hadd _ _ _ _ (hg a) (hg a')))
  · intro o a
    rw [RingHom.id_apply, ← map_smul]
    exact (Submodule.Quotient.eq K).2 (huniq _ _ _ (hg (o • a)) (hsmul o _ _ (hg a)))

end Lin

section bigCellDetWeightedEnergyIntegral

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem pchain_DN' (i : ZMod n) (k : ℕ) {m : ℕ} {cc : ℝ} {FF : Type} [AddCommGroup FF]
    [Module O FF] (K : Submodule O ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)) (s : Finset (W.DD T))
    (hs : s.card ≤ m) (hsN : (↑s : Set (W.DD T)) ⊆ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) (L kO : ℕ)
    (hL : Module.length O (↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸
      (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype) ≤ (L : ℕ∞))
    (hkO : lenOl PD (O := O) = kO) (hLc : (L : ℝ) ≤ cc * kO) (A : Submodule O FF)
    (ψ : ↥A →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain (lenOl PD (O := O)) m cc A
      (kerSub A ψ (((Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype).map K.mkQ)) 1 1 := by
  set X := (Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hXdef
  set Y := (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hYdef
  have hXY : X ≤ Y := Submodule.comap_mono le_sup_left
  have hlen : Module.length O ((↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) ⧸ Y.map K.mkQ) ≤ (L : ℕ∞) := by
    rw [(Submodule.quotientQuotientEquivQuotientSup K Y).length_eq]
    refine le_trans ?_ hL
    exact Module.length_le_of_surjective (Submodule.mapQ Y (K ⊔ Y) LinearMap.id
      (fun y hy => Submodule.mem_sup_right (by simpa using hy)))
      (fun z => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        exact ⟨Submodule.Quotient.mk x, rfl⟩)
  have h1 := pstep_len (m := m) (c := cc) A ψ (Y.map K.mkQ) L kO hlen hkO hLc
  set A₁ := kerSub A ψ (Y.map K.mkQ) with hA₁def
  have hA₁ : A₁ ≤ A := kerSub_le A ψ _
  set ψ₁ : ↥A₁ →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K := ψ.comp (Submodule.inclusion hA₁)
  set sN : Finset ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) := s.subtype (· ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)
  set s' := sN.image K.mkQ
  have hcard : s'.card ≤ m := by
    refine Finset.card_image_le.trans (le_trans ?_ hs)
    rw [Finset.card_subtype]
    exact Finset.card_filter_le _ _
  have hspan : Submodule.span O (↑s : Set (W.DD T)) =
      (Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i))).map
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype := by
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hsN hy⟩, Finset.mem_subtype.2 hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact Finset.mem_subtype.1 hz
  have hY : Y ≤ X ⊔ Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)) := by
    intro z hz
    have hz' : (z : W.DD T) ∈ Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T)) := hz
    obtain ⟨x, hx, t, ht, hxt⟩ := Submodule.mem_sup.1 hz'
    rw [hspan] at ht
    obtain ⟨t', ht', rfl⟩ := Submodule.mem_map.1 ht
    have hxN : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i := by
      have e : x = (z : W.DD T) - (t' : W.DD T) := by rw [← hxt]; simp
      rw [e]; exact (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).sub_mem z.2 t'.2
    refine Submodule.mem_sup.2 ⟨⟨x, hxN⟩, hx, t', ht', Subtype.ext ?_⟩
    simpa using hxt
  have hgen : ∀ a, ψ₁ a ∈ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
    intro a
    have ha : ψ ⟨(a : FF), hA₁ a.2⟩ ∈ Y.map K.mkQ := (mem_kerSub_coe A ψ _ ⟨a, hA₁ a.2⟩).1 a.2
    have hle : Y.map K.mkQ ≤ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
      calc Y.map K.mkQ ≤ (X ⊔ Submodule.span O (↑sN : Set _)).map K.mkQ := Submodule.map_mono hY
        _ = X.map K.mkQ ⊔ (Submodule.span O (↑sN : Set _)).map K.mkQ := Submodule.map_sup _ _ _
        _ = X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
          rw [Submodule.map_span, Finset.coe_image]
    exact hle ha
  have h2 := pstep_gen (lenO := lenOl PD (O := O)) (m := m) (c := cc) A₁ ψ₁ (X.map K.mkQ) s' hcard hgen
  have heq : kerSub A₁ ψ₁ (X.map K.mkQ) = kerSub A ψ (X.map K.mkQ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := (mem_kerSub A₁ ψ₁ _ x).1 hx
      exact (mem_kerSub A ψ _ x).2 ⟨hA₁ hx1, hx2⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := (mem_kerSub A ψ _ x).1 hx
      have hx1' : x ∈ A₁ := (mem_kerSub A ψ _ x).2 ⟨hx1, Submodule.map_mono hXY hx2⟩
      exact (mem_kerSub A₁ ψ₁ _ x).2 ⟨hx1', hx2⟩
  rw [heq] at h2
  exact (pchain_of_len h1).trans (pchain_of_gen h2)

end bigCellDetWeightedEnergyIntegral

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.NDlCoords
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

section GenM

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {LL : Type} [Field LL]
  [Algebra O LL] [IsFractionRing O LL] {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
  {U : Type} [AddCommGroup U] [Module LL U]

theorem genM (φ : M →+ U) (hφ : ∀ (c : O) (x : M), φ (c • x) = algebraMap O LL c • φ x) {m : ℕ}
    (hm : Module.finrank LL ↥(Submodule.span LL (Set.range φ)) ≤ m) :
    ∃ s : Finset M, s.card ≤ m ∧ ∀ x : M, ∃ y ∈ Submodule.span O (↑s : Set M), φ (x - y) = 0 := by
  let A : Submodule O M := ⊤
  let φ' : ↥A →+ U := φ.comp A.subtype.toAddMonoidHom
  have hφ' : ∀ (c : O) (x : ↥A), φ' (c • x) = algebraMap O LL c • φ' x := fun c x => hφ c x
  have hr : Set.range φ' = Set.range φ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨⟨x, trivial⟩, rfl⟩
  have hm' : Module.finrank LL ↥(Submodule.span LL (Set.range φ')) ≤ m := by rwa [hr]
  obtain ⟨-, Q, i1, i2, ob, hker, hgen, -⟩ :=
    pstep_rank (lenO := 0) (m := m) (c := 0) A φ' hφ' hm'
  obtain ⟨sQ, hsQ, hspan⟩ := hgen trivial
  obtain ⟨t, ht, htN, hNt⟩ := Formalism.MainNotions.RamifiedCoefficientChains.exists_gen_of_le_span sQ (LinearMap.range ob)
    (by rw [hspan]; exact le_top)
  have hpre : ∀ q : ↥t, ∃ x : ↥A, ob x = q := fun q => htN q.2
  choose f hf using hpre
  refine ⟨Finset.univ.image (fun q : ↥t => ((f q : ↥A) : M)), ?_, fun x => ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp only [Finset.card_univ, Fintype.card_coe]
    exact ht.trans hsQ
  · have hx : ob ⟨x, trivial⟩ ∈ Submodule.span O (↑t : Set Q) := hNt ⟨_, rfl⟩
    rw [Submodule.mem_span_finset] at hx
    obtain ⟨a, -, hax⟩ := hx
    set y : M := ∑ q : ↥t, a q • ((f q : ↥A) : M) with hy
    refine ⟨y, Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ q)))), ?_⟩
    have hoby : ob ⟨y, trivial⟩ = ob ⟨x, trivial⟩ := by
      have e : (⟨y, trivial⟩ : ↥A) = ∑ q : ↥t, a q • f q := Subtype.ext (by simp [hy])
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e, map_sum, ← hax]
      rw [← Finset.sum_coe_sort t]
      exact Finset.sum_congr rfl fun q _ => by rw [map_smul, hf q]
    have h0 : ob (⟨x, trivial⟩ - ⟨y, trivial⟩) = 0 := by rw [map_sub, hoby, sub_self]
    have hz := (hker _).1 h0
    have := (mem_zeroSub_coe A φ' hφ' (⟨x, trivial⟩ - ⟨y, trivial⟩)).1 hz
    simpa [φ'] using this

end GenM

section Frame

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem NDl_coords (i : ZMod n) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) :
    ∃ (d : ℕ) (b : Fin d → W.DD T), (∀ k, b k ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ∧
      ∀ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i, ∃ α : Fin d → O,
        Formalism.MainNotions.ArcLiftingSetup.cmpD W T y = ∑ k, algebraMap O LL (α k) • Formalism.MainNotions.ArcLiftingSetup.cmpD W T (b k) := by
  obtain ⟨d, b, hb⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.frame_exists W T i hmod
  have hbN : ∀ k, b k ∈ W.N T := fun k => (hb.1 k).1.1
  have hbl : ∀ k, (letE i : LetA O n) • b k = b k := fun k =>
    Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T i (hb.1 k).2
  refine ⟨d, b, fun k => ⟨hbN k, hbl k, (hb.1 k).1.2⟩, fun y hy => ?_⟩
  have hy' : y ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i y := hy
  have hyi : Formalism.MainNotions.LiftingTheory.InNΔi W T i y :=
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_of W T i ⟨hy'.1, hy'.2.2⟩ hy'.2.1
  obtain ⟨a, ⟨-, hya⟩, -⟩ := hb.2 y hyi
  refine ⟨fun k => PowerSeries.constantCoeff ((a k) i), ?_⟩
  rw [hya, cmpD_sum W T _ _ (fun k _ => (W.N T).smul_mem _ (hbN k))]
  exact Finset.sum_congr rfl fun k _ => cmpD_smul_letter W T i (a k) (hbN k) (hbl k)

end Frame

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Fam

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem levN_osmul (c : ZMod n) (ζ : LL) (o : O) (x : ↥(W.N T)) :
    W.levN T c ζ (o • x) = algebraMap O LL o • W.levN T c ζ x := by
  obtain ⟨m, hm⟩ := W.levN_supp T c ζ x
  have e : (o • x : ↥(W.N T)) = (algebraMap O (LetA O n) o) • x := by
    ext; simp [algebraMap_smul]
  rw [e]
  have := funext fun k => W.levN_smul T c ζ (algebraMap O (LetA O n) o) x k
  rw [this]
  change smulS _ _ = _
  have hC : (algebraMap O (PowerSeries LL) o) = PowerSeries.C (algebraMap O LL o) := by
    first
    | exact PowerSeries.algebraMap_apply' o
    | exact PowerSeries.algebraMap_apply o
    | simp [PowerSeries.algebraMap_apply']
    | simp [PowerSeries.algebraMap_apply]
  rw [AlgHom.commutes, hC, smulS_C hm]

theorem fam_exp [IsDomain O] {A : Type} [AddCommGroup A] [Module O A] (hs : W.s = 1)
    (c : ZMod n) (ζ₀ : LL)
    (hLv : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T c ζ₀ x k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-k))
    (χ : LL) (hχ0 : χ ≠ 0) (hχ : ∀ i : ℤ, i ≠ 0 → χ ^ i ≠ 1)
    (hγN : ∀ (x : W.DD T) (hx : x ∈ W.N T) (hγx : W.γ T x ∈ W.N T) (k : ℤ),
      W.levN T c ζ₀ ⟨W.γ T x, hγx⟩ k = χ ^ k • W.levN T c ζ₀ ⟨x, hx⟩ k)
    (hγA : ∀ f : LetA O n, W.lev c ζ₀ (W.γA W.gam f) = PowerSeries.rescale χ (W.lev c ζ₀ f))
    (u₀ : PowerSeries LL) (hu₀ : W.lev c ζ₀ W.q = X * u₀) (hu0 : constantCoeff u₀ ≠ 0)
    (K : ℕ) (w : A →ₗ[O] W.DD T) (hK : ∀ f, W.Q ^ K • w f ∈ W.N T)
    (hγw : ∀ f, W.γ T (w f) - w f ∈ W.N T) :
    ∃ dd : A → ℤ → T.V ⊗[Qp] BdR, (∀ f, ∃ m, LB m (dd f)) ∧
      (∀ f, W.levN T c ζ₀ ⟨W.Q ^ K • w f, hK f⟩ = smulS ((X * u₀) ^ K) (dd f)) ∧
      (∀ f (i : ℤ), i ≠ 0 → dd f i ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i)) ∧
      (∀ f g, dd (f + g) = dd f + dd g) ∧ (∀ (o : O) f, dd (o • f) = algebraMap O LL o • dd f) := by
  have ex : ∀ f, ∃ d : ℤ → T.V ⊗[Qp] BdR, (∃ m, LB m d) ∧
      W.levN T c ζ₀ ⟨W.Q ^ K • w f, hK f⟩ = smulS ((X * u₀) ^ K) d ∧
      ∀ i : ℤ, (χ ^ i - 1) • d i ∈ Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-i) :=
    fun f => gamma_levels_expansion W T hs c ζ₀ hLv χ hχ0 hγN hγA u₀ hu₀ hu0 (hK f) (hγw f)
  choose dd hdLB hde hdγ using ex
  have hanti := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T c 0
  refine ⟨dd, hdLB, hde, fun f i hi => ?_, fun f g => ?_, fun o f => ?_⟩
  · have h := Formalism.KernelCokernelLengths.exists_fixed_add_of_sub_mem LL (T.V ⊗[Qp] BdR) (fun a => Formalism.MainNotions.WachCoordinates.FilLev W T c 0 a)
      hanti χ hχ 0 0 (dd f) (fun j h1 h2 => by omega) (hdγ f)
    exact h.1 i hi
  · obtain ⟨m1, h1⟩ := hdLB (f + g)
    obtain ⟨m2, h2⟩ := hdLB f
    obtain ⟨m3, h3⟩ := hdLB g
    have e1 : (⟨W.Q ^ K • w (f + g), hK (f + g)⟩ : ↥(W.N T)) =
        ⟨W.Q ^ K • w f, hK f⟩ + ⟨W.Q ^ K • w g, hK g⟩ := Subtype.ext (by simp [smul_add])
    have e2 := hde (f + g)
    rw [e1, map_add (f := _), hde f, hde g, ← smulS_add (LB_mono h2 (min_le_left m2 m3))
      (LB_mono h3 (min_le_right m2 m3))] at e2
    exact div_unique (m := min m1 (min m2 m3)) (LB_mono h1 (min_le_left _ _))
      (LB_mono (LB_add (LB_mono h2 (min_le_left m2 m3)) (LB_mono h3 (min_le_right m2 m3)))
        (min_le_right _ _)) u₀ hu0 K e2.symm
  · obtain ⟨m1, h1⟩ := hdLB (o • f)
    obtain ⟨m2, h2⟩ := hdLB f
    have e1 : (⟨W.Q ^ K • w (o • f), hK (o • f)⟩ : ↥(W.N T)) = o • ⟨W.Q ^ K • w f, hK f⟩ :=
      Subtype.ext (by simp [osmul_comm W T])
    have e2 := hde (o • f)
    rw [e1, levN_osmul W T c ζ₀ o, hde f, ← smulS_smul h2] at e2
    exact div_unique (m := min m1 m2) (LB_mono h1 (min_le_left _ _))
      (LB_mono (LB_smul h2 _) (min_le_right _ _)) u₀ hu0 K e2.symm

end Fam

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Pre

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def preG (i : ZMod n) {U : Type} [AddCommGroup U] [Module LL U]
    (G : (T.V ⊗[Qp] B) →ₗ[LL] U) (Z : Submodule LL U) :
    Submodule O ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) where
  carrier := {x | G (Formalism.MainNotions.ArcLiftingSetup.cmpD W T (x : W.DD T)) ∈ Z}
  add_mem' := fun {a b} ha hb => by
    show G (Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((a : W.DD T) + b)) ∈ Z
    rw [cmpD_add W T (NDl_N W T a.2) (NDl_N W T b.2), map_add (f := _)]
    exact Z.add_mem ha hb
  zero_mem' := by
    show G (Formalism.MainNotions.ArcLiftingSetup.cmpD W T 0) ∈ Z
    rw [cmpD_zero W T, map_zero]; exact Z.zero_mem
  smul_mem' := fun o x hx => by
    show G (Formalism.MainNotions.ArcLiftingSetup.cmpD W T (o • (x : W.DD T))) ∈ Z
    rw [cmpD_osmul W T o (NDl_N W T x.2), map_smul]
    exact Z.smul_mem _ hx

end Pre

section Pass3

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem pass3 [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O LL]
    (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (c : ZMod n) {hh e₂ m : ℕ} {κ : ℤ} {cc : ℝ} (η : ℕ)
    (hM' : ∀ z ∈ W.Nl T (c - 1 - 1 - 1), W.Q ^ hh • W.φD T z ∈ W.N T)
    (hDN : ∃ s : Finset (W.DD T), s.card ≤ m ∧
      (↑s : Set (W.DD T)) ⊆ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1) ∧
      ∃ L kO : ℕ, Module.length O (↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1)) ⧸
          (Xd W T (c - 1 - 1) hh ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
            (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1)).subtype) ≤ (L : ℕ∞) ∧
        lenOl PD (O := O) = kO ∧ (L : ℝ) ≤ cc * kO)
    (C : Submodule LL (T.V ⊗[Qp] B)) [FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb (c - 1)))]
    (hRk : Module.finrank LL ↥((DcrisL PD T.ρ (W.emb (c - 1))).map C.mkQ) ≤ m)
    {FF : Type} [AddCommGroup FF] [Module O FF] (A : Submodule O FF)
    (d0 : ↥A → T.V ⊗[Qp] BdR) (hd0a : ∀ f g, d0 (f + g) = d0 f + d0 g)
    (hd0s : ∀ (o : O) f, d0 (o • f) = algebraMap O LL o • d0 f)
    (hex : ∀ f, ∃ x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1),
      (PD.p : LL) ^ e₂ • d0 f - (PD.p : LL) ^ (κ - hh) • ιV PD (LL := LL) (V := T.V)
        (φVB PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T x))) ∈
        Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-(η : ℤ))) :
    ∃ (F3 : Submodule O FF) (hF3 : F3 ≤ A),
      Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain (lenOl PD (O := O)) m cc A F3 2 1 ∧
      ∀ f : ↥F3, ∃ ell ∈ (fun z => φVB PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) z)) ''
          Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T (c - 1 - 1 - 1), ell ∈ C ∧
        (PD.p : LL) ^ e₂ • d0 (Submodule.inclusion hF3 f) - (PD.p : LL) ^ κ •
          ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) ell) ∈
          Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-(η : ℤ)) := by
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  set Fη := Formalism.MainNotions.WachCoordinates.FilLev W T c 0 (-(η : ℤ)) with hFη
  set φ1 : (T.V ⊗[Qp] B) →ₗ[LL] (T.V ⊗[Qp] B) := φVB PD (LL := LL) (V := T.V) with hφ1
  set φ2 : (T.V ⊗[Qp] B) →ₗ[LL] (T.V ⊗[Qp] B) := φ1.comp φ1 with hφ2
  set ιv : (T.V ⊗[Qp] B) →ₗ[LL] (T.V ⊗[Qp] BdR) := ιV PD (LL := LL) (V := T.V) with hιv
  set Gx := ιv.comp φ2 with hGx
  set G3 := ιv.comp (φ1.comp φ2) with hG3
  set K3 := preG W T (c - 1 - 1) Gx Fη with hK3

  let R : ↥A → ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1)) → Prop := fun f x =>
    (PD.p : LL) ^ e₂ • d0 f - (PD.p : LL) ^ (κ - hh) • Gx (Formalism.MainNotions.ArcLiftingSetup.cmpD W T (x : W.DD T)) ∈ Fη
  have hex' : ∀ f, ∃ x, R f x := fun f => by
    obtain ⟨x, hx, hx'⟩ := hex f
    exact ⟨⟨x, hx⟩, hx'⟩
  have hadd : ∀ f g x x', R f x → R g x' → R (f + g) (x + x') := by
    intro f g x x' h1 h2
    show _ ∈ Fη
    have e : Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((x + x' : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1))) : W.DD T) =
        Formalism.MainNotions.ArcLiftingSetup.cmpD W T (x : W.DD T) + Formalism.MainNotions.ArcLiftingSetup.cmpD W T (x' : W.DD T) :=
      cmpD_add W T (NDl_N W T x.2) (NDl_N W T x'.2)
    rw [e, hd0a, map_add (f := _), smul_add, smul_add]
    have := Fη.add_mem h1 h2
    convert this using 1
    abel
  have hsm : ∀ (o : O) f x, R f x → R (o • f) (o • x) := by
    intro o f x h
    show _ ∈ Fη
    have e : Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((o • x : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1))) : W.DD T) =
        algebraMap O LL o • Formalism.MainNotions.ArcLiftingSetup.cmpD W T (x : W.DD T) :=
      cmpD_osmul W T o (NDl_N W T x.2)
    rw [e, hd0s, map_smul, smul_comm _ (algebraMap O LL o), smul_comm _ (algebraMap O LL o),
      ← smul_sub]
    exact Fη.smul_mem _ h
  have huniq : ∀ f x x', R f x → R f x' → x - x' ∈ K3 := by
    intro f x x' h1 h2
    show Gx (Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((x - x' : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1))) : W.DD T)) ∈ Fη
    rw [Submodule.coe_sub, cmpD_sub W T (NDl_N W T x.2) (NDl_N W T x'.2), map_sub]
    have h := Fη.sub_mem h2 h1
    rw [sub_sub_sub_cancel_left, ← smul_sub] at h
    have h' := Fη.smul_mem ((PD.p : LL) ^ (κ - hh))⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hp), one_smul] at h'
  obtain ⟨ψ3, hψ3⟩ := linLift K3 R hex' hadd hsm huniq
  obtain ⟨s₂, hs₂, hs₂N, L, kO, hL, hkO, hLc⟩ := hDN
  have ch1 := pchain_DN' W T (c - 1 - 1) hh K3 s₂ hs₂ hs₂N L kO hL hkO hLc A ψ3
  set F3b := kerSub A ψ3 (((Xd W T (c - 1 - 1) hh).comap
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1)).subtype).map K3.mkQ) with hF3bdef
  have hF3b : F3b ≤ A := kerSub_le _ _ _

  set Amb := preG W T (c - 1 - 1 - 1) G3 Fη with hAmb
  let R3 : ↥F3b → ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1)) → Prop := fun f y =>
    (PD.p : LL) ^ e₂ • d0 (Submodule.inclusion hF3b f) -
      (PD.p : LL) ^ κ • G3 (Formalism.MainNotions.ArcLiftingSetup.cmpD W T (y : W.DD T)) ∈ Fη
  have hex3 : ∀ f, ∃ y, R3 f y := by
    intro f
    have hf := (mem_kerSub_coe A ψ3 _ (Submodule.inclusion hF3b f)).1 f.2
    obtain ⟨x, hxX, hxe⟩ := Submodule.mem_map.1 hf
    obtain ⟨xf, hRf, hψf⟩ := hψ3 (Submodule.inclusion hF3b f)
    rw [hψf] at hxe
    have hdiff : xf - x ∈ K3 := (Submodule.Quotient.eq K3).1 hxe.symm
    obtain ⟨y, hy, hyx⟩ := cmp_of_mem_X W T hs hR h3 hM' hxX
    refine ⟨⟨y, hy⟩, ?_⟩
    show _ ∈ Fη
    have hk : Gx (Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((xf - x : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1))) :
        W.DD T)) ∈ Fη := hdiff
    rw [Submodule.coe_sub, cmpD_sub W T (NDl_N W T xf.2) (NDl_N W T x.2), map_sub] at hk
    have hGxx : Gx (Formalism.MainNotions.ArcLiftingSetup.cmpD W T (x : W.DD T)) =
        (PD.p : LL) ^ hh • G3 (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y) := by
      have hyx' : Formalism.MainNotions.ArcLiftingSetup.cmpD W T (x : W.DD T) =
          (PD.p : LL) ^ hh • φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y) := hyx
      rw [hyx']
      simp only [hGx, hG3, LinearMap.comp_apply, map_smul]
      rfl
    have := Fη.add_mem hRf (Fη.smul_mem ((PD.p : LL) ^ (κ - hh)) hk)
    rw [hGxx] at this
    have hsc : (PD.p : LL) ^ (κ - hh) * (PD.p : LL) ^ hh = (PD.p : LL) ^ κ := by
      rw [← zpow_natCast, ← zpow_add₀ hp, sub_add_cancel]
    convert this using 1
    rw [smul_sub, smul_smul, hsc]
    abel
  have hadd3 : ∀ f g y y', R3 f y → R3 g y' → R3 (f + g) (y + y') := by
    intro f g y y' h1 h2
    show _ ∈ Fη
    have e : Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((y + y' : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1))) :
        W.DD T) = Formalism.MainNotions.ArcLiftingSetup.cmpD W T (y : W.DD T) + Formalism.MainNotions.ArcLiftingSetup.cmpD W T (y' : W.DD T) :=
      cmpD_add W T (NDl_N W T y.2) (NDl_N W T y'.2)
    rw [e, map_add (f := _), map_add (f := _), hd0a, smul_add, smul_add]
    have := Fη.add_mem h1 h2
    convert this using 1
    abel
  have hsm3 : ∀ (o : O) f y, R3 f y → R3 (o • f) (o • y) := by
    intro o f y h
    show _ ∈ Fη
    have e : Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((o • y : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1))) :
        W.DD T) = algebraMap O LL o • Formalism.MainNotions.ArcLiftingSetup.cmpD W T (y : W.DD T) :=
      cmpD_osmul W T o (NDl_N W T y.2)
    rw [e, map_smul, map_smul, hd0s, smul_comm _ (algebraMap O LL o),
      smul_comm _ (algebraMap O LL o), ← smul_sub]
    exact Fη.smul_mem _ h
  have huniq3 : ∀ f y y', R3 f y → R3 f y' → y - y' ∈ Amb := by
    intro f y y' h1 h2
    show G3 (Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((y - y' : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1))) :
      W.DD T)) ∈ Fη
    rw [Submodule.coe_sub, cmpD_sub W T (NDl_N W T y.2) (NDl_N W T y'.2), map_sub]
    have h := Fη.sub_mem h2 h1
    rw [sub_sub_sub_cancel_left, ← smul_sub] at h
    have h' := Fη.smul_mem ((PD.p : LL) ^ κ)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hp), one_smul] at h'
  obtain ⟨ψ3c, hψ3c⟩ := linLift Amb R3 hex3 hadd3 hsm3 huniq3

  set preC := preG W T (c - 1 - 1 - 1) φ2 C with hpreC
  obtain ⟨d, bF, hbN, hcoord⟩ := NDl_coords W T (c - 1 - 1 - 1) hmod
  have hbN' : ∀ k, bF k ∈ W.N T := fun k => NDl_N W T (hbN k)
  let phA : (Fin d → O) →+ (T.V ⊗[Qp] B) ⧸ C :=
    { toFun := fun α => C.mkQ (φ2 (∑ k, algebraMap O LL (α k) • Formalism.MainNotions.ArcLiftingSetup.cmpD W T (bF k)))
      map_zero' := by simp
      map_add' := fun α β => by
        simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib] }
  have hphA : ∀ (o : O) (α : Fin d → O), phA (o • α) = algebraMap O LL o • phA α := by
    intro o α
    simp only [phA, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.smul_apply, smul_eq_mul, map_mul,
      mul_smul, ← Finset.smul_sum, map_smul]
  have hletter : ∀ k, φ2 (Formalism.MainNotions.ArcLiftingSetup.cmpD W T (bF k)) ∈ DcrisL PD T.ρ (W.emb (c - 1)) := by
    intro k
    have h0 : Formalism.MainNotions.ArcLiftingSetup.cmpD W T (bF k) ∈ DcrisL PD T.ρ (W.emb (c - 1 - 1 - 1)) := by
      rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (hbN' k)]
      exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_mem_letter W T _ (hbN' k) (NDl_DL W T (hbN k)).1
    have h2 := Formalism.MainNotions.UnusedSlot80.ArcF.φVB_letter W T _ (Formalism.MainNotions.UnusedSlot80.ArcF.φVB_letter W T _ h0)
    rw [show c - 1 - 1 - 1 + 1 + 1 = c - 1 by ring] at h2
    exact h2
  have hrank : Module.finrank LL ↥(Submodule.span LL (Set.range phA)) ≤ m := by
    have hsub : Submodule.span LL (Set.range phA) ≤ (DcrisL PD T.ρ (W.emb (c - 1))).map C.mkQ := by
      rw [Submodule.span_le]
      rintro _ ⟨α, rfl⟩
      refine ⟨_, ?_, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Submodule.sum_mem _ fun k _ => by
        rw [map_smul]; exact Submodule.smul_mem _ _ (hletter k)
    exact (Submodule.finrank_mono hsub).trans hRk
  obtain ⟨s₀, hs₀, hs₀g⟩ := genM phA hphA hrank
  let lin : (Fin d → O) →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1)) :=
    Fintype.linearCombination O (fun k => (⟨bF k, hbN k⟩ : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1))))
  have hlin : ∀ α, Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((lin α : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1))) :
      W.DD T) = ∑ k, algebraMap O LL (α k) • Formalism.MainNotions.ArcLiftingSetup.cmpD W T (bF k) := by
    intro α
    simp only [lin, Fintype.linearCombination_apply, Submodule.coe_sum, Submodule.coe_smul]
    rw [cmpD_sum W T _ _ (fun k _ => by
      rw [← algebraMap_smul (LetA O n)]; exact (W.N T).smul_mem _ (hbN' k))]
    exact Finset.sum_congr rfl fun k _ => cmpD_osmul W T _ (hbN' k)
  set sG : Finset (↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1)) ⧸ Amb) :=
    s₀.image (fun α => Amb.mkQ (lin α)) with hsG
  have hsGc : sG.card ≤ m := Finset.card_image_le.trans hs₀
  have hgenz : ∀ z : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1)) ⧸ Amb,
      z ∈ preC.map Amb.mkQ ⊔ Submodule.span O (↑sG : Set _) := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective Amb z
    obtain ⟨α, hα⟩ := hcoord y y.2
    obtain ⟨σ, hσ, hφ0⟩ := hs₀g α
    have hy' : y - lin σ ∈ preC := by
      show φ2 (Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((y - lin σ : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1))) :
        W.DD T)) ∈ C
      rw [Submodule.coe_sub, cmpD_sub W T (NDl_N W T y.2) (NDl_N W T (lin σ).2), hα, hlin]
      have h0 : C.mkQ (φ2 (∑ k, algebraMap O LL ((α - σ) k) • Formalism.MainNotions.ArcLiftingSetup.cmpD W T (bF k))) = 0 :=
        hφ0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
      convert h0 using 2
      simp only [Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]
    have hm1 : Amb.mkQ (y - lin σ) ∈ preC.map Amb.mkQ := Submodule.mem_map_of_mem hy'
    have hm2 : Amb.mkQ (lin σ) ∈ Submodule.span O (↑sG : Set _) := by
      have h := Submodule.mem_map_of_mem (f := Amb.mkQ ∘ₗ lin) hσ
      rw [Submodule.map_span] at h
      rw [hsG, Finset.coe_image]
      exact h
    have e : Submodule.Quotient.mk y = Amb.mkQ (y - lin σ) + Amb.mkQ (lin σ) := by
      rw [← map_add (f := _), sub_add_cancel]; rfl
    rw [e]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hm1) (Submodule.mem_sup_right hm2)
  have ch2 := pchain_of_gen (pstep_gen (lenO := lenOl PD (O := O)) (m := m) (c := cc) F3b ψ3c
    (preC.map Amb.mkQ) sG hsGc (fun a => hgenz _))
  set F3 := kerSub F3b ψ3c (preC.map Amb.mkQ) with hF3def
  have hF3' : F3 ≤ F3b := kerSub_le _ _ _
  refine ⟨F3, hF3'.trans hF3b, (ch1.trans ch2).mono (by norm_num) (by norm_num), fun f => ?_⟩
  set f3b : ↥F3b := Submodule.inclusion hF3' f
  have hker := (mem_kerSub_coe F3b ψ3c _ f3b).1 f.2
  obtain ⟨y', hy'C, hy'e⟩ := Submodule.mem_map.1 hker
  obtain ⟨yf, hR3f, hψf⟩ := hψ3c f3b
  rw [hψf] at hy'e
  have hdiff : yf - y' ∈ Amb := (Submodule.Quotient.eq Amb).1 hy'e.symm
  have hdiff' : G3 (Formalism.MainNotions.ArcLiftingSetup.cmpD W T ((yf - y' : ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1))) :
      W.DD T)) ∈ Fη := hdiff
  rw [Submodule.coe_sub, cmpD_sub W T (NDl_N W T yf.2) (NDl_N W T y'.2), map_sub] at hdiff'
  refine ⟨φ2 (Formalism.MainNotions.ArcLiftingSetup.cmpD W T (y' : W.DD T)),
    ⟨Formalism.MainNotions.ArcLiftingSetup.cmpD W T (y' : W.DD T), ⟨(y' : W.DD T), NDl_N W T y'.2, NDl_DL W T y'.2,
      Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T _⟩, rfl⟩, hy'C, ?_⟩
  have e2 : Submodule.inclusion (hF3'.trans hF3b) f = Submodule.inclusion hF3b f3b := rfl
  rw [e2]
  have := Fη.add_mem hR3f (Fη.smul_mem ((PD.p : LL) ^ κ) hdiff')
  convert this using 1
  simp only [hG3, LinearMap.comp_apply, smul_sub]
  abel

end Pass3

end Formalism.MainNotions.N.Pv.LocalLengthBound
