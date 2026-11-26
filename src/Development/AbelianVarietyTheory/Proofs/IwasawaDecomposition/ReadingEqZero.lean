module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesian
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordinatesTangentFieldHolomorphicPeriodMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingEqZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.GeoTies

set_option synthInstance.maxHeartbeats 400000 in
def BarAtOne {D : D7} (T : CoreJ D) (j : ℕ) (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) {W : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel W S) (Hm : Links.HMod (MMap M)) (jf : T.cuspA j (wtA w) w.n → Hm.H) (Z : Prop) : Prop :=
  ¬ GoodEmb T.Q.c s → ∀ hV : T.V j ((starRingEnd ℂ).comp s) = W,
    ((∃ v : M.Vec, IsUnitV v ∧ EvEx (C := T.cuspA j (wtA w) w.n) s (fun h : Hm.H => Hm.e h v)
        (fun f g => starRingEnd ℂ (phiC T hV (wtA w) (f : T.R j) g))) →
      ∃ v : M.Vec, IsUnitV v ∧ ∀ f, Hm.e (jf f) v = fun g => starRingEnd ℂ (phiC T hV (wtA w) (f : T.R j) g)) ∧
    (¬ (∃ v : M.Vec, IsUnitV v ∧ EvEx (C := T.cuspA j (wtA w) w.n) s (fun h : Hm.H => Hm.e h v)
        (fun f g => starRingEnd ℂ (phiC T hV (wtA w) (f : T.R j) g))) → Z)

theorem barTie_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (t : FWTie T R κ v₀) :
    BarTie t ↔ ∀ (i : Fin D.R.m) σ, BarAtOne T ((i : ℕ) + 1) (κ i) (res T σ) (R.MW i σ) (R.HW i σ) (fun f => t.jK i σ f) ((R.FW i).j σ = 0) :=
  Iff.rfl

theorem BarAtOne.congr {D : D7} (T T' : CoreJ D) (h1 : HEq T'.Q.H T.Q.H) (h2 : HEq T'.Q.l T.Q.l) (h3 : HEq T'.Q.c T.Q.c)
    (h4 : HEq T'.Q.Dw T.Q.Dw) (h5 : HEq T'.Q.Xo T.Q.Xo) (h6 : HEq T'.U T.U) (h7 : HEq T'.V T.V) (h8 : HEq T'.dict T.dict)
    (h9 : HEq T'.mu T.mu) (h10 : HEq T'.cE T.cE) (j : ℕ) (w w' : WeightFamilies.Wt D j) (hP : HEq w'.aP w.aP) (hM : HEq w'.aM w.aM)
    (hn : w'.n = w.n) (s : T.Q.c.F →+* ℂ) (s' : T'.Q.c.F →+* ℂ)
    (hs : ∀ (y : T.Q.c.F) (y' : T'.Q.c.F), (y' : ℂ) = (y : ℂ) → s' y' = s y)
    {W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel W S) (M' : DSModel W S') (hMM : ModelSame M M')
    (Hm : Links.HMod (MMap M)) (Hm' : Links.HMod (MMap M')) (hH : HEq Hm' Hm)
    (jf : T.cuspA j (wtA w) w.n → Hm.H) (jf' : T'.cuspA j (wtA w') w'.n → Hm'.H)
    (hj : ∀ f f', HEq f' f → HEq (jf' f') (jf f)) {Z Z' : Prop} (hZ : Z → Z') :
    BarAtOne T j w s M Hm jf Z → BarAtOne T' j w' s' M' Hm' jf' Z' := by
  obtain ⟨⟨⟨H, l, c, Dw, Xo, eO⟩, U, V, dict, mu, Kf, pb⟩, cE, chiW, x₀, iota⟩ := T
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  cases h8
  cases h9
  cases h10
  obtain ⟨aP, aM, _, _, n, _⟩ := w
  obtain ⟨aP', aM', _, _, n', _⟩ := w'
  dsimp only at hP hM hn
  cases hP
  cases hM
  cases hn
  have hs' : s' = s := RingHom.ext fun y => hs y y rfl
  subst hs'
  obtain ⟨X, σ, lam, ε, fr, _, _, _, _⟩ := M
  obtain ⟨X', σ', lam', ε', fr', _, _, _, _⟩ := M'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hMM
  dsimp only at m1 m2 m3 m4 m5 m6 m7
  cases m1
  cases m2
  cases m3
  cases m4
  cases m5
  cases m6
  cases m7
  have hH' : Hm' = Hm := eq_of_heq hH
  subst hH'
  have hj' : jf' = jf := funext fun f => eq_of_heq (hj f f HEq.rfl)
  subst hj'
  intro h hg hV
  exact ⟨(h hg hV).1, fun h' => hZ ((h hg hV).2 h')⟩

theorem reading_eq_zero {L L' : Type} [Field L] [Field L'] (ι : L →+* L') (σ' : L' →+* ℂ) {n n' : ℕ} (hn : n = n')
    {A A' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A']
    (j : (Fin n → L) →ₛₗ[σ'.comp ι] A) (j' : (Fin n' → L') →ₛₗ[σ'] A')
    (h : ∀ x x', CrdOver ι x x' → HEq (j' x') (j x)) (h0 : j = 0) : j' = 0 := by
  subst hn
  subst h0
  have hz : HEq (j' 0) (0 : A) := h 0 0 ⟨rfl, fun k k' _ => (map_zero ι).symm⟩
  have hk : ∀ k, j' (Pi.single k 1) = 0 := fun k => by
    have h1 : HEq (j' (Pi.single k 1)) (0 : A) := h (Pi.single k 1) (Pi.single k 1) ⟨rfl, fun a b hab => by
      obtain rfl : a = b := Fin.ext hab
      by_cases hak : a = k
      · subst hak
        simp
      · simp [Pi.single_apply, hak]⟩
    exact (eq_of_heq (h1.trans hz.symm)).trans (map_zero j')
  refine LinearMap.ext fun x => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pi_eq_sum_univ' x, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [map_smulₛₗ, hk, smul_zero]

theorem barTie_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
        ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
        ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (fw' : FWTie core' R'.toRealDat κ' v₀'),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
          (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)) →
        GeoTies.MWOver z.R.toRealDat R'.toRealDat → BarTie fw' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg hc Xg tr R' cG' hpins hRS κ' hκ v₀' fw' hcrd hMW
  letI := alg'
  letI := z.alg
  have hK : B'.Ks.map B'.embLL.toRatAlgHom = B.Ks.map B.embLL.toRatAlgHom := SetLike.coe_injective hE.2.1
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := (by with_unfolding_all exact ((congrArg (fun P : Pre => P.R.m) hE.1) :))
  refine (barTie_iff fw').2 fun i' σ' => ?_
  let i : Fin (w.st Z).toD7.R.m := ⟨i'.1, hm ▸ i'.2⟩
  have hi : (i : ℕ) = i' := rfl
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL := (by with_unfolding_all exact ((enlEmb hE.2.2.2) :))
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := (by with_unfolding_all exact ((enlEmb_spec hE.2.2.2) :))
  have hb := (barTie_iff z.geo.fw).1 z.geo.bar i (σ'.comp ι)
  have hMM := hMW i i' hi ι hι σ'
  have hnW := hRS.1.2.2.2.2.2.1
  have hcl := ((hRS.1.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1 σ'
  have hH := hcl.2.1
  have hjj := hcl.2.2.2
  have hs : ∀ (y : z.core.Q.c.F) (y' : core'.Q.c.F), (y' : ℂ) = (y : ℂ) →
      res core' σ' y' = res z.core (σ'.comp ι) y := fun y y' hy =>
    congrArg σ' ((w'.st Z').toD7.what₂.embLL.injective
      (((by with_unfolding_all exact ((halg y') :)) : (w'.st Z').toD7.what₂.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y') = (y' : ℂ)).trans
        (hy.trans ((hι _).trans ((by with_unfolding_all exact ((z.alg_eq y) :)) :
          (w.st Z).toD7.what₂.embLL (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL y) = (y : ℂ))).symm)))
  have hgen : ∀ {m m' : ℕ} (_ : m' = m) (a : Fin m → ℕ) (a' : Fin m' → ℕ), HEq a' a → ∀ (k : Fin m) (k' : Fin m'),
      (k : ℕ) = k' → a k = a' k' := by
    intro m m' h a a' ha k k' hk
    subst h
    cases ha
    rw [Fin.ext hk]
  have hn : z.R.nW i = R'.nW i' := hgen hm _ _ hnW i i' hi
  have hj : ∀ φ φ', HEq φ' φ → HEq (fw'.jK i' σ' φ') (z.geo.fw.jK i (σ'.comp ι) φ) := fun φ φ' hφ =>
    hjj _ _ ⟨hn, fun k k' hk => (w'.st Z').toD7.what₂.embLL.injective ((hcrd i i' hi φ φ' hφ k k' hk).trans (hι _).symm)⟩
  have hZ : (z.R.FW i).j (σ'.comp ι) = 0 → (R'.FW i').j σ' = 0 := reading_eq_zero ι σ' hn _ _ hjj
  obtain ⟨hP, hM, hnn⟩ := hκ i i' hi
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -, c10, -⟩ := hc
  have h1 := hE.1
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  let Q₀ : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := (by with_unfolding_all exact (z.core.Q.H :)), l := (by with_unfolding_all exact (z.core.Q.l :)), c := (by with_unfolding_all exact (z.core.Q.c :)), Dw := (by with_unfolding_all exact (z.core.Q.Dw :)), Xo := (by with_unfolding_all exact (z.core.Q.Xo :)),
      eO := (by with_unfolding_all exact ((z.core.Q.eO.trans (oEquiv hK)) :)) }
  let core₀ : Formalism.L2.Pj.CoreJ (w'.st Z').toD7 :=
    { toCore :=
        { Q := Q₀, U := (by with_unfolding_all exact (z.core.U :)), V := (by with_unfolding_all exact (z.core.V :)), dict := (by with_unfolding_all exact (z.core.dict :)), mu := (by with_unfolding_all exact (z.core.mu :)),
          Kf := (by with_unfolding_all exact (z.core.Kf :)), pb := (by with_unfolding_all exact (z.core.pb :)) }
      cE := (by with_unfolding_all exact (z.core.cE :)), chiW := (by with_unfolding_all exact (z.core.chiW :)), x₀ := (by with_unfolding_all exact (z.core.x₀ :)), iota := (by with_unfolding_all exact (z.core.iota :)) }
  let κ₀ : WeightFamilies.Wt (w'.st Z').toD7 ((i' : ℕ) + 1) :=
    { aP := (by with_unfolding_all exact ((z.geo.κ i).aP :)), aM := (by with_unfolding_all exact ((z.geo.κ i).aM :)), aPlus_antitone := (by with_unfolding_all exact ((z.geo.κ i).aPlus_antitone :)),
      aM_anti := (by with_unfolding_all exact ((z.geo.κ i).aM_anti :)), n := (z.geo.κ i).n, n_even := (z.geo.κ i).n_even }
  let S₀ : (w'.st Z').toD7.what₂.Tau → SPar := (by with_unfolding_all exact ((parAt (Wc (w.st Z).toD7 i) (σ'.comp ι)) :))
  let M₀ : DSModel (Wc (w'.st Z').toD7 i') S₀ :=
    @DSModel.mk _ _ _ ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).H :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).nacg :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ips :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).σ :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).lam :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ε :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).enum :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ds :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr_unit :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr_gram :)))
  let H₀ : Links.HMod (MMap M₀) := (by with_unfolding_all exact ((z.R.HW i (σ'.comp ι)) :))
  let s₀ : core₀.Q.c.F →+* ℂ := (by with_unfolding_all exact ((res z.core (σ'.comp ι)) :))
  let j₀ : core₀.cuspA ((i' : ℕ) + 1) (wtA κ₀) κ₀.n → H₀.H := (by with_unfolding_all exact ((fun φ => z.geo.fw.jK i (σ'.comp ι) φ) :))
  exact BarAtOne.congr core₀ core' ((by with_unfolding_all exact (c1 :))) ((by with_unfolding_all exact (c2 :))) ((by with_unfolding_all exact (c3 :))) ((by with_unfolding_all exact (c4 :))) ((by with_unfolding_all exact (c5 :))) ((by with_unfolding_all exact (c6 :))) ((by with_unfolding_all exact (c7 :))) ((by with_unfolding_all exact (c8 :))) ((by with_unfolding_all exact (c9 :))) ((by with_unfolding_all exact (c10 :)))
    ((i' : ℕ) + 1) κ₀ (κ' i') ((by with_unfolding_all exact (hP :))) ((by with_unfolding_all exact (hM :))) ((by with_unfolding_all exact (hnn :))) s₀ (res core' σ') ((by with_unfolding_all exact (hs :))) M₀ (R'.MW i' σ') ((by with_unfolding_all exact (hMM :)))
    H₀ (R'.HW i' σ') ((by with_unfolding_all exact (hH :))) j₀ _ ((by with_unfolding_all exact (hj :))) hZ ((by with_unfolding_all exact (hb :)))

end GlobalTheory.Mem.R3.Rw.GeoTies
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralAppOfUniversallyClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalSectionOfIsIntegralElemNormalScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalSectionOfIsIntegralElemNormalScheme
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem exists_section_of_isIntegralElem_of_isOpenImmersion {T Z : Scheme.{0}}
    [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j] :
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by
  intro hd U s hs u hu
  let C : irreducibleComponents Z := ⟨_, irreducibleComponent_mem_irreducibleComponents u⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, huW, hWle⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (show u ∈ ((U ⊓ IsNormalScheme.component C : Z.Opens) : Set Z) from
      ⟨hu, mem_irreducibleComponent⟩)
    (U ⊓ IsNormalScheme.component C).isOpen
  have hWU : W ≤ U := fun x hx ↦ (hWle hx).1
  refine ⟨W, hWU, huW, ?_⟩
  have hWirr : IsIrreducible (W : Set Z) :=
    ⟨⟨u, huW⟩, C.2.1.2.open_subset W.isOpen fun x hx ↦ (hWle hx).2⟩
  obtain ⟨_, _⟩ := IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hWirr
  obtain ⟨x, hxW, hfr, hgen⟩ : ∃ (x : Z) (hxW : x ∈ W),
      (letI := Z.presheaf.algebra_section_stalk (U := W) ⟨x, hxW⟩;
        IsFractionRing Γ(Z, W) (Z.presheaf.stalk x)) ∧ ∀ w ∈ W, x ⤳ w := by
    let P : Spec Γ(Z, W) := ⟨⊥, Ideal.isPrime_bot⟩
    have hxW : hW.fromSpec P ∈ W := hW.range_fromSpec.le ⟨P, rfl⟩
    refine ⟨_, hxW, ?_, ?_⟩
    · let _ := Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩
      have h := hW.isLocalization_stalk' P hxW
      have e : P.asIdeal.primeCompl = nonZeroDivisors Γ(Z, W) := by
        ext a
        simp [P, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
      unfold IsLocalization.AtPrime at h
      rw [e] at h
      exact h
    · intro w hw
      obtain ⟨q, rfl⟩ : w ∈ Set.range hW.fromSpec := hW.range_fromSpec.ge hw
      exact ((PrimeSpectrum.le_iff_specializes P q).mp bot_le).map hW.fromSpec.continuous
  obtain ⟨y, rfl⟩ : x ∈ Set.range j := by
    obtain ⟨w, hw, hwr⟩ := hd.inter_open_nonempty _ W.isOpen ⟨u, huW⟩
    exact (hgen w hw).mem_open j.isOpenEmbedding.isOpen_range hwr
  let _ := Z.presheaf.algebra_section_stalk (U := W) ⟨_, hxW⟩
  let _ : Algebra Γ(Z, W) Γ(T, j ⁻¹ᵁ W) := (j.app W).hom.toAlgebra
  have hyW : y ∈ j ⁻¹ᵁ W := hxW
  have hnat : (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op).hom.comp (j.app U).hom =
      (algebraMap Γ(Z, W) Γ(T, j ⁻¹ᵁ W)).comp (Z.presheaf.map (homOfLE hWU).op).hom := by
    change _ = (j.app W).hom.comp _
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, j.naturality]
    rfl
  have hs₁ : IsIntegral Γ(Z, W) (T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) := by
    obtain ⟨p, hp, hps⟩ := hs
    refine ⟨p.map (Z.presheaf.map (homOfLE hWU).op).hom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← hnat, ← Polynomial.hom_eval₂, hps, map_zero]
  have hgerm (a : Γ(Z, W)) : j.stalkMap y (Z.presheaf.germ W (j y) hxW a) =
      T.presheaf.germ (j ⁻¹ᵁ W) y hyW (j.app W a) :=
    j.germ_stalkMap_apply W y hxW a
  have hbij : Function.Bijective (j.stalkMap y) := ConcreteCategory.bijective_of_isIso _
  let φ : Γ(T, j ⁻¹ᵁ W) ⟶ Z.presheaf.stalk (j y) :=
    T.presheaf.germ (j ⁻¹ᵁ W) y hyW ≫ inv (j.stalkMap y)
  have hφ (c : Γ(T, j ⁻¹ᵁ W)) : j.stalkMap y (φ c) = T.presheaf.germ (j ⁻¹ᵁ W) y hyW c := by
    rw [← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ : Γ(T, j ⁻¹ᵁ W) →ₐ[Γ(Z, W)] Z.presheaf.stalk (j y) :=
    { φ.hom with commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.map ψ hs₁)
  refine ⟨a, ?_⟩
  have hg : T.presheaf.germ (j ⁻¹ᵁ W) y hyW
      (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) = 0 := by
    rw [map_sub, ← hgerm, ← hφ, sub_eq_zero]
    exact congr(j.stalkMap y $ha)
  have : IsReduced T := isReduced_of_isOpenImmersion j
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro t ht
  have hyt : y ⤳ t :=
    j.isOpenEmbedding.isInducing.specializes_iff.mp (hgen _ (T.basicOpen_le _ ht))
  have hy : y ∈ T.basicOpen
      (j.app W a - T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) :=
    hyt.mem_open (T.basicOpen _).isOpen ht
  rw [Scheme.mem_basicOpen _ _ _ hyW, hg] at hy
  exact (not_isUnit_zero hy).elim

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalSectionOfIsIntegralElemNormalSchemeStatement
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_section_of_isIntegralElem_normal_scheme : ∀ {T Z : Scheme.{0}} [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j],
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by
  first | exact @GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion | exact GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion | (intros; apply GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueOfDenseOpenImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueOfDenseOpenImmersion
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem app_injective_of_dense_range {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j]
    (hj : Dense (Set.range j)) (W : Z.Opens) : Function.Injective (j.app W).hom := by
  intro a b hab
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  have h0 : j ⁻¹ᵁ Z.basicOpen (a - b) = ⊥ := by
    rw [Scheme.preimage_basicOpen, map_sub, hab, sub_self, Scheme.basicOpen_zero]
  by_contra hne
  obtain ⟨z, hz⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
  obtain ⟨x, hx1, ⟨y, rfl⟩⟩ := hj.inter_open_nonempty _ (Z.basicOpen (a - b)).isOpen ⟨z, hz⟩
  have : y ∈ j ⁻¹ᵁ Z.basicOpen (a - b) := hx1
  rw [h0] at this
  exact this

theorem app_res_eq {T Z : Scheme.{0}} (j : T ⟶ Z) {V W : Z.Opens} (i : V ⟶ W)
    (i' : j ⁻¹ᵁ V ⟶ j ⁻¹ᵁ W) (a : Γ(Z, W)) :
    j.app V (Z.presheaf.map i.op a) = T.presheaf.map i'.op (j.app W a) := by
  obtain rfl : i' = (Opens.map j.base).map i := Subsingleton.elim _ _
  have := congrArg (fun f => f.hom a) (j.naturality i.op)
  simpa using this

theorem glue_of_dense_openImmersion : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by
  intro T Z _ j _ hj U s hloc
  choose W hWU hmem h hh using hloc
  let Wf : U → Z.Opens := fun u => W u.1 u.2
  have hcover : U ≤ iSup Wf := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hmem x hx⟩
  obtain ⟨g, hg, -⟩ := Z.sheaf.existsUnique_gluing' Wf U (fun u => homOfLE (hWU u.1 u.2)) hcover
    (fun u => h u.1 u.2) (by
      intro u v
      apply app_injective_of_dense_range j hj
      change j.app _ (Z.presheaf.map _ (h u.1 u.2)) = j.app _ (Z.presheaf.map _ (h v.1 v.2))
      rw [app_res_eq j _ (homOfLE (j.preimage_mono inf_le_left)),
        app_res_eq j _ (homOfLE (j.preimage_mono inf_le_right)), hh, hh]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  let g' : Γ(Z, U) := g
  have hg' : ∀ u : U, Z.presheaf.map (homOfLE (hWU u.1 u.2)).op g' = h u.1 u.2 := hg
  refine ⟨g', ?_⟩
  refine T.sheaf.eq_of_locally_eq' (fun u : U => j ⁻¹ᵁ Wf u) (j ⁻¹ᵁ U)
    (fun u => homOfLE (j.preimage_mono (hWU u.1 u.2))) ?_ _ _ ?_
  · intro x hx
    exact Opens.mem_iSup.2 ⟨⟨j x, hx⟩, hmem _ hx⟩
  · intro u
    have key : T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op (j.app U g') =
        T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op s := by
      rw [← app_res_eq j (homOfLE (hWU u.1 u.2)), hg' u, hh]
    exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueOfDenseOpenImmersionStatement
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_extending_of_dense_openImmersion : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by
  first | exact @GlobalTheory.glue_of_dense_openImmersion | exact GlobalTheory.glue_of_dense_openImmersion | (intros; apply GlobalTheory.glue_of_dense_openImmersion <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GenPush

theorem isIntegral_of_isIso_comp {A B C D : CommRingCat.{0}} (k : A ⟶ B) (f : B ⟶ C) (m : C ⟶ D) [IsIso k]
    [IsIso m] (h : (k ≫ f ≫ m).hom.IsIntegral) : f.hom.IsIntegral := by
  have e : f = inv k ≫ (k ≫ f ≫ m) ≫ inv m := by simp
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.IsIntegral.trans _ _ ?_ (RingHom.IsIntegral.trans _ _ h ?_)
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv k)).2
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv m)).2

theorem isIntegral_app_of_universallyClosed {Z₁ Z₂ : Scheme.{0}} (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (U : Z₂.Opens) (hU : IsAffineOpen U) : (ρ.app U).hom.IsIntegral := by
  have : IsAffine U.toScheme := hU
  have h := isIntegral_appTop_of_universallyClosed (ρ ∣_ U)
  rw [morphismRestrict_appTop] at h
  have e : U.ι ''ᵁ ⊤ = U := by simp
  rw [ρ.app_eq e, Category.assoc, Category.assoc, ← Functor.map_comp] at h
  simp only [eqToHom_op, eqToHom_map, eqToHom_trans] at h
  have hi : ∀ {A B : CommRingCat.{0}} (p : A = B), IsIso (eqToHom p) := fun p => by
    subst p; rw [eqToHom_refl]; infer_instance
  refine @isIntegral_of_isIso_comp _ _ _ _ _ _ _ ?_ ?_ h
  · exact hi _
  · exact hi _

theorem exists_app_eq_of_isIntegralElem {T Z : Scheme.{0}} [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z]
    (j : T ⟶ Z) [IsOpenImmersion j] (hj : Dense (Set.range j)) (U : Z.Opens)
    (s : Γ(T, j ⁻¹ᵁ U)) (hs : (j.app U).hom.IsIntegralElem s) : ∃ h : Γ(Z, U), j.app U h = s :=
  GlobalTheory.T.exists_section_extending_of_dense_openImmersion j hj U s fun u hu => GlobalTheory.T.exists_local_section_of_isIntegralElem_normal_scheme j hj U s hs u hu

section Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

end Models

end GlobalTheory.GenPush
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorStrictnessSmoothFan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorStrictnessSmoothFan
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolCell

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X X₁ : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] {m : ℕ}

theorem StrictWith.mul {N t : ℕ} (ht : 0 < t) {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    {u : Fin m → LinearMap.BilinForm ℤ X} (h : StrictWith bar φ N ℓ u) :
    StrictWith bar φ (t * N) ((t : ℤ) • ℓ) u := by
  obtain ⟨h1, h2, h3⟩ := h
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  refine ⟨fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => h3 β hβ hp ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, h1 i, Nat.cast_mul]; ring
  · have := mul_le_mul_of_nonneg_left (h2 β hβ hp) ht'.le
    simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    linarith
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at he
    have : (t : ℝ) * (N * φ.evalZ β) = t * ℓ β := by linarith
    exact mul_left_cancel₀ ht'.ne' this

theorem StrictWith.of_pull {N : ℕ} {r : X →ₗ[O] X₁} (hr : Function.Surjective r) {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    {u : Fin m → LinearMap.BilinForm ℤ X₁} (h : StrictWith bar φ N ℓ fun i => pull r (u i)) :
    StrictWith bar φ N (ℓ ∘ₗ { toFun := pull r, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }) u := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => (h1 i).trans (by rw [evalZ_pull φ hr]), fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · rw [← evalZ_pull φ hr]
    exact h2 _ (pull_mem r hβ) fun y => hp _
  · rw [← evalZ_pull φ hr] at he
    obtain ⟨k, c, hk, hc⟩ := h3 _ (pull_mem r hβ) (fun y => hp _) he
    refine ⟨k, c, hk, LinearMap.ext₂ fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := hr a
    obtain ⟨b, rfl⟩ := hr b
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ hc a b

end GlobalTheory.PolCell


open Classical in
theorem GlobalTheory.PolCell.exists_common_den : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ),
    IsPolFanOn (id : ℤ → ℤ) φ X → ∃ N : ℕ, 0 < N ∧ ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ)
      (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧
      StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u := by
  intro X _ _ φ hφ
  obtain ⟨S, hS, hSc⟩ := hφ.finite
  haveI : Finite S := hS.to_subtype
  let K := Σ m : Fin (Nat.card S + 1), (Fin m → S)
  haveI : Fintype K := Fintype.ofFinite K
  let D : K → ℕ := fun k =>
    if h : IsCone (id : ℤ → ℤ) φ (fun i => ((k.2 i : S) : LinearMap.BilinForm ℤ X)) then Classical.choose h.strict else 1
  have hD : ∀ k, 0 < D k := fun k => by
    simp only [D]
    split_ifs with h
    · exact (Classical.choose_spec (Classical.choose_spec h.strict)).1
    · exact one_pos
  refine ⟨∏ k, D k, Finset.prod_pos fun k _ => hD k, fun B hB => ?_⟩
  obtain ⟨m, γ, c, hγ, hc, rfl⟩ := hφ.cover B hB
  obtain ⟨e, he⟩ := hSc m γ hγ
  have hγ' := hγ.pull_equiv e
  have hm : m < Nat.card S + 1 := by
    have := Nat.card_le_card_of_injective (fun i : Fin m => (⟨_, he i⟩ : S))
      (fun i j h => hγ'.injective (congrArg Subtype.val h))
    rw [Nat.card_fin] at this
    exact Nat.lt_succ_of_le this
  let k : K := ⟨⟨m, hm⟩, fun i => ⟨_, he i⟩⟩
  have hk : IsCone (id : ℤ → ℤ) φ (fun i => ((k.2 i : S) : LinearMap.BilinForm ℤ X)) := hγ'
  have hDk : D k = Classical.choose hk.strict := dif_pos hk
  obtain ⟨ℓ, -, hℓ⟩ := Classical.choose_spec hk.strict
  obtain ⟨t, ht⟩ : D k ∣ ∏ k, D k := Finset.dvd_prod_of_mem D (Finset.mem_univ k)
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · have := Finset.prod_pos fun k (_ : k ∈ Finset.univ) => hD k
      rw [ht, h, mul_zero] at this; exact absurd this (lt_irrefl 0)
    · exact h
  have h1 : StrictWith (id : ℤ → ℤ) φ (t * D k) ((t : ℤ) • ℓ) fun i => pull e.toLinearMap (γ i) := by
    rw [hDk]; exact StrictWith.mul ht0 hℓ
  have h2 := StrictWith.of_pull e.surjective h1
  obtain ⟨w, hw⟩ := exists_linW_eq X (((t : ℤ) • ℓ) ∘ₗ
    { toFun := pull e.toLinearMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl })
  refine ⟨m, γ, w, hγ, ?_, c, hc, rfl⟩
  rw [hw, ht, mul_comm]
  exact h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorStrictnessSmoothFanStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_strictness_smooth_fan : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → ∃ N : ℕ, 0 < N ∧ ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), ∃ (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsCone (id : ℤ → ℤ) φ u ∧ StrictWith (id : ℤ → ℤ) φ N (linW w) u ∧ B ∈ rcone u := by
  first | exact @GlobalTheory.PolCell.exists_common_den | exact GlobalTheory.PolCell.exists_common_den | (intros; apply GlobalTheory.PolCell.exists_common_den <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimplicialLabellingOfBarycentricStageZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimplicialLabellingOfBarycentricStageZero
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.BaryFin

variable {X : Type} [AddCommGroup X]

theorem toReal_zero' : toReal (0 : LinearMap.BilinForm ℤ X) = 0 := LinearMap.ext₂ fun a b => by simp

theorem eq_zero_of_genRank_eq_zero {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (h : genRank γ = 0) (i : Fin m) :
    γ i = 0 := by
  unfold genRank at h
  haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range γ)) := Module.Finite.span_of_finite ℤ (Set.finite_range γ)
  obtain ⟨a, ha, e⟩ := Module.finrank_eq_zero_iff.1 h ⟨γ i, Submodule.subset_span ⟨i, rfl⟩⟩
  have e' : a • γ i = 0 := congrArg Subtype.val e
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ e' y z
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this ⊢
  exact (mul_eq_zero.1 this).resolve_left ha

theorem inRCone_smul_iff {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) {k : ℕ}
    (hk : 0 < k) : InRCone γ ((k : ℤ) • β) ↔ InRCone γ β := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨fun i => c i / k, fun i => div_nonneg (hc i) hk'.le, LinearMap.ext₂ fun a b => ?_⟩
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at this ⊢
    push_cast at this
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, ← this]
    field_simp
  · rintro ⟨c, hc, h⟩
    refine ⟨fun i => k * c i, fun i => mul_nonneg hk'.le (hc i), LinearMap.ext₂ fun a b => ?_⟩
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul] at this ⊢
    push_cast
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

variable {O : Type} [CommRing O] {bar : O → O} {q : ℕ}

theorem eq_zero_of_label_nonpos {ψ lab : InvFun O} (hlab : IsCarrierDim bar q ψ lab) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Projective O X] (hX : Module.finrank O X ≤ q) {b : ℕ}
    {v : Fin b → LinearMap.BilinForm ℤ X} (hv : IsCell bar ψ v) (k : Fin b) (hk : lab.evalZ (v k) ≤ 0) : v k = 0 := by
  have key := hlab X hX (v k) (hv.mem k) (hv.nonneg k)
  rw [key] at hk
  have h0 := Nat.cast_nonpos.1 hk
  have hS : ({n : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ (v k) ∧
      genRank γ = n}).Nonempty := ⟨_, b, v, hv, inRCone_self v k, rfl⟩
  obtain ⟨m, γ, -, ⟨c, -, hc⟩, hr⟩ := Nat.sInf_mem hS
  rw [h0] at hr
  have hz := eq_zero_of_genRank_eq_zero γ hr
  refine LinearMap.ext₂ fun y z => ?_
  have := LinearMap.congr_fun₂ hc y z
  simp [hz, LinearMap.sum_apply] at this
  simpa using this


variable (O bar q) in
theorem simpLab_of_isBaryStage_zero (ψ lab φ : InvFun O) (hlab : IsCarrierDim bar q ψ lab)
    (hφ : IsBaryStage bar q ψ lab φ 0) : SimpLab bar q φ lab := by
  refine ⟨fun X _ _ _ _ hX β hβ hp k hk => ?_, fun X _ _ _ _ hX m γ hγ => ?_⟩
  · have hp' : ∀ y, 0 ≤ ((k : ℤ) • β) y y := fun y => by
      simp only [LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg (by positivity) (hp y)
    rw [hlab X hX _ (Submodule.smul_mem _ _ hβ) hp', hlab X hX β hβ hp]
    simp only [inRCone_smul_iff _ _ hk]
  · obtain ⟨b, a, v, u, hc, hv, hin, hinj, -, hle, -, hli⟩ := hφ.2.2 X hX m γ hγ
    have hv0 : ∀ k, v k = 0 := fun k => eq_zero_of_label_nonpos hlab hX hv k
      (by simpa using hle (v k) (hv.mem k) (hv.nonneg k) (inRCone_self v k))
    have hu : IsCell bar φ u := by
      refine ⟨fun j => by simpa using hc.mem (Fin.natAdd b j), fun j => by simpa using hc.nonneg (Fin.natAdd b j),
        ?_, ?_⟩
      · have := linearOn_comp hc.linear (⟨Fin.natAdd b, fun x y h => by simpa using h⟩ : Fin a ↪ Fin (b + a))
        convert this using 1
        funext i
        exact (Fin.append_right v u i).symm
      · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hc.strict
        refine ⟨N, ℓ, hN, fun i => by simpa using h1 (Fin.natAdd b i), h2, fun β hβ hp he => ?_⟩
        obtain ⟨k, c, hk, hc'⟩ := h3 β hβ hp he
        refine ⟨k, fun i => c (Fin.natAdd b i), hk, ?_⟩
        rw [hc', Fin.sum_univ_add]
        simp [hv0]
    refine ⟨a, u, hu, Fintype.linearIndependent_iff.2 fun c hc0 i => congrFun (hli 0 c (by rw [hc0]; simp)) i,
      hinj, fun j => ?_⟩
    obtain ⟨c, hc0, h⟩ := hin j
    refine ⟨fun i => c (Fin.natAdd b i), fun i => hc0 _, ?_⟩
    rw [h, Fin.sum_univ_add]
    simp [hv0, toReal_zero']

end GlobalTheory.PolFan.BaryFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimplicialLabellingOfBarycentricStageZeroStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialLabelling_of_barycentricStage_zero : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ lab φ : InvFun O), IsCarrierDim bar q ψ lab → IsBaryStage bar q ψ lab φ 0 → SimpLab bar q φ lab := by
  first | exact @GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero | exact GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero | (intros; apply GlobalTheory.PolFan.BaryFin.simpLab_of_isBaryStage_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFamilyCoefficientMapsMulRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFamilyCoefficientMapsMulRootOfUnity
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.OmExt.RootUpd

open Formalism.DivisionValues

variable {D : D7}

theorem exists_unit_of_pow (a : D.what₂.LL) (n : ℕ) (hn : n ≠ 0) (ha : a ^ n = 1) :
    ∃ u : (𝓞 D.what₂.LL)ˣ, ((u : 𝓞 D.what₂.LL) : D.what₂.LL) = a ∧ a ∈ Formalism.DivisionValues.cmMax D.what₂.LL ∧ star a * a = 1 := by
  have hσ : ∀ σ : D.what₂.LL →+* ℂ, ‖σ a‖ = 1 := fun σ => by
    have h : (σ a) ^ n = 1 := by rw [← map_pow, ha, map_one]
    exact Complex.norm_eq_one_of_pow_eq_one h hn
  have hconj : ∀ z : ℂ, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun z hz => by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
    simp
  have a0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at ha
    exact zero_ne_one ha
  have m0 : D.what₂.embLL a ≠ 0 := (map_ne_zero _).2 a0
  have h2 : star a * a = 1 := D.what₂.embLL.injective (by
    rw [map_mul, D.starLL_cx, hconj _ (hσ _), inv_mul_cancel₀ m0, map_one])
  have hs : star a = a⁻¹ := eq_inv_of_mul_eq_one_left h2
  have h1 : a ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
    change ∀ σ : D.what₂.LL →+* ℂ, σ (star a) = starRingEnd ℂ (σ a)
    intro σ
    rw [hs, map_inv₀, hconj _ (hσ σ)]
  have hi : IsIntegral (𝓞 D.what₂.LL) a := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [ha]
    exact isIntegral_one
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hx1 : x ^ n = 1 := IsFractionRing.injective (𝓞 D.what₂.LL) D.what₂.LL (by rw [map_pow, hx, ha, map_one])
  refine ⟨(IsUnit.of_pow_eq_one hx1 hn).unit, ?_, h1, h2⟩
  rw [IsUnit.unit_spec]
  exact hx

theorem coefMapTie_smul {V C lam c0 rho} (h : Formalism.IndefR.Bridge.CoefMapTie (D := D) V C (lam := lam) c0 rho) {μ : ℂ} (hμ : μ ≠ 0) :
    Formalism.IndefR.Bridge.CoefMapTie V C (μ • c0) rho := by
  obtain ⟨a1, a2, a3⟩ := h
  refine ⟨fun γ γE hγ v => by simp [a1 γ γE hγ v], a2.units_smul fun _ => Units.mk0 _ hμ, ?_⟩
  rw [eq_top_iff, ← a3, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have := Submodule.smul_mem _ μ⁻¹ (Submodule.subset_span (R := ℂ)
    (s := Set.range fun i => (μ • c0) (bVV D.what₂.LL lam i)) ⟨i, rfl⟩)
  exact Set.mem_of_eq_of_mem (inv_smul_smul₀ hμ (c0 _)).symm this

theorem coefTie_smul {V C S J χ P lam c0 pair nab del}
    (h : Formalism.IndefR.Bridge.CoefTie (D := D) V C (S := S) (J := J) (χ := χ) P lam c0 pair nab del)
    (l : D.what₂.LL) (u : (𝓞 D.what₂.LL)ˣ) (hu : ((u : 𝓞 D.what₂.LL) : D.what₂.LL) = l) (h1 : l ∈ Formalism.DivisionValues.cmMax D.what₂.LL)
    (h2 : star l * l = 1) :
    Formalism.IndefR.Bridge.CoefTie V C P lam (D.what₂.embLL l • c0) pair nab del := by
  have l0 : l ≠ 0 := right_ne_zero_of_mul_eq_one h2
  have m0 : D.what₂.embLL l ≠ 0 := (map_ne_zero _).2 l0
  have li : (((u⁻¹ : (𝓞 D.what₂.LL)ˣ) : 𝓞 D.what₂.LL) : D.what₂.LL) = l⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← hu, ← map_mul (algebraMap (𝓞 D.what₂.LL) D.what₂.LL), Units.inv_mul, map_one])
  obtain ⟨e, a1, a2, a3, a4, a5⟩ := h
  let s := LinearEquiv.smulOfNeZero D.what₂.LL (VV D.what₂.LL lam) l⁻¹ (inv_ne_zero l0)
  have hs : ∀ x, (e.trans s) x = l⁻¹ • e x := fun _ => rfl
  have hm : ∀ N : Submodule (𝓞 D.what₂.LL) S.V,
      N.map ((e.trans s).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) =
        N.map (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := fun N => by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨((u⁻¹ : (𝓞 D.what₂.LL)ˣ) : 𝓞 D.what₂.LL) • v, N.smul_mem _ hv, ?_⟩
      rw [← algebraMap_smul D.what₂.LL]
      exact (map_smul e _ _).trans (congrArg (· • e v) li)
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(u : 𝓞 D.what₂.LL) • v, N.smul_mem _ hv, ?_⟩
      rw [← algebraMap_smul D.what₂.LL]
      show (e.trans s) ((algebraMap (𝓞 D.what₂.LL) D.what₂.LL (u : 𝓞 D.what₂.LL)) • v) = e v
      rw [show algebraMap (𝓞 D.what₂.LL) D.what₂.LL (u : 𝓞 D.what₂.LL) = l from hu]
      exact (hs _).trans ((congrArg (l⁻¹ • ·) (map_smul e l v)).trans (inv_smul_smul₀ l0 _))
  refine ⟨e.trans s, fun i j => ?_, fun x => ?_, fun x x' => ?_, fun c => (hm _).trans (a4 c), fun c => (hm _).trans (a5 c)⟩
  · rw [hs, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem (inv_mem h1) (a1 i j)
  · rw [hs, LinearMap.smul_apply, map_smulₛₗ, map_inv₀, smul_inv_smul₀ m0, a2]
  · rw [hs, hs, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, a3, smul_smul, starRingEnd_apply, star_inv₀,
      ← mul_inv, mul_comm, h2, inv_one, one_smul]

end GlobalTheory.Mem.R3.Rw.OmExt.RootUpd

namespace GlobalTheory.Mem.R3.Rw.OmExt


set_option maxHeartbeats 1000000 in
theorem coefFam_update_root : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (c0L : ∀ i : Fin D.R.m, Formalism.IndefR.FWT.VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W),
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R c0L → ∀ (i : Fin D.R.m) (a : D.what₂.LL) (n : ℕ), n ≠ 0 → a ^ n = 1 →
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R (Function.update c0L i (D.what₂.embLL a • c0L i)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R c0L hc i a n hn ha
  obtain ⟨u, hu, h1, h2⟩ := RootUpd.exists_unit_of_pow a n hn ha
  have m0 : D.what₂.embLL a ≠ 0 := (map_ne_zero _).2 (right_ne_zero_of_mul_eq_one h2)
  obtain ⟨gramR, c0R, ht⟩ := hc
  refine ⟨gramR, c0R, ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, ht.ok, ht.gramR_eq, ht.mapR, fun j => ?_,
    ht.coefR, fun j t => ?_⟩⟩
  · rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      exact RootUpd.coefMapTie_smul (ht.mapL j) m0
    · rw [Function.update_of_ne hj]
      exact ht.mapL j
  · rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      exact RootUpd.coefTie_smul (ht.coefL j t) a u hu h1 h2
    · rw [Function.update_of_ne hj]
      exact ht.coefL j t

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFamilyCoefficientMapsMulRootOfUnityStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteFamilyCoefficientMaps_mul_rootOfUnity : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (c0L : ∀ i : Fin D.R.m, Formalism.IndefR.FWT.VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W),
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R c0L → ∀ (i : Fin D.R.m) (a : D.what₂.LL) (n : ℕ), n ≠ 0 → a ^ n = 1 →
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R (Function.update c0L i (D.what₂.embLL a • c0L i)) := by
  first | exact @GlobalTheory.Mem.R3.Rw.OmExt.coefFam_update_root | exact GlobalTheory.Mem.R3.Rw.OmExt.coefFam_update_root | (intros; apply GlobalTheory.Mem.R3.Rw.OmExt.coefFam_update_root <;> assumption)
end
end
