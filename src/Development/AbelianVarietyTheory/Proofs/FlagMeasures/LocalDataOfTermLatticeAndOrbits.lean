module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeUnipotentIntegralNormalisedHaar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OverOfIsTermOver
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace GlobalTheory.LocOver.Check

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Mat

end Mat

section Loc

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.NonGenericLocalCheck

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

theorem img_mul' (g h : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * h) Λ = img g (img h Λ) := by
  unfold img; rw [← Submodule.map_comp]; rfl

theorem img_one' (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext x; simp [img]

theorem move_one (t : Term V M r) : move 1 t = t := by
  cases t; simp [move, img_one']

theorem move_mul (g h : V ≃ₗ[E] V) (t : Term V M r) : move (g * h) t = move g (move h t) := by
  simp [move, img_mul']

theorem over_of_isTermOver {H : HermSp M V} (P : FPair H r) (d : Datum P) (t : Term V M r)
    (h : IsTermOver P d t) : Over P d t := by
  refine ⟨1, fun _ _ => rfl, d, ⟨1, one_mem _, ?_, ?_, ?_⟩, by rwa [move_one]⟩
  · intro x y hy; rw [show y = x from Subtype.ext hy]
  · intro x y hy; rw [show y = x from Subtype.ext hy]
  · intro x' y' x y hy' hy; rw [show y = x from Subtype.ext hy, show y' = x' from Subtype.ext hy']

theorem over_move_iff {H : HermSp M V} (P : FPair H r) (d : Datum P) (t : Term V M r) (g : V ≃ₗ[E] V)
    (hg : IsUnitary H g) : Over P d (move g t) ↔ Over P d t := by
  constructor
  · rintro ⟨h, hh, d', hd, ht⟩
    exact ⟨h * g, fun x y => (hh _ _).trans (hg x y), d', hd, by rwa [move_mul]⟩
  · rintro ⟨h, hh, d', hd, ht⟩
    refine ⟨h * g⁻¹, fun x y => (hh _ _).trans ?_, d', hd, ?_⟩
    · rw [← hg]; simp
    · rwa [← move_mul, mul_assoc, inv_mul_cancel, mul_one]

end Loc

section Glob

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs

variable {D : D7}

variable {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

end Glob

end GlobalTheory.LocOver.Check
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDatumOrbitUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDatumOrbitUnique
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical Pointwise

noncomputable section

namespace GlobalTheory.LocOver.OrbitUniq

open GlobalTheory.HL

section Fr

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem change (g : Fin (r + 1) → S.V) (K : Subgroup S.GLV)
    (hon : ∀ n ∈ K, ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      ((∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1) ∧ ∀ j, n (g j) = ∑ i, s i j • g i)
    (σ a b : S.GLV) (ha : a ∈ K) (hb : b ∈ K) (h : ∀ j, σ (a (g j)) = b (g j)) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      ((∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1) ∧ ∀ j, σ (g j) = ∑ i, s i j • g i := by
  obtain ⟨u, hu, hu'⟩ := hon _ (K.mul_mem hb (K.inv_mem ha))
  obtain ⟨w, -, hw⟩ := hon _ (K.inv_mem ha)
  refine ⟨u, hu, fun j => ?_⟩
  rw [← hu' j]
  have e1 : g j = a (a⁻¹ (g j)) := by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  calc σ (g j) = σ (a (∑ i, w i j • g i)) := by rw [← hw j, ← e1]
    _ = ∑ i, w i j • b (g i) := by simp only [map_sum, map_smul, h]
    _ = b (a⁻¹ (g j)) := by rw [hw j, map_sum]; simp only [map_smul]
    _ = (b * a⁻¹) (g j) := rfl

end Fr

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

theorem grp_e {P : FPair H r} {S : Frames M.L r k} (c : Coord P S) (g : V ≃ₗ[E] V) (x : V) :
    c.grp g (c.e x) = c.e (g x) := by
  show c.e (g (c.e.symm (c.e x))) = _
  simp

theorem grp_iso {P : FPair H r} {S : Frames M.L r k} (c : Coord P S) (g : V ≃ₗ[E] V) (hg : IsUnitary H g)
    (x y : S.V) : hf M.L S.Hm (c.grp g x) (c.grp g y) = hf M.L S.Hm x y := by
  obtain ⟨a, rfl⟩ := c.e.surjective x
  obtain ⟨b, rfl⟩ := c.e.surjective y
  have e := fun u v => c.h_eq u v
  simp only [Frames.h] at e
  rw [grp_e, grp_e, e, e, hg]

end GlobalTheory.LocOver.OrbitUniq

namespace GlobalTheory.LocOver

open GlobalTheory.HL GlobalTheory.LocOver.OrbitUniq

theorem orbit_over_unique : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d d' : Datum P) (t : Term V M r), Over P d t → Over P d' t → Datum.Rel d d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hrk hP d d' t h1 h2
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := CoordExist.exists_coord M hM H r k P hrk hP
  have he := (orbit_reps_over M hM H r P).1
  obtain ⟨g1, hg1, d1, hd1, ht1⟩ := h1
  obtain ⟨g2, hg2, d2, hd2, ht2⟩ := h2
  suffices h12 : Datum.Rel d1 d2 from he.trans hd1 (he.trans h12 (he.symm hd2))
  obtain ⟨-, hNA, hNB, -⟩ := CoordUnip.transport M hM H r k P S c
  obtain ⟨-, -, -, hlat, -⟩ := CoordMass.transport M hM H r k P S c
  obtain ⟨-, -, hRel, -⟩ := CoordDatum.transport M hM H r k P S c
  obtain ⟨hT, -, -⟩ := CoordTermWt.terms_correspond M hM H r k P S c
  obtain ⟨-, -, ⟨n1, hn1, hf1, -⟩, ⟨n1', hn1', hf1', -⟩, -⟩ := id ht1
  obtain ⟨-, -, ⟨m, hm, hfm, -⟩, ⟨m', hm', hfm', -⟩, -⟩ := id ht2
  obtain ⟨on1, on2, -⟩ := FrameOnto.unipotent_onto M.L r k S
  set G1 := c.grp g1 with hG1
  set G2 := c.grp g2 with hG2
  set σ : S.GLV := G2 * G1⁻¹ with hσ
  have hσG : ∀ x, σ (G1 x) = G2 x := fun x => by
    show (G2 * G1⁻¹ * G1) x = G2 x
    rw [inv_mul_cancel_right]
  have hσiso : ∀ x y, hf M.L S.Hm (σ x) (σ y) = hf M.L S.Hm x y := by
    intro x y
    obtain ⟨a, rfl⟩ := G1.surjective x
    obtain ⟨b, rfl⟩ := G1.surjective y
    rw [hσG, hσG, grp_iso c g2 hg2, grp_iso c g1 hg1]
  have rA : ∀ j, σ (c.grp n1 (S.f j)) = c.grp m (S.f j) := fun j => by
    have a1 := congrFun hf1 j
    have a2 := congrFun hfm j
    simp only [move] at a1 a2
    rw [c.f_eq, grp_e, grp_e, ← a1, ← a2, ← grp_e c g1, hσG, grp_e]
  have rB : ∀ j, σ (c.grp n1' (S.f' j)) = c.grp m' (S.f' j) := fun j => by
    have a1 := congrFun hf1' j
    have a2 := congrFun hfm' j
    simp only [move] at a1 a2
    rw [c.f'_eq, grp_e, grp_e, ← a1, ← a2, ← grp_e c g1, hσG, grp_e]
  obtain ⟨u, hu, hσf⟩ := change S S.f S.N on1 σ _ _ ((hNA n1).1 hn1) ((hNA m).1 hm) rA
  obtain ⟨u', hu', hσf'⟩ := change S S.f' S.N' on2 σ _ _ ((hNB n1').1 hn1') ((hNB m').1 hm') rB
  have hZ : cT M.L u * S.Zh * u' = S.Zh := by
    ext a b
    rw [← FrameStab.pair_eq S u u' a b, ← hσf, ← hσf', hσiso]
    rfl
  obtain ⟨st, hst, hsf, hsf'⟩ := ((FrameStab.stab_eq M.L r k S).2 u u' hu hu').1 hZ
  set η : S.GLV := st⁻¹ * σ with hη
  have hηf : ∀ j, η (S.f j) = S.f j := fun j => by
    show st⁻¹ (σ (S.f j)) = S.f j
    rw [hσf, ← hsf, ← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have hηf' : ∀ j, η (S.f' j) = S.f' j := fun j => by
    show st⁻¹ (σ (S.f' j)) = S.f' j
    rw [hσf', ← hsf', ← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  have fix : ∀ v ∈ S.ME, η v = v := by
    have : S.ME ≤ LinearMap.eqLocus (η : S.V →ₗ[E] S.V) LinearMap.id := by
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨i, -, rfl⟩
        exact hηf i
      · rintro _ ⟨i, -, rfl⟩
        exact hηf' i
    exact fun v hv => this hv
  have hσI : σ ∈ isomG M.L S.Hm := hσiso
  have hη0 : η ∈ S.H0 := by
    refine ⟨(isomG M.L S.Hm).mul_mem ((isomG M.L S.Hm).inv_mem hst.1.1.1) hσI, fun v => ⟨fun h => ?_, fun h => ?_⟩,
      fun v hv => ?_⟩
    · rwa [η.injective (fix _ h)] at h
    · rw [fix v h]; exact h
    · rw [fix v hv, sub_self]; exact zero_mem _
  have hI1 := (hT d1 _ ht1).1
  have hI2 := (hT d2 _ ht2).1
  have e1 : c.lat (move g1 t).abelian₂ = G1 • c.lat t.abelian₂ := hlat g1 t.abelian₂
  have e2 : c.lat (move g2 t).abelian₂ = G2 • c.lat t.abelian₂ := hlat g2 t.abelian₂
  have hA := (ComplAct.main M.L r k S (c.dat d1) _ hI1 η hη0).1
  have hB := (FrameAct.stabiliser_acts_on_terms M.L r k S _ _ hA st hst).1
  have e3 : st • η • c.lat (move g1 t).abelian₂ = c.lat (move g2 t).abelian₂ := by
    rw [e1, e2, smul_smul, smul_smul, hη, mul_inv_cancel_left, hσ, inv_mul_cancel_right]
  rw [e3] at hB
  have hd := (TermBasic.term_basic M.L r k S (c.dat d2) _ hI2).2.2.2.2.2.2.2 _ hB
  exact (hRel d1 d2).2 ⟨η, hη0, hd⟩

end GlobalTheory.LocOver
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDatumOrbitUniqueStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_datum_orbit_unique : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d d' : Datum P) (t : Term V M r), Over P d t → Over P d' t → Datum.Rel d d' := by
  first | exact @GlobalTheory.LocOver.orbit_over_unique | exact GlobalTheory.LocOver.orbit_over_unique | (intros; apply GlobalTheory.LocOver.orbit_over_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataOfTermLatticeAndOrbits
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.TermLocal

variable {D : D7}

section Tri

theorem tri_map {K W W' : Type} [CommSemiring K] [AddCommMonoid W] [Module K W] [AddCommMonoid W'] [Module K W']
    {n : ℕ} (φ : W →ₗ[K] W') {f g : Fin n → W} (h : GlobalTheory.LocOver.Tri K f g) :
    GlobalTheory.LocOver.Tri K (fun a => φ (f a)) (fun a => φ (g a)) := by
  obtain ⟨A, hA, hc⟩ := h
  refine ⟨A, hA, fun b => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hc b, map_sum, map_smul]

theorem tri_trans {K W : Type} [CommSemiring K] [AddCommMonoid W] [Module K W] {n : ℕ} {f g h : Fin n → W}
    (h1 : GlobalTheory.LocOver.Tri K f g) (h2 : GlobalTheory.LocOver.Tri K g h) : GlobalTheory.LocOver.Tri K f h := by
  obtain ⟨A, ⟨hA1, hA2⟩, hcA⟩ := h1
  obtain ⟨B, ⟨hB1, hB2⟩, hcB⟩ := h2
  refine ⟨A * B, ⟨fun a c hca => ?_, fun a => ?_⟩, fun c => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases lt_or_ge b a with hb | hb
    · rw [hA1 a b hb, zero_mul]
    · rw [hB1 b c (lt_of_lt_of_le hca hb), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA2, hB2, one_mul]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with hb | hb
      · rw [hA1 a b hb, zero_mul]
      · rw [hB1 b a hb, mul_zero]
    · intro hn; exact absurd (Finset.mem_univ a) hn
  · show h c = ∑ a, (A * B) a c • f a
    rw [hcB c]
    simp only [show ∀ b, g b = ∑ a, A a b • f a from hcA, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]

end Tri

theorem isTerm_move {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Formalism.MainNotions.S.Loc.HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Formalism.MainNotions.S.Loc.Term V M r)
    (hg : Formalism.MainNotions.S.LocNG.IsUnitary H g) (ht : H.IsTerm t) : H.IsTerm (GlobalTheory.LocOver.move g t) :=
  GlobalTheory.T.isTerm_localTermMove_of_isometry H g t hg ht

theorem tri_adapt_loc (Z : LocDat D) (p : PlF D) (g : GV D) {T : D.host.E} (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T)
    (g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hg : Adapt g F₁ F₂) (he : Ext p g g') :
    GlobalTheory.LocOver.Tri (D.s.atP p).Ep (GlobalTheory.LocOver.scaled Z p (frame F₂))
      (fun a => g' (GlobalTheory.LocOver.scaled Z p (frame F₁) a)) := by
  obtain ⟨A, ⟨hA1, hA2⟩, hc⟩ := GlobalTheory.Unfold.BasePt.tri_of_adapt g F₁ F₂ hg.1 hg.2
  have hu := fun a => Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a
  refine ⟨fun a b => frFac Z.δ p b * (D.s.atP p).ιE (A a b) * Ring.inverse (frFac Z.δ p a),
    ⟨fun a b hba => ?_, fun a => ?_⟩, fun b => ?_⟩
  · simp [hA1 a b hba]
  · show frFac Z.δ p a * (D.s.atP p).ιE (A a a) * Ring.inverse (frFac Z.δ p a) = 1
    rw [hA2, map_one, mul_one, Ring.mul_inverse_cancel _ (hu a)]
  · have e := hc b
    rw [Formalism.L2.SG.Saturated.frame_mapL] at e
    simp only [GlobalTheory.LocOver.scaled]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, he, e, map_sum]
    simp only [baseChange_smul₂, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc (frFac Z.δ p b * _), Ring.inverse_mul_cancel _ (hu a), mul_one]

theorem isLattice_gmap (g : GV D) (A : LV D) (hA : Submodule.IsLattice D.host.E A) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g A) := by
  refine ⟨hA.fg.map _, ?_⟩
  have : (Formalism.HermitianLatticesTheory.gmap g A : Set (VS D).V) = (g : (VS D).V →ₗ[D.host.E] (VS D).V) '' (A : Set (VS D).V) := rfl
  rw [this]
  intro s hs hli
  let t := g.symm '' s
  have ht : t ⊆ (A : Set (VS D).V) := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hs hy
    simpa [← hzy] using hz
  have heq : (g : (VS D).V →ₗ[D.host.E] (VS D).V) '' t = s := by
    ext x
    simp [t]
  change (g : (VS D).V → (VS D).V) '' t = s at heq
  have hli' : LinearIndepOn (𝓞 D.host.E) id t := by
    apply (linearIndepOn_id_imageₛ_iff (f := g.toLinearMap.restrictScalars (𝓞 D.host.E))
      g.injective.injOn).1
    change LinearIndepOn (𝓞 D.host.E) id ((g : (VS D).V → (VS D).V) '' t)
    rw [heq]
    exact hli
  have hE := hA.linearIndepOn t ht hli'
  have := (linearIndepOn_id_imageₛ_iff (f := g.toLinearMap) g.injective.injOn).2 hE
  change LinearIndepOn D.host.E id ((g : (VS D).V → (VS D).V) '' t) at this
  rwa [heq] at this

theorem finrank_Vp_eq (p : PlF D) : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem local_data_of_term : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → ∃ y : Dat Z FP, LocOver Λ y ∧ ∀ p d, GlobalTheory.LocOver.Over (FP p) d (GlobalTheory.LocOver.locU Z p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) ↔ LocNG.Datum.Rel d (y p) := by
  intro D X Y u u' F F' w hZ hG Z FP hB hRel t Λ hTG
  obtain ⟨hExt, -, hlat, -⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hZ hG Z FP hB hRel
  have hGt : t.G ≠ 0 := (GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hZ hG t Λ hTG).1
  obtain ⟨g, hgF, hgF', hΛ⟩ := hTG
  have hrow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hPD : Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u' t.frame := t.rep.2.2.2.2
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by rwa [Formalism.L2.SG.Pf.SatGram.gterm_G Y t] at hGt
  choose gp hgp using fun p => (hExt g p).exists
  have hu : ∀ p, LocNG.IsUnitary (locH Z p) (gp p) := fun p => GlobalTheory.Unfold.Model.ext_unitary hgF.1 (hgp p)
  have hτ := fun p => GlobalTheory.LocOver.locU_isTerm D Z u u' (X.Fu u) t.lam hrow t.frame hPD hGv p
  have hex : ∀ p, ∃ d, LocNG.IsTermOver (FP p) d
      (GlobalTheory.LocOver.move (gp p) (GlobalTheory.LocOver.locU Z p t.lam (lf D (X.Fu u)) t.frame (Tu D u) (Tu D u'))) := by
    intro p
    refine GlobalTheory.T.exists_datum_of_two_congruent_frames (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (FP p) _
      (isTerm_move (locH Z p) (gp p) _ (hu p) (hτ p).1) (hB p).2.2.1.symm (hB p).2.2.2.symm ?_ ?_
    · rw [(hB p).1]
      exact tri_adapt_loc Z p g _ _ (gp p) hgF (hgp p)
    · rw [(hB p).2.1]
      exact tri_trans (tri_adapt_loc Z p g _ _ (gp p) hgF' (hgp p))
        (tri_map (gp p).toLinearMap (hτ p).2)
  choose y hy using hex
  refine ⟨y, ⟨?_, fun p => ⟨_, hy p, ?_⟩⟩, fun p d => ?_⟩
  · rw [hΛ]; exact isLattice_gmap g _ hrow.1.1.toIsLattice
  · show LocNG.img (gp p) (lattice₂ D Z.M p t.lam) = _
    rw [hΛ, hlat g p (gp p) t.lam (hgp p)]
  · have hDC : Formalism.L2.SG.TermDef.DCRel t.lam (lf D (X.Fu u)) t.frame (Quot.out t.toTerm.cls).1 :=
      (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hrow ⟨t.frame, hPD⟩ (Quot.out t.toTerm.cls)).1
        (Quot.out_eq t.toTerm.cls).symm
    refine (GlobalTheory.T.localData_globalTerm_independent_of_representative D Z u u' (X.Fu u) t.lam hrow t.frame (Quot.out t.toTerm.cls).1 hPD
      (Quot.out t.toTerm.cls).2 hGv hDC p (FP p) (hRel p) d).symm.trans ?_
    refine (GlobalTheory.LocOver.Check.over_move_iff (FP p) d _ (gp p) (hu p)).symm.trans ?_
    constructor
    · intro h
      exact GlobalTheory.T.term_datum_orbit_unique (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq p) (hRel p) d (y p) _ h
        (GlobalTheory.LocOver.Check.over_of_isTermOver _ _ _ (hy p))
    · intro h
      refine ⟨1, fun _ _ => rfl, y p, h, ?_⟩
      rw [GlobalTheory.LocOver.Check.move_one]
      exact hy p

end GlobalTheory.Unfold.TermLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataOfTermLatticeAndOrbitsStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localData_of_term_lattice_and_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → ∃ y : Dat Z FP, LocOver Λ y ∧ ∀ p d, GlobalTheory.LocOver.Over (FP p) d (GlobalTheory.LocOver.locU Z p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) ↔ LocNG.Datum.Rel d (y p) := by
  first | exact @GlobalTheory.Unfold.TermLocal.local_data_of_term | exact GlobalTheory.Unfold.TermLocal.local_data_of_term | (intros; apply GlobalTheory.Unfold.TermLocal.local_data_of_term <;> assumption)
end
