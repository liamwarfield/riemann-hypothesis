module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FourMulRootLt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemSpanOfSemilinear
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB

theorem mem_span_of_semilinear {B K O Kf V W ι : Type*} [CommRing B] [IsDomain B] [IsPrincipalIdealRing B] [Field K]
    [Algebra B K] [IsFractionRing B K] [CommRing O] [Field Kf] [Algebra O Kf]
    [AddCommGroup V] [Module K V] [Module B V] [IsScalarTower B K V]
    [AddCommGroup W] [Module Kf W] [Module O W] [IsScalarTower O Kf W]
    (σ : K →+* Kf) (hσ : ∀ k, σ k ∈ Set.range (algebraMap O Kf) ↔ k ∈ Set.range (algebraMap B K))
    (φ : V →+ W) (hφ : ∀ (a : K) x, φ (a • x) = σ a • φ x) (b : Module.Basis ι K V)
    (hb : LinearIndependent Kf (φ ∘ b)) (S : Set V) (x : V) (hx : φ x ∈ Submodule.span O (φ '' S)) :
    x ∈ Submodule.span B S := by
  classical
  obtain ⟨T, hTS, hxT⟩ := Submodule.mem_span_finite_of_mem_span hx
  obtain ⟨T', hT'S, rfl⟩ := Finset.subset_set_image_iff.1 hTS
  refine Submodule.span_mono hT'S ?_
  set N := Submodule.span B (T' : Set V) with hN
  have : Module.Finite B N := Module.Finite.span_of_finite B T'.finite_toSet
  have : Module.IsTorsionFree B V := Module.IsTorsionFree.trans_faithfulSMul B K V
  have : Module.Free B N := inferInstance
  let e0 := Module.Free.chooseBasis B N
  let e : Module.Free.ChooseBasisIndex B N → V := fun i => (e0 i : V)
  have heB : LinearIndependent B e := e0.linearIndependent.map' N.subtype N.ker_subtype
  have heK : LinearIndependent K e := (LinearIndependent.iff_fractionRing B K).1 heB
  have hspan : N ≤ Submodule.span B (Set.range e) := by
    intro y hy
    have h1 : (⟨y, hy⟩ : N) ∈ Submodule.span B (Set.range e0) := by rw [e0.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := N.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  have hxe : φ x ∈ Submodule.span O (Set.range (φ ∘ e)) := by
    refine (Submodule.span_le.2 ?_) hxT
    rw [Finset.coe_image]
    rintro _ ⟨y, hy, rfl⟩
    have hy' := hspan (Submodule.subset_span hy)
    rw [SetLike.mem_coe]
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add z z' _ _ h h' => rw [map_add (f := _)]; exact Submodule.add_mem _ h h'
    | smul a z _ h =>
      obtain ⟨o, ho⟩ := (hσ (algebraMap B K a)).2 ⟨a, rfl⟩
      rw [← algebraMap_smul K a z, hφ, ← ho, algebraMap_smul]
      exact Submodule.smul_mem _ _ h
  have hxK : x ∈ Submodule.span K (Set.range e) := by
    by_contra hn
    have h1 : LinearIndependent K (fun o => Option.casesOn' o x e) := heK.option hn
    have h2 := FBC.li_of_basis_li σ φ hφ b hb _ h1
    have h3 : (φ ∘ fun o => Option.casesOn' o x e) = fun o => Option.casesOn' o (φ x) (φ ∘ e) := by
      ext o; cases o <;> rfl
    rw [h3, linearIndependent_option'] at h2
    exact h2.2 (Submodule.span_subset_span O Kf _ hxe)
  obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hxK
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hxe
  have hli := FBC.li_of_basis_li σ φ hφ b hb _ heK
  have heq : ∀ i, σ (k i) = algebraMap O Kf (o i) := by
    apply Fintype.linearIndependent_iffₛ.1 hli
    simp only [algebraMap_smul, ho]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hk, map_sum]
    simp [hφ]
  rw [← hk]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨a, ha⟩ := (hσ (k i)).1 ⟨o i, (heq i).symm⟩
  rw [← ha, algebraMap_smul]
  exact Submodule.smul_mem _ _ (e0 i).2

theorem NP_full (D : D7) (L : SizeData₂ D) (X : G.Inst D L) (Y : G.LatInst D) (K : G.Consts) (c : LatCmp D)
    (hv : c.VramDef Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    (∀ x, c.cmp u w hg (D.nuIn u x) ∈ G.NP X Y K u w hg → InLoc (D.plEq w) (DV.MramL D u) x) ∧
      ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ DV.MramL D u, c.cmp u w hg (D.nuIn u (n • x)) ∈ G.NP X Y K u w hg := by
  constructor
  · intro x hx
    have hM : c.cmp u w hg (D.nuIn u x) ∈ (D.gat u w hg).M := by
      obtain ⟨⟨-, F, hF, hFe⟩, -⟩ := hx
      rw [← hFe]
      exact Submodule.smul_mem _ _ hF
    rw [← c.cmp_M u w hg] at hM
    have := D.intW_dvr w
    have := D.intW_frac w
    have h1 : D.nuIn u x ∈ Submodule.span (intW D.what₂.places w) (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V) := by
      refine mem_span_of_semilinear (c.embW u w hg) (fun k => ?_) (c.cmp u w hg) (c.cmp_smul u w hg)
        ((D.fm u).lat 0).b (c.cmp_li u w hg) _ _ hM
      rw [← c.embW_int u w hg k]
      exact ⟨fun h => ⟨⟨k, h⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.2⟩
    obtain ⟨s, hs, hsx⟩ := (D.mem_locW_iff w ((D.fm u).lat 0).L (D.nuIn u x)).1 h1
    refine ⟨s, hs, ?_⟩
    show ((D.nuIn u).restrictScalars (𝓞 D.what₂.LL)) (s • x) ∈ ((D.fm u).lat 0).L
    rw [map_smul]
    exact hsx
  · set a : ℕ := ∑ t0 ∈ G.VV X K (G.aL L) (G.bL L) (D.what₂.places.resChar w),
      ⌈G.Sv X K (G.aL L) (G.bL L) (D.what₂.places.resChar w) t0⌉.toNat with ha
    set b : ℕ := ⌈G.tauP X K (G.aL L) (G.bL L) (D.what₂.places.resChar w)⌉.toNat with hb
    refine ⟨D.what₂.places.resChar w ^ (b + a), pow_ne_zero _ (D.what₂.places.resChar_prime w).ne_zero, fun x hx => ?_⟩
    have hF1 : c.cmp u w hg (D.nuIn u x) ∈ (D.gat u w hg).M := by
      rw [← c.cmp_M u w hg]
      exact Submodule.subset_span ⟨D.nuIn u x, hx, rfl⟩
    have hF2 : c.cmp u w hg (D.nuIn u x) ∈ Y.Vram u w hg := by
      rw [← SetLike.mem_coe, hv u w hg]
      refine Submodule.subset_span ⟨D.nuIn u x, ?_, rfl⟩
      rw [← D.nuIn_range u]
      exact ⟨x, rfl⟩
    rw [map_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul (D.gat u w hg).O, Nat.cast_pow]
    generalize c.cmp u w hg (D.nuIn u x) = F at hF1 hF2
    unfold G.NP
    refine ⟨⟨?_, ?_⟩, Submodule.smul_mem _ _ hF2⟩
    · rw [pow_add, mul_smul]
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨∅, Finset.empty_subset _, F, hF1, ?_⟩
      simp [G.yProd, ha]
    · refine ⟨((D.what₂.places.resChar w : ℕ) : (D.gat u w hg).O) ^ a • F, Submodule.smul_mem _ _ hF1, ?_⟩
      rw [pow_add, mul_smul]
      rfl

end GlobalTheory.EX.OB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosIffSideMemMax
noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

theorem pos_iff_side_mem_max {D : D7} {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) (x : 𝓞 ↥D.LL0)
    (e : ↥D.LL0 →+* FractionRing (D.ntw.O0 (c.twI w)))
    (he : e = if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) :
    0 < D.what₂.places.val w ((x : ↥D.LL0) : D.what₂.LL) ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y = e (x : ↥D.LL0) := by
  have hint : IsIntegral (D.ntw.O0 (c.twI w)) (e (x : ↥D.LL0)) :=
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) e (RingHom.ext_int _ _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = e (x : ↥D.LL0)) ↔ ¬ IsUnit y := by
    refine ⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩
    rw [← IsFractionRing.injective _ _ (h2.trans hy.symm)]
    exact h1
  have e1 := h.embedding_baseField_condition w x y 1 one_ne_zero (by rw [← he, map_one, mul_one, hy])
  simp only [map_one, mul_one] at e1
  rw [hleft, GlobalTheory.TwistGoodCompare.pos_iff_not_isUnit c w _ _ e1, not_iff_not]
  exact ⟨GlobalTheory.TwistGoodCompare.isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩

theorem resChar_eq_of_pos {D : D7} (w : D.what₂.places.Pl) {p : ℕ} (hp : p.Prime)
    (h : 0 < D.what₂.places.val w ((p : ℕ) : D.what₂.LL)) : D.what₂.places.resChar w = p := by
  by_contra hne
  have hq := D.what₂.places.resChar_prime w
  have hq0 : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
    rw [D.what₂.places.val_resChar w]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  have hnat : ∀ n : ℕ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (D.what₂.places.val w).map_le_add ih (by simp)
  have hint : ∀ n : ℤ, 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simpa using hnat m
    · rw [Int.cast_neg, AddValuation.map_neg]; simpa using hnat m
  have h1 : (a : D.what₂.LL) * ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) + (b : D.what₂.LL) * ((p : ℕ) : D.what₂.LL) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → D.what₂.LL) hab
  have h2 : 0 < D.what₂.places.val w 1 := by
    rw [← h1]
    refine (D.what₂.places.val w).map_lt_add ?_ ?_
    · rw [AddValuation.map_mul]; exact hq0.trans_le (le_add_of_nonneg_left (hint a))
    · rw [AddValuation.map_mul]; exact h.trans_le (le_add_of_nonneg_left (hint b))
  simp at h2

theorem twCoverPair_of_tie (D : D7) (c : NChoice D) (h : NChTie D c) : TwCoverPair D := by
  rintro p hp w hw ⟨w', -, hw'⟩
  refine ⟨c.twI w', ?_, ?_⟩
  · rw [c.twI_l]
    refine resChar_eq_of_pos w' hp ?_
    simpa using (hw' _).1 hw
  · cases hs : c.sd w'
    · exact Or.inr fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_neg (by simp)]))
    · exact Or.inl fun x => (hw' x).trans (pos_iff_side_mem_max h w' x _ (by rw [hs, if_pos rfl]))

end GlobalTheory.Mem.Top

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.LayOfCore

variable {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B}

theorem ties (c : V4.Core K X f T) : Formalism.BasicNotions.Ties X.toD7 :=
  ⟨c.real.cdScale, c.real.dsig_all, c.row.bu_def, twCoverPair_of_tie _ _ c.nch_tie, X.B.coeffGaloisSubfield_isGalois, c.row.ft_occ⟩

theorem dgam (c : V4.Core K X f T) : DGamDef X.toD7 := fun u μ =>
  ⟨fun u' μ' i hi x => by
    rw [c.col.one u μ, ← c.col.one u' μ']
    exact (X.toD7.chTw u' μ').dvd_DGam i hi x, c.col.one u μ⟩

noncomputable def lay (c : V4.Core K X f T) (hv : StandardLattice.VolumeEqMass₂ X.toD7) : Lay X.toD7 :=
  { c.O with
    ties := ties c
    rrDef := c.row.rrDef
    th_io := c.th_io
    vram := c.gy.vram
    fills_all := c.gy.fills
    idx := c.row.idx
    kap_def := c.row.kap_def
    lam_def := c.row.lam_def
    kapR_def := c.row.kapR_def
    piG_lev := c.col.piG_lev
    piT_lev := c.col.piT_lev
    seen := c.col.seen
    tauOf := c.col.tauOf
    dgam := dgam c
    nch_tie := c.nch_tie
    rationalRoots_def := c.row.rationalRoots_def
    duStar_def := (sizes_eq_count K X c.isOver hv c.dsig_eq).1
    Dstar_def := (sizes_eq_count K X c.isOver hv c.dsig_eq).2
    gauge_def := c.gauge_def }

theorem layObj_lay (c : V4.Core K X f T) (hv : StandardLattice.VolumeEqMass₂ X.toD7) : layObj (lay c hv) = c.O := rfl

theorem isOver (c : V4.Core K X f T) : Over X.toD7 K.P K.Lv := by
  obtain ⟨sp, hT, hY, hA, hV, hz, h, -⟩ := c.isOver
  exact ⟨sp, hT, hY, hA, hV, hz, X, h, rfl⟩

theorem untw (c : V4.Core K X f T) (w : X.toD7.what₂.places.Pl) (hw : X.toD7.what₂.muAt w = X.toD7.what₂.mu0) (j : ℕ)
    (h1 : 1 ≤ j) (h2 : j ≤ X.toD7.R.m) : X.toD7.what₂.Aj j w = 0 := by
  have a := c.row.untw w hw j h1 h2
  have b := c.row.untw (X.toD7.what₂.places.conj w) ((X.toD7.what₂.muAt_conj w).trans hw) j h1 h2
  unfold Rows.Data.Aj
  rw [hw, a.1, a.2, b.1]
  rfl

theorem fin (c : V4.Core K X f T) : {w | X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0}.Finite :=
  (TwFin.tw_fin X.B f T).2.2.2.subset fun w hw => c.mu.sub w (by_contra fun h => hw (c.mu.off w h))

theorem ledOK (c : V4.Core K X f T) (hv : StandardLattice.VolumeEqMass₂ X.toD7) : LedOK K.s K.C K.cD K.ch (lay c hv) K.a K.b := by
  intro L hs hW hV
  refine ⟨fun w hw j hj => ?_, fun I hI he hk hf => ⟨c.gy.led L hs hW hV I hI he hk hf, fun u w hg => ?_, fun u w hg _ =>
    NP_full X.toD7 L I c.O.Gy K.C.GK c.O.cmp c.gy.vram u w hg⟩⟩
  · refine c.fval L hs hW hV w (fun h => (TwFin.tw_fin X.B f T).2.1 w ?_) j hj
    rw [← c.mu.tw w, ← c.mu.on w h]
    exact (congrArg c.xi hw).trans c.mu.mu0
  · have hC : K.C.cX.Ce = 1 := by
      have := K.std.1
      unfold FC.Fixed at this
      tauto
    rw [(c.gatNum u w hg).2, he, hC, hs]

theorem tupUsed (c : V4.Core K X f T) : DQ.TupUsedAt X.toD7 := by
  intro μ
  have hμ : c.xi μ ∈ T.set f := c.mu.range ▸ Set.mem_range_self μ
  rcases hμ with (h | h | h) | ⟨w, h⟩
  · exact .inl (c.mu.inj (h.trans c.mu.mu0.symm))
  · exact .inr (.inl (c.mu.inj (h.trans c.mu.star.symm)))
  · exact .inr (.inr (.inl (c.mu.inj (h.trans c.mu.star'.symm))))
  · by_cases hw : w ∈ c.Wt
    · exact .inr (.inr (.inr ⟨w, (c.mu.inj (h.symm.trans (c.mu.tw w).symm)).trans (c.mu.on w hw).symm⟩))
    · unfold TwDat.xiTw at h
      rw [c.mu.supp w hw, mul_one] at h
      split_ifs at h
      · exact .inr (.inr (.inl (c.mu.inj (h.symm.trans c.mu.star'.symm))))
      · exact .inr (.inl (c.mu.inj (h.symm.trans c.mu.star.symm)))

theorem ev_imp {p q : Ctx → Prop} (hp : Ev p) (h : ∀ K, p K → q K) : Ev q := by
  obtain ⟨ε0, h0, H⟩ := hp
  refine ⟨ε0, h0, fun eps C8 a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, H⟩ := H eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, H⟩ := H C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, H⟩ := H cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H⟩ := H ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 => h K (H K d1 d2 d3 d4 d5)⟩

theorem lay_of_core : Ev fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T),
    StandardLattice.VolumeEqMass₂ X.toD7 → ∃ Y : Lay X.toD7, layObj Y = c.O ∧ Over X.toD7 K.P K.Lv ∧ RecOK K.s K.C K.cD X.toD7 ∧
      LedOK K.s K.C K.cD K.ch Y K.a K.b ∧ DQ.TupUsedAt X.toD7 :=
  ev_imp TamePow.tame_of_pow fun _ hK X _ _ c hv =>
    ⟨lay c hv, layObj_lay c hv, isOver c,
      ⟨c.del, c.etaF, untw c, fin c, (Full.dgam_pos_and_full X.toD7).1, (Full.dgam_pos_and_full X.toD7).2,
        hK X c.isOver c.chiT, c.col.mink, c.col.atT⟩, ledOK c hv, tupUsed c⟩

end GlobalTheory.Mem.Top.LayOfCore
