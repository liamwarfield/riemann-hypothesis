module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameVal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isAffineOpen_nonzeroLocus_of_universallyClosed {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y]
    [UniversallyClosed f] {H : LB X} {κ : Type} [Finite κ] (s : κ → H.Sec) (hcov : ⨆ j, nonzeroLocus (s j) = ⊤)
    (haff : ∀ j, IsAffineOpen (nonzeroLocus (s j))) (t : H.Sec) : IsAffineOpen (nonzeroLocus t) := by
  classical
  have := Fintype.ofFinite κ
  choose r hr using fun j => AmpleSpan.exists_isRatio (s j) t
  choose σ hσ using fun j => AmpleSpan.exists_isRatio t (s j)
  have top := AmpleSpan.ker_sup_span_eq_top f s s hcov (fun j l => if l = j then 1 else 0)
    (fun j k => by simp [apply_ite]) t (AmpleSpan.isCompact_nonzeroLocus s hcov haff t) r hr
  refine isAffineOpen_of_isAffineOpen_basicOpen _ (Set.range r) ?_ ?_
  · have e := congrArg (Ideal.map (MvPolynomial.eval₂Hom (f.appLE ⊤ (nonzeroLocus t) le_top).hom r)) top
    rw [Ideal.map_sup, Ideal.map_top, Ideal.map_span, ← Set.range_comp,
      (Ideal.map_eq_bot_iff_le_ker _).2 le_rfl, bot_sup_eq] at e
    convert e using 3
    funext j
    simp [apply_ite]
  · rintro _ ⟨j, rfl⟩
    rw [(hr j).basicOpen, inf_comm, ← (hσ j).basicOpen]
    exact (haff j).basicOpen _

theorem IsAmpleLB.isAffineOpen_nonzeroLocus {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffine Y] [UniversallyClosed f]
    {L : LB X} (h : IsAmpleLB L) {n : ℕ} (hn : 1 ≤ n) (s : (lbPow L n).Sec) : IsAffineOpen (nonzeroLocus s) := by
  obtain ⟨N, hN, H⟩ := h.exists_cover_mul
  obtain ⟨M, u, hu, ha⟩ := H n hn
  have := isAffineOpen_nonzeroLocus_of_universallyClosed f u hu ha (secCast (Nat.mul_comm n N) (secPow s N))
  rwa [nonzeroLocus_secCast, nonzeroLocus_secPow s hN] at this

theorem isAffineOpen_nonzeroLocus_of_relAmple : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] (L : LB X.left), L.IsLB → RelAmple X L → ∀ (n : ℕ), 1 ≤ n → (∀ s : H0 L n, IsAffineOpen (nonzeroLocus s)) ∧ ∃ (m : ℕ) (_ : 1 ≤ m) (M : ℕ) (t : Fin M → H0 L (n * m)), ⨆ i, nonzeroLocus (t i) = ⊤ := by
  intro R _ X _ L hL hA n hn
  have h := isAmpleLB_of_relAmple_of_isAffine X hL hA
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨s', hs, -⟩ : ∃ s' : (lbPow L n).Sec, nonzeroLocus s' = nonzeroLocus s ∧ _ :=
      exists_sec_oneTerm L (K' := PUnit) rfl s
    exact hs ▸ h.isAffineOpen_nonzeroLocus X.hom hn s'
  · obtain ⟨N, hN, H⟩ := h.exists_cover_mul
    obtain ⟨M, u, hu, -⟩ := H n hn
    choose t ht using fun i => exists_sec_oneTerm L (K' := Fin 1) (e' := ((n * N : ℕ) : ℤ))
      (by rw [Nat.mul_comm]) (u i)
    exact ⟨N, hN, M + 1, t, (iSup_congr fun i => (ht i).1).trans hu⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroClosedFibre
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpreadSec

variable {X X' : Scheme.{0}}

theorem exists_pull {M : LB X} (s : LB.Sec M) (π : X' ⟶ X) :
    ∃ t : LB.Sec (M.pull π), ∀ (j : (M.pull π).ι) (z : X'), π z ∈ M.U (j PUnit.unit) →
      gs (𝟙 X') z _ (t.f j) = gs π z _ (s.f (j PUnit.unit)) := by
  let a : ∀ j : (M.pull π).ι, Γ(X', (M.pull π).U j) := fun j =>
    rs X' (LB.wchart_le M (fun _ : PUnit => π) j PUnit.unit) ((π.app _).hom (s.f (j PUnit.unit)))
  have ha : ∀ (j : (M.pull π).ι) (z : X'), π z ∈ M.U (j PUnit.unit) →
      gs (𝟙 X') z _ (a j) = gs π z _ (s.f (j PUnit.unit)) := fun j z hz => by
    have hm : (𝟙 X' : X' ⟶ X') z ∈ (M.pull π).U j := Set.mem_iInter.2 fun _ => hz
    refine (gs_res (𝟙 X') z _ hm _).trans ?_
    rw [gs_pull (𝟙 X') π z _ hz, Category.id_comp]
  refine ⟨⟨a, fun i j => fn_ext fun z hz => ?_⟩, ha⟩
  have hi : π z ∈ M.U (i PUnit.unit) := Set.mem_iInter.1 hz.1 PUnit.unit
  have hj : π z ∈ M.U (j PUnit.unit) := Set.mem_iInter.1 hz.2 PUnit.unit
  refine ((gs_res (𝟙 X') z _ hz _).trans (ha i z hi)).trans (Eq.trans ?_ ((gs_mul (𝟙 X') z _ hz _ _).trans
    (congrArg₂ (· * ·) ((gs_unit (𝟙 X') z _ hz _).trans
      (congrArg Units.val (gm_linComb M _ _ (𝟙 X') z i j hz.1 hz.2))) ((gs_res (𝟙 X') z _ hz _).trans
        (ha j z hj)))).symm)
  rw [FlatSec.gs_sec_trans s π z hi hj, Fintype.prod_unique, zpow_one, Category.id_comp]

theorem app_eq_zero {M : LB X} {π : X' ⟶ X} (h : ∀ (t : LB.Sec (M.pull π)) j, t.f j = 0) (s : LB.Sec M) (k : M.ι) :
    (π.app _).hom (s.f k) = 0 := by
  obtain ⟨t, ht⟩ := exists_pull s π
  refine fn_ext fun z hz => ?_
  have hz' : π z ∈ M.U k := hz
  rw [gs_pull (𝟙 X') π z _ hz', Category.id_comp, ← ht (fun _ => k) z hz',
    LBGerm.gs_zero (𝟙 X') z _ hz]
  refine (congrArg (gs (𝟙 X') z _) (h t fun _ => k)).trans ?_
  exact LBGerm.gs_zero (𝟙 X') z _ (Set.mem_iInter.2 fun _ => hz')

theorem exists_ne_zero_closed_fibre : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] [GeometricallyConnected G.hom] (N : LB G.left), N.IsLB → (∃ s : LB.Sec (N.pull (pullback.fst G.hom (jK V))), (∃ j, s.f j ≠ 0)) → ∃ s : LB.Sec (N.pull (fstG (IsLocalRing.maximalIdeal V) 0 G).left), (∃ j, s.f j ≠ 0) := by
  intro V _ _ _ G _ _ _ _ _ N hN ⟨s, j, hj⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have h0 : ∀ σ : LB.Sec N, ∃ τ : LB.Sec N, DVR.SecIsMul G.hom (ϖ ^ (0 + 1)) σ τ := fun σ =>
    (ThickDiv.main V ϖ hϖ G N σ 0).1 (app_eq_zero hcon σ)
  have h1 : ∀ (n : ℕ) (σ : LB.Sec N), ∃ τ : LB.Sec N, DVR.SecIsMul G.hom (ϖ ^ (n + 1)) σ τ := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      intro σ
      obtain ⟨τ, hτ⟩ := ih σ
      obtain ⟨ρ, hρ⟩ := h0 τ
      refine ⟨ρ, fun k => ?_⟩
      have e₁ : σ.f k = AbLaw.cst G.hom _ (ϖ ^ (n + 1)) * τ.f k := hτ k
      have e₂ : τ.f k = AbLaw.cst G.hom _ (ϖ ^ (0 + 1)) * ρ.f k := hρ k
      change σ.f k = AbLaw.cst G.hom _ (ϖ ^ (n + 1 + 1)) * ρ.f k
      rw [e₁, e₂, ← _root_.mul_assoc, ← map_mul, ← pow_add]
  have h2 : ∀ (σ : LB.Sec N) k, σ.f k = 0 := fun σ =>
    (sec_eq_zero_and_hom_eq_of_thickenings V (IsLocalRing.maximalIdeal V)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge G).1 N hN σ fun n =>
        (ThickDiv.main V ϖ hϖ G N σ n).2 (h1 n σ)
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  obtain ⟨n, c, u, hu⟩ := FlatSec.exists_comb_of_flat V (FractionRing V) (algebraMap V _)
    (RingHom.flat_algebraMap_iff.2 inferInstance) G.left G.hom _ _ _
    (IsPullback.of_hasPullback G.hom (jK V)) N hN s
  refine hj (fn_ext fun z hz => ?_)
  have hz' : pullback.fst G.hom (jK V) z ∈ N.U (j PUnit.unit) := Set.mem_iInter.1 hz PUnit.unit
  rw [LBGerm.gs_zero _ z _ hz]
  refine (hu z (j PUnit.unit) hz').trans (Finset.sum_eq_zero fun i _ => ?_)
  rw [h2, LBGerm.gs_zero _ z _ hz', mul_zero]

end GlobalTheory.SpreadSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecTwist
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.PullPair

open LBGerm GlobalTheory.AbLaw

def chartPullTw {X : Scheme.{0}} (L : LB X) (f : X ⟶ X) (e : ℤ) (n t : ℕ) :
    ChartPull (LB.LinComb L (K := Fin 2) ![f, 𝟙 X] ![e, ((n * t : ℕ) : ℤ)])
      (tw (LB.LinComb L (fun _ : PUnit => f) (fun _ => e)) (lbPow L n) t) (𝟙 X) where
  idx J := (fun _ => J 0, fun _ => J 1)
  le J y hy := ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0, Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1⟩
  g y J J' hJ hJ' := by
    have a₀ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : PUnit => f) (fun _ => J 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ 0
    have a₁ : (𝟙 X : X ⟶ X) y ∈ powChart L (fun _ => J 1) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ 1
    have b₀ : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : PUnit => f) (fun _ => J' 0) :=
      Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ' 0
    have b₁ : (𝟙 X : X ⟶ X) y ∈ powChart L (fun _ => J' 1) := Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hJ' 1
    refine (gm_linComb L _ _ (𝟙 X) y J J' hJ hJ').trans (Units.ext (Eq.symm ?_))
    refine (TwistGen.gm_tw_g (LB.LinComb L (fun _ : PUnit => f) (fun _ => e)) (lbPow L n) t y
      (fun _ => J 0, fun _ => J 1) (fun _ => J' 0, fun _ => J' 1) ⟨a₀, a₁⟩ ⟨b₀, b₁⟩).trans ?_
    rw [gm_lbPow_g n (𝟙 X) y _ _ a₁ b₁, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    refine congrArg Units.val ((congrArg (· * _) (gm_linComb L _ _ (𝟙 X) y _ _ a₀ b₀)).trans ?_)
    rw [Fintype.prod_unique, Fin.prod_univ_two, ← pow_mul, ← zpow_natCast]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp]

theorem exists_sec_twist {X : Scheme.{0}} {L : LB X} (h : IsAmpleLB L) (f : X ⟶ X) (e : ℤ) (k : ℕ) (hk : 1 ≤ k)
    (y : X) : ∃ n, 1 ≤ n ∧ ∃ u : LB.Sec (LB.LinComb L (K := Fin 2) ![f, 𝟙 X] ![e, ((k * n : ℕ) : ℤ)]),
      y ∈ nonzeroLocus u := by
  have hLB := h.isLB
  obtain ⟨n, hn, hc⟩ := h.exists_cover_mul
  obtain ⟨N, s, hs, ha⟩ := hc k hk
  have : CompactSpace X := h.compactSpace
  have : QuasiSeparatedSpace X := h.quasiSeparatedSpace
  obtain ⟨i, hi⟩ : ∃ i, y ∈ nonzeroLocus (s i) := by
    have hy : y ∈ (⨆ i, nonzeroLocus (s i)) := hs ▸ trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using hy
  have hM := LB.isLB_linComb hLB (fun _ : PUnit => f) (fun _ => e)
  have hH := isLB_lbPow hLB (n * k)
  obtain ⟨V, N', hyV, hV⟩ := GlobalTheory.TwistGen.exists_nhds hM hH (s i) (ha i) y hi
  obtain ⟨u, hu⟩ := hV 1
  have hmul : n * k * (N' + 1) = k * (n * (N' + 1)) := by ring
  refine ⟨n * (N' + 1), Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩
  rw [← hmul]
  refine ⟨chartSec (chartPullTw L f e (n * k) (N' + 1)) u, ?_⟩
  rw [nonzeroLocus_chartSec_id]
  · exact hu hyV
  · intro z j hj
    refine ⟨![j.1 PUnit.unit, j.2 PUnit.unit], Set.mem_iInter.2 fun m => ?_⟩
    fin_cases m
    · exact Set.mem_iInter.1 hj.1 PUnit.unit
    · exact Set.mem_iInter.1 hj.2 PUnit.unit

theorem exists_cross : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (a : A.A ⟶ A.A), IsMonHom a → ∀ (j k : ℕ), 1 ≤ k → ∃ n, 1 ≤ n ∧ ∀ t₁ t₂ : SecA A F j, ∃ t₁' t₂' : SecA A F (k * n), Cross a t₁ t₂ t₁' t₂' ∧ ((∀ z J, Good A.L z J → sA t₂ (ptSecT A.A 1).left z J ≠ 0) → (∀ z J, Good A.L z J → sA t₂' (ptSecT A.A 1).left z J ≠ 0)) := by
  intro _ R _ _ A F _ _ a ha j k hk
  have hamp : IsAmpleLB A.L := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A.A A.isLB A.ample
  have hUq : Unique (TFK (R := R) F).left := by
    unfold TFK
    exact inferInstanceAs (Unique (Spec (CommRingCat.of F)))
  obtain ⟨n, hn, u, hu⟩ := PullPair.exists_sec_twist hamp a.left (-(j : ℤ)) k hk
    ((1 : TFK (R := R) F ⟶ A.A).left default)
  have hασ : ((TFK (R := R) F) ◁ a).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) A.A).left ≫ a.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  have hF : FormEq (Sum.elim (fun m => (snd (TFK (R := R) F) A.A).left ≫ (![a.left, 𝟙 A.A.left] : Fin 2 → _) m)
      (fun _ : Fin 1 => ((TFK (R := R) F) ◁ a).left ≫ (snd (TFK (R := R) F) A.A).left))
      (Sum.elim (![-(j : ℤ), ((k * n : ℕ) : ℤ)] : Fin 2 → ℤ) (fun _ : Fin 1 => (j : ℤ)))
      (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (fun _ => ((k * n : ℕ) : ℤ)) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, hασ]
    rw [mul_right_comm, ← zpow_add, neg_add_cancel, zpow_zero, _root_.one_mul]
  refine ⟨n, hn, fun (t₁ t₂ : LB.Sec (LB.LinComb A.L (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left)
    (fun _ => (j : ℤ)))) => ?_⟩
  obtain ⟨s₁, hs₁⟩ := exists_sec A.isLB hF
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec u (snd (TFK (R := R) F) A.A).left)
      (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec t₁ ((TFK (R := R) F) ◁ a).left))
  obtain ⟨s₂, hs₂⟩ := exists_sec A.isLB hF
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec u (snd (TFK (R := R) F) A.A).left)
      (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec t₂ ((TFK (R := R) F) ◁ a).left))
  refine ⟨s₁, s₂, ?_, ?_⟩
  · intro z J hJ
    unfold sA
    rw [hs₁ _ _ z J hJ, hs₂ _ _ z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ,
      ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ,
      ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
    simp only [Category.id_comp]
    ring
  · intro hne z J hJ
    have hr : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ ((TFK (R := R) F) ◁ a).left =
        (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left := by
      rw [← Over.comp_left]
      unfold ptSecT
      rw [lift_whiskerLeft, MonObj.one_comp]
    have hs : (ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left =
        (1 : TFK (R := R) F ⟶ A.A).left := by
      rw [← Over.comp_left]
      unfold ptSecT
      rw [lift_snd]
    have hne' := hne z J hJ
    unfold sA at hne' ⊢
    rw [hs₂ _ _ z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ,
      ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, hr]
    have hmem : ((ptSecT A.A (1 : TFK (R := R) F ⟶ A.A)).left ≫ (snd (TFK (R := R) F) A.A).left) z ∈
        nonzeroLocus u := by
      rw [hs, Subsingleton.elim z default]
      exact hu
    unfold nonzeroLocus at hmem
    obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).1 hmem
    have hunit := ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.isUnit_sval u _ z hJ i hi
    exact fun h0 => hne' ((hunit.mul_right_eq_zero).1 h0)

end GlobalTheory.PullPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPointEqOfIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sabMap_of_iso (hG : GlobalFnsSt) {S S' : Scheme.{0}} {t t' : SAB H S} {u u' : SAB H S'} {f : S' ⟶ S}
    (n : SABMap u t f) (n' : SABMap u' t' f) (hA : IsAbelianScheme u.G) (ψ : t.G ≅ t'.G) [IsMonHom ψ.hom]
    (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ t'.act.act x) (hL : LBIso t.PP.L (t'.PP.L.pull ψ.hom.left)) :
    ∃ m : SABMap u u' (𝟙 _), m.φ ≫ n'.φ = n.φ ≫ ψ.hom.left := by
  have c := n.cart.comp (isGrpPullback_of_iso ψ)
  rw [Category.comp_id] at c
  obtain ⟨α, hα, hφ⟩ := grpPullback_iso c n'.cart
  have ha : ∀ x, (u.act.act x).left ≫ α.hom.left = α.hom.left ≫ (u'.act.act x).left := fun x => by
    have e : (t.act.act x).left ≫ ψ.hom.left = ψ.hom.left ≫ (t'.act.act x).left := congrArg (fun q => q.left) (hact x)
    apply n'.cart.1.hom_ext
    · rw [Category.assoc, hφ, Category.assoc, n'.act, ← Category.assoc, n.act, ← Category.assoc, hφ, Category.assoc,
        Category.assoc, e]
    · simp only [Category.assoc, Over.w]
  have hb : LBIso u.PP.L (u'.PP.L.pull α.hom.left) := by
    obtain ⟨w, hw⟩ := hL
    obtain ⟨w₁, g₁, -⟩ := (isPullCubical_iff n.cm t.cub u.cub).1 n.lin
    obtain ⟨w₂, g₂, -⟩ := (isPullCubical_iff n'.cm t'.cub u'.cub).1 n'.lin
    have hw' := (isGen_iff w).1 hw
    obtain ⟨w₃, T⟩ := exists_comp t.PP.isLB w w₁ hw' g₁ t'.PP.isLB u.PP.isLB
    obtain ⟨w₄, g₄⟩ : ∃ w₄ : LB.Iso u.PP.L (t'.PP.L.pull (α.hom.left ≫ n'.cm.F)), PGen w₄ := by
      rw [hφ]; exact ⟨w₃, T.pgen_comp t.PP.isLB hw' g₁⟩
    obtain ⟨w₅, T'⟩ := exists_cancel t'.PP.isLB w₂ w₄ g₂ g₄ u'.PP.isLB u.PP.isLB
    exact ⟨w₅, (isGen_iff w₅).2 (T'.pgen_cancel t'.PP.isLB g₂ g₄)⟩
  exact ⟨⟨CubeMap.ofHom α.hom, isGrpPullback_of_iso α, rfl, ha,
    HeckePoint.isPullCubical_of_iso hG hA α.hom u.cub u'.cub hb⟩, hφ⟩

theorem exists_sab_fac {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : h = g ≫ f) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact ObjMaps.exists_sab_cancel m n

variable {D : Datum H} {l : Level H}

theorem objMap_eq (hS : SerreSt) {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {F : Type} [Field F]
    {s : S ⟶ Sp B} {s' : Sp F ⟶ Sp B} {o : Obj D l b s} {o₁ : Obj D l b s'} {y y' : Sp F ⟶ S} (e : y = y')
    (m : ObjMap o₁ o y) (m' : ObjMap o₁ o y') : m.toSABMap.φ = m'.toSABMap.φ := by
  subst e
  exact objMap_unique_of_field hS m m'

theorem point_eq (hL : Laws) {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'} {S : Scheme.{0}} {χ : S ⟶ Y.X}
    {χ' : S ⟶ Y'.X} {t t' : SAB H S} (m : SABMap t Y.t χ) (m' : SABMap t' Y'.t χ') (ψ : t.G ≅ t'.G) [IsMonHom ψ.hom]
    (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ t'.act.act x) (hb : LBIso t.PP.L (t'.PP.L.pull ψ.hom.left))
    {K : Type} [Field K] (j : Sp K ⟶ S) (y y' : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = j ≫ χ) (hy' : y' ≫ Y'.j = j ≫ χ')
    (hs : y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _)
    (hlev : ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G),
      ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) →
      ∀ g : Sp K ⟶ t.G.left, g ≫ t.G.hom = j → g ≫ m.φ = y ≫ σ.left ≫ Y.m.φ →
        g ≫ ψ.hom.left ≫ m'.φ = y' ≫ σ'.left ≫ Y'.m.φ) :
    y = y' ∧ ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left) (τ : T ⟶ Sp K),
      g ≫ t.G.hom = τ ≫ j → g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g ≫ m.φ = g₁ ≫ Y.m.φ →
      g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
      g ≫ ψ.hom.left ≫ m'.φ = g₂ ≫ Y'.m.φ := by
  have hid : spMap (RingHom.id (KA l)) = 𝟙 _ := Spec.map_id _
  have hs' : y' ≫ pullback.fst _ _ ≫ Xo.s = y ≫ pullback.fst _ _ ≫ Xo.s := by
    rw [pullback.condition, reassoc_of% hs]
  obtain ⟨o, ⟨m₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ (y ≫ pullback.fst _ _ ≫ Xo.s) y
    rfl rfl (by rw [hid, Category.comp_id]) Y.oF
  obtain ⟨o', ⟨m₂⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ (y ≫ pullback.fst _ _ ≫ Xo.s) y'
    rfl rfl (by rw [hid, Category.comp_id, hs']) Y'.oF
  obtain ⟨k₁, e₁⟩ := ObjMaps.exists_sab_comp Y.m m₁.toSABMap
  obtain ⟨k₂, e₂⟩ := ObjMaps.exists_sab_comp Y'.m m₂.toSABMap
  obtain ⟨n, hn⟩ := exists_sab_fac m k₁ hy
  obtain ⟨n', hn'⟩ := exists_sab_fac m' k₂ hy'
  obtain ⟨ν, hν⟩ := exists_sabMap_of_iso hL.globalFns n n'
    ⟨inferInstance, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩ ψ hact hb
  have hνw : ν.φ ≫ o'.t.G.hom = o.t.G.hom := ν.cart.1.w.trans (Category.comp_id _)
  have hψ : n.φ ≫ ψ.hom.left ≫ m'.φ = ν.φ ≫ m₂.toSABMap.φ ≫ Y'.m.φ := by
    rw [← e₂, hn', reassoc_of% hν]
  have key : ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G)
      (x : 𝟙_ (Over (Sp K)) ⟶ o.t.G) (x' : 𝟙_ (Over (Sp K)) ⟶ o'.t.G),
      ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) →
      x.left ≫ m₁.toSABMap.φ = y ≫ σ.left → x'.left ≫ m₂.toSABMap.φ = y' ≫ σ'.left →
      x.left ≫ ν.φ = 𝟙 _ ≫ x'.left := by
    intro σ σ' x x' h hx hx'
    have b : x.left ≫ o.t.G.hom = 𝟙 _ := Over.w x
    have b' : x'.left ≫ o'.t.G.hom = 𝟙 _ := Over.w x'
    have q := hlev σ σ' h (x.left ≫ n.φ) (by rw [Category.assoc, n.cart.1.w, reassoc_of% b])
      (by rw [Category.assoc, ← hn, e₁, reassoc_of% hx])
    rw [Category.id_comp]
    apply k₂.cart.1.hom_ext
    · show (_ ≫ _) ≫ k₂.φ = _ ≫ k₂.φ
      rw [e₂, Category.assoc, ← hψ, reassoc_of% hx', ← q, Category.assoc]
    · rw [Category.assoc, hνw, b, b']
  let ν' : ObjMap o o' (𝟙 _) :=
    ⟨ν, fun a => key _ _ _ _ (Or.inr ⟨a, rfl, rfl⟩) (m₁.eta a) (m₂.eta a),
      fun a => key _ _ _ _ (Or.inl ⟨a, rfl, rfl⟩) (m₁.etaA a) (m₂.etaA a)⟩
  obtain ⟨p₁, f₁⟩ := ObjComp.objMap_comp Y.m0 m₁
  obtain ⟨p₀, f₀⟩ := ObjComp.objMap_comp m₂ ν'
  obtain ⟨p₂, f₂⟩ := ObjComp.objMap_comp Y'.m0 p₀
  have hf := (Xo.rep _ _ inferInstance o).unique ⟨Category.assoc _ _ _, ⟨p₁⟩⟩
    ⟨by rw [Category.id_comp, Category.assoc, hs'], ⟨p₂⟩⟩
  have hp : m₁.toSABMap.φ ≫ Y.m0.toSABMap.φ = (ν.φ ≫ m₂.toSABMap.φ) ≫ Y'.m0.toSABMap.φ :=
    f₁.symm.trans ((objMap_eq hL.serre hf p₁ p₂).trans (f₂.trans (congrArg (· ≫ _) f₀)))
  rw [Category.id_comp] at hf
  obtain rfl : y = y' := pullback.hom_ext hf hs
  refine ⟨rfl, fun T g g₁ g₂ τ h₁ h₂ h₃ h₄ h₅ => ?_⟩
  obtain ⟨u, u₁, u₂⟩ : ∃ u : T ⟶ o.t.G.left, u ≫ m₁.toSABMap.φ = g₁ ∧ u ≫ o.t.G.hom = τ :=
    ⟨m₁.cart.1.lift g₁ τ h₂, m₁.cart.1.lift_fst _ _ _, m₁.cart.1.lift_snd _ _ _⟩
  have a₁ : u ≫ n.φ = g := by
    apply m.cart.1.hom_ext
    · show (_ ≫ _) ≫ m.φ = _ ≫ m.φ
      rw [Category.assoc, ← hn, e₁, reassoc_of% u₁, h₃]
    · rw [Category.assoc, n.cart.1.w, reassoc_of% u₂, h₁]
  have a₂ : u ≫ ν.φ ≫ m₂.toSABMap.φ = g₂ := by
    apply Y'.m0.cart.1.hom_ext
    · show (_ ≫ _) ≫ Y'.m0.toSABMap.φ = _ ≫ Y'.m0.toSABMap.φ
      rw [Category.assoc, ← hp, reassoc_of% u₁, h₄]
    · rw [Category.assoc, Category.assoc, m₂.cart.1.w, reassoc_of% hνw, reassoc_of% u₂, ← h₅, h₂]
  rw [← a₁, ← a₂, Category.assoc, hψ, Category.assoc, Category.assoc]

end ArcObj

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecSuccOfRelAmple
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open LBGerm

theorem IsAmpleLB.exists_sec_succ {X : Scheme.{0}} {L : LB X} (h : IsAmpleLB L) (x : X) :
    ∃ n, 1 ≤ n ∧ ∃ (a : (lbPow L n).Sec) (b : (lbPow L (n + 1)).Sec), x ∈ nonzeroLocus a ∧ x ∈ nonzeroLocus b := by
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  have hL := h.isLB
  obtain ⟨i, hi⟩ := exists_chart hL x
  obtain ⟨n, hn, s, hs, hr, -⟩ := h.exists_affine_le hi
  have le : ∀ J : PUnit → L.ι, nonzeroLocus s ⊓ powChart L J ≤ L.U (J PUnit.unit) ⊓ L.U i :=
    fun J y hy => ⟨mem_powChart.1 hy.2, hr hy.1⟩
  have hg : ∀ (J : PUnit → L.ι) (y : X), y ∈ nonzeroLocus s ⊓ powChart L J →
      gs (𝟙 X) y _ (resG X (le J) (L.g (J PUnit.unit) i).val) =
        (gm (𝟙 X) y (L.U (J PUnit.unit) ⊓ L.U i) (L.g (J PUnit.unit) i)).val := fun J y hy =>
    (gs_res (𝟙 X) y _ hy _).trans (gs_unit (𝟙 X) y _ (le J hy) _)
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul (m := 1) hL s (fun J => resG X (le J) (L.g (J PUnit.unit) i).val)
    (mem_secOn_of_germ (M := lbPow L 1) _ fun y J J' h hJ hJ' => by
      rw [gm_lbPow_g 1 (𝟙 X) y J J' hJ hJ', pow_one]
      refine (hg J y ⟨h, hJ⟩).trans (Eq.trans ?_ (congrArg _ (hg J' y ⟨h, hJ'⟩)).symm)
      rw [← Units.val_mul, gm_cocycle hL (𝟙 X) y (mem_powChart.1 hJ) (mem_powChart.1 hJ') (hr h)])
  obtain ⟨u, hu⟩ := hN (N + 1) (Nat.le_succ N)
  refine ⟨n * (N + 1), Nat.mul_pos hn (Nat.succ_pos N), secPow s (N + 1), secCast (Nat.add_comm _ _) u, ?_, ?_⟩
  · rwa [nonzeroLocus_secPow s (Nat.succ_pos N)]
  · have hJ : x ∈ powChart L (fun _ => i) := mem_powChart.2 hi
    have hy : x ∈ nonzeroLocus s ⊓ powChart L (fun _ => i) := ⟨hs, hJ⟩
    have e := congrArg (gs (𝟙 X) x _) (hu fun _ => i)
    rw [gs_res _ x _ hy, gs_mul _ x _ hy, gs_pow _ x _ hy, gs_res _ x _ hy, hg _ x hy] at e
    rw [nonzeroLocus_secCast, mem_nonzeroLocus_iff_powFn u hJ, e]
    exact (((mem_nonzeroLocus_iff_powFn s hJ).1 hs).pow _).mul (Units.isUnit _)

theorem exists_sec_succ_of_relAmple : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] (L : LB X.left), L.IsLB → RelAmple X L → ∀ x : X.left, ∃ (n : ℕ) (_ : 1 ≤ n) (a : H0 L n) (b : H0 L (n + 1)), x ∈ nonzeroLocus a ∧ x ∈ nonzeroLocus b := by
  intro R _ X _ L hL hA x
  obtain ⟨n, hn, a, b, ha, hb⟩ := (isAmpleLB_of_relAmple_of_isAffine X hL hA).exists_sec_succ x
  obtain ⟨a', ha', -⟩ := exists_sec_oneTerm L (K' := Fin 1) (e' := ((n : ℕ) : ℤ)) rfl a
  obtain ⟨b', hb', -⟩ := exists_sec_oneTerm L (K' := Fin 1) (e' := ((n + 1 : ℕ) : ℤ)) rfl b
  exact ⟨n, hn, a', b', ha'.ge ha, hb'.ge hb⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomExtOfSecPullEq
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor LBGerm

theorem ι_comp_eq_of_gs_eq {X Z : Scheme.{0}} (f g : Z ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) (W : Z.Opens)
    (hf : W ≤ f ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ U) (h : ∀ (a : Γ(X, U)), ∀ z ∈ W, gs f z U a = gs g z U a) :
    W.ι ≫ f = W.ι ≫ g := by
  have key : ∀ (U' : X.Opens) (hU' : U' = U) (V : Z.Opens) (hV : V ≤ W) (e₁ : V ≤ f ⁻¹ᵁ U') (e₂ : V ≤ g ⁻¹ᵁ U'),
      f.appLE U' V e₁ = g.appLE U' V e₂ := by
    intro U' hU' V hV e₁ e₂
    subst hU'
    ext a
    refine TopCat.Presheaf.section_ext Z.sheaf V _ _ fun z hz => ?_
    have hfz : f z ∈ U' := e₁ hz
    have hgz : g z ∈ U' := e₂ hz
    have := h a z (hV hz)
    rw [gs_eq f z U' hfz, gs_eq g z U' hgz] at this
    simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    erw [Z.presheaf.germ_res_apply, Z.presheaf.germ_res_apply]
    exact this
  rw [← f.resLE_comp_ι hf, ← g.resLE_comp_ι hg]
  congr 1
  have : IsAffine U := hU
  apply ext_of_isAffine
  show (Scheme.Hom.resLE f U W hf).app ⊤ = (Scheme.Hom.resLE g U W hg).app ⊤
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE, Scheme.Hom.resLE_appLE]
  exact key _ (Scheme.Opens.ι_image_top U) _ (Scheme.Opens.ι_image_le _ _) _ _

private theorem hom_mul_eq_mul_of_eq_mul {R R' S : CommRingCat} (φ : R ⟶ S) (ψ : R' ⟶ S) (x y : R) (x' y' : R')
    (G₁ G₂ : S) (hx : φ.hom x = G₁ * ψ.hom x') (hy : φ.hom y = G₂ * ψ.hom y') :
    φ.hom (x * y) = (G₁ * G₂) * ψ.hom (x' * y') := by
  rw [map_mul, map_mul, hx, hy]
  ring

theorem exists_sec_extend_pos {X : Scheme.{0}} [CompactSpace X] [QuasiSeparatedSpace X] {L : LB X} (hL : L.IsLB)
    {N : ℕ} (s : H0 L N) (a : Γ(X, nonzeroLocus s)) :
    ∃ (m : ℕ) (t : H0 L (N * m)), 1 ≤ m ∧ ∀ (x : X) (i : L.ι), x ∈ nonzeroLocus s → x ∈ L.U i →
      gs (𝟙 X) x _ (t.f fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) ^ m * gs (𝟙 X) x _ a := by
  obtain ⟨m, t, ht⟩ := (sec_extend_of_nonzeroLocus X L hL N s).1 a
  refine ⟨m + 1, ⟨fun j => s.f j * @id Γ(X, (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U j) (t.f j), fun i j => ?_⟩, by omega, fun x i hx hi => ?_⟩
  · have hc : ((N * (m + 1) : ℕ) : ℤ) = (N : ℤ) + ((N * m : ℕ) : ℤ) := by push_cast; ring
    have key := hom_mul_eq_mul_of_eq_mul _ _ (s.f i) (t.f i) (s.f j) (t.f j) _ _ (s.compat i j) (t.compat i j)
    refine key.trans (congrArg₂ (· * ·) ?_ rfl)
    dsimp only [LB.LinComb]
    rw [Fin.prod_univ_one, Fin.prod_univ_one, Fin.prod_univ_one, hc, zpow_add]
    exact (Units.val_mul _ _).symm
  · have hw : (𝟙 X) x ∈ (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U (fun _ => i) :=
      (mem_wchart_oneTerm (0 : Fin 1)).2 hi
    have e := gs_mul (𝟙 X) x _ hw (s.f fun _ => i) (t.f fun _ => i)
    have ht' : gs (𝟙 X) x ((L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U (fun _ => i)) (t.f fun _ => i) =
        gs (𝟙 X) x ((L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U (fun _ => i)) (s.f fun _ => i) ^ m *
          gs (𝟙 X) x _ a := ht x (fun _ => i) hx hi
    refine e.trans ?_
    rw [ht']
    ring

private theorem gs_eq_stalkMap_gs_id_uniformization {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (hz : r z ∈ U) (b : Γ(X, U)) :
    gs r z U b = (r.stalkMap z).hom (gs (𝟙 X) (r z) U b) := by
  rw [gs_eq r z U hz, gs_eq (𝟙 X) (r z) U hz]
  have e := congrArg (fun φ => φ.hom b) (r.germ_stalkMap U z hz)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e.symm

theorem gs_pull_extend {X Z : Scheme.{0}} {L : LB X} {N n m : ℕ} (s : H0 L N) (t : H0 L n) (a : Γ(X, nonzeroLocus s))
    (h : ∀ (x : X) (i : L.ι), x ∈ nonzeroLocus s → x ∈ L.U i →
      gs (𝟙 X) x _ (t.f fun _ => i) = gs (𝟙 X) x _ (s.f fun _ => i) ^ m * gs (𝟙 X) x _ a)
    (r : Z ⟶ X) (z : Z) (i : L.ι) (hz : r z ∈ nonzeroLocus s) (hi : r z ∈ L.U i) :
    gs r z _ (t.f fun _ => i) = gs r z _ (s.f fun _ => i) ^ m * gs r z _ a := by
  have hw : r z ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) := (mem_wchart_oneTerm (0 : Fin 1)).2 hi
  have hwn : r z ∈ (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (n : ℤ)).U (fun _ => i) := hw
  have hwN : r z ∈ (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (N : ℤ)).U (fun _ => i) := hw
  rw [gs_eq_stalkMap_gs_id_uniformization r z _ hwn, gs_eq_stalkMap_gs_id_uniformization r z _ hwN, gs_eq_stalkMap_gs_id_uniformization r z _ hz, h (r z) i hz hi, map_mul, map_pow]

private theorem isUnit_gs_of_mem_basicOpen' {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U : X.Opens} (b : Γ(X, U))
    (hb : r z ∈ X.basicOpen b) : IsUnit (gs r z U b) := by
  have hU : r z ∈ U := X.basicOpen_le b hb
  rw [gs_eq_stalkMap_gs_id_uniformization r z U hU, gs_eq (𝟙 X) (r z) U hU]
  exact ((X.mem_basicOpen b (r z) hU).1 hb).map (r.stalkMap z).hom

private theorem mem_basicOpen_of_isUnit_gs {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U : X.Opens} (b : Γ(X, U))
    (hU : r z ∈ U) (hb : IsUnit (gs r z U b)) : r z ∈ X.basicOpen b := by
  rw [gs_eq_stalkMap_gs_id_uniformization r z U hU, gs_eq (𝟙 X) (r z) U hU] at hb
  rw [X.mem_basicOpen b (r z) hU]
  exact (isUnit_map_iff (r.stalkMap z).hom _).1 hb

private theorem exists_mem_basicOpen_of_mem_nonzeroLocus {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : H0 L n) {x : X}
    (hx : x ∈ nonzeroLocus a) : ∃ j : L.ι, x ∈ X.basicOpen (a.f fun _ => j) := by
  unfold nonzeroLocus at hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨j, rfl⟩ : ∃ j, k = fun _ => j := ⟨k 0, funext fun q => congrArg k (Subsingleton.elim q 0)⟩
  exact ⟨j, hk⟩

private theorem mem_nonzeroLocus_of_mem_basicOpen {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : H0 L n) (j : L.ι) {x : X}
    (hx : x ∈ X.basicOpen (a.f fun _ => j)) : x ∈ nonzeroLocus a := by
  unfold nonzeroLocus
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j, hx⟩

private theorem exists_mem_chart' {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : X) : ∃ j, x ∈ L.U j := by
  have hx : x ∈ ⨆ i, L.U i := by
    rw [hL.cover]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.1 hx

theorem hom_ext_of_sec_pull_eq : ∀ (X Z : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → (∃ (N : ℕ) (_ : 1 ≤ N) (κ : Type) (s : κ → H0 L N), (⨆ i, nonzeroLocus (s i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (s i))) → ∀ (f g : Z ⟶ X) (v : LB.Iso (L.pull f) (L.pull g)), v.IsGen → (∀ (n : ℕ), 1 ≤ n → ∀ (a : H0 L n) (z : Z) (j j' : L.ι), g z ∈ L.U j → f z ∈ L.U j' → Geo.Tor.gs g z _ (a.f (fun _ => j)) = (Geo.Tor.gw v (𝟙 Z) z j (fun _ => j') ^ n).val * Geo.Tor.gs f z _ (a.f (fun _ => j'))) → f = g := by
  intro X Z _ _ L hL hcov f g v _ hrel
  obtain ⟨N, hN, κ, s, hD, haff⟩ := hcov
  have fg : ∀ (n : ℕ), 1 ≤ n → ∀ (a : H0 L n) (z : Z), f z ∈ nonzeroLocus a → g z ∈ nonzeroLocus a := by
    intro n hn a z hz
    obtain ⟨j', hj'⟩ := exists_mem_basicOpen_of_mem_nonzeroLocus a hz
    obtain ⟨j, hj⟩ := exists_mem_chart' hL (g z)
    have hf' : f z ∈ L.U j' := (mem_wchart_oneTerm (0 : Fin 1)).1 (X.basicOpen_le _ hj')
    have hgw : g z ∈ (L.LinComb (fun _ : Fin 1 => 𝟙 X) fun _ => (n : ℤ)).U (fun _ => j) :=
      (mem_wchart_oneTerm (0 : Fin 1)).2 hj
    have u2 : IsUnit (gs g z _ (a.f fun _ => j)) := by
      rw [hrel n hn a z j j' hj hf']
      exact (Units.isUnit _).mul (isUnit_gs_of_mem_basicOpen' f z _ hj')
    exact mem_nonzeroLocus_of_mem_basicOpen a j (mem_basicOpen_of_isUnit_gs g z _ hgw u2)
  have hW : ⨆ i, f ⁻¹ᵁ nonzeroLocus (s i) = ⊤ := by
    refine eq_top_iff.2 fun z _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    have hz : f z ∈ ⨆ i, nonzeroLocus (s i) := by
      rw [hD]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact ⟨i, hi⟩
  refine (Z.openCoverOfIsOpenCover (fun i => f ⁻¹ᵁ nonzeroLocus (s i)) hW).hom_ext f g fun i => ?_
  show (f ⁻¹ᵁ nonzeroLocus (s i)).ι ≫ f = (f ⁻¹ᵁ nonzeroLocus (s i)).ι ≫ g
  refine ι_comp_eq_of_gs_eq f g (haff i) _ le_rfl (fun z hz => fg N hN (s i) z hz) fun a z hz => ?_
  have hfD : f z ∈ nonzeroLocus (s i) := hz
  have hgD : g z ∈ nonzeroLocus (s i) := fg N hN (s i) z hz
  obtain ⟨j, hb⟩ := exists_mem_basicOpen_of_mem_nonzeroLocus (s i) hgD
  have hgj : g z ∈ L.U j := (mem_wchart_oneTerm (0 : Fin 1)).1 (X.basicOpen_le _ hb)
  obtain ⟨j', hfj'⟩ := exists_mem_chart' hL (f z)
  obtain ⟨m, t, hm, ht⟩ := exists_sec_extend_pos hL (s i) a
  have step_before_last_eq_s_succ := hrel N hN (s i) z j j' hgj hfj'
  have eq_t := hrel (N * m) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) t z j j' hgj hfj'
  have ext_g := gs_pull_extend (s i) t a ht g z j hgD hgj
  have ext_f := gs_pull_extend (s i) t a ht f z j' hfD hfj'
  have hu : IsUnit (gs g z _ ((s i).f fun _ => j)) := isUnit_gs_of_mem_basicOpen' g z _ hb
  have key : gs g z _ ((s i).f fun _ => j) ^ m * gs g z _ a =
      gs g z _ ((s i).f fun _ => j) ^ m * gs f z _ a := by
    rw [← ext_g, eq_t, ext_f, step_before_last_eq_s_succ, mul_pow, ← Units.val_pow_eq_pow_val, ← pow_mul]
    ring
  exact ((hu.pow m).mul_left_cancel key).symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmallTorusPointKeepingRatiosIsZero
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmallTorusPointKeepingRatiosIsZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.SmallZero
open CoefBasic SmallPoint

theorem le_of_sumV_sub {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {f g : Ix → F}
    (h : SumV v (fun i => f i - g i) 0) (i₀ i₁ : Ix) (q : ℚ) (hf : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (f i))
    (hg : ∀ i, i ≠ i₁ → (q : WithTop ℚ) ≤ v (g i)) : (q : WithTop ℚ) ≤ v (f i₀ - g i₁) := by
  classical
  obtain ⟨S, hS⟩ := h q
  have h₁ := hS (insert i₀ (insert i₁ S)) ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))
  have m₀ : i₀ ∈ insert i₀ (insert i₁ S) := Finset.mem_insert_self _ _
  have m₁ : i₁ ∈ insert i₀ (insert i₁ S) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have h₂ : (q : WithTop ℚ) ≤ v (∑ i ∈ (insert i₀ (insert i₁ S)).erase i₀, f i) :=
    v.map_le_sum fun i hi => hf i (Finset.ne_of_mem_erase hi)
  have h₃ : (q : WithTop ℚ) ≤ v (∑ i ∈ (insert i₀ (insert i₁ S)).erase i₁, g i) :=
    v.map_le_sum fun i hi => hg i (Finset.ne_of_mem_erase hi)
  rw [Finset.sum_sub_distrib, ← Finset.add_sum_erase _ f m₀, ← Finset.add_sum_erase _ g m₁, zero_sub,
    v.map_neg] at h₁
  have := v.map_le_add (v.map_le_sub h₁ h₂) h₃
  convert this using 2
  ring

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 1 ≤ k → ∀ (d o : GtPtF D.toPre F) (l : D.toPre.X → ℚ), o.IsZero → GtV hϖ hv d l → (∀ m, |l m| ≤ Q m) → (∀ (n j : ℕ), 1 ≤ n → j = k * n → ∀ (w₁ : Frm D.toPre F j o.b), FrmOne w₁ → ∃ w : Frm D.toPre F j d.b, w.IsGen ∧ ∀ S₁ S₂ : Fam D.toPre F j, ¬ SumV v (coef S₂ o w₁) 0 → ∀ α, SumV v (fun χ => coef S₁ d w χ * coef S₂ o w₁ (α - χ) - coef S₂ d w χ * coef S₁ o w₁ (α - χ)) 0) → d.IsZero := by
  intro hL hT hVR hTW hUU V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv k hk d o l ho hl hlQ H
  have hdb : d.b = 1 := SmallPoint.main hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv k hk d o l ho hl hlQ H
  have I := GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv
  have I' := GlobalTheory.UT.CoefUnit.exists_fam_coef_val hL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have K := GlobalTheory.UT.gt_onto_divisible_kernel hL V (maximalIdeal V) hA D F
  have hob : o.b = 1 := ((isZero_iff o).1 ho).1
  obtain ⟨l', hl', -⟩ := (I d).1
  have hll : ∀ χ, l χ = l' χ := by
    obtain ⟨w, hw⟩ := (coef_basic V D.toPre F 4 d).1
    obtain ⟨ω, hω, -⟩ := (I d).2.1 4 w hw
    have le : ∀ l₁ l₂, GtV hϖ hv d l₁ → GtV hϖ hv d l₂ → ∀ χ, l₁ χ ≤ l₂ χ := fun l₁ l₂ h₁ h₂ χ => by
      obtain ⟨s, hs, -, e⟩ := I' 4 le_rfl d w l₂ ω hw h₂ hω χ
      have := ((I d).2.2.2.2.2.2 4 (by omega) w s hw).2 l₁ ω 0 h₁ hω hs χ
      rw [e, WithTop.coe_le_coe] at this
      linarith
    exact fun χ => le_antisymm (le _ _ hl hl' χ) (le _ _ hl' hl χ)
  have hlow : ∀ m, -(Q m : ℚ) ≤ l' m := fun m => hll m ▸ (abs_le.1 (hlQ m)).1
  obtain ⟨t, ht, -⟩ := K.2.2.2.1 d hdb
  have hto : IsTor 1 o := ⟨hob, fun χ z J hJ => by
    rw [((isZero_iff o).1 ho).2 χ z J hJ, MonoidHom.one_apply, Units.val_one, Units.val_one, cst_eq, map_one]⟩
  have hadd : o.IsAdd d d := (K.2.2.2.2 1 t o d d hto ht).2 (by rwa [_root_.one_mul])
  have hQ0 : ∀ m, (0 : ℚ) ≤ Q m := fun m => (abs_nonneg _).trans (hlQ m)
  have A : ∀ (κ₀ : D.toPre.X) (n j : ℕ), 4 ≤ n → j = k * n →
      (((j : ℚ) - 1 - 2 * Q κ₀ : ℚ) : WithTop ℚ) ≤ v ((t (Multiplicative.ofAdd κ₀)).val - 1) := by
    intro κ₀ n j hn hj
    have hj4 : 4 ≤ j := hj ▸ le_trans hn (Nat.le_mul_of_pos_left _ hk)
    have hj1 : 1 ≤ j := by omega
    have hj0 : (0 : ℚ) < j := by exact_mod_cast hj1
    have hj1' : (1 : ℚ) ≤ j := by exact_mod_cast hj1
    obtain ⟨w₁, hw₁⟩ := (coef_basic V D.toPre F j o).2.1 hob
    obtain ⟨w', hw'⟩ := (coef_basic V D.toPre F j d).2.1 hdb
    obtain ⟨w, hw, Hw⟩ := H n j (by omega) hj w₁ hw₁
    obtain ⟨c, hc0, vc, ec⟩ := ((coef_basic V D.toPre F j d).2.2 w' hw'.1).2.2.1 w hw
    have et := ((coef_basic V D.toPre F j o).2.2 w₁ hw₁.1).2.2.2 t d d w' ht hadd
      (fun z J hJ => (hw'.2 z J hJ).trans (hw₁.2 z J hJ).symm)
    obtain ⟨ω, hcω⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 hc0)
    have hω : GenV hϖ hv w ω := by
      obtain ⟨φ₀, hφ, t₀, ht₀, x, hx, e⟩ := (I d).2.2.1 j w' hw' hdb
      refine ⟨φ₀, hφ, t₀, ht₀, c * x, by rw [v.map_mul, hx, ← hcω]; simp, fun z J hJ => ?_⟩
      rw [vc z J hJ, e z J hJ, cst_eq, cst_eq, cst_eq, map_mul, _root_.mul_assoc]
    have hω₁ := (I o).2.2.1 j w₁ hw₁ hob
    obtain ⟨S₁, n₁, -, e₁⟩ := I' j hj4 o w₁ 0 0 hw₁.1 (gtV_zero ho) hω₁ κ₀
    obtain ⟨S₂, n₂, z₂, e₂⟩ := I' j hj4 o w₁ 0 0 hw₁.1 (gtV_zero ho) hω₁ 0
    rw [Pi.zero_apply, add_zero, add_zero] at e₁ e₂
    rw [QForm.Q_zero hϖ D hQ, Int.cast_zero, zero_div] at e₂
    have hQj : ∀ mu, (Q (j • mu) : ℚ) / j = j * Q mu := fun mu => by
      rw [Q_nsmul hϖ hQ]; push_cast; field_simp
    have hQs : ∀ mu, (Q κ₀ : ℚ) / j + j * Q mu - Q mu - Q κ₀ ≤ (Q (κ₀ + j • mu) : ℚ) / j := fun mu => by
      have h0 := hQ0 (mu + κ₀)
      have : (Q (κ₀ + j • mu) : ℚ) / j = Q κ₀ / j + j * Q mu + (Q (mu + κ₀) - Q mu - Q κ₀) := by
        rw [q_shift hϖ hQ, QForm.bOf]; push_cast; field_simp; ring
      linarith
    have bo : ∀ S : Fam D.toPre F j, NuGe D Q F v j S 0 → ∀ χ,
        (((Q χ : ℚ) / j : ℚ) : WithTop ℚ) ≤ v (coef S o w₁ χ) := fun S hS χ => by
      have := ((I o).2.2.2.2.2.2 j hj1 w₁ S hw₁.1).2 0 0 0 (gtV_zero ho) hω₁ hS χ
      rwa [Pi.zero_apply, add_zero, add_zero, zero_add] at this
    have bd : ∀ S : Fam D.toPre F j, NuGe D Q F v j S 0 → ∀ χ,
        (((Q χ : ℚ) / j + l' χ + ω : ℚ) : WithTop ℚ) ≤ v (coef S d w χ) := fun S hS χ => by
      have := ((I d).2.2.2.2.2.2 j hj1 w S hw).2 l' ω 0 hl' hω hS χ
      rwa [zero_add] at this
    have hQ1 : ∀ mu : D.toPre.X, mu ≠ 0 → (1 : ℚ) ≤ Q mu := fun mu h => by
      exact_mod_cast QForm.Q_pos hϖ D hQ h
    have z₂' : ∀ (g : GtPtF D.toPre F) (u : Frm D.toPre F j g.b) (χ), (¬ ∃ mu, χ = j • mu) → coef S₂ g u χ = 0 :=
      fun g u χ e => coef_zero S₂ g u (z₂ χ fun mu h => e ⟨mu, by rw [h, zero_add]⟩)
    have hne : ¬ SumV v (coef S₂ o w₁) 0 := fun h => by
      have := le_of_sumV h 0 1 fun χ hχ => by
        by_cases e : ∃ mu, χ = j • mu
        · obtain ⟨mu, rfl⟩ := e
          refine le_trans (WithTop.coe_le_coe.2 ?_) (bo S₂ n₂ _)
          have := hQ1 mu fun e => hχ (by rw [e, smul_zero])
          rw [hQj]
          nlinarith
        · rw [z₂' o w₁ χ e, v.map_zero]; exact le_top
      rw [e₂, WithTop.coe_le_coe] at this
      linarith
    have key := le_of_sumV_sub (Hw S₁ S₂ hne κ₀) κ₀ 0 (ω + (Q κ₀ : ℚ) / j + ((j : ℚ) - 1 - 2 * Q κ₀))
      (fun χ hχ => by
        by_cases e : ∃ mu, κ₀ - χ = j • mu
        · obtain ⟨mu, e⟩ := e
          obtain rfl : χ = κ₀ + j • (-mu) := by rw [smul_neg, ← e]; abel
          have h1 := hQ1 (-mu) fun e => hχ (by rw [e, smul_zero, add_zero])
          rw [v.map_mul, e]
          refine le_trans ?_ (add_le_add (bd S₁ n₁ _) (bo S₂ n₂ _))
          rw [← WithTop.coe_add, WithTop.coe_le_coe, hQj, ← QForm.Q_neg hϖ D hQ mu, map_add (f := _), map_nsmul, nsmul_eq_mul]
          have h2 := hQs (-mu)
          have h3 := hlow κ₀
          have h4 := mul_le_mul_of_nonneg_left (hlow (-mu)) hj0.le
          have h5 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hj1')
          nlinarith
        · rw [z₂' o w₁ _ e, MulZeroClass.mul_zero, v.map_zero]; exact le_top)
      (fun χ hχ => by
        by_cases e : ∃ mu, χ = j • mu
        · obtain ⟨mu, rfl⟩ := e
          have h1 := hQ1 mu fun e => hχ (by rw [e, smul_zero])
          rw [v.map_mul, sub_eq_add_neg κ₀, ← smul_neg]
          refine le_trans ?_ (add_le_add (bd S₂ n₂ _) (bo S₁ n₁ _))
          rw [← WithTop.coe_add, WithTop.coe_le_coe, hQj, map_nsmul, nsmul_eq_mul]
          have h2 := hQs (-mu)
          rw [QForm.Q_neg hϖ D hQ mu] at h2
          have h3 := hQ0 κ₀
          have h4 := mul_le_mul_of_nonneg_left (hlow mu) hj0.le
          have h5 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hj1')
          nlinarith
        · rw [z₂' d w _ e, MulZeroClass.zero_mul, v.map_zero]; exact le_top)
    rw [sub_self, sub_zero, ec, ec, et, et, ofAdd_zero, map_one, Units.val_one,
      show c * ((t (Multiplicative.ofAdd κ₀)).val * coef S₁ o w₁ κ₀) * coef S₂ o w₁ 0 -
        c * (1 * coef S₂ o w₁ 0) * coef S₁ o w₁ κ₀ =
        c * coef S₁ o w₁ κ₀ * coef S₂ o w₁ 0 * ((t (Multiplicative.ofAdd κ₀)).val - 1) by ring,
      v.map_mul, v.map_mul, v.map_mul, ← hcω, e₁, e₂, ← WithTop.coe_add, ← WithTop.coe_add, add_zero,
      WithTop.coe_add (ω + (Q κ₀ : ℚ) / j)] at key
    exact (WithTop.add_le_add_iff_left WithTop.coe_ne_top).1 key
  have B : ∀ κ₀, (t (Multiplicative.ofAdd κ₀)).val = 1 := fun κ₀ => by
    by_contra hx
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 (v.ne_top_iff.2 (sub_ne_zero.2 hx))
    obtain ⟨n, hn⟩ := exists_nat_gt (q + 1 + 2 * Q κ₀)
    have e := A κ₀ (n + 4) _ (by omega) rfl
    rw [← hq, WithTop.coe_le_coe] at e
    have : ((n + 4 : ℕ) : ℚ) ≤ ((k * (n + 4) : ℕ) : ℚ) := by exact_mod_cast Nat.le_mul_of_pos_left _ hk
    push_cast at this e
    linarith
  refine (isZero_iff d).2 ⟨hdb, fun χ z J hJ => Units.ext ?_⟩
  rw [ht.2 χ z J hJ, B, cst_eq, map_one, Units.val_one]

end GlobalTheory.UT.SmallZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmallTorusPointKeepingRatiosIsZeroStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallTorusPoint_keeping_ratios_isZero : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ (k : ℕ), 1 ≤ k → ∀ (d o : GtPtF D.toPre F) (l : D.toPre.X → ℚ), o.IsZero → GtV hϖ hv d l → (∀ m, |l m| ≤ Q m) → (∀ (n j : ℕ), 1 ≤ n → j = k * n → ∀ (w₁ : Frm D.toPre F j o.b), FrmOne w₁ → ∃ w : Frm D.toPre F j d.b, w.IsGen ∧ ∀ S₁ S₂ : Fam D.toPre F j, ¬ SumV v (coef S₂ o w₁) 0 → ∀ α, SumV v (fun χ => coef S₁ d w χ * coef S₂ o w₁ (α - χ) - coef S₂ d w χ * coef S₁ o w₁ (α - χ)) 0) → d.IsZero := by
  first | exact @GlobalTheory.UT.SmallZero.main | exact GlobalTheory.UT.SmallZero.main | (intros; apply GlobalTheory.UT.SmallZero.main <;> assumption)
end
end
