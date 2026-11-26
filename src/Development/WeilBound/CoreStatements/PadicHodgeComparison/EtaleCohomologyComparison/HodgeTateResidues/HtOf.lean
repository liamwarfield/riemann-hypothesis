module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernCocycleAllLevels
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Half1
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.SumCoord
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.SmulAbs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.DiffMem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.NmAMem
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.ClsZeroOfRep
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HalfGaloisOfCompatible
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.CrisSurj
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfEtSide

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.GTSmul
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

set_option maxHeartbeats 1000000

namespace CrystallineSemistableComparison.HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {ht : TFil l}
  {Lf : ∀ {M : Model l K} (r : ℕ) {j : ℕ}, M.T j → Fam M r j → Prop} (h1 : Half1 ht @Lf)
  {γ : ∀ {M : Model l K} {r j : ℕ}, Fam M r j → ∀ a, Module.Dual K (Hdg M.q a j) →+ ℂ_[l]} (h2 : Half2 ht @γ)

include h1 h2 in
theorem indep {M : Model l K} (hM : M.Sm) {j r r' : ℕ} {v : M.T j} {x : Fam M r j} {x' : Fam M r' j} (hx : Lf r v x)
    (hx' : Lf r' v x') (a : ℕ) : γ x a = γ x' a := by
  obtain ⟨k, hk⟩ := h1.uniq M hM j
  have a1 := h1.sh r' (rfl : r + r' = r + r') hx
  have a2 := h1.sh r (Nat.add_comm r' r) hx'
  have e := hk (r + r') v _ _ a1 a2
  rw [← h2.sh hM r' rfl x (h1.comp hx) a, ← h2.sh hM r (Nat.add_comm r' r) x' (h1.comp hx') a,
    ← h2.sh hM k rfl _ (h1.comp a1) a, ← h2.sh hM k rfl _ (h1.comp a2) a, e]

def rr {M : Model l K} (hM : M.Sm) (j : ℕ) : ℕ := (h1.ex M hM j).choose

def xx {M : Model l K} (hM : M.Sm) {j : ℕ} (v : M.T j) : Fam M (rr h1 hM j) j := ((h1.ex M hM j).choose_spec v).choose

theorem xx_spec {M : Model l K} (hM : M.Sm) {j : ℕ} (v : M.T j) : Lf _ v (xx h1 hM v) := ((h1.ex M hM j).choose_spec v).choose_spec


variable (γ) in
def gT {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (v : M.T j) : Module.Dual K (Hdg M.q a j) →+ ℂ_[l] := γ (xx h1 hM v) a

include h2 in
theorem gT_eq {M : Model l K} (hM : M.Sm) (a : ℕ) {j r : ℕ} {v : M.T j} {x : Fam M r j} (hx : Lf r v x) :
    gT h1 (@γ) hM a v = γ x a := indep h1 h2 hM (xx_spec h1 hM v) hx a

include h2 in
theorem gT_add {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (v w : M.T j) :
    gT h1 (@γ) hM a (v + w) = gT h1 (@γ) hM a v + gT h1 (@γ) hM a w :=
  (gT_eq h1 h2 hM a (h1.add (xx_spec h1 hM v) (xx_spec h1 hM w))).trans
    (h2.add hM _ _ (h1.comp (xx_spec h1 hM v)) (h1.comp (xx_spec h1 hM w)) a)

include h2 in
theorem gT_smul {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (z : ℤ_[l]) (v : M.T j) (φ : Module.Dual K (Hdg M.q a j)) :
    gT h1 (@γ) hM a (z • v) φ = qC l (z : ℚ_[l]) * gT h1 (@γ) hM a v φ := by
  rw [gT_eq h1 h2 hM a (h1.smul z (xx_spec h1 hM v)), h2.lin hM _ _ (h1.comp (xx_spec h1 hM v)), θA_zA]
  rfl

include h2 in
theorem gT_act {M : Model l K} (hM : M.Sm) (a : ℕ) {j : ℕ} (σ : K.fixingSubgroup) (v : M.T j) (φ : Module.Dual K (Hdg M.q a j)) :
    qC l (period_ring_base.χ σ.1) ^ a * gT h1 (@γ) hM a (M.actT j σ v) φ = period_ring_base.σC σ.1 (gT h1 (@γ) hM a v φ) := by
  have e1 := gT_smul h1 h2 hM a ((DeRhamTwist.Twist.chi0 l σ.1 ^ rr h1 hM j : ℤ_[l]ˣ) : ℤ_[l]) (M.actT j σ v) φ
  replace e1 := (DFunLike.congr_fun (gT_eq h1 h2 hM a (h1.gal σ (xx_spec h1 hM v))) φ).symm.trans e1
  rw [Units.val_pow_eq_pow_val, PadicInt.coe_pow, map_pow] at e1
  have e2 := h2.gal hM σ _ (h1.comp (xx_spec h1 hM v)) a φ
  rw [e1] at e2
  have hc : qC l (period_ring_base.χ σ.1) ^ rr h1 hM j ≠ 0 := pow_ne_zero _ ((map_ne_zero _).2 (χ_ne _))
  refine mul_left_cancel₀ hc (Eq.trans ?_ e2)
  exact mul_left_comm _ _ _

def hV {M : Model l K} (hM : M.Sm) (a n : ℕ) : M.V n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l]) :=
  (TensorProduct.liftAddHom (R := ℤ_[l]) (M := ℚ_[l]) (N := M.T n)
    (AddMonoidHom.mk' (fun z => AddMonoidHom.mk' (fun u =>
      AddMonoidHom.mk' (fun φ => qC l z * gT h1 (@γ) hM a u φ) (by intros; simp [mul_add]))
        (by intros; ext; simp [gT_add h1 h2, mul_add])) (by intros; ext; simp [add_mul]))
    (by
      intro r z u
      ext φ
      simp only [AddMonoidHom.mk'_apply]
      rw [gT_smul h1 h2, Algebra.smul_def, map_mul]
      simp only [PadicInt.algebraMap_apply]
      ring) :
    ℚ_[l] ⊗[ℤ_[l]] M.T n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l]))


open Classical in
def hP (M : Model l K) (a n : ℕ) : M.V n →+ (Module.Dual K (Hdg M.q a n) →+ ℂ_[l]) :=
  if hM : M.Sm then hV h1 h2 hM a n else 0

theorem hP_tmV {M : Model l K} (hM : M.Sm) (a n : ℕ) (z : ℚ_[l]) (u : M.T n) (φ : Module.Dual K (Hdg M.q a n)) :
    hP h1 h2 M a n (tmV M n z u) φ = qC l z * gT h1 (@γ) hM a u φ := by
  rw [hP, dite_eq_left hM]
  unfold hV tmV
  erw [TensorProduct.liftAddHom_tmul]
  rfl

theorem hP_toV {M : Model l K} (hM : M.Sm) (a : ℕ) {n r : ℕ} {u : M.T n} {x : Fam M r n} (hx : Lf r u x)
    (φ : Module.Dual K (Hdg M.q a n)) : hP h1 h2 M a n (M.toV n u) φ = γ x a φ := by
  rw [toV_eq, hP_tmV h1 h2 hM, map_one, one_mul, gT_eq h1 h2 hM a hx]

theorem hP_not {M : Model l K} (hM : ¬ M.Sm) (a n : ℕ) (v : M.V n) (φ : Module.Dual K (Hdg M.q a n)) :
    hP h1 h2 M a n v φ = 0 := by
  rw [hP, dite_eq_right hM]; rfl

include h1 h2 in
theorem pre_of (hF : KFin) (hC : DlogClassExistsUnique) : Nonempty (HTPre l K) := ⟨{
  h := hP h1 h2
  lin := fun M a n z v φ => by
    by_cases hM : M.Sm
    · refine V_induction (p := fun v => hP h1 h2 M a n (z • v) φ = qC l z * hP h1 h2 M a n v φ) v ?_ ?_ ?_
      · simp only [smul_zero, map_zero, AddMonoidHom.zero_apply, mul_zero]
      · intro z' u
        simp only [smul_tmV, hP_tmV h1 h2 hM, map_mul, mul_assoc]
      · intro x y hx hy
        simp only [smul_add, map_add (f := _), AddMonoidHom.add_apply, mul_add] at hx hy ⊢
        rw [hx, hy]
    · simp only [hP_not h1 h2 hM, mul_zero]
  lin' := fun M a n k v φ => by
    by_cases hM : M.Sm
    · refine V_induction (p := fun v => hP h1 h2 M a n v (k • φ) = kC K k * hP h1 h2 M a n v φ) v ?_ ?_ ?_
      · simp only [map_zero, AddMonoidHom.zero_apply, mul_zero]
      · intro z' u
        simp only [hP_tmV h1 h2 hM, gT]
        rw [h2.lin' hM _ (h1.comp (xx_spec h1 hM u)), mul_left_comm]
      · intro x y hx hy
        simp only [map_add (f := _), AddMonoidHom.add_apply, mul_add] at hx hy ⊢
        rw [hx, hy]
    · simp only [hP_not h1 h2 hM, mul_zero]
  fin := fun M hM a n => by
    have := proper_q hM
    have := smooth_q hM
    exact hF M.q a n
  equi := fun M hM a n σ v φ => by
    refine V_induction (p := fun v => qC l (period_ring_base.χ σ.1) ^ a * hP h1 h2 M a n (M.act n σ v) φ =
      period_ring_base.σC σ.1 (hP h1 h2 M a n v φ)) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply, mul_zero]
    · intro z u
      simp only [act_tmV, hP_tmV h1 h2 hM]
      rw [map_mul, σC_qC, mul_left_comm, gT_act h1 h2 hM]
    · intro x y hx hy
      simp only [map_add (f := _), AddMonoidHom.add_apply, mul_add] at hx hy ⊢
      rw [hx, hy]
  nat := fun M N u hu hM hN a n v φ => by
    refine V_induction (p := fun v => hP h1 h2 M a n (Model.pullV u hu n v) φ =
      hP h1 h2 N a n v (φ ∘ₗ pullH (Model.genMap u hu) (Model.genMap_q u hu) a n)) v ?_ ?_ ?_
    · simp only [map_zero, AddMonoidHom.zero_apply]
    · intro z w
      simp only [pullV_tmV, hP_tmV h1 h2 hM, hP_tmV h1 h2 hN]
      rw [gT_eq h1 h2 hM a (h1.nat u hu (xx_spec h1 hN w)), h2.nat u hu hM hN _ (h1.comp (xx_spec h1 hN w))]
      rfl
    · intro x y hx hy
      simp only [map_add (f := _), AddMonoidHom.add_apply] at hx hy ⊢
      rw [hx, hy]
  cup := fun M hM i j x y z hz m m' b b' c φ => by
    have hx := xx_spec h1 hM x
    have hy := xx_spec h1 hM y
    rw [hP_toV h1 h2 hM c (h1.cup rfl hz hx hy), h2.cup hM rfl _ _ (h1.comp hx) (h1.comp hy) b b' c φ]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    rw [hP_toV h1 h2 hM _ hx, hP_toV h1 h2 hM _ hy]
  one := fun M hM v hv φ => by rw [hP_toV h1 h2 hM 0 (h1.one M v hv), h2.one hM]
  first_chern_class_exists := fun M hM D _ hD => ⟨h1.first_chern_class_exists M D, hC M.q (genD D) (sSup_pb D _ hD)⟩
  c1 := fun M hM D hE hD r v c hv hc => by
    obtain ⟨x, hx, hl⟩ := h1.c1 M D hE hD r v hv
    have := h2.c1 hM D hD x c (h1.comp hl) hx hc
    exact ⟨fun φ => (hP_toV h1 h2 hM 1 hl φ).trans (this.1 φ),
      fun a ha φ => (hP_toV h1 h2 hM a hl φ).trans (by rw [this.2 a ha]; rfl)⟩ }⟩

end CrystallineSemistableComparison.HT
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompat
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb GlobalTheory.CompanionTheory

namespace FirstChernHodgeTateFacts

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {A : C ⥤ CommAlgCat.{0} R}
  {A' : C' ⥤ CommAlgCat.{0} R'} {σ : R →+* R'}

theorem rep_of_closed (a b : IdF A) {n : ℕ} (z : CH.Cn (CH.modF A) n) (hz : CH.d _ n z = 0) (ha : ∀ s, z s ∈ a.S _) :
    ∃ c, Rep a b z c := by
  let f : CH.Cn (sq a b) n := fun s => sqMk a b (z s) (ha s)
  let m₁ := toSq (IdF.top A) b fun _ => rfl
  let m₂ : CH.Mor (sq a b) (sq (IdF.top A) b) (RingHom.id R) := sqLe (fun _ => le_top) fun _ => le_rfl
  have e1 : m₂.pullC n f = m₁.pullC n z := rfl
  have e2 : m₂.pullC (n + 1) (CH.d _ n f) = 0 := by
    rw [← m₂.d_pullC, e1, m₁.d_pullC, hz, map_zero]
  have hf : CH.d _ n f = 0 := by
    funext s
    obtain ⟨y, hy, e⟩ := sq_surj a b (CH.d _ n f s)
    have e3 := congrArg Subtype.val (congrFun e2 s)
    change Ideal.Quotient.factorₐ R le_rfl (show sqM a b _ from CH.d _ n f s).1 = 0 at e3
    rw [← e] at e3 ⊢
    exact Subtype.ext e3
  exact ⟨_, f, hf, rfl, fun _ => rfl⟩

theorem rep_cls {F : C ⥤ ModuleCat.{0} R} {a' b' : IdF A'} (m : CH.Mor F (sq a' b') σ) {n : ℕ} (f : CH.Cn F n) (hf : CH.d _ n f = 0)
    (z' : ∀ s : ComposableArrows C' n, A'.obj (s.obj (Fin.last n)))
    (h : ∀ s, (show sqM a' b' _ from m.τ _ (f (s ⋙ m.G))).1 = Ideal.Quotient.mk _ (z' s)) :
    Rep a' b' z' (m.pull n ((CH.cx F).cls f hf)) :=
  ⟨m.pullC n f, by rw [m.d_pullC, hf, map_zero], rfl, h⟩

theorem rep_pull {a b : IdF A} {a' b' : IdF A'} (m : CH.Mor (sq a b) (sq a' b') σ) {n : ℕ}
    {z : ∀ s : ComposableArrows C n, A.obj (s.obj (Fin.last n))} {c : CH.H (sq a b) n} (hc : Rep a b z c)
    (z' : ∀ s : ComposableArrows C' n, A'.obj (s.obj (Fin.last n)))
    (h : ∀ (s : ComposableArrows C' n) (x : sqM a b (m.G.obj (s.obj (Fin.last n)))), x.1 = Ideal.Quotient.mk _ (z (s ⋙ m.G)) →
      (show sqM a' b' _ from m.τ _ x).1 = Ideal.Quotient.mk _ (z' s)) : Rep a' b' z' (m.pull n c) := by
  obtain ⟨f, hf, rfl, hv⟩ := hc
  exact rep_cls m f hf z' fun s => h s _ (hv _)

end Gen

theorem dlog_sub {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {N : ℕ} (hN : N ≠ 0) {v : B} (hv : v - 1 ∈ J) :
    CrystallineSemistableComparison.B.dlog δ N v - (v - 1) ∈ pdP δ 2 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  unfold CrystallineSemistableComparison.B.dlog
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, δ.dpow_one hv]
  rw [add_sub_cancel_right]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (dividedPowerFiltration_anti δ (by omega) (dpow_mem_pdP δ _ hv))

theorem dlog_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ) {v : B} (hv : v - 1 ∈ J) :
    CrystallineSemistableComparison.B.dlog δ N v ∈ pdP δ 1 :=
  Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (dividedPowerFiltration_anti δ (by omega) (dpow_mem_pdP δ _ hv))

theorem r_mem {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {D : E.LineData X} {C : Type 1} [Category.{0} C] {G : C ⥤ Thick ((B.schFn q).cr b ht κ)}
    (Lf : B.CLift G D) (s : ComposableArrows C 2) : (Lf.r s).val - 1 ∈ (G.obj (s.obj (Fin.last 2))).J := by
  have hfg : s.map' 0 2 = s.map' 0 1 ≫ s.map' 1 2 := s.map'_comp 0 1 2
  have := CocCls.red_Rf Lf (s.map' 0 1) (s.map' 1 2)
  rw [← hfg] at this
  exact CocCls.sub_one_mem this

section Lat
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens)

theorem le_top' : TS γ q l s 𝒱 ≤ TS γ q l s {⊤} := fun _ h => ⟨h.1, ⊤, rfl, fun _ _ => trivial⟩

abbrev G0 : (TS γ q l s 𝒱).FullSubcategory ⥤ Thick ((B.schFn q).cr (nlBase A I γ 0) rfl (κA O I)) := (TS γ q l s 𝒱).ι

abbrev Lf (D : E.LineData X) : Type 1 :=
  B.CLift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) (G0 γ q l s 𝒱) D

variable {γ q l s 𝒱}

def zz {D : E.LineData X} (Λ : Lf γ q l s 𝒱 D) (t : ComposableArrows (TS γ q l s 𝒱).FullSubcategory 2) :
    (sP (TS γ q l s 𝒱)).A.obj (t.obj (Fin.last 2)) := ((show (t.obj (Fin.last 2)).obj.B from (Λ.r t).val) - 1 : (t.obj (Fin.last 2)).obj.B)


variable (𝒱) in
abbrev resG (r j : ℕ) (z : HG (TS γ q l s {⊤}) r j) : HG (TS γ q l s 𝒱) r j :=
  ((incl (le_top' γ q l s 𝒱)).sq (incl_fil _ (r : ℤ)) (incl_fil _ ((r : ℤ) + 1))).pull j z

theorem zarT (h : sSup 𝒱 = ⊤) (j : ℕ) :
    (∀ r r' : ℤ, Function.Bijective (((incl (le_top' γ q l s 𝒱)).sq (incl_fil _ r) (incl_fil _ r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : A), Function.Bijective (((incl (le_top' γ q l s 𝒱)).sq (incl_std _ r c) (incl_std _ r' c')).pull j)) :=
  have := zar (TF l s) (Or.inl ⟨rfl, l, s, rfl⟩) 𝒱 {⊤} (le_top' γ q l s 𝒱) (by rintro W rfl; rw [h]) j
  ⟨this.1, this.2.1⟩

theorem z_ex {D : E.LineData X} (h : sSup 𝒱 = ⊤) (hs : s ≠ 0) (Λ : Lf γ q l s 𝒱 D) :
    ∃ z : HG (TS γ q l s {⊤}) 1 2, Pb.Rep (sFil (TS γ q l s 𝒱) ((1 : ℕ) : ℤ)) (sFil _ (((1 : ℕ) : ℤ) + 1)) (zz Λ) (resG 𝒱 1 2 z) := by
  have hz := CocCls.closed Λ (RingHom.id A) s fun T k hk x hx => CrystallineFirstChernTorsionFree.dpow_vanish T.property.1 k hk x hx
  obtain ⟨c, hc⟩ := rep_of_closed (sFil (TS γ q l s 𝒱) ((1 : ℕ) : ℤ)) (sFil _ (((1 : ℕ) : ℤ) + 1)) (Λ.coc (RingHom.id A) s) hz
    fun t => dlog_mem (t.obj (Fin.last 2)).obj.δ s (r_mem Λ t)
  obtain ⟨z, rfl⟩ := ((zarT h 2).1 _ _).2 c
  exact ⟨z, rep_congr (fun t => dlog_sub (t.obj (Fin.last 2)).obj.δ hs (r_mem Λ t)) hc⟩

section Red
variable {R : Type} [CommRing R] {I' : Ideal R} {γ' : DividedPowers I'} {κ' : O →+* R ⧸ I'} {n : ℕ} (d : RedIn γ' κ' γ l n)

abbrev Gr : (TS γ q l s 𝒱).FullSubcategory ⥤ Thick ((B.schFn q).cr (nlBase R I' γ' l) rfl κ') := redG q s d 𝒱

def redL {D : E.LineData X} (Λ : Lf γ q l s 𝒱 D) :
    B.CLift (q := q) (b := nlBase R I' γ' l) (ht := rfl) (κ := κ') (Gr (q := q) (s := s) (𝒱 := 𝒱) d) D where
  p T := Spec.map (CommRingCat.ofHom (qBar T.obj l n)) ≫ Λ.p T
  hp T := by
    rw [Category.assoc]
    exact congrArg (Spec.map (CommRingCat.ofHom (qBar T.obj l n)) ≫ ·) (Λ.hp T)
  w {T T'} φ := Units.map (Ideal.Quotient.mk (lnT T'.obj l n)).toMonoidHom (Λ.w φ)
  hw {T T'} φ h := by
    have e : B.thSp ((Gr d).map φ) ≫ Spec.map (CommRingCat.ofHom (qBar T.obj l n)) ≫ Λ.p T =
        Spec.map (CommRingCat.ofHom (qBar T'.obj l n)) ≫ B.thSp ((G0 γ q l s 𝒱).map φ) ≫ Λ.p T := by
      unfold B.thSp
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
    have h' : (Spec.map (CommRingCat.ofHom (qBar T'.obj l n)) ≫ B.thSp ((G0 γ q l s 𝒱).map φ) ≫ Λ.p T) ≫ D.f =
        (Spec.map (CommRingCat.ofHom (qBar T'.obj l n)) ≫ Λ.p T') ≫ D.f := e ▸ h
    have k1 := congrArg Units.val (CocCls.uq_map D (qBar T'.obj l n) _ _ (CocCls.hh Λ φ) h')
    have k2 := congrArg (qBar T'.obj l n) (Λ.hw φ (CocCls.hh Λ φ))
    exact (k2.trans k1.symm).trans (FirstChernPullback.u_congr D e.symm rfl h' h)

variable {Λ₀ : Type} [CommRing Λ₀] (c : Λ₀ →+* R) (lam : Λ₀ →+* A) (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))

theorem res_red (r j : ℕ) (a : A) (z : HG (TS γ q l s {⊤}) r j) :
    ((incl (le_top' γ q l s 𝒱)).sq (incl_std _ (some (r : ℤ)) a) (incl_std _ (some ((r : ℤ) + 1)) a)).pull j
      (redG' (TS γ q l s {⊤}) a r j z) = redG' (TS γ q l s 𝒱) a r j (resG 𝒱 r j z) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun t => ?_))
  obtain ⟨y, hy, e⟩ := sq_surj _ _ (z.1 (t ⋙ (incl (le_top' γ q l s 𝒱)).G))
  change ((incl (le_top' γ q l s 𝒱)).sq (incl_std _ (some (r : ℤ)) a) (incl_std _ (some ((r : ℤ) + 1)) a)).τ _
      ((sqLe (fun _ => le_sup_left) fun _ => le_sup_left).τ _ (z.1 (t ⋙ (incl (le_top' γ q l s 𝒱)).G))) =
    (sqLe (fun _ => le_sup_left) fun _ => le_sup_left).τ _
      (((incl (le_top' γ q l s 𝒱)).sq (incl_fil _ (r : ℤ)) (incl_fil _ ((r : ℤ) + 1))).τ _ (z.1 (t ⋙ (incl (le_top' γ q l s 𝒱)).G)))
  rw [← e]
  rfl

def redSub' (r : ℕ) : CH.Mor (redG q s d 𝒱 ⋙ (B.pdS (nlFun γ' l X q κ') c r).fn)
    (sq (stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)) (stdI (TS γ q l s 𝒱) (some ((r : ℤ) + 1)) ((l : A) ^ n))) lam where
  G := 𝟭 _
  τ T := (redSub q s 𝒱 d c lam hc r).τ T
  nat φ x := (redSub q s 𝒱 d c lam hc r).nat φ x

theorem id_q {B : Type} [CommRing B] (J : Ideal B) (h) (w : B ⧸ J) : Ideal.quotientMap J (RingHom.id B) h w = w := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
  rfl

theorem res_sub (r j : ℕ) (x : CH.H (B.pdS (nlFun γ' l X q κ') c r).fn j) :
    ((incl (le_top' γ q l s 𝒱)).sq (incl_std _ (some (r : ℤ)) ((l : A) ^ n)) (incl_std _ (some ((r : ℤ) + 1)) ((l : A) ^ n))).pull j
      ((redSub q s {⊤} d c lam hc r).pull j x) =
    (redSub' d c lam hc r).pull j ((CH.Mor.restrict _ (redG q s d 𝒱)).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun t => Subtype.ext (id_q _ _ _)))

theorem val_eq (hl : l ≠ 0) (T : (TS γ q l s 𝒱).FullSubcategory) {v : T.obj.B} (hv : v - 1 ∈ T.obj.J) :
    Ideal.Quotient.factor (ln_le (n := n) q s 𝒱 (some (((1 : ℕ) : ℤ) + 1)) T)
      (CrystallineSemistableComparison.B.dlog (redδ T.obj T.property.1 n) (l * n) (Ideal.Quotient.mk _ v)) = Ideal.Quotient.mk _ (v - 1) := by
  rw [← CocCls.dlog_map (redδ_dp T.obj T.property.1 n) (l * n) hv]
  refine Ideal.Quotient.eq.2 ?_
  rcases eq_or_ne n 0 with rfl | hn
  · refine ln_le (n := 0) q s 𝒱 _ T ?_
    rw [lnT, pow_zero, Ideal.span_singleton_one]; trivial
  · exact Ideal.mem_sup_left (dlog_sub T.obj.δ (mul_ne_zero hl hn) hv)

theorem red_eq {D : E.LineData X} (h : sSup 𝒱 = ⊤) (Λ : Lf γ q l s 𝒱 D) (z : HG (TS γ q l s {⊤}) 1 2)
    (hz : Pb.Rep (sFil (TS γ q l s 𝒱) ((1 : ℕ) : ℤ)) (sFil _ (((1 : ℕ) : ℤ) + 1)) (zz Λ) (resG 𝒱 1 2 z))
    (x : CH.H (B.pdS (nlFun γ' l X q κ') c 1).fn 2) (f : CH.Cn (redG q s d 𝒱 ⋙ (B.pdS (nlFun γ' l X q κ') c 1).fn) 2)
    (hf : CH.d _ 2 f = 0) (hv : ∀ t, Subtype.val (f t) = (redL d Λ).coc c (l * n) t)
    (hx : (CH.cx _).cls f hf = (CH.Mor.restrict _ (redG q s d 𝒱)).pull 2 x) :
    redG' (TS γ q l s {⊤}) ((l : A) ^ n) 1 2 z = (redSub q s {⊤} d c lam hc 1).pull 2 x := by
  refine ((zarT h 2).2 _ _ _ _).1 ?_
  rw [res_red, res_sub, ← hx]
  refine rep_uniq (z := zz Λ) (rep_pull _ hz _ fun t y hy => ?_) (rep_cls _ f hf _ fun t => ?_)
  · obtain ⟨y, hy'⟩ := y
    dsimp only at hy
    subst hy
    rfl
  · change Ideal.Quotient.factor (ln_le (n := n) q s 𝒱 (some (((1 : ℕ) : ℤ) + 1)) (t.obj (Fin.last 2))) (Subtype.val (f t)) = _
    rw [hv]
    exact val_eq d.hl (t.obj (Fin.last 2)) (r_mem Λ t)

theorem red_eq' {D : E.LineData X} (h : sSup 𝒱 = ⊤) (Λ : Lf γ q l s 𝒱 D) (z : HG (TS γ q l s {⊤}) 1 2)
    (hz : Pb.Rep (sFil (TS γ q l s 𝒱) ((1 : ℕ) : ℤ)) (sFil _ (((1 : ℕ) : ℤ) + 1)) (zz Λ) (resG 𝒱 1 2 z))
    (x : CH.H (B.pdS ((B.schFn q).cr (nlBase R I' γ' l) rfl κ') c 1).fn 2)
    (hx : ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr (nlBase R I' γ' l) rfl κ'))
      (Λ : B.CLift (q := q) (b := nlBase R I' γ' l) (ht := rfl) (κ := κ') G D),
      ∃ (z : CH.Cn (G ⋙ (B.pdS ((B.schFn q).cr (nlBase R I' γ' l) rfl κ') c 1).fn) 2) (hz : CH.d _ 2 z = 0),
        (∀ s, (show (B.pdS ((B.schFn q).cr (nlBase R I' γ' l) rfl κ') c 1).S _ from z s).1 = Λ.coc c (l * n) s) ∧
        (CH.cx _).cls z hz = (CH.Mor.restrict (B.pdS ((B.schFn q).cr (nlBase R I' γ' l) rfl κ') c 1).fn G).pull 2 x)
    (mm : CH.Mor (B.pdS ((B.schFn q).cr (nlBase R I' γ' l) rfl κ') c 1).fn
      (sq (stdI (TS γ q l s {⊤}) (some ((1 : ℕ) : ℤ)) ((l : A) ^ n)) (stdI (TS γ q l s {⊤}) (some (((1 : ℕ) : ℤ) + 1)) ((l : A) ^ n))) lam)
    (hmm : mm = redSub q s {⊤} d c lam hc 1) :
    redG' (TS γ q l s {⊤}) ((l : A) ^ n) 1 2 z = mm.pull 2 x := by
  subst hmm
  obtain ⟨f, hf, hv, e⟩ := hx _ (Gr d) (redL d Λ)
  exact red_eq d c lam hc h Λ z hz x f hf hv e

end Red

end Lat

section Rat
variable {O A K B : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing K] [CommRing B] [Algebra K B] {I : Ideal A}
  {γ : DividedPowers I} {IB : Ideal B} {γB : DividedPowers IB} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {q' : X' ⟶ Spec (CommRingCat.of K)} {ι : A →+* B} (m : NMor γ q (κA O I) γB q' (κA K IB) ι) {l s : ℕ}
  (hm : ∀ T, TS γB q' 1 s {⊤} T → TS γ q l s {⊤} ((m.mor 0).obj T)) (D : E.LineData X)

abbrev 𝒲 : Set X'.Opens := (fun V : X.Opens => m.u ⁻¹ᵁ V) '' 𝒱D D

include hm in
theorem hm' (T : Thick (nlFun γB 0 X' q' (κA K IB))) (h : TS γB q' 1 s (𝒲 m D) T) : TS γ q l s (𝒱D D) ((m.mor 0).obj T) := by
  obtain ⟨h1, -, ⟨V, hV, rfl⟩, hT⟩ := h
  exact ⟨(hm T ⟨h1, ⊤, rfl, fun _ _ => trivial⟩).1, V, hV, hT⟩

abbrev sm' : SMor (sP (TS γ q l s (𝒱D D))) (sP (TS γB q' 1 s (𝒲 m D))) ι := m.smor _ _ (hm' m hm D)

abbrev gK (s : ℕ) : (TS γB q' 1 s (𝒲 m D)).FullSubcategory ⥤ Thick (smFun X' q') := (kS γB q' (TS γB q' 1 s (𝒲 m D))).G

theorem pt_gK (T : (TS γB q' 1 s (𝒲 m D)).FullSubcategory) : pt ((gK m D s).obj T) = pt T.obj := Category.comp_id _

def liftK (Λ : Lf γ q l s (𝒱D D) D) : CLiftK (gK m D s) (D.pb m.u) where
  p T := pullback.lift (Λ.p ((sm' m hm D).G.obj T)) (pt T.obj) (Λ.hp ((sm' m hm D).G.obj T))
  hp T := (pullback.lift_snd _ _ _).trans (pt_gK m D T).symm
  w φ := Λ.w ((sm' m hm D).G.map φ)
  hw {T T'} φ h := by
    refine (Λ.hw ((sm' m hm D).G.map φ) (CocCls.hh Λ _)).trans (FirstChernPullback.u_congr D ?_ ?_ _ _)
    · rw [Category.assoc, pullback.lift_fst]; rfl
    · exact (pullback.lift_fst _ _ _).symm

theorem res_b (r j : ℕ) (z : HG (TS γ q l s {⊤}) r j) :
    resG (𝒲 m D) r j (((m.smor _ _ hm).sq (a := sFil _ r) (b := sFil _ ((r : ℤ) + 1)) (a' := sFil _ r) (b' := sFil _ ((r : ℤ) + 1))
      (fun _ _ hx => hx) fun _ _ hx => hx).pull j z) =
    ((sm' m hm D).sq (a := sFil _ r) (b := sFil _ ((r : ℤ) + 1)) (a' := sFil _ r) (b' := sFil _ ((r : ℤ) + 1))
      (fun _ _ hx => hx) fun _ _ hx => hx).pull j (resG (𝒱D D) r j z) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

variable {t : B} (ht : t ∈ IB)

def muM (Q : ObjectProperty (Thick (nlFun γB 0 X' q' (κA K IB)))) (a r : ℕ) :
    CH.Mor (grT (smFun X' q') a) (sq (sFil Q r) (sFil Q ((r : ℤ) + 1))) (algebraMap K B) :=
  (kS γB q' Q).sqC (t ^ (r - a)) (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := sFil Q r) (b' := sFil Q ((r : ℤ) + 1))
    (fun T _ hx => fil_mul_le (b := nlBase B IB γB 0) ht (r := a) (r' := r) (by omega) T.obj hx)
    fun T _ hx => fil_mul_le (b := nlBase B IB γB 0) ht (r := a + 1) (r' := r + 1) (by omega) T.obj hx

def muM' (Q : ObjectProperty (Thick (nlFun γB 0 X' q' (κA K IB)))) (a r : ℕ) :
    CH.Mor (sq ((thFil (smFun X' q') (a : ℤ)).res (kS γB q' Q).G) ((thFil (smFun X' q') ((a : ℤ) + 1)).res (kS γB q' Q).G))
      (sq (sFil Q r) (sFil Q ((r : ℤ) + 1))) (algebraMap K B) where
  G := 𝟭 _
  τ T := (muM ht Q a r).τ T
  nat φ x := (muM ht Q a r).nat φ x

theorem res_mu (𝒱 : Set X'.Opens) (a r j : ℕ) (y : Hdg q' a j) :
    resG 𝒱 r j (muG γB q' (TS γB q' 1 s {⊤}) ht a r j y) =
      (muM' ht (TS γB q' 1 s 𝒱) a r).pull j ((CH.Mor.restrict (grT (smFun X' q') a) (kS γB q' (TS γB q' 1 s 𝒱)).G).pull j y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun t => Subtype.ext (id_q _ _ _)))

theorem b_eq (hD : sSup (𝒱D D) = ⊤) (Λ : Lf γ q l s (𝒱D D) D) (z : HG (TS γ q l s {⊤}) 1 2)
    (hz : Pb.Rep (sFil (TS γ q l s (𝒱D D)) ((1 : ℕ) : ℤ)) (sFil _ (((1 : ℕ) : ℤ) + 1)) (zz Λ) (resG (𝒱D D) 1 2 z))
    (c : Hdg q' 1 2) (hc : IsDlogFirstChernClass q' (D.pb m.u) c) :
    muG γB q' (TS γB q' 1 s {⊤}) ht 1 1 2 c =
      ((m.smor _ _ hm).sq (a := sFil _ ((1 : ℕ) : ℤ)) (b := sFil _ (((1 : ℕ) : ℤ) + 1)) (a' := sFil _ ((1 : ℕ) : ℤ))
        (b' := sFil _ (((1 : ℕ) : ℤ) + 1)) (fun _ _ hx => hx) fun _ _ hx => hx).pull 2 z := by
  refine ((zarT (FirstChernPullback.sSup_preimage _ m.u hD) 2).1 _ _).1 ?_
  have hr := hc _ (gK m D s) (fun T => by
    obtain ⟨T, -, -, ⟨V, hV, rfl⟩, hT⟩ := T
    refine ⟨_, FirstChernPullback.mem_VD_pb D m.u hV, ?_⟩
    unfold InU
    rw [pt_gK]
    exact hT) (liftK m hm D Λ)
  refine (res_mu ht _ 1 1 2 c).trans (Eq.trans ?_ (res_b m hm D 1 2 z).symm)
  refine rep_uniq (z := fun u => zz Λ (u ⋙ (sm' m hm D).G)) (rep_pull _ hr _ fun u y hy => ?_) (rep_pull _ hz _ fun u y hy => ?_)
  · obtain ⟨y, hy'⟩ := y
    dsimp only at hy
    subst hy
    refine congrArg (Ideal.Quotient.mk _) ?_
    change (u.obj (Fin.last 2)).obj.i (t ^ (1 - 1)) * _ = _
    rw [Nat.sub_self, pow_zero, map_one, one_mul]
    rfl
  · exact (id_q _ _ _).trans hy

end Rat

theorem pz {R : Type} {N : Type 1} [CommRing R] [AddCommGroup N] [Module R N] (a : R) (x : N) : a ^ 0 • x = x := by
  rw [pow_zero, one_smul]

end FirstChernHodgeTateFacts

open FirstChernHodgeTateFacts in
theorem firstChern_hodgeTate_rho (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : FirstChernHodgeTateCompat l K := by
  intro Y m L M hm D hD x c hx hc
  obtain ⟨Λ⟩ : Nonempty (Lf L.γ M.p l m (𝒱D D) D) :=
    clift_ex (G0 L.γ M.p l m (𝒱D D)) D fun T => CrystallineFirstChernTorsionFree.lifts_of_mem D T.obj T.property.2
  obtain ⟨z, hz⟩ := z_ex hD (by omega) Λ
  refine ⟨0, z, fun n => ?_, ?_⟩
  · exact (red_eq' (L.d n) (Y.c n) L.lam (L.d_lam n) hD Λ z hz (x n) (hx n) (L.rS M 1 n) rfl).trans (pz _ _).symm
  · exact (pz _ _).trans (b_eq (L.nmB M) (L.nmB_mem M) D L.tB_mem hD Λ z hz c hc)

end CrystallineSemistableComparison.HT
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.PowZeroSmul
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.RedSubVal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.Mul

open Pb

theorem pull_sqC {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄] {C₁ C₂ C₃ C₄ : Type 1}
    [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄] {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂}
    {F₃ : C₃ ⥤ ModuleCat.{0} R₃} {F₄ : C₄ ⥤ ModuleCat.{0} R₄} {σa : R₁ →+* R₂} {σb : R₂ →+* R₄} {σc : R₁ →+* R₃} {σd : R₃ →+* R₄}
    (a : CH.Mor F₁ F₂ σa) (b : CH.Mor F₂ F₄ σb) (c : CH.Mor F₁ F₃ σc) (d : CH.Mor F₃ F₄ σd) (n : ℕ)
    (h : ∀ f s, b.pullC n (a.pullC n f) s = d.pullC n (c.pullC n f) s) (x : CH.H F₁ n) :
    b.pull n (a.pull n x) = d.pull n (c.pull n x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => h z.1 s))

theorem pull_triC {R₁ R₂ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₄] {C₁ C₂ C₄ : Type 1}
    [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₄] {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂}
    {F₄ : C₄ ⥤ ModuleCat.{0} R₄} {σa : R₁ →+* R₂} {σb : R₂ →+* R₄} {σc : R₁ →+* R₄}
    (a : CH.Mor F₁ F₂ σa) (b : CH.Mor F₂ F₄ σb) (c : CH.Mor F₁ F₄ σc) (n : ℕ)
    (h : ∀ f s, b.pullC n (a.pullC n f) s = c.pullC n f s) (x : CH.H F₁ n) :
    b.pull n (a.pull n x) = c.pull n x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => h z.1 s))

theorem cup_smul {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
    {p q n : ℕ} (h : p + q = n) (a b : R) (x : CH.H F₁ p) (y : CH.H F₂ q) : P.cup h (a • x) (b • y) = (a * b) • P.cup h x y := by
  obtain ⟨B, hB⟩ := CrystallineSemistableComparison.P.cup_bilin P h
  rw [← hB, ← hB, map_smul, map_smul, LinearMap.smul_apply, smul_smul, mul_comm]

section SM
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R' C'}
  {σ : R →+* R'} (m : SMor Φ Φ' σ) {a₁ b₁ a₂ b₂ a₃ b₃ : IdF Φ.A} {a₁' b₁' a₂' b₂' a₃' b₃' : IdF Φ'.A}
  (h : MulOk a₁ b₁ a₂ b₂ a₃ b₃) (h' : MulOk a₁' b₁' a₂' b₂' a₃' b₃')

theorem pair_mk {A : C ⥤ CommAlgCat.{0} R} {a b a' b' a'' b'' : IdF A} (h : MulOk a b a' b' a'' b'') (T : C) (x y : A.obj T)
    (hx : x ∈ a.S T) (hy : y ∈ a'.S T) : h.pair.μ T (sqMk a b x hx) (sqMk a' b' y hy) = sqMk a'' b'' (x * y) (h.aa T hx hy) :=
  h.mul_mk x y hx hy

theorem sq_cup (h₁ : m.Le a₁ a₁') (k₁ : m.Le b₁ b₁') (h₂ : m.Le a₂ a₂') (k₂ : m.Le b₂ b₂') (h₃ : m.Le a₃ a₃') (k₃ : m.Le b₃ b₃')
    {p q n : ℕ} (e : p + q = n) (x : CH.H (sq a₁ b₁) p) (y : CH.H (sq a₂ b₂) q) :
    (m.sq h₃ k₃).pull n (h.pair.cup e x y) = h'.pair.cup e ((m.sq h₁ k₁).pull p x) ((m.sq h₂ k₂).pull q y) := by
  refine CrystallineSemistableComparison.P.cup_pull h.pair h'.pair m.G (m.sq h₁ k₁).τ (m.sq h₂ k₂).τ (m.sq h₃ k₃).τ (m.sq h₁ k₁).nat (m.sq h₂ k₂).nat
    (m.sq h₃ k₃).nat (fun T x y => ?_) e x y
  obtain ⟨x, hx, rfl⟩ := sq_surj a₁ b₁ x
  obtain ⟨y, hy, rfl⟩ := sq_surj a₂ b₂ y
  refine (congrArg ((m.sq h₃ k₃).τ T) (pair_mk h _ x y hx hy)).trans ?_
  refine Eq.trans ?_ (pair_mk h' T (m.ρ T x) (m.ρ T y) (h₁ T x hx) (h₂ T y hy)).symm
  exact Subtype.ext (congrArg (Ideal.Quotient.mk _) (map_mul (m.ρ T) x y))

theorem sqC_cup (c₁ c₂ c₃ : R') (hc : c₃ = c₁ * c₂) (h₁ : m.LeC c₁ a₁ a₁') (k₁ : m.LeC c₁ b₁ b₁') (h₂ : m.LeC c₂ a₂ a₂')
    (k₂ : m.LeC c₂ b₂ b₂') (h₃ : m.LeC c₃ a₃ a₃') (k₃ : m.LeC c₃ b₃ b₃')
    {p q n : ℕ} (e : p + q = n) (x : CH.H (sq a₁ b₁) p) (y : CH.H (sq a₂ b₂) q) :
    (m.sqC c₃ h₃ k₃).pull n (h.pair.cup e x y) = h'.pair.cup e ((m.sqC c₁ h₁ k₁).pull p x) ((m.sqC c₂ h₂ k₂).pull q y) := by
  refine CrystallineSemistableComparison.P.cup_pull h.pair h'.pair m.G (m.sqC c₁ h₁ k₁).τ (m.sqC c₂ h₂ k₂).τ (m.sqC c₃ h₃ k₃).τ (m.sqC c₁ h₁ k₁).nat
    (m.sqC c₂ h₂ k₂).nat (m.sqC c₃ h₃ k₃).nat (fun T x y => ?_) e x y
  obtain ⟨x, hx, rfl⟩ := sq_surj a₁ b₁ x
  obtain ⟨y, hy, rfl⟩ := sq_surj a₂ b₂ y
  refine (congrArg ((m.sqC c₃ h₃ k₃).τ T) (pair_mk h _ x y hx hy)).trans ?_
  refine Eq.trans ?_ (pair_mk h' T _ _ (h₁ T x hx) (h₂ T y hy)).symm
  refine Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)
  change algebraMap R' _ c₃ * m.ρ T (x * y) = _
  rw [hc, map_mul, map_mul]; ring

theorem le_cup {A : C ⥤ CommAlgCat.{0} R} {a₁ b₁ a₂ b₂ a₃ b₃ a₁' b₁' a₂' b₂' a₃' b₃' : IdF A}
    (h : MulOk a₁ b₁ a₂ b₂ a₃ b₃) (h' : MulOk a₁' b₁' a₂' b₂' a₃' b₃')
    (h₁ : ∀ T, a₁.S T ≤ a₁'.S T) (k₁ : ∀ T, b₁.S T ≤ b₁'.S T) (h₂ : ∀ T, a₂.S T ≤ a₂'.S T) (k₂ : ∀ T, b₂.S T ≤ b₂'.S T)
    (h₃ : ∀ T, a₃.S T ≤ a₃'.S T) (k₃ : ∀ T, b₃.S T ≤ b₃'.S T)
    {p q n : ℕ} (e : p + q = n) (x : CH.H (sq a₁ b₁) p) (y : CH.H (sq a₂ b₂) q) :
    (sqLe h₃ k₃).pull n (h.pair.cup e x y) = h'.pair.cup e ((sqLe h₁ k₁).pull p x) ((sqLe h₂ k₂).pull q y) := by
  refine CrystallineSemistableComparison.P.cup_pull h.pair h'.pair (𝟭 C) (sqLe h₁ k₁).τ (sqLe h₂ k₂).τ (sqLe h₃ k₃).τ (sqLe h₁ k₁).nat
    (sqLe h₂ k₂).nat (sqLe h₃ k₃).nat (fun T x y => ?_) e x y
  obtain ⟨x, hx, rfl⟩ := sq_surj a₁ b₁ x
  obtain ⟨y, hy, rfl⟩ := sq_surj a₂ b₂ y
  refine (congrArg ((sqLe h₃ k₃).τ T) (pair_mk h _ x y hx hy)).trans ?_
  exact (pair_mk h' T x y (h₁ T hx) (h₂ T hy)).symm

theorem sq_sh (c : R) (c' : R') (hc : σ c = c') (h₁ : (idS Φ).LeC c a₁ a₂) (k₁ : (idS Φ).LeC c b₁ b₂) (h₂ : m.Le a₂ a₂')
    (k₂ : m.Le b₂ b₂') (h₃ : m.Le a₁ a₁') (k₃ : m.Le b₁ b₁') (h₄ : (idS Φ').LeC c' a₁' a₂') (k₄ : (idS Φ').LeC c' b₁' b₂')
    (n : ℕ) (x : CH.H (sq a₁ b₁) n) :
    (m.sq h₂ k₂).pull n (((idS Φ).sqC c h₁ k₁).pull n x) = ((idS Φ').sqC c' h₄ k₄).pull n ((m.sq h₃ k₃).pull n x) := by
  have key : ∀ (T : C') (x : sqM a₁ b₁ (m.G.obj T)), (m.sq h₂ k₂).τ T (((idS Φ).sqC c h₁ k₁).τ (m.G.obj T) x) =
      ((idS Φ').sqC c' h₄ k₄).τ T ((m.sq h₃ k₃).τ T x) := by
    intro T x
    obtain ⟨x, hx, rfl⟩ := sq_surj a₁ b₁ x
    refine Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)
    change m.ρ T (algebraMap R _ c * x) = algebraMap R' _ c' * m.ρ T x
    rw [map_mul, m.comm, hc]
  exact pull_sqC _ _ _ _ n (fun f s => key _ (f (s ⋙ m.G))) x

theorem sqC_sh (c c' c'' : R') (hc : c'' = c' * c) (h₁ : m.LeC c a₁ a₁') (k₁ : m.LeC c b₁ b₁') (h₂ : (idS Φ').LeC c' a₁' a₂')
    (k₂ : (idS Φ').LeC c' b₁' b₂') (h₃ : m.LeC c'' a₁ a₂') (k₃ : m.LeC c'' b₁ b₂') (n : ℕ) (x : CH.H (sq a₁ b₁) n) :
    ((idS Φ').sqC c' h₂ k₂).pull n ((m.sqC c h₁ k₁).pull n x) = (m.sqC c'' h₃ k₃).pull n x := by
  have key : ∀ (T : C') (x : sqM a₁ b₁ (m.G.obj T)), ((idS Φ').sqC c' h₂ k₂).τ T ((m.sqC c h₁ k₁).τ T x) = (m.sqC c'' h₃ k₃).τ T x := by
    intro T x
    obtain ⟨x, hx, rfl⟩ := sq_surj a₁ b₁ x
    refine Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)
    change algebraMap R' _ c' * (algebraMap R' _ c * m.ρ T x) = algebraMap R' _ c'' * m.ρ T x
    rw [hc, map_mul, mul_assoc]
  exact pull_triC _ _ _ n (fun f s => key _ (f (s ⋙ m.G))) x

theorem le_sh {a₁' b₁' a₂' b₂' : IdF Φ.A} (c : R) (h₁ : (idS Φ).LeC c a₁ a₂) (k₁ : (idS Φ).LeC c b₁ b₂) (h₂ : ∀ T, a₂.S T ≤ a₂'.S T)
    (k₂ : ∀ T, b₂.S T ≤ b₂'.S T) (h₃ : ∀ T, a₁.S T ≤ a₁'.S T) (k₃ : ∀ T, b₁.S T ≤ b₁'.S T) (h₄ : (idS Φ).LeC c a₁' a₂')
    (k₄ : (idS Φ).LeC c b₁' b₂') (n : ℕ) (x : CH.H (sq a₁ b₁) n) :
    (sqLe h₂ k₂).pull n (((idS Φ).sqC c h₁ k₁).pull n x) = ((idS Φ).sqC c h₄ k₄).pull n ((sqLe h₃ k₃).pull n x) := by
  have key : ∀ (T : C) (x : sqM a₁ b₁ T), (sqLe h₂ k₂).τ T (((idS Φ).sqC c h₁ k₁).τ T x) =
      ((idS Φ).sqC c h₄ k₄).τ T ((sqLe h₃ k₃).τ T x) := by
    intro T x
    obtain ⟨x, hx, rfl⟩ := sq_surj a₁ b₁ x
    rfl
  exact pull_sqC _ _ _ _ n (fun f s => key _ (f s)) x

end SM

theorem sup_mul {B : Type} [CommRing B] {I J P N : Ideal B} (h : ∀ x ∈ I, ∀ y ∈ J, x * y ∈ P) {x y : B} (hx : x ∈ I ⊔ N)
    (hy : y ∈ J ⊔ N) : x * y ∈ P ⊔ N := by
  obtain ⟨a, ha, n, hn, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨b, hb, n', hn', rfl⟩ := Submodule.mem_sup.1 hy
  have : (a + n) * (b + n') = a * b + (a * n' + n * (b + n')) := by ring
  rw [this]
  exact Submodule.add_mem_sup (h a ha b hb) (add_mem (N.mul_mem_left _ hn') (N.mul_mem_right _ hn))

theorem mul_sup {B : Type} [CommRing B] {I P N : Ideal B} {c : B} (h : ∀ x ∈ I, c * x ∈ P) {x : B} (hx : x ∈ I ⊔ N) :
    c * x ∈ P ⊔ N := by
  obtain ⟨a, ha, n, hn, rfl⟩ := Submodule.mem_sup.1 hx
  rw [mul_add]
  exact Submodule.add_mem_sup (h a ha) (N.mul_mem_left _ hn)

section Base
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

theorem okm (c : b.R) {a a' s : ℕ} (h : a + a' = s) :
    MulOk (stdI Q (some (a : ℤ)) c) (stdI Q (some ((a : ℤ) + 1)) c) (stdI Q (some (a' : ℤ)) c) (stdI Q (some ((a' : ℤ) + 1)) c)
      (stdI Q (some (s : ℤ)) c) (stdI Q (some ((s : ℤ) + 1)) c) :=
  ⟨fun T _ _ hx hy => sup_mul (fun _ hx _ hy => (grOkQ Q h).aa T hx hy) hx hy,
    fun T _ _ hx hy => sup_mul (fun _ hx _ hy => (grOkQ Q h).ab T hx hy) hx hy,
    fun T _ _ hx hy => sup_mul (fun _ hx _ hy => (grOkQ Q h).ba T hx hy) hx hy⟩

theorem lem {t : b.R} (ht : t ∈ b.I) (c : b.R) {r r' k : ℕ} (h : r' ≤ r + k) :
    (idS (sP Q)).LeC (t ^ k) (stdI Q (some (r : ℤ)) c) (stdI Q (some (r' : ℤ)) c) :=
  fun T _ hx => mul_sup (fun _ hx => fil_mul_le ht h T.obj hx) hx

def shm {t : b.R} (ht : t ∈ b.I) (c : b.R) {r r' : ℕ} (k : ℕ) (h : r + k = r') :
    CH.Mor (sq (stdI Q (some (r : ℤ)) c) (stdI Q (some ((r : ℤ) + 1)) c)) (sq (stdI Q (some (r' : ℤ)) c) (stdI Q (some ((r' : ℤ) + 1)) c))
      (RingHom.id _) :=
  (idS (sP Q)).sqC (t ^ k) (lem Q ht c (r := r) (r' := r') (by omega)) (lem Q ht c (r := r + 1) (r' := r' + 1) (by omega))

theorem red_sh {t : b.R} (ht : t ∈ b.I) (c : b.R) {r r' : ℕ} (k : ℕ) (h : r + k = r') (j : ℕ) (z : HG Q r j) :
    redG' Q c r' j (shG Q ht k h j z) = (shm Q ht c k h).pull j (redG' Q c r j z) :=
  le_sh (Φ := sP Q) (t ^ k) _ _ _ _ _ _ _ _ j z

theorem red_cup (c : b.R) {r r' s i j : ℕ} (h : r + r' = s) (z : HG Q r i) (z' : HG Q r' j) :
    redG' Q c s (i + j) (cupG Q h z z') = (okm Q c h).pair.cup rfl (redG' Q c r i z) (redG' Q c r' j z') :=
  le_cup (grOkQ Q h) (okm Q c h) _ _ _ _ _ _ rfl z z'

def oneG : HG Q 0 0 :=
  (toSq (sFil Q ((0 : ℕ) : ℤ)) (sFil Q (((0 : ℕ) : ℤ) + 1)) fun T => T.obj.pdPow_zero).pull 0 (CH.oneH (sP Q).A)

end Base

section Red
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] {I : Ideal A} {γ : DividedPowers I}
  {R : Type} [CommRing R] {I' : Ideal R} {γ' : DividedPowers I'} {κ' : O →+* R ⧸ I'} {l n : ℕ}
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (s : ℕ) (𝒱 : Set X.Opens) (d : RedIn γ' κ' γ l n)
  {Λ : Type} [CommRing Λ] (c : Λ →+* R) (lam : Λ →+* A) (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))

theorem redSub_val (r : ℕ) (T : (TS γ q l s 𝒱).FullSubcategory) (x : (B.pdS (nlFun γ' l X q κ') c r).S (redObj T.obj d T.property.1))
    (y : T.obj.B) (hy : x.1 = Ideal.Quotient.mk (lnT T.obj l n) y) :
    Subtype.val ((redSub q s 𝒱 d c lam hc r).τ T x) = Ideal.Quotient.mk _ y := by
  obtain ⟨x, hx⟩ := x
  dsimp only at hy
  subst hy
  rfl

theorem redSub_rep (r : ℕ) (T : (TS γ q l s 𝒱).FullSubcategory) (x : (B.pdS (nlFun γ' l X q κ') c r).S (redObj T.obj d T.property.1)) :
    ∃ y : T.obj.B, y ∈ T.obj.pdPow r ∧ x.1 = Ideal.Quotient.mk (lnT T.obj l n) y := by
  obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1
    (dividedPowerFiltration_red T.obj.δ _ Ideal.Quotient.mk_surjective _ (redδ_dp T.obj T.property.1 n) r
      ((mem_pdS (T := redObj T.obj d T.property.1)).1 x.2))
  exact ⟨y, hy, e.symm⟩

theorem redSub_mk (r : ℕ) (T : (TS γ q l s 𝒱).FullSubcategory) (x : (B.pdS (nlFun γ' l X q κ') c r).S (redObj T.obj d T.property.1))
    (y : T.obj.B) (h : y ∈ (stdI (TS γ q l s 𝒱) (some (r : ℤ)) ((l : A) ^ n)).S T) (hy : x.1 = Ideal.Quotient.mk (lnT T.obj l n) y) :
    (redSub q s 𝒱 d c lam hc r).τ T x = sqMk _ (stdI (TS γ q l s 𝒱) (some ((r : ℤ) + 1)) ((l : A) ^ n)) y h :=
  Subtype.ext (redSub_val q s 𝒱 d c lam hc r T x y hy)

include hc in
theorem i_c (T : (TS γ q l s 𝒱).FullSubcategory) (a : Λ) :
    (redObj T.obj d T.property.1).i (c a) = Ideal.Quotient.mk (lnT T.obj l n) (T.obj.i (lam a)) := by
  change iBar T.obj l n (d.ρ (c a)) = _
  rw [hc]; rfl

theorem redSub_sh {t : Λ} (ht : c t ∈ I') (ht' : lam t ∈ I) {r r' : ℕ} (k : ℕ) (h : r + k = r') (j : ℕ)
    (x : CH.H (B.pdS (nlFun γ' l X q κ') c r).fn j) :
    (redSub q s 𝒱 d c lam hc r').pull j ((pdSh (nlFun γ' l X q κ') c ht k h).pull j x) =
      (shm (TS γ q l s 𝒱) ht' ((l : A) ^ n) k h).pull j ((redSub q s 𝒱 d c lam hc r).pull j x) := by
  have key : ∀ (T : (TS γ q l s 𝒱).FullSubcategory) (x : (B.pdS (nlFun γ' l X q κ') c r).S (redObj T.obj d T.property.1)),
      (redSub q s 𝒱 d c lam hc r').τ T ((pdSh (nlFun γ' l X q κ') c ht k h).τ (redObj T.obj d T.property.1) x) =
        (shm (TS γ q l s 𝒱) ht' ((l : A) ^ n) k h).τ T ((redSub q s 𝒱 d c lam hc r).τ T x) := by
    intro T x
    obtain ⟨y, hy, e⟩ := redSub_rep q s 𝒱 d c r T x
    rw [redSub_mk q s 𝒱 d c lam hc r T x y (Ideal.mem_sup_left hy) e]
    refine Subtype.ext ((redSub_val q s 𝒱 d c lam hc r' T _ (T.obj.i (lam t ^ k) * y) ?_).trans rfl)
    refine Eq.trans (congrArg₂ (fun a b : T.obj.B ⧸ lnT T.obj l n => a * b) (i_c q s 𝒱 d c lam hc T (t ^ k)) e) ?_
    rw [map_pow lam, map_mul]
  exact pull_sqC _ _ _ _ j (fun f s' => key _ (f (s' ⋙ redG q s d 𝒱))) x

theorem redSub_cup {r r' u i j : ℕ} (h : r + r' = u) (x : CH.H (B.pdS (nlFun γ' l X q κ') c r).fn i)
    (y : CH.H (B.pdS (nlFun γ' l X q κ') c r').fn j) :
    (redSub q s 𝒱 d c lam hc u).pull (i + j) ((pdPair (nlFun γ' l X q κ') c h).cup rfl x y) =
      (okm (TS γ q l s 𝒱) ((l : A) ^ n) h).pair.cup rfl ((redSub q s 𝒱 d c lam hc r).pull i x) ((redSub q s 𝒱 d c lam hc r').pull j y) := by
  refine CrystallineSemistableComparison.P.cup_pull (pdPair (nlFun γ' l X q κ') c h) (okm (TS γ q l s 𝒱) ((l : A) ^ n) h).pair (redG q s d 𝒱)
    (redSub q s 𝒱 d c lam hc r).τ (redSub q s 𝒱 d c lam hc r').τ (redSub q s 𝒱 d c lam hc u).τ (redSub q s 𝒱 d c lam hc r).nat
    (redSub q s 𝒱 d c lam hc r').nat (redSub q s 𝒱 d c lam hc u).nat (fun T x y => ?_) rfl x y
  obtain ⟨x', hx, e⟩ := redSub_rep q s 𝒱 d c r T x
  obtain ⟨y', hy, e'⟩ := redSub_rep q s 𝒱 d c r' T y
  refine Eq.trans ?_ (congrArg₂ (fun a b => (okm (TS γ q l s 𝒱) ((l : A) ^ n) h).pair.μ T a b)
    (redSub_mk q s 𝒱 d c lam hc r T x x' (Ideal.mem_sup_left hx) e)
    (redSub_mk q s 𝒱 d c lam hc r' T y y' (Ideal.mem_sup_left hy) e')).symm
  refine Eq.trans ?_ (pair_mk (okm (TS γ q l s 𝒱) ((l : A) ^ n) h) T x' y' _ _).symm
  refine redSub_mk q s 𝒱 d c lam hc u T _ (x' * y') _ ?_
  exact (congrArg₂ (fun a b : T.obj.B ⧸ lnT T.obj l n => a * b) e e').trans (map_mul _ _ _).symm

theorem redSub_one : (redSub q s 𝒱 d c lam hc 0).pull 0 (pdOne (nlFun γ' l X q κ') c) =
    redG' (TS γ q l s 𝒱) ((l : A) ^ n) 0 0 (oneG (TS γ q l s 𝒱)) := by
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s' => Subtype.ext ?_))
  refine (redSub_val q s 𝒱 d c lam hc 0 _ _ 1 ?_).trans rfl
  exact (one_smul Λ _).trans (map_one (Ideal.Quotient.mk (lnT (s'.obj (Fin.last 0)).obj l n))).symm

end Red

end CrystallineSemistableComparison.HT.Mul
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb Mul

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K)

namespace Mul

theorem rS_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (n : ℕ) (x : Y.Fam M r j) :
    (L.rS M r' n).pull j (CB.shS k h x n) = (shm (L.QA M) L.t_mem ((l : L.A) ^ n) k h).pull j ((L.rS M r n).pull j (x n)) :=
  redSub_sh M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n) (Y.ht n) L.t_mem k h j (x n)

theorem rS_cup {r r' s i j : ℕ} (h : r + r' = s) (n : ℕ) (x : Y.Fam M r i) (y : Y.Fam M r' j) :
    (L.rS M s n).pull (i + j) (CB.cupS h x y n) =
      (okm (L.QA M) ((l : L.A) ^ n) h).pair.cup rfl ((L.rS M r n).pull i (x n)) ((L.rS M r' n).pull j (y n)) :=
  redSub_cup M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n) h (x n) (y n)

theorem rS_one (n : ℕ) : (L.rS M 0 n).pull 0 (Y.oneS M n) = redG' (L.QA M) ((l : L.A) ^ n) 0 0 (oneG (L.QA M)) :=
  redSub_one M.p m {⊤} (L.d n) (Y.c n) L.lam (L.d_lam n)

theorem b_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (z : HG (L.QA M) r j) :
    L.bG M r' j (shG (L.QA M) L.t_mem k h j z) = shG (L.QB M) L.tB_mem k h j (L.bG M r j z) :=
  sq_sh ((L.nmB M).smor _ _ (L.nmB_mem M)) (L.lam Y.t ^ k) (L.tB ^ k) (map_pow _ _ _) _ _ _ _ _ _ _ _ j z

theorem b_cup {r r' s i j : ℕ} (h : r + r' = s) (z : HG (L.QA M) r i) (z' : HG (L.QA M) r' j) :
    L.bG M s (i + j) (cupG (L.QA M) h z z') = cupG (L.QB M) h (L.bG M r i z) (L.bG M r' j z') :=
  sq_cup ((L.nmB M).smor _ _ (L.nmB_mem M)) (grOkQ (L.QA M) h) (grOkQ (L.QB M) h) _ _ _ _ _ _ rfl z z'

theorem b_one : L.bG M 0 0 (oneG (L.QA M)) = L.μ M 0 0 0 (oneH M.q) := by
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)))
  change (1 : (s.obj (Fin.last 0)).obj.B) = (s.obj (Fin.last 0)).obj.i (L.tB ^ (0 - 0)) * 1
  rw [Nat.sub_self, pow_zero, map_one, mul_one]

theorem lifts_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) (e : ℕ) (z : HG (L.QA M) r j) (hz : L.Lifts e z x) :
    L.Lifts e (shG (L.QA M) L.t_mem k h j z) (CB.shS k h x) := fun n =>
  (red_sh (L.QA M) L.t_mem ((l : L.A) ^ n) k h j z).trans
    ((congrArg ((shm (L.QA M) L.t_mem ((l : L.A) ^ n) k h).pull j) (hz n)).trans
      ((map_smul ((shm (L.QA M) L.t_mem ((l : L.A) ^ n) k h).pull j) _ _).trans
        (congrArg (fun v => (l : L.A) ^ e • v) (rS_sh L M k h n x).symm)))

theorem lifts_cup {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) (e e' : ℕ) (z : HG (L.QA M) r i)
    (z' : HG (L.QA M) r' j) (hz : L.Lifts e z x) (hz' : L.Lifts e' z' y) :
    L.Lifts (e + e') (cupG (L.QA M) h z z') (CB.cupS h x y) := fun n =>
  (red_cup (L.QA M) ((l : L.A) ^ n) h z z').trans
    ((congrArg₂ ((okm (L.QA M) ((l : L.A) ^ n) h).pair.cup rfl) (hz n) (hz' n)).trans
      ((cup_smul _ _ _ _ _ _).trans
        (congrArg₂ (fun (a : L.A) (v : HGm (L.QA M) ((l : L.A) ^ n) s (i + j)) => a • v) (pow_add _ _ _).symm
          (rS_cup L M h n x y).symm)))

theorem rho_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) (w : HG (L.QB M) r j) (hr : L.Rho x w) :
    L.Rho (CB.shS k h x) (shG (L.QB M) L.tB_mem k h j w) :=
  hr.elim fun e he => he.elim fun z hz => ⟨e, shG (L.QA M) L.t_mem k h j z, lifts_sh L M k h x e z hz.1,
    (map_smul (shG (L.QB M) L.tB_mem k h j) _ _).symm.trans
      ((congrArg (shG (L.QB M) L.tB_mem k h j) hz.2).trans (b_sh L M k h z).symm)⟩

theorem cupG_smul {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) {r r' s i j : ℕ} (h : r + r' = s) (c : b.R) (e e' : ℕ)
    (w : HG Q r i) (w' : HG Q r' j) : c ^ (e + e') • cupG Q h w w' = cupG Q h (c ^ e • w) (c ^ e' • w') := by
  rw [pow_add]
  exact (cup_smul _ _ _ _ _ _).symm

theorem rho_cup {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) (w : HG (L.QB M) r i) (w' : HG (L.QB M) r' j)
    (hr : L.Rho x w) (hr' : L.Rho y w') : L.Rho (CB.cupS h x y) (cupG (L.QB M) h w w') :=
  hr.elim fun e he => he.elim fun z hz => hr'.elim fun e' he' => he'.elim fun z' hz' =>
    ⟨e + e', cupG (L.QA M) h z z', lifts_cup L M h x y e e' z z' hz.1 hz'.1,
      (cupG_smul (L.QB M) h (l : L.B) e e' w w').trans ((congrArg₂ (cupG (L.QB M) h) hz.2 hz'.2).trans (b_cup L M h z z').symm)⟩

theorem pow_zero_smul {R : Type} [CommRing R] {V : Type 1} [AddCommGroup V] [Module R V] (c : R) (v : V) : c ^ 0 • v = v := by
  rw [pow_zero, one_smul]

theorem rho_one : L.Rho (Y.oneS M) (L.μ M 0 0 0 (oneH M.q)) :=
  ⟨0, oneG (L.QA M), fun n => (rS_one L M n).symm.trans (pow_zero_smul _ _).symm, (pow_zero_smul _ _).trans (b_one L M).symm⟩

section Rat
variable {K B : Type} [CommRing K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of K)) (Q : ObjectProperty (Thick (nlFun γ 0 X q (κA K I)))) {t : B} (ht : t ∈ I)

theorem mu_sh {r r' j : ℕ} (k : ℕ) (h : r + k = r') (a : ℕ) (ha : a ≤ r) (y : Hdg q a j) :
    shG Q ht k h j (muG γ q Q ht a r j y) = muG γ q Q ht a r' j y :=
  sqC_sh (kS γ q Q) (t ^ (r - a)) (t ^ k) (t ^ (r' - a)) (by rw [← pow_add]; congr 1; omega) _ _ _ _ _ _ j y

theorem mu_cup {r r' s i j a a' c : ℕ} (h : r + r' = s) (ha : a + a' = c) (h1 : a ≤ r) (h2 : a' ≤ r') (y : Hdg q a i) (y' : Hdg q a' j) :
    cupG Q h (muG γ q Q ht a r i y) (muG γ q Q ht a' r' j y') = muG γ q Q ht c s (i + j) (cupH q ha rfl y y') :=
  (sqC_cup (kS γ q Q) (grOk (smFun X q) ha) (grOkQ Q h) (t ^ (r - a)) (t ^ (r' - a')) (t ^ (s - c))
    (by rw [← pow_add]; congr 1; omega) _ _ _ _ _ _ rfl y y').symm

end Rat

end Mul

variable (l K) in
theorem mulRho : MulRho l K :=
  ⟨fun {_ _} L M {_ _ _} k h x w hr => rho_sh L M k h x w hr,
   fun {_ _} L M {_ _ _} k h a ha y => mu_sh L.γB M.q (L.QB M) L.tB_mem k h a ha y,
   fun {_ _} L M {_ _ _ _ _} h x y w w' hr hr' => rho_cup L M h x y w w' hr hr',
   fun {_ _} L M {_ _ _ _ _ _ _ _} h ha h1 h2 y y' =>
     mu_cup L.γB M.q (L.QB M) L.tB_mem h ha h1 h2 y y',
   fun {_ _} L M => rho_one L M⟩

end CrystallineSemistableComparison.HT
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.HT

theorem half2 (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (hL : LvEx l K)
    (hF : KFin) : ∃ γ, Half2 (K := K) (tFil l) γ :=
  half2Of l K (tFil l) (crisSurj l) hL rhoEx (coEx l K) homRho homMu (mulRho l K) (firstChern_hodgeTate_rho l K) kForm hF

theorem ht_of (hL : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], LvEx l K)
    (hF : KFin) (hC : DlogClassExistsUnique) (hT : KTop) (hE : EtSideS) : HodgeTateMapExists := fun l _ K _ =>
  (etP l K).elim fun _ he => (half2 l K (hL l K) hF).elim fun _ h2 =>
    (pre_of (half1 (tFil l) he) h2 hF hC).elim fun P => ⟨P, inj_of P (hE l K) hT kForm he.one_ex⟩

end CrystallineSemistableComparison.HT
