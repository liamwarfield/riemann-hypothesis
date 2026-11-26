module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechDifferentialOneInclusion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TerminalRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def wz {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T) (I : Fin j → Fin d) (s : ComposableArrows C j) :
    Φ.A.obj (s.obj (Fin.last j)) :=
  ∏ k : Fin j, (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
    (u (I k) (s.obj k.succ) -
      (Φ.A.map (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))).hom (u (I k) (s.obj k.castSucc)))

theorem wz_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    (I : Fin j → Fin d) (s : ComposableArrows C j) : wz u I s ∈ (Fil j).S _ := by
  have key : ∀ (S : Finset (Fin j)) (f : Fin j → Φ.A.obj (s.obj (Fin.last j))),
      (∀ k, f k ∈ (Fil 1).S _) → ∏ k ∈ S, f k ∈ (Fil ((S.card : ℕ) : ℤ)).S _ := by
    classical
    intro S f hf
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.card_empty]
      rw [hF.top _ (by simp)]
      trivial
    | insert a S ha ih =>
      have e : (insert a S).card = 1 + S.card := by rw [Finset.card_insert_of_notMem ha, Nat.add_comm]
      rw [Finset.prod_insert ha, e]
      exact hF.mul 1 S.card _ (by simpa using hf a) ih
  have := key Finset.univ (fun k => (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
    (u (I k) (s.obj k.succ) -
      (Φ.A.map (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))).hom (u (I k) (s.obj k.castSucc))))
    (fun k => by
      rw [hF.one]
      exact Φ.J.map_mem _ (hu _ _))
  simpa [wz] using this

variable {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))

abbrev LL : (nlBase O ⊥ (dividedPowersBot O) 0).Fun := nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)

abbrev GF (r : ℕ) : Thick (LL q) ⥤ ModuleCat.{0} O := sq (thFil (LL q) r) (thFil (LL q) ((r : ℤ) + 1))

abbrev SS (l s : ℕ) (W : X.Opens) : ObjectProperty (Thick (LL q)) :=
  St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {W}

variable {q}

theorem ev_nat {W : X.Opens} {T T' : Thick (LL q)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T') (f : Γ(X, W)) :
    ev T' h' f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
  have e : pt T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T := by
    have := φ.pt
    unfold pt
    rw [← this]
    rfl
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X) (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (hh : ⊤ ≤ y ⁻¹ᵁ W), GlobalTheory.Cris.evalAt y W hh f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
    intro y hy hh
    subst hy
    exact evalAt_map (B := CommRingCat.of (T.B ⧸ T.J)) (B' := CommRingCat.of (T'.B ⧸ T'.J)) _ (pt T) h hh f
  exact key _ e h'

theorem ev_res {W W' : X.Opens} (hW : W' ≤ W) (T : Thick (LL q)) (h : InU W T) (h' : InU W' T) (f : Γ(X, W)) :
    ev T h' (rs hW f) = ev T h f := evalAt_res (pt T) hW h h' f

theorem ev_str {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (a : O) :
    ev T h (strV q W a) = Ideal.Quotient.mk T.J (T.i a) :=
  (evalAt_base q (Ideal.Quotient.mk ⊥) (show PtOver X q (Ideal.Quotient.mk (⊥ : Ideal O)) (T.B ⧸ T.J) from T.y).1.1 (pt T)
    (show PtOver X q (Ideal.Quotient.mk (⊥ : Ideal O)) (T.B ⧸ T.J) from T.y).2 h a).trans (T.w a)


open Classical in
def lft (W : X.Opens) (T : Thick (LL q)) (f : Γ(X, W)) : T.B :=
  if h : InU W T then Function.surjInv Ideal.Quotient.mk_surjective (ev T h f) else 0

theorem lft_spec {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f : Γ(X, W)) :
    Ideal.Quotient.mk T.J (lft W T f) = ev T h f := by
  rw [lft, dite_eq_left h]
  exact Function.surjInv_eq _ _

def IsLift (W : X.Opens) {d : ℕ} (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) : Prop :=
  ∀ i (T : Thick (LL q)) (h : InU W T), Ideal.Quotient.mk T.J (u i T) = ev T h (t i)

def Rp {W : X.Opens} (P : ObjectProperty (Thick (LL q))) {d r : ℕ} (u : Fin d → ∀ T : Thick (LL q), T.B)
    (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r) : Prop :=
  CrystallineSemistableComparison.Pb.Rep (sFil P r) (sFil P ((r : ℤ) + 1)) (fun s => ∑ I : Idx r d,
    wz (Φ := sP P) (fun i T => u i T.obj) I.1 s *
      (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I))) c

end GlobalTheory.CompanionTheory.GrForm

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

def StCocycle : Prop := ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    (y : ∀ T : C, Φ.A.obj T) (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (Φ.A.map φ).hom (y T) ∈ Φ.J.S T')
    (I : Fin j → Fin d),
    ∃ f : CH.Cn (sq (Fil j) (Fil ((j : ℤ) + 1))) j, CH.d _ j f = 0 ∧
      ∀ s, (show sqM (Fil j) (Fil ((j : ℤ) + 1)) _ from f s).1 = Ideal.Quotient.mk _ (wz u I s * y _)

def StExists : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W t u)
    (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (x : Idx r d → Γ(X, W)),
    ∃ c, Rp (W := W) P u x c

def StAdd : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W t u)
    (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (x x' : Idx r d → Γ(X, W))
    (c c' : HU (GF q r) P r), Rp (W := W) P u x c → Rp (W := W) P u x' c' →
      Rp (W := W) P u (x + x') (c + c') ∧ Rp (W := W) P u (-x) (-c)

def StSmul : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W t u)
    (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (x : Idx r d → Γ(X, W))
    (c : HU (GF q r) P r) (a : O), Rp (W := W) P u x c → Rp (W := W) P u (fun I => strV q W a * x I) (a • c)

def StRes : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W W' : X.Opens) (hW : W' ≤ W)
    {d : ℕ} (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W t u)
    (P P' : ObjectProperty (Thick (LL q))) (hPP : P' ≤ P) (hP : ∀ T, P T → InU W T) (hP' : ∀ T, P' T → InU W' T)
    (r : ℕ) (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r), Rp (W := W) P u x c →
      Rp (W := W') P' u (fun I => rs hW (x I)) ((resU (GF q r) hPP).pull r c)

def StAct : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens)
    (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (z : Γ(X, W)),
    ∃ m : HU (GF q r) P r →+ HU (GF q r) P r, ∀ {d : ℕ} (t : Fin d → Γ(X, W)) (u : Fin d → ∀ T : Thick (LL q), T.B),
      IsLift W t u → ∀ (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r), Rp (W := W) P u x c →
        Rp (W := W) P u (fun I => z * x I) (m c)

def StFrame : Prop := ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} {d : ℕ} (c : Coord q W d)
    (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W c.t u),
    ∃ (E : Frame (sP (SS q l s W)) d) (σ : ∀ T, E.D ⟶ T) (θ : Γ(X, W) ≃+* (sP (SS q l s W)).A.obj E.D),
      E.GrConst (sFil (SS q l s W)) ∧ (∀ n : ℕ, n ≠ 0 → (sFil (SS q l s W) n).S E.D = ⊥) ∧
      E.Coords (fun i => θ (c.t i)) ∧
      (∀ i T, ((sP (SS q l s W)).A.map (σ T)).hom (θ (c.t i)) = u i T.obj) ∧
      ∀ (T : (SS q l s W).FullSubcategory) (h : InU W T.obj) (f : Γ(X, W)),
        Ideal.Quotient.mk T.obj.J (show T.obj.B from ((sP (SS q l s W)).A.map (σ T)).hom (θ f)) = ev T.obj h f

def StLoc : Prop := ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} {d : ℕ} (c : Coord q W d)
    (u : Fin d → ∀ T : Thick (LL q), T.B) (hu : IsLift W c.t u) (r : ℕ) (hr : r < s),
    (∀ cl : HU (GF q r) (SS q l s W) r, ∃ x, Rp (W := W) (SS q l s W) u x cl) ∧
      ∀ x : Idx r d → Γ(X, W), Rp (W := W) (SS q l s W) u x 0 → x = 0

def StVan : Prop := ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (r j : ℕ), r < s → j ≠ r →
    Subsingleton (HU (GF q r) (SS q l s W) j)

def StVB : Prop := ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {ι : Type} [Fintype ι] (U : ι → X.Opens) (d : ι → ℕ)
    (c : ∀ α, Coord q (U α) (d α)) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)) (r : ℕ), r < s →
    Nonempty (VB (strV q) U (CrystallineSemistableComparison.Pb.cechH (GF q r) (fun α => SS q l s (U α)) r))

def StCover : Prop := ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [Smooth q]
    (V : X.Opens), IsAffineOpen V → ∃ (ι : Type) (_ : Fintype ι) (U : ι → X.Opens) (d : ι → ℕ)
      (_ : ∀ α, Coord q (U α) (d α)), (⨆ α, U α) = V ∧ ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i)

end GlobalTheory.CompanionTheory.GrForm
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartFil

section Rings

variable {R B : Type} [CommRing R] [CommRing B] {I : Ideal R} {J : Ideal B}

theorem dividedPowerFiltration_anti (δ : DividedPowers J) {r r' : ℕ} (h : r ≤ r') : pdP δ r' ≤ pdP δ r :=
  Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, h.trans hr, hz⟩

theorem one_mem_pdP_zero (δ : DividedPowers J) : (1 : B) ∈ pdP δ 0 :=
  Ideal.subset_span ⟨[], by simp, by simp, by simp⟩

theorem mul_mem_map (γ : DividedPowers I) (i : R →+* B) (r r' : ℕ) {x y : B}
    (hx : x ∈ (pdP γ r).map i) (hy : y ∈ (pdP γ r').map i) : x * y ∈ (pdP γ (r + r')).map i := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← Ideal.map_mul] at h
  exact Ideal.map_mono (GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le γ r r') h

theorem dpow_mem_map (γ : DividedPowers I) (δ : DividedPowers J) (i : R →+* B) (hi : IsDPMorphism γ δ i)
    (hJ : J = I.map i) {x : B} (hx : x ∈ J) (n : ℕ) : δ.dpow n x ∈ (pdP γ n).map i := by
  have h0 : ∀ y ∈ J, δ.dpow 0 y ∈ (pdP γ 0).map i := fun y hy => by
    rw [δ.dpow_zero hy, ← map_one i]
    exact Ideal.mem_map_of_mem i (one_mem_pdP_zero γ)
  rw [hJ] at hx
  revert n
  refine Submodule.span_induction (p := fun x _ => ∀ n, δ.dpow n x ∈ (pdP γ n).map i) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩ n
    rw [hi.2 a ha]
    exact Ideal.mem_map_of_mem i (GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP γ n ha)
  · intro n
    by_cases hn : n = 0
    · subst hn
      exact h0 0 J.zero_mem
    · rw [δ.dpow_eval_zero hn]
      exact Ideal.zero_mem _
  · intro y z hy hz ihy ihz n
    have hy' : y ∈ J := hJ ▸ hy
    have hz' : z ∈ J := hJ ▸ hz
    rw [δ.dpow_add hy' hz']
    refine Ideal.sum_mem _ fun ab hab => ?_
    have e : ab.1 + ab.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    rw [← e]
    exact mul_mem_map γ i _ _ (ihy _) (ihz _)
  · intro a y hy ihy n
    have hy' : y ∈ J := hJ ▸ hy
    rw [smul_eq_mul, δ.dpow_mul hy']
    exact Ideal.mul_mem_left _ _ (ihy n)

theorem dividedPowerFiltration_eq_map (γ : DividedPowers I) (δ : DividedPowers J) (i : R →+* B) (hi : IsDPMorphism γ δ i)
    (hJ : J = I.map i) (r : ℕ) : pdP δ r = (pdP γ r).map i := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.map_le_iff_le_comap.2 fun x hx => dividedPowerFiltration_map hi r hx)
  rintro _ ⟨l, hl, hr, rfl⟩
  have key : ∀ l : List (ℕ × B), (∀ q ∈ l, q.2 ∈ J) →
      (l.map fun q => δ.dpow q.1 q.2).prod ∈ (pdP γ (l.map Prod.fst).sum).map i := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [List.map_nil, List.prod_nil, List.sum_nil]
      rw [← map_one i]
      exact Ideal.mem_map_of_mem i (one_mem_pdP_zero γ)
    | cons a t ih =>
      intro h
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact mul_mem_map γ i _ _ (dpow_mem_map γ δ i hi hJ (h a (by simp)) _)
        (ih fun q hq => h q (List.mem_cons_of_mem _ hq))
  exact Ideal.map_mono (dividedPowerFiltration_anti γ hr) (key l hl)

end Rings

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ}

theorem sub_mem_J (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) (f g : c.D ⟶ T)
    (z : c.D.B) : f.φ z - g.φ z ∈ T.J := by
  obtain ⟨φ, -, hu⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y hT
  have e := (hu _ f.pt).trans (hu _ g.pt).symm
  exact Ideal.Quotient.eq.1 (RingHom.congr_fun e (Ideal.Quotient.mk _ z))

theorem sub_mem_pdP (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)} (hT : InU V T) (f g : c.D ⟶ T)
    (n : ℕ) {x : c.D.B} (hx : x ∈ (pdP γ n).map c.D.i) : f.φ x - g.φ x ∈ pdP T.δ (n + 1) := by
  refine Submodule.span_induction (p := fun x _ => f.φ x - g.φ x ∈ pdP T.δ (n + 1)) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, -, rfl⟩
    have e : f.φ (c.D.i a) - g.φ (c.D.i a) = 0 := by rw [f.comm, g.comm, sub_self]
    rw [e]
    exact Ideal.zero_mem _
  · rw [map_zero, map_zero, sub_zero]
    exact Ideal.zero_mem _
  · intro y z _ _ hy hz
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
    exact Ideal.add_mem _ hy hz
  · intro a y hy ih
    have e : f.φ (a • y) - g.φ (a • y) = f.φ a * (f.φ y - g.φ y) + (f.φ a - g.φ a) * g.φ y := by
      rw [smul_eq_mul, map_mul, map_mul]
      ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) ?_
    have h1 : f.φ a - g.φ a ∈ pdP T.δ 1 := T.J_le_pdPow_one (sub_mem_J c hT f g a)
    have hm : (pdP γ n).map c.D.i ≤ pdP c.D.δ n :=
      Ideal.map_le_iff_le_comap.2 fun x hx => dividedPowerFiltration_map c.D.compat n hx
    have hy' : y ∈ pdP c.D.δ n := hm hy
    have h2 : g.φ y ∈ pdP T.δ n := dividedPowerFiltration_map g.dp n hy'
    have h3 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ 1 n (Ideal.mul_mem_mul h1 h2)
    rwa [add_comm 1 n] at h3

theorem chart_grConst : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (h : c.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D),
    (∀ r, c.D.pdPow r = (pdP γ r).map c.D.i) ∧ (c.frame h Q hQ hD).GrConst (sFil Q) := by
  intro O R _ _ I γ p X q κ V d c h Q hQ hD
  have h1 : ∀ r, c.D.pdPow r = (pdP γ r).map c.D.i := fun r =>
    dividedPowerFiltration_eq_map γ c.D.δ c.D.i c.D.compat c.J_eq r
  refine ⟨h1, ?_⟩
  intro n T σ σ' x hx
  have hx' : (show c.D.B from x) ∈ c.D.pdPow ((n : ℤ).toNat) := hx
  rw [Int.toNat_natCast, h1] at hx'
  change _ ∈ T.obj.pdPow (((n : ℤ) + 1).toNat)
  have e : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [e]
  exact sub_mem_pdP c (hQ _ T.property) σ.hom σ'.hom n hx'

end GlobalTheory.CompanionTheory.ChartFil
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_divided_powers_graded_constant : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (h : c.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D),
    (∀ r, c.D.pdPow r = (pdP γ r).map c.D.i) ∧ (c.frame h Q hQ hD).GrConst (sFil Q) := by
  first | exact @GlobalTheory.CompanionTheory.ChartFil.chart_grConst | exact GlobalTheory.CompanionTheory.ChartFil.chart_grConst | (intros; apply GlobalTheory.CompanionTheory.ChartFil.chart_grConst <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CompanionTheory.ChartAlg in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_from_coordinates : ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {I : Ideal R} (γ : DividedPowers I) (l s : ℕ)
    (hb : TFBase γ l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I)
    (hκ : ∀ a, κ a = Ideal.Quotient.mk I (algebraMap O R a)) {V : X.Opens} {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∃ (c' : Chart γ 0 q κ V d) (e : R ⊗[O] Γ(X, V) ≃+* c'.D.B), TF l s c'.D ∧ (∀ r, e (r ⊗ₜ 1) = c'.D.i r) ∧
      (∀ i, e (1 ⊗ₜ c.t i) = c'.t i) ∧ ∀ f, ev c'.D c'.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f)) := by
  intro O R _ _ _ I γ l s hb X q κ hκ V d c
  let a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  have hstr : algebraMap O Γ(X, V) = strV q V := rfl
  have hE : (MvPolynomial.eval₂Hom (algebraMap O Γ(X, V)) c.t : MvPolynomial (Fin d) O →+* Γ(X, V)).Etale := c.etale
  have hF : Module.Flat O Γ(X, V) := flat_of_etale c.t hE
  let iL : R →+* R ⊗[O] Γ(X, V) := Algebra.TensorProduct.includeLeftRingHom
  have hl : ∀ x : R ⊗[O] Γ(X, V), (l : R ⊗[O] Γ(X, V)) * x = 0 → x = 0 := fun x h => by
    have := tf_tensor (G := Γ(X, V)) (O := O) (pdP γ s) l (hb.tf s) x (by rw [h]; exact zero_mem _)
    rw [hb.nil, Ideal.map_bot] at this
    exact this
  have hlk : ∀ (k : ℕ) (x : R ⊗[O] Γ(X, V)), (l : R ⊗[O] Γ(X, V)) ^ k * x = 0 → x = 0 := fun k => by
    induction k with
    | zero => intro x h; simpa using h
    | succ k ih =>
      intro x h
      refine ih x (hl _ ?_)
      rw [← h, pow_succ']
      ring
  have hn : ∀ n : ℕ, n ≠ 0 → ∀ x : R ⊗[O] Γ(X, V), (n : R ⊗[O] Γ(X, V)) * x = 0 → x = 0 := fun n hn0 x h => by
    obtain ⟨k, u, hu⟩ := hb.dv n hn0
    refine hlk k x ?_
    have e := congrArg iL hu
    rw [map_mul, map_pow, map_natCast, map_natCast] at e
    rw [← e, mul_comm (n : R ⊗[O] Γ(X, V)), mul_assoc, h, mul_zero]
  obtain ⟨δ, hδ⟩ := exists_dp γ iL hn
  have hP := dividedPowerFiltration_eq_map γ iL δ hδ
  let g : Γ(X, V) →+* (R ⊗[O] Γ(X, V)) ⧸ I.map iL :=
    (Ideal.Quotient.mk _).comp (Algebra.TensorProduct.includeRight : Γ(X, V) →ₐ[O] R ⊗[O] Γ(X, V)).toRingHom
  let ψ : R ⧸ I →+* (R ⊗[O] Γ(X, V)) ⧸ I.map iL := Ideal.quotientMap _ iL Ideal.le_comap_map
  have hcomp : g.comp (strV q V) = ψ.comp κ := RingHom.ext fun a => by
    change Ideal.Quotient.mk _ ((1 : R) ⊗ₜ[O] (algebraMap O Γ(X, V) a)) = ψ (κ a)
    rw [hκ]
    change _ = Ideal.Quotient.mk _ ((algebraMap O R a) ⊗ₜ[O] (1 : Γ(X, V)))
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  let y : PtOver X q κ ((R ⊗[O] Γ(X, V)) ⧸ I.map iL) :=
    ⟨(ψ, Spec.map (CommRingCat.ofHom g) ≫ c.affine.fromSpec), by
      change (Spec.map (CommRingCat.ofHom g) ≫ c.affine.fromSpec) ≫ q = _
      rw [Category.assoc, fromSpec_comp q c.affine, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]⟩
  have hnil : IsNilpotent (I.map iL) := ⟨s, by
    have h := pow_le_pdP δ s
    rw [hP, hb.nil, Ideal.map_bot] at h
    exact le_bot_iff.1 h⟩
  let D : Thick (nlFun γ 0 X q κ) := mkT (R ⊗[O] Γ(X, V)) iL (I.map iL) δ ⟨fun h => (h rfl).elim, fun _ => hnil⟩ hδ y
    (fun r => rfl)
  have hin : InU V D := top_le_specMap c.affine g
  let c' : Chart γ 0 q κ V d :=
    { D := D
      t := fun k => (1 : R) ⊗ₜ[O] c.t k
      etale := etale_tensor c.t hE
      J_eq := rfl
      inV := hin
      rep := fun B' y' hy' => rep_tensor hstr hκ c.affine y (fun r => rfl) g (fun f => rfl) rfl B' y' hy' }
  have key : ∀ (r : ℕ) (x : R ⊗[O] Γ(X, V)), (l : R ⊗[O] Γ(X, V)) * x ∈ pdP δ r → x ∈ pdP δ r := fun r x hx => by
    rw [hP] at hx ⊢
    exact tf_tensor (pdP γ r) l (hb.tf r) x hx
  refine ⟨c', RingEquiv.refl _, ⟨?_, fun r x hx => ?_⟩, fun r => rfl, fun k => rfl, fun f => ?_⟩
  · change pdP δ s = ⊥
    rw [hP, hb.nil, Ideal.map_bot]
  · exact key r x hx
  · have := evalAt_specMap c.affine g (pt D) rfl hin
    exact RingHom.congr_fun this f
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace GlobalTheory.CompanionTheory.PTIso

section Gen

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {I : Type} [Fintype I] {D : I → Type} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))
  (χ : Γ →* Rˣ)
  (j : ∀ i, H2 ((charRep χ).comp (φ i)) →ₗ[R] R)
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation R Γ M)

def gloc0 : H0 ρ →ₗ[R] ∀ i, H0 (ρ.comp (φ i)) :=
  LinearMap.pi fun i => resH0 ρ (φ i)

def gloc1 : H1 ρ →ₗ[R] ∀ i, H1 (ρ.comp (φ i)) :=
  LinearMap.pi fun i => resH1 ρ (φ i) (hφ i)

def gloc2 : H2 ρ →ₗ[R] ∀ i, H2 (ρ.comp (φ i)) :=
  LinearMap.pi fun i => resH2 ρ (φ i) (hφ i)

def gtr0 : (∀ i, H0 (ρ.comp (φ i))) →ₗ[R] Module.Dual R (H2 (twDual χ ρ)) :=
  ∑ i, (((cupH0H2TwistedDual χ ρ (φ i)).compr₂ (j i)).compl₁₂ (LinearMap.proj i)
    (resH2 (twDual χ ρ) (φ i) (hφ i)))

def gtr1 (hρ : ContAction ρ) : (∀ i, H1 (ρ.comp (φ i))) →ₗ[R] Module.Dual R (H1 (twDual χ ρ)) :=
  ∑ i, (((cupH1H1TwistedDual χ ρ (φ i) (hρ.comp' (hφ i))).flip.compr₂ (j i)).compl₁₂ (LinearMap.proj i)
    (resH1 (twDual χ ρ) (φ i) (hφ i)))

def gtr2 : (∀ i, H2 (ρ.comp (φ i))) →ₗ[R] Module.Dual R (H0 (twDual χ ρ)) :=
  ∑ i, (((cup20 χ ρ (φ i)).compr₂ (j i)).compl₁₂ (LinearMap.proj i)
    (resH0 (twDual χ ρ) (φ i)))

def NineG (hρ : ContAction ρ) : Prop :=
  ∃ (δ₁ : Module.Dual R (H2 (twDual χ ρ)) →ₗ[R] H1 ρ)
    (δ₂ : Module.Dual R (H1 (twDual χ ρ)) →ₗ[R] H2 ρ),
    Function.Injective (gloc0 φ ρ) ∧
    Function.Exact (gloc0 φ ρ) (gtr0 φ hφ χ j ρ) ∧
    Function.Exact (gtr0 φ hφ χ j ρ) δ₁ ∧
    Function.Exact δ₁ (gloc1 φ hφ ρ) ∧
    Function.Exact (gloc1 φ hφ ρ) (gtr1 φ hφ χ j ρ hρ) ∧
    Function.Exact (gtr1 φ hφ χ j ρ hρ) δ₂ ∧
    Function.Exact δ₂ (gloc2 φ hφ ρ) ∧
    Function.Exact (gloc2 φ hφ ρ) (gtr2 φ χ j ρ) ∧
    Function.Surjective (gtr2 φ χ j ρ)

def ShaG : Prop :=
  (Finite (Sha1 (twDual χ ρ) φ hφ) ∧ Finite (Sha2 ρ φ hφ) ∧
    Nonempty (Sha2 ρ φ hφ ≃ₗ[R] Module.Dual R (Sha1 (twDual χ ρ) φ hφ)) ∧
    Nat.card (Sha1 (twDual χ ρ) φ hφ) = Nat.card (Sha2 ρ φ hφ)) ∧
  (Finite (Sha1 ρ φ hφ) ∧ Finite (Sha2 (twDual χ ρ) φ hφ) ∧
    Nonempty (Sha2 (twDual χ ρ) φ hφ ≃ₗ[R] Module.Dual R (Sha1 ρ φ hφ)) ∧
    Nat.card (Sha1 ρ φ hφ) = Nat.card (Sha2 (twDual χ ρ) φ hφ))

end Gen

section Concrete

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 F)))
  (Av : S → ValuationSubring Ω)
  (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ)
  (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M]
  (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)

theorem nineTermExact_iff (hρ : ContAction ρ) :
    NineTermExact S Av μ j ρ hρ ↔
      NineG (locFam S Av) (continuous_locFam S Av) μ j ρ hρ := Iff.rfl

theorem shaDual_iff :
    ShaDual S Av μ ρ ↔ ShaG (locFam S Av) (continuous_locFam S Av) μ ρ := Iff.rfl

end Concrete

def subgroupIso {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]
    (Φ : A ≃ₜ* B) (H : Subgroup A) (K : Subgroup B) (h : ∀ a, a ∈ H ↔ Φ a ∈ K) : H ≃ₜ* K where
  toFun a := ⟨Φ a.1, (h a.1).1 a.2⟩
  invFun b := ⟨Φ.symm b.1, (h _).2 (by simpa using b.2)⟩
  left_inv a := Subtype.ext (by simp)
  right_inv b := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  continuous_toFun := (Φ.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (Φ.symm.continuous.comp continuous_subtype_val).subtype_mk _

end GlobalTheory.CompanionTheory.PTIso
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrCech

section Site

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

theorem J_mul_mem (hF : IsFil Φ Fil) (r : ℕ) {T : C} {x y : Φ.A.obj T} (hx : x ∈ Φ.J.S T)
    (hy : y ∈ (Fil r).S T) : x * y ∈ (Fil ((r : ℤ) + 1)).S T := by
  have h1 : x ∈ (Fil ((1 : ℕ) : ℤ)).S T := by
    have := hF.one T
    simpa [this] using hx
  have := hF.mul 1 r T h1 hy
  have e : (((1 + r : ℕ)) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
  rwa [e] at this

def mulT (Fil : ℤ → IdF Φ.A) (r : ℤ) {T : C} (u : Φ.A.obj T) : (gr Fil r).obj T →ₗ[R] (gr Fil r).obj T :=
  (LinearMap.mulLeft R (Ideal.Quotient.mk ((Fil (r + 1)).S T) u)).restrict fun x hx =>
    Ideal.mul_mem_left _ _ hx

theorem mulT_congr (hF : IsFil Φ Fil) (r : ℕ) {T : C} {u v : Φ.A.obj T} (h : u - v ∈ Φ.J.S T)
    (x : (gr Fil r).obj T) : mulT Fil r u x = mulT Fil r v x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ u * Ideal.Quotient.mk _ y = Ideal.Quotient.mk _ v * Ideal.Quotient.mk _ y
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← sub_mul]
  exact J_mul_mem hF r h hy

def mulMor (hF : IsFil Φ Fil) (r : ℕ) (u : ∀ T, Φ.A.obj T)
    (hu : ∀ {T T' : C} (φ : T ⟶ T'), u T' - (Φ.A.map φ).hom (u T) ∈ Φ.J.S T') :
    CH.Mor (gr Fil r) (gr Fil r) (RingHom.id R) where
  G := 𝟭 C
  τ T := mulT Fil r (u T)
  nat {T T'} φ x := by
    have e := mulT_congr hF r (hu φ) ((gr Fil r).map φ |>.hom x)
    refine e.trans ?_
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Subtype.ext ?_
    change Ideal.Quotient.mk _ ((Φ.A.map φ).hom (u T)) * Ideal.Quotient.mk _ ((Φ.A.map φ).hom y) =
      Ideal.Quotient.mk _ ((Φ.A.map φ).hom (u T * (show Φ.A.obj T from y)))
    rw [map_mul, map_mul]

end Site

end GlobalTheory.CompanionTheory.GrCech
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GrCech

section Act

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

theorem pull_mk {R' : Type} [CommRing R'] {C' : Type 1} [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R}
    {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'} (m : CH.Mor F F' σ) (n : ℕ) (z : (CH.cx F).Z n) :
    m.pull n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (m.hom.mapZ n z) := rfl

variable (hF : IsFil Φ Fil) (r : ℕ)
include hF

theorem mulMor_add {u v w : ∀ T, Φ.A.obj T} (hu hv hw) (h : ∀ T, w T - (u T + v T) ∈ Φ.J.S T) (n : ℕ) (c : CH.H (gr Fil r) n) :
    (mulMor hF r w hw).pull n c = (mulMor hF r u hu).pull n c + (mulMor hF r v hv).pull n c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [pull_mk, pull_mk, pull_mk, ← Submodule.Quotient.mk_add]
  congr 1
  refine Subtype.ext (funext fun s => ?_)
  refine (mulT_congr hF r (h _) (z.1 s)).trans ?_
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (u _ + v _) * _ = Ideal.Quotient.mk _ (u _) * _ + Ideal.Quotient.mk _ (v _) * _
  rw [map_add (f := _), add_mul]
  rfl

theorem mulMor_mul {u v w : ∀ T, Φ.A.obj T} (hu hv hw) (h : ∀ T, w T - u T * v T ∈ Φ.J.S T) (n : ℕ) (c : CH.H (gr Fil r) n) :
    (mulMor hF r w hw).pull n c = (mulMor hF r u hu).pull n ((mulMor hF r v hv).pull n c) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [pull_mk, pull_mk, pull_mk]
  congr 1
  refine Subtype.ext (funext fun s => ?_)
  refine (mulT_congr hF r (h _) (z.1 s)).trans ?_
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (u _ * v _) * _ = Ideal.Quotient.mk _ (u _) * (Ideal.Quotient.mk _ (v _) * _)
  rw [map_mul, mul_assoc]
  rfl

theorem mulMor_smul {u : ∀ T, Φ.A.obj T} (hu) (a : R) (h : ∀ T, u T - algebraMap R _ a ∈ Φ.J.S T) (n : ℕ) (c : CH.H (gr Fil r) n) :
    (mulMor hF r u hu).pull n c = a • c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [pull_mk, ← Submodule.Quotient.mk_smul]
  congr 1
  refine Subtype.ext (funext fun s => ?_)
  refine (mulT_congr hF r (h _) (z.1 s)).trans ?_
  refine Subtype.ext ?_
  exact (Algebra.smul_def a (show sqM (Fil r) (Fil ((r : ℤ) + 1)) _ from z.1 s).1).symm

end Act

section Thickenings

variable {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem ev_map {W : X.Opens} {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T')
    (f : Γ(X, W)) : ev T' h' f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
  have e : pt T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T := by
    have := φ.pt
    unfold pt
    rw [← this]
    rfl
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X) (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (h'' : ⊤ ≤ y ⁻¹ᵁ W), GlobalTheory.Cris.evalAt y W h'' f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
    intro y hy h''
    subst hy
    exact GlobalTheory.LogCris.evalAt_map _ (pt T) h h'' f
  exact key _ e h'

def evLift {Q : ObjectProperty (Thick (nlFun γ p X q κ))} {W : X.Opens} (hQ : ∀ T, Q T → InU W T) (f : Γ(X, W))
    (T : Q.FullSubcategory) : (sP Q).A.obj T :=
  Function.surjInv (Ideal.Quotient.mk_surjective (I := T.obj.J)) (ev T.obj (hQ _ T.property) f)

theorem mk_evLift {Q : ObjectProperty (Thick (nlFun γ p X q κ))} {W : X.Opens} (hQ : ∀ T, Q T → InU W T) (f : Γ(X, W))
    (T : Q.FullSubcategory) : Ideal.Quotient.mk T.obj.J (evLift hQ f T) = ev T.obj (hQ _ T.property) f :=
  Function.surjInv_eq _ _

theorem sub_mem_of_mk {T : Thick (nlFun γ p X q κ)} {x y : T.B} (h : Ideal.Quotient.mk T.J x = Ideal.Quotient.mk T.J y) :
    x - y ∈ T.J := Ideal.Quotient.eq.1 h

theorem evLift_nat {Q : ObjectProperty (Thick (nlFun γ p X q κ))} {W : X.Opens} (hQ : ∀ T, Q T → InU W T) (f : Γ(X, W))
    {T T' : Q.FullSubcategory} (φ : T ⟶ T') :
    evLift hQ f T' - ((sP Q).A.map φ).hom (evLift hQ f T) ∈ (sP Q).J.S T' := by
  refine sub_mem_of_mk (T := T'.obj) ?_
  rw [mk_evLift, ev_map φ.hom (hQ _ T.property) (hQ _ T'.property), ← mk_evLift hQ f T]
  rfl

abbrev grF (L : (nlBase R I γ p).Fun) (r : ℕ) : Thick L ⥤ ModuleCat.{0} R :=
  sq (thFil L r) (thFil L ((r : ℤ) + 1))

def fAct {Q : ObjectProperty (Thick (nlFun γ p X q κ))} (hF : IsFil (sP Q) (sFil Q)) {W : X.Opens}
    (hQ : ∀ T, Q T → InU W T) (r : ℕ) (f : Γ(X, W)) :
    HU (grF (nlFun γ p X q κ) r) Q r →ₗ[R] HU (grF (nlFun γ p X q κ) r) Q r :=
  (mulMor hF r (evLift hQ f) (evLift_nat hQ f)).pull r

end Thickenings

end GlobalTheory.CompanionTheory.GrCech
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GrCech

section ThAct

variable {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
  {Q : ObjectProperty (Thick (nlFun γ p X q κ))} (hF : IsFil (sP Q) (sFil Q)) {W : X.Opens}
  (hQ : ∀ T, Q T → InU W T) (r : ℕ)

theorem fAct_add (f g : Γ(X, W)) (c : HU (grF (nlFun γ p X q κ) r) Q r) :
    fAct hF hQ r (f + g) c = fAct hF hQ r f c + fAct hF hQ r g c := by
  refine mulMor_add hF r _ _ _ (fun T => sub_mem_of_mk (T := T.obj) ?_) r c
  rw [mk_evLift, map_add (Ideal.Quotient.mk T.obj.J), mk_evLift, mk_evLift, map_add (f := _)]

theorem fAct_mul (f g : Γ(X, W)) (c : HU (grF (nlFun γ p X q κ) r) Q r) :
    fAct hF hQ r (f * g) c = fAct hF hQ r f (fAct hF hQ r g c) := by
  refine mulMor_mul hF r _ _ _ (fun T => sub_mem_of_mk (T := T.obj) ?_) r c
  rw [mk_evLift, map_mul (Ideal.Quotient.mk T.obj.J), mk_evLift, mk_evLift, map_mul]

theorem fAct_one (c : HU (grF (nlFun γ p X q κ) r) Q r) : fAct hF hQ r 1 c = c := by
  refine (mulMor_smul hF r _ (1 : R) (fun T => sub_mem_of_mk (T := T.obj) ?_) r c).trans (one_smul _ _)
  rw [mk_evLift, map_one, map_one (algebraMap R _)]
  exact (map_one _).symm

def fHom : Γ(X, W) →+* AddMonoid.End (HU (grF (nlFun γ p X q κ) r) Q r) :=
  RingHom.mk' { toFun := fun f => (fAct hF hQ r f).toAddMonoidHom
                map_one' := AddMonoidHom.ext fun c => fAct_one hF hQ r c
                map_mul' := fun f g => AddMonoidHom.ext fun c => fAct_mul hF hQ r f g c }
    fun f g => AddMonoidHom.ext fun c => fAct_add hF hQ r f g c

theorem ev_rs {W' : X.Opens} (hW : W' ≤ W) (T : Thick (nlFun γ p X q κ)) (h : InU W T) (h' : InU W' T) (f : Γ(X, W)) :
    ev T h' (rs hW f) = ev T h f :=
  GlobalTheory.LogCris.evalAt_res (pt T) hW h h' f

theorem res_fAct {Q' : ObjectProperty (Thick (nlFun γ p X q κ))} (hF' : IsFil (sP Q') (sFil Q')) {W' : X.Opens}
    (hQ' : ∀ T, Q' T → InU W' T) (hW : W' ≤ W) (hle : Q' ≤ Q) (f : Γ(X, W)) (c : HU (grF (nlFun γ p X q κ) r) Q r) :
    (resU (grF (nlFun γ p X q κ) r) hle).pull r (fAct hF hQ r f c) =
      fAct hF' hQ' r (rs hW f) ((resU (grF (nlFun γ p X q κ) r) hle).pull r c) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  change Submodule.Quotient.mk ((resU (grF (nlFun γ p X q κ) r) hle).hom.mapZ r ((mulMor hF r (evLift hQ f) (evLift_nat hQ f)).hom.mapZ r z)) =
    Submodule.Quotient.mk ((mulMor hF' r (evLift hQ' (rs hW f)) (evLift_nat hQ' (rs hW f))).hom.mapZ r ((resU (grF (nlFun γ p X q κ) r) hle).hom.mapZ r z))
  congr 1
  refine Subtype.ext (funext fun s => ?_)
  refine Eq.symm (((mulT_congr hF' r (T := s.obj (Fin.last r)) (u := evLift hQ' (rs hW f) _) (v := evLift hQ f ((ObjectProperty.ιOfLE hle).obj (s.obj (Fin.last r)))) ?_ _)).trans ?_)
  · refine sub_mem_of_mk (T := (s.obj (Fin.last r)).obj) ?_
    rw [mk_evLift]
    exact (ev_rs hW _ (hQ _ (hle _ (s.obj (Fin.last r)).property)) _ _).trans (mk_evLift hQ f ((ObjectProperty.ιOfLE hle).obj (s.obj (Fin.last r)))).symm
  · rfl

end ThAct

end GlobalTheory.CompanionTheory.GrCech
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GrCech

section Sec

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

end Sec

section Res

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem res_res (F : C ⥤ ModuleCat.{0} R) {U V W : ObjectProperty C} (h₁ : V ≤ U) (h₂ : W ≤ V) (n : ℕ) (c : HU F U n) :
    (resU F h₂).pull n ((resU F h₁).pull n c) = (resU F (h₂.trans h₁)).pull n c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rfl

end Res

section Str

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)))} (hF : IsFil (sP Q) (sFil Q)) {W : X.Opens}
  (hQ : ∀ T, Q T → InU W T) (r : ℕ)

theorem fAct_str (a : O) (c : HU (grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) Q r) :
    fAct hF hQ r (strV q W a) c = a • c := by
  refine mulMor_smul hF r _ a (fun T => sub_mem_of_mk (T := T.obj) ?_) r c
  rw [mk_evLift]
  have e := GlobalTheory.LogCris.evalAt_base q (Ideal.Quotient.mk ⊥) (T.obj.y.1.1) (T.obj.y.1.2) T.obj.y.2 (hQ _ T.property) a
  exact e.trans (T.obj.w a)

end Str

end GlobalTheory.CompanionTheory.GrCech
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningFiltrationIsFil
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.DPFil

theorem isFil_thFil : ∀ {b : Base} (L : b.Fun), IsFil (thP L) (thFil L) := by
  intro b L
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr T
    change T.pdPow r.toNat = ⊤
    rw [Int.toNat_of_nonpos hr]
    exact T.pdPow_zero
  · intro T
    change T.pdPow (1 : ℤ).toNat = T.J
    exact le_antisymm (dividedPowerFiltration_one_le T.δ) T.J_le_pdPow_one
  · intro r r' h T
    exact T.pdPow_anti (Int.toNat_le_toNat h)
  · intro r r' T x y hx hy
    have hx' : (show T.B from x) ∈ pdP T.δ r := by
      have : (show T.B from x) ∈ T.pdPow ((r : ℤ).toNat) := hx
      rw [Int.toNat_natCast] at this
      exact this
    have hy' : (show T.B from y) ∈ pdP T.δ r' := by
      have : (show T.B from y) ∈ T.pdPow ((r' : ℤ).toNat) := hy
      rw [Int.toNat_natCast] at this
      exact this
    have h := dividedPowerFiltration_mul_le T.δ r r' (Ideal.mul_mem_mul hx' hy')
    change _ ∈ T.pdPow (((r + r' : ℕ) : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact h
  · intro k T x hx
    change _ ∈ T.pdPow ((k : ℤ).toNat)
    rw [Int.toNat_natCast]
    exact dpow_mem_pdP T.δ k hx

end GlobalTheory.CompanionTheory.DPFil
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorSpaceHasBasisOfDimension
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorSpaceHasBasisOfDimension
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem vb_basis_of_isField {R : Type} [CommRing R] (hR : IsField R) {M : Type} [AddCommGroup M] [Module R M]
    (g : ℕ) (h : VB R M g) : Nonempty (Module.Basis (Fin g) R M) := by
  obtain ⟨hfin, -, hrank⟩ := h
  haveI : Module.Free R M := by
    letI := hR.toField
    exact Module.Free.of_divisionRing R M
  haveI : Nontrivial R := ⟨hR.exists_pair_ne⟩
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  have hg : Module.finrank R M = g := by
    have hp := hrank p
    rw [Module.rankAtStalk_eq_finrank_of_free] at hp
    exact hp
  exact ⟨Module.finBasisOfFinrankEq R M hg⟩

end GlobalTheory.CompanionTheory.HopfC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorSpaceHasBasisOfDimensionStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_space_has_basis_of_dimension : ∀ {R : Type} [CommRing R] (_ : IsField R) {M : Type} [AddCommGroup M] [Module R M] (g : ℕ), VB R M g → Nonempty (Module.Basis (Fin g) R M) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.vb_basis_of_isField | exact GlobalTheory.CompanionTheory.HopfC.vb_basis_of_isField | (intros; apply GlobalTheory.CompanionTheory.HopfC.vb_basis_of_isField <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialValueOfFactorPullbacks
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialValueOfFactorPullbacks
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem bv_pulln_box {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {N p q : ℕ}
    (ρ₁ : Fin (N + 1) →o Fin (p + 1)) (ρ₂ : Fin (N + 1) →o Fin (q + 1)) (x : Cn F N) :
    (bv F ρ₁ ρ₂ (pulln (boxL F) N x) = fun a _ ↦ pr F ρ₁ x a ⊗ₜ[R] 1) ∧
      (bv F ρ₁ ρ₂ (pulln (boxR F) N x) = fun _ b ↦ 1 ⊗ₜ[R] pr F ρ₂ x b) := by
  refine ⟨funext fun a => funext fun b => ?_, funext fun a => funext fun b => ?_⟩
  · show Algebra.TensorProduct.map _ _ (_ ⊗ₜ[R] 1) = _
    refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
    congr 1
    all_goals first | exact map_one _ | rfl
  · show Algebra.TensorProduct.map _ _ (1 ⊗ₜ[R] _) = _
    refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
    congr 1
    all_goals first | exact map_one _ | rfl

end GlobalTheory.CompanionTheory.HopfC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialValueOfFactorPullbacksStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bisimplicial_value_of_factor_pullbacks : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {N p q : ℕ} (ρ₁ : Fin (N + 1) →o Fin (p + 1)) (ρ₂ : Fin (N + 1) →o Fin (q + 1)) (x : Cn F N), (bv F ρ₁ ρ₂ (pulln (boxL F) N x) = fun a _ ↦ pr F ρ₁ x a ⊗ₜ[R] 1) ∧ (bv F ρ₁ ρ₂ (pulln (boxR F) N x) = fun _ b ↦ 1 ⊗ₜ[R] pr F ρ₂ x b) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.bv_pulln_box | exact GlobalTheory.CompanionTheory.HopfC.bv_pulln_box | (intros; apply GlobalTheory.CompanionTheory.HopfC.bv_pulln_box <;> assumption)
end
end
