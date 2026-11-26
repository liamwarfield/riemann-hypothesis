module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.CrystallinePeriodsOfSmooth
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HodgeTateSpectral.HTSpecGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtSideGoodHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.SqCore
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HtOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.LatLink
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HtBijOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.FinalC

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.HodgeTateComparisonSmoothProjective
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.DlogClassExistsUnique
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.HT

open Pb
open GlobalTheory.CatH (face toLast)

namespace DlogClassConstruction

theorem mem1 {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {x : B} (hx : x ∈ J) : x ∈ pdP δ 1 := by
  have := dpow_mem_pdP δ 1 hx
  rwa [δ.dpow_one hx] at this

theorem mul2 {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {x y : B} (hx : x ∈ J) (hy : y ∈ J) : x * y ∈ pdP δ 2 :=
  dividedPowerFiltration_mul δ 1 1 (mem1 δ hx) (mem1 δ hy)

theorem four {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {a b c d : B} (ha : a - 1 ∈ J) (hb : b - 1 ∈ J)
    (hc : c - 1 ∈ J) (hd : d - 1 ∈ J) (h : a * b = c * d) : (c - 1) - (b - 1) + (d - 1) - (a - 1) ∈ pdP δ 2 := by
  have := sub_mem (mul2 δ ha hb) (mul2 δ hc hd)
  convert this using 1
  linear_combination (-1 : B) * h

theorem five {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {r' r a b c : B} (hr' : r' - 1 ∈ J) (hr : r - 1 ∈ J)
    (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) (hc : c - 1 ∈ J) (h : r' * c = r * a * b) :
    ((b - 1) - (c - 1) + (a - 1)) - ((r' - 1) - (r - 1)) ∈ pdP δ 2 := by
  have hra : r * a - 1 ∈ J := by
    have := add_mem (J.mul_mem_left r ha) hr
    convert this using 1; ring
  have := sub_mem (sub_mem (mul2 δ hr' hc) (mul2 δ hr ha)) (mul2 δ hra hb)
  convert this using 1
  linear_combination (-1 : B) * h

theorem plog_sub {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) {x : B} (hx : x ∈ J) :
    x - plogK δ (s + 1) x ∈ pdP δ 2 := by
  unfold plogK
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, zero_add, δ.dpow_one hx]
  rw [sub_add_cancel_right]
  exact neg_mem (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (dividedPowerFiltration_anti δ (by omega) (dpow_mem_pdP δ _ hx)))

theorem incl_res {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) (j : ℕ)
    (x : CH.H (sq (thFil L r) (thFil L r')) j) :
    ((incl h).sq (incl_fil h r) (incl_fil h r')).pull j ((CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q.ι).pull j x) =
      (CH.Mor.restrict (sq (thFil L r) (thFil L r')) Q'.ι).pull j x := by
  obtain ⟨z, hz, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 x
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun σ => Subtype.ext ?_))
  have key : ∀ (T : Thick L) (h') (w : T.B ⧸ T.pdPow r'.toNat), Ideal.quotientMap (T.pdPow r'.toNat) (RingHom.id T.B) h' w = w := by
    intro T h' w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    rfl
  exact key _ _ _

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
  {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

abbrev Fg (g : C ⥤ Thick (smFun X q)) (r : ℤ) : IdF (g ⋙ thA (smFun X q)) := (thFil (smFun X q) r).res g

abbrev zz (Λ : CLiftK g D) : ∀ σ : ComposableArrows C 2, (g ⋙ thA (smFun X q)).obj (σ.obj (Fin.last 2)) :=
  fun σ => ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1 : (g.obj (σ.obj (Fin.last 2))).B)

def fz (Λ : CLiftK g D) : CH.Cn (sq (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1))) 2 :=
  fun σ => sqMk _ _ (zz Λ σ) (mem1 (g.obj (σ.obj (Fin.last 2))).δ (r_sub_one_mem Λ σ))

theorem fz_coc (Λ : CLiftK g D) : CH.d _ 2 (fz Λ) = 0 := by
  funext τ
  have m0 := GlobalTheory.CompanionTheory.ConeZcoc.mem_J Λ (face 0 τ) (toLast 0 τ)
  have m1 := GlobalTheory.CompanionTheory.ConeZcoc.mem_J Λ (face 1 τ) (toLast 1 τ)
  have m2 := GlobalTheory.CompanionTheory.ConeZcoc.mem_J Λ (face 2 τ) (toLast 2 τ)
  have m3 := GlobalTheory.CompanionTheory.ConeZcoc.mem_J Λ (face 3 τ) (toLast 3 τ)
  have e0 : Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) = Λ.r (face 0 τ) :=
    GlobalTheory.CompanionTheory.ConeZcoc.map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 0 τ) (τ.map_id _) _
  have e1 : Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) = Λ.r (face 1 τ) :=
    GlobalTheory.CompanionTheory.ConeZcoc.map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 1 τ) (τ.map_id _) _
  have e2 : Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) = Λ.r (face 2 τ) :=
    GlobalTheory.CompanionTheory.ConeZcoc.map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 2 τ) (τ.map_id _) _
  have key : Units.map (g.map (toLast 3 τ)).φ.toMonoidHom (Λ.r (face 3 τ)) *
      Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) =
      Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) *
      Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) := by
    rw [e0, e1, e2]
    exact GlobalTheory.CompanionTheory.ConeZcoc.rr_coboundary Λ (τ.map' 0 1) (τ.map' 1 2) (τ.map' 2 3) (τ.map' 0 2) (τ.map' 1 3) (τ.map' 0 3)
      (τ.map'_comp 0 1 2) (τ.map'_comp 1 2 3)
  have hval := congrArg (Units.val) key
  rw [Units.val_mul, Units.val_mul] at hval
  have p := four (g.obj (τ.obj (Fin.last 3))).δ m3 m1 m0 m2 hval
  have hi : ∀ i : Fin 4, ((sq (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1))).map (toLast i τ)).hom (fz Λ (face i τ)) =
      sqMk (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1)) (T := τ.obj (Fin.last 3))
        (((Units.map (g.map (toLast i τ)).φ.toMonoidHom (Λ.r (face i τ)) : (g.obj (τ.obj (Fin.last 3))).Bˣ) :
          (g.obj (τ.obj (Fin.last 3))).B) - 1 : (g.obj (τ.obj (Fin.last 3))).B)
        (mem1 (g.obj (τ.obj (Fin.last 3))).δ (GlobalTheory.CompanionTheory.ConeZcoc.mem_J Λ (face i τ) (toLast i τ))) := fun i =>
    Subtype.ext (congrArg (Ideal.Quotient.mk _) (by
      change (g.map (toLast i τ)).φ (_ - 1) = _
      rw [map_sub, map_one]; rfl))
  change ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • ((sq (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1))).map (toLast i τ)).hom
    (fz Λ (face i τ)) = 0
  rw [Fin.sum_univ_four, hi, hi, hi, hi]
  have fin : ∀ {M : Type} [AddCommGroup M] (a b c d : M), a - b + c - d = 0 →
      (-1 : ℤ) ^ ((0 : Fin 4) : ℕ) • a + (-1 : ℤ) ^ ((1 : Fin 4) : ℕ) • b + (-1 : ℤ) ^ ((2 : Fin 4) : ℕ) • c +
        (-1 : ℤ) ^ ((3 : Fin 4) : ℕ) • d = 0 := by
    intro M _ a b c d h
    change (-1 : ℤ) ^ 0 • a + (-1 : ℤ) ^ 1 • b + (-1 : ℤ) ^ 2 • c + (-1 : ℤ) ^ 3 • d = 0
    rw [← h]
    norm_num
    abel
  exact fin _ _ _ _ (Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 p))

def cz (Λ : CLiftK g D) : CH.H (sq (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1))) 2 := (CH.cx _).cls (fz Λ) (fz_coc Λ)

theorem rep_cz (Λ : CLiftK g D) : Rep (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1)) (zz Λ) (cz Λ) :=
  ⟨fz Λ, fz_coc Λ, rfl, fun _ => rfl⟩

open GlobalTheory.CompanionTheory.ConeZcls in
theorem eps_rel (Λ Λ' : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ)
    (hv : ∀ c, Ideal.Quotient.mk (g.obj c).J ((v c : (g.obj c).Bˣ) : (g.obj c).B) =
      ub (Λ.p c) (Λ'.p c) ((Λ.hp c).trans (Λ'.hp c).symm)) {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂) (χ : c₀ ⟶ c₂)
    (hχ : χ = φ ≫ ψ) : ((Units.val (eps Λ Λ' v ψ) - 1) - (Units.val (eps Λ Λ' v χ) - 1) + (g.map ψ).φ (Units.val (eps Λ Λ' v φ) - 1)) -
      ((Units.val (GlobalTheory.CompanionTheory.ConeZcls.rr Λ' φ ψ χ) - 1) - (Units.val (GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ) - 1)) ∈ pdP (g.obj c₂).δ 2 := by
  have e0 := (g.map ψ).hle (eps_sub Λ Λ' v hv φ)
  rw [Ideal.mem_comap, map_sub, map_one] at e0
  have key := rr_eq Λ Λ' v φ ψ χ hχ
  have key' := congrArg Units.val (mul_inv_eq_iff_eq_mul.1 key.symm).symm
  rw [Units.val_mul, Units.val_mul, Units.val_mul] at key'
  rw [map_sub, map_one]
  exact five (g.obj c₂).δ (GlobalTheory.CompanionTheory.ConeUnit.r_sub_mem Λ' φ ψ χ hχ) (GlobalTheory.CompanionTheory.ConeUnit.r_sub_mem Λ φ ψ χ hχ) e0
    (eps_sub Λ Λ' v hv ψ) (eps_sub Λ Λ' v hv χ) key'

open GlobalTheory.CompanionTheory.ConeZcls in
theorem cz_eq (Λ Λ' : CLiftK g D) : cz Λ' = cz Λ := by
  have hl : ∀ c, ∃ v : (g.obj c).Bˣ, Ideal.Quotient.mk (g.obj c).J ((v : (g.obj c).Bˣ) : (g.obj c).B) =
      ub (Λ.p c) (Λ'.p c) ((Λ.hp c).trans (Λ'.hp c).symm) :=
    fun c => exists_unit_lift (g.obj c) _ (ub_isUnit _ _ _)
  choose v hv using hl
  let F := sq (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1))
  let ε : ∀ {c c' : C}, (c ⟶ c') → F.obj c' := fun {c c'} φ =>
    sqMk (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1)) (T := c') (((eps Λ Λ' v φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 : (g.obj c').B)
      (mem1 (g.obj c').δ (eps_sub Λ Λ' v hv φ))
  let e : CH.Cn F 1 := fun τ => ε (τ.map' 0 1)
  refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) 2).2.2.1 _ _ _ _).2 ⟨e, ?_⟩
  funext σ
  have h0 : (F.map (toLast 0 σ)).hom (e (face 0 σ)) = ε (σ.map' 1 2) := map_self F σ (Fin.last 2) _ _
  have h1 : (F.map (toLast 1 σ)).hom (e (face 1 σ)) = ε (σ.map' 0 2) := map_self F σ (Fin.last 2) _ _
  have h2 : (F.map (toLast 2 σ)).hom (e (face 2 σ)) = (F.map (σ.map' 1 2)).hom (ε (σ.map' 0 1)) := rfl
  have p := eps_rel Λ Λ' v hv (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) (composable_arrows_map_zero_two σ)
  change ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i σ)).hom (e (face i σ)) = fz Λ' σ - fz Λ σ
  rw [Fin.sum_univ_three, h0, h1, h2]
  have fin : ∀ {M : Type} [AddCommGroup M] (a b c d : M), a - b + c - d = 0 →
      (-1 : ℤ) ^ ((0 : Fin 3) : ℕ) • a + (-1 : ℤ) ^ ((1 : Fin 3) : ℕ) • b + (-1 : ℤ) ^ ((2 : Fin 3) : ℕ) • c = d := by
    intro M _ a b c d h
    change (-1 : ℤ) ^ 0 • a + (-1 : ℤ) ^ 1 • b + (-1 : ℤ) ^ 2 • c = d
    rw [← sub_eq_zero, ← h]
    norm_num
    abel
  exact fin _ _ _ _ (Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 p))

omit [CharZero K] in
theorem lift_ex (g : C ⥤ Thick (smFun X q)) (D : E.LineData X) (h : ∀ c, ∃ V ∈ 𝒱D D, InU V (g.obj c)) : Nonempty (CLiftK g D) := by
  have hp : ∀ c : C, ∃ p : Spec (CommRingCat.of ((g.obj c).B ⧸ (g.obj c).J)) ⟶ D.Y, p ≫ D.f = pt (g.obj c) := by
    intro c
    obtain ⟨V, ⟨σ, hσ⟩, hV⟩ := h c
    have hr : Set.range (pt (g.obj c)) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
    refine ⟨IsOpenImmersion.lift V.ι (pt (g.obj c)) hr ≫ σ, ?_⟩
    rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]
  choose p hp using hp
  have hw : ∀ {c c' : C} (φ : c ⟶ c'), ∃ w : (g.obj c').Bˣ,
      ∀ (h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f),
        Ideal.Quotient.mk (g.obj c').J w = (Scheme.ΓSpecIso (CommRingCat.of ((g.obj c').B ⧸ (g.obj c').J))).hom.hom
          (D.u (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle)) ≫ p c) (p c') h) := by
    intro c c' φ
    by_cases h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f
    · obtain ⟨w, hw⟩ := GlobalTheory.CompanionTheory.ConeZcls.exists_unit_lift (g.obj c') _ (GlobalTheory.CompanionTheory.ConeZcls.ub_isUnit _ _ h)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose w hw using @hw
  exact ⟨{ p := p, hp := hp, w := fun φ => w φ, hw := fun φ h => hw φ h }⟩

variable (q)

abbrev Q0 (𝒱 : Set X.Opens) : ObjectProperty (Thick (smFun X q)) :=
  St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ 𝒱

omit [CharZero K] in
theorem res_ks (s a j : ℕ) (hs : a < s) (𝒱 : Set X.Opens) (h : sSup 𝒱 = ⊤) :
    Function.Bijective ((CH.Mor.restrict (grT (smFun X q) a) (KS q s 𝒱).ι).pull j) := by
  have b := GlobalTheory.CompanionTheory.KIso.chain_bij q s 𝒱 h (a : ℤ) ((a : ℤ) + 1) (by omega) j
  have e : GlobalTheory.CompanionTheory.KIso.chain q s 𝒱 (a : ℤ) ((a : ℤ) + 1) j =
      fun x => (CH.Mor.restrict (grT (smFun X q) a) (KS q s 𝒱).ι).pull j x :=
    funext fun x => (congrArg _ (incl_res (GlobalTheory.CompanionTheory.KIso.top_ge q s) _ _ j x)).trans (incl_res (GlobalTheory.CompanionTheory.KIso.st_le q s 𝒱) _ _ j x)
  rw [e] at b
  exact b

omit [CharZero K] in
theorem restriction_open_cover_bijective (a j : ℕ) (𝒱 : Set X.Opens) (h : sSup 𝒱 = ⊤) :
    Function.Bijective ((CH.Mor.restrict (grT (smFun X q) a) (Q0 q 𝒱).ι).pull j) := by
  have hle : KS q (a + 1) 𝒱 ≤ Q0 q 𝒱 := fun _ h => ⟨trivial, h.2⟩
  have b1 := Pb.refl (γ := dividedPowersBot K) (q := q) (κ := Ideal.Quotient.mk ⊥) ⊤ 1 (a + 1) (Or.inl ⟨rfl, rfl⟩) 𝒱 hle
    (a : ℤ) ((a : ℤ) + 1) (by push_cast; omega) j
  have b := res_ks q (a + 1) a j (by omega) 𝒱 h
  refine ⟨fun x y hxy => b.1 ?_, fun y => ?_⟩
  · exact (incl_res hle _ _ j x).symm.trans ((congrArg _ hxy).trans (incl_res hle _ _ j y))
  · obtain ⟨x, hx⟩ := b.2 (((incl hle).sq (incl_fil hle (a : ℤ)) (incl_fil hle ((a : ℤ) + 1))).pull j y)
    exact ⟨x, b1.1 ((incl_res hle _ _ j x).trans hx)⟩

theorem pow_rep (g : C ⥤ Thick (smFun X q)) (c : Hdg q 1 2) (z : CH.Cn (CH.modF (g ⋙ thA (smFun X q))) 2)
    (hz : ∀ s, z s ∈ (Fg g ((1 : ℕ) : ℤ)).S _)
    (hc : Rep (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1)) z ((CH.Mor.restrict (grT (smFun X q) 1) g).pull 2 c)) (k : ℕ) :
    (∀ s, cupPowC (g ⋙ thA (smFun X q)) z k s ∈ (Fg g (k : ℤ)).S _) ∧
    Rep (Fg g (k : ℤ)) (Fg g ((k : ℤ) + 1)) (cupPowC (g ⋙ thA (smFun X q)) z k)
      ((CH.Mor.restrict (grT (smFun X q) k) g).pull (2 * k) (powH q c k)) := by
  induction k with
  | zero =>
    refine ⟨fun s => ?_, _, _, rfl, fun s => rfl⟩
    change _ ∈ (g.obj _).pdPow 0
    rw [Thick.pdPow_zero]; trivial
  | succ k ih =>
    have ok : MulOk (Fg g (k : ℤ)) (Fg g ((k : ℤ) + 1)) (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1))
        (Fg g ((k + 1 : ℕ) : ℤ)) (Fg g (((k + 1 : ℕ) : ℤ) + 1)) :=
      ⟨fun T _ _ => (grOk (smFun X q) rfl).aa (g.obj T), fun T _ _ => (grOk (smFun X q) rfl).ab (g.obj T),
        fun T _ _ => (grOk (smFun X q) rfl).ba (g.obj T)⟩
    have h := rep_cup ok (show 2 * k + 2 = 2 * (k + 1) by omega) _ z ih.1 hz ih.2 hc
    have key := CrystallineSemistableComparison.P.cup_pull (grOk (smFun X q) (rfl : k + 1 = k + 1)).pair ok.pair g
      (fun _ => LinearMap.id) (fun _ => LinearMap.id) (fun _ => LinearMap.id)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (show 2 * k + 2 = 2 * (k + 1) by omega) (powH q c k) c
    exact ⟨h.1, key ▸ h.2⟩

end DlogClassConstruction

open DlogClassConstruction

theorem dlog_class_exists_unique : DlogClassExistsUnique := by
  intro K _ _ X q D hD
  have hb := restriction_open_cover_bijective q 1 2 (𝒱D D) hD
  have hU : ∀ c : (Q0 q (𝒱D D)).FullSubcategory, ∃ V ∈ 𝒱D D, InU V ((Q0 q (𝒱D D)).ι.obj c) := fun c => c.property.2
  obtain ⟨Λ₀⟩ := lift_ex (Q0 q (𝒱D D)).ι D hU
  obtain ⟨x, hx⟩ := hb.2 (cz Λ₀)
  refine ⟨x, fun C _ g hg Λ => ?_, fun y hy => hb.1 ((rep_uniq (hy _ _ hU Λ₀) (rep_cz Λ₀)).trans hx.symm)⟩
  let h : C ⥤ (Q0 q (𝒱D D)).FullSubcategory := (Q0 q (𝒱D D)).lift g fun c => ⟨trivial, hg c⟩
  have e1 : (CH.Mor.restrict (grT (smFun X q) 1) g).pull 2 x =
      (CH.Mor.restrict ((Q0 q (𝒱D D)).ι ⋙ grT (smFun X q) 1) h).pull 2 ((CH.Mor.restrict (grT (smFun X q) 1) (Q0 q (𝒱D D)).ι).pull 2 x) :=
    (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict (grT (smFun X q) 1) (Q0 q (𝒱D D)).ι)
      (CH.Mor.restrict ((Q0 q (𝒱D D)).ι ⋙ grT (smFun X q) 1) h) 2 x).1
  have e2 : (CH.Mor.restrict (grT (smFun X q) 1) g).pull 2 x = cz Λ :=
    e1.trans ((congrArg _ hx).trans (cz_eq Λ (Λ₀.precomp h)))
  rw [e2]
  exact rep_cz Λ

theorem kTop : KTop := by
  intro K _ _ X q _ d _ D hD c hc h0
  obtain ⟨c', hc'⟩ := isFirstChernDeRham_exists q d D hD
  refine powK_ne_zero q d D hD c' hc' ?_
  obtain ⟨N, i, hi, hip, hO⟩ := hD
  have hP : IsProper q := GlobalTheory.CommonModel.isProper_of_isProjOver ⟨N, i, hi, hip⟩
  obtain ⟨U, hUd⟩ := (cov_ex q).2 d inferInstance
  have hcov : sSup (𝒱D D) = ⊤ := sSup_𝒱D D N i hO
  have hk := (k_iso_pf q U (d + 1) (fun α => by rw [hUd]; omega) (𝒱D D) hcov (2 * d)).1
  let g := (KS q (d + 1) (𝒱D D)).ι
  obtain ⟨Λ⟩ := lift_exists q D (d + 1)
  obtain ⟨z, hz, hzf, hzc⟩ := hc' (d + 1) _ g (fun c => c.property.1.1) (fun c => by
    obtain ⟨-, V, ⟨σ, hσ⟩, hV⟩ := c.property
    exact ⟨V, σ, hσ, hV⟩) Λ
  have r1 := hc _ g (fun c => c.property.2) Λ
  have r2 : Rep (Fg g ((1 : ℕ) : ℤ)) (Fg g (((1 : ℕ) : ℤ) + 1)) z ((CH.Mor.restrict (grT (smFun X q) 1) g).pull 2 c) :=
    rep_congr (fun s => by
      have := plog_sub (g.obj (s.obj (Fin.last 2))).δ d (r_sub_one_mem Λ s)
      rw [← hzf s] at this
      exact this) r1
  have r3 := (pow_rep q g c z (fun s => by
      have := mem1 (g.obj (s.obj (Fin.last 2))).δ (plogK_mem (g.obj (s.obj (Fin.last 2))).δ (d + 1) (r_sub_one_mem Λ s))
      rw [← hzf s] at this
      exact this) r2 d).2
  rw [h0, map_zero] at r3
  obtain ⟨hp, ep⟩ := powK_pull q g c' z hz hzc d
  have := cls_zero_of_rep (fun T => T.property.1.1) _ hp r3
  exact hk.1 ((ep.symm.trans this).trans (map_zero _).symm)

end CrystallineSemistableComparison.HT
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KFin
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.HT

theorem kFin : KFin := @kFin_of (@Pb.finO'.2)

end CrystallineSemistableComparison.HT
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.LvLink
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.HT

theorem lvEx (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] : LvEx l K :=
  lvEx_of l K levSys_ex

end CrystallineSemistableComparison.HT
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.HT

theorem hodgeTate_of_etale_side (h : EtSideS) : HodgeTateMapExists := ht_of lvEx kFin dlog_class_exists_unique kTop h

end CrystallineSemistableComparison.HT
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.SpecOf
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.SigCEq
theorem UpperTheory.Gal.Seam.sigC_eq :
    ∀ (l : ℕ) [Fact l.Prime] (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (y : ℂ_[l]), GaloisFrobeniusFixed.σC g y = Formalism.Per.σC g y := by
  intro l _ g y
  induction y using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (GroundTheory.PAdicHodge.continuous_galCp (GaloisFrobeniusFixed.toBot g))
      (AddMonoidHomClass.isometry_of_norm (Formalism.Per.σC g) (GlobalTheory.RingBasics.norm_σC g)).continuous
  | ih a =>
    rw [GlobalTheory.RingBasics.σC_coe]
    exact GroundTheory.PAdicHodge.galCp_coe (GaloisFrobeniusFixed.toBot g) a
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Gal.Seam.Spec

open CrystallineSemistableComparison CrystallineSemistableComparison.HTSpecB

open GlobalTheory.HTLink

def HdgIso : Prop := ∀ (K : Type) [Field K] [CharZero K],
    ∃ e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] [IsProper q] (a j : ℕ),
      CrystallineSemistableComparison.HT.Hdg q a (a + j) ≃ₗ[K] CrystallineSemistableComparison.Om.HodgeC q a j,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [IsProper q]
      [Smooth p] [IsProper p] (u : X ⟶ Y) (hu : u ≫ p = q) (a j : ℕ) (x : CrystallineSemistableComparison.HT.Hdg p a (a + j)),
      e q a j (CrystallineSemistableComparison.HT.pullH u hu a (a + j) x) = CrystallineSemistableComparison.Om.pullC u hu a j (e p a j x)

section Proj

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isProper_pstr (R : Type) [CommRing R] (N : ℕ) : IsProper (PSpace.str R N) := by
  have : IsScalarTower R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) (MvPolynomial (Fin (N + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  have : IsClosedImmersion (spMap (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))) := by
    apply IsClosedImmersion.spec_of_surjective
    rintro ⟨p, hp⟩
    have h0 : p.totalDegree = 0 := Nat.le_zero.1 (MvPolynomial.IsHomogeneous.totalDegree_le hp)
    exact ⟨p.coeff 0, Subtype.ext (MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 h0).symm⟩
  unfold PSpace.str
  infer_instance

end Proj

section Mat

variable {R : Type} [Field R] {m : Type} [Fintype m] [DecidableEq m] {d : ℕ}

theorem exists_inv_of_inj (H : Matrix m (Fin d) R) (hc : Fintype.card m = d) (hi : ∀ z, H.mulVec z = 0 → z = 0) :
    ∃ Ψ : Matrix (Fin d) m R, Ψ * H = 1 ∧ H * Ψ = 1 := by
  let e : m ≃ Fin d := Fintype.equivFinOfCardEq hc
  let H' : Matrix (Fin d) (Fin d) R := H.submatrix e.symm id
  have hdet : H'.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv
    apply hi
    funext c
    have := congrFun hv0 (e c)
    simpa [H', Matrix.mulVec, dotProduct] using this
  have hu : IsUnit H'.det := isUnit_iff_ne_zero.2 hdet
  have hH : H = H'.submatrix e (Equiv.refl (Fin d)) := by
    funext c i
    simp [H']
  refine ⟨H'⁻¹.submatrix (Equiv.refl (Fin d)) e, ?_, ?_⟩
  · rw [hH, Matrix.submatrix_mul_equiv, Matrix.nonsing_inv_mul _ hu, Matrix.submatrix_one_equiv]
  · rw [hH, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hu, Matrix.submatrix_one_equiv]

def invM (H : Matrix m (Fin d) R) : Matrix (Fin d) m R :=
  open Classical in
  if h : ∃ Ψ : Matrix (Fin d) m R, Ψ * H = 1 ∧ H * Ψ = 1 then h.choose else 0

theorem invM_spec (H : Matrix m (Fin d) R) (h : ∃ Ψ : Matrix (Fin d) m R, Ψ * H = 1 ∧ H * Ψ = 1) :
    invM H * H = 1 ∧ H * invM H = 1 := by
  unfold invM
  rw [dite_eq_left h]
  exact h.choose_spec

theorem mul_inv_twist {n : Type} [Fintype n] [DecidableEq n] (H : Matrix m n R) (Φ : Matrix n m R) (ρ : Matrix n n R)
    (D Dp : Matrix m m R) (Hσ : Matrix m n R) (Φσ : Matrix n m R) (h1 : Φ * H = 1) (h2 : D * Dp = 1)
    (h3 : Dp * (H * ρ) = Hσ) (h4 : Hσ * Φσ = 1) : ρ * Φσ = Φ * D := by
  calc ρ * Φσ = Φ * H * ρ * Φσ := by rw [h1, Matrix.one_mul]
    _ = Φ * (D * Dp) * H * ρ * Φσ := by rw [h2, Matrix.mul_one]
    _ = Φ * D * (Dp * (H * ρ)) * Φσ := by simp only [Matrix.mul_assoc]
    _ = Φ * D := by rw [h3, Matrix.mul_assoc (Φ * D), h4, Matrix.mul_one]

theorem mul_inv_nat {n m' n' : Type} [Fintype n] [DecidableEq n] [Fintype m'] [DecidableEq m'] [Fintype n']
    [DecidableEq n'] (H : Matrix m n R) (Φ : Matrix n m R) (H' : Matrix m' n' R) (Φ' : Matrix n' m' R) (E : Matrix n' n R)
    (G : Matrix m' m R) (h1 : Φ' * H' = 1) (h2 : H * Φ = 1) (h : H' * E = G * H) : E * Φ = Φ' * G := by
  calc E * Φ = Φ' * H' * E * Φ := by rw [h1, Matrix.one_mul]
    _ = Φ' * (G * H) * Φ := by rw [Matrix.mul_assoc Φ' H' E, h]
    _ = Φ' * G := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]

end Mat

section Dict

variable {l : ℕ} [Fact l.Prime] {K : Formalism.BasicNotions.Loc.FinExt l}

theorem sigma_eq (g : Formalism.BasicNotions.Loc.GQ l) (y : ℂ_[l]) : GaloisFrobeniusFixed.σC g y = Formalism.Per.σC g y := UpperTheory.Gal.Seam.sigC_eq l g y

end Dict

section Build

variable {l : ℕ} [Fact l.Prime] {K : Formalism.BasicNotions.Loc.FinExt l}

theorem sm_q {M : CrystallineSemistableComparison.Model l K.1} (h : M.Sm) : IsProper M.q ∧ Smooth M.q := by
  obtain ⟨N, i, hi, hc⟩ := h.1.1
  have := isProper_pstr (CrystallineSemistableComparison.OK l K.1) N
  have hp : IsProper M.p := by rw [← hc]; infer_instance
  have hs : Smooth M.p := h.2
  exact ⟨inferInstance, inferInstance⟩


variable (K) in
abbrev IsoFam : Type 1 := ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K.1)) [Smooth q] [IsProper q] (a j : ℕ),
  CrystallineSemistableComparison.HT.Hdg q a (a + j) ≃ₗ[K.1] CrystallineSemistableComparison.Om.HodgeC q a j

def IsoNat (e : IsoFam K) : Prop := ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K.1))
  (p : Y ⟶ Spec (CommRingCat.of K.1)) [Smooth q] [IsProper q] [Smooth p] [IsProper p] (u : X ⟶ Y) (hu : u ≫ p = q)
  (a j : ℕ) (x : CrystallineSemistableComparison.HT.Hdg p a (a + j)), e q a j (CrystallineSemistableComparison.HT.pullH u hu a (a + j) x) = CrystallineSemistableComparison.Om.pullC u hu a j (e p a j x)

def eqv (e : IsoFam K) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K.1)) [Smooth q] [IsProper q] (a j m : ℕ)
    (h : a + j = m) : CrystallineSemistableComparison.HT.Hdg q a m ≃ₗ[K.1] CrystallineSemistableComparison.Om.HodgeC q a j := by
  subst h
  exact e q a j

theorem eqv_nat (e : IsoFam K) (he : IsoNat e) {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K.1))
    (p : Y ⟶ Spec (CommRingCat.of K.1)) [Smooth q] [IsProper q] [Smooth p] [IsProper p] (u : X ⟶ Y) (hu : u ≫ p = q)
    (a j m : ℕ) (h : a + j = m) (x : CrystallineSemistableComparison.HT.Hdg p a m) :
    eqv e q a j m h (CrystallineSemistableComparison.HT.pullH u hu a m x) = CrystallineSemistableComparison.Om.pullC u hu a j (eqv e p a j m h x) := by
  subst h
  exact he q p u hu a j x

theorem add_sub_fin {n : ℕ} (a : Fin (n + 1)) : (a : ℕ) + (n - a) = n := Nat.add_sub_cancel' (Nat.le_of_lt_succ a.2)

def hb (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ} (F : Frame (K := K) M.q n) (a : Fin (n + 1)) :
    Module.Basis (Fin (F.e a)) K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n) :=
  have := (sm_q hM).1
  have := (sm_q hM).2
  (F.c a).map (eqv e M.q a (n - a) n (add_sub_fin a)).symm

def bV {M : CrystallineSemistableComparison.Model l K.1} {n : ℕ} (F : Frame (K := K) M.q n) : Module.Basis (Fin F.d) ℚ_[l] (M.V n) := F.b

def Hm (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (F : Frame (K := K) M.q n) : Matrix F.Col (Fin F.d) ℂ_[l] :=
  fun c i => P.h M c.1 n (bV F i) ((hb e hM F c.1).coord c.2)

def Phi (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (F : Frame (K := K) M.q n) : Matrix (Fin F.d) F.Col ℂ_[l] :=
  invM (Hm P e hM F)

theorem sum_e (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (hr : Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n))
    (F : Frame (K := K) M.q n) : ∑ a, F.e a = F.d := by
  have h1 : ∀ a : Fin (n + 1), F.e a = Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n) := fun a => by
    rw [Module.finrank_eq_card_basis (hb e hM F a), Fintype.card_fin]
  have h2 : F.d = Module.finrank ℚ_[l] (M.V n) := by
    have := Module.finrank_eq_card_basis F.b
    rw [Fintype.card_fin] at this
    exact this.symm
  rw [h2, hr, Finset.sum_congr rfl (fun a _ => h1 a)]
  exact Fin.sum_univ_eq_sum_range (fun a => Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n)) (n + 1)

theorem h_dual (P : CrystallineSemistableComparison.HT.HTPre l K.1) (M : CrystallineSemistableComparison.Model l K.1) (a n : ℕ) (v : M.V n) {ι : Type} (s : Finset ι)
    (c : ι → K.1) (φ : ι → Module.Dual K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n)) :
    P.h M a n v (∑ i ∈ s, c i • φ i) = ∑ i ∈ s, CrystallineSemistableComparison.HT.kC K.1 (c i) * P.h M a n v (φ i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => P.lin' M a n (c i) v (φ i)

theorem h_vec (P : CrystallineSemistableComparison.HT.HTPre l K.1) (M : CrystallineSemistableComparison.Model l K.1) (a n : ℕ) {ι : Type} (s : Finset ι) (r : ι → ℚ_[l])
    (v : ι → M.V n) (φ : Module.Dual K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n)) :
    P.h M a n (∑ i ∈ s, r i • v i) φ = ∑ i ∈ s, CrystallineSemistableComparison.HT.qC l (r i) * P.h M a n (v i) φ := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, AddMonoidHom.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => P.lin M a n (r i) (v i) φ

theorem hm_inj (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (hI : P.Inj M n) (F : Frame (K := K) M.q n) (z : Fin F.d → ℂ_[l]) (hz : (Hm P e hM F).mulVec z = 0) : z = 0 := by
  apply hI (bV F) z
  intro a φ
  by_cases ha : a ≤ n
  · let a' : Fin (n + 1) := ⟨a, Nat.lt_succ_of_le ha⟩
    let B : Module.Basis (Fin (F.e a')) K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n) := hb e hM F a'
    have hφ : φ = ∑ s, φ (B s) • B.coord s := (Module.Basis.sum_dual_apply_smul_coord B φ).symm
    have hrow : ∀ i, P.h M a n (bV F i) φ = ∑ s, CrystallineSemistableComparison.HT.kC K.1 (φ (B s)) * Hm P e hM F ⟨a', s⟩ i := by
      intro i
      calc P.h M a n (bV F i) φ = P.h M a n (bV F i) (∑ s, φ (B s) • B.coord s) := by rw [← hφ]
        _ = _ := by rw [h_dual]; rfl
    calc ∑ i, z i * P.h M a n (bV F i) φ
        = ∑ s, CrystallineSemistableComparison.HT.kC K.1 (φ (B s)) * (Hm P e hM F).mulVec z ⟨a', s⟩ := by
          simp only [hrow, Matrix.mulVec, dotProduct, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = 0 := by simp [hz]
  · have : Subsingleton (CrystallineSemistableComparison.HT.Hdg M.q a n) := (P.fin M hM a n).2 (by omega)
    have hφ : φ = 0 := by
      ext x
      rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
    simp [hφ]

theorem phi_spec (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (hr : Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n))
    (hI : P.Inj M n) (F : Frame (K := K) M.q n) :
    Phi P e hM F * Hm P e hM F = 1 ∧ Hm P e hM F * Phi P e hM F = 1 := by
  apply invM_spec
  apply exists_inv_of_inj _ _ (hm_inj P e hM hI F)
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact sum_e e hM hr F

end Build

section Assembly

variable {l : ℕ} [Fact l.Prime] {K : Formalism.BasicNotions.Loc.FinExt l}

theorem equi_entry (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (F : Frame (K := K) M.q n) (σ : ↥(Formalism.BasicNotions.Loc.GK K)) (c : F.Col) (i : Fin F.d) :
    algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l]) ^ (c.1 : ℕ) * (Hm P e hM F * F.rho σ) c i =
      Formalism.Per.σC (σ : Formalism.BasicNotions.Loc.GQ l) (Hm P e hM F c i) := by
  have hexp : (Hm P e hM F * F.rho σ) c i =
      P.h M c.1 n (M.act n σ (bV F i)) ((hb e hM F c.1).coord c.2) := by
    rw [← (bV F).sum_repr (M.act n σ (bV F i)), h_vec]
    simp only [Matrix.mul_apply, Frame.rho, Matrix.map_apply, LinearMap.toMatrix_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
    rfl
  rw [hexp]
  have h := P.equi M hM c.1 n σ (bV F i) ((hb e hM F c.1).coord c.2)
  rw [sigma_eq] at h
  exact h

theorem isHT (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (hr : Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n))
    (hI : P.Inj M n) (F : Frame (K := K) M.q n) : F.IsHT (Phi P e hM F) := by
  obtain ⟨h1, h2⟩ := phi_spec P e hM hr hI F
  refine ⟨⟨Hm P e hM F, h1, h2⟩, fun σ => ?_⟩
  have hx0 : algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l]) ≠ 0 := (map_ne_zero _).2 (Units.ne_zero _)
  refine mul_inv_twist (Hm P e hM F) (Phi P e hM F) (F.rho σ) _
    (Matrix.diagonal fun c : F.Col => algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l]) ^ (c.1 : ℕ))
    ((Hm P e hM F).map (Formalism.Per.σC (σ : Formalism.BasicNotions.Loc.GQ l))) _ h1 ?_ ?_ ?_
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext c
    show algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l]) ^ (-((c.1 : ℕ) : ℤ)) *
      algebraMap ℚ_[l] ℂ_[l] (Formalism.L2.LocGap.Gal.χQ l σ : ℚ_[l]) ^ (c.1 : ℕ) = 1
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hx0)]
  · funext c i
    rw [Matrix.diagonal_mul, Matrix.map_apply]
    exact equi_entry P e hM F σ c i
  · rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]

theorem coord_pull (e : IsoFam K) (he : IsoNat e) {M M' : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) (hM' : M'.Sm) {n : ℕ}
    (F : Frame (K := K) M.q n) (F' : Frame (K := K) M'.q n) (u : M'.X ⟶ M.X) (hu : u ≫ M.p = M'.p) (a : Fin (n + 1))
    (j' : Fin (F'.e a)) :
    (hb e hM' F' a).coord j' ∘ₗ CrystallineSemistableComparison.HT.pullH (CrystallineSemistableComparison.Model.genMap u hu) (CrystallineSemistableComparison.Model.genMap_q u hu) a n =
      ∑ j, LinearMap.toMatrix (F.c a) (F'.c a) (GlobalTheory.HodgeCoh.hodgePull (CrystallineSemistableComparison.Model.genMap_q u hu) a (n - a)) j' j •
        (hb e hM F a).coord j := by
  have := (sm_q hM).1
  have := (sm_q hM).2
  have := (sm_q hM').1
  have := (sm_q hM').2
  have hB : ∀ j, hb e hM F a j = (eqv e M.q a (n - a) n (add_sub_fin a)).symm (F.c a j) := fun j =>
    Module.Basis.map_apply _ _ _
  have hB' : ∀ y j, (hb e hM' F' a).repr y j = (F'.c a).repr (eqv e M'.q a (n - a) n (add_sub_fin a) y) j := by
    intro y j
    simp only [hb, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
  apply (hb e hM F a).ext
  intro j0
  have hnat := eqv_nat e he M'.q M.q (CrystallineSemistableComparison.Model.genMap u hu) (CrystallineSemistableComparison.Model.genMap_q u hu) a (n - a) n (add_sub_fin a)
    ((eqv e M.q a (n - a) n (add_sub_fin a)).symm (F.c a j0))
  rw [LinearEquiv.apply_symm_apply] at hnat
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, LinearMap.toMatrix_apply]
  rw [hB j0, hB', hnat]
  rfl

theorem nat_entry (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) (he : IsoNat e) {M M' : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm)
    (hM' : M'.Sm) {n : ℕ} (F : Frame (K := K) M.q n) (F' : Frame (K := K) M'.q n) (u : M'.X ⟶ M.X)
    (hu : u ≫ M.p = M'.p) :
    Hm P e hM' F' * F.etMat F' (CrystallineSemistableComparison.Model.genMap_q u hu) =
      F.hodgeMat F' (CrystallineSemistableComparison.Model.genMap_q u hu) * Hm P e hM F := by
  funext c' i
  obtain ⟨a, j'⟩ := c'
  have hL : (Hm P e hM' F' * F.etMat F' (CrystallineSemistableComparison.Model.genMap_q u hu)) ⟨a, j'⟩ i =
      P.h M' a n (CrystallineSemistableComparison.Model.pullV u hu n (bV F i)) ((hb e hM' F' a).coord j') := by
    rw [← (bV F').sum_repr (CrystallineSemistableComparison.Model.pullV u hu n (bV F i)), h_vec]
    simp only [Matrix.mul_apply, Frame.etMat, Matrix.map_apply, LinearMap.toMatrix_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
    rfl
  rw [hL, P.nat M' M u hu hM' hM a n (bV F i), coord_pull e he hM hM' F F' u hu a j', h_dual, Matrix.mul_apply,
    Fintype.sum_sigma, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Frame.hodgeMat, Matrix.map_apply, Matrix.blockDiagonal'_apply_eq]
    rfl
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro j _
    simp only [Frame.hodgeMat, Matrix.map_apply, Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hb), map_zero,
      zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem frame_ex (P : CrystallineSemistableComparison.HT.HTPre l K.1) (e : IsoFam K) {M : CrystallineSemistableComparison.Model l K.1} (hM : M.Sm) {n : ℕ}
    (hfd : FiniteDimensional ℚ_[l] (M.V n))
    (hr : Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n)) :
    ∃ F : Frame (K := K) M.q n, ∑ a, F.e a = F.d := by
  have := (sm_q hM).1
  have := (sm_q hM).2
  have : ∀ a : Fin (n + 1), FiniteDimensional K.1 (HodgeV (K := K) M.q n a) := fun a => by
    have := (P.fin M hM a n).1
    exact LinearEquiv.finiteDimensional (eqv e M.q a (n - a) n (add_sub_fin a))
  have : FiniteDimensional ℚ_[l] (EtV (K := K) M.q n) := hfd
  set_option synthInstance.maxHeartbeats 200000 in
  exact ⟨⟨_, Module.finBasis ℚ_[l] (EtV (K := K) M.q n), fun a => _,
    fun a => Module.finBasis K.1 (HodgeV (K := K) M.q n a)⟩, sum_e e hM hr _⟩

end Assembly

theorem htSpecGood_of (hB : CrystallineSemistableComparison.Onto.HTBij) (hI : HdgIso) (hF : CrystallineSemistableComparison.Onto.EtFin) : HTSpecGood := by
  intro l _ K n
  have : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨P, hP⟩ := hB l K.1
  obtain ⟨e, he⟩ := hI K.1
  have hrank : ∀ M : CrystallineSemistableComparison.Model l K.1, M.Sm → (∃ d, SmoothOfRelativeDimension d M.p) →
      Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K.1 (CrystallineSemistableComparison.HT.Hdg M.q a n) :=
    fun M hM hd => ((hP M hM).2.2 hd.choose hd.choose_spec n).2
  refine ⟨fun M hM hd => frame_ex P e hM (hF l K.1 M hM n) (hrank M hM hd), fun M hM hd F => Phi P e hM F,
    fun M hM hd F => isHT P e hM (hrank M hM hd) ((hP M hM).1 n) F, ?_⟩
  intro M M' hM hM' hd hd' F F' u hu
  have h1 := (phi_spec P e hM' (hrank M' hM' hd') ((hP M' hM').1 n) F').1
  have h2 := (phi_spec P e hM (hrank M hM hd) ((hP M hM).1 n) F).2
  exact mul_inv_nat _ _ _ _ _ _ h1 h2 (nat_entry P e he hM hM' F F' u hu)

end UpperTheory.Gal.Seam.Spec
end
end

namespace UpperTheory.Gal.Seam.HT

open UpperTheory.Gal.Seam

open CrystallineSemistableComparison UpperTheory.Gal.KunnethLefschetz

theorem etSideS : EtSideS := fun l _ K _ => Top.etSide_sm_holds l K

theorem hodgeTate_comparison_smooth_projective : CrystallineSemistableComparison.HT.HodgeTateMapExists := CrystallineSemistableComparison.HT.hodgeTate_of_etale_side etSideS

theorem htBij : Onto.HTBij := Onto.htBij_of hodgeTate_comparison_smooth_projective G.sqEx3 Top.diagEt3_holds Top.etFin_holds

theorem htSpecGood : HTSpecB.HTSpecGood := Spec.htSpecGood_of htBij CrystallineSemistableComparison.Om.Nt2F.hodge_iso_natural_cech Top.etFin_holds

end UpperTheory.Gal.Seam.HT
