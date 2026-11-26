module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasisBOfBcOn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftPOfBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransportSymm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousRatioIsUnit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverLatticeBase

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapOAffine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FinOverO

section Les

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem sub_H {R : Type} [CommRing R] (K : Cx.{1} R) (n : ℕ) (h : Subsingleton (K.X n)) : Subsingleton (K.H n) :=
  ⟨fun x y => by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact congrArg _ (Subtype.ext (Subsingleton.elim _ _))⟩

theorem sub_CH (F : C ⥤ ModuleCat.{0} R) (h : ∀ T, Subsingleton (F.obj T)) (n : ℕ) : Subsingleton (CH.H F n) :=
  sub_H (CH.cx F) n ⟨fun x y => funext fun s => (h _).elim _ _⟩

theorem sq_sub (a b : IdF A) (h : ∀ T, a.S T ≤ b.S T) (T : C) : Subsingleton ((sq a b).obj T) :=
  ⟨fun x y => by
    have key : ∀ z : sqM a b T, z = 0 := fun z => by
      obtain ⟨z, hz⟩ := z
      obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hz
      exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (h T hw))
    exact (key x).trans (key y).symm⟩

variable (a c b : IdF A) (hbc : ∀ T, b.S T ≤ c.S T) (hca : ∀ T, c.S T ≤ a.S T)

theorem tau_inj (T : C) (x y : (sq c b).obj T)
    (h : (sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).τ T x =
      (sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).τ T y) : x = y := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : Ideal.Quotient.mk (b.S T) x = Ideal.Quotient.mk (b.S T) y :=
    congrArg (fun z => (show sqM a b T from z).1) h
  exact Subtype.ext h1

theorem tau_surj (T : C) (z : (sq a c).obj T) :
    ∃ y : (sq a b).obj T, (sqLe (a := a) (b := b) (a' := a) (b' := c) (fun _ => le_rfl) hbc).τ T y = z := by
  obtain ⟨x, hx⟩ := z
  obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact ⟨sqMk a b w hw, rfl⟩

theorem tau_ex (T : C) (z : (sq a b).obj T)
    (h : (sqLe (a := a) (b := b) (a' := a) (b' := c) (fun _ => le_rfl) hbc).τ T z = 0) :
    ∃ y : (sq c b).obj T, (sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).τ T y = z := by
  obtain ⟨x, hx⟩ := z
  obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  have h2 : w ∈ c.S T := Ideal.Quotient.eq_zero_iff_mem.1 (congrArg Subtype.val h)
  exact ⟨sqMk c b w h2, rfl⟩

theorem tau_comp (T : C) (y : (sq c b).obj T) :
    (sqLe (a := a) (b := b) (a' := a) (b' := c) (fun _ => le_rfl) hbc).τ T
      ((sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).τ T y) = 0 := by
  obtain ⟨x, hx⟩ := y
  obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 hw)

theorem sq_exact (j : ℕ) :
    Function.Exact ((sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).pull j)
      ((sqLe (a := a) (b := b) (a' := a) (b' := c) (fun _ => le_rfl) hbc).pull j) := by
  have inj : ∀ n, Function.Injective ((sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).hom.f n) :=
    fun n f g h => funext fun s => tau_inj a c b hca _ _ _ (congrFun h s)
  have surj : ∀ n, Function.Surjective ((sqLe (a := a) (b := b) (a' := a) (b' := c) (fun _ => le_rfl) hbc).hom.f n) := by
    intro n f
    choose y hy using fun s : ComposableArrows C n => tau_surj a c b hbc _ (f s)
    exact ⟨y, funext hy⟩
  have ex : ∀ n, Function.Exact ((sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).hom.f n)
      ((sqLe (a := a) (b := b) (a' := a) (b' := c) (fun _ => le_rfl) hbc).hom.f n) := by
    intro n f
    constructor
    · intro h
      choose y hy using fun s : ComposableArrows C n => tau_ex a c b hbc hca _ (f s) (congrFun h s)
      exact ⟨y, funext hy⟩
    · rintro ⟨g, rfl⟩
      exact funext fun s => tau_comp a c b hbc hca _ (g s)
  obtain ⟨δ, -, -, e1, -, -⟩ := CrystallineSemistableComparison.P.les _ _ inj ex surj
  exact e1 j

end Les

section Chart

theorem dividedPowerFiltration_bot (O : Type) [CommRing O] {k : ℕ} (hk : 1 ≤ k) : pdP (dividedPowersBot O) k = ⊥ := by
  classical
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨l, hl, hr, rfl⟩
  have : ∃ q ∈ l, 1 ≤ q.1 := by
    by_contra hcon
    push_neg at hcon
    have : (l.map Prod.fst).sum = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      have := hcon q hq
      omega
    omega
  obtain ⟨q, hq, h1⟩ := this
  have h0 : (dividedPowersBot O).dpow q.1 q.2 = 0 := by
    have : q.2 = 0 := by simpa using hl q hq
    rw [this]
    exact (dividedPowersBot O).dpow_eval_zero (by omega)
  exact List.prod_eq_zero (List.mem_map.2 ⟨q, hq, h0⟩)

variable {O : Type} [CommRing O]

theorem van_coord (hLoc : KH.LocGr) (hPoly : KH.PolyTf) (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (r : ℕ) (hr : r < s) (b : ℕ) (hne : b ≠ r) :
    Subsingleton (HU (sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1)))
      (St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {W}) b) := by
  obtain ⟨c', e, hTF, -, -, -⟩ := GlobalTheory.T.exists_chart_from_coordinates (dividedPowersBot O) l s hb q (Ideal.Quotient.mk ⊥) (fun _ => rfl) c
  have hg := GlobalTheory.T.chart_is_good c'
  let Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))) := St (TF l s) {W}
  have hQ : ∀ T, Q T → InU W T := fun T hT => by
    obtain ⟨_, V, hV, h⟩ := hT
    rw [Set.mem_singleton_iff.1 hV] at h
    exact h
  have hD : Q c'.D := ⟨hTF, W, rfl, c'.inV⟩
  obtain ⟨hpd, hgc⟩ := GlobalTheory.T.chart_divided_powers_graded_constant c' hg Q hQ hD
  obtain ⟨P, hP⟩ := hPoly (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  let E := c'.frame hg Q hQ hD
  let σ : ∀ T, E.D ⟶ T := fun T => (E.ne T).some
  have main := hLoc P (GlobalTheory.T.sheaf_filtration_property Q) E σ hgc (r : ℤ) (fun r' hr' => (hP r' (by omega)).1) b
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, r = b + k := ⟨r - b, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have hall : ∀ z : CH.H (gr (sFil Q) (r : ℤ)) b, z = 0 := by
      intro z
      obtain ⟨x, hx, f, hf, rfl, hfs⟩ := (main.2 k (by push_cast; omega)).1 z
      have hx0 : ∀ I, x I = 0 := fun I => by
        have h2 : x I ∈ c'.D.pdPow ((k : ℤ).toNat) := hx I
        rw [Int.toNat_natCast] at h2
        rw [hpd k, dividedPowerFiltration_bot O hk1, Ideal.map_bot] at h2
        exact h2
      have f0 : f = 0 := funext fun s => Subtype.ext (by
        rw [hfs s]
        simp [hx0, Frame.form])
      subst f0
      exact Submodule.Quotient.mk_zero _
    exact ⟨fun y z => (hall y).trans (hall z).symm⟩
  · exact main.1 (by exact_mod_cast hgt)

end Chart

section Glob

variable {O : Type} [CommRing O]

theorem capO_affine {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (U : Cov q) {n : ℕ} (i : Fin (n + 1) → U.ι) :
    IsAffineOpen (capO U.U i) := by
  classical
  have h := U.inter (Finset.univ.image i) ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have e : (⨅ α ∈ Finset.univ.image i, U.U α) = capO U.U i := by
    refine le_antisymm (le_iInf fun a => ?_) (le_iInf₂ fun α hα => ?_)
    · exact iInf₂_le (i a) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
      exact capO_le U.U i a
  rwa [e] at h

set_option maxHeartbeats 2000000 in
theorem gr_range [IsNoetherianRing O] (hLoc : KH.LocGr) (hPoly : KH.PolyTf) (hSer : KH.GlobSerreSt) (hCech : KH.GrCechFin)
    (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q]
    (U : Cov q) (r : ℤ) (hr : r < s) (j : ℕ) : Module.Finite O (HQ (TO q l s (Set.range U.U)) r (r + 1) j) := by
  obtain ⟨𝒮, h𝒮⟩ := GlobalTheory.T.finite_modules_serre_class O
  rcases lt_or_ge r 0 with h0 | h0
  · refine (h𝒮 _).1 (𝒮.zero _ (sub_CH _ (sq_sub _ _ fun T => ?_) j))
    have e1 : r.toNat = 0 := by omega
    have e2 : (r + 1).toNat = 0 := by omega
    change T.obj.pdPow r.toNat ≤ T.obj.pdPow (r + 1).toNat
    rw [e1, e2]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have hn : n < s := by exact_mod_cast hr
    refine (h𝒮 _).1 (hSer (sq (thFil (smFun X q) n) (thFil (smFun X q) ((n : ℤ) + 1))) (TF l s) U.U 𝒮 j ?_)
    intro a b hab
    by_cases hbn : b = n
    · subst hbn
      exact (h𝒮 _).2 (hCech l s hb q U b hn a)
    · refine 𝒮.zero _ (sub_H _ a ⟨fun x y => funext fun i => ?_⟩)
      have e := (GlobalTheory.T.stable_family_properties).2.2.2 (TF l s : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)))) U.U i
      obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c (i 0)) (capO_le U.U i 0) (capO_affine U i)
      have hv := van_coord hLoc hPoly l s hb q c' n hn b hbn
      rw [← e] at hv
      exact hv.elim _ _

theorem range_fin [IsNoetherianRing O] (hLoc : KH.LocGr) (hPoly : KH.PolyTf) (hSer : KH.GlobSerreSt) (hCech : KH.GrCechFin)
    (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q]
    (U : Cov q) (n : ℕ) (r r' : ℤ) (hn : r' = r + n) (hs : r' ≤ s) (j : ℕ) :
    Module.Finite O (HQ (TO q l s (Set.range U.U)) r r' j) := by
  obtain ⟨𝒮, h𝒮⟩ := GlobalTheory.T.finite_modules_serre_class O
  have hF := GlobalTheory.T.sheaf_filtration_property (TO q l s (Set.range U.U))
  induction n generalizing r with
  | zero =>
    have e : r' = r := by simpa using hn
    subst e
    exact (h𝒮 _).1 (𝒮.zero _ (sub_CH _ (sq_sub _ _ fun T => le_rfl) j))
  | succ n ih =>
    have h1 := ih (r + 1) (by rw [hn]; push_cast; ring)
    have h3 := gr_range hLoc hPoly hSer hCech l s hb q U r (by push_cast at hn; omega) j
    exact (h𝒮 _).1 (𝒮.mid _ _ _ _ _ (sq_exact (sFil _ r) (sFil _ (r + 1)) (sFil _ r')
      (fun T => hF.anti (by push_cast at hn; omega) T) (fun T => hF.anti (by omega) T) j) ((h𝒮 _).2 h1) ((h𝒮 _).2 h3))

theorem fin_surj {M N : Type 1} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] (f : M →ₗ[O] N)
    (hf : Function.Surjective f) (h : Module.Finite O M) : Module.Finite O N :=
  Module.Finite.of_surjective f hf

theorem fin_bij {M N : Type 1} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] (f : M →ₗ[O] N)
    (hf : Function.Bijective f) (h : Module.Finite O N) : Module.Finite O M :=
  Module.Finite.of_surjective (LinearEquiv.ofBijective f hf).symm.toLinearMap (LinearEquiv.surjective _)

theorem inU_top {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (T : Thick (nlFun γ p X q κ)) : InU ⊤ T :=
  fun _ _ => trivial

end Glob

theorem finO : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GrCechFin → FinO := by
  intro hLoc hPoly hSer hCech O _ _ l s hb X q _ U 𝒱 h𝒱 r r' hr hr' j
  have hU : Used (TF l s : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)))) :=
    Or.inl ⟨rfl, l, s, rfl⟩
  have h1 : TO q l s (Set.range U.U) ≤ TO q l s {⊤} :=
    fun T hT => ⟨hT.1, ⊤, rfl, inU_top T⟩
  have h2 : TO q l s 𝒱 ≤ TO q l s {⊤} :=
    fun T hT => ⟨hT.1, ⊤, rfl, inU_top T⟩
  have c1 : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup (Set.range U.U) := by
    rintro W rfl
    rw [sSup_range, U.cover]
  have c2 : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup 𝒱 := by
    rintro W rfl
    rw [h𝒱]
  have B1 := (GlobalTheory.T.cech_refinement_cohomology_bijective _ hU _ _ h1 c1 j).1 r r'
  have B2 := (GlobalTheory.T.cech_refinement_cohomology_bijective _ hU _ _ h2 c2 j).1 r r'
  obtain ⟨n, hn⟩ : ∃ n : ℕ, r' = r + n := ⟨(r' - r).toNat, by omega⟩
  have hR := range_fin hLoc hPoly hSer hCech l s hb q U n r r' hn hr' j
  exact fin_surj _ B2.2 (fin_bij _ B1 hR)

end GlobalTheory.CompanionTheory.FinOverO
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PdPBotPos
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartTensorBaseCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartTensorBaseCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BcMor

theorem chart_mor : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} {d : ℕ} (cV : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) V d) (cA : Chart γ 0 q (κA O I) V d)
      (eO : O ⊗[O] Γ(X, V) ≃+* cO.D.B) (eA : A ⊗[O] Γ(X, V) ≃+* cA.D.B),
      (∀ r, eO (r ⊗ₜ 1) = cO.D.i r) → (∀ r, eA (r ⊗ₜ 1) = cA.D.i r) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (eO (1 ⊗ₜ f))) →
      (∀ f, ev cA.D cA.inV f = Ideal.Quotient.mk _ (eA (1 ⊗ₜ f))) →
      ∃ e₀ : cO.D ⟶ ((nmO γ q).mor 0).obj cA.D, ∀ f, e₀.φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f) := by
  intro O A _ _ _ I γ X q V d cV
  letI a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  intro cO cA eO eA hO hA hvO hvA
  have hptT : pt (((nmO γ q).mor 0).obj cA.D) = pt cA.D := Category.comp_id _
  have hT : InU V (((nmO γ q).mor 0).obj cA.D) := by
    unfold InU
    rw [hptT]
    exact cA.inV
  obtain ⟨g, hg, -⟩ := cO.rep (CommRingCat.of ((((nmO γ q).mor 0).obj cA.D).B ⧸ (((nmO γ q).mor 0).obj cA.D).J))
    (((nmO γ q).mor 0).obj cA.D).y hT
  have hg' : (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)).Pt.map (CommRingCat.ofHom g) cO.D.y =
      (((nmO γ q).mor 0).obj cA.D).y := hg
  let ι : O ⊗[O] Γ(X, V) →+* A ⊗[O] Γ(X, V) :=
    (Algebra.TensorProduct.map (Algebra.ofId O A) (AlgHom.id O Γ(X, V))).toRingHom
  let φ : cO.D.B →+* cA.D.B := (eA.toRingHom.comp ι).comp eO.symm.toRingHom
  have hφ : ∀ f, φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f) := fun f => by
    change eA (ι (eO.symm (eO (1 ⊗ₜ f)))) = _
    rw [RingEquiv.symm_apply_apply]
    change eA (Algebra.TensorProduct.map (Algebra.ofId O A) (AlgHom.id O Γ(X, V)) (1 ⊗ₜ f)) = _
    simp
  have hf : ∀ r, φ (cO.D.i r) = (((nmO γ q).mor 0).obj cA.D).i r := fun r => by
    change eA (ι (eO.symm (cO.D.i r))) = cA.D.i (algebraMap O A r)
    rw [← hO r, RingEquiv.symm_apply_apply, ← hA]
    change eA (Algebra.TensorProduct.map (Algebra.ofId O A) (AlgHom.id O Γ(X, V)) (r ⊗ₜ 1)) = _
    simp [Algebra.ofId_apply]
  have hptg : pt (((nmO γ q).mor 0).obj cA.D) = Spec.map (CommRingCat.ofHom g) ≫ pt cO.D := by
    unfold pt
    rw [← hg']
    rfl
  have hev : ∀ f, ev cA.D cA.inV f = g (ev cO.D cO.inV f) := fun f => by
    have key : ∀ (y : Spec (CommRingCat.of (cA.D.B ⧸ cA.D.J)) ⟶ X) (_ : y = Spec.map (CommRingCat.ofHom g) ≫ pt cO.D)
        (h'' : ⊤ ≤ y ⁻¹ᵁ V), GlobalTheory.Cris.evalAt y V h'' f = g (ev cO.D cO.inV f) := by
      intro y hy h''
      subst hy
      exact GlobalTheory.LogCris.evalAt_map _ (pt cO.D) cO.inV h'' f
    exact key _ (hptT.symm.trans hptg) cA.inV
  have hq : (Ideal.Quotient.mk (((nmO γ q).mor 0).obj cA.D).J).comp φ = g.comp (Ideal.Quotient.mk cO.D.J) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨f, rfl⟩ : ∃ f, x = eO (1 ⊗ₜ f) := by
      refine ⟨TensorProduct.lid O Γ(X, V) (eO.symm x), ?_⟩
      have e : (1 : O) ⊗ₜ[O] (TensorProduct.lid O Γ(X, V) (eO.symm x)) = eO.symm x :=
        (TensorProduct.lid O Γ(X, V)).symm_apply_apply (eO.symm x)
      rw [e, RingEquiv.apply_symm_apply]
    change Ideal.Quotient.mk cA.D.J (φ (eO (1 ⊗ₜ f))) = g (Ideal.Quotient.mk cO.D.J (eO (1 ⊗ₜ f)))
    rw [hφ, ← hvA, ← hvO, hev]
  exact ⟨GlobalTheory.CompanionTheory.ChartMaps.homOf cO (((nmO γ q).mor 0).obj cA.D) φ hf g hq hg', hφ⟩

end GlobalTheory.CompanionTheory.BcMor
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartTensorBaseCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_tensor_base_compat : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
    {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} {d : ℕ} (cV : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) V d) (cA : Chart γ 0 q (κA O I) V d)
      (eO : O ⊗[O] Γ(X, V) ≃+* cO.D.B) (eA : A ⊗[O] Γ(X, V) ≃+* cA.D.B),
      (∀ r, eO (r ⊗ₜ 1) = cO.D.i r) → (∀ r, eA (r ⊗ₜ 1) = cA.D.i r) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (eO (1 ⊗ₜ f))) →
      (∀ f, ev cA.D cA.inV f = Ideal.Quotient.mk _ (eA (1 ⊗ₜ f))) →
      ∃ e₀ : cO.D ⟶ ((nmO γ q).mor 0).obj cA.D, ∀ f, e₀.φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f) := by
  first | exact @GlobalTheory.CompanionTheory.BcMor.chart_mor | exact GlobalTheory.CompanionTheory.BcMor.chart_mor | (intros; apply GlobalTheory.CompanionTheory.BcMor.chart_mor <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplitRangeIsoOfInterval
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplitRangeIsoOfInterval
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrPiece

theorem subsingleton_tmul {O N M : Type} [CommRing O] [AddCommGroup N] [Module O N] [AddCommGroup M] [Module O M]
    [Subsingleton M] (y : N ⊗[O] M) : y = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rfl
  | tmul n x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

set_option maxHeartbeats 1000000 in
theorem main : ∀ {O A G : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing G] [Algebra O G] [Module.Flat O G]
    {I : Ideal A} (γ : DividedPowers I) (m : ℕ) (S : GrSplit O γ m) (u v : ℕ)
    {M : Fin m → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module O (M i)] {M' : Type} [AddCommGroup M']
    (θ : ∀ i : Fin m, u ≤ (i : ℕ) → (i : ℕ) < v → (G ≃ₗ[O] M i))
    (h0 : ∀ i : Fin m, ¬ (u ≤ (i : ℕ) ∧ (i : ℕ) < v) → Subsingleton (M i))
    (π : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G)) →+ M'),
    Function.Surjective π →
    (∀ x, π x = 0 ↔ x.1 ∈ (pdP γ v).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G))) →
    ∀ f : ∀ i, S.N i → M i → M', (∀ i n, f i n 0 = 0) →
    (∀ (i : Fin m) n x (hu : u ≤ (i : ℕ)) (hv : (i : ℕ) < v) hx, f i n (θ i hu hv x) = π ⟨S.ν i n ⊗ₜ x, hx⟩) →
    Tens O f := by
  intro O A G _ _ _ _ _ _ I γ m S u v M _ _ M' _ θ h0 π hπ hker f hf0 hf
  classical
  obtain ⟨g₀, hs, hm⟩ := GlobalTheory.T.graded_splitting_tensor_filtration (Γ := G) γ m S
  let t : ∀ i : Fin m, S.N i ⊗[O] M i →+ S.N i ⊗[O] G := fun i =>
    if h : u ≤ (i : ℕ) ∧ (i : ℕ) < v then
      ((LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).symm : S.N i ⊗[O] M i ≃ₗ[O] S.N i ⊗[O] G).toLinearMap.toAddMonoidHom
    else 0
  have t_act : ∀ (i : Fin m) (h : u ≤ (i : ℕ) ∧ (i : ℕ) < v) (a : S.N i ⊗[O] G),
      t i (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2) a) = a := by
    intro i h a
    simp only [t, dif_pos h]
    exact (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).symm_apply_apply a
  have t_inact : ∀ (i : Fin m), ¬ (u ≤ (i : ℕ) ∧ (i : ℕ) < v) → t i = 0 := by
    intro i h
    simp only [t, dif_neg h]
  let T : (∀ i, S.N i ⊗[O] M i) →+ (∀ i, S.N i ⊗[O] G) :=
    { toFun := fun w i => t i (w i)
      map_zero' := by funext i; simp
      map_add' := fun a b => by funext i; simp }
  have T_apply : ∀ w i, T w i = t i (w i) := fun _ _ => rfl
  have hT : ∀ w, g₀ (T w) ∈ (pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) := by
    intro w
    refine (hm u _).2 fun i hi => ?_
    rw [T_apply, t_inact i (by omega)]
    rfl
  let φ : (∀ i, S.N i ⊗[O] M i) →+ M' :=
    { toFun := fun w => π ⟨g₀ (T w), hT w⟩
      map_zero' := by
        have : (⟨g₀ (T 0), hT 0⟩ : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G))) = 0 :=
          Subtype.ext (by simp)
        rw [this, map_zero]
      map_add' := fun a b => by
        rw [← map_add (f := _)]
        exact congrArg π (Subtype.ext (by simp)) }
  have φ_apply : ∀ w, φ w = π ⟨g₀ (T w), hT w⟩ := fun _ => rfl
  have inj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun w hw => ?_
    rw [φ_apply] at hw
    have h1 := (hm v _).1 ((hker _).1 hw)
    funext i
    by_cases h : u ≤ (i : ℕ) ∧ (i : ℕ) < v
    · have h2 := h1 i h.2
      rw [T_apply] at h2
      obtain ⟨a, ha⟩ := (LinearEquiv.lTensor (S.N i) (θ i h.1 h.2)).surjective (w i)
      rw [← ha, t_act i h] at h2
      rw [← ha, h2, map_zero]
      rfl
    · haveI := h0 i h
      exact subsingleton_tmul _
  have surj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    obtain ⟨z, hz⟩ := g₀.surjective x.1
    have hzu := (hm u z).1 (by rw [hz]; exact x.2)
    let w : ∀ i, S.N i ⊗[O] M i := fun i =>
      if h : u ≤ (i : ℕ) ∧ (i : ℕ) < v then LinearEquiv.lTensor (S.N i) (θ i h.1 h.2) (z i) else 0
    refine ⟨w, ?_⟩
    rw [φ_apply, ← sub_eq_zero, ← map_sub, hker]
    have : ((⟨g₀ (T w), hT w⟩ - x : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G))) : A ⊗[O] G)
        = g₀ (T w - z) := by
      rw [map_sub, hz]
      rfl
    rw [this, hm]
    intro i hi
    rw [Pi.sub_apply, T_apply, sub_eq_zero]
    by_cases h : u ≤ (i : ℕ)
    · have h' : u ≤ (i : ℕ) ∧ (i : ℕ) < v := ⟨h, hi⟩
      simp only [w, dif_pos h']
      exact t_act i h' _
    · rw [t_inact i (by omega), hzu i (by omega)]
      rfl
  refine ⟨AddEquiv.ofBijective φ ⟨inj, surj⟩, fun i n x => ?_⟩
  rw [AddEquiv.ofBijective_apply]
  by_cases h : u ≤ (i : ℕ) ∧ (i : ℕ) < v
  · obtain ⟨y, rfl⟩ := (θ i h.1 h.2).surjective x
    have hTs : T (Pi.single i (n ⊗ₜ[O] θ i h.1 h.2 y)) = Pi.single i (n ⊗ₜ[O] y) := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [T_apply, Pi.single_eq_same, Pi.single_eq_same]
        exact t_act j h (n ⊗ₜ[O] y)
      · rw [T_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, map_zero]
    have hx : S.ν i n ⊗ₜ[O] y ∈ (pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) := by
      rw [← hs, ← hTs]
      exact hT _
    rw [hf i n y h.1 h.2 hx, φ_apply]
    exact congrArg π (Subtype.ext (by simp only [hTs, hs]))
  · haveI := h0 i h
    rw [Subsingleton.elim x 0, TensorProduct.tmul_zero, Pi.single_zero, map_zero, hf0]

end GlobalTheory.CompanionTheory.GrPiece
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplitRangeIsoOfIntervalStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_split_range_iso_of_interval : ∀ {O A G : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing G] [Algebra O G] [Module.Flat O G]
    {I : Ideal A} (γ : DividedPowers I) (m : ℕ) (S : GrSplit O γ m) (u v : ℕ)
    {M : Fin m → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module O (M i)] {M' : Type} [AddCommGroup M']
    (θ : ∀ i : Fin m, u ≤ (i : ℕ) → (i : ℕ) < v → (G ≃ₗ[O] M i))
    (h0 : ∀ i : Fin m, ¬ (u ≤ (i : ℕ) ∧ (i : ℕ) < v) → Subsingleton (M i))
    (π : ((pdP γ u).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G)) : Ideal (A ⊗[O] G)) →+ M'),
    Function.Surjective π →
    (∀ x, π x = 0 ↔ x.1 ∈ (pdP γ v).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := G))) →
    ∀ f : ∀ i, S.N i → M i → M', (∀ i n, f i n 0 = 0) →
    (∀ (i : Fin m) n x (hu : u ≤ (i : ℕ)) (hv : (i : ℕ) < v) hx, f i n (θ i hu hv x) = π ⟨S.ν i n ⊗ₜ x, hx⟩) →
    Tens O f := by
  first | exact @GlobalTheory.CompanionTheory.GrPiece.main | exact GlobalTheory.CompanionTheory.GrPiece.main | (intros; apply GlobalTheory.CompanionTheory.GrPiece.main <;> assumption)
end
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BcLoc

theorem dividedPowerFiltration_dividedPowersBot' (O : Type) [CommRing O] {r : ℕ} (hr : r ≠ 0) : pdP (dividedPowersBot O) r = ⊥ := by
  classical
  rw [eq_bot_iff]
  refine Ideal.span_le.2 ?_
  rintro _ ⟨l, hl, hs, rfl⟩
  have hq : ∃ q ∈ l, q.1 ≠ 0 := by
    by_contra h
    push_neg at h
    have : (l.map Prod.fst).sum = 0 := List.sum_eq_zero (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact h q hq)
    omega
  obtain ⟨q, hq, h0⟩ := hq
  refine List.prod_eq_zero (List.mem_map.2 ⟨q, hq, ?_⟩)
  rw [dividedPowersBot_dpow_eq]
  simp [h0]

section Sq
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}

theorem sub_of_bot (a b : IdF F) (T : C) (h : a.S T = ⊥) : Subsingleton (sqM a b T) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx := x.2
  have hy := y.2
  simp only [sqM, h, Ideal.map_bot] at hx hy
  exact (show (x.1 : F.obj T ⧸ b.S T) = 0 from hx).trans (show (y.1 : F.obj T ⧸ b.S T) = 0 from hy).symm

theorem sub_of_top (a b : IdF F) (T : C) (h : b.S T = ⊤) : Subsingleton (sqM a b T) := by
  haveI : Subsingleton (F.obj T ⧸ b.S T) := Ideal.Quotient.subsingleton_iff.2 h
  exact ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩

theorem pi_ex (a b : IdF F) (T : C) {Y : Type} [CommRing Y] {P Q : Ideal Y} (e : Y ≃+* F.obj T)
    (hP : ∀ z, e z ∈ a.S T ↔ z ∈ P) (hQ : ∀ z, e z ∈ b.S T ↔ z ∈ Q) :
    ∃ π : P →+ sqM a b T, Function.Surjective π ∧ (∀ x, π x = 0 ↔ x.1 ∈ Q) ∧
      ∀ x, (π x).1 = Ideal.Quotient.mk _ (e x.1) := by
  refine ⟨AddMonoidHom.mk' (fun x => ⟨Ideal.Quotient.mk _ (e x.1), Ideal.mem_map_of_mem _ ((hP _).2 x.2)⟩)
    (fun x y => Subtype.ext (by simp)), ?_, fun x => ?_, fun x => rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hy
    refine ⟨⟨e.symm w, (hP _).1 (by simpa using hw)⟩, Subtype.ext ?_⟩
    simp
  · rw [← hQ, ← Ideal.Quotient.eq_zero_iff_mem]
    exact Subtype.ext_iff

theorem theta_ex {G : Type} [CommRing G] [Algebra R G] (a b : IdF F) (T : C) (ht : a.S T = ⊤) (hb : b.S T = ⊥)
    (e : R ⊗[R] G ≃+* F.obj T) (he : ∀ r, e (r ⊗ₜ 1) = algebraMap R (F.obj T) r) :
    ∃ θ : G ≃ₗ[R] sqM a b T, ∀ x, (θ x).1 = Ideal.Quotient.mk _ (e (1 ⊗ₜ x)) := by
  let f : G →ₗ[R] sqM a b T :=
    { toFun := fun x => ⟨Ideal.Quotient.mk _ (e (1 ⊗ₜ x)), Ideal.mem_map_of_mem _ (by rw [ht]; trivial)⟩
      map_add' := fun x y => Subtype.ext (by simp [TensorProduct.tmul_add])
      map_smul' := fun r x => Subtype.ext (by
        have h1 : (1 : R) ⊗ₜ[R] (r • x) = (r ⊗ₜ[R] (1 : G)) * ((1 : R) ⊗ₜ[R] x) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, TensorProduct.tmul_smul,
            TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        change Ideal.Quotient.mk _ (e ((1 : R) ⊗ₜ[R] (r • x))) = r • Ideal.Quotient.mk _ (e ((1 : R) ⊗ₜ[R] x))
        rw [h1, map_mul, he, map_mul, Algebra.smul_def]
        rfl) }
  refine ⟨LinearEquiv.ofBijective f ⟨fun x y h => ?_, ?_⟩, fun x => rfl⟩
  · have h1 := congrArg Subtype.val h
    have h2 := Ideal.Quotient.eq.1 h1
    rw [hb, Ideal.mem_bot, ← map_sub, map_eq_zero_iff _ e.injective, ← TensorProduct.tmul_sub] at h2
    have h3 := congrArg (TensorProduct.lid R G) h2
    simpa [sub_eq_zero] using h3
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨TensorProduct.lid R G (e.symm w), Subtype.ext ?_⟩
    change Ideal.Quotient.mk _ (e ((1 : R) ⊗ₜ[R] TensorProduct.lid R G (e.symm w))) = _
    have : (1 : R) ⊗ₜ[R] TensorProduct.lid R G (e.symm w) = e.symm w := by
      rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
    rw [this, e.apply_symm_apply]

end Sq

theorem crit_of {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (P : Poly Φ)
    {F a : ℤ → IdF Φ.A} {r r₀ : ℤ} (h : P.Crit F r₀) (h0 : a r = F r₀)
    (hk : ∀ k : ℕ, a (r - k) = F (r₀ - k)) : P.Crit a r := by
  intro T b
  rw [h0]
  simp only [hk]
  exact h T b

theorem chart_tens : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) (l s m : ℕ)
    (S : GrSplit O γ m) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V : X.Opens} {d : ℕ} (cV : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) V d) (cA : Chart γ 0 q (κA O I) V d)
      (eO : O ⊗[O] Γ(X, V) ≃+* cO.D.B) (eA : A ⊗[O] Γ(X, V) ≃+* cA.D.B)
      (hD : TO q l s {V} cO.D) (hD' : TS γ q l s {V} cA.D)
      (e : (⟨cO.D, hD⟩ : (TO q l s {V}).FullSubcategory) ⟶ (smO γ q l s {V}).G.obj ⟨cA.D, hD'⟩),
      (∀ r, eO (r ⊗ₜ 1) = cO.D.i r) → (∀ r, eA (r ⊗ₜ 1) = cA.D.i r) →
      (∀ f, e.hom.φ (eO (1 ⊗ₜ f)) = eA (1 ⊗ₜ f)) →
      ∀ (c t : ℤ), 0 ≤ c →
      ∀ (ha : ∀ (i : Fin m) n, (smO γ q l s {V}).LeC (S.ν i n) (sFil _ (t - c - i)) (sFil _ (t - c)))
        (hb : ∀ (i : Fin m) n, (smO γ q l s {V}).LeC (S.ν i n) (sFil _ (t - i)) (sFil _ t)),
      Tens O (N := S.N) (M := fun i => (sq (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i))).obj ⟨cO.D, hD⟩)
        (M' := (sq (sFil (TS γ q l s {V}) (t - c)) (sFil (TS γ q l s {V}) t)).obj ⟨cA.D, hD'⟩)
        fun i n x => ((smO γ q l s {V}).sqC (S.ν i n) (ha i n) (hb i n)).τ ⟨cA.D, hD'⟩
          (((sq (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i))).map e).hom x) := by
  intro O A _ _ _ I γ l s m S X q V d cV
  letI a0 : Algebra O Γ(X, V) := (strV q V).toAlgebra
  intro cO cA eO eA hD hD' e hiO hiA he c t hc ha hb
  haveI hF : Module.Flat O Γ(X, V) := GlobalTheory.CompanionTheory.ChartAlg.flat_of_etale cV.t cV.etale
  have hQ : ∀ T, TO q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have hQ' : ∀ T, TS γ q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have pO := (GlobalTheory.T.chart_divided_powers_graded_constant cO (GlobalTheory.T.chart_is_good cO) (TO q l s {V}) hQ hD).1
  have pA := (GlobalTheory.T.chart_divided_powers_graded_constant cA (GlobalTheory.T.chart_is_good cA) (TS γ q l s {V}) hQ' hD').1
  have bot1 : ∀ r : ℕ, r ≠ 0 → cO.D.pdPow r = ⊥ := fun r hr => by
    rw [pO, dividedPowerFiltration_dividedPowersBot' O hr, Ideal.map_bot]
  have mA : ∀ (r : ℕ) (z : A ⊗[O] Γ(X, V)), eA z ∈ cA.D.pdPow r ↔
      z ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ(X, V))) := fun r z => by
    have h1 : cA.D.i = (eA : A ⊗[O] Γ(X, V) →+* cA.D.B).comp
        (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ(X, V))) :=
      RingHom.ext fun a => (hiA a).symm
    rw [pA, h1, ← Ideal.map_map]
    constructor
    · intro h
      obtain ⟨w, hw, h2⟩ := (Ideal.mem_map_iff_of_surjective _ eA.surjective).1 h
      have h3 := eA.injective h2
      rwa [← h3]
    · exact fun h => Ideal.mem_map_of_mem _ h
  have fa : ∀ (i : Fin m) (hu : (t - c).toNat ≤ (i : ℕ)) (hv : (i : ℕ) < t.toNat),
      ∃ θ : Γ(X, V) ≃ₗ[O] sqM (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i)) ⟨cO.D, hD⟩,
        ∀ x, (θ x).1 = Ideal.Quotient.mk _ (eO (1 ⊗ₜ x)) := fun i hu hv =>
    theta_ex (sFil (TO q l s {V}) (t - c - i)) (sFil (TO q l s {V}) (t - i)) ⟨cO.D, hD⟩
      (by
        change cO.D.pdPow _ = ⊤
        rw [show (t - c - i).toNat = 0 by omega]
        exact cO.D.pdPow_zero)
      (by
        change cO.D.pdPow _ = ⊥
        exact bot1 _ (by omega)) eO hiO
  choose θ hθ using fa
  obtain ⟨π, hs, hk, hπ⟩ := pi_ex (sFil (TS γ q l s {V}) (t - c)) (sFil (TS γ q l s {V}) t) ⟨cA.D, hD'⟩ eA (mA _) (mA _)
  refine GlobalTheory.T.graded_split_range_iso_of_interval (O := O) (A := A) (G := Γ(X, V)) γ m S (t - c).toNat t.toNat θ ?_ π hs hk _ ?_ ?_
  · intro i hi
    by_cases hu : (t - c).toNat ≤ (i : ℕ)
    · refine sub_of_top _ _ _ ?_
      change cO.D.pdPow _ = ⊤
      rw [show (t - i).toNat = 0 by
        have : ¬ (i : ℕ) < t.toNat := fun h => hi ⟨hu, h⟩
        omega]
      exact cO.D.pdPow_zero
    · refine sub_of_bot _ _ _ ?_
      change cO.D.pdPow _ = ⊥
      exact bot1 _ (by omega)
  · intro i n
    simp only [map_zero]
  · intro i n x hu hv hx
    refine Subtype.ext ?_
    rw [hπ]
    have hz := hθ i hu hv x
    generalize θ i hu hv x = z at hz ⊢
    obtain ⟨z, hz'⟩ := z
    change z = _ at hz
    subst hz
    have key : ∀ w : cA.D.B, w = eA (1 ⊗ₜ x) → cA.D.i (S.ν i n) * w = eA (S.ν i n ⊗ₜ x) := by
      rintro _ rfl
      rw [← hiA, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact congrArg (Ideal.Quotient.mk _) (key _ (he x))

theorem bc_single : KH.LocBc → KH.PolyTf → BcOn True := by
  intro hLoc hPoly O A _ _ _ I γ l s m hO hA S X q 𝒱 h r r' hrr hrs ha hb j
  obtain ⟨-, V, d, rfl, ⟨cV⟩⟩ | ⟨hF, -⟩ := h
  swap
  · exact absurd trivial hF
  obtain ⟨c, hc, rfl⟩ : ∃ c : ℤ, 0 ≤ c ∧ r = r' - c := ⟨r' - r, by omega, by ring⟩
  obtain ⟨cO, eO, tfO, hiO, htO, hevO⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := O) (R := O) (dividedPowersBot O) l s hO q
    (Ideal.Quotient.mk ⊥) (fun _ => rfl) cV
  obtain ⟨cA, eA, tfA, hiA, htA, hevA⟩ := GlobalTheory.T.exists_chart_from_coordinates (O := O) (R := A) γ l s hA q (κA O I) (fun _ => rfl) cV
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.chart_tensor_base_compat γ q cV cO cA eO eA hiO hiA hevO hevA
  have hQ : ∀ T, TO q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have hQ' : ∀ T, TS γ q l s {V} T → InU V T := by
    rintro T ⟨-, V', rfl, h⟩
    exact h
  have hD : TO q l s {V} cO.D := ⟨tfO, V, rfl, cO.inV⟩
  have hD' : TS γ q l s {V} cA.D := ⟨tfA, V, rfl, cA.inV⟩
  have gO := GlobalTheory.T.chart_is_good cO
  have gA := GlobalTheory.T.chart_is_good cA
  let E := cO.frame gO (TO q l s {V}) hQ hD
  let E' := cA.frame gA (TS γ q l s {V}) hQ' hD'
  let e : E.D ⟶ (smO γ q l s {V}).G.obj E'.D := ObjectProperty.homMk e₀
  have he : (smO γ q l s {V}).Fr E E' e := by
    intro i T σ σ'
    have h1 : e₀.φ (cO.t i) = cA.t i := by
      rw [← htO, ← htA]; exact he₀ _
    change (σ'.hom.φ (e₀.φ (cO.t i)) - σ.hom.φ (e₀.φ (cO.t i)) : T.obj.B) = σ'.hom.φ (cA.t i) - σ.hom.φ (cA.t i)
    rw [h1]
  have fil := GlobalTheory.T.sheaf_filtration_property (TO q l s {V})
  have fil' := GlobalTheory.T.sheaf_filtration_property (TS γ q l s {V})
  obtain ⟨PO, hPO⟩ := hPoly (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {V}
  obtain ⟨PA, hPA⟩ := hPoly γ q (κA O I) l s {V}
  have lem : ∀ (i : ℕ) (a : A), a ∈ pdP γ i → ∀ t : ℤ, (smO γ q l s {V}).LeC a (sFil _ (t - i)) (sFil _ t) :=
    fun i a h t => GlobalTheory.T.scalar_multiplication_shifts_filtration γ q l s {V} i a h t
  refine hLoc (smO γ q l s {V}) PO PA E E' e he (fun _ => Function.injective_id) S.N S.ν
    (fun i t => sFil _ (t - c - i)) (fun i t => sFil _ (t - i)) (fun t => sFil _ (t - c)) (fun t => sFil _ t) r'
    (fun i => ⟨fun t T => fil.anti (by omega) T, fun t ht => crit_of PO (hPO (t - c - i) (by omega)).1 rfl
        (fun k => by congr 1; ring),
      fun t ht => crit_of PO (hPO (t - i) (by omega)).1 rfl (fun k => by congr 1; ring)⟩)
    ⟨fun t T => fil'.anti (by omega) T, fun t ht => crit_of PA (hPA (t - c) (by omega)).1 rfl (fun k => by congr 1; ring),
      fun t ht => (hPA t (by omega)).1⟩
    (fun i n t => lem i _ (S.mem i n) _) (fun i n t => lem i _ (S.mem i n) _) ?_ j
  intro t _ _
  exact chart_tens γ l s m S q cV cO cA eO eA hD hD' e hiO hiA he₀ c t hc _ _

end GlobalTheory.CompanionTheory.BcLoc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFgPullSqC
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatticeFinite

universe u v u' v'

section General

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {R' : Type} [CommRing R'] {C' : Type u'} [Category.{v'} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'}

theorem pull_sqC_comb (m : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} {c c₁ c₂ e e' : R'}
    (hc : c = e * c₁ + e' * c₂) (ha : m.LeC c a a') (hb : m.LeC c b b') (ha₁ : m.LeC c₁ a a') (hb₁ : m.LeC c₁ b b')
    (ha₂ : m.LeC c₂ a a') (hb₂ : m.LeC c₂ b b') (j : ℕ) (x : CH.H (sq a b) j) :
    (m.sqC c ha hb).pull j x =
      e • (m.sqC c₁ ha₁ hb₁).pull j x + e' • (m.sqC c₂ ha₂ hb₂).pull j x := by
  obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk _ = e • Submodule.Quotient.mk _ + e' • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  refine congrArg _ (Subtype.ext (funext fun s => ?_))
  change (m.sqC c ha hb).τ _ (f (s ⋙ m.G)) =
    e • (m.sqC c₁ ha₁ hb₁).τ _ (f (s ⋙ m.G)) + e' • (m.sqC c₂ ha₂ hb₂).τ _ (f (s ⋙ m.G))
  generalize f (s ⋙ m.G) = w
  obtain ⟨z, hz⟩ := w
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine Subtype.ext ?_
  have key : algebraMap R' (Φ'.A.obj (s.obj (Fin.last j))) c * m.ρ (s.obj (Fin.last j)) y =
      e • (algebraMap R' (Φ'.A.obj (s.obj (Fin.last j))) c₁ * m.ρ (s.obj (Fin.last j)) y) +
      e' • (algebraMap R' (Φ'.A.obj (s.obj (Fin.last j))) c₂ * m.ρ (s.obj (Fin.last j)) y) := by
    rw [hc, map_add (f := _), map_mul, map_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  exact congrArg (Ideal.Quotient.mk (b'.S (s.obj (Fin.last j)))) key

theorem exists_fg_pull_sqC (m : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (P : Ideal R') (hP : P.FG)
    (h₁ : ∀ c ∈ P, m.LeC c a a') (h₂ : ∀ c ∈ P, m.LeC c b b') (j : ℕ) (hfin : Module.Finite R (CH.H (sq a b) j)) :
    ∃ N : Submodule R' (CH.H (sq a' b') j), N.FG ∧ ∀ (c : R') (ha : m.LeC c a a') (hb : m.LeC c b b'), c ∈ P →
      ∀ x, (m.sqC c ha hb).pull j x ∈ N := by
  classical
  obtain ⟨G, rfl⟩ := hP
  obtain ⟨X, hX⟩ := (Module.Finite.fg_top : (⊤ : Submodule R (CH.H (sq a b) j)).FG)
  let φ : G × X → CH.H (sq a' b') j := fun p =>
    (m.sqC p.1.1 (h₁ _ (Ideal.subset_span p.1.2)) (h₂ _ (Ideal.subset_span p.1.2))).pull j p.2.1
  refine ⟨Submodule.span R' (Set.range φ), Submodule.fg_span (Set.finite_range φ), ?_⟩
  have hgen : ∀ (g : R') (hg : g ∈ G) (ha : m.LeC g a a') (hb : m.LeC g b b') (x : CH.H (sq a b) j),
      (m.sqC g ha hb).pull j x ∈ Submodule.span R' (Set.range φ) := by
    intro g hg ha hb x
    have hx : x ∈ Submodule.span R (X : Set (CH.H (sq a b) j)) := hX ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨(⟨g, hg⟩, ⟨x, hx⟩), rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  intro c ha hb hc x
  refine Submodule.span_induction
    (p := fun c _ => ∀ (ha : m.LeC c a a') (hb : m.LeC c b b'), (m.sqC c ha hb).pull j x ∈ Submodule.span R' (Set.range φ))
    ?_ ?_ ?_ ?_ hc ha hb
  · intro g hg ha hb
    exact hgen g hg ha hb x
  · intro ha hb
    rw [pull_sqC_comb m (c₁ := 0) (c₂ := 0) (e := 0) (e' := 0) (by simp) ha hb ha hb ha hb j x]
    simp
  · intro c₁ c₂ m₁ m₂ i₁ i₂ ha hb
    rw [pull_sqC_comb m (c₁ := c₁) (c₂ := c₂) (e := 1) (e' := 1) (by simp) ha hb (h₁ _ m₁) (h₂ _ m₁) (h₁ _ m₂) (h₂ _ m₂) j x]
    simpa using add_mem (i₁ (h₁ _ m₁) (h₂ _ m₁)) (i₂ (h₁ _ m₂) (h₂ _ m₂))
  · intro e c₁ m₁ i₁ ha hb
    rw [pull_sqC_comb m (c₁ := c₁) (c₂ := c₁) (e := e) (e' := 0) (by simp) ha hb (h₁ _ m₁) (h₂ _ m₁) (h₁ _ m₁) (h₂ _ m₁) j x]
    simpa using Submodule.smul_mem _ e (i₁ (h₁ _ m₁) (h₂ _ m₁))

end General

theorem dividedPowerFiltration_anti {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {r r' : ℕ} (h : r ≤ r') :
    pdP δ r' ≤ pdP δ r :=
  Ideal.span_mono fun _ ⟨l, h₁, h₂, h₃⟩ => ⟨l, h₁, h.trans h₂, h₃⟩

theorem tfBase_mono {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J} {l m s : ℕ} (h : TFBase δ l m)
    (hms : m ≤ s) : TFBase δ l s :=
  ⟨le_bot_iff.1 (h.nil ▸ dividedPowerFiltration_anti δ hms), h.tf, h.dv⟩

theorem afgA_of_bcOn_finO : BcOn False → FinO → AfgA := by
  intro hB hF O A _ _ _ _ _ I γ l s m hl hO hL hms X q _ U 𝒱 h𝒱 r r' hr hr' j
  obtain ⟨S⟩ := GlobalTheory.T.graded_splitting_over_lattice_base γ l m hl hL
  have hA : TFBase γ l s := tfBase_mono hL.tf hms
  have hC : ∀ (i : Fin m) (t : ℤ) (c : A), c ∈ pdP γ i →
      (smO γ q l s 𝒱).LeC c (sFil _ (t - i)) (sFil _ t) :=
    fun i t c hc => GlobalTheory.T.scalar_multiplication_shifts_filtration γ q l s 𝒱 i c hc t
  have ha : ∀ (i : Fin m) n, (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r - i)) (sFil _ r) :=
    fun i n => hC i r _ (S.mem i n)
  have hb : ∀ (i : Fin m) n, (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r' - i)) (sFil _ r') :=
    fun i n => hC i r' _ (S.mem i n)
  obtain ⟨g, hg⟩ := hB γ l s m hO hA S q 𝒱 (Or.inr ⟨not_false, ⟨U⟩, h𝒱⟩) r r' hr hr' ha hb j
  have hN : ∀ i : Fin m, ∃ N : Submodule A (HQ (TS γ q l s 𝒱) r r' j), N.FG ∧
      ∀ n x, ((smO γ q l s 𝒱).sqC (S.ν i n) (ha i n) (hb i n)).pull j x ∈ N := by
    intro i
    have hi : (0 : ℤ) ≤ (i : ℕ) := Int.natCast_nonneg _
    obtain ⟨N, h₁, h₂⟩ := exists_fg_pull_sqC (smO γ q l s 𝒱) (pdP γ i) (hL.fg i) (fun c hc => hC i r c hc)
      (fun c hc => hC i r' c hc) j (hF l s hO q U 𝒱 h𝒱 (r - i) (r' - i) (by omega) (by omega) j)
    exact ⟨N, h₁, fun n x => h₂ _ _ _ (S.mem i n) x⟩
  choose N hNfg hNmem using hN
  refine ⟨0, ⨆ i, N i, Submodule.fg_iSup _ hNfg, fun y => ?_⟩
  rw [pow_zero, one_smul]
  have hsingle : ∀ (i : Fin m) (t : S.N i ⊗[O] HQ (TO q l s 𝒱) (r - i) (r' - i) j),
      g (Pi.single i t) ∈ ⨆ i, N i := by
    intro i t
    induction t using TensorProduct.inductionOn with
    | tmul n x => rw [hg]; exact Submodule.mem_iSup_of_mem i (hNmem i n x)
    | add t t' ht ht' => rw [Pi.single_add, map_add (f := _)]; exact add_mem ht ht'
  have hy : y = ∑ i, g (Pi.single i (g.symm y i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, Finset.univ_sum_single, g.apply_symm_apply]
  rw [hy]
  exact sum_mem fun i _ => hsingle i _

end GlobalTheory.CompanionTheory.LatticeFinite
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem split_field : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := @GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit

theorem leC_shift : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (i : ℕ) (a : A), a ∈ pdP γ i → ∀ r : ℤ,
    (smO γ q l s 𝒱).LeC a (sFil _ (r - i)) (sFil _ r) := @GlobalTheory.CompanionTheory.LecShift.leC_shift

theorem bc_loc : KH.LocBc → KH.PolyTf → BcOn True := @GlobalTheory.CompanionTheory.BcLoc.bc_single

theorem bc_glob : KH.GlobBcSt → BcOn True → BcOn False := @GlobalTheory.CompanionTheory.GlobBc.main

theorem fin_o : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GrCechFin → FinO := @GlobalTheory.CompanionTheory.FinOverO.finO

theorem afg_a : BcOn False → FinO → AfgA := @GlobalTheory.CompanionTheory.LatticeFinite.afgA_of_bcOn_finO

theorem lift_a : AfgA → LiftA := @GlobalTheory.CompanionTheory.LiftLat.liftA_of_afgA

theorem basis_b : BcOn False → KH.KIso → BasisB := @GlobalTheory.CompanionTheory.BasisBase.basisB_of_bcOn

end CrystallineSemistableComparison.Pb
