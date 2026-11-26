module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivHopf
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GaGram

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsDenOfOpen
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Mh

theorem emb : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)), Γ.IsEmb (Γ.btOrder ⊤) j := by
  intro R _ _ T _ _ Γ
  let A := Γ.btOrder ⊤
  have htop (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤) (s : Γ(Γ.G.left, ⊤)) :
      valAt (Γ.pt t).left ⊤ h s = val (Γ.pt t).left s := by
    simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hsec (a : A) : ∃ s : Γ(Γ.G.left, ⊤), ∀ t,
      val (Γ.pt t).left s = algebraMap R (FractionRing R) (a.1 t) := by
    have ha := (Twhopf.mem_order R T Γ ⊤ a.1).1 a.2
    obtain ⟨s, hs⟩ := (Twhopf.reg_iff R T Γ ⊤ _).1 (ha 1)
    refine ⟨s, fun t => (htop t le_top s).symm.trans ?_⟩
    simpa only [_root_.one_mul] using hs t le_top
  have hsec_ext {s s' : Γ(Γ.G.left, ⊤)}
      (h : ∀ t, val (Γ.pt t).left s = val (Γ.pt t).left s') : s = s' := by
    rw [← sub_eq_zero]
    refine Twhopf.sec_inj R T Γ ⊤ _ fun t ht => ?_
    rw [htop, map_sub, h, sub_self]
  have hhom_ext {B : Type} [CommRing B] {j j' : Γ.G.left ⟶ Spec (CommRingCat.of B)}
      (h : ∀ t, (Γ.pt t).left ≫ j = (Γ.pt t).left ≫ j') : j = j' :=
    pb_ext fun a => hsec_ext fun t => by rw [val_pb_comp, h, ← val_pb_comp]
  choose s hs using hsec
  let φ : A →+* Γ(Γ.G.left, ⊤) :=
    { toFun := s
      map_one' := hsec_ext fun t => by rw [hs, map_one]; simp
      map_mul' := fun a b => hsec_ext fun t => by rw [hs, map_mul, hs, hs]; simp
      map_zero' := hsec_ext fun t => by rw [hs, map_zero]; simp
      map_add' := fun a b => hsec_ext fun t => by rw [hs, map_add (f := _), hs, hs]; simp }
  obtain ⟨j, hj⟩ := exists_pb φ
  have hpt : ∀ t, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom
      ((algebraMap R (FractionRing R)).comp
        ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    intro t
    apply comp_eq_spec
    intro a
    rw [hj]
    exact hs a t
  refine ⟨j, ⟨?_, hpt⟩, fun j' hj' => hhom_ext fun t => by rw [hj'.pt, hpt]⟩
  apply hhom_ext
  intro t
  rw [← Category.assoc, hpt, spec_comp, Over.w (Γ.pt t)]
  show _ = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  congr 2

theorem emb_square : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ (A : Subalgebra R (T → R)) (A' : Subalgebra R' (T → R')) (ψ : A →+* A'), (∀ (a : A) t, (ψ a).1 t = algebraMap R R' (a.1 t)) → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)) (j' : Γ'.G.left ⟶ Spec (CommRingCat.of A')), Γ.IsEmb A j → Γ'.IsEmb A' j' → F ≫ j = j' ≫ Spec.map (CommRingCat.ofHom ψ) := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF A A' ψ hψ j j' hj hj'
  obtain ⟨B, _, i, k, k', σ, hk, hki, hki', -, hσ, hσ'⟩ := hF.pts
  have hhom_ext {f g : Γ'.G.left ⟶ Spec (CommRingCat.of A)}
      (h : ∀ t, (Γ'.pt t).left ≫ f = (Γ'.pt t).left ≫ g) : f = g := by
    apply pb_ext
    intro a
    rw [← sub_eq_zero]
    refine Twhopf.sec_inj R' T Γ' ⊤ _ fun t ht => ?_
    unfold valAt
    change val (Γ'.pt t).left (pb f a - pb g a) = 0
    rw [map_sub, val_pb_comp, h, ← val_pb_comp, sub_self]
  refine hhom_ext fun t => ?_
  have h1 : σ t ≫ j = Spec.map (CommRingCat.ofHom
      (i.comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    obtain ⟨c, hc⟩ := Spec.map_surjective (σ t ≫ j)
    have h2 := hj.pt t
    rw [← hσ t, Category.assoc, ← hc, ← CommRingCat.ofHom_hom c, spec_comp, ← hki] at h2
    rw [← hc, ← CommRingCat.ofHom_hom c]
    congr 2
    exact RingHom.ext fun a => hk (RingHom.congr_fun (spec_inj h2) a)
  rw [← Category.assoc, ← hσ', Category.assoc, h1, spec_comp, ← Category.assoc, hj'.pt t, spec_comp,
    ← RingHom.comp_assoc, hki']
  congr 2
  exact RingHom.ext fun a => congrArg (algebraMap R' (FractionRing R')) (hψ a t).symm

theorem valAt_comp {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Y) (F : Y ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ (x ≫ F) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (x ≫ F) U h s = valAt x (F ⁻¹ᵁ U) h ((F.app U).hom s) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

theorem exists_den_of_open {A : Type} [CommRing A] {X : Scheme.{0}} (j : X ⟶ Spec (CommRingCat.of A))
    [IsOpenImmersion j] (g : X) (s : Γ(X, ⊤)) :
    ∃ u a : A, u ∉ (j g).asIdeal ∧ ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ X),
      val x (pb j u) * val x s = val x (pb j a) := by
  have htop {K : Type} [CommRing K] {Y : Scheme.{0}} (x : Spec (CommRingCat.of K) ⟶ Y)
      (h : ⊤ ≤ x ⁻¹ᵁ ⊤) (b : Γ(Y, ⊤)) : valAt x ⊤ h b = val x b := by
    simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hY := isAffineOpen_top (Spec (CommRingCat.of A))
  obtain ⟨r, hr, hg⟩ := hY.exists_basicOpen_le (V := j.opensRange) ⟨j g, g, rfl⟩ trivial
  let D := (Spec (CommRingCat.of A)).basicOpen r
  have := j.isIso_app D hr
  obtain ⟨s', hs'⟩ := (ConcreteCategory.bijective_of_isIso (j.app D)).2
    ((X.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ D ≤ ⊤)).op).hom s)
  have hl := hY.isLocalization_basicOpen r
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers r) s'
  let c := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
  have hc : ∀ b, pb j (c b) = j.appTop b := fun b => by simp [pb, c]
  refine ⟨c (r ^ (n + 1)), c (r * a), ?_, fun K _ x => ?_⟩
  · rw [map_pow]
    intro h
    have h1 := (j g).isPrime.mem_of_pow_mem _ h
    have h2 : j g ∈ (Spec (CommRingCat.of A)).basicOpen r := hg
    rw [basicOpen_eq_of_affine'] at h2
    exact h2 h1
  · rw [hc, hc, ← val_comp, ← val_comp, map_pow, map_mul, pow_succ']
    by_cases h0 : val (x ≫ j) r = 0
    · simp [h0]
    have hx : ⊤ ≤ (x ≫ j) ⁻¹ᵁ D := by
      rw [Scheme.preimage_basicOpen_top, top_le_iff]
      apply Scheme.basicOpen_of_isUnit
      have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((x ≫ j).appTop r)) := Ne.isUnit h0
      simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    have e := congrArg (SubOrder.valHom (x ≫ j) D hx) ha
    have hres : ∀ b, SubOrder.valHom (x ≫ j) D hx (algebraMap Γ(Spec (CommRingCat.of A), ⊤) _ b) = val (x ≫ j) b :=
      fun b => (Twhopf.valAt_restrict (x ≫ j) (homOfLE (le_top : D ≤ ⊤)) hx le_top b).trans (htop _ _ _)
    rw [map_mul, hres, hres, SubOrder.valHom_apply, valAt_comp] at e
    have e2 : valAt x (j ⁻¹ᵁ D) hx ((j.app D).hom s') = val x s :=
      (congrArg (valAt x (j ⁻¹ᵁ D) hx) hs').trans
        ((Twhopf.valAt_restrict x (homOfLE (le_top : j ⁻¹ᵁ D ≤ ⊤)) hx le_top s).trans (htop _ _ _))
    rw [e2, map_pow] at e
    rw [← e]
    ring

theorem char : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)), Γ.IsEmb A j → IsOpenImmersion j → Γ.TranslatesCover A j ⊤ → Γ.btOrder ⊤ = A := by
  intro R _ _ T _ _ Γ A hA j hj hopen hcov
  have htop (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤) (s : Γ(Γ.G.left, ⊤)) :
      valAt (Γ.pt t).left ⊤ h s = val (Γ.pt t).left s := by
    simp only [valAt, val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hmem (f : T → R) : f ∈ Γ.btOrder ⊤ ↔
      ∀ t, ∃ s : Γ(Γ.G.left, ⊤), ∀ h,
        val (Γ.pt h).left s = algebraMap R (FractionRing R) (f (t * h)) := by
    rw [Twhopf.mem_order]
    change (∀ t, ∀ g ∈ (⊤ : Γ.G.left.Opens), Γ.RegularAt
      (fun h => algebraMap R (FractionRing R) (f (t * h))) g) ↔ _
    simp only [Twhopf.reg_iff, htop]
    simp
  have hval (t : T) (a : A) :
      val (Γ.pt t).left (pb j a) = algebraMap R (FractionRing R) (a.1 t) :=
    val_pb (hj.pt t) a
  have tr := Twhopf.translate_mem R T A hA
  apply le_antisymm
  · intro f hf
    rw [hmem] at hf
    let I : Ideal A :=
      { carrier := {a | a.1 * f ∈ A}
        add_mem' := fun {a b} ha hb => by
          change (a.1 + b.1) * f ∈ A
          rw [add_mul]
          exact A.add_mem ha hb
        zero_mem' := by
          change (0 : T → R) * f ∈ A
          rw [zero_mul]
          exact A.zero_mem
        smul_mem' := fun c a ha => by
          change (c.1 * a.1) * f ∈ A
          rw [_root_.mul_assoc]
          exact A.mul_mem c.2 ha }
    have hI : I = ⊤ := by
      by_contra hne
      obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hne
      obtain ⟨t, g, -, hg⟩ := hcov ⟨P, hP.isPrime⟩
      obtain ⟨s, hs⟩ := hf t
      obtain ⟨u, a, hu, hua⟩ := exists_den_of_open j g s
      have h1 : ∀ h, u.1 h * f (t * h) = a.1 h := fun h => by
        have := hua _ (Γ.pt h).left
        rw [hval, hval, hs, ← map_mul] at this
        exact IsFractionRing.injective R (FractionRing R) this
      let u' : A := ⟨_, tr _ u.2 t⁻¹⟩
      refine hu ((hg u' u fun h => by simp [u']).1 (hIP ?_))
      change u'.1 * f ∈ A
      convert tr _ a.2 t⁻¹ using 1
      funext h
      rw [← h1]
      simp [u']
    have h1 : (1 : A) ∈ I := hI ▸ Submodule.mem_top
    have h2 : (1 : T → R) * f ∈ A := h1
    rwa [_root_.one_mul] at h2
  · intro f hf
    rw [hmem]
    exact fun t => ⟨pb j ⟨_, tr f hf t⟩, fun h => hval h _⟩

end PositivityTheory.HtPt.Mh
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLat
noncomputable section

namespace PositivityTheory.HtPt.Htat

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT

theorem inj_mod_of_surj_mod {M : Type} [AddCommGroup M] [Module.Finite ℤ M] (f : M →ₗ[ℤ] M) (q : ℕ)
    (hs : ∀ a, ∃ z b, a = f z + q • b) (z b : M) (h : f z = q • b) : ∃ z', z = q • z' := by
  let K : Submodule ℤ M := LinearMap.range (q • (LinearMap.id : M →ₗ[ℤ] M))
  have hK : ∀ a, a ∈ K ↔ ∃ b, a = q • b := fun a =>
    ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hle : K ≤ K.comap f := by
    intro a ha
    obtain ⟨b, rfl⟩ := (hK a).1 ha
    exact (hK _).2 ⟨f b, map_nsmul f q b⟩
  let g := K.mapQ K f hle
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨a, rfl⟩ := K.mkQ_surjective a
    obtain ⟨z, b, rfl⟩ := hs a
    refine ⟨K.mkQ z, ?_⟩
    show K.mkQ (f z) = _
    rw [map_add (f := _), show K.mkQ (q • b) = 0 from (Submodule.Quotient.mk_eq_zero K).2 ((hK _).2 ⟨b, rfl⟩), add_zero]
  have hi := OrzechProperty.injective_of_surjective_endomorphism g hg
  have h0 : g (K.mkQ z) = g 0 := by
    rw [map_zero]
    exact (Submodule.Quotient.mk_eq_zero K).2 ((hK _).2 ⟨b, h⟩)
  exact (hK z).1 ((Submodule.Quotient.mk_eq_zero K).1 (hi h0))

theorem surj_mod_pow {M L : Type} [AddCommGroup M] [AddCommGroup L] (σ : M →+ L) (p : ℕ)
    (h : ∀ a, ∃ z b, a = σ z + p • b) (n : ℕ) (a : L) : ∃ z b, a = σ z + (p ^ n) • b := by
  induction n with
  | zero => exact ⟨0, a, by simp⟩
  | succ n ih =>
    obtain ⟨z, b, rfl⟩ := ih
    obtain ⟨z', b', rfl⟩ := h b
    exact ⟨z + (p ^ n) • z', b', by rw [map_add (f := _), map_nsmul, smul_add, pow_succ, mul_smul, add_assoc]⟩

theorem perfect_mod {M L : Type} [AddCommGroup M] [AddCommGroup L] [Module.Free ℤ L] (σ : M →ₗ[ℤ] L) (q : ℕ)
    (EF : L →ₗ[ℤ] L →ₗ[ℤ] ℤ) (hE : Function.Bijective EF) (hs : ∀ a, ∃ z b, a = σ z + q • b)
    (hk : ∀ z b, σ z = q • b → ∃ z', z = q • z') :
    (∀ φ : M →+ ZMod q, ∃ y, ∀ z, ((EF (σ y) (σ z) : ℤ) : ZMod q) = φ z) ∧
      ∀ y, (∀ z, ((EF (σ y) (σ z) : ℤ) : ZMod q) = 0) → ∃ y', y = q • y' := by
  let B := Module.Free.chooseBasis ℤ L
  constructor
  · intro φ
    choose zz cc hzc using hs
    let s : L →ₗ[ℤ] M := B.constr ℤ fun i => zz (B i)
    let t : L →ₗ[ℤ] L := B.constr ℤ fun i => cc (B i)
    have hst : ∀ a, a = σ (s a) + q • t a := by
      have : (LinearMap.id : L →ₗ[ℤ] L) = σ ∘ₗ s + q • t := B.ext fun i => by
        simpa [s, t] using hzc (B i)
      intro a
      simpa using LinearMap.congr_fun this a
    let ψ : L →ₗ[ℤ] ℤ := B.constr ℤ fun i => ((φ (zz (B i))).cast : ℤ)
    have hψ : ∀ a, ((ψ a : ℤ) : ZMod q) = φ (s a) := by
      have : (Int.castAddHom (ZMod q)).toIntLinearMap ∘ₗ ψ = φ.toIntLinearMap ∘ₗ s := B.ext fun i => by
        simp [ψ, s]
      intro a
      simpa using LinearMap.congr_fun this a
    obtain ⟨a₀, ha₀⟩ := hE.2 ψ
    refine ⟨zz a₀, fun z => ?_⟩
    obtain ⟨z', hz'⟩ := hk (z - s (σ z)) (t (σ z)) (by
      rw [map_sub, sub_eq_iff_eq_add']
      exact hst (σ z))
    have h1 : φ z = φ (s (σ z)) := by
      rw [sub_eq_iff_eq_add.1 hz', map_add (f := _), map_nsmul]
      simp [← sub_eq_iff_eq_add.1 hz']
    have h2 : σ (zz a₀) = a₀ - q • cc a₀ := eq_sub_iff_add_eq.2 (hzc a₀).symm
    rw [h1, ← hψ, ← ha₀, h2]
    simp
  · intro y hy
    have hd : ∀ a, (q : ℤ) ∣ EF (σ y) a := by
      intro a
      obtain ⟨z, b, rfl⟩ := hs a
      rw [map_add (f := _), map_nsmul, nsmul_eq_mul]
      exact dvd_add ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (hy z)) (dvd_mul_right _ _)
    choose d hd using hd
    let ψ : L →ₗ[ℤ] ℤ := B.constr ℤ fun i => d (B i)
    obtain ⟨a₀, ha₀⟩ := hE.2 ψ
    refine hk y a₀ (hE.1 (B.ext fun i => ?_))
    rw [map_nsmul, ha₀, hd]
    simp [ψ]

theorem exists_levPairing {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (p : ℕ) [Fact p.Prime] (n : ℕ)
    {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) {N : ℕ} (u : Fin N → La)
    (hu : IsPolLattice c p EF u) :
    ∃ (π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n)
      (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n)),
      (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) ∧
      (∀ z z', e z z' = ((EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) ∧
      (∀ a : La, ∃ (z : Fin N → 𝓞 E) (b : La), a = ∑ k, z k • u k + (p ^ n) • b) ∧
      Function.Surjective π ∧
      (∀ y, π (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = (p ^ n) • y') ∧
      (∀ y, e y y = 0) ∧
      (∀ (a : 𝓞 E) (y z : Fin N → 𝓞 E), e (a • y) z = e y (RingOfIntegers.mapRingEquiv c a • z)) ∧
      (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ n), ∃ y, e y = φ) ∧
      (∀ y, e y = 0 → ∃ y', y = (p ^ n) • y') := by
  have := hu.free
  have := hu.finite
  let σ₀ : (Fin N → 𝓞 E) →ₗ[𝓞 E] La := Fintype.linearCombination (𝓞 E) u
  let σ : (Fin N → 𝓞 E) →ₗ[ℤ] La := σ₀.toAddMonoidHom.toIntLinearMap
  have hσ : ∀ z, σ z = ∑ k, z k • u k := fun z => Fintype.linearCombination_apply _ _ _
  have hσa : ∀ (a : 𝓞 E) z, σ (a • z) = a • σ z := fun a z => map_smul σ₀ a z
  have hs : ∀ a, ∃ z b, a = σ z + (p ^ n) • b :=
    surj_mod_pow σ.toAddMonoidHom p (fun a => by
      obtain ⟨z, b, h⟩ := hu.span a
      exact ⟨z, b, h.trans (by rw [← hσ]; rfl)⟩) n
  have hrk : Module.finrank ℤ La = Module.finrank ℤ (Fin N → 𝓞 E) := by
    rw [hu.rank, Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  let φ := LinearEquiv.ofFinrankEq La (Fin N → 𝓞 E) hrk
  have hk : ∀ z b, σ z = (p ^ n) • b → ∃ z', z = (p ^ n) • z' := fun z b h =>
    inj_mod_of_surj_mod (φ.toLinearMap ∘ₗ σ) (p ^ n) (fun a => by
      obtain ⟨z, b, h⟩ := hs (φ.symm a)
      refine ⟨z, φ b, ?_⟩
      have := congrArg φ h
      rwa [φ.apply_symm_apply, map_add, map_nsmul] at this) z (φ b) (by
      show φ (σ z) = _
      rw [h, map_nsmul])
  obtain ⟨hsu, hin⟩ := perfect_mod σ (p ^ n) EF hu.unimod hs hk
  let K : Submodule ℤ La := LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))
  let π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n :=
    AddMonoidHom.toMultiplicative (K.mkQ ∘ₗ σ).toAddMonoidHom
  have hπ : ∀ z, π (Multiplicative.ofAdd z) = lev p n (σ z) := fun z => rfl
  let e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ n) :=
    { toFun := fun y => (Int.castAddHom (ZMod (p ^ n))).comp (EF (σ y) ∘ₗ σ).toAddMonoidHom
      map_zero' := by ext z; simp
      map_add' := fun y y' => by ext z; simp }
  have he : ∀ y z, e y z = ((EF (σ y) (σ z) : ℤ) : ZMod (p ^ n)) := fun y z => rfl
  have hone : ∀ a : La, lev p n a = 1 ↔ ∃ b, a = (p ^ n) • b := fun a => by
    show (Submodule.Quotient.mk a : La ⧸ K) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  refine ⟨π, e, fun z => by rw [hπ, hσ], fun z z' => by rw [he, hσ, hσ], fun a => ?_, fun t => ?_, fun y => ?_,
    fun y => ?_, fun a y z => ?_, fun ψ => ?_, fun y hy => ?_⟩
  · simpa only [hσ] using hs a
  · obtain ⟨a, ha⟩ := K.mkQ_surjective (Multiplicative.toAdd t)
    obtain ⟨z, b, rfl⟩ := hs a
    refine ⟨Multiplicative.ofAdd z, ?_⟩
    have h0 : K.mkQ ((p ^ n) • b) = 0 := (hone _).2 ⟨b, rfl⟩
    rw [map_add (f := _), h0, add_zero] at ha
    exact ha
  · rw [hπ, hone]
    exact ⟨fun ⟨b, hb⟩ => hk y b hb, fun ⟨y', hy'⟩ => ⟨σ y', by rw [hy', map_nsmul]⟩⟩
  · rw [he, hu.alt, Int.cast_zero]
  · rw [he, he, hσa, hσa, hu.adj]
  · obtain ⟨y, hy⟩ := hsu ψ
    exact ⟨y, AddMonoidHom.ext hy⟩
  · exact hin y fun z => (he y z).symm.trans (by rw [hy]; rfl)

end PositivityTheory.HtPt.Htat
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.Twpdiv
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivTate
noncomputable section

namespace PositivityTheory.HtPt.Twpdiv

open TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {G : PDivGroup p O}

def lvl (G : PDivGroup p O) (n : ℕ) : G.Tate →+ Additive (WithConv (G.A n →ₐ[O] O)) where
  toFun x := Additive.ofMul (x.conv n)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lvl_smul (n : ℕ) (a : ℤ_[p]) (x : G.Tate) : lvl G n (a • x) = digit n a • lvl G n x := rfl

theorem tate_equiv {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (τ : La →+ G.Tate)
    (h1 : ∀ n a a', (τ a).conv n = (τ a').conv n ↔ ∃ b : La, a - a' = (p ^ n) • b)
    (h2 : ∀ n y, ∃ a, (τ a).conv n = y) :
    ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] G.Tate, ∀ a, j (1 ⊗ₜ a) = τ a := by
  classical
  let j : ℤ_[p] ⊗[ℤ] La →ₗ[ℤ_[p]] G.Tate := LinearMap.liftBaseChange ℤ_[p] τ.toIntLinearMap
  have hj : ∀ (c : ℤ_[p]) a, j (c ⊗ₜ a) = c • τ a := fun c a => rfl
  let b := Module.Free.chooseBasis ℤ La
  have key : ∀ (c : Module.Free.ChooseBasisIndex ℤ La → ℤ_[p]) n,
      (j (∑ i, c i ⊗ₜ b i)).conv n = (τ (∑ i, digit n (c i) • b i)).conv n := by
    intro c n
    change lvl G n _ = lvl G n _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hj, lvl_smul, map_nsmul]
  have hdiv : ∀ n (a a' : La), (∃ u : La, a - a' = (p ^ n) • u) ↔
      ∀ i, ((b.repr a i : ℤ) : ZMod (p ^ n)) = (b.repr a' i : ℤ) := by
    intro n a a'
    simp only [ZMod.intCast_eq_intCast_iff_dvd_sub]
    constructor
    · rintro ⟨u, hu⟩ i
      have := congrArg (fun x => b.repr x i) hu
      simp only [map_sub, map_nsmul, Finsupp.sub_apply, Finsupp.smul_apply, nsmul_eq_mul] at this
      rw [dvd_sub_comm]
      exact ⟨_, this⟩
    · intro H
      choose u hu using fun i => dvd_sub_comm.1 (H i)
      refine ⟨b.equivFun.symm u, b.equivFun.injective (funext fun i => ?_)⟩
      rw [map_nsmul, LinearEquiv.apply_symm_apply, map_sub]
      simpa using hu i
  have hrep : ∀ (k : Module.Free.ChooseBasisIndex ℤ La → ℕ) i, b.repr (∑ i, k i • b i) i = k i := by
    intro k i
    have : ∑ i, k i • b i = b.equivFun.symm fun i => (k i : ℤ) := by simp
    rw [this, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨LinearEquiv.ofBijective j ⟨?_, fun x => ?_⟩, fun a => (hj 1 a).trans (one_smul _ _)⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨c, rfl⟩ : ∃ c : Module.Free.ChooseBasisIndex ℤ La → ℤ_[p], z = ∑ i, c i ⊗ₜ b i := by
      refine ⟨(b.baseChange ℤ_[p]).repr z, ?_⟩
      conv_lhs => rw [← (b.baseChange ℤ_[p]).sum_repr z]
      simp [TensorProduct.smul_tmul']
    have hc : ∀ i, c i = 0 := fun i => PadicInt.ext_of_toZModPow.1 fun n => by
      have h3 := key c n
      rw [hz, ← map_zero τ] at h3
      have h4 := (hdiv n _ _).1 ((h1 n _ _).1 h3) i
      rw [hrep] at h4
      rw [map_zero, ← cast_digit]
      simpa using h4.symm
    simp [hc]
  · choose a ha using fun n => h2 n (x.conv n)
    have hc : ∀ n, (τ (a (n + 1))).conv n = (τ (a n)).conv n := fun n => by
      rw [← TateOver.compat_conv, ha, ha, TateOver.compat_conv]
    have hd : ∀ i n, (p : ℤ) ^ n ∣ b.repr (a (n + 1)) i - b.repr (a n) i := fun i n => by
      have := (hdiv n _ _).1 ((h1 n _ _).1 (hc n).symm) i
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      exact_mod_cast this
    refine ⟨∑ i, PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
      (fun n => b.repr (a n) i) p (hd i)) ⊗ₜ b i,
      TateOver.ext_conv fun n => ?_⟩
    rw [key, ← ha, h1, hdiv]
    intro i
    rw [hrep, Int.cast_natCast, cast_digit, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub
      (fun n => b.repr (a n) i) p (hd i)]

end PositivityTheory.HtPt.Twpdiv
end
end

noncomputable section

namespace PositivityTheory.HtPt.Twpdiv

open TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT Coalgebra Bialgebra

section Lev

variable {La : Type} [AddCommGroup La] (p : ℕ)

theorem lev_surjective (n : ℕ) : Function.Surjective (lev (La := La) p n) := fun t =>
  Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)

theorem lev_eq_iff (n : ℕ) (a a' : La) : lev p n a = lev p n a' ↔ ∃ b : La, a - a' = (p ^ n) • b := by
  rw [lev, lev, Multiplicative.ofAdd.apply_eq_iff_eq, Submodule.Quotient.eq]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

theorem lev_add (n : ℕ) (a a' : La) : lev p n (a + a') = lev p n a * lev p n a' := rfl

theorem lev_zero (n : ℕ) : lev p n (0 : La) = 1 := rfl

theorem lev_nsmul (n k : ℕ) (a : La) : lev p n (k • a) = lev p n a ^ k := by
  induction k with
  | zero => simp [lev_zero]
  | succ k ih => rw [succ_nsmul, lev_add, ih, pow_succ]

theorem lev_pow (n : ℕ) (t : LevGrp La p n) : t ^ p ^ n = 1 := by
  obtain ⟨a, rfl⟩ := lev_surjective p n t
  rw [← lev_nsmul, ← lev_zero, lev_eq_iff]
  exact ⟨a, sub_zero _⟩

def incl (n : ℕ) : LevGrp La p n →* LevGrp La p (n + 1) :=
  AddMonoidHom.toMultiplicative (Submodule.mapQ _ _ (p • (LinearMap.id : La →ₗ[ℤ] La)) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨b, by simp only [LinearMap.smul_apply, LinearMap.id_apply, pow_succ', mul_smul]⟩)).toAddMonoidHom

theorem incl_lev (n : ℕ) (a : La) : incl p n (lev p n a) = lev p (n + 1) (p • a) := rfl

theorem card_lev [Module.Free ℤ La] [Module.Finite ℤ La] (n : ℕ) :
    Nat.card (LevGrp La p n) = p ^ (n * Module.finrank ℤ La) := by
  rw [pow_mul, ← AddSubgroup.index_range_nsmul]
  have : (nsmulAddMonoidHom (α := La) (p ^ n)).range =
      (LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))).toAddSubgroup := by
    ext x; exact Iff.rfl
  rw [this]
  rfl

instance [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] (n : ℕ) : Finite (LevGrp La p n) :=
  Nat.finite_of_card_ne_zero (by rw [card_lev]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

end Lev

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {La : Type} [AddCommGroup La] [Module.Free ℤ La]
  [Module.Finite ℤ La] {L : Type} [AddCommGroup L] [Module O L] (X : OrdTower p O La L)

def resT (n : ℕ) : Ord (X.hopf (n + 1)) →ₐc[O] Ord (X.hopf n) :=
  Ord.comap (X.hopf n) (X.hopf (n + 1)) (incl p n) fun f hf => (X.res_iff n _).2 ⟨f, hf, fun _ => rfl⟩

theorem ev_resT (n : ℕ) (t : LevGrp La p n) (f : Ord (X.hopf (n + 1))) :
    Ord.ev _ t (resT X n f) = Ord.ev _ (incl p n t) f := Ord.ev_comap _ _ _ _ t f

theorem resT_surjective (n : ℕ) : Function.Surjective (resT X n) := fun g => by
  obtain ⟨f, hf, h⟩ := (X.res_iff n _).1 (Ord.equiv _ g).2
  refine ⟨(Ord.equiv _).symm ⟨f, hf⟩, Ord.sep _ _ _ fun t => ?_⟩
  obtain ⟨a, rfl⟩ := lev_surjective p n t
  rw [ev_resT]
  exact (h a).symm

theorem ker_resT (n : ℕ) :
    RingHom.ker (resT X n) = torsionIdeal (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n) := by
  apply le_antisymm
  · intro f hf
    have hf' : resT X n f = 0 := hf
    have h1 := X.ker_res n (Ord.equiv _ f) fun a => by
      have := ev_resT X n (lev p n a) f
      rw [hf', map_zero] at this
      exact this.symm
    have h2 : Ideal.span {g : X.A (n + 1) | ∃ h ∈ X.A (n + 1), ∀ t, g.1 t = h (t ^ p ^ n) - h 1} ≤
        (torsionIdeal (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n)).comap
          (Ord.equiv (X.hopf (n + 1))).symm := by
      rw [Ideal.span_le]
      rintro g ⟨u, hu, hg⟩
      let u' := (Ord.equiv (X.hopf (n + 1))).symm ⟨u, hu⟩
      have h3 : (Ord.equiv (X.hopf (n + 1))).symm g =
          mulBy (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n)
            (u' - algebraMap O _ (counit u')) := Ord.sep _ _ _ fun t => by
        rw [Ord.ev_mulBy, map_sub, AlgHom.commutes, Ord.counit_eq]
        exact hg t
      change (Ord.equiv (X.hopf (n + 1))).symm g ∈ torsionIdeal (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n)
      rw [h3]
      have hu' : u' - algebraMap O _ (counit u') ∈ augIdeal (R := O) (A := Ord (X.hopf (n + 1))) := by
        change counit (R := O) (u' - algebraMap O _ (counit (R := O) u')) = 0
        rw [map_sub, counit_algebraMap, sub_self]
      unfold torsionIdeal kerIdeal
      exact Ideal.mem_map_of_mem (mulBy (R := O) (A := Ord (X.hopf (n + 1))) (p ^ n)).toAlgHom hu'
    exact h2 h1
  · refine (kerIdeal_le_ker_iff _ (resT X n : Ord (X.hopf (n + 1)) →ₐ[O] Ord (X.hopf n))).2 fun c =>
      Ord.sep _ _ _ fun t => ?_
    rw [AlgHom.commutes]
    change Ord.ev _ t (resT X n _) = _
    rw [ev_resT, Ord.ev_mulBy, ← map_pow, lev_pow, map_one, Ord.counit_eq]
    rfl

variable [IsDomain O] [IsLocalRing O]

def grp : PDivGroup p O where
  height := Module.finrank ℤ La
  A n := Ord (X.hopf n)
  rank_eq n q := by rw [Ord.rankAtStalk_eq, card_lev]
  res := resT X
  res_surjective := resT_surjective X
  ker_res := ker_resT X

def tau : La →+ (grp X).Tate :=
  AddMonoidHom.mk' (fun a => ⟨fun n => Ord.ev (X.hopf n) (lev p n a), fun n => AlgHom.ext fun g => by
      obtain ⟨f, rfl⟩ := (grp X).res_surjective n g
      refine (congrArg (Ord.ev (X.hopf (n + 1)) (lev p (n + 1) a)) ((grp X).mulP_res n f)).trans ?_
      refine (Ord.ev_mulBy _ _ p f).trans ?_
      rw [← lev_nsmul]
      exact (ev_resT X n (lev p n a) f).symm⟩)
    fun a b => TateOver.ext_conv fun n => map_mul (Ord.evHom (X.hopf n)) (lev p n a) (lev p n b)

theorem realises : X.Realises (grp X) (fun n => Ord.equiv (X.hopf n)) (tau X) :=
  ⟨fun n f a => ev_resT X n (lev p n a) f, fun _ _ _ => rfl⟩

theorem exists_tate : ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] (grp X).Tate, ∀ a, j (1 ⊗ₜ a) = tau X a :=
  tate_equiv (tau X)
    (fun n a a' => ((Ord.evHom_bijective (X.hopf n)).1.eq_iff (a := lev p n a) (b := lev p n a')).trans
      (lev_eq_iff p n a a'))
    fun n y => by
      obtain ⟨t, ht⟩ := (Ord.evHom_bijective (X.hopf n)).2 y
      obtain ⟨a, rfl⟩ := lev_surjective p n t
      exact ⟨a, ht⟩

end PositivityTheory.HtPt.Twpdiv

end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem PositivityTheory.HtPt.Twpdiv.tower_pdiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L), ∃ (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate), X.Realises G e τ ∧ G.height = Module.finrank ℤ La ∧ ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] G.Tate, ∀ a, j (1 ⊗ₜ a) = τ a := by
  intro p _ C _ _ _ v O _ _ _ hv _ _ La _ _ _ L _ _ X
  have : ValuationRing O := ValuationRing.of_integers v hv
  exact ⟨PositivityTheory.HtPt.Twpdiv.grp X, _, _, PositivityTheory.HtPt.Twpdiv.realises X, rfl, PositivityTheory.HtPt.Twpdiv.exists_tate X⟩
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GcField
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Gc

theorem test_field : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (p : ℕ) [Fact p.Prime] (𝔮 : Ideal A), 𝔮.IsPrime → 𝔮.height = 1 → (p : A) ∈ 𝔮 → ∃ (C O : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : CommRing O) (_ : IsDomain O) (_ : Algebra O C) (v : Valuation C NNReal) (φ : A →+* O), v.Integers O ∧ v (p : C) < 1 ∧ IsAdicComplete (Ideal.span {(p : O)}) O ∧ Function.Injective φ ∧ ∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (φ a)) < 1 := by
  intro A _ _ _ _ _ p hp q hq h1 hpq
  obtain ⟨R, _, _, _, _, _⟩ : ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra A R),
      IsLocalization.AtPrime R q ∧ IsDiscreteValuationRing R :=
    ⟨Localization.AtPrime q, inferInstance, inferInstance, inferInstance, inferInstance,
      dvr_of_height_one q h1⟩
  let K := FractionRing R
  have hAR : Function.Injective (algebraMap A R) :=
    IsLocalization.injective R q.primeCompl_le_nonZeroDivisors
  haveI : CharZero R := charZero_of_injective_algebraMap hAR
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  have hpR : (p : R) ∈ IsLocalRing.maximalIdeal R := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff R q (p : A)).2 hpq
    rwa [map_natCast] at this
  obtain ⟨C, _, _, _, _, _, _, hC⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_padic_of_isDiscreteValuationRing R K p hpR
  obtain ⟨φ, hφ, hφ'⟩ := GlobalTheory.exists_isLocalHom_normIntegers hC
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  have hO := GlobalTheory.normIntegers_integers C
  have key : ∀ a : A, a ∈ q ↔
      NormedField.valuation (K := C) (algebraMap (GlobalTheory.normIntegers C) C (φ (algebraMap A R a))) < 1 := by
    intro a
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R q a, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, ← isUnit_map_iff φ, hO.isUnit_iff_valuation_eq_one]
    exact (hO.map_le_one _).lt_iff_ne.symm
  have hv : NormedField.valuation (K := C) (p : C) < 1 := by
    simpa only [map_natCast] using (key p).1 hpq
  refine ⟨C, GlobalTheory.normIntegers C, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, NormedField.valuation, φ.comp (algebraMap A R), hO, hv, ?_, ?_, key⟩
  · apply GlobalTheory.NormIntegers.isAdicComplete_span_singleton hO
    exact_mod_cast hv
  · intro a b hab
    have : (φ (algebraMap A R a) : C) = (φ (algebraMap A R b) : C) := congrArg Subtype.val hab
    rw [hφ', hφ'] at this
    exact hAR (IsFractionRing.injective R K ((algebraMap K C).injective this))

end PositivityTheory.HtPt.Gc
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.DualUnique
noncomputable section

namespace PositivityTheory.HtPt.Ga

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {N : ℕ}

theorem dual_exists (y : Fin N → M) (t : A) (G H Z : Matrix (Fin N) (Fin N) A)
    (h : H * G = 1 + t • Z) :
    ∃ i : Module.Dual A M →ₗ[A] (Fin N → A), ∀ w j, ∃ z, ∑ l, i w l * G l j = w (y j) + t * z := by
  let ev : Module.Dual A M →ₗ[A] (Fin N → A) := LinearMap.pi fun j => Module.Dual.eval A M (y j)
  refine ⟨(Matrix.vecMulLinear H).comp ev, fun w j => ⟨Matrix.vecMul (ev w) Z j, ?_⟩⟩
  change Matrix.vecMul (Matrix.vecMul (ev w) H) G j = _
  rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_smul]
  rfl

theorem dual_unique (t : A) (G H Z : Matrix (Fin N) (Fin N) A) (h : G * H = 1 + t • Z)
    (a a' r : Fin N → A) (ha : ∀ j, ∃ z, ∑ l, a l * G l j = r j + t * z)
    (ha' : ∀ j, ∃ z, ∑ l, a' l * G l j = r j + t * z) : ∃ x : Fin N → A, a = a' + t • x := by
  choose z hz using ha
  choose z' hz' using ha'
  have h1 : Matrix.vecMul (a - a') G = t • (z - z') := by
    ext j
    rw [Matrix.sub_vecMul]
    change ∑ l, a l * G l j - ∑ l, a' l * G l j = t * (z j - z' j)
    rw [hz, hz']
    ring
  have h2 := congrArg (fun v => Matrix.vecMul v H) h1
  simp only [Matrix.vecMul_vecMul, h, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_smul,
    Matrix.smul_vecMul] at h2
  refine ⟨Matrix.vecMul (z - z') H - Matrix.vecMul (a - a') Z, ?_⟩
  rw [smul_sub, ← h2]
  abel

theorem dual_split [Module.Projective A M] (y : Fin N → M) (t : A) (G : Matrix (Fin N) (Fin N) A)
    (hs : ∀ x : M, ∃ a : Fin N → A, ∃ x' : M, x = ∑ j, a j • y j + t • x')
    (i : Module.Dual A M →ₗ[A] (Fin N → A))
    (hi : ∀ w j, ∃ z, ∑ l, i w l * G l j = w (y j) + t * z) :
    ∃ r : (Fin N → A) →ₗ[A] Module.Dual A M, ∀ w, ∃ w', r (i w) = w + t • w' := by
  let f : ((Fin N → A) × M) →ₗ[A] M :=
    (Fintype.linearCombination A y).coprod (t • LinearMap.id)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, x', e⟩ := hs x
    exact ⟨(a, x'), by rw [e]; simp [f, Fintype.linearCombination_apply]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let s₁ := (LinearMap.fst A _ _).comp s
  let s₂ := (LinearMap.snd A _ _).comp s
  have hs' : ∀ x, ∑ j, s₁ x j • y j + t • s₂ x = x := by
    intro x
    have := LinearMap.congr_fun hs x
    simpa [f, s₁, s₂, Fintype.linearCombination_apply] using this
  let B : (Fin N → A) →ₗ[A] Module.Dual A M := (dotProductBilin A A).compl₂ s₁
  refine ⟨B.comp (Matrix.vecMulLinear G), fun w => ?_⟩
  choose z hz using hi w
  refine ⟨B z - w.comp s₂, ?_⟩
  ext x
  change ∑ j, (∑ l, i w l * G l j) * s₁ x j = w x + t * (∑ j, z j * s₁ x j - w (s₂ x))
  conv_rhs => rw [← hs' x]
  rw [hs' x]
  nth_rewrite 2 [← hs' x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hz, map_add (f := _), map_sum, map_smul, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_sub,
    Finset.mul_sum, mul_assoc]
  simp only [mul_comm (w _)]
  ring

end

theorem dual_map : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d : A) (m : ℕ), (∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → (∃ (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), D.IsDualMap σ d m i) ∧ (∀ i i', D.IsDualMap σ d m i → D.IsDualMap σ d m i' → ∀ w, ∃ x : Fin N → A, i w = i' w + ((p : A) ^ m) • x) ∧ ∀ i, D.IsDualMap σ d m i → ∃ r : (Fin N → A) →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∀ w, ∃ w', r (i w) = w + ((p : A) ^ m) • w' := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D κ σ d m hσ hd hκ hom hproj
  obtain ⟨G, H, Z, Z', hG, hGH, hHG⟩ := gram_unit A K hAK E c hc p R N Ω D σ d (hσ σ) hd
  obtain ⟨-, -, hsurj⟩ := q_surj A K hAK E c hc p R N Ω D κ (σ.comp c.toRingHom) m (hσ _) hκ hom
  obtain ⟨t, ht⟩ := hκ
  have hR : ∀ Y : Matrix (Fin N) (Fin N) A, ((p : A) ^ R) • Y = ((p : A) ^ m) • (κ * t) • Y := by
    intro Y
    rw [ht, smul_smul]
    congr 1
    ring
  rw [hR] at hGH hHG
  let y : Fin N → D.omHT (σ.comp c.toRingHom) := fun j =>
    ⟨_, proj_mem_omHT D (σ.comp c.toRingHom) (h_mem_om' D (Pi.single j 1))⟩
  have key : ∀ i, D.IsDualMap σ d m i ↔
      ∀ w j, ∃ z, ∑ l, i w l * G l j = w (y j) + (p : A) ^ m * z := by
    intro i
    constructor
    · intro h w j
      obtain ⟨z, hz⟩ := h w j (y j) rfl
      refine ⟨z, hAK ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hz, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, hG]
    · intro h w j y' hy'
      obtain rfl : y' = y j := Subtype.ext hy'
      obtain ⟨z, hz⟩ := h w j
      refine ⟨z, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hz, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, hG]
  simp only [key]
  refine ⟨dual_exists y _ G H _ hHG, fun i i' hi hi' w =>
    dual_unique _ G H _ hGH _ _ (fun j => w (y j)) (hi w) (hi' w), fun i hi =>
    dual_split y _ G (fun x => ?_) i hi⟩
  obtain ⟨a, x', hx', e⟩ := hsurj x x.2
  refine ⟨a, ⟨x', hx'⟩, Subtype.ext ?_⟩
  rw [e, Submodule.coe_add, Submodule.coe_sum]
  rfl

end PositivityTheory.HtPt.Ga
end
end
