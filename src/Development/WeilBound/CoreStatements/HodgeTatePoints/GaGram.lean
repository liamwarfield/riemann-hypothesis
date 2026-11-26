module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentres

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GaGram
noncomputable section

namespace PositivityTheory.HtPt.Ga

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem exists_left_inv {B : Type} [CommRing B] {n : ℕ} (φ : ZMod n →+* B) (c : 𝓞 E ≃+* 𝓞 E)
    (hc : ∀ a, c (c a) = a) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod n)
    (adj : ∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (c a • y))
    (surj : ∀ f : (Fin N → 𝓞 E) →+ ZMod n, ∃ x, e x = f)
    (s : 𝓞 E →+* B) (cc u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → B) (hu : ∑ k, u k * cc k = 1)
    (hcc : ∀ (a : 𝓞 E) l, ∑ k, cc k *
      (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : B) = s a * cc l) :
    ∃ β : Matrix (Fin N) (Fin N) B, ∀ j₀ j, ∑ i, β j₀ i *
      (∑ k, cc k * φ (e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1))) =
        if j₀ = j then 1 else 0 := by
  classical
  set b := RingOfIntegers.basis E with hb
  let Λ : (Fin N → 𝓞 E) → (Fin N → 𝓞 E) → B := fun x y => ∑ k, cc k * φ (e (b k • x) y)
  have Λadd : ∀ x x' y, Λ (x + x') y = Λ x y + Λ x' y := by
    intro x x' y
    simp only [Λ, smul_add, map_add (f := _), AddMonoidHom.add_apply, mul_add, Finset.sum_add_distrib]
  have Λsmul : ∀ (a : 𝓞 E) x y, Λ (a • x) y = s a * Λ x y := by
    intro a x y
    have h1 : ∀ k, b k • a • x = ∑ l, (b.repr (a * b k) l) • (b l • x) := by
      intro k
      rw [smul_smul, mul_comm]
      conv_lhs => rw [← b.sum_repr (a * b k)]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_assoc]
    have h2 : ∀ k, φ (e (b k • a • x) y) = ∑ l, ((b.repr (a * b k) l : ℤ) : B) * φ (e (b l • x) y) := by
      intro k
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_sum]
      change φ ((AddMonoidHom.eval y) (∑ l, e ((b.repr (a * b k) l) • (b l • x)))) = _
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      change φ (e ((b.repr (a * b k) l) • (b l • x)) y) = _
      rw [map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul, zsmul_eq_mul]
    simp only [Λ, h2, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, ← hcc a l, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  let Λh : (Fin N → 𝓞 E) → (Fin N → 𝓞 E) →+ B := fun y =>
    AddMonoidHom.mk' (fun x => Λ x y) (fun x x' => Λadd x x' y)
  have hdec : ∀ x y, Λ x y = ∑ i, s (x i) * Λ (Pi.single i 1) y := by
    intro x y
    have hx : x = ∑ i, x i • (Pi.single i 1 : Fin N → 𝓞 E) := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun i _ => ?_
      funext j
      simp [Pi.single_apply]
    have := congrArg (Λh y) hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simpa [Λh, Λsmul] using this
  let f : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (Fin N → 𝓞 E) →+ ZMod n := fun q =>
    AddMonoidHom.mk' (fun y => ((b.repr (c (y q.1)) q.2 : ℤ) : ZMod n)) (by
      intro y y'
      simp only [Pi.add_apply, map_add (f := _), Finsupp.add_apply, Int.cast_add])
  choose x hx using fun q => surj (f q)
  have hΛx : ∀ j₀ l j, Λ (x (j₀, l)) (Pi.single j 1) = if j₀ = j then cc l else 0 := by
    intro j₀ l j
    have hk : ∀ k, e (b k • x (j₀, l)) (Pi.single j 1) =
        ((b.repr (c ((Pi.single j (c (b k)) : Fin N → 𝓞 E) j₀)) l : ℤ) : ZMod n) := by
      intro k
      rw [adj, hx]
      have : (c (b k) • (Pi.single j 1 : Fin N → 𝓞 E)) = Pi.single j (c (b k)) := by
        funext i
        simp [Pi.single_apply]
      rw [this]
      rfl
    simp only [Λ, hk]
    split_ifs with hj
    · subst hj
      simp only [Pi.single_eq_same, hc, Basis.repr_self, Finsupp.single_apply]
      simp
    · simp [Pi.single_apply, hj]
  refine ⟨Matrix.of fun j₀ i => ∑ l, u l * s (x (j₀, l) i), ?_⟩
  intro j₀ j
  have hΓ : ∀ i, (∑ k, cc k * φ (e (Pi.single i (b k)) (Pi.single j 1))) = Λ (Pi.single i 1) (Pi.single j 1) := by
    intro i
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (Pi.single i (b k) : Fin N → 𝓞 E) = b k • Pi.single i 1 from by
      funext i'
      simp [Pi.single_apply]]
  simp only [hΓ, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ l, ∑ i, u l * s (x (j₀, l) i) * Λ (Pi.single i 1) (Pi.single j 1) = u l * (if j₀ = j then cc l else 0) := by
    intro l
    rw [← hΛx, hdec (x (j₀, l)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [this]
  split_ifs
  · simpa using hu
  · simp

end

theorem exists_of_map_eq_one {A : Type} [CommRing A] {N : ℕ} (t : A) (M : Matrix (Fin N) (Fin N) A)
    (h : (Ideal.Quotient.mk (Ideal.span {t})).mapMatrix M = 1) :
    ∃ Z : Matrix (Fin N) (Fin N) A, M = 1 + t • Z := by
  have hmem : ∀ i j, ∃ z : A, z * t = M i j - (1 : Matrix (Fin N) (Fin N) A) i j := by
    intro i j
    have h1 := congrFun (congrFun h i) j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h1
    have h2 : Ideal.Quotient.mk (Ideal.span {t}) (M i j) =
        Ideal.Quotient.mk (Ideal.span {t}) ((1 : Matrix (Fin N) (Fin N) A) i j) := by
      rw [h1, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    exact Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h2)
  choose Z hZ using hmem
  refine ⟨Matrix.of Z, ?_⟩
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  rw [mul_comm, hZ]
  ring

theorem gram_unit : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (d : A), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → ∃ G H Z Z' : Matrix (Fin N) (Fin N) A, (∀ i j, algebraMap A K (G i j) = D.gram σ d i j) ∧ G * H = 1 + ((p : A) ^ R) • Z ∧ H * G = 1 + ((p : A) ^ R) • Z' := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D σ d hσ hd
  classical
  obtain ⟨-, hrange, u, hu⟩ := GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt A K E σ d hAK hσ hd
  choose g hg using hrange
  set T := algebraMap A K with hT
  set b := RingOfIntegers.basis E with hb
  let Gm : Matrix (Fin N) (Fin N) A := Matrix.of fun i j =>
    ∑ k, g k * (((D.e (Pi.single i (b k)) (Pi.single j 1)).val : ℕ) : A)
  let I : Ideal A := Ideal.span {(p : A) ^ R}
  let mkB := Ideal.Quotient.mk I
  haveI : NeZero (p ^ R) := ⟨by have := (Fact.out : p.Prime).pos; positivity⟩
  have hzero : (Int.castRingHom (A ⧸ I)) ((p ^ R : ℕ) : ℤ) = 0 := by
    show ((((p ^ R : ℕ) : ℤ)) : A ⧸ I) = 0
    rw [Int.cast_natCast, Nat.cast_pow, ← map_natCast mkB, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  let φ : ZMod (p ^ R) →+* A ⧸ I :=
    (Ideal.Quotient.lift (Ideal.span {((p ^ R : ℕ) : ℤ)}) (Int.castRingHom (A ⧸ I)) (by
      intro a ha
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, hzero, mul_zero])).comp (Int.quotientSpanNatEquivZMod (p ^ R)).symm.toRingHom
  have hφ : ∀ z : ZMod (p ^ R), φ z = mkB ((z.val : ℕ) : A) := by
    intro z
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast, map_natCast]
  have hinj : Function.Injective T.rangeRestrict := fun x y h => hAK (by
    have := congrArg Subtype.val h
    simpa using this)
  let eA : A ≃+* T.range := RingEquiv.ofBijective T.rangeRestrict ⟨hinj, T.rangeRestrict_surjective⟩
  let σ' : 𝓞 E →+* T.range := (σ.comp (algebraMap (𝓞 E) E)).codRestrict T.range (fun a => hσ a)
  let ψ : 𝓞 E →+* A := eA.symm.toRingHom.comp σ'
  have hψ : ∀ a, T (ψ a) = σ a := by
    intro a
    have := congrArg Subtype.val (eA.apply_symm_apply (σ' a))
    exact this
  let s : 𝓞 E →+* A ⧸ I := mkB.comp ψ
  let cc : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A ⧸ I := fun k => mkB (g k)
  let uB : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A ⧸ I := fun k => mkB (u k)
  have hu' : ∑ k, uB k * cc k = 1 := by
    have : ∑ k, u k * g k = 1 := by
      apply hAK
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_one, ← hu]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, hg]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [uB, cc, ← map_mul, ← map_sum, this, map_one]
  have hcc : ∀ (a : 𝓞 E) l, ∑ k, cc k * (((b.repr (a * b k) l : ℤ)) : A ⧸ I) = s a * cc l := by
    intro a l
    have : ∑ k, g k * (((b.repr (a * b k) l : ℤ)) : A) = ψ a * g l := by
      apply hAK
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_mul, hψ, hg, mul_left_comm, ← map_mul, GlobalTheory.CompanionTheory.Ar.HT.ProjEig.mul_dualInt_eq,
        map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul T, hg, map_mul σ, map_intCast σ, map_intCast T]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [cc, s, RingHom.comp_apply, ← map_intCast mkB, ← map_mul, ← map_sum, this]
  have hc' : ∀ a, RingOfIntegers.mapRingEquiv c (RingOfIntegers.mapRingEquiv c a) = a := by
    intro a
    apply RingOfIntegers.ext
    simp [hc]
  obtain ⟨β, hβ⟩ := exists_left_inv φ (RingOfIntegers.mapRingEquiv c) hc' D.e D.adj D.e_surj s cc uB hu' hcc
  have hΓ : mkB.mapMatrix Gm = Matrix.of fun i j =>
      ∑ k, cc k * φ (D.e (Pi.single i (b k)) (Pi.single j 1)) := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Gm, map_sum, map_mul, hφ, cc]
  have hβΓ : β * mkB.mapMatrix Gm = 1 := by
    rw [hΓ]
    ext j₀ j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa only [Matrix.of_apply] using hβ j₀ j
  choose Hf hHf using fun ij : Fin N × Fin N => Ideal.Quotient.mk_surjective (I := I) (β ij.1 ij.2)
  let H : Matrix (Fin N) (Fin N) A := Matrix.of fun i j => Hf (i, j)
  have hH : mkB.mapMatrix H = β := by
    ext i j
    simp [H, hHf, mkB]
  obtain ⟨Z, hZ⟩ := exists_of_map_eq_one ((p : A) ^ R) (Gm * H) (by
    rw [map_mul, hH]
    exact mul_eq_one_comm.1 hβΓ)
  obtain ⟨Z', hZ'⟩ := exists_of_map_eq_one ((p : A) ^ R) (H * Gm) (by
    rw [map_mul, hH]
    exact hβΓ)
  refine ⟨Gm, H, Z, Z', ?_, hZ, hZ'⟩
  intro i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Gm, Matrix.of_apply, map_sum, map_mul, map_natCast, hg]
  unfold GlobalTheory.CompanionTheory.Ar.HT.HTChart.gram
  rfl

end PositivityTheory.HtPt.Ga
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLCentre
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LCentre.Centre

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
    have hab : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hab
    refine ⟨h0, a.2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right hab]
    exact b.2
  · rintro ⟨h0, -, hi⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨(a : Ω)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem exists_centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ := by
  intro o _ Ω _ _ κ _ x M X' Ω' _ ξ' i p' hp'
  obtain ⟨c, hc, hreg⟩ := hp'
  haveI : IsLocalRing (regAt ξ' p') := (PositivityTheory.HtPt.Ma.reg_local X' Ω' ξ').1 p'
  let φ : chRing o x c →+* regAt ξ' p' :=
    (i.comp (chRing o x c).val.toRingHom).codRestrict (regAt ξ' p') (fun a => hreg a a.2)
  let P : Ideal (chRing o x c) := (IsLocalRing.maximalIdeal (regAt ξ' p')).comap φ
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨p₀, ⟨hin, hP⟩, -⟩ := PositivityTheory.HtPt.Ma.prime_pt o Ω κ x M c hc P hPp
  have key : ∀ u : chRing o x c, unitAt M.ξ p₀ (u : Ω) ↔ unitAt ξ' p' (i u) := by
    intro u
    have h := hP u
    have h2 : u ∈ P ↔ ¬ unitAt ξ' p' (i u) := by
      change φ u ∈ IsLocalRing.maximalIdeal (regAt ξ' p') ↔ _
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_regAt_iff]
      rfl
    tauto
  have hloc := fun (c₁ : κ) (p : Cpt M.ξ) (h : InChart M.ξ x c₁ p) =>
    PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c₁ p h
  have hch : ∀ a ∈ chRing o x c, a ∈ regAt M.ξ p₀ := (hloc c p₀ hin).1
  have hdom : ∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p' := by
    intro a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c p₀ hin).2 a).1 ha
    have h1 := (key ⟨v, hv⟩).1 hvu
    rw [map_div₀, div_eq_mul_inv]
    exact mul_mem (hreg u hu) h1.2.2
  have hlift : ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a := by
    intro a ha hu'
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c p₀ hin).2 a).1 ha
    have hiu : unitAt ξ' p' (i u) := by
      have h1 : i u = i (u / v) * i v := by rw [← map_mul, div_mul_cancel₀ _ hvu.1]
      rw [h1]
      exact Flat.ZUnit.mul hu' ((key ⟨v, hv⟩).1 hvu)
    have hu0 : unitAt M.ξ p₀ u := (key ⟨u, hu⟩).2 hiu
    rw [div_eq_mul_inv]
    exact Flat.ZUnit.mul hu0 (Flat.ZUnit.inv hvu)
  have hchart : ∀ c₁, x c₁ ≠ 0 → (∀ j, i (x j / x c₁) ∈ regAt ξ' p') → InChart M.ξ x c₁ p₀ := by
    intro c₁ h1 hj
    have hmem : x c₁ / x c ∈ regAt M.ξ p₀ := hch _ (Algebra.subset_adjoin ⟨c₁, rfl⟩)
    have hunit : unitAt ξ' p' (i (x c₁ / x c)) := by
      refine ⟨(map_ne_zero i).2 (div_ne_zero h1 hc), hdom _ hmem, ?_⟩
      rw [← map_inv₀, inv_div]
      exact hj c
    have hu := hlift _ hmem hunit
    refine ⟨h1, fun j => ?_⟩
    have h2 : x j / x c₁ = x j / x c * (x c₁ / x c)⁻¹ := by
      field_simp
    rw [h2]
    exact mul_mem (hch _ (Algebra.subset_adjoin ⟨j, rfl⟩)) hu.2.2
  refine ⟨p₀, ⟨hdom, hlift⟩, ?_, hchart⟩
  intro p hp
  rw [← PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p p₀]
  obtain ⟨c₁, hc₁⟩ := M.tie.cover p
  have hin₁ := hchart c₁ hc₁.1 (fun j => hp _ (hc₁.2 j))
  intro a ha
  obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c₁ p hc₁).2 a).1 ha
  have hch₁ := (hloc c₁ p₀ hin₁).1
  have hv' : unitAt M.ξ p₀ v := hlift v (hch₁ v hv)
    ⟨(map_ne_zero i).2 hvu.1, hp v hvu.2.1, by rw [← map_inv₀]; exact hp _ hvu.2.2⟩
  rw [div_eq_mul_inv]
  exact mul_mem (hch₁ u hu) hv'.2.2

end PositivityTheory.HtPt.Mb.LCentre.Centre


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ :=
  @PositivityTheory.HtPt.Mb.LCentre.Centre.exists_centre
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLMorph
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LMorph.ChMorph

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem hom_eq_of_points {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'}
    (hgen : IsCptGen ξ') (hall : ∀ q : X', genPt ξ' ⤳ q) {i : Ω →+* Ω'} {f g : X' ⟶ X}
    (hf : Dominates ξ' ξ f i) (hg : Dominates ξ' ξ g i) (hb : ∀ q, f q = g q) : f = g := _root_.GlobalTheory.CompanionTheory.Ar.ChMorph.hom_eq_of_points (ξ := ξ) (ξ' := ξ') (i := i) (f := f) (g := g) hgen hall hf hg hb

variable {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  {o' : Type} [CommRing o'] [Algebra o' Ω'] {κ' : Type} {y : κ' → Ω'}

theorem specializes_of_dominates (M : PModel o x) (M' : PModel o' y) {i : Ω →+* Ω'} {f g : M'.X ⟶ M.X}
    (hf : Dominates M'.ξ M.ξ f i) (hg : Dominates M'.ξ M.ξ g i) (q : M'.X) : g q ⤳ f q := by
  let p' : Cpt M'.ξ := ⟨q, M'.all q⟩
  obtain ⟨h1, fa, -⟩ := RegAtDom.regAt_dominates M.X Ω M.ξ M'.X Ω' M'.ξ f i hf p'
  obtain ⟨h2, ga, gb⟩ := RegAtDom.regAt_dominates M.X Ω M.ξ M'.X Ω' M'.ξ g i hg p'
  replace gb := gb M'.tie.gen
  obtain ⟨c, hc0, hc⟩ := M.tie.cover ⟨f q, h1⟩
  obtain ⟨c', hc'0, hc'⟩ := M.tie.cover ⟨g q, h2⟩
  have hu : unitAt M.ξ ⟨g q, h2⟩ (x c / x c') := by
    refine gb _ (hc' c) ⟨?_, ga _ (hc' c), ?_⟩
    · exact (map_ne_zero i).2 (div_ne_zero hc0 hc'0)
    · rw [← map_inv₀, inv_div]
      exact fa _ (hc c')
  have hin : InChart M.ξ x c ⟨g q, h2⟩ := by
    refine ⟨hc0, fun j => ?_⟩
    have : x j / x c = x j / x c' * (x c / x c')⁻¹ := by
      field_simp
    rw [this]
    exact mul_mem (hc' j) hu.2.2
  refine specializes_iff_forall_open.2 fun V hV hq => ?_
  obtain ⟨a, ha, hau, hU⟩ := PositivityTheory.HtPt.Ma.basic o Ω κ x M c ⟨f q, h1⟩ ⟨V, hV⟩ ⟨hc0, hc⟩ hq
  have hag : a ∈ regAt M.ξ ⟨g q, h2⟩ := (M.tie.ring c hc0 a).1 ha _ hin
  refine hU ⟨g q, h2⟩ hin (gb a hag ⟨(map_ne_zero i).2 hau.1, fa a hau.2.1, ?_⟩)
  rw [← map_inv₀]
  exact fa _ hau.2.2

theorem existsUnique_dominates :
    ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x)
      (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω')
      (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) →
      ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i := _root_.GlobalTheory.CompanionTheory.Ar.ChMorph.existsUnique_dominates

end PositivityTheory.HtPt.Mb.LMorph.ChMorph


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.morph : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (o' : Type) [CommRing o'] (Ω' : Type) [Field Ω'] [Algebra o' Ω'] (κ' : Type) [Finite κ'] (y : κ' → Ω') (M' : PModel o' y) (i : Ω →+* Ω'), (∀ p', p' ∈ ctrSet o x i M'.ξ) → ∃! f : M'.X ⟶ M.X, Dominates M'.ξ M.ξ f i :=
  @PositivityTheory.HtPt.Mb.LMorph.ChMorph.existsUnique_dominates
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.LiftComul
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Chart (spMap_comp spMap_id)

namespace PositivityTheory.HtPt.Rf

section
variable {R : Type} [CommRing R] {p : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

omit [GrpObj G] in
theorem spc {A B S : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing S]
    [Algebra R S] (ψ : B →ₐ[R] S) (φ : A →ₐ[R] B) (y : sp (R₀ := R) A ⟶ G) :
    spMap (ψ.comp φ) ≫ y = spMap ψ ≫ spMap φ ≫ y := by
  rw [← Category.assoc, spMap_comp]

omit [GrpObj G] in
theorem spc' {A B S : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing S]
    [Algebra R S] (ψ : B →ₐ[R] S) (φ : A →ₐ[R] B) (y : sp (R₀ := R) A ⟶ G) :
    spMap ψ ≫ spMap φ ≫ y = spMap (ψ.comp φ) ≫ y := (spc ψ φ y).symm

theorem tors_pow (T : TorsRep G p) {S : Type} [CommRing S] [Algebra R S] (φ : T.A →ₐ[R] S) :
    (spMap φ ≫ T.y) ^ p = 1 := by
  rw [← MonObj.comp_pow, T.y_p, MonObj.comp_one]

theorem tors_ext (T : TorsRep G p) {S : Type} [CommRing S] [Algebra R S] {φ φ' : T.A →ₐ[R] S}
    (h : spMap φ ≫ T.y = spMap φ' ≫ T.y) : φ = φ' := by
  exact (T.univ S _ (tors_pow T φ)).unique rfl h.symm

theorem lift_comul (T : TorsRep G p) (Δ : T.A →ₐ[R] TensorProduct R T.A T.A)
    (hΔ : spMap Δ ≫ T.y = (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) * (spMap (Algebra.TensorProduct.includeRight : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y))
    {S : Type} [CommRing S] [Algebra R S] (F : TensorProduct R T.A T.A →ₐ[R] S) :
    spMap (F.comp Δ) ≫ T.y = (spMap (F.comp Algebra.TensorProduct.includeLeft) ≫ T.y) *
      (spMap (F.comp Algebra.TensorProduct.includeRight) ≫ T.y) := by
  rw [spc, hΔ, MonObj.comp_mul, spc', spc']

end

theorem tors_alg : ∀ (R : Type) [CommRing R] (p : ℕ), ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ T : TorsRep G p, ∃ (Δ : T.A →ₐ[R] TensorProduct R T.A T.A) (ε : T.A →ₐ[R] R) (s : T.A →ₐ[R] T.A), spMap Δ ≫ T.y = (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) * (spMap (Algebra.TensorProduct.includeRight : T.A →ₐ[R] TensorProduct R T.A T.A) ≫ T.y) ∧ spMap ε ≫ T.y = 1 ∧ (spMap s ≫ T.y) * T.y = 1 ∧ (Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp ((Algebra.TensorProduct.map Δ (AlgHom.id R T.A)).comp Δ) = (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp Δ ∧ (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp Δ = (Algebra.TensorProduct.lid R T.A).symm.toAlgHom ∧ (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp Δ = (Algebra.TensorProduct.rid R R T.A).symm.toAlgHom ∧ (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp Δ = (Algebra.ofId R T.A).comp ε ∧ (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp Δ = Δ := by
  intro R _ p G _ _ T
  set iL : T.A →ₐ[R] TensorProduct R T.A T.A := Algebra.TensorProduct.includeLeft with hiL
  set iR : T.A →ₐ[R] TensorProduct R T.A T.A := Algebra.TensorProduct.includeRight with hiR
  have hz : ((spMap iL ≫ T.y) * (spMap iR ≫ T.y)) ^ p = 1 := by
    rw [mul_pow, tors_pow, tors_pow, _root_.one_mul]
  obtain ⟨Δ, hΔ, -⟩ := T.univ _ _ hz
  obtain ⟨ε, hε, -⟩ := T.univ R (1 : sp (R₀ := R) R ⟶ G) (one_pow p)
  have hz' : (T.y⁻¹) ^ p = 1 := by rw [inv_pow, T.y_p, inv_one]
  obtain ⟨s, hs, -⟩ := T.univ T.A _ hz'
  refine ⟨Δ, ε, s, hΔ, hε, by rw [hs, _root_.inv_mul_cancel], ?_, ?_, ?_, ?_, ?_⟩
  · apply tors_ext T
    rw [← AlgHom.comp_assoc, lift_comul T Δ hΔ, lift_comul T Δ hΔ]
    have e1 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.map Δ (AlgHom.id R T.A))).comp iL = ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp Δ := by
      ext x; simp [hiL]
    have e2 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.map Δ (AlgHom.id R T.A))).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp iR := by
      ext x; simp [hiR, Algebra.TensorProduct.one_def]
    have e3 : (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp iL = (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)) := by
      ext x; simp [hiL]
    have e4 : (Algebra.TensorProduct.map (AlgHom.id R T.A) Δ).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp Δ := by
      ext x; simp [hiR]
    have e5 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp iL = (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)) := by
      ext x; simp [hiL, Algebra.TensorProduct.one_def]
    have e6 : ((Algebra.TensorProduct.assoc R R R T.A T.A T.A).toAlgHom.comp (Algebra.TensorProduct.includeLeft : TensorProduct R T.A T.A →ₐ[R] TensorProduct R (TensorProduct R T.A T.A) T.A)).comp iR = (Algebra.TensorProduct.includeRight : TensorProduct R T.A T.A →ₐ[R] TensorProduct R T.A (TensorProduct R T.A T.A)).comp iL := by
      ext x; simp [hiL, hiR, Algebra.TensorProduct.one_def]
    rw [e1, e2, lift_comul T Δ hΔ, e5, e6, e3, e4, lift_comul T Δ hΔ, _root_.mul_assoc]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp iL = (Algebra.TensorProduct.includeLeft : R →ₐ[R] TensorProduct R R T.A).comp ε := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.map ε (AlgHom.id R T.A)).comp iR = (Algebra.TensorProduct.lid R T.A).symm.toAlgHom := by
      ext x; simp [hiR]
    rw [e1, e2, spc, hε, MonObj.comp_one, _root_.one_mul]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp iL = (Algebra.TensorProduct.rid R R T.A).symm.toAlgHom := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.map (AlgHom.id R T.A) ε).comp iR = (Algebra.TensorProduct.includeRight : R →ₐ[R] TensorProduct R T.A R).comp ε := by
      ext x; simp [hiR]
    rw [e1, e2, spc, hε, MonObj.comp_one, _root_.mul_one]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ]
    have e1 : (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp iL = s := by
      ext x; simp [hiL]
    have e2 : (Algebra.TensorProduct.lift s (AlgHom.id R T.A) (fun _ _ => Commute.all _ _)).comp iR = AlgHom.id R T.A := by
      ext x; simp [hiR]
    rw [e1, e2, spMap_id, Category.id_comp, hs, _root_.inv_mul_cancel, spc, hε, MonObj.comp_one]
  · apply tors_ext T
    rw [lift_comul T Δ hΔ, hΔ]
    have e1 : (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp iL = iR := by
      ext x; simp [hiL, hiR]
    have e2 : (Algebra.TensorProduct.comm R T.A T.A).toAlgHom.comp iR = iL := by
      ext x; simp [hiL, hiR]
    rw [e1, e2, _root_.mul_comm]

end PositivityTheory.HtPt.Rf
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GdSplit
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

private theorem isTorsionFree_of_projective {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]
    [Module.Projective A P] : Module.IsTorsionFree A P := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective A P›
  have hinj : Function.Injective s :=
    Function.LeftInverse.injective (g := Finsupp.linearCombination A id)
      (fun x => LinearMap.congr_fun hs x)
  refine ⟨fun r hr p p' h => hinj ?_⟩
  have h' : r • s p = r • s p' := by
    rw [← map_smul, ← map_smul]
    exact congrArg s h
  ext x
  have hx := congrArg (fun g => g x) h'
  simp only [Finsupp.smul_apply, smul_eq_mul] at hx
  exact hr.left hx

theorem inj_mod_of_surj_mod {A : Type} [CommRing A] [IsDomain A] {P : Type} [AddCommGroup P]
    [Module A P] [Module.Finite A P] [Module.IsTorsionFree A P] {N : ℕ} (a : A)
    (φ : (Fin N → A) →ₗ[A] P) (hN : (N : Cardinal) ≤ Module.rank A P)
    (hs : ∀ y, ∃ x y', y = φ x + a • y') (x : Fin N → A) (y : P) (hx : φ x = a • y) :
    ∃ x', x = a • x' := by
  haveI : Module.IsTorsionFree A (Fin N → A) := isTorsionFree_of_projective
  obtain ⟨r, hr1, hrP⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (I := Ideal.span {a}) (N := LinearMap.range φ) (Module.Finite.fg_top (R := A) (M := P)) le_rfl
    (by
      intro z _
      obtain ⟨x₀, z', rfl⟩ := hs z
      exact Submodule.add_mem_sup (LinearMap.mem_range_self φ x₀)
        (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) Submodule.mem_top))
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr1
  by_cases hr : r = 0
  · refine ⟨-(c • x), ?_⟩
    rw [smul_neg, smul_smul, mul_comm, hc, hr]
    simp
  have hrange : ∀ p : P, r • p ∈ LinearMap.range φ := fun p =>
    hrP (Submodule.smul_mem_pointwise_smul p r ⊤ Submodule.mem_top)
  let f : P →ₗ[A] LinearMap.range φ :=
    LinearMap.codRestrict (LinearMap.range φ) (r • LinearMap.id) (fun p => hrange p)
  have hf : Function.Injective f := by
    intro p p' h
    have h' : r • p = r • p' := congrArg Subtype.val h
    exact smul_right_injective P hr h'
  have hrk : (N : Cardinal) ≤ Module.rank A (LinearMap.range φ) :=
    hN.trans (LinearMap.rank_le_of_injective f hf)
  have hsum := LinearMap.rank_range_add_rank_ker φ
  rw [rank_fin_fun] at hsum
  have hker : Module.rank A (LinearMap.ker φ) = 0 := by
    have hle : Module.rank A (LinearMap.range φ) ≤ N := by
      rw [← hsum]
      exact le_self_add
    rw [le_antisymm hle hrk, add_comm] at hsum
    exact (Cardinal.add_right_inj_of_lt_aleph0 Cardinal.natCast_lt_aleph0).mp (by rw [hsum, zero_add])
  have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp (Submodule.rank_eq_zero.mp hker)
  obtain ⟨z, hz⟩ := hrange y
  have hxz : r • x = a • z :=
    hinj (by rw [map_smul, map_smul, hx, hz, smul_smul, smul_smul, mul_comm])
  refine ⟨z - c • x, ?_⟩
  rw [smul_sub, ← hxz, smul_smul, ← sub_smul, mul_comm a c, hc]
  simp

theorem split_exact : ∀ (A : Type) [CommRing A] [IsDomain A] (P₁ P₂ : Type) [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁] [AddCommGroup P₂] [Module A P₂] [Module.Finite A P₂] [Module.Projective A P₂] (N : ℕ) (a : A) (i : P₁ →ₗ[A] (Fin N → A)) (r : (Fin N → A) →ₗ[A] P₁) (q : (Fin N → A) →ₗ[A] P₂), Module.finrank A P₁ + Module.finrank A P₂ = N → (∀ w, ∃ w', r (i w) = w + a • w') → (∀ y, ∃ x y', y = q x + a • y') → (∀ w, ∃ y, q (i w) = a • y) → ∀ x, (∃ y, q x = a • y) → ∃ w x', x = i w + a • x' := by
  intro A _ _ P₁ P₂ _ _ _ _ _ _ _ _ N a i r q hrank hri hq hqi x hx
  haveI : Module.IsTorsionFree A (P₁ × P₂) := isTorsionFree_of_projective
  have hN : (N : Cardinal) ≤ Module.rank A (P₁ × P₂) := by
    rw [← hrank, Nat.cast_add, Module.finrank_eq_rank, Module.finrank_eq_rank]
    exact rank_add_rank_le_rank_prod A P₁
  have hs : ∀ y : P₁ × P₂, ∃ x y', y = (r.prod q) x + a • y' := by
    rintro ⟨w, y⟩
    obtain ⟨x₀, y₀, rfl⟩ := hq y
    obtain ⟨w', hw'⟩ := hri (w - r x₀)
    obtain ⟨y'', hy''⟩ := hqi (w - r x₀)
    refine ⟨x₀ + i (w - r x₀), (-w', y₀ - y''), Prod.ext ?_ ?_⟩
    · show w = r (x₀ + i (w - r x₀)) + a • -w'
      rw [map_add (f := _), hw', smul_neg]
      abel
    · show q x₀ + a • y₀ = q (x₀ + i (w - r x₀)) + a • (y₀ - y'')
      rw [map_add (f := _), hy'', smul_sub]
      abel
  obtain ⟨w', hw'⟩ := hri (r x)
  obtain ⟨y'', hy''⟩ := hqi (r x)
  obtain ⟨y, hy⟩ := hx
  have hφ : (r.prod q) (x - i (r x)) = a • (-w', y - y'') := by
    refine Prod.ext ?_ ?_
    · show r (x - i (r x)) = a • -w'
      rw [map_sub, hw', smul_neg]
      abel
    · show q (x - i (r x)) = a • (y - y'')
      rw [map_sub, hy, hy'', smul_sub]
  obtain ⟨x', hx'⟩ := PositivityTheory.HtPt.Gd.inj_mod_of_surj_mod a (r.prod q) hN hs _ _ hφ
  refine ⟨r x, x', ?_⟩
  rw [← hx']
  abel

end PositivityTheory.HtPt.Gd
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GcIncl
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

private theorem mem_range_bc_of_entries_mem_intL {A K : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (k : K)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 →
      ∃ s : A, s ∉ q ∧ ∃ c : A, s • k = algebraMap A K c) :
    ∃ c : A, algebraMap A K c = k := by
  have hk : k ∈ Subalgebra.toSubmodule (⊥ : Subalgebra A K) := by
    rw [GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.proof A K]
    refine (Submodule.mem_iInf _).2 fun p => (Submodule.mem_iInf _).2 fun hp => ?_
    obtain ⟨s, hs, c, hc⟩ := h p.asIdeal p.isPrime hp
    refine ⟨s, hs, ?_⟩
    rw [hc, Subalgebra.mem_toSubmodule]
    exact Subalgebra.algebraMap_mem _ c
  rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot] at hk
  obtain ⟨c, hc⟩ := hk
  exact ⟨c, hc⟩

theorem test_incl : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω), M.IsFullLattice K → Module.Projective A M → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ M) → x ∈ M := by
  intro A K _ _ _ _ _ _ _ Ω _ _ _ _ M x hlat hproj hloc
  classical
  have hden : ∀ w ∈ Submodule.span K (M : Set Ω), ∃ d ∈ nonZeroDivisors A, d • w ∈ M := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact ⟨1, one_mem _, by rw [one_smul]; exact hw⟩
    | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact M.zero_mem⟩
    | add u w _ _ hu hw =>
      obtain ⟨d1, hd1, h1⟩ := hu
      obtain ⟨d2, hd2, h2⟩ := hw
      refine ⟨d1 * d2, mul_mem hd1 hd2, ?_⟩
      have e1 : (d1 * d2) • u = d2 • (d1 • u) := by rw [mul_comm, mul_smul]
      have e2 : (d1 * d2) • w = d1 • (d2 • w) := by rw [mul_smul]
      rw [smul_add, e1, e2]
      exact M.add_mem (M.smul_mem _ h1) (M.smul_mem _ h2)
    | smul k w _ hw =>
      obtain ⟨d, hd, h1⟩ := hw
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) k
      refine ⟨b * d, mul_mem hb hd, ?_⟩
      have hb0 : algebraMap A K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
      have e : (b * d) • ((algebraMap A K a / algebraMap A K b) • w) = a • (d • w) := by
        rw [← algebraMap_smul K (b * d), smul_smul, smul_smul a d w, ← algebraMap_smul K (a * d) w]
        congr 1
        rw [map_mul, map_mul]
        field_simp
      rw [e]
      exact M.smul_mem a h1
  letI := hlat
  obtain ⟨d, hd, hdx⟩ := hden x (by rw [Submodule.IsFullLattice.span_eq_top]; trivial)
  have hd0' : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  obtain ⟨σ, hσ⟩ := hproj.out
  set z : M := ⟨d • x, hdx⟩ with hzdef
  have hdiv : ∀ m : M, ∃ c : A, σ z m = d * c := by
    intro m
    have hl : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧
        ∃ c : A, s • (algebraMap A K (σ z m) / algebraMap A K d) = algebraMap A K c := by
      intro q hq hh
      obtain ⟨s, hs, hsx⟩ := hloc q hq hh
      refine ⟨s, hs, σ ⟨s • x, hsx⟩ m, ?_⟩
      have hz : s • z = d • (⟨s • x, hsx⟩ : M) := Subtype.ext (smul_comm s d x)
      have hm : s * σ z m = d * σ ⟨s • x, hsx⟩ m := by
        have h' := congrArg (fun f => f m) (congrArg σ hz)
        simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h'
      rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, hm, map_mul]
      field_simp
    obtain ⟨c, hc⟩ := mem_range_bc_of_entries_mem_intL (K := K) _ hl
    refine ⟨c, IsFractionRing.injective A K ?_⟩
    rw [map_mul, hc]
    field_simp
  choose c hc using hdiv
  have hyM : (∑ m ∈ (σ z).support, c m • (m : Ω)) ∈ M :=
    M.sum_mem (fun m _ => M.smul_mem _ m.2)
  have hsum : (∑ m ∈ (σ z).support, (σ z m) • (m : Ω)) = (z : Ω) := by
    have h1 := congrArg Subtype.val (hσ z)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum] at h1
    simpa using h1
  have hzy : d • (∑ m ∈ (σ z).support, c m • (m : Ω)) = d • x := by
    rw [Finset.smul_sum]
    refine Eq.trans (Finset.sum_congr rfl fun m _ => ?_) hsum
    rw [hc m, mul_smul]
  have hcancel : ∀ u w : Ω, d • u = d • w → u = w := by
    intro u w huw
    have h1 : (algebraMap A K d) • u = (algebraMap A K d) • w := by
      rw [algebraMap_smul, algebraMap_smul]
      exact huw
    have h2 : (algebraMap A K d)⁻¹ • ((algebraMap A K d) • u) =
        (algebraMap A K d)⁻¹ • ((algebraMap A K d) • w) := by rw [h1]
    rw [smul_smul, smul_smul, inv_mul_cancel₀ hd0', one_smul, one_smul] at h2
    exact h2
  rw [← hcancel _ _ hzy]
  exact hyM

theorem dvd_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {a t : A} (ha : a ≠ 0)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧ a ∣ s * t) : a ∣ t := by
  classical
  have ha' : algebraMap A (FractionRing A) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).mpr ha
  have hl : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧
      ∃ c : A, s • (algebraMap A (FractionRing A) t / algebraMap A (FractionRing A) a) =
        algebraMap A (FractionRing A) c := by
    intro q hq hh
    obtain ⟨s, hs, u, hu⟩ := h q hq hh
    refine ⟨s, hs, u, ?_⟩
    rw [Algebra.smul_def, ← mul_div_assoc, ← map_mul, hu, map_mul]
    field_simp
  obtain ⟨c, hc⟩ := mem_range_bc_of_entries_mem_intL (K := FractionRing A) _ hl
  refine ⟨c, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, hc]
  field_simp

theorem smul_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {M : Type} [AddCommGroup M] [Module A M] [Module.Projective A M]
    {a : A} (ha : a ≠ 0) (x : M)
    (h : ∀ q : Ideal A, q.IsPrime → q.height = 1 → ∃ s : A, s ∉ q ∧ ∃ y : M, s • x = a • y) :
    ∃ y : M, x = a • y := by
  classical
  obtain ⟨σ, hσ⟩ := ‹Module.Projective A M›.out
  have hdiv : ∀ m : M, a ∣ σ x m := by
    intro m
    refine dvd_of_height_one ha (fun q hq hh => ?_)
    obtain ⟨s, hs, y, hy⟩ := h q hq hh
    refine ⟨s, hs, σ y m, ?_⟩
    have h' := congrArg (fun f => f m) (congrArg σ hy)
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h'
  choose c hc using hdiv
  refine ⟨∑ m ∈ (σ x).support, c m • m, ?_⟩
  conv_lhs => rw [← hσ x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [hc m, mul_smul, id_eq]

theorem test_div : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (M : Submodule A Ω) (x : Ω) (a b : A), M.FG → Module.Projective A M → x ∈ M → a ≠ 0 → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → a ∈ 𝔮 → b ∈ 𝔮) → (∀ 𝔮 : Ideal A, 𝔮.IsPrime → 𝔮.height = 1 → b ∈ 𝔮 → ∃ s : A, s ∉ 𝔮 ∧ ∃ y ∈ M, s • x = a • y) → ∃ y ∈ M, x = a • y := by
  intro A K _ _ _ _ _ _ _ Ω _ _ _ _ M x a b _ hproj hx ha hab hloc
  have hloc' : ∀ q : Ideal A, q.IsPrime → q.height = 1 →
      ∃ s : A, s ∉ q ∧ ∃ y : M, s • (⟨x, hx⟩ : M) = a • y := by
    intro q hq hh
    by_cases hb : b ∈ q
    · obtain ⟨s, hs, y, hy, hsy⟩ := hloc q hq hh hb
      exact ⟨s, hs, ⟨y, hy⟩, Subtype.ext hsy⟩
    · exact ⟨a, fun haq => hb (hab q hq haq), ⟨x, hx⟩, rfl⟩
  obtain ⟨y, hy⟩ := smul_of_height_one ha (⟨x, hx⟩ : M) hloc'
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

end PositivityTheory.HtPt.Gc
end
