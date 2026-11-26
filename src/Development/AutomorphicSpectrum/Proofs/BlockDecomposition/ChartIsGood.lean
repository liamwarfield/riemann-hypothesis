module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleLiftingOfNilIdeal
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechDifferentialOneInclusion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TerminalRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEtaleLiftOfSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDpOfCompOnGens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates

@[expose] public section

local instance (priority := high) : IsEmpty Empty := ⟨Empty.elim⟩

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartMaps

variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem nil_J (T : Thick (nlFun γ p X q κ)) : ∀ x ∈ T.J, IsNilpotent x := by
  intro x hx
  by_cases hp : p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have h : x ^ n ∈ T.J ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at h
    exact h
  · obtain ⟨n, hn⟩ : IsNilpotent ((p : ℕ) : T.B) := T.adm.1 hp
    refine ⟨p * n, ?_⟩
    have h1 : x ^ p = (p.factorial : T.B) * T.δ.dpow p x := (T.δ.factorial_mul_dpow_eq_pow hx).symm
    have h2 : (p.factorial : T.B) = (p : T.B) * ((p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, h1, h2, mul_assoc, mul_pow, hn, zero_mul]

theorem isDP {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (T : Thick (nlFun γ p X q κ))
    (f : c.D.B →+* T.B) (hf : ∀ r, f (c.D.i r) = T.i r) : IsDPMorphism c.D.δ T.δ f := by
  have e : f.comp c.D.i = T.i := RingHom.ext hf
  refine IsDPMorphism.of_comp γ c.D.δ T.δ c.D.i f c.J_eq c.D.compat ?_
  rw [e]
  exact T.compat

theorem exists_unique_lift {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d)
    (T : Thick (nlFun γ p X q κ)) (g : c.D.B ⧸ c.D.J →+* T.B ⧸ T.J)
    (hg : ∀ r, g (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (T.i r))
    (y : Fin d → T.B) (hy : ∀ k, Ideal.Quotient.mk T.J (y k) = g (Ideal.Quotient.mk _ (c.t k))) :
    ∃! f : c.D.B →+* T.B, (∀ r, f (c.D.i r) = T.i r) ∧ (∀ k, f (c.t k) = y k) ∧
      (Ideal.Quotient.mk T.J).comp f = g.comp (Ideal.Quotient.mk c.D.J) := by
  have hL := GlobalTheory.T.etale_lifting_of_nil_ideal T.J (nil_J T)
  have hc : (g.comp (Ideal.Quotient.mk c.D.J)).comp
      (MvPolynomial.eval₂Hom c.D.i c.t : MvPolynomial (Fin d) R →+* c.D.B) =
      (Ideal.Quotient.mk T.J).comp (MvPolynomial.eval₂Hom T.i y : MvPolynomial (Fin d) R →+* T.B) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · simpa using hg r
    · simpa using (hy k).symm
  obtain ⟨f, ⟨h1, h2⟩, hu⟩ := hL (MvPolynomial (Fin d) R) c.D.B _ c.etale
    (MvPolynomial.eval₂Hom T.i y) (g.comp (Ideal.Quotient.mk c.D.J)) hc
  refine ⟨f, ⟨fun r => ?_, fun k => ?_, h2⟩, ?_⟩
  · simpa using RingHom.congr_fun h1 (MvPolynomial.C r)
  · simpa using RingHom.congr_fun h1 (MvPolynomial.X k)
  · rintro f' ⟨a1, a2, a3⟩
    refine hu f' ⟨MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_), a3⟩
    · simpa using a1 r
    · simpa using a2 k

theorem inU_of_hom {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) {T : Thick (nlFun γ p X q κ)}
    (σ : c.D ⟶ T) : InU V T := by
  have e : pt T = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle)) ≫ pt c.D := by
    unfold pt
    rw [← σ.pt]
    rfl
  unfold InU
  rw [e]
  intro x _
  exact c.inV (show (Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle))) x ∈ ⊤ from trivial)

theorem quot_comm {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (T : Thick (nlFun γ p X q κ))
    (g : c.D.B ⧸ c.D.J →+* T.B ⧸ T.J)
    (hg : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y) (r : R) :
    g (Ideal.Quotient.mk _ (c.D.i r)) = Ideal.Quotient.mk _ (T.i r) := by
  have e := congrArg (fun z : PtOver X q κ (T.B ⧸ T.J) => z.1.1 (Ideal.Quotient.mk _ r)) hg
  have w1 := c.D.w r
  have w2 := T.w r
  calc g (Ideal.Quotient.mk _ (c.D.i r))
      = g ((nlFun γ p X q κ).str c.D.y (Ideal.Quotient.mk _ r)) := by rw [w1]
    _ = (nlFun γ p X q κ).str T.y (Ideal.Quotient.mk _ r) := e
    _ = Ideal.Quotient.mk _ (T.i r) := w2

def homOf {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) (T : Thick (nlFun γ p X q κ))
    (f : c.D.B →+* T.B) (hf : ∀ r, f (c.D.i r) = T.i r) (g : c.D.B ⧸ c.D.J →+* T.B ⧸ T.J)
    (hq : (Ideal.Quotient.mk T.J).comp f = g.comp (Ideal.Quotient.mk c.D.J))
    (hg : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y) : c.D ⟶ T :=
  have hdp := isDP c T f hf
  have hle : c.D.J ≤ T.J.comap f := fun _ hx => hdp.1 (Ideal.mem_map_of_mem f hx)
  mkH f hf hdp hle (by
    have e : Ideal.quotientMap T.J f hle = g :=
      Ideal.Quotient.ringHom_ext (RingHom.ext fun x => RingHom.congr_fun hq x)
    rw [e]
    exact hg)

theorem good {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d) : c.Good := by
  refine ⟨fun T hT => ?_, fun T σ y hy => ?_⟩
  · obtain ⟨g, hg, -⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y hT
    have hg' : (nlFun γ p X q κ).Pt.map (CommRingCat.ofHom g) c.D.y = T.y := hg
    choose y hy using fun k => Ideal.Quotient.mk_surjective (g (Ideal.Quotient.mk _ (c.t k)))
    obtain ⟨f, ⟨h1, -, h3⟩, -⟩ := exists_unique_lift c T g (quot_comm c T g hg') y hy
    exact ⟨homOf c T f h1 g h3 hg'⟩
  · have hg : (nlFun γ p X q κ).Pt.map
        (CommRingCat.ofHom (Ideal.quotientMap T.J σ.φ σ.hle)) c.D.y = T.y := σ.pt
    have hs : ∀ k, Ideal.Quotient.mk T.J (σ.φ (c.t k) + y k) =
        Ideal.quotientMap T.J σ.φ σ.hle (Ideal.Quotient.mk _ (c.t k)) := fun k => by
      rw [Ideal.quotientMap_mk, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 (hy k), add_zero]
    obtain ⟨f, ⟨h1, h2, h3⟩, hu⟩ := exists_unique_lift c T (Ideal.quotientMap T.J σ.φ σ.hle)
      (quot_comm c T _ hg) (fun k => σ.φ (c.t k) + y k) hs
    refine ⟨homOf c T f h1 _ h3 hg, fun i => ?_, fun τ hτ => hom_ext ?_⟩
    · change f (c.t i) - σ.φ (c.t i) = y i
      rw [h2 i]
      ring
    · obtain ⟨g₀, -, hu₀⟩ := c.rep (CommRingCat.of (T.B ⧸ T.J)) T.y (inU_of_hom c σ)
      have e : Ideal.quotientMap T.J τ.φ τ.hle = Ideal.quotientMap T.J σ.φ σ.hle :=
        (hu₀ _ τ.pt).trans (hu₀ _ σ.pt).symm
      refine hu τ.φ ⟨τ.comm, fun k => ?_, ?_⟩
      · have := hτ k
        rw [← this]
        ring
      · rw [← e]
        rfl

end GlobalTheory.CompanionTheory.ChartMaps
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_is_good : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d), c.Good := by
  first | exact @GlobalTheory.CompanionTheory.ChartMaps.good | exact GlobalTheory.CompanionTheory.ChartMaps.good | (intros; apply GlobalTheory.CompanionTheory.ChartMaps.good <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfEtalePoly
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FlatChartP

open GlobalTheory.CompanionTheory.ChartAlg

theorem flat_of_etale_poly {R D : Type} [CommRing R] [CommRing D] (i : R →+* D) {d : ℕ} (t : Fin d → D)
    (h : (MvPolynomial.eval₂Hom i t : MvPolynomial (Fin d) R →+* D).Etale) : i.Flat := by
  have h1 : (MvPolynomial.eval₂Hom i t : MvPolynomial (Fin d) R →+* D).Flat :=
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp h).1
  have h2 : (algebraMap R (MvPolynomial (Fin d) R)).Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  have e : i = (MvPolynomial.eval₂Hom i t).comp (algebraMap R (MvPolynomial (Fin d) R)) := by
    ext x
    simp [MvPolynomial.algebraMap_eq]
  rw [e]
  exact RingHom.Flat.comp h2 h1

theorem rep_lift {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (hV : IsAffineOpen V)
    {T : Fin d → Γ(X, V)} (L : CrystallineSemistableComparison.B.Lift (strV q V) T R I κ) (y : PtOver X q κ (L.D ⧸ I.map L.i))
    (h1 : ∀ r, y.1.1 (Ideal.Quotient.mk I r) = Ideal.Quotient.mk _ (L.i r))
    (h2 : y.1.2 = Spec.map (CommRingCat.ofHom L.j) ≫ hV.fromSpec)
    (B : CommRingCat.{0}) (y' : PtOver X q κ B) (hy' : ⊤ ≤ y'.1.2 ⁻¹ᵁ V) :
    ∃! φ : L.D ⧸ I.map L.i →+* B, (ptFun X q κ).map (CommRingCat.ofHom φ) y = y' := by
  let e' : Γ(X, V) →+* B := GlobalTheory.Cris.evalAt y'.1.2 V hy'
  let ψ' : R ⧸ I →+* B := y'.1.1
  have hcomp : ∀ o x, Ideal.Quotient.mk I x = κ o → e' (strV q V o) = (ψ'.comp (Ideal.Quotient.mk I)) x := by
    intro o x hx
    rw [RingHom.comp_apply, hx]
    exact evalAt_base q κ ψ' y'.1.2 y'.2 hy' o
  have hkill : ∀ x ∈ I, (ψ'.comp (Ideal.Quotient.mk I)) x = 0 := fun x hx => by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  obtain ⟨f, ⟨hf1, hf2⟩, hu⟩ := L.univ B (ψ'.comp (Ideal.Quotient.mk I)) e' hkill hcomp
  have hJ : ∀ a ∈ I.map L.i, f a = 0 := by
    have : I.map L.i ≤ RingHom.ker f := by
      refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hf1]
      exact hkill x hx
    exact fun a ha => this ha
  let φ : L.D ⧸ I.map L.i →+* B := Ideal.Quotient.lift _ f hJ
  have hφj : φ.comp L.j = e' := by
    refine RingHom.ext fun r => ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (L.j r)
    rw [RingHom.comp_apply, ← hz, Ideal.Quotient.lift_mk]
    exact hf2 r z hz
  refine ⟨φ, ?_, fun φ₂ h => ?_⟩
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · refine RingHom.ext fun z => ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      change φ (y.1.1 (Ideal.Quotient.mk I r)) = ψ' (Ideal.Quotient.mk I r)
      rw [h1, Ideal.Quotient.lift_mk]
      exact RingHom.congr_fun hf1 r
    · change Spec.map (CommRingCat.ofHom φ) ≫ y.1.2 = y'.1.2
      rw [h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφj]
      exact eq_specMap hV _ hy'
  · have a : φ₂.comp y.1.1 = ψ' := congrArg (fun z => z.1.1) h
    have b : Spec.map (CommRingCat.ofHom φ₂) ≫ y.1.2 = y'.1.2 := congrArg (fun z => z.1.2) h
    have e : e' = φ₂.comp L.j := by
      refine evalAt_specMap hV (φ₂.comp L.j) y'.1.2 ?_ hy'
      rw [← b, h2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hf : φ₂.comp (Ideal.Quotient.mk _) = f := by
      refine hu _ ⟨?_, fun r z hz => ?_⟩
      · refine RingHom.ext fun r => ?_
        rw [← a, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, h1]
      · rw [RingHom.comp_apply, hz, e]
        rfl
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    rw [hf]
    exact (Ideal.Quotient.lift_mk _ f hJ).symm

theorem exists_flat_chart : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} (γ : DividedPowers I) (p : ℕ) (hp : p ≠ 0)
    (hn : IsNilpotent (p : R)) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (κ : O →+* R ⧸ I) {V : X.Opens} {d : ℕ}
    (c : Coord q V d), ∃ c' : Chart γ p q κ V d, FlatT c'.D ∧ ∀ i, ev c'.D c'.inV (c.t i) = Ideal.Quotient.mk _ (c'.t i) := by
  intro O R _ _ I γ p hp hn X q κ V d c
  obtain ⟨L⟩ := GlobalTheory.CompanionTheory.EtaleLift.nonempty_lift (strV q V) c.t I κ c.etale
  have hF : L.i.Flat := flat_of_etale_poly L.i L.t L.et
  obtain ⟨δ, hδ⟩ : ∃ δ : DividedPowers (I.map L.i), IsDPMorphism γ δ L.i := by
    letI : Algebra R L.D := L.i.toAlgebra
    haveI : Module.Flat R L.D := hF
    exact GlobalTheory.CompanionTheory.JLiftDP.dpFlat R L.D I γ
  let ψ : R ⧸ I →+* L.D ⧸ I.map L.i := Ideal.quotientMap _ L.i Ideal.le_comap_map
  have hψ : ∀ r, ψ (Ideal.Quotient.mk I r) = Ideal.Quotient.mk _ (L.i r) := fun r => rfl
  have hκ : L.j.comp (strV q V) = ψ.comp κ := by
    refine RingHom.ext fun o => ?_
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (κ o)
    rw [RingHom.comp_apply, RingHom.comp_apply, L.hj o x hx, ← hx, hψ]
  let y : PtOver X q κ (L.D ⧸ I.map L.i) :=
    ⟨(ψ, Spec.map (CommRingCat.ofHom L.j) ≫ c.affine.fromSpec), by
      change (Spec.map (CommRingCat.ofHom L.j) ≫ c.affine.fromSpec) ≫ q = _
      rw [Category.assoc, fromSpec_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hκ]⟩
  let T : Thick (nlFun γ p X q κ) := mkT L.D L.i (I.map L.i) δ
    ⟨fun _ => by simpa using hn.map L.i, fun h => absurd h hp⟩ hδ y hψ
  have hin : InU V T := top_le_specMap c.affine L.j
  refine ⟨⟨T, L.t, L.et, rfl, hin, fun B y' hy' => rep_lift c.affine L y hψ rfl B y' hy'⟩, hF, fun i => ?_⟩
  have e : ev T hin = L.j := evalAt_specMap c.affine L.j _ rfl hin
  change ev T hin (c.t i) = _
  rw [e]
  exact L.hT i

end GlobalTheory.CompanionTheory.FlatChartP
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemSpanOfEtale
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.LiftFlat

theorem flat_of_eval₂Hom_etale {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ}
    (t : Fin d → D) (het : (MvPolynomial.eval₂Hom i t).Etale) : i.Flat := by
  have h1 : (MvPolynomial.eval₂Hom i t).Flat := by
    letI := (MvPolynomial.eval₂Hom i t).toAlgebra
    haveI : Algebra.Etale (MvPolynomial (Fin d) Λ) D := het
    exact Algebra.Smooth.flat (MvPolynomial (Fin d) Λ) D
  have h2 : (MvPolynomial.C : Λ →+* MvPolynomial (Fin d) Λ).Flat := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  have h3 := RingHom.Flat.comp h2 h1
  rwa [MvPolynomial.eval₂Hom_comp_C] at h3

theorem sub_mem_span_of_etale {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ}
    (t : Fin d → D) (het : (MvPolynomial.eval₂Hom i t).Etale) (J : Ideal D) (μ : D) (g : D →+* D)
    (hJ : ∀ x ∈ J, IsNilpotent x) (hgi : g.comp i = i)
    (hgt : ∀ k, g (t k) - t k ∈ Ideal.span {μ}) (hgJ : ∀ z, g z - z ∈ J) (z : D) :
    g z - z ∈ Ideal.span {μ} := by
  classical
  letI : Algebra (MvPolynomial (Fin d) Λ) D := (MvPolynomial.eval₂Hom i t).toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) Λ) D := het
  let q : D →+* D ⧸ Ideal.span ({μ} : Set D) := Ideal.Quotient.mk _
  have hcomm : (q.comp g).comp (MvPolynomial.eval₂Hom i t) = q.comp (MvPolynomial.eval₂Hom i t) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      rw [← RingHom.comp_apply g i, hgi]
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      exact Ideal.Quotient.eq.mpr (hgt k)
  let φ₁ : D →ₐ[MvPolynomial (Fin d) Λ] D ⧸ Ideal.span ({μ} : Set D) := Ideal.Quotient.mkₐ _ _
  let φ₂ : D →ₐ[MvPolynomial (Fin d) Λ] D ⧸ Ideal.span ({μ} : Set D) :=
    { (q.comp g) with
      commutes' := fun a => by
        change q (g (algebraMap _ D a)) = q (algebraMap _ D a)
        exact RingHom.congr_fun hcomm a }
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra (MvPolynomial (Fin d) Λ) D).FG)
  let I : Ideal (D ⧸ Ideal.span ({μ} : Set D)) :=
    Ideal.span ((fun s => q (g s - s)) '' (S : Set D))
  have hfg : I.FG := Submodule.fg_span (S.finite_toSet.image _)
  have hnil : IsNilpotent I := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical hfg]
    rw [Ideal.span_le]
    rintro _ ⟨s, -, rfl⟩
    exact mem_nilradical.mpr ((hJ _ (hgJ s)).map q)
  have hψ : (Ideal.Quotient.mkₐ (MvPolynomial (Fin d) Λ) I).comp φ₁ =
      (Ideal.Quotient.mkₐ (MvPolynomial (Fin d) Λ) I).comp φ₂ := by
    apply AlgHom.ext_of_adjoin_eq_top hS
    intro s hs
    have hmem : q (g s - s) ∈ I := Ideal.subset_span ⟨s, hs, rfl⟩
    rw [map_sub] at hmem
    show Ideal.Quotient.mk I (q s) = Ideal.Quotient.mk I (q (g s))
    exact (Ideal.Quotient.eq.mpr hmem).symm
  have hφ : φ₁ = φ₂ := by
    apply Algebra.FormallyUnramified.ext I hnil
    intro x
    exact congrArg (fun ψ : D →ₐ[MvPolynomial (Fin d) Λ] _ => ψ x) hψ
  have hz : q z = q (g z) := congrArg (fun ψ : D →ₐ[MvPolynomial (Fin d) Λ] _ => ψ z) hφ
  exact Ideal.Quotient.eq.mp hz.symm

theorem lift_flat : ∀ {Λ D : Type} [CommRing Λ] [CommRing D] (i : Λ →+* D) {d : ℕ} (t : Fin d → D), (MvPolynomial.eval₂Hom i t).Etale → i.Flat ∧ ∀ (J : Ideal D) (μ : D) (g : D →+* D), (∀ x ∈ J, IsNilpotent x) → g.comp i = i → (∀ k, g (t k) - t k ∈ Ideal.span {μ}) → (∀ z, g z - z ∈ J) → ∀ z, g z - z ∈ Ideal.span {μ} := by
  intro Λ D _ _ i d t het
  exact ⟨flat_of_eval₂Hom_etale i t het, fun J μ g hJ hgi hgt hgJ z =>
    sub_mem_span_of_etale i t het J μ g hJ hgi hgt hgJ z⟩

end GlobalTheory.CompanionTheory.LiftFlat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineSiteZariskiCoveredByAtlas
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickZar

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}

theorem isNilpotent_of_mem_J (hp : b.p ≠ 0) {L : b.Fun} (T : Thick L) {x : T.B} (hx : x ∈ T.J) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := T.adm.1 hp
  obtain ⟨c, hc⟩ : b.p ∣ b.p.factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero hp) le_rfl
  refine ⟨b.p * N, ?_⟩
  rw [pow_mul, ← T.δ.factorial_mul_dpow_eq_pow hx, hc, Nat.cast_mul, mul_assoc, mul_pow, hN, zero_mul]

def push (T : Thick (F.cr b ht κ)) {B' : Type} [CommRing B'] (g : T.B →+* B') (δ' : DividedPowers (T.J.map g))
    (hg : IsDPMorphism T.δ δ' g) : Thick (F.cr b ht κ) where
  B := B'
  i := g.comp T.i
  J := T.J.map g
  δ := δ'
  adm := ⟨fun h => by simpa using (T.adm.1 h).map g, fun h => by
    obtain ⟨n, hn⟩ := T.adm.2 h
    exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]⟩⟩
  compat := IsDPMorphism.comp δ' hg T.compat
  α := ()
  y := (F.cr b ht κ).Pt.map (CommRingCat.ofHom (Ideal.quotientMap (T.J.map g) g Ideal.le_comap_map)) T.y
  inα := trivial
  w r := by
    rw [(F.cr b ht κ).str_map]
    change (Ideal.quotientMap (T.J.map g) g Ideal.le_comap_map) ((F.cr b ht κ).str T.y (Ideal.Quotient.mk _ r)) = _
    rw [T.w]; rfl
  x j := j.elim
  v j := j.elim
  s := Units.map g.toMonoidHom T.s
  hx j := j.elim
  hs := by
    haveI : IsEmpty Empty := ⟨Empty.elim⟩
    have h := congrArg g T.hs
    have e : ∏ j, T.x j = 1 := Finset.prod_of_isEmpty (ι := Empty) _
    rw [e, map_one, map_mul] at h
    exact (Finset.prod_of_isEmpty (ι := Empty) _).trans h
  hv := by
    haveI : IsEmpty Empty := ⟨Empty.elim⟩
    have h := T.hv
    have e : ∏ j, T.v j = 1 := Finset.prod_of_isEmpty (ι := Empty) _
    rw [e] at h
    refine Eq.trans ?_ (Finset.prod_of_isEmpty (ι := Empty) _).symm
    ext
    have h' := congrArg (fun u : (T.B ⧸ T.J)ˣ => Ideal.quotientMap (T.J.map g) g Ideal.le_comap_map (u : T.B ⧸ T.J)) h
    simpa using h'

def pushHom (T : Thick (F.cr b ht κ)) {B' : Type} [CommRing B'] (g : T.B →+* B') (δ' : DividedPowers (T.J.map g))
    (hg : IsDPMorphism T.δ δ' g) : T ⟶ push T g δ' hg where
  φ := g
  u j := j.elim
  comm _ := rfl
  dp := hg
  hle := Ideal.le_comap_map
  pt := rfl
  hx j := j.elim
  hs := by
    have e : ∏ j : (F.cr b ht κ).ι, ((j.elim : (push T g δ' hg).Bˣ)) = 1 := Finset.prod_of_isEmpty (ι := Empty) _
    rw [e, one_mul]; rfl
  hv j := j.elim

def pushDesc (T : Thick (F.cr b ht κ)) {B' : Type} [CommRing B'] (g : T.B →+* B') (δ' : DividedPowers (T.J.map g))
    (hg : IsDPMorphism T.δ δ' g) {T'' : Thick (F.cr b ht κ)} (ψ : T ⟶ T'') (χ : B' →+* T''.B) (h : χ.comp g = ψ.φ) :
    push T g δ' hg ⟶ T'' :=
  have hdp : IsDPMorphism δ' T''.δ χ := (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers T.δ g δ' hg).2 T''.δ χ (h ▸ ψ.dp)
  have hle : T.J.map g ≤ T''.J.comap χ := Ideal.map_le_iff_le_comap.1 hdp.1
  have e2 : CommRingCat.ofHom (Ideal.quotientMap (T.J.map g) g Ideal.le_comap_map) ≫
      CommRingCat.ofHom (Ideal.quotientMap T''.J χ hle) = CommRingCat.ofHom (Ideal.quotientMap T''.J ψ.φ ψ.hle) := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (χ (g x)) = Ideal.Quotient.mk _ (ψ.φ x)
    rw [← RingHom.comp_apply χ g, h]
  { φ := χ
    u := fun j => j.elim
    comm := fun r => by
      change χ (g (T.i r)) = _
      rw [← RingHom.comp_apply χ g, h]; exact ψ.comm r
    dp := hdp
    hle := hle
    pt := by
      refine Eq.trans ?_ ψ.pt
      change (F.cr b ht κ).Pt.map _ ((F.cr b ht κ).Pt.map _ T.y) = (F.cr b ht κ).Pt.map _ T.y
      rw [← e2, Functor.map_comp]
      rfl
    hx := fun j => j.elim
    hs := by
      have e : ∏ j : (F.cr b ht κ).ι, ((j.elim : T''.Bˣ)) = 1 := Finset.prod_of_isEmpty (ι := Empty) _
      rw [e, one_mul, ψ.hs]
      have e' : ∏ j, ψ.u j = 1 := Finset.prod_of_isEmpty (ι := Empty) _
      rw [e', one_mul]
      ext
      change ψ.φ _ = χ (g _)
      rw [← RingHom.comp_apply χ g, h]
    hv := fun j => j.elim }

theorem hom_ext_cr {T T' : Thick (F.cr b ht κ)} {f g : T ⟶ T'} (h : f.φ = g.φ) : f = g :=
  Thick.Hom.ext h (funext fun j => j.elim)

def locT (T : Thick (F.cr b ht κ)) (a : T.B) : Thick (F.cr b ht κ) :=
  push T (algebraMap T.B (Localization.Away a))
    (Classical.choose (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))
    (Classical.choose_spec (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))

def locHom (T : Thick (F.cr b ht κ)) (a : T.B) : T ⟶ locT T a :=
  pushHom T (algebraMap T.B (Localization.Away a))
    (Classical.choose (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))
    (Classical.choose_spec (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))

theorem locT_univ (T : Thick (F.cr b ht κ)) (a : T.B) {T'' : Thick (F.cr b ht κ)} (ψ : T ⟶ T'')
    (hu : IsUnit (ψ.φ a)) : ∃! χ : locT T a ⟶ T'', locHom T a ≫ χ = ψ := by
  let l : Localization.Away a →+* T''.B := IsLocalization.Away.lift a hu
  have hl : l.comp (algebraMap T.B (Localization.Away a)) = ψ.φ := IsLocalization.Away.lift_comp a hu
  refine ⟨pushDesc T _ _ _ ψ l hl, hom_ext_cr hl, fun χ hχ => hom_ext_cr ?_⟩
  let χ' : Localization.Away a →+* T''.B := χ.φ
  have h1 : χ'.comp (algebraMap T.B (Localization.Away a)) = ψ.φ := congrArg Thick.Hom.φ hχ
  have h2 : χ' = l := IsLocalization.ringHom_ext (Submonoid.powers a) (h1.trans hl.symm)
  exact h2

theorem unit_of_mem (T : Thick (F.cr b ht κ)) {m : ℕ} (f : Fin m → T.B) (S : Finset (Fin m)) {k : Fin m} (hk : k ∈ S) :
    IsUnit ((locHom T (∏ k ∈ S, f k)).φ (f k)) := by
  have h : IsUnit (algebraMap T.B (Localization.Away (∏ k ∈ S, f k)) (∏ k ∈ S, f k)) :=
    IsLocalization.Away.algebraMap_isUnit _
  exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem f hk)) h

theorem pdPow_locT (T : Thick (F.cr b ht κ)) (a : T.B) (r : ℕ) :
    (locT T a).pdPow r = (T.pdPow r).map (algebraMap T.B (Localization.Away a)) :=
  (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers T.δ (algebraMap T.B (Localization.Away a)) _
    (Classical.choose_spec (GlobalTheory.CompanionTheory.JLiftDP.dpFlat T.B (Localization.Away a) T.J T.δ))).1 r

theorem loc_surj (T : Thick (F.cr b ht κ)) (a : T.B) (r : ℕ) (y : Localization.Away a)
    (hy : y ∈ (T.pdPow r).map (algebraMap T.B (Localization.Away a))) :
    ∃ (n : ℕ) (x : T.B), x ∈ T.pdPow r ∧
      algebraMap T.B (Localization.Away a) (a ^ n) * y = algebraMap T.B (Localization.Away a) x := by
  obtain ⟨⟨x, s⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers a) _).1 hy
  obtain ⟨n, hn⟩ := s.2
  refine ⟨n, x.1, x.2, ?_⟩
  have hn' : a ^ n = s := hn
  rw [mul_comm, hn']
  exact hx

theorem span_lift (hp : b.p ≠ 0) (T : Thick (F.cr b ht κ)) {m : ℕ} (f : Fin m → T.B) (s : Fin m → T.B ⧸ T.J)
    (hf : ∀ k, Ideal.Quotient.mk T.J (f k) = s k) (hs : Ideal.span (Set.range s) = ⊤) :
    Ideal.span (Set.range f) = ⊤ := by
  have h1 : Ideal.map (Ideal.Quotient.mk T.J) (Ideal.span (Set.range f)) = ⊤ := by
    rw [Ideal.map_span, ← Set.range_comp, ← hs]
    congr 2
    exact funext hf
  have h2 : (1 : T.B ⧸ T.J) ∈ Ideal.map (Ideal.Quotient.mk T.J) (Ideal.span (Set.range f)) := by
    rw [h1]; trivial
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h2
  have hj : a - 1 ∈ T.J := Ideal.Quotient.eq.1 (by rw [ha1, map_one])
  have hu : IsUnit a := by
    have := (isNilpotent_of_mem_J hp T hj).isUnit_add_one
    simpa using this
  exact Ideal.eq_top_of_isUnit_mem _ ha hu

section Mod

variable {Λ : Type} [CommRing Λ] (c : Λ →+* b.R) (r : ℕ)

def mulR (T : Thick (F.cr b ht κ)) : T.B →+* Module.End Λ ((pdS (F.cr b ht κ) c r).fn.obj T) where
  toFun a :=
    { toFun := fun x => ⟨(show T.B from a * (show T.B from x.1)), (T.pdPow r).mul_mem_left a x.2⟩
      map_add' := fun x y => Subtype.ext (mul_add a (show T.B from x.1) (show T.B from y.1))
      map_smul' := fun e x => Subtype.ext (mul_left_comm a (T.i (c e)) (show T.B from x.1)) }
  map_one' := LinearMap.ext fun x => Subtype.ext (one_mul (show T.B from x.1))
  map_mul' a a' := LinearMap.ext fun x => Subtype.ext (mul_assoc a a' (show T.B from x.1))
  map_zero' := LinearMap.ext fun x => Subtype.ext (zero_mul (show T.B from x.1))
  map_add' a a' := LinearMap.ext fun x => Subtype.ext (add_mul a a' (show T.B from x.1))

def locMod (T : Thick (F.cr b ht κ)) {m : ℕ} (f : Fin m → T.B) (hf : Ideal.span (Set.range f) = ⊤) :
    LocMod (pdS (F.cr b ht κ) c r).fn T (fun S => locT T (∏ k ∈ S, f k)) (fun S => locHom T (∏ k ∈ S, f k)) where
  Λ := T.B
  f := f
  span := hf
  ρ₀ := mulR c r T
  ρ S := (mulR c r (locT T (∏ k ∈ S, f k))).comp (locHom T (∏ k ∈ S, f k)).φ
  lam_ρ S a x := Subtype.ext (map_mul (locHom T (∏ k ∈ S, f k)).φ a (show T.B from x.1))
  tr_ρ S S' t ht' a x := by
    have e : t.φ.comp (locHom T (∏ k ∈ S, f k)).φ = (locHom T (∏ k ∈ S', f k)).φ := congrArg Thick.Hom.φ ht'
    refine Subtype.ext ?_
    change t.φ ((locHom T (∏ k ∈ S, f k)).φ a * (show (locT T (∏ k ∈ S, f k)).B from x.1)) =
      (locHom T (∏ k ∈ S', f k)).φ a * t.φ (show (locT T (∏ k ∈ S, f k)).B from x.1)
    rw [map_mul, ← RingHom.comp_apply t.φ, e]
  unit S k hk := by
    have hu : IsUnit ((locHom T (∏ k ∈ S, f k)).φ (f k)) := unit_of_mem T f S hk
    obtain ⟨u, hu⟩ := hu
    have hinv : ∀ y : ((pdS (F.cr b ht κ) c r).fn.obj (locT T (∏ k ∈ S, f k))),
        mulR c r _ (↑u : (locT T (∏ k ∈ S, f k)).B) (mulR c r _ (↑u⁻¹ : (locT T (∏ k ∈ S, f k)).B) y) = y := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]
    have hinv' : ∀ y : ((pdS (F.cr b ht κ) c r).fn.obj (locT T (∏ k ∈ S, f k))),
        mulR c r _ (↑u⁻¹ : (locT T (∏ k ∈ S, f k)).B) (mulR c r _ (↑u : (locT T (∏ k ∈ S, f k)).B) y) = y := fun y => by
      rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]
    change Function.Bijective (mulR c r _ ((locHom T (∏ k ∈ S, f k)).φ (f k)))
    rw [← hu]
    exact ⟨Function.LeftInverse.injective hinv', Function.RightInverse.surjective hinv⟩
  surj S y := by
    obtain ⟨n, x, hx, e⟩ := loc_surj T (∏ k ∈ S, f k) r y.1 ((pdPow_locT T _ r).le y.2)
    exact ⟨n, ⟨x, hx⟩, Subtype.ext e⟩
  ker S x hx := by
    have h0 : algebraMap T.B (Localization.Away (∏ k ∈ S, f k)) (show T.B from x.1) = 0 := congrArg Subtype.val hx
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (∏ k ∈ S, f k)) _ _).1 h0
    exact ⟨n, Subtype.ext hn⟩

end Mod

theorem zarCov_pdS : ∀ {O : Type} [CommRing O] (F : Fn O) (b : Base) (ht : b.t = 1) (κ : O →+* b.R ⧸ b.I) {Λ : Type}
    [CommRing Λ] (c : Λ →+* b.R) {d : ℕ} (𝒜 : F.Atlas d), b.p ≠ 0 → ∀ r : ℕ,
    ZarCov (pdS (F.cr b ht κ) c r).fn fun T => ∃ α, (𝒜.V α).In T.y.1.2 := by
  intro O _ F b ht κ Λ _ c d 𝒜 hp r
  refine ⟨fun T T' φ ⟨α, hα⟩ => ⟨α, ?_⟩, fun T => ?_⟩
  · have h := (𝒜.V α).in_map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) hα
    rw [← φ.pt]
    exact h
  obtain ⟨m, s, hs, hcov⟩ := 𝒜.cov (CommRingCat.of (T.B ⧸ T.J)) T.y.1.2
  choose f hf using fun k => Ideal.Quotient.mk_surjective (s k)
  have hspan : Ideal.span (Set.range f) = ⊤ := span_lift hp T f s hf hs
  refine ⟨m, fun k _ ψ => IsUnit (ψ.φ (f k)), fun k T₁ T₂ ψ χ h => h.map χ.φ, fun k T₁ ψ h => ?_, fun T' φ => ?_⟩
  · have hu : IsUnit ((CommRingCat.ofHom (Ideal.quotientMap T₁.J ψ.φ ψ.hle)).hom (s k)) := by
      rw [← hf k]; exact h.map (Ideal.Quotient.mk T₁.J)
    obtain ⟨α, hα⟩ := hcov k _ _ hu
    refine ⟨α, ?_⟩
    rw [← ψ.pt]
    exact hα
  refine ⟨fun S => locT T' (∏ k ∈ S, φ.φ (f k)), fun S => locHom T' _, fun S k hk => unit_of_mem T' _ S hk,
    fun S T'' ψ h => locT_univ T' _ ψ ?_, ⟨locMod c r T' (fun k => φ.φ (f k)) ?_⟩⟩
  · rw [map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one h
  · have h := congrArg (Ideal.map φ.φ) hspan
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h

end GlobalTheory.CompanionTheory.ThickZar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLiftToThickening
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLiftToThickening
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickHom

theorem isNilpotent_of_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {p : ℕ} (h0 : p ≠ 0)
    (hp : IsNilpotent (p : B)) {x : B} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hp
  have key : ∀ M : ℕ, p ^ M ∣ (M * p).factorial := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Nat.succ_mul, pow_succ]
      exact (mul_dvd_mul ih (Nat.dvd_factorial (Nat.pos_of_ne_zero h0) le_rfl)).trans
        (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  obtain ⟨c, hc⟩ := key N
  refine ⟨N * p, ?_⟩
  rw [← δ.factorial_mul_dpow_eq_pow hx, hc]
  push_cast
  rw [hN]
  simp

variable {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1)
  {κ : O →+* b.R ⧸ b.I}

theorem comp_eq (T : Thick (F.cr b ht κ)) {g : s.R →+* T.B ⧸ T.J}
    (hg : F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2) (o : O) (x : b.R)
    (hx : Ideal.Quotient.mk b.I x = κ o) : g (s.a o) = Ideal.Quotient.mk T.J (T.i x) := by
  have h1 : F.Ov T.y.1.2 (g.comp s.a) := by
    have := F.ov_map (CommRingCat.ofHom g) s.ov
    rw [hg] at this
    exact this
  have h2 := F.ov_uniq h1 T.y.2
  have h3 := congrArg (fun f : O →+* _ => f o) h2
  have h4 : T.y.1.1 (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk T.J (T.i x) := T.w x
  rw [← h4, hx]
  exact h3

variable (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i))
  (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R))

theorem s_eq_one (T : Thick (F.cr b ht κ)) : T.s = 1 := by
  have h : (1 : T.B) = T.s * T.i b.t := (Finset.prod_of_isEmpty (ι := Empty) _).symm.trans T.hs
  rw [ht, map_one, mul_one] at h
  exact Units.ext h.symm

def homOf (T : Thick (F.cr b ht κ)) {g : s.R →+* T.B ⧸ T.J}
    (hg : F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2) (f : 𝓛.D →+* T.B) (hf : f.comp 𝓛.i = T.i)
    (hfg : ∀ r z, Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (f z) = g r) :
    liftObj s ht 𝓛 δ hδ hp hn ⟶ T :=
  have hdp : IsDPMorphism δ T.δ f :=
    (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers b.γ 𝓛.i δ hδ).2 T.δ f (by rw [hf]; exact T.compat)
  have hle : b.I.map 𝓛.i ≤ T.J.comap f := Ideal.map_le_iff_le_comap.1 hdp.1
  { φ := f
    u := fun j => j.elim
    comm := fun r => congrArg (fun e : b.R →+* T.B => e r) hf
    dp := hdp
    hle := hle
    pt := by
      have hq : (Ideal.quotientMap T.J f hle).comp 𝓛.j = g := by
        ext r
        obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (𝓛.j r)
        rw [RingHom.comp_apply, ← hz]
        exact hfg r z hz
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        have h1 : T.y.1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk T.J (T.i r) := T.w r
        refine Eq.trans ?_ h1.symm
        change Ideal.Quotient.mk T.J (f (𝓛.i r)) = _
        rw [← hf]
        rfl
      · refine Eq.trans ?_ hg
        rw [← hq]
        exact (congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _))
          (F.Pt.map_comp (CommRingCat.ofHom 𝓛.j) (CommRingCat.ofHom (Ideal.quotientMap T.J f hle)))) s.y₀).symm
    hx := fun j => j.elim
    hs := by
      have : IsEmpty (F.cr b ht κ).ι := inferInstanceAs (IsEmpty Empty)
      have h1 : (liftObj s ht 𝓛 δ hδ hp hn).s = 1 := rfl
      rw [s_eq_one ht T, h1, map_one, Finset.prod_of_isEmpty, one_mul]
    hv := fun j => j.elim }

theorem main (T : Thick (F.cr b ht κ)) :
    ∃ g : s.R →+* T.B ⧸ T.J,
      (∀ (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (r : s.R) (z : 𝓛.D),
        Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (c.φ z) = g r) ∧
      F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2 ∧
      ∀ u : Fin d → T.B, (∀ k, Ideal.Quotient.mk T.J (u k) = g (s.T k)) →
        ∃! c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T, ∀ k, c.φ (𝓛.t k) = u k := by
  obtain ⟨g, hg, hgu⟩ := s.univ (CommRingCat.of (T.B ⧸ T.J)) T.y.1.2 (T.y.1.1.comp κ) T.y.2
  have hc : ∀ (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (r : s.R) (z : 𝓛.D),
      Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (c.φ z) = g r := by
    intro c r z hz
    have hpt : F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T.J c.φ c.hle))
        (F.Pt.map (CommRingCat.ofHom 𝓛.j) s.y₀) = T.y.1.2 := congrArg (fun y => y.1.2) c.pt
    have e := congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _))
      (F.Pt.map_comp (CommRingCat.ofHom 𝓛.j) (CommRingCat.ofHom (Ideal.quotientMap T.J c.φ c.hle)))) s.y₀
    have hq : (Ideal.quotientMap T.J c.φ c.hle).comp 𝓛.j = g := hgu _ (e.trans hpt)
    have := congrArg (fun e : s.R →+* T.B ⧸ T.J => e r) hq
    refine Eq.trans ?_ this
    exact congrArg (Ideal.quotientMap T.J c.φ c.hle) hz
  refine ⟨g, hc, hg, fun u hu => ?_⟩
  have hJ : EtLift T.J := GlobalTheory.CompanionTheory.EtNil.etLift_of_nil T.J fun x hx =>
    isNilpotent_of_mem T.δ hp (T.adm.1 hp) hx
  obtain ⟨f, ⟨hf1, hf2, hf3⟩, hfu⟩ := GlobalTheory.CompanionTheory.EtaleLift.lift_hom_existsUnique s.a (fun k => (s.T k : s.R)) b.I κ 𝓛
    T.J hJ T.i g u (fun x hx => T.i_mem hx) (comp_eq s ht T hg) hu
  refine ⟨homOf s ht 𝓛 δ hδ hp hn T hg f hf1 hf3, hf2, fun c hck => ?_⟩
  have hcf : c.φ = f := hfu c.φ ⟨RingHom.ext c.comm, hck, hc c⟩
  exact Thick.Hom.ext hcf (funext fun j => j.elim)

end GlobalTheory.CompanionTheory.ThickHom
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLiftToThickeningStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_to_thickening : ∀ {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1) {κ : O →+* b.R ⧸ b.I} (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i)) (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R)) (T : Thick (F.cr b ht κ)), ∃ g : s.R →+* T.B ⧸ T.J, (∀ (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (r : s.R) (z : 𝓛.D), Ideal.Quotient.mk _ z = 𝓛.j r → Ideal.Quotient.mk T.J (c.φ z) = g r) ∧ F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.y.1.2 ∧ ∀ u : Fin d → T.B, (∀ k, Ideal.Quotient.mk T.J (u k) = g (s.T k)) → ∃! c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T, ∀ k, c.φ (𝓛.t k) = u k := by
  first | exact @GlobalTheory.CompanionTheory.ThickHom.main | exact GlobalTheory.CompanionTheory.ThickHom.main | (intros; apply GlobalTheory.CompanionTheory.ThickHom.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveOfUnramified
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
open TensorProduct

namespace GlobalTheory.CompanionTheory.EtalePerfect

theorem surjective_of_unramified {R S : Type} [CommRing R] [CommRing S] (p : ℕ) (hp : p.Prime)
    (hS : (p : S) = 0) (f : R →+* S) (hu : f.FormallyUnramified) (hft : f.FiniteType)
    (hpow : ∀ x : S, ∃ r, f r = x ^ p) : Function.Surjective f := by
  algebraize [f]
  have hint : Algebra.IsIntegral R S := ⟨fun x => by
    obtain ⟨r, hr⟩ := hpow x
    refine IsIntegral.of_pow hp.pos ?_
    rw [← hr]
    exact isIntegral_algebraMap⟩
  have hfin : Module.Finite R S := Algebra.IsIntegral.finite
  obtain ⟨t, ht2, ht1⟩ := Algebra.FormallyUnramified.iff_exists_tensorProduct.1
    (inferInstance : Algebra.FormallyUnramified R S)
  have hT : (p : S ⊗[R] S) = 0 := by
    rw [← map_natCast (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] S), hS, map_zero]
  have hadd : ∀ x y : S ⊗[R] S, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, hT]
    simp
  have haddS : ∀ x y : S, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, hS]
    simp
  have hfrob : ∀ u : S ⊗[R] S,
      u ^ p = ((Algebra.TensorProduct.lmul' R (S := S) u) ^ p) ⊗ₜ[R] (1 : S) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp [zero_pow hp.ne_zero]
    | tmul a b =>
      obtain ⟨s, hs⟩ := hpow b
      have hs' : b ^ p = s • (1 : S) := by
        rw [← hs, Algebra.smul_def, mul_one]; rfl
      rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.lmul'_apply_tmul, mul_pow, hs',
        TensorProduct.tmul_smul, mul_smul_comm, mul_one, TensorProduct.smul_tmul']
    | add x y hx hy =>
      rw [hadd, hx, hy, map_add (f := _), haddS, TensorProduct.add_tmul]
  have hmul : ∀ u : S ⊗[R] S,
      u * t = (Algebra.TensorProduct.lmul' R (S := S) u ⊗ₜ[R] (1 : S)) * t := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hb := ht2 b
      rw [sub_mul, sub_eq_zero] at hb
      have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : S)) * ((1 : S) ⊗ₜ[R] b) := by simp
      rw [this, mul_assoc, hb, ← mul_assoc]
      simp
    | add x y hx hy =>
      rw [add_mul, hx, hy, map_add (f := _), TensorProduct.add_tmul, add_mul]
  have hidem : t * t = t := by
    rw [hmul t, ht1]
    exact one_mul t
  have htp : t ^ p = t := (show IsIdempotentElem t from hidem).pow_eq hp.ne_zero
  have ht : t = 1 := by
    rw [← htp, hfrob t, ht1, one_pow]
    rfl
  have hepi : Algebra.IsEpi R S := by
    rw [Algebra.isEpi_iff_forall_one_tmul_eq]
    intro s
    have := ht2 s
    rw [ht, mul_one, sub_eq_zero] at this
    exact this
  exact Algebra.isEpi_iff_surjective_algebraMap_of_finite.1 hepi

theorem pf_of_etale : ∀ (p : ℕ), p.Prime → ∀ {P E : Type} [CommRing P] [CommRing E] (ψ : P →+* E),
    ψ.Etale → D.Pf p P → D.Pf p E := by
  intro p hp P E _ _ ψ hψ hP
  have hEc : (p : E) = 0 := by rw [← map_natCast ψ, hP.char, map_zero]
  have hadd : ∀ {A : Type} [CommRing A], (p : A) = 0 → ∀ x y : A, (x + y) ^ p = x ^ p + y ^ p := by
    intro A _ h x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, h]
    simp
  let φ : E →+* E :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd hEc }
  let Fp : P →+* P :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd hP.char }
  let e : P ≃+* P := RingEquiv.ofBijective Fp hP.bij
  let G : P →+* P := e.symm.toRingHom
  have hFG : ∀ x, (G x) ^ p = x := fun x => e.apply_symm_apply x
  have hGF : ∀ x, G (x ^ p) = x := fun x => e.symm_apply_apply x
  have hcomp : φ.comp (ψ.comp G) = ψ := by
    ext x
    change (ψ (G x)) ^ p = ψ x
    rw [← map_pow, hFG]
  have hUψ : ψ.FormallyUnramified := hψ.formallyUnramified
  have hFTψ : ψ.FiniteType := by
    algebraize [ψ]
    have : Algebra.Etale P E := hψ.toAlgebra
    exact (inferInstance : Algebra.FiniteType P E)
  have hu : φ.FormallyUnramified := by
    rw [← hcomp] at hUψ
    exact RingHom.FormallyUnramified.of_comp hUψ
  have hft : φ.FiniteType := by
    rw [← hcomp] at hFTψ
    exact RingHom.FiniteType.of_comp_finiteType hFTψ
  have hsurj : Function.Surjective φ :=
    surjective_of_unramified p hp hEc φ hu hft (fun x => ⟨x, rfl⟩)
  let N : Ideal E := RingHom.ker φ
  have hN : ∀ x ∈ N, IsNilpotent x := fun x hx => ⟨p, hx⟩
  have hL : EtLift N := GlobalTheory.T.etale_lifting_of_nil_ideal N hN
  let eb : (E ⧸ N) ≃+* E := RingHom.quotientKerEquivOfSurjective hsurj
  have heb : ∀ x, eb (Ideal.Quotient.mk N x) = x ^ p := fun x => rfl
  let g : E →+* E ⧸ N := eb.symm.toRingHom
  have hg : ∀ x, g (x ^ p) = Ideal.Quotient.mk N x := by
    intro x
    apply eb.injective
    rw [heb]
    exact eb.apply_symm_apply _
  have hgψ : g.comp ψ = (Ideal.Quotient.mk N).comp (ψ.comp G) := by
    ext x
    apply eb.injective
    change eb (eb.symm (ψ x)) = eb (Ideal.Quotient.mk N (ψ (G x)))
    rw [eb.apply_symm_apply, heb, ← map_pow, hFG]
  obtain ⟨h, ⟨hh1, hh2⟩, -⟩ := hL P E ψ hψ (ψ.comp G) g hgψ
  have hid : h.comp φ = RingHom.id E := by
    refine (hL P E ψ hψ ψ (Ideal.Quotient.mk N) rfl).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · ext x
      change h ((ψ x) ^ p) = ψ x
      rw [← map_pow]
      have := RingHom.congr_fun hh1 (x ^ p)
      simp only [RingHom.comp_apply] at this
      rw [this, hGF]
    · ext x
      have := RingHom.congr_fun hh2 (x ^ p)
      simp only [RingHom.comp_apply] at this
      change Ideal.Quotient.mk N (h (x ^ p)) = _
      rw [this, hg]
    · rfl
    · rfl
  refine ⟨hEc, ?_, ?_⟩
  · intro x y hxy
    have hx := RingHom.congr_fun hid x
    have hy := RingHom.congr_fun hid y
    simp only [RingHom.comp_apply, RingHom.id_apply] at hx hy
    rw [← hx, ← hy]
    exact congrArg h hxy
  · exact hsurj

end GlobalTheory.CompanionTheory.EtalePerfect
end
