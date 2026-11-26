module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClass

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

def FMat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → ∃ kp σ, IsFMat L kp σ

def FForm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) kp σ, IsFMat L kp σ → ∃ A : Matrix (Fin G.n) (Fin G.n) G.F, A.det ≠ 0 ∧ (A.map (IsCMField.complexConj G.F))ᵀ = -A ∧
    (∀ u w, D.EF.baseChange ℚ u w = Algebra.trace ℚ G.F ((fun i => IsCMField.complexConj G.F (kp w i)) ⬝ᵥ (A *ᵥ kp u))) ∧
    ∀ c, A * σ (sh G c) = ((σ c).map (IsCMField.complexConj G.F))ᵀ * A

def SN : Prop :=
  ∀ (F K : Type) [Field F] [Field K] (n : ℕ) (τ : F →+* K) (ψ : Matrix (Fin n) (Fin n) F →+* Matrix (Fin n) (Fin n) K),
    (∀ x : F, ψ (Matrix.scalar (Fin n) x) = Matrix.scalar (Fin n) (τ x)) →
    ∃ S : Matrix (Fin n) (Fin n) K, S.det ≠ 0 ∧ ∀ M, ψ M * S = S * M.map τ

def ArchSpan : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (n : ℕ),
    Submodule.span ℝ (Set.range fun (x : Fin n → F) (v : InfinitePlace F) (i : Fin n) => v.embedding (x i)) = ⊤ ∧
    Module.finrank ℝ (InfinitePlace F → Fin n → ℂ) = n * Module.finrank ℚ F ∧
    ∀ x : F, ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ v : InfinitePlace F, 2 * (v.embedding x).re

def ArchEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → Nonempty (ArchFrame L)

def SigB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (B : GlobalTheory.LKCx.Form G) (v : InfinitePlace G.F), (GlobalTheory.LKCx.herm G v B.β).IsHermitian ∧
    (sigPosH (G.gram_herm v) = 1 → (∃ z, 0 < (hv (GlobalTheory.LKCx.herm G v B.β) z z).re) ∧ ∀ z x, 0 < (hv (GlobalTheory.LKCx.herm G v B.β) z z).re →
      x ≠ 0 → hv (GlobalTheory.LKCx.herm G v B.β) x z = 0 → (hv (GlobalTheory.LKCx.herm G v B.β) x x).re < 0) ∧
    (sigPosH (G.gram_herm v) ≠ 1 → ∀ x, x ≠ 0 → (hv (GlobalTheory.LKCx.herm G v B.β) x x).re < 0)

def PerExt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (A : ArchFrame L) (β : G.Cˣ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : VQ D →+ (Fin D.g → ℂ)), IsPerQ L β ρ Q →
    ∃ R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ), ∀ w, Q w = R (A.th w)

def JStruct : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (A : ArchFrame L) (β : G.Cˣ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : VQ D →+ (Fin D.g → ℂ)), IsPerQ L β ρ Q →
    (∀ v, (GlobalTheory.LKCx.herm G v β).IsHermitian) → ∀ R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ), (∀ w, Q w = R (A.th w)) →
    ∃ J : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ, (∀ x : Arch G, R (fun v => J v *ᵥ x v) = Complex.I • R x) ∧
      ∀ v, IsPosJ (GlobalTheory.LKCx.herm G v β) (J v) (sgnV L v)

def JLine : Prop :=
  ∀ (n : ℕ) (M J : Matrix (Fin n) (Fin n) ℂ) (s : ℂ), M.IsHermitian → (s = 1 ∨ s = -1) → IsPosJ M J s →
    (∀ z, z ≠ 0 → J *ᵥ z = (s * Complex.I) • z → 0 < (hv M z z).re) ∧
    ((∀ x, x ≠ 0 → (hv M x x).re < 0) → J = -(s * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)) ∧
    ((∃ z, 0 < (hv M z z).re) → ∃ z, z ≠ 0 ∧ J *ᵥ z = (s * Complex.I) • z) ∧
    ∀ z, 0 < (hv M z z).re → (∀ x, x ≠ 0 → hv M x z = 0 → (hv M x x).re < 0) → J *ᵥ z = (s * Complex.I) • z →
      ∀ x, J *ᵥ x = (s * Complex.I) • ((2 * (hv M x z / hv M z z)) • z - x)

def HermOfJ : Prop :=
  ∀ (g : ℕ) (E : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ), (∀ x, E x x = 0) → (∀ x y, E (Complex.I • x) (Complex.I • y) = E x y) →
    (∀ x, x ≠ 0 → 0 < E (Complex.I • x) x) → ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm x y).im = E x y

def LineBasis : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ), M.IsHermitian → 0 < (hv M z z).re →
    ∃ (i₀ : Fin n) (S : Matrix (Fin n) (Fin n) ℂ), S.det ≠ 0 ∧ S *ᵥ Pi.single i₀ 1 = z ∧ ∀ i, i ≠ i₀ → hv M (S *ᵥ Pi.single i 1) z = 0

def PlaceT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    (∀ v', sigPosH (G.gram_herm v') = 1 → v' = v) ∧ t₀ (D.ω : D.F) = D.ρc ∧ (starRingEnd ℂ) D.ρc ≠ D.ρc ∧
    ((sgnV L v = 1 ∧ ∀ x, v.embedding (L.e x) = t₀ x) ∨
      (sgnV L v = -1 ∧ (¬ ∀ x, v.embedding (L.e x) = t₀ x) ∧ ∀ x, (starRingEnd ℂ) (v.embedding (L.e x)) = t₀ x))

def TypeIso : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ i₀ : Fin G.n, ∃ R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ),
      (∀ x : Arch G, R (fun v' i => (if v' = v ∧ i = i₀ then 1 else -1) * (sgnV L v' * Complex.I) * x v' i) = Complex.I • R x) ∧
      ∀ (c : 𝓞 D.F) (x : Arch G), R (fun v' => v'.embedding (L.e (c : D.F)) • x v') = ρ (algebraMap (𝓞 D.F) D.O c) *ᵥ R x

def RPer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.a = 1 → ∀ (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ t₀ : D.F →+* ℂ, (∀ i, D.tau i = t₀) →
    ∀ ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ, IsSigD D ρ t₀ → ∀ (A : ArchFrame L) (B : GlobalTheory.LKCx.Form G) (z : GlobalTheory.LKCx.PosV G v B.β),
    ∃ (Q : VQ D →+ (Fin D.g → ℂ)) (R : Arch G →ₗ[ℝ] (Fin D.g → ℂ)), IsPerQ L B.β ρ Q ∧ (∀ w, Q w = R (A.th w)) ∧
      R (Pi.single v (Complex.I • z.1)) = (sgnV L v * Complex.I) • R (Pi.single v z.1)

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPowSm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.powSm_of :
    UpperTheory.Gal.W2.PowSm := by
  intro X s d g hs hqc hsep A _ _ hA hg k
  have hP : IsProper (KS.pow A k).hom := KS.Leray.isProper_pow_hom A hA.proper k
  have hsm := FibPow.smoothOfRelativeDimension_fibrePower ℂ X s d g hs A hA hg k
  refine ⟨hsm, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · haveI : Smooth ((KS.pow A k).hom ≫ s) := hsm.smooth
    infer_instance
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PHeckeCoord
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.heckeCoord_of :
    UpperTheory.Gal.W2.IsogAt → UpperTheory.Gal.W2.IsogCoord → UpperTheory.Gal.W2.HeckeCoord := by
  intro hA hC p _ D G L gb N N' h hlev X X' c hX hL hX' hL' ρ hF D' t P x e hU B j h₁ M hpl hco hloc
  obtain ⟨D'', t'', P'', e'', inc, d, hcls, hU'', hP, he, hd, hinc, f, nu, f'', nu'', hw, hw'', hf, hf'', hiff⟩ :=
    hA p D G L gb N N' h hlev X X' c hX hL hX' hL' ρ hF D' t P x e hU
  obtain ⟨h3, hNp, h3', hNp', -, hK⟩ := hlev
  obtain ⟨j'', hj, hpl'', hco'', hloc''⟩ :=
    hC p D G L B N N' (by omega) hNp (by omega) hNp' h hK ρ D' t D'' t'' P P'' inc d hU.2.1 hU''.2.1 hP hd hinc
      f nu f'' nu'' hw hw'' hf hf'' hiff j h₁ M hpl hco hloc
  refine ⟨D'', t'', P'', e'', inc, j'', hcls, hU'', hP, he, ?_, hj, hpl'', hco'', hloc''⟩
  intro u''
  obtain ⟨u, hu⟩ := hinc u''
  refine ⟨d, u, ?_, hu⟩
  rintro rfl
  have hp : p = 1 := by simpa using hd
  exact (Fact.out : p.Prime).one_lt.ne' hp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPowCorr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.powCorr_of :
    UpperTheory.Gal.W2.PwOver → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.PowCorr := by
  intro hPw hPt p _ D G L gb N N' h X X' c₁ c₂ ρ D' S hact ga hcomp k α
  have w₁ := hPw p D G L gb N N' 1 X X' c₁ k
  have w₂ := hPw p D G L gb N N' h X X' c₂ k
  refine ⟨?_, ?_⟩
  · intro P P'' hP hP'' hga z
    obtain ⟨hu, hex⟩ := hcomp P P'' hP hP'' hga
    have f := hPt D.O D.inv D.g ρ D' X'.X X'.s X'.univ.A S k P hP
    have f'' := hPt D.O D.inv D.g ρ D' X'.X X'.s X'.univ.A S k P'' hP''
    apply KS.PowPB.pow_left_hom_ext
    · simp only [Category.assoc, (w₂.2.2.2 α).1, w₁.1]
      simp only [← Category.assoc, f.1, f''.1]
      exact hu
    · intro i
      simp only [Category.assoc, (w₂.2.2.2 α).2 i, w₁.2.1 i]
      simp only [← Category.assoc, f.2.1, f''.2.1]
      rw [hex, Category.assoc, ← w₁.2.2.1, ← Category.assoc, ← hact P'' hP'']
      rfl
  · intro P hP hinj z z' heq
    have f := hPt D.O D.inv D.g ρ D' X'.X X'.s X'.univ.A S k P hP
    refine (f.2.2.2.1 z z').2 (fun j => hinj (z j) (z' j) ?_)
    have e := congrArg (· ≫ Over.Hom.left (KS.pr X.univ.A j)) heq
    simp only [Category.assoc, w₁.2.1 j] at e
    simpa only [← Category.assoc, f.2.1] using e
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.POneAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem congOne_of_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N N' : ℕ}
    (hd : N ∣ N') {g : G.GAf} (h : L.CongOne N' g) : L.CongOne N g := by
  obtain ⟨k, rfl⟩ := hd
  intro v hv
  obtain ⟨w, hw, hv'⟩ := h v hv
  exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [hv', smul_smul]⟩

private theorem coordA_of_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    {x : (AfP p ⊗[ℚ] G.C)ˣ} {N N' : ℕ} (hd : N ∣ N') {D' : PLat D.O D.inv} {t : D.La → D'.La}
    {j : D'.La →+ VQ D} {h₁ : G.GAf} (h : IsCoordA L x N' D' t j h₁) : IsCoordA L x N D' t j h₁ := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun a => ?_⟩
  obtain ⟨w, hw, e⟩ := h2 a
  exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩

theorem UpperTheory.Gal.W2.oneAt_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.OneAt := by
  intro hk li p _ D G L gb N N' h hlev X X' c₁ hX hL hX' hL' ρ hF B PD D' t hcls j a hpl hco hloc P x e hU
  obtain ⟨h3, hcop, h3', hcop', hdvd, -⟩ := hlev
  have lev1 : LevOk L N N' 1 := ⟨h3, hcop, h3', hcop', hdvd, fun u hu => by
    have hm : u ∈ L.KN N := ⟨congOne_of_dvd L hdvd hu.1, congOne_of_dvd L hdvd hu.2⟩
    simpa using hm⟩
  obtain ⟨D'', t'', P'', e'', inc, j'', hcls'', hU'', hPinc, he'', -, hj'', hpl'', hco'', hloc''⟩ :=
    hk p D G L gb N N' 1 lev1 X X' c₁ hX hL hX' hL' ρ hF D' t P x e hU B j a.1 (PD.lat a.2) hpl hco hloc
  have hco₁ : IsCoordA L (trivX B) N D'' t'' j'' a.1 := by simpa using hco''
  have hpos : 0 < N := by omega
  obtain ⟨w, hmk, hw⟩ := (li p D G L B PD N hpos hcop D' t D'' t'' j j'' a a N' N t t'' hcls hcls'' hpl hpl''
    (coordA_of_dvd L hdvd hco) hco₁ hloc hloc'' 1).1 ⟨by simp, by simp⟩
  have hw1 : ∀ u, j (w u) = j'' u := fun u => by
    rw [hw u]
    simp [actY]
  have hinc : ∀ u, w (inc u) = u := fun u => hpl.1 (by rw [hw1, hj''])
  have hP : ∀ u'', P (w u'') = P'' u'' := fun u'' => by
    have e1 : inc (w u'') = u'' := w.injective (hinc _)
    rw [← hPinc, e1]
  refine ⟨_, GlobalTheory.T.uniformisationAt_transport_isometry D.O D.inv D.g ρ ℂ (RingHom.id ℂ) D.La (gfam X.univ hX hL) N D'' D' t'' t P'' P
    (x ≫ c₁.q) e'' w (LinearEquiv.refl ℂ _) hpos hU'' hmk (fun u => hP u) hU.2.1, fun z => ?_⟩
  simpa using he'' z
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFixGa
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem isCoordA_of_dvd {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {G : HTGroup p} (L : Link D G)
    {x : (AfP p ⊗[ℚ] G.C)ˣ} {N N' : ℕ} (hd : N ∣ N') {D' : PLat D.O D.inv} {t : D.La → D'.La}
    {j : D'.La →+ VQ D} {h₁ : G.GAf} (h : IsCoordA L x N' D' t j h₁) : IsCoordA L x N D' t j h₁ := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun a => ?_⟩
  obtain ⟨w, hw, e⟩ := h2 a
  exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩

theorem UpperTheory.Gal.W2.fixGa_of :
    UpperTheory.Gal.W2.HeckeCoord → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.FixLine → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.IntMult → UpperTheory.Gal.W2.FixGa := by
  intro hHC hLI hFL hAY hIM
  unfold FixGa
  intro p _ D G L gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ B PD RD D' t hcls P j a hco x e hU y hsee
  obtain ⟨hpl, hca, hloc, Q₀, hQ₀, hQ₀j, hrel⟩ := hco
  obtain ⟨h3, hcp, h3', hcp', hd, hconj⟩ := hlev
  obtain ⟨D'', t'', P'', e'', inc, j'', hcls'', hU'', hP, he, hinc, hj, hpl'', hco'', hloc''⟩ :=
    hHC p D G L gb N N' h ⟨h3, hcp, h3', hcp', hd, hconj⟩ X X' c₂ hX hL hX' hL' ρ hfine D' t P x e hU B j a.1.1
      (PD.lat a.1.2) hpl hca hloc
  obtain ⟨hfix, hS, hK⟩ := hsee
  have hN : 0 < N := by omega
  have hS' : h * (a.1.1⁻¹ * B.toAf y * a.1.1) ∈ L.KN N := hS
  obtain ⟨w, hw, hwj⟩ := (hLI p D G L B PD N hN hcp D' t D'' t'' j j'' a.1 (a.1.1 * h⁻¹, a.1.2) N' N t t''
    hcls hcls'' hpl hpl'' (isCoordA_of_dvd L hd hca) hco'' hloc hloc'' y⁻¹).1 (by
      constructor
      · have := (L.KN N).inv_mem hS'
        simp only [map_inv, _root_.mul_inv_rev, _root_.inv_inv, _root_.mul_assoc] at this ⊢
        exact this
      · have := (KHT p G.m G.n 1 G.Fw).inv_mem hK
        simp only [map_inv, _root_.mul_inv_rev, _root_.inv_inv, _root_.mul_assoc] at this ⊢
        exact this)
  have hfix' := (hFL p D G L v t₀ ρ B.β RD Q₀ a.2 hQ₀ hrel y).2 hfix
  obtain ⟨H, hH⟩ := (hFL p D G L v t₀ ρ B.β RD Q₀ a.2 hQ₀ hrel y⁻¹).1.1 hfix'
  have hga : ∀ u, j (w (inc u)) = actY L y⁻¹ (j u) := fun u => by rw [hwj, hj]
  have hQQ : ∀ Q : VQ D →+ Fin D.g → ℂ, (∀ u, Q (j u) = P u) → ∀ w₀, Q w₀ = Q₀ w₀ := by
    intro Q hQj w₀
    obtain ⟨m, u, hm, hmu⟩ := hpl.2.2.1 w₀
    apply smul_right_injective (Fin D.g → ℂ) hm
    simp only
    rw [← map_nsmul Q, ← map_nsmul Q₀, hmu, hQj, hQ₀j]
  obtain ⟨s, hs, hEF⟩ := hpl.2.2.2
  have hpos : (0 : ℚ) < ((y⁻¹ : LKCx.grp G B.β) : G.Cˣ × ℚˣ).2 := (y⁻¹).2.2
  have hmul : ∀ u u' : D'.La, (((D'.EF ((w.toLinearMap ∘ₗ inc) u)) ((w.toLinearMap ∘ₗ inc) u') : ℤ) : ℚ) =
      (((y⁻¹ : LKCx.grp G B.β) : G.Cˣ × ℚˣ).2 : ℚ) * ((D'.EF u u' : ℤ) : ℚ) := by
    intro u u'
    show (((D'.EF (w (inc u))) (w (inc u')) : ℤ) : ℚ) = _
    rw [hEF, hEF, hga, hga, (hAY p D G L B.β y⁻¹).1]
    ring
  obtain ⟨m, hm, hm'⟩ := hIM D.O D.inv D' (w.toLinearMap ∘ₗ inc) _ hpos hmul
  refine ⟨w.toLinearMap ∘ₗ inc, H, fun u => hga u, ⟨⟨m, hm, hm'⟩, fun u => ?_⟩, fun w' Q hQj hQ => ?_⟩
  · show P (w (inc u)) = H *ᵥ P u
    rw [← hQ₀j, ← hQ₀j, hga, hH]
  · rw [hQQ Q hQj, hQQ Q hQj, hH]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPwOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem list_prod_ofFn_eq_of_eq_one_of_ne' {M : Type*} [Monoid M] :
    ∀ {m : ℕ} (f : Fin m → M) (i : Fin m), (∀ j, j ≠ i → f j = 1) → (List.ofFn f).prod = f i := by
  intro m
  induction m with
  | zero => intro f i; exact i.elim0
  | succ m ih =>
    intro f i hf
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun i' => ?_) i hf
    · intro hf0
      rw [List.prod_eq_one, _root_.mul_one]
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact hf0 _ (Fin.succ_ne_zero j)
    · intro hfs
      rw [hfs 0 (Fin.succ_ne_zero i').symm, _root_.one_mul]
      exact ih (fun j => f j.succ) i' (fun j hj => hfs _ (fun h => hj (Fin.succ_injective _ h)))

private theorem matEnd_diagonal_pr {S : Scheme.{0}} {O : Type} [Ring O] {A : Over S} [GrpObj A] (act : OActN O A) {m : ℕ}
    (d : Fin m → O) (i : Fin m) :
    GlobalTheory.KS.matEnd act (Matrix.diagonal d) ≫ GlobalTheory.KS.pr A i = GlobalTheory.KS.pr A i ≫ act.act (d i) := by
  unfold GlobalTheory.KS.matEnd GlobalTheory.KS.pr
  rw [Pi.lift_comp_π]
  rw [list_prod_ofFn_eq_of_eq_one_of_ne' _ i]
  · simp
  · intro j hj
    simp [Matrix.diagonal_apply_ne' d hj, GlobalTheory.KS.Model.act_zero, Hom.one_def]

theorem UpperTheory.Gal.W2.pwOver_of :
    UpperTheory.Gal.W2.PwOver := by
  intro p _ D G L gb N N' h X X' c k
  have hpw : c.pw k ≫ (KS.pow X.univ.A k).hom = (KS.pow X'.univ.A k).hom ≫ c.q := by
    delta Leg.pw
    exact KS.Model.powMap_over _ _ _ k
  have hpr : ∀ i : Fin k,
      c.pw k ≫ Over.Hom.left (KS.pr X.univ.A i) = Over.Hom.left (KS.pr X'.univ.A i) ≫ c.tot := by
    intro i
    delta Leg.pw
    exact KS.Model.powMap_pr _ _ _ k i
  refine ⟨hpw, hpr, ?_, fun α => ⟨?_, fun i => ?_⟩⟩
  · intro b
    delta Leg.tot
    have h1 := congrArg Over.Hom.left (c.tr.2.1 b)
    simp only [Over.comp_left] at h1
    rw [← Category.assoc, h1, Category.assoc, c.φ.act b, Category.assoc]
  · delta Leg.tw
    rw [Category.assoc, Over.w, hpw]
  · have hm := congrArg Over.Hom.left
      (matEnd_diagonal_pr X.univ.act (fun s => (algebraMap (𝓞 D.F) D.O (α s) : D.toG.O)) i)
    rw [Over.comp_left, Over.comp_left] at hm
    delta Leg.tw
    refine (Category.assoc _ _ _).trans ((congrArg (c.pw k ≫ ·) hm).trans ?_)
    rw [← Category.assoc, hpr, Category.assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTateWit
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

theorem tateWit_of : TateWit := by
  intro p _ D gb N S s o hX hL ρ D' t P x e hN hNp hU I hI
  classical
  obtain ⟨-, hper, hexp, hker, hact, hweil, heta⟩ := hU
  have hadd : ∀ z w, e (z + w) = e z * e w := hexp.1
  have hsurj : Function.Surjective e := hexp.2.1
  have hlin : ∀ (c : D.O) u, P (c • u) = ρ c *ᵥ P u := hper.1
  have hinj : Function.Injective P := hper.2.1
  haveI : Module.Free ℤ D.toG.La := D.freeLa
  have hlift : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ φ : D.La →+ D'.La, ∀ a, I.ev n a = e ((n : ℂ)⁻¹ • P (φ a)) :=
    fun n hn hnp => unifCls_lift e P hadd hsurj hker (I.ev n) (I.add n) hn
      (fun y => (I.onto n hn _).2 ⟨y, rfl⟩)
  have hroot : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ v : ℤ, IsCoprime v n ∧
      ((I.ζ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (v : ℂ) / n) :=
    fun n hn hnp => unifCls_root hn _ (I.ζ_prim n hn)
  let f : ℕ → D.La →+ D'.La := fun n => if hn : 0 < n ∧ n.Coprime p then Classical.choose (hlift n hn.1 hn.2) else 0
  let nu : ℕ → ℤ := fun n => if hn : 0 < n ∧ n.Coprime p then Classical.choose (hroot n hn.1 hn.2) else 0
  have hf : ∀ (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) a, I.ev n a = e ((n : ℂ)⁻¹ • P (f n a)) := by
    intro n hn hnp a
    simp only [f, dif_pos (And.intro hn hnp)]
    exact Classical.choose_spec (hlift n hn hnp) a
  have hnu : ∀ (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p), IsCoprime (nu n) n ∧
      ((I.ζ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (nu n : ℂ) / n) := by
    intro n hn hnp
    simp only [nu, dif_pos (And.intro hn hnp)]
    exact Classical.choose_spec (hroot n hn hnp)
  have heq : ∀ {n : ℕ}, 0 < n → ∀ v v' : D'.La,
      e ((n : ℂ)⁻¹ • P v) = e ((n : ℂ)⁻¹ • P v') ↔ ∃ w, v = v' + n • w :=
    fun hn v v' => unifCls_eq_iff e P hadd hker hinj hn v v'
  refine ⟨f, nu, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro n m hn hm hnm
    have hnp : n.Coprime p := (Nat.coprime_mul_iff_left.1 hnm).1
    refine ⟨?_, fun a => ?_⟩
    · have hz := I.ζ_pow n m hn hm
      have hz' := congrArg (fun u : ℂˣ => (u : ℂ)) hz
      simp only [Units.val_pow_eq_pow_val] at hz'
      rw [(hnu _ (Nat.mul_pos hn hm) hnm).2, (hnu n hn hnp).2, ← Complex.exp_nat_mul] at hz'
      have : (m : ℂ) * (-(2 * Real.pi * Complex.I) * (nu (n * m) : ℂ) / ((n * m : ℕ) : ℂ)) =
          -(2 * Real.pi * Complex.I) * (nu (n * m) : ℂ) / n := by
        have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
        have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
        push_cast; field_simp
      rw [this] at hz'
      exact (unifCls_exp_eq_iff hn _ _).1 hz'
    · have ht := I.tower n m hn hm a
      have e1 := hf _ (Nat.mul_pos hn hm) hnm a
      have e2 := hf n hn hnp a
      rw [e1, e2] at ht
      erw [unifCls_tower e P hadd hn hm] at ht
      exact (heq hn _ _).1 ht
  · intro n hn hnp
    refine ⟨(hnu n hn hnp).1, fun c a => ?_, fun a => ?_, fun a' => ?_, fun a a' => ?_⟩
    · have hl := I.lin n c a
      erw [hf n hn hnp (c • a), hf n hn hnp a] at hl
      have h3 := hact c ((n : ℂ)⁻¹ • P (f n a))
      rw [Matrix.mulVec_smul] at h3
      have h4 := hlin c (f n a)
      have h5 : e ((n : ℂ)⁻¹ • P (c • f n a)) = e ((n : ℂ)⁻¹ • P (f n a)) ≫ o.act.act c := by
        rw [h4]; exact h3
      exact (heq hn _ _).1 (hl.trans h5.symm)
    · have h1 := I.ker n hn a
      erw [hf n hn hnp a, unifCls_unit_iff e P hker hinj hn] at h1
      exact h1
    · obtain ⟨y, hy⟩ := (I.onto n hn (e ((n : ℂ)⁻¹ • P a'))).1 (unifCls_pow e P hadd hker hn a')
      rw [hf n hn hnp y] at hy
      obtain ⟨w, hw⟩ := (heq hn _ _).1 hy.symm
      exact ⟨y, w, hw⟩
    · have hiso := I.isom n hn a a'
      rw [hf n hn hnp a, hf n hn hnp a'] at hiso
      have hw := hweil n (f n a) (f n a')
        (Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF (f n a) (f n a') : ℂ) / n)) (Complex.exp_ne_zero _))
        hn rfl
      have hu := GlobalTheory.T.weilPairing_complex_value_unique S o.A D.g o.ab hX _ hL x n _ _ _ _ hiso hw
      have hu' := congrArg (fun u : ℂˣ => (u : ℂ)) hu
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hu'
      rw [(hnu n hn hnp).2, ← Complex.exp_int_mul] at hu'
      have : ((2 * D.toG.EF a a' : ℤ) : ℂ) * (-(2 * Real.pi * Complex.I) * (nu n : ℂ) / n) =
          -(2 * Real.pi * Complex.I) * ((nu n * (2 * D.toG.EF a a') : ℤ) : ℂ) / n := by
        push_cast; ring
      rw [this] at hu'
      exact (unifCls_exp_eq_iff hn _ _).1 hu'.symm
  · intro a
    have h3 : I.ev N a = e ((N : ℂ)⁻¹ • P (t a)) := (hI a).symm.trans (heta a)
    rw [hf N hN hNp a] at h3
    obtain ⟨w, hw⟩ := (heq hN _ _).1 h3
    exact ⟨w, hw⟩
  · intro n hn hnp a
    exact hf n hn hnp a

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.FixedPointsIntegralBaseOfUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem kn_anti {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N N' : ℕ}
    (hd : N ∣ N') : L.KN N' ≤ L.KN N := by
  obtain ⟨k, rfl⟩ := hd
  intro u hu
  have hu' : L.CongOne (N * k) u ∧ L.CongOne (N * k) u⁻¹ := hu
  show L.CongOne N u ∧ L.CongOne N u⁻¹
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨w, hw, e⟩ := hu'.1 v hv
    exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩
  · obtain ⟨w, hw, e⟩ := hu'.2 v hv
    exact ⟨k • w, (LaHat D).nsmul_mem hw k, by rw [e, smul_smul]⟩

private theorem s_inv {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {N N' : ℕ} {h : G.GAf}
    (hd : N ∣ N') (hc : ∀ u ∈ L.KN N', h * u * h⁻¹ ∈ L.KN N) :
    ∀ u ∈ L.KN N', ∀ g, u⁻¹ * g * u ∈ {g | h * g ∈ L.KN N} ↔ g ∈ {g | h * g ∈ L.KN N} := by
  intro u hu g
  have a : h * u⁻¹ * h⁻¹ ∈ L.KN N := hc _ (inv_mem hu)
  have b : u ∈ L.KN N := kn_anti L hd hu
  have e : h * (u⁻¹ * g * u) = (h * u⁻¹ * h⁻¹) * (h * g) * u := by group
  show h * (u⁻¹ * g * u) ∈ L.KN N ↔ h * g ∈ L.KN N
  rw [e, Subgroup.mul_mem_cancel_right _ b, Subgroup.mul_mem_cancel_left _ a]

private theorem sees_div {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} (B : GlobalTheory.LKCx.Form G)
    (a : GlobalTheory.LKCx.Dat G v B.β) (K : Subgroup G.GAf) (h : G.GAf) (y y' : GlobalTheory.LKCx.grp G B.β)
    (H : Sees B {g | h * g ∈ K} a y) (H' : Sees B {g | h * g ∈ K} a y') : Sees B (K : Set G.GAf) a (y⁻¹ * y') := by
  obtain ⟨⟨c, hc⟩, hS, hK⟩ := H
  obtain ⟨⟨c', hc'⟩, hS', hK'⟩ := H'
  have hS1 : h * (a.1.1⁻¹ * B.toAf y * a.1.1) ∈ K := hS
  have hS2 : h * (a.1.1⁻¹ * B.toAf y' * a.1.1) ∈ K := hS'
  refine ⟨⟨c⁻¹ * c', ?_⟩, ?_, ?_⟩
  · have key : ∀ w : Fin G.n → ℂ,
        ((LKCx.toV G v B.β y)⁻¹ : GL (Fin G.n) ℂ).val *ᵥ ((LKCx.toV G v B.β y).val *ᵥ w) = w := by
      intro w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [map_mul, map_inv, Units.val_mul, ← Matrix.mulVec_mulVec, hc', Matrix.mulVec_smul]
    by_cases h0 : c = 0
    · have hz := key a.2.1
      rw [hc, h0, zero_smul, Matrix.mulVec_zero] at hz
      rw [← hz]
      simp
    · have hz := key a.2.1
      rw [hc, Matrix.mulVec_smul] at hz
      have h3 : ((LKCx.toV G v B.β y)⁻¹ : GL (Fin G.n) ℂ).val *ᵥ a.2.1 = c⁻¹ • a.2.1 := by
        calc _ = c⁻¹ • (c • (((LKCx.toV G v B.β y)⁻¹ : GL (Fin G.n) ℂ).val *ᵥ a.2.1)) := by
                rw [smul_smul, _root_.inv_mul_cancel₀ h0, one_smul]
          _ = _ := by rw [hz]
      rw [h3, smul_smul, _root_.mul_comm]
  · show a.1.1⁻¹ * B.toAf (y⁻¹ * y') * a.1.1 ∈ K
    have e : a.1.1⁻¹ * B.toAf (y⁻¹ * y') * a.1.1 =
        (h * (a.1.1⁻¹ * B.toAf y * a.1.1))⁻¹ * (h * (a.1.1⁻¹ * B.toAf y' * a.1.1)) := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact K.mul_mem (K.inv_mem hS1) hS2
  · have e : a.1.2⁻¹ * LKCx.toP1 G B.β (y⁻¹ * y') * a.1.2 =
        (a.1.2⁻¹ * LKCx.toP1 G B.β y * a.1.2)⁻¹ * (a.1.2⁻¹ * LKCx.toP1 G B.β y' * a.1.2) := by
      rw [map_mul, map_inv]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hK) hK'

theorem UpperTheory.Gal.W2.fixedPoints_integral_base_of_uniformisation :
    UpperTheory.Gal.W2.RhoSig → UpperTheory.Gal.W2.GUnif → UpperTheory.Gal.W2.PDicEx → UpperTheory.Gal.W2.RDicEx → UpperTheory.Gal.W2.UnifG → UpperTheory.Gal.W2.StabTriv → UpperTheory.Gal.W2.FixFwd → UpperTheory.Gal.W2.FixEq → UpperTheory.Gal.W2.FixGa → UpperTheory.Gal.W2.FixLoc → UpperTheory.Gal.W2.TanExists → UpperTheory.Gal.W2.FixFinite → UpperTheory.Gal.W2.PowSm → UpperTheory.Gal.W2.PwOver → UpperTheory.Gal.W2.SumPts → UpperTheory.Gal.W2.EigSame → UpperTheory.Gal.W2.HeckeFixedPointCMCycleClass := by
  intro hRS hGU hPDE hRDE hUG hST hFF hFE hFG hFLo hTE hFFin hPS hPO hSP hES
  intro p _ D G L ha hm v hs t₀ ht gb hstd N N' h hlev X X' c₁ c₂ hreg k α hα het h₁ h₂
  obtain ⟨h3, hcp, h3', hcp', hd, hconj⟩ := hlev
  obtain ⟨ρ, hsig⟩ := hRS p D ha hm t₀ ht
  obtain ⟨hsm, hqc, hsep, hX, hL, hfine, ⟨U₀⟩⟩ := hGU p D ha hm t₀ ht ρ hsig gb hstd N h3 hcp X
  obtain ⟨hsm', hqc', hsep', hX', hL', hfine', ⟨U⟩⟩ := hGU p D ha hm t₀ ht ρ hsig gb hstd N' h3' hcp' X'
  have hpow := @hPS X.X X.s (D.n - 1) D.g hsm hqc hsep X.univ.A X.univ.grp X.univ.comm X.univ.ab hX k
  have hpow' := @hPS X'.X X'.s (D.n - 1) D.g hsm' hqc' hsep' X'.univ.A X'.univ.grp X'.univ.comm X'.univ.ab hX' k
  refine ⟨hpow.1, ?_⟩
  have hTan : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α →
      ∃ A, W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x A :=
    fun x hx => hTE _ _ (sZ X k) (sZ X' k) _ hpow.1 (c₁.pw k) (c₂.tw α) h₁ h₂ het x hx
  let At : CxPts (sZ X' k) (RingHom.id ℂ) → Matrix (Fin (D.n - 1 + k * D.g)) (Fin (D.n - 1 + k * D.g)) ℂ :=
    fun x => if hx : x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α then (hTan x hx).choose else 0
  have hAt : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), ∀ hx : x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α,
      W1.IsTan (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ x (At x) := by
    intro x hx
    simp only [At, dif_pos hx]
    exact (hTan x hx).choose_spec
  let PD : (B : LKCx.Form G) → PDic L B.β := fun B => (hPDE p D G L ha hm B).some
  let RD : (B : LKCx.Form G) → RDic L v B.β ρ t₀ := fun B => (hRDE p D G L ha hm v hs t₀ ht ρ hsig B).some
  obtain ⟨Φ, hΦ⟩ := hUG p D G L ha hm v hs t₀ ht ρ hsig PD RD N' (by omega) hcp' _ U
  have hproj : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ),
      (x.1 ≫ (KS.pow X'.univ.A k).hom) ≫ X'.s = spMap (RingHom.id ℂ) := by
    intro x
    rw [Category.assoc]
    exact x.2
  let π : CxPts (sZ X' k) (RingHom.id ℂ) → CxPts (gfam X'.univ hX' hL').s (RingHom.id ℂ) :=
    fun x => ⟨x.1 ≫ (KS.pow X'.univ.A k).hom, hproj x⟩
  have hbase : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α →
      (x.1 ≫ (KS.pow X'.univ.A k).hom) ≫ c₁.q = (x.1 ≫ (KS.pow X'.univ.A k).hom) ≫ c₂.q := by
    intro x hx
    rw [Category.assoc, Category.assoc, ← (hPO p D G L gb N N' 1 X X' c₁ k).1,
      ← ((hPO p D G L gb N N' h X X' c₂ k).2.2.2 α).1, ← Category.assoc, ← Category.assoc, hx]
  have hFwd : ∀ (q : LKCx.FCls G) (a : LKCx.Dat G v (Quot.out q).β) (i : Fin U.n) P j,
      PELU.IsPeriod (U.Di i) ρ P →
      IsCoord L (Quot.out q) (PD (Quot.out q)) (RD (Quot.out q)) N' (U.Di i) (U.t i) P j a →
      U.u i P ≫ c₁.q = U.u i P ≫ c₂.q → ∃ y, Sees (Quot.out q) {g | h * g ∈ L.KN N} a y :=
    fun q a i P j hper hco hfb => hFF p D G L gb N N' h ⟨h3, hcp, h3', hcp', hd, hconj⟩ X X' c₁ c₂ hX hL hX' hL' ρ
      hfine v t₀ (Quot.out q) (PD _) (RD _) (U.Di i) (U.t i) (U.mem i) P j a hco (U.u i P) (U.ex i P)
      (U.unif i P hper) hfb
  have hLoc := fun (q : LKCx.FCls G) (a : LKCx.Dat G v (Quot.out q).β) (i : Fin U.n) P j
      (hper : PELU.IsPeriod (U.Di i) ρ P)
      (hco : IsCoord L (Quot.out q) (PD (Quot.out q)) (RD (Quot.out q)) N' (U.Di i) (U.t i) P j a)
      (y : LKCx.grp G (Quot.out q).β) (hy : Sees (Quot.out q) {g | h * g ∈ L.KN N} a y) =>
    hFLo p D G L ha hm v hs t₀ ht gb N N' h ⟨h3, hcp, h3', hcp', hd, hconj⟩ X X' c₁ c₂ hX hL hX' hL' ρ hfine hsig
      hsm' hreg U (Quot.out q) (PD _) (RD _) i P j a hper hco y hy k α hα h₁ h₂
  have hdet : ∀ x : CxPts (sZ X' k) (RingHom.id ℂ), x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α → (1 - At x).det ≠ 0 := by
    intro x hx
    obtain ⟨q, a, i, P, j, -, hper, hxu, hco⟩ := hΦ (π x)
    have hxu' : x.1 ≫ (KS.pow X'.univ.A k).hom = U.u i P := hxu
    have hfb : U.u i P ≫ c₁.q = U.u i P ≫ c₂.q := by rw [← hxu']; exact hbase x hx
    obtain ⟨y, hy⟩ := hFwd q a i P j hper hco hfb
    obtain ⟨Fl, hFl, -, hAll⟩ := hLoc q a i P j hper hco y hy
    exact (hAll At (fun z hz => hAt z ((hFl z).1 hz).2)).1 x ((hFl x).2 ⟨hxu', hx⟩)
  have hfin : {x : CxPts (sZ X' k) (RingHom.id ℂ) | x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α}.Finite :=
    hFFin _ _ (sZ X k) (sZ X' k) (D.n - 1 + k * D.g) (c₁.pw k) (c₂.tw α) h₁ h₂ hpow.2.2.1 hpow'.2.1 hpow'.2.2.2
      (fun x hx => ⟨At x, hAt x hx, hdet x hx⟩)
  have hSinv := s_inv L hd hconj
  have hK1 : ∀ (B : LKCx.Form G) (a : LKCx.Dat G v B.β) (y : LKCx.grp G B.β),
      Sees B (L.KN N' : Set G.GAf) a y → y = 1 :=
    fun B a y hy => hST p D G L ha hm v hs t₀ ht ρ hsig PD RD N' h3' hcp' B a y hy
  have huniq : ∀ (B : LKCx.Form G) (a : LKCx.Dat G v B.β) (y y' : LKCx.grp G B.β),
      Sees B {g | h * g ∈ L.KN N} a y → Sees B {g | h * g ∈ L.KN N} a y' → y = y' := by
    intro B a y y' hy hy'
    exact _root_.inv_mul_eq_one.1
      (hST p D G L ha hm v hs t₀ ht ρ hsig PD RD N h3 hcp B a _ (sees_div B a (L.KN N) h y y' hy hy'))
  have hFb : ∀ (x' : CxPts (gfam X'.univ hX' hL').s (RingHom.id ℂ)) (q : LKCx.FCls G)
      (a : LKCx.Dat G v (Quot.out q).β) (i : Fin U.n) P j,
      PELU.IsPeriod (U.Di i) ρ P → x'.1 = U.u i P →
      IsCoord L (Quot.out q) (PD (Quot.out q)) (RD (Quot.out q)) N' (U.Di i) (U.t i) P j a →
      (x' ∈ hfin.toFinset.image π ↔ ∃ y, Sees (Quot.out q) {g | h * g ∈ L.KN N} a y) := by
    intro x' q a i P j hper hxu hco
    constructor
    · intro hx'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
      have hx2 : x.1 ≫ c₁.pw k = x.1 ≫ c₂.tw α := hfin.mem_toFinset.1 hx
      apply hFwd q a i P j hper hco
      rw [← hxu]
      exact hbase x hx2
    · rintro ⟨y, hy⟩
      obtain ⟨Fl, hFl, ⟨x, hxF⟩, -⟩ := hLoc q a i P j hper hco y hy
      obtain ⟨hxu', hx2⟩ := (hFl x).1 hxF
      exact Finset.mem_image.2 ⟨x, hfin.mem_toFinset.2 hx2, Subtype.ext (hxu'.trans hxu.symm)⟩
  refine ⟨hfin.toFinset, At, fun x => by rw [Set.Finite.mem_toFinset]; rfl,
    fun x hx => ⟨hAt x (hfin.mem_toFinset.1 hx), hdet x (hfin.mem_toFinset.1 hx)⟩, ?_,
    fun B a y hy => hST p D G L ha hm v hs t₀ ht ρ hsig PD RD N h3 hcp B a y hy, fun t => ?_⟩
  · refine ((hfin.toFinset.image π).finite_toSet.image Φ).subset ?_
    intro z hz
    obtain ⟨q, a, i, P, j, hΦx, hper, hxu, hco⟩ := hΦ (Φ.symm z)
    rw [Equiv.apply_symm_apply] at hΦx
    subst hΦx
    refine ⟨Φ.symm _, ?_, Equiv.apply_symm_apply _ _⟩
    obtain ⟨y, hy⟩ := hz
    obtain ⟨E, -, hE⟩ := hES p G v (fun _ _ => 0) (Quot.out q) (L.KN N') {g | h * g ∈ L.KN N} hSinv _ a
      (Quot.out_eq _)
    exact (hFb _ q a i P j hper hxu hco).2 ⟨E y, (hE y).1.1 hy⟩
  · let w : CxPts (gfam X'.univ hX' hL').s (RingHom.id ℂ) → ℂ :=
      fun x' => ∑ x ∈ hfin.toFinset.filter (fun x => π x = x'), lefTerm (At x) t
    have hsum : ∑ x ∈ hfin.toFinset, lefTerm (At x) t = ∑ x' ∈ hfin.toFinset.image π, w x' :=
      (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem π hx) _).symm
    rw [hsum]
    refine hSP p G v (wtFix L v t₀ α t) (L.KN N') {g | h * g ∈ L.KN N} hSinv hK1 huniq _ Φ _ w (fun x' => ?_)
    obtain ⟨q, a, i, P, j, hΦx, hper, hxu, hco⟩ := hΦ x'
    refine ⟨q, a, hΦx, hFb x' q a i P j hper hxu hco, fun y hy => ?_⟩
    obtain ⟨Fl, hFl, -, hAll⟩ := hLoc q a i P j hper hco y hy
    have hEq : hfin.toFinset.filter (fun x => π x = x') = Fl := by
      ext x
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hFl x]
      constructor
      · rintro ⟨hx, he⟩
        refine ⟨?_, hx⟩
        rw [← hxu, ← he]
        rfl
      · rintro ⟨he, hx⟩
        exact ⟨hx, Subtype.ext (he.trans hxu.symm)⟩
    show ∑ x ∈ hfin.toFinset.filter (fun x => π x = x'), lefTerm (At x) t = _
    rw [hEq]
    exact (hAll At (fun z hz => hAt z ((hFl z).1 hz).2)).2 t
end
