module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyProjectorComplexBounded
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyProjectorComplexBounded
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfRetract

section Elements

variable {R : Type} [CommRing R] {K C E : ℕ → Type}
  [∀ p, AddCommGroup (K p)] [∀ p, AddCommGroup (C p)] [∀ p, AddCommGroup (E p)]
  [∀ p, Module R (K p)] [∀ p, Module R (C p)] [∀ p, Module R (E p)]

theorem qIsoAt_of_retract
    (dK : ∀ p, K p →ₗ[R] K (p + 1)) (dC : ∀ p, C p →ₗ[R] C (p + 1))
    (dE : ∀ p, E p →ₗ[R] E (p + 1))
    (φ : ∀ p, K p →ₗ[R] C p) (inc : ∀ p, C p →ₗ[R] E p) (r : ∀ p, E p →ₗ[R] C p)
    (h : ∀ p, E (p + 1) →ₗ[R] E p)
    (hc : ConeExact (K := K) (C := C) (fun p => dK p) (fun p => dC p) (fun p => φ p))
    (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ dC p = dE p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ dE p = dC p ∘ₗ r p)
    (h0 : inc 0 ∘ₗ r 0 = LinearMap.id + h 0 ∘ₗ dE 0)
    (hs : ∀ p, inc (p + 1) ∘ₗ r (p + 1) =
      LinearMap.id + dE p ∘ₗ h p + h (p + 1) ∘ₗ dE (p + 1)) :
    QIsoAt (0 : R →ₗ[R] K 0) (dK 0) (0 : R →ₗ[R] E 0) (dE 0) (inc 0 ∘ₗ φ 0) ∧
    ∀ n, QIsoAt (dK n) (dK (n + 1)) (dE n) (dE (n + 1)) (inc (n + 1) ∘ₗ φ (n + 1)) := by
  have hri' : ∀ p x, r p (inc p x) = x := fun p x => LinearMap.congr_fun (hri p) x
  have hinc' : ∀ p x, inc (p + 1) (dC p x) = dE p (inc p x) := fun p x => LinearMap.congr_fun (hinc p) x
  have hr' : ∀ p x, r (p + 1) (dE p x) = dC p (r p x) := fun p x => LinearMap.congr_fun (hr p) x
  have h0' : ∀ x, inc 0 (r 0 x) = x + h 0 (dE 0 x) := fun x => LinearMap.congr_fun h0 x
  have hs' : ∀ p x, inc (p + 1) (r (p + 1) x) = x + dE p (h p x) + h (p + 1) (dE (p + 1) x) :=
    fun p x => LinearMap.congr_fun (hs p) x
  refine ⟨⟨?_, ?_⟩, fun n => ⟨?_, ?_⟩⟩
  · rintro x hx ⟨y, hy⟩
    have h1 : inc 0 (φ 0 x) = 0 := by simpa using hy.symm
    have h2 : φ 0 x = 0 := by rw [← hri' 0 (φ 0 x), h1, map_zero]
    exact ⟨0, by simpa using (hc.inj x h2 hx).symm⟩
  · intro z hz
    obtain ⟨x, hx, hx'⟩ := hc.zero (r 0 z) 0
      (by change dC 0 (r 0 z) = φ 1 0; rw [← hr', hz]; simp) (by simp)
    have hx2 : φ 0 x = r 0 z := hx
    refine ⟨x, 0, hx', ?_⟩
    simp [hx2, h0', hz]
  · rintro x hx ⟨y, hy⟩
    have hy' : dE n y = inc (n + 1) (φ (n + 1) x) := hy
    have h1 : dC n (r n y) = φ (n + 1) x := by rw [← hr', hy', hri']
    cases n with
    | zero =>
      obtain ⟨w, -, hw⟩ := hc.zero (r 0 y) x h1 hx
      exact ⟨w, hw⟩
    | succ m =>
      obtain ⟨-, w, -, hw⟩ := hc.succ m (r (m + 1) y) x h1 hx
      exact ⟨w, hw⟩
  · intro z hz
    obtain ⟨c, k, hck, hk⟩ := hc.succ n (r (n + 1) z) 0
      (by change dC (n + 1) (r (n + 1) z) = φ (n + 2) 0; rw [← hr', hz]; simp) (by simp)
    have hck' : dC n c + φ (n + 1) k = r (n + 1) z := hck
    refine ⟨k, h n z - inc n c, hk, ?_⟩
    have h3 : φ (n + 1) k = r (n + 1) z - dC n c := eq_sub_of_add_eq' hck'
    simp only [LinearMap.comp_apply, h3, map_sub, hs', hinc', hz, map_zero, add_zero]
    abel

end Elements

section Complex

variable {R : Type} [CommRing R] {E : ℕ → Type} [∀ n, AddCommGroup (E n)] [∀ n, Module R (E n)]

theorem finite_homology_of_surjective (C : CochainComplex (ModuleCat.{0} R) ℕ) (i j k : ℕ)
    (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k)
    (W : Type) [AddCommGroup W] [Module R W] [Module.Finite R W]
    (f : W →ₗ[R] (LinearMap.ker (C.d j k).hom ⧸
      (LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype))
    (hf : Function.Surjective f) : Module.Finite R (C.homology j) := by
  have e := (C.homologyIsoSc' i j k hi hk ≪≫ (C.sc' i j k).moduleCatHomologyIso).toLinearEquiv
  have h1 : Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
      (LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype) :=
    Module.Finite.of_surjective f hf
  have h2 : Module.Finite R (LinearMap.ker (C.d j k).hom ⧸
      LinearMap.range (C.sc' i j k).moduleCatToCycles) := by
    refine Module.Finite.equiv (Submodule.quotEquivOfEq
      ((LinearMap.range (C.d i j).hom).comap (LinearMap.ker (C.d j k).hom).subtype)
      (LinearMap.range (C.sc' i j k).moduleCatToCycles) ?_)
    ext x
    exact ⟨fun ⟨y, hy⟩ => ⟨y, Subtype.ext hy⟩, fun ⟨y, hy⟩ => ⟨y, congrArg Subtype.val hy⟩⟩
  have h3 : Module.Finite R (C.sc' i j k).moduleCatLeftHomologyData.H := h2
  exact Module.Finite.equiv e.symm

noncomputable def cyclesMap (d : ∀ n, E n →ₗ[R] E (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (r : ∀ n, E n →ₗ[R] C.X n)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p) (j : ℕ) :
    LinearMap.ker (d j) →ₗ[R] LinearMap.ker (C.d j (j + 1)).hom :=
  (r j ∘ₗ (LinearMap.ker (d j)).subtype).codRestrict _ fun x => by
    have h1 := LinearMap.congr_fun (hr j) x.1
    simp only [LinearMap.comp_apply] at h1
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ← h1,
      LinearMap.mem_ker.1 x.2, map_zero]

theorem cyclesMap_surjective (d : ∀ n, E n →ₗ[R] E (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (inc : ∀ n, C.X n →ₗ[R] E n)
    (r : ∀ n, E n →ₗ[R] C.X n) (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p) (j : ℕ) :
    Function.Surjective (cyclesMap d C r hr j) := by
  intro y
  have h1 := LinearMap.congr_fun (hinc j) y.1
  simp only [LinearMap.comp_apply] at h1
  refine ⟨⟨inc j y.1, ?_⟩, Subtype.ext ?_⟩
  · rw [LinearMap.mem_ker, ← h1, LinearMap.mem_ker.1 y.2, map_zero]
  · exact LinearMap.congr_fun (hri j) y.1

theorem finite_homology_of_retract (d : ∀ n, E n →ₗ[R] E (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (inc : ∀ n, C.X n →ₗ[R] E n)
    (r : ∀ n, E n →ₗ[R] C.X n) (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p)
    (hf0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfs : ∀ n, Module.Finite R (LinearMap.ker (d (n + 1)) ⧸
      (LinearMap.range (d n)).comap (LinearMap.ker (d (n + 1))).subtype)) (p : ℕ) :
    Module.Finite R (C.homology p) := by
  have hsurj := cyclesMap_surjective d C inc r hri hinc hr
  cases p with
  | zero =>
    refine finite_homology_of_surjective C 0 0 1 (by simp) (by simp) (LinearMap.ker (d 0))
      (Submodule.mkQ _ ∘ₗ cyclesMap d C r hr 0) ?_
    exact (Submodule.mkQ_surjective _).comp (hsurj 0)
  | succ p =>
    have := hfs p
    refine finite_homology_of_surjective C p (p + 1) (p + 1 + 1) (by simp) (by simp)
      (LinearMap.ker (d (p + 1)) ⧸
        (LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)
      (Submodule.mapQ ((LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)
        ((LinearMap.range (C.d p (p + 1)).hom).comap
          (LinearMap.ker (C.d (p + 1) (p + 1 + 1)).hom).subtype)
        (cyclesMap d C r hr (p + 1)) ?_) ?_
    · rintro x ⟨y, hy⟩
      refine ⟨r p y, ?_⟩
      have h1 := LinearMap.congr_fun (hr p) y
      simp only [LinearMap.comp_apply] at h1
      rw [← h1, hy]
      rfl
    · intro y
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
      obtain ⟨x, rfl⟩ := hsurj (p + 1) y
      exact ⟨Submodule.Quotient.mk x, rfl⟩

end Complex

section Main

variable {R : Type} [CommRing R]

theorem exists_model_of_complex_retract [IsNoetherianRing R] {E : ℕ → Type}
    [∀ n, AddCommGroup (E n)] [∀ n, Module R (E n)] (d : ∀ n, E n →ₗ[R] E (n + 1))
    (e : ∀ n, E n →ₗ[R] E n) (h : ∀ n, E (n + 1) →ₗ[R] E n) (B : ℕ)
    (he0 : e 0 = LinearMap.id + h 0 ∘ₗ d 0)
    (hes : ∀ n, e (n + 1) = LinearMap.id + d n ∘ₗ h n + h (n + 1) ∘ₗ d (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (inc : ∀ n, C.X n →ₗ[R] E n)
    (r : ∀ n, E n →ₗ[R] C.X n) (hri : ∀ p, r p ∘ₗ inc p = LinearMap.id)
    (hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p)
    (hir : ∀ p, inc p ∘ₗ r p = e p)
    (hB : ∀ p, B < p → Limits.IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p)) :
    ∃ (Q : CochainComplex (ModuleCat.{0} R) ℕ) (ψ : ∀ n, Q.X n →ₗ[R] E n),
      (∀ n, Module.Finite R (Q.X n)) ∧ (∀ n, Module.Projective R (Q.X n)) ∧
      (∀ n, ψ (n + 1) ∘ₗ (Q.d n (n + 1)).hom = d n ∘ₗ ψ n) ∧
      ∀ M : ModuleCat.{0} R,
        QIsoAt (0 : R →ₗ[R] M ⊗[R] Q.X 0) ((Q.d 0 1).hom.lTensor M) (0 : R →ₗ[R] M ⊗[R] E 0)
          ((d 0).lTensor M) ((ψ 0).lTensor M) ∧
        ∀ n, QIsoAt ((Q.d n (n + 1)).hom.lTensor M) ((Q.d (n + 1) (n + 2)).hom.lTensor M)
          ((d n).lTensor M) ((d (n + 1)).lTensor M) ((ψ (n + 1)).lTensor M) := by
  obtain ⟨Q, φ, hQ0, hQfin, -, hQproj, hq, -, -⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso.{0, 0} C B hB hflat hfin
  have hQflat : ∀ p, Module.Flat R (Q.X p) := fun p => by
    have := hQproj p
    infer_instance
  refine ⟨Q, fun n => inc n ∘ₗ (φ.f n).hom, hQfin, hQproj, fun n => ?_, fun M => ?_⟩
  · refine LinearMap.ext fun x => ?_
    have h1 := LinearMap.congr_fun (hinc n) ((φ.f n).hom x)
    have h2 := GlobalTheory.cochain_comm_apply φ n (n + 1) x
    simp only [LinearMap.comp_apply] at h1 ⊢
    rw [← h1, h2]
  · have hc := GlobalTheory.coneExact_lTensor_of_quasiIso φ hQflat hflat B hQ0 hB M
    have key := qIsoAt_of_retract (R := R) (K := fun p => M ⊗[R] Q.X p)
      (C := fun p => M ⊗[R] C.X p) (E := fun p => M ⊗[R] E p)
      (fun p => (Q.d p (p + 1)).hom.lTensor M) (fun p => (C.d p (p + 1)).hom.lTensor M)
      (fun p => (d p).lTensor M) (fun p => (φ.f p).hom.lTensor M)
      (fun p => (inc p).lTensor M) (fun p => (r p).lTensor M) (fun p => (h p).lTensor M) hc
      (fun p => by rw [← LinearMap.lTensor_comp, hri, LinearMap.lTensor_id])
      (fun p => by rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hinc])
      (fun p => by rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hr])
      (by
        rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hir, he0, LinearMap.lTensor_add,
          LinearMap.lTensor_id])
      (fun p => by
        rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hir, hes,
          LinearMap.lTensor_add, LinearMap.lTensor_add, LinearMap.lTensor_id])
    simp only [LinearMap.lTensor_comp]
    exact key

theorem exists_finite_projective_model : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] (E : ℕ → Type) [∀ n, AddCommGroup (E n)]
    [∀ n, Module R (E n)] [∀ n, Module.Flat R (E n)] (d : ∀ n, E n →ₗ[R] E (n + 1))
    (_ : ∀ n, d (n + 1) ∘ₗ d n = 0) (e : ∀ n, E n →ₗ[R] E n) (h : ∀ n, E (n + 1) →ₗ[R] E n) (B : ℕ)
    (_ : ∀ n, e n ∘ₗ e n = e n) (_ : ∀ n, e (n + 1) ∘ₗ d n = d n ∘ₗ e n)
    (_ : e 0 = LinearMap.id + h 0 ∘ₗ d 0)
    (_ : ∀ n, e (n + 1) = LinearMap.id + d n ∘ₗ h n + h (n + 1) ∘ₗ d (n + 1))
    (_ : ∀ n, B < n → e n = 0)
    (_ : Module.Finite R (LinearMap.ker (d 0)))
    (_ : ∀ n, Module.Finite R (LinearMap.ker (d (n + 1)) ⧸
      (LinearMap.range (d n)).comap (LinearMap.ker (d (n + 1))).subtype)),
    ∃ (Q : CochainComplex (ModuleCat.{0} R) ℕ) (ψ : ∀ n, Q.X n →ₗ[R] E n),
      (∀ n, Module.Finite R (Q.X n)) ∧ (∀ n, Module.Projective R (Q.X n)) ∧
      (∀ n, ψ (n + 1) ∘ₗ (Q.d n (n + 1)).hom = d n ∘ₗ ψ n) ∧
      ∀ M : ModuleCat.{0} R,
        QIsoAt (0 : R →ₗ[R] M ⊗[R] Q.X 0) ((Q.d 0 1).hom.lTensor M) (0 : R →ₗ[R] M ⊗[R] E 0)
          ((d 0).lTensor M) ((ψ 0).lTensor M) ∧
        ∀ n, QIsoAt ((Q.d n (n + 1)).hom.lTensor M) ((Q.d (n + 1) (n + 2)).hom.lTensor M)
          ((d n).lTensor M) ((d (n + 1)).lTensor M) ((ψ (n + 1)).lTensor M) := by
  intro R _ _ E _ _ _ d hdd e h B hee hed he0 hes hB hf0 hfs
  have hrange : ∀ n (x : E n), x ∈ LinearMap.range (e n) → e n x = x := by
    rintro n _ ⟨y, rfl⟩
    exact LinearMap.congr_fun (hee n) y
  let dN : ∀ n, LinearMap.range (e n) →ₗ[R] LinearMap.range (e (n + 1)) := fun n =>
    (d n ∘ₗ (LinearMap.range (e n)).subtype).codRestrict _ (by
      rintro ⟨_, y, rfl⟩
      exact ⟨d n y, LinearMap.congr_fun (hed n) y⟩)
  have hdN : ∀ n (x : LinearMap.range (e n)), ((dN n x : LinearMap.range (e (n + 1))) : E (n + 1)) =
      d n x := fun _ _ => rfl
  let C : CochainComplex (ModuleCat.{0} R) ℕ :=
    CochainComplex.of (fun n => ModuleCat.of R (LinearMap.range (e n)))
      (fun n => ModuleCat.ofHom (dN n)) (fun n => by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
        exact LinearMap.congr_fun (hdd n) x.1)
  have hCd : ∀ p, C.d p (p + 1) = ModuleCat.ofHom (dN p) := fun p => by
    simp [C, CochainComplex.of_d]
  let inc : ∀ n, C.X n →ₗ[R] E n := fun n => (LinearMap.range (e n)).subtype
  let r : ∀ n, E n →ₗ[R] C.X n := fun n => (e n).rangeRestrict
  have hri : ∀ p, r p ∘ₗ inc p = LinearMap.id := fun p => by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hrange p _ x.2
  have hinc : ∀ p, inc (p + 1) ∘ₗ (C.d p (p + 1)).hom = d p ∘ₗ inc p := fun p => by
    rw [hCd]
    rfl
  have hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p := fun p => by
    rw [hCd]
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact LinearMap.congr_fun (hed p) x
  have hflat : ∀ p, Module.Flat R (C.X p) := fun p =>
    Module.Flat.of_retract (inc p) (r p) (hri p)
  refine exists_model_of_complex_retract d e h B he0 hes C inc r hri hinc hr (fun _ => rfl)
    (fun p hp => ?_) hflat (finite_homology_of_retract d C inc r hri hinc hr hf0 hfs)
  refine ModuleCat.isZero_iff_subsingleton.2 ?_
  change Subsingleton (LinearMap.range (e p))
  rw [hB p hp, LinearMap.range_zero]
  infer_instance

end Main

end GlobalTheory.CompanionTheory.PerfRetract
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyProjectorComplexBoundedStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
alias GlobalTheory.T.homotopy_projector_complex_bounded := GlobalTheory.CompanionTheory.PerfRetract.exists_finite_projective_model
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainHomotopyFiniteProjector
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainHomotopyFiniteProjector
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open AlgebraicTopology AlgebraicTopology.DoldKan Simplicial

namespace GlobalTheory.CompanionTheory.NerveNorm

section Cos

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def cosMap {x y : SimplexCategory} (θ : x ⟶ y) : Cn F x.len →ₗ[R] Cn F y.len where
  toFun f c := mp F (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last x.len)))))
    (f (θ.toOrderHom.monotone.functor ⋙ c))
  map_add' _ _ := funext fun _ ↦ map_add _ _ _
  map_smul' _ _ := funext fun _ ↦ map_smul _ _ _

theorem cosMap_apply {x y : SimplexCategory} (θ : x ⟶ y) (f : Cn F x.len) (c : Fin (y.len + 1) ⥤ C) :
    cosMap F θ f c = mp F (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last x.len)))))
      (f (θ.toOrderHom.monotone.functor ⋙ c)) := rfl

def cosK : SimplexCategory ⥤ ModuleCat.{0} R where
  obj x := ModuleCat.of R (Cn F x.len)
  map θ := ModuleCat.ofHom (cosMap F θ)
  map_id x := by
    ext f c
    have h : c.map (homOfLE (Fin.le_last ((𝟙 x : x ⟶ x).toOrderHom (Fin.last x.len)))) = 𝟙 _ :=
      (congrArg c.map (Subsingleton.elim _ _)).trans (c.map_id _)
    exact (congrArg (fun φ ↦ mp F φ (f c)) h).trans (mp_id F _ _)
  map_comp {x y z} θ ψ := by
    ext f c
    have h : c.map (homOfLE (Fin.le_last ((θ ≫ ψ).toOrderHom (Fin.last x.len)))) =
        c.map (homOfLE (ψ.toOrderHom.monotone (Fin.le_last (θ.toOrderHom (Fin.last x.len))))) ≫
          c.map (homOfLE (Fin.le_last (ψ.toOrderHom (Fin.last y.len)))) :=
      (congrArg c.map (Subsingleton.elim _ _)).trans (c.map_comp _ _)
    exact (congrArg (fun φ ↦ mp F φ (f ((θ ≫ ψ).toOrderHom.monotone.functor ⋙ c))) h).trans
      (mp_comp F _ _ _)

theorem cosK_map_δ (n : ℕ) (i : Fin (n + 2)) :
    ((cosK F).map (SimplexCategory.δ i)).hom = cof F n i := rfl

end Cos

section Norm

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev simpX : SimplicialObject (ModuleCat.{0} R)ᵒᵖ := (cosK F).op

def eN (n : ℕ) : Cn F n →ₗ[R] Cn F n := ((PInfty (X := simpX F)).f n).unop.hom

def hN (n : ℕ) : Cn F (n + 1) →ₗ[R] Cn F n := ((homotopyPInftyToId (simpX F)).hom n (n + 1)).unop.hom

theorem d_unop (n : ℕ) :
    ((AlternatingFaceMapComplex.obj (simpX F)).d (n + 1) n).unop.hom = dn F n := by
  rw [AlternatingFaceMapComplex.obj_d_eq]
  simp only [unop_sum, unop_zsmul, ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  unfold dn
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_smul_eq_zsmul R]
  push_cast
  rw [← cosK_map_δ F n i]
  rfl

theorem eN_idem (n : ℕ) : eN F n ∘ₗ eN F n = eN F n := by
  exact congrArg (fun f => f.unop.hom) (PInfty_f_idem (X := simpX F) n)

theorem eN_comm (n : ℕ) : eN F (n + 1) ∘ₗ dn F n = dn F n ∘ₗ eN F n := by
  have h := congrArg (fun f => f.unop.hom) ((PInfty (X := simpX F)).comm (n + 1) n)
  rw [← d_unop]
  exact h

theorem eN_zero : eN F 0 = LinearMap.id + hN F 0 ∘ₗ dn F 0 := by
  have h := (homotopyPInftyToId (simpX F)).comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at h
  have key : eN F 0 = hN F 0 ∘ₗ dn F 0 + LinearMap.id := by
    rw [← d_unop]
    exact congrArg (fun f => f.unop.hom) h
  exact key.trans (add_comm _ _)

theorem eN_succ (n : ℕ) :
    eN F (n + 1) = LinearMap.id + dn F n ∘ₗ hN F n + hN F (n + 1) ∘ₗ dn F (n + 1) := by
  have h := (homotopyPInftyToId (simpX F)).comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  have key : eN F (n + 1) = dn F n ∘ₗ hN F n + hN F (n + 1) ∘ₗ dn F (n + 1) + LinearMap.id := by
    rw [← d_unop, ← d_unop]
    exact congrArg (fun f => f.unop.hom) h
  rw [key]
  abel

theorem cosMap_σ_eN (n : ℕ) (i : Fin (n + 1)) :
    cosMap F (SimplexCategory.σ i) ∘ₗ eN F (n + 1) = 0 := by
  unfold eN
  change ((simpX F).σ i ≫ (PInfty (X := simpX F)).f (n + 1)).unop.hom = 0
  rw [σ_comp_PInfty]
  rfl

end Norm

section Vanish

variable {R : Type} [CommRing R] {P : Type} [PartialOrder P]

theorem exists_stutter [Finite P] (n : ℕ) (hn : Nat.card P < n + 1) (c : Fin (n + 2) ⥤ Pᵒᵖ) :
    ∃ i : Fin (n + 1), c.obj i.castSucc = c.obj i.succ := by
  by_contra hne
  simp only [not_exists] at hne
  have hanti : StrictAnti fun k : Fin (n + 2) => (c.obj k).unop := by
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    have hle : (c.obj i.succ).unop ≤ (c.obj i.castSucc).unop :=
      leOfHom (c.map (homOfLE (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le)).unop
    exact lt_of_le_of_ne hle fun heq => hne i (Opposite.unop_injective heq).symm
  haveI := Fintype.ofFinite P
  have hcard := Fintype.card_le_of_injective _ hanti.injective
  rw [Fintype.card_fin, ← Nat.card_eq_fintype_card] at hcard
  omega

theorem zero_of_degenerate (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) {m : ℕ} (g : Cn F m) {c₁ c₂ : Fin (m + 1) ⥤ Pᵒᵖ}
    (h : c₁ = c₂) {T : Pᵒᵖ} (φ : c₁.obj (Fin.last m) ⟶ T) (hT : c₂.obj (Fin.last m) = T)
    (h0 : mp F φ (g c₁) = 0) : g c₂ = 0 := by
  subst h
  subst hT
  have hφ : φ = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [hφ, mp_id] at h0
  exact h0

theorem eN_vanish [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) (n : ℕ) (hn : Nat.card P < n + 1) :
    eN F (n + 1) = 0 := by
  refine LinearMap.ext fun f => funext fun c => ?_
  show eN F (n + 1) f c = 0
  obtain ⟨i, hi⟩ := exists_stutter n hn c
  have h0 := congrFun (LinearMap.congr_fun (cosMap_σ_eN F n i) f)
    ((SimplexCategory.δ i.castSucc).toOrderHom.monotone.functor ⋙ c)
  rw [LinearMap.comp_apply, cosMap_apply, LinearMap.zero_apply, Pi.zero_apply] at h0
  have hlast : (SimplexCategory.δ i.castSucc).toOrderHom (Fin.last n) = Fin.last (n + 1) := by
    show i.castSucc.succAbove (Fin.last n) = Fin.last (n + 1)
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i))]
    exact Fin.succ_last n
  have hfun : (SimplexCategory.σ i).toOrderHom.monotone.functor ⋙
      ((SimplexCategory.δ i.castSucc).toOrderHom.monotone.functor ⋙ c) = c := by
    fapply CategoryTheory.Functor.ext
    · intro k
      show c.obj (i.castSucc.succAbove (i.predAbove k)) = c.obj k
      by_cases hk : k = i.castSucc
      · subst hk
        rw [Fin.predAbove_castSucc_self, Fin.succAbove_castSucc_self]
        exact hi.symm
      · rw [Fin.succAbove_predAbove hk]
    · intro _ _ _
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  exact zero_of_degenerate F (eN F (n + 1) f) hfun _ (congrArg c.obj hlast.symm) h0

end Vanish

theorem exists_normalisation {R : Type} [CommRing R] (P : Type) [SemilatticeInf P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R) :
    ∃ (e : ∀ n, Cn F n →ₗ[R] Cn F n) (h : ∀ n, Cn F (n + 1) →ₗ[R] Cn F n) (B : ℕ),
      (∀ n, e n ∘ₗ e n = e n) ∧ (∀ n, e (n + 1) ∘ₗ dn F n = dn F n ∘ₗ e n) ∧
      e 0 = LinearMap.id + h 0 ∘ₗ dn F 0 ∧
      (∀ n, e (n + 1) = LinearMap.id + dn F n ∘ₗ h n + h (n + 1) ∘ₗ dn F (n + 1)) ∧
      ∀ n, B < n → e n = 0 := by
  refine ⟨eN F, hN F, Nat.card P, eN_idem F, eN_comm F, eN_zero F, eN_succ F, fun n hn => ?_⟩
  cases n with
  | zero => exact absurd hn (Nat.not_lt_zero _)
  | succ m => exact eN_vanish F m hn

end GlobalTheory.CompanionTheory.NerveNorm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainHomotopyFiniteProjectorStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_homotopy_finite_projector : ∀ {R : Type} [CommRing R] (P : Type) [SemilatticeInf P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R),
    ∃ (e : ∀ n, Cn F n →ₗ[R] Cn F n) (h : ∀ n, Cn F (n + 1) →ₗ[R] Cn F n) (B : ℕ),
      (∀ n, e n ∘ₗ e n = e n) ∧ (∀ n, e (n + 1) ∘ₗ dn F n = dn F n ∘ₗ e n) ∧
      e 0 = LinearMap.id + h 0 ∘ₗ dn F 0 ∧
      (∀ n, e (n + 1) = LinearMap.id + dn F n ∘ₗ h n + h (n + 1) ∘ₗ dn F (n + 1)) ∧
      ∀ n, B < n → e n = 0 := by
  first | exact @GlobalTheory.CompanionTheory.NerveNorm.exists_normalisation | exact GlobalTheory.CompanionTheory.NerveNorm.exists_normalisation | (intros; apply GlobalTheory.CompanionTheory.NerveNorm.exists_normalisation <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfN

theorem QIsoAt.transport {R A₀ A₁ A₂ B₀ B₁ B₂ B₀' B₁' B₂' : Type} [CommRing R] [AddCommGroup A₀] [AddCommGroup A₁]
    [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₀'] [AddCommGroup B₁']
    [AddCommGroup B₂'] [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [Module R B₀'] [Module R B₁'] [Module R B₂'] {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁}
    {b₁ : B₁ →ₗ[R] B₂} {b₀' : B₀' →ₗ[R] B₁'} {b₁' : B₁' →ₗ[R] B₂'} {f : A₁ →ₗ[R] B₁}
    (v₀ : B₀ →ₗ[R] B₀') (v₁ : B₁ →ₗ[R] B₁') (v₂ : B₂ →ₗ[R] B₂')
    (s₀ : Function.Surjective v₀) (s₁ : Function.Bijective v₁) (s₂ : Function.Injective v₂)
    (c₀ : ∀ x, v₁ (b₀ x) = b₀' (v₀ x)) (c₁ : ∀ x, v₂ (b₁ x) = b₁' (v₁ x))
    (H : QIsoAt a₀ a₁ b₀ b₁ f) : QIsoAt a₀ a₁ b₀' b₁' (v₁ ∘ₗ f) := by
  refine ⟨fun x hx ⟨y, hy⟩ ↦ ?_, fun z hz ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := s₀ y
    exact H.1 x hx ⟨y, s₁.1 (by rw [c₀, hy]; rfl)⟩
  · obtain ⟨z, rfl⟩ := s₁.2 z
    obtain ⟨x, y, hx, hy⟩ := H.2 z (s₂ (by rw [c₁, hz, map_zero]))
    refine ⟨x, v₀ y, hx, ?_⟩
    rw [← c₀, ← hy, map_sub]; rfl

theorem finite_chains (P : Type) [PartialOrder P] [Finite P] (n : ℕ) : Finite (Fin (n + 1) ⥤ Pᵒᵖ) := by
  have : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  refine Finite.of_injective (fun (c : Fin (n + 1) ⥤ Pᵒᵖ) (i : Fin (n + 1)) ↦ c.obj i) fun c c' h ↦ ?_
  exact CategoryTheory.Functor.ext (fun i ↦ congrFun h i) (fun _ _ _ ↦ Subsingleton.elim _ _)

theorem flat_Cn {R : Type} [CommRing R] (P : Type) [PartialOrder P] [Finite P] (F : Pᵒᵖ ⥤ CommAlgCat.{0} R)
    (hF : ∀ T, Module.Flat R (F.obj T)) (n : ℕ) : Module.Flat R (Cn F n) := by
  have := finite_chains P n
  have := Fintype.ofFinite (Fin (n + 1) ⥤ Pᵒᵖ)
  classical
  exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R (Fin (n + 1) ⥤ Pᵒᵖ)
    (fun c ↦ F.obj (c.obj (Fin.last n)))).symm

theorem perfNoeth : CxSt → DictSt → PerfNoethSt := by
  intro hCx hD R _ P _ _ F hN hfl hf0 hfs
  obtain ⟨hd, -⟩ := hCx R Pᵒᵖ F
  obtain ⟨e₀, e₁, e₂, e₃, -, -, -, -, h0, h1, h2⟩ := hD R Pᵒᵖ F
  obtain ⟨e, h, B, i1, i2, i3, i4, i5⟩ := GlobalTheory.T.chain_homotopy_finite_projector P F
  have := fun n ↦ flat_Cn P F hfl n
  obtain ⟨Q, ψ, f1, f2, f3, f4⟩ := GlobalTheory.T.homotopy_projector_complex_bounded (fun n ↦ Cn F n) (dn F) hd e h B i1 i2 i3 i4 i5 hf0 hfs
  have g₀ : ∀ x, e₁ (dn F 0 x) = d0 F (e₀ x) := h0
  have g₁ : ∀ x, e₂ (dn F 1 x) = d1 F (e₁ x) := h1
  have g₂ : ∀ x, e₃ (dn F 2 x) = d2 F (e₂ x) := h2
  have k : ∀ n x, ψ (n + 1) ((Q.d n (n + 1)).hom x) = dn F n (ψ n x) := fun n x ↦
    LinearMap.congr_fun (f3 n) x
  have lt : ∀ {A B A' B' : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B'] [Module R A]
      [Module R B] [Module R A'] [Module R B'] (M : ModuleCat.{0} R) (u : A ≃ₗ[R] A') (v : B ≃ₗ[R] B')
      (b : A →ₗ[R] B) (b' : A' →ₗ[R] B'), (∀ x, v (b x) = b' (u x)) →
      ∀ x, (v : B →ₗ[R] B').lTensor M (b.lTensor M x) = b'.lTensor M ((u : A →ₗ[R] A').lTensor M x) := by
    intro A B A' B' _ _ _ _ _ _ _ _ M u v b b' h x
    have : (v : B →ₗ[R] B') ∘ₗ b = b' ∘ₗ (u : A →ₗ[R] A') := LinearMap.ext h
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, this]
  have bij : ∀ {A A' : Type} [AddCommGroup A] [AddCommGroup A'] [Module R A] [Module R A'] (M : ModuleCat.{0} R)
      (u : A ≃ₗ[R] A'), Function.Bijective ((u : A →ₗ[R] A').lTensor M) := fun M u ↦
    (u.lTensor M).bijective
  refine ⟨Q.X 0, Q.X 1, Q.X 2, Q.X 3, (Q.d 0 1).hom, (Q.d 1 2).hom, (Q.d 2 3).hom, (e₀ : _ →ₗ[R] _) ∘ₗ ψ 0,
    (e₁ : _ →ₗ[R] _) ∘ₗ ψ 1, (e₂ : _ →ₗ[R] _) ∘ₗ ψ 2, ⟨f1 0, f2 0⟩, ⟨f1 1, f2 1⟩, ⟨f1 2, f2 2⟩, ⟨f1 3, f2 3⟩,
    ?_, ?_, ?_, ?_, ⟨(e₃ : _ →ₗ[R] _) ∘ₗ ψ 3, ?_⟩, fun M ↦ ?_⟩
  · exact congrArg ModuleCat.Hom.hom (Q.d_comp_d 0 1 2)
  · exact congrArg ModuleCat.Hom.hom (Q.d_comp_d 1 2 3)
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, k]
    exact g₀ _
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [k 1]; exact g₁ _
  · refine LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [k 2]; exact g₂ _
  · obtain ⟨q0, qs⟩ := f4 M
    rw [LinearMap.lTensor_comp, LinearMap.lTensor_comp, LinearMap.lTensor_comp]
    exact ⟨QIsoAt.transport LinearMap.id _ _ Function.surjective_id (bij M e₀) (bij M e₁).1
        (fun x ↦ by simp) (lt M e₀ e₁ _ _ g₀) q0,
      QIsoAt.transport _ _ _ (bij M e₀).2 (bij M e₁) (bij M e₂).1 (lt M e₀ e₁ _ _ g₀) (lt M e₁ e₂ _ _ g₁) (qs 0),
      QIsoAt.transport _ _ _ (bij M e₁).2 (bij M e₂) (bij M e₃).1 (lt M e₁ e₂ _ _ g₁) (lt M e₂ e₃ _ _ g₂) (qs 1)⟩

end GlobalTheory.CompanionTheory.PerfN
