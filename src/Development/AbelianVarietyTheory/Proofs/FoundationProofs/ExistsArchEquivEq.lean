module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def placeOf (D : D7) (ρ : D.what₂.Tau) : InfinitePlace D.host.F :=
  InfinitePlace.mk ((tauE D ρ).comp (algebraMap D.host.F D.host.E))

theorem placeOf_bijective (D : D7) : Function.Bijective (placeOf D) := GlobalTheory.CMTypePlaces.places_bijective D

def embOverOf (D : D7) (ρ : D.what₂.Tau) : EmbOver D.host.E (placeOf D ρ) :=
  ⟨tauE D ρ, by
    have := (isCMExt_host D).1
    exact (InfinitePlace.embedding_mk_eq_of_isReal
      (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (placeOf D ρ)))).symm⟩

@[simp] theorem embOverOf_val (D : D7) (ρ : D.what₂.Tau) : (embOverOf D ρ).1 = tauE D ρ := rfl

theorem isInfFam_infProj (D : D7) : IsInfFam (D := D) fun ρ : D.what₂.Tau => infProj (embOverOf D ρ) :=
  fun ρ => isInfEmb_infProj (embOverOf D ρ)

theorem exists_isInfFam (D : D7) : ∃ θ, IsInfFam (D := D) θ := ⟨_, isInfFam_infProj D⟩

variable {D : D7}

theorem eq_placeOf {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F} (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) :
    w = placeOf D ρ := by
  rw [placeOf, ← hτ, τ.2, InfinitePlace.mk_embedding]

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem eq_infProj (hθ : IsInfFam θ) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F} (τ : EmbOver D.host.E w)
    (hτ : τ.1 = tauE D ρ) : θ ρ = infProj τ :=
  GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hθ ρ) (hτ ▸ isInfEmb_infProj τ)

theorem isAtTau_embArch (hθ : IsInfFam θ) (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) (x : GArch D.sp.cm.sig V.gram w) :
    IsAtTau θ V ρ (archEquiv V.gram (isCMExt_host D) τ x).1.1 (embArch D.sp.cm.sig V.gram w x) := by
  refine ⟨mem_infPts.2 (projFin_embArch _ _ w x), ?_, fun ρ' h => ?_⟩
  · rw [eq_infProj hθ τ hτ, infMat_infProj V.gram (isCMExt_host D), projArch_embArch_self]
  · have hw : placeOf D ρ' ≠ w := fun e => h ((placeOf_bijective D).1 (e.trans (eq_placeOf τ hτ)))
    rw [eq_infProj hθ (embOverOf D ρ') rfl, infMat_infProj V.gram (isCMExt_host D), projArch_embArch_ne _ _ hw,
      map_one]
    rfl

theorem archEquiv_mem_UH (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) (x : GArch D.sp.cm.sig V.gram w) :
    (archEquiv V.gram (isCMExt_host D) τ x).1.1 ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
  have h := (archEquiv V.gram (isCMExt_host D) τ x).2
  rw [gramAt, ← hτ]
  exact h

theorem exists_archEquiv_eq (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)) :
    ∃ x : GArch D.sp.cm.sig V.gram w, (archEquiv V.gram (isCMExt_host D) τ x).1.1 = g := by
  obtain ⟨θ, hθ⟩ := exists_isInfFam D
  obtain ⟨h, hh, -⟩ := GlobalTheory.PointAtPlace.existsUnique_isAtTau V ρ θ hθ g hg
  refine ⟨projArch _ _ w h, ?_⟩
  rw [← infMat_infProj, ← eq_infProj hθ τ hτ]
  exact hh.2.1

theorem atTau_archEquiv (hθ : IsInfFam θ) (V : HSp D) {ρ : D.what₂.Tau} {w : InfinitePlace D.host.F}
    (τ : EmbOver D.host.E w) (hτ : τ.1 = tauE D ρ) (x : GArch D.sp.cm.sig V.gram w) :
    atTau θ V ρ (archEquiv V.gram (isCMExt_host D) τ x).1.1 = embArch D.sp.cm.sig V.gram w x := by
  have hu := GlobalTheory.PointAtPlace.existsUnique_isAtTau V ρ θ hθ _ (archEquiv_mem_UH V τ hτ x)
  refine hu.unique ?_ (isAtTau_embArch hθ V τ hτ x)
  unfold atTau
  rw [dite_eq_left hu.exists]
  exact hu.exists.choose_spec

end GlobalTheory.AdelicU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct Matrix RestrictedProduct
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem eventually_algebraMap_mem_integers (a : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) a).2

theorem eventually_one_tmul_mem_intLoc (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (1 : Fv F v) ⊗ₜ[F] e ∈ intLoc F E v := by
  have : Algebra.IsAlgebraic ℤ E := IsFractionRing.comap_isAlgebraic_iff.2 (inferInstance : Algebra.IsAlgebraic ℚ E)
  obtain ⟨d, hd, hi⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) e).exists_integral_multiple
  have hd' : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
  filter_upwards [eventually_algebraMap_mem_integers (d : F)⁻¹] with v hv
  have h := tmul_mem_intLoc hv (⟨d • e, hi⟩ : 𝓞 E)
  convert h using 1
  change _ = _ ⊗ₜ[F] (d • e)
  rw [← Int.cast_smul_eq_zsmul F, ← TensorProduct.smul_tmul, Algebra.smul_def, ← map_mul, mul_inv_cancel₀ hd', map_one]

theorem eventually_map_evalV_mem_intLoc (z : Af F ⊗[F] E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z ∈ intLoc F E v := by
  induction z using TensorProduct.induction_on with
  | zero => exact Eventually.of_forall fun v => by rw [map_zero]; exact zero_mem _
  | add y z hy hz =>
    filter_upwards [hy, hz] with v h h'
    simpa only [map_add] using add_mem h h'
  | tmul a e =>
    filter_upwards [a.2, eventually_one_tmul_mem_intLoc (F := F) e] with v h h'
    have := mul_mem (tmul_mem_intLoc (a := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a) h (1 : 𝓞 E)) h'
    simpa using this

theorem exists_map_evalV_eq (z : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v ⊗[F] E)
    (hz : ∀ᶠ v in cofinite, z v ∈ intLoc F E v) :
    ∃ Z : Af F ⊗[F] E, ∀ v, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) Z = z v := by
  let b := Module.finBasis F E
  let c := RingOfIntegers.basis E
  have h1 : ∀ k, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y ∈ intLoc F E v,
      (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F := fun k => by
    filter_upwards [eventually_all.2 fun j => eventually_algebraMap_mem_integers (b.repr (c j : E) k)] with v hv y hy
    refine intLoc_induction (p := fun y => (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) (fun a ha x => ?_) (by simp) (fun y z h h' => by simpa using add_mem h h')
      (fun y h => by simpa using h) hy
    have e : b.repr (x : E) k = ∑ j, c.repr x j • b.repr (c j : E) k := by
      have e' : (x : E) = ∑ j, c.repr x j • (c j : E) := by
        conv_lhs => rw [← c.sum_repr x]
        simp
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [e', map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, e,
      map_sum, map_zsmul]
    exact mul_mem ha (sum_mem fun j _ => zsmul_mem (hv j) _)
  let A : Fin (Module.finrank F E) → Af F := fun k =>
    ⟨fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (z v) k, by
      filter_upwards [h1 k, hz] with v h h' using h _ h'⟩
  refine ⟨(Algebra.TensorProduct.basis (Af F) b).equivFun.symm A, fun v => ?_⟩
  apply (Algebra.TensorProduct.basis (Fv F v) b).repr.injective
  ext k
  rw [GlobalTheory.LatticeLocalGlobal.repr_map, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem eventually_one_tmul_mem_latLoc {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (fun i => (1 : Fv F v) ⊗ₜ[F] x i) ∈ latLoc F L v := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact Eventually.of_forall fun v => tmul_mem_latLoc (one_mem _) hx
  | zero => exact Eventually.of_forall fun v => tmul_mem_latLoc (one_mem _) L.zero_mem
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with v h h'
    convert add_mem h h' using 1
    funext i
    exact TensorProduct.tmul_add _ _ _
  | smul c x _ hx =>
    filter_upwards [hx, eventually_one_tmul_mem_intLoc (F := F) c] with v h h'
    convert (latLoc F L v).smul_mem ⟨_, h'⟩ h using 1
    funext i
    change _ = (1 : Fv F v) ⊗ₜ[F] c * (1 : Fv F v) ⊗ₜ[F] x i
    simp

theorem eventually_latLoc_le {L L' : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    (hL' : Submodule.span E (L' : Set (Fin n → E)) = ⊤) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, latLoc F L v ≤ latLoc F L' v := by
  obtain ⟨s, rfl⟩ := hL
  filter_upwards [(eventually_all_finset s).2 fun x _ => eventually_one_tmul_mem_latLoc (F := F) hL' x] with v hv y hy
  have h1 : ∀ x ∈ Submodule.span (𝓞 E) (s : Set (Fin n → E)), (fun i => (1 : Fv F v) ⊗ₜ[F] x i) ∈ latLoc F L' v := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hv x hx
    | zero => exact tmul_mem_latLoc (one_mem _) L'.zero_mem
    | add x y _ _ h h' =>
      convert add_mem h h' using 1
      funext i
      exact TensorProduct.tmul_add _ _ _
    | smul c x _ h =>
      convert (latLoc F L' v).smul_mem ⟨_, tmul_mem_intLoc (one_mem _) c⟩ h using 1
      funext i
      change (1 : Fv F v) ⊗ₜ[F] ((c : E) * x i) = (1 : Fv F v) ⊗ₜ[F] (c : E) * (1 : Fv F v) ⊗ₜ[F] x i
      simp
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  convert (latLoc F L' v).smul_mem ⟨_, tmul_mem_intLoc ha 1⟩ (h1 x hx) using 1
  funext i
  change _ = a ⊗ₜ[F] ((1 : 𝓞 E) : E) * (1 : Fv F v) ⊗ₜ[F] x i
  simp


variable (F) in
theorem eventually_latLoc_eq (L L' : Submodule (𝓞 E) (Fin n → E)) [hL : Submodule.IsFullLattice E L]
    [hL' : Submodule.IsFullLattice E L'] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, latLoc F L v = latLoc F L' v := by
  filter_upwards [eventually_latLoc_le (F := F) (Submodule.IsLattice.fg E L) (Submodule.IsFullLattice.span_eq_top (A := E) (M := L')),
    eventually_latLoc_le (F := F) (Submodule.IsLattice.fg E L') (Submodule.IsFullLattice.span_eq_top (A := E) (M := L))] with v h h' using le_antisymm h h'


theorem isLattice_stdLattice : Submodule.IsFullLattice E (stdLattice E n) := by
  haveI : Submodule.IsLattice E (stdLattice E n) := Submodule.IsLattice.of_fg E (by
    refine Submodule.fg_pi fun _ => ?_
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _)
  refine ⟨eq_top_iff.2 ?_⟩
  intro y _
  rw [← Finset.univ_sum_single y]
  refine sum_mem fun i _ => ?_
  have h1 : (Pi.single i 1 : Fin n → E) ∈ stdLattice E n := fun j _ => ⟨Pi.single (M := fun _ => 𝓞 E) i 1 j, by
      by_cases e : j = i
      · subst e; simp
      · simp [e]⟩
  convert Submodule.smul_mem _ (y i) (Submodule.subset_span h1) using 1
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)


omit [NumberField E] in
variable {σ J} in
theorem mem_stabLoc_stdLattice_iff {v : HeightOneSpectrum (𝓞 F)} {k : GLoc σ J v} :
    k ∈ stabLoc σ J (stdLattice E n) v ↔ (∀ i j, (matHom _ σ J k).1 i j ∈ intLoc F E v) ∧
      ∀ i j, (matHom _ σ J k⁻¹).1 i j ∈ intLoc F E v := by
  have h1 : ∀ k ∈ stabLoc σ J (stdLattice E n) v, ∀ i j, (matHom _ σ J k).1 i j ∈ intLoc F E v := fun k hk i j => by
    have := mem_latLoc_stdLattice.1 ((mem_stabLoc.1 hk (Pi.single j 1)).1 (mem_latLoc_stdLattice.2 fun l => by
      by_cases e : l = j
      · subst e; simp
      · simp [e])) i
    simpa using this
  have h2 : ∀ M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), (∀ i j, M i j ∈ intLoc F E v) →
      ∀ y ∈ latLoc F (stdLattice E n) v, M *ᵥ y ∈ latLoc F (stdLattice E n) v := fun M hM y hy =>
    mem_latLoc_stdLattice.2 fun i => show ∑ j, M i j * y j ∈ _ from
      sum_mem fun j _ => mul_mem (hM i j) (mem_latLoc_stdLattice.1 hy j)
  refine ⟨fun hk => ⟨h1 k hk, h1 _ (inv_mem hk)⟩, fun h => mem_stabLoc.2 fun y => ⟨h2 _ h.1 y, fun hy => ?_⟩⟩
  have := h2 _ h.2 _ hy
  rwa [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec] at this

theorem eventually_stabLoc_eq (L L' : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]
    [Submodule.IsFullLattice E L'] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, stabLoc σ J L v = stabLoc σ J L' v := by
  filter_upwards [eventually_latLoc_eq F L L'] with v h
  rw [stabLoc, stabLoc, h]

variable (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]

theorem eventually_projFinLoc_mem_stabLoc (g : GFin σ J) :
    ∀ᶠ v in cofinite, projFinLoc σ J v g ∈ stabLoc σ J L v := by
  have := isLattice_stdLattice (E := E) (n := n)
  filter_upwards [eventually_stabLoc_eq σ J L (stdLattice E n),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_map_evalV_mem_intLoc ((matHom _ σ J g).1 i j),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_map_evalV_mem_intLoc ((matHom _ σ J g⁻¹).1 i j)]
    with v h h1 h2
  rw [h, mem_stabLoc_stdLattice_iff, ← map_inv]
  exact ⟨h1, h2⟩

theorem eventually_proj_mem_stabLoc (g : GAd σ J) : ∀ᶠ v in cofinite, proj σ J v g ∈ stabLoc σ J L v := by
  simpa using eventually_projFinLoc_mem_stabLoc σ J L (projFin σ J g)

theorem existsUnique_projFinLoc_eq (x : ∀ v, GLoc σ J v) (hx : ∀ᶠ v in cofinite, x v ∈ stabLoc σ J L v) :
    ∃! g : GFin σ J, ∀ v, projFinLoc σ J v g = x v := by
  refine existsUnique_of_exists_of_unique ?_ fun g h hg hh => GFin_ext σ J fun v => (hg v).trans (hh v).symm
  have := isLattice_stdLattice (E := E) (n := n)
  have h0 : ∀ᶠ v in cofinite, (∀ i j, (matHom _ σ J (x v)).1 i j ∈ intLoc F E v) ∧
      ∀ i j, (matHom _ σ J (x v)⁻¹).1 i j ∈ intLoc F E v := by
    filter_upwards [eventually_stabLoc_eq σ J L (stdLattice E n), hx] with v h h'
    rwa [h, mem_stabLoc_stdLattice_iff] at h'
  choose A hA using fun i j => exists_map_evalV_eq (fun v => (matHom _ σ J (x v)).1 i j) (h0.mono fun v h => h.1 i j)
  choose B hB using fun i j =>
    exists_map_evalV_eq (fun v => (matHom _ σ J (x v)⁻¹).1 i j) (h0.mono fun v h => h.2 i j)
  let φ : ∀ v, Af F ⊗[F] E →+* Fv F v ⊗[F] E := fun v =>
    (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)).toRingHom
  have hext : ∀ M N : Matrix (Fin n) (Fin n) (Af F ⊗[F] E), (∀ v, M.map (φ v) = N.map (φ v)) → M = N :=
    fun M N h => Matrix.ext fun i j => GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => congrFun₂ (h v) i j
  have hA' : ∀ v, (Matrix.of A).map (φ v) = (matHom _ σ J (x v)).1 := fun v => Matrix.ext fun i j => hA i j v
  have hB' : ∀ v, (Matrix.of B).map (φ v) = (matHom _ σ J (x v)⁻¹).1 := fun v => Matrix.ext fun i j => hB i j v
  have hσ : ∀ v z, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (φ v z) = φ v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ z) := fun v z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [φ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hJ : ∀ v, (JR (Af F) J).map (φ v) = JR (Fv F v) J := fun v => by ext r s; simp [φ, JR, inclR]
  let u : GL (Fin n) (Af F ⊗[F] E) := ⟨Matrix.of A, Matrix.of B,
    hext _ _ fun v => by
      rw [Matrix.map_mul, hA', hB', map_inv, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)],
    hext _ _ fun v => by
      rw [Matrix.map_mul, hA', hB', map_inv, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hu : u ∈ HR (Af F) σ J := hext _ _ fun v => by
    change (cT _ (Matrix.of A) * _ * Matrix.of A).map _ = _
    rw [Matrix.map_mul, Matrix.map_mul, ← GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map _ _ _ (hσ v), hA', hJ]
    exact (x v).2
  exact ⟨⟨u, hu⟩, fun v => matHom_injective _ σ J (Units.ext (hA' v))⟩

end GlobalTheory.AdelicU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory NumberField Matrix Topology GlobalTheory.Mem.Vol
open Formalism.L2.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.VolPairExists
open scoped TensorProduct

namespace GlobalTheory.Mem.VolExists

section Chart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem infEmb_tmul (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (a : Ainf F) (x : E) : θ (a ⊗ₜ x) = GlobalTheory.InfAdeleCM.ext (τ.comp (algebraMap F E)) a * τ x :=
  haveI := h.1
  GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2 a x

theorem infEmb_unique (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ θ' : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (hθ' : IsInfEmb τ θ') : θ = θ' := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [infEmb_tmul h hθ, infEmb_tmul h hθ']
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem infEmb_continuous {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) : Continuous θ :=
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  IsModuleTopology.continuous_of_ringHom (R := Ainf F) θ hθ.2

theorem infEmb_sigR (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (z : Ainf F ⊗[F] E) : θ (sigR (Ainf F) σ z) = starRingEnd ℂ (θ z) := by
  haveI := h.1
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : sigR (Ainf F) σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl
    rw [e, infEmb_tmul h hθ, infEmb_tmul h hθ, map_mul, GlobalTheory.InfAdeleCM.conj_ext, h.2.2.2]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem infEmb_bijective (h : IsCMExt F E σ) {I : Type} {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) :
    Function.Bijective fun (z : Ainf F ⊗[F] E) (ρ : I) => θ ρ z := by
  haveI := h.1
  haveI := h.2.1
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc : ∀ (φ : E →+* ℂ) x, φ (c x) = starRingEnd ℂ (φ x) := h.2.2.2
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc1 : c ≠ 1 := fun e => by
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc, e, AlgEquiv.one_apply]
  choose θ₀ h1 h2 using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hΨ : ∀ φ, φ ∈ Set.range τ ↔ ComplexEmbedding.conjugate φ ∉ Set.range τ := fun φ => by
    constructor
    · rintro ⟨i, rfl⟩ ⟨j, hj⟩
      have : j = i := hτ.1 (by simp only [hj, InfinitePlace.mk_conjugate_eq])
      subst this
      exact hnr _ hj.symm
    · intro hn
      obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk φ)
      rcases InfinitePlace.mk_eq_iff.1 hi with e | e
      · exact ⟨i, e⟩
      · exact absurd ⟨i, by rw [← e]; ext x; simp⟩ hn
  have hb := GlobalTheory.InfAdeleCM.bijective c h.2.2.1 hc1 hc θ₀
    (fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ₀ φ) (h1 φ) (h2 φ)) _ hΨ
  have hinj : Function.Injective τ := fun i j e => hτ.1 (by simp only [e])
  have e0 : ∀ ρ, θ ρ = θ₀ (τ ρ) := fun ρ => infEmb_unique h (hθ ρ) ⟨h1 _, h2 _⟩
  have := ((Equiv.ofInjective τ hinj).symm.arrowCongr (Equiv.refl ℂ)).bijective.comp hb
  convert this using 1
  funext z ρ
  rw [e0]
  rfl

theorem exists_compact_adele (h : IsCMExt F E σ) {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, IsInfEmb (τ ρ) (θ ρ)) (R : ℝ) (C : Set (Af F ⊗[F] E))
    (hC : IsCompact C) : ∃ K : Set (AF F ⊗[F] E), IsCompact K ∧ ∀ z : AF F ⊗[F] E,
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z ∈ C →
      (∀ ρ, ‖θ ρ (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z)‖ ≤ R) → z ∈ K := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e₀⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e₀.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e₀.secondCountableTopology
  have hb := infEmb_bijective h hτ hθ
  let Θ : Ainf F ⊗[F] E →+ (I → ℂ) := (Pi.ringHom θ).toAddMonoidHom
  have hΘ : Continuous Θ := continuous_pi fun ρ => infEmb_continuous (hθ ρ)
  have ho : IsOpenMap Θ := AddMonoidHom.isOpenMap_of_sigmaCompact Θ hb.2 hΘ
  let Φ := (Equiv.ofBijective Θ hb).toHomeomorphOfContinuousOpen hΘ ho
  have hB : IsCompact (Φ ⁻¹' Set.pi Set.univ fun _ : I => Metric.closedBall (0 : ℂ) R) :=
    Φ.isCompact_preimage.2 (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨_, (hB.prod hC).image hc, fun z hz hR => ⟨e z, ⟨?_, ?_⟩, e.symm_apply_apply z⟩⟩
  · rw [(he z).1]
    exact fun ρ _ => mem_closedBall_zero_iff.2 (hR ρ)
  · rw [(he z).2]
    exact hz

variable {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem continuous_infMat {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) :
    Continuous fun h => infMat σ J θ h := by
  have h1 : Continuous fun h : HA (AF F) σ J => (HA.mat (AF F) σ J h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF F) σ J)))
  exact (h1.matrix_map (GlobalTheory.Member.Arch.continuous_inf F E)).matrix_map (infEmb_continuous hθ)

theorem continuous_finMat : Continuous fun h => finMat σ J h := by
  have h1 : Continuous fun h : HA (AF F) σ J => (HA.mat (AF F) σ J h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF F) σ J)))
  exact h1.matrix_map (GlobalTheory.LevelOpen.continuous_fin F E)

theorem JR_map {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ) :
    (JR (F := F) (Ainf F) J).map θ = J.map τ :=
  Matrix.ext fun _ _ => hθ.1 _

theorem infMat_unitary (h : IsCMExt F E σ) {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmb τ θ)
    (g : HA (AF F) σ J) : (infMat σ J θ g)ᴴ * J.map τ * infMat σ J θ g = J.map τ := by
  have hm := GlobalTheory.Member.Arch.inf_mem σ J (HA.mat (AF F) σ J g) g.2
  have h2 := GlobalTheory.Member.Arch.form_map _ θ (infEmb_sigR h hθ)
    ((HA.mat (AF F) σ J g).1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))) (JR (Ainf F) J)
  rw [← JR_map J hθ]
  exact h2.symm.trans (congrArg (fun X => X.map θ) hm)


variable (σ) in
def stab (L : Set (Fin M → E)) : Subgroup (HA (AF F) σ J) where
  carrier := {h | StabHat F L (finMat σ J h)}
  one_mem' := fun y => by rw [finMat_one, Matrix.one_mulVec]
  mul_mem' := fun {a b} ha hb y => by
    rw [finMat_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := fun {a} ha y => by
    refine Iff.trans ?_ (ha _).symm
    rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec]

theorem isOpen_stab (L : Submodule (𝓞 E) (Fin M → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) : IsOpen (stab σ J L : Set (HA (AF F) σ J)) := by
  have := Unfold.topGroupHA σ J
  have hn := GlobalTheory.LevelOpen.congr_mem_nhds F E M L hfg hsp 1 one_pos
  have hc := continuous_finMat (σ := σ) J
  have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds (by rw [finMat_one]; exact hn)
  have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
    (by rw [Function.comp_apply, inv_one, finMat_one]; exact hn)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_)
  rintro k ⟨hk1, hk2⟩ y
  constructor
  · intro hy
    obtain ⟨w, hw, h⟩ := hk1 y hy
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy
  · intro hy
    obtain ⟨w, hw, h⟩ := hk2 _ hy
    rw [Function.comp_apply, Matrix.mulVec_mulVec, ← finMat_mul, inv_mul_cancel, finMat_one,
      Matrix.one_mulVec] at h
    rw [eq_add_of_sub_eq h]
    exact add_mem (nsmul_mem hw 1) hy

end Chart

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem isCMExt (cm : CMData F E) : IsCMExt F E cm.sig :=
  ⟨cm.totReal, cm.cmUnram.1, cm.deg2, cm.cmUnram.2.1⟩

theorem isHermND (cm : CMData F E) (W : HSpace E) : IsHermND cm.sig W.gram :=
  ⟨fun i j => W.herm.eq (W.frame j) (W.frame i), GlobalTheory.StabCompact.det_gram_ne_zero W⟩

theorem exists_lattice (W : HSpace E) : ∃ L : Submodule (𝓞 E) (Fin W.rank → E), L.FG ∧
    Submodule.span E (L : Set (Fin W.rank → E)) = ⊤ ∧ (L : Set (Fin W.rank → E)) = latC W := by
  let f := W.frame.equivFun.toLinearMap
  refine ⟨W.L0.map (f.restrictScalars (𝓞 E)), W.standardTuple_isLattice.fg.map _, ?_, ?_⟩
  · have : (W.L0.map (f.restrictScalars (𝓞 E)) : Set (Fin W.rank → E)) = f '' W.L0 := rfl
    have hspan : Submodule.span E (W.L0 : Set W.V) = ⊤ := by
      classical
      by_contra hspan
      obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
      obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis W.hT W.nondeg W.frame
      let μ := ∑ j, star (φ (W.frame j)) • bs j
      have hμ : ∀ v, W.hT μ v = φ v := by
        have key : W.hT μ = φ := by
          apply W.frame.ext
          intro i
          dsimp [μ]
          rw [map_sum, LinearMap.sum_apply]
          have hs : ∀ j, W.hT (star (φ (W.frame j)) • bs j) (W.frame i) =
              φ (W.frame j) * (if i = j then 1 else 0) := by
            intro j
            rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
            congr 1
            rw [← W.herm.eq (W.frame i) (bs j), hbs]
            split_ifs <;> simp
          simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        intro v
        rw [key]
      have hμ₀ : μ ≠ 0 := by
        intro h
        apply hφ₀
        ext y
        simpa [h] using (hμ y).symm
      have hline (a : E) : a • μ ∈ W.L0 := by
        rw [← W.baseLattice_isUnimodular]
        change a • μ ∈ Formalism.E.hdual W.hT W.L0
        simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
          LinearMap.restrictScalars_apply]
        intro y hy
        have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
        simp [← W.herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
      obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
        (show μ ∉ (⊥ : Submodule E W.V) by simpa using hμ₀)
      let g := ψ.restrictScalars (𝓞 E)
      have hmap (x : E) : x ∈ W.L0.map g := by
        refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
        change ψ ((x / ψ μ) • μ) = x
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
      obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
        (S := nonZeroDivisors (𝓞 E)) (W.standardTuple_isLattice.fg.map g)
      have hinj := IsFractionRing.injective (𝓞 E) E
      have hne {a : 𝓞 E} (ha : a ≠ 0) : algebraMap (𝓞 E) E a ≠ 0 :=
        fun h => ha (hinj (h.trans (map_zero _).symm))
      have hinteger (x : E) : IsLocalization.IsInteger (𝓞 E) x := by
        have hx := hd _ (hmap ((algebraMap (𝓞 E) E d)⁻¹ * x))
        rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
          one_mul] at hx
      apply RingOfIntegers.not_isField E
      refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
      intro a ha
      obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 E) E a)⁻¹)
      refine ⟨b, hinj ?_⟩
      rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]
    rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]
  · ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, W.frame.equivFun x i • W.frame i ∈ W.L0
      rwa [W.frame.sum_equivFun]
    · intro hv
      refine ⟨W.frame.equivFun.symm v, ?_, W.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv

end Main

end GlobalTheory.Mem.VolExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
namespace GlobalTheory.AdelicU

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))

omit [NumberField E] in
theorem mem_levelOpen_iff_projFin {g : GAd σ J} :
    g ∈ levelOpen σ J L ↔ projFin σ J g ∈ levelOffFin σ J L ∅ := by
  simp [mem_levelOpen, mem_levelOffFin]

omit [NumberField E] in
theorem mem_stabLoc_iff_embLocFin {v : HeightOneSpectrum (𝓞 F)} {g : GLoc σ J v} :
    g ∈ stabLoc σ J L v ↔ embLocFin σ J v g ∈ levelOffFin σ J L ∅ := by
  rw [mem_levelOffFin]
  refine ⟨fun h => ⟨by simp, fun u _ => ?_⟩, fun h => by simpa using h.2 v (by simp)⟩
  by_cases e : u = v
  · subst e; simpa using h
  · rw [projFinLoc_embLocFin_ne σ J e]; exact one_mem _

omit [NumberField E] in
theorem image_ofFin_levelOffFin (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ofFin σ J '' (levelOffFin σ J L S : Set (GFin σ J)) = (levelOff σ J L S : Set (GAd σ J)) := by
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hg
    have h : g ∈ (ofFin σ J).range := by rw [range_ofFin]; exact (mem_levelOff.1 hg).1
    obtain ⟨y, rfl⟩ := h
    exact ⟨y, hg, rfl⟩

variable [Submodule.IsFullLattice E L]

theorem isOpen_isCompact_levelOffFin_empty :
    IsOpen (levelOffFin σ J L ∅ : Set (GFin σ J)) ∧ IsCompact (levelOffFin σ J L ∅ : Set (GFin σ J)) := by
  have hfg : L.FG := Submodule.IsLattice.fg (A := E) L
  obtain ⟨K, hK, ho, hc⟩ := GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab F E σ n J L hfg
    Submodule.IsFullLattice.span_eq_top
  have e : levelOffFin σ J L ∅ = K := by
    ext g
    have h := mem_levelOpen_iff_latHat σ J hfg (ofFin σ J g)
    have h2 : Formalism.MainNotions.StandardLattice.finMat σ J (ofFin σ J g) = (HA.mat (Af F) σ J g).1 :=
      congrArg (fun x => (HA.mat (Af F) σ J x).1) (projFin_ofFin σ J g)
    rw [mem_levelOpen_iff_projFin, projFin_ofFin, h2] at h
    exact h.trans (hK g).symm
  rw [e]
  exact ⟨ho, hc⟩

theorem isOpen_levelOffFin_empty : IsOpen (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
  (isOpen_isCompact_levelOffFin_empty σ J L).1

theorem isOpen_levelOpen : IsOpen (levelOpen σ J L : Set (GAd σ J)) := by
  have : (levelOpen σ J L : Set (GAd σ J)) = projFin σ J ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_levelOpen_iff_projFin σ J L
  rw [this]
  exact (isOpen_levelOffFin_empty σ J L).preimage (continuous_projFin σ J)

theorem isOpen_stabLoc (v : HeightOneSpectrum (𝓞 F)) : IsOpen (stabLoc σ J L v : Set (GLoc σ J v)) := by
  have : (stabLoc σ J L v : Set (GLoc σ J v)) = embLocFin σ J v ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_stabLoc_iff_embLocFin σ J L
  rw [this]
  exact (isOpen_levelOffFin_empty σ J L).preimage (continuous_embLocFin σ J v)

theorem isCompact_stabLoc (v : HeightOneSpectrum (𝓞 F)) : IsCompact (stabLoc σ J L v : Set (GLoc σ J v)) := by
  have : (stabLoc σ J L v : Set (GLoc σ J v)) = embLocFin σ J v ⁻¹' (levelOffFin σ J L ∅ : Set (GFin σ J)) :=
    Set.ext fun _ => mem_stabLoc_iff_embLocFin σ J L
  rw [this]
  exact (Function.LeftInverse.isClosedEmbedding (projFinLoc_embLocFin_self σ J v) (continuous_projFinLoc σ J v)
    (continuous_embLocFin σ J v)).isCompact_preimage (isOpen_isCompact_levelOffFin_empty σ J L).2

theorem isCompact_levelOffFin (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (levelOffFin σ J L S : Set (GFin σ J)) := by
  have : (levelOffFin σ J L S : Set (GFin σ J)) =
      (levelOffFin σ J L ∅ : Set (GFin σ J)) ∩ ofFin σ J ⁻¹' (awayPts σ J S : Set (GAd σ J)) := by
    ext g
    change ofFin σ J g ∈ levelOff σ J L S ↔ ofFin σ J g ∈ levelOff σ J L ∅ ∧ ofFin σ J g ∈ awayPts σ J S
    simp only [levelOff_eq, finAwayPts, Subgroup.mem_inf, awayPts_empty, Subgroup.mem_top]
    tauto
  rw [this]
  exact (isOpen_isCompact_levelOffFin_empty σ J L).2.inter_right
    ((isClosed_awayPts σ J S).preimage (continuous_ofFin σ J))

theorem isCompact_levelOff (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsCompact (levelOff σ J L S : Set (GAd σ J)) := by
  rw [← image_ofFin_levelOffFin]
  exact (isCompact_levelOffFin σ J L S).image (continuous_ofFin σ J)

theorem isCompact_levelFin : IsCompact (levelFin σ J L : Set (GAd σ J)) := isCompact_levelOff σ J L ∅

end GlobalTheory.AdelicU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem valued_natCast_le_of_mem_asIdeal {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (m : ℕ)
    (hm : (m : 𝓞 L) ∈ P.asIdeal) : Valued.v ((m : P.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ) := by
  have h1 : ((m : P.adicCompletion L)) = ((algebraMap (𝓞 L) L (m : 𝓞 L) : L) : P.adicCompletion L) := by
    rw [map_natCast]
    exact (map_natCast (algebraMap L (P.adicCompletion L)) m).symm
  rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have := (P.intValuation_le_pow_iff_mem (m : 𝓞 L) 1).2 (by simpa using hm)
  simpa using this

theorem finiteAdele_apply_sub_one_of_eq {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (m : ℕ)
    (a b : FiniteAdeleRing (𝓞 L) L) (e : a - 1 = (m : FiniteAdeleRing (𝓞 L) L) * b) :
    a P - 1 = (m : P.adicCompletion L) * b P := by
  let ev : FiniteAdeleRing (𝓞 L) L →+* P.adicCompletion L :=
    RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) P
  have e3 : ev (a - 1) = ev ((m : FiniteAdeleRing (𝓞 L) L) * b) := congrArg ev e
  rw [ev.map_sub, ev.map_mul, ev.map_one, map_natCast ev m] at e3
  exact e3

theorem tame_heckeChar_eq_one_of_finUnit : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → (∀ P, χ.TameAt P) → ∀ m : ℕ, (∀ P : HeightOneSpectrum (𝓞 D.host.E), (m : 𝓞 D.host.E) ∉ P.asIdeal → χ.UnrAt P) → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = m • y) → c x = 1 := by
  intro D c χ hc ht m hu x hx ⟨y, hy, hxy⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.T.exists_baseChangeFiniteAdele_ringEquiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.T.heckeChar_eq_prod_localComponents_approximating D ι h1 h2 (GlobalTheory.T.exists_finitePlaceIdempotent_baseChangeAdeles D ι h1 h2 h3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.T.finiteIdele_exists_local_approx' D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have key := hprod x hx1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  obtain ⟨a, -, b⟩ := hS P hP
  have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := a
  have b' : Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k P : D.host.E) := b
  rw [hv P] at a'
  rw [← a', mul_one] at b'
  have hun : IsUnitAt P (atFin P (k P)) := by
    show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
  have : χ.loc P (atFin P (k P)) = 1 := by
    by_cases hm : (m : 𝓞 D.host.E) ∈ P.asIdeal
    · refine ht P _ hun ?_
      have e : ι (finPart D (x : AE D)) - 1 = (m : FiniteAdeleRing (𝓞 D.host.E) D.host.E) * ι y := by
        rw [← map_one ι, ← map_sub, hxy, map_nsmul, nsmul_eq_mul]
      have e2 : ι (finPart D (x : AE D)) P - 1 = (m : P.adicCompletion D.host.E) * ι y P :=
        finiteAdele_apply_sub_one_of_eq P m _ _ e
      have c1 : Valued.v (ι (finPart D (x : AE D)) P - 1) ≤ WithZero.exp (-1 : ℤ) := by
        rw [e2, map_mul]
        calc _ ≤ WithZero.exp (-1 : ℤ) * 1 :=
              mul_le_mul' (valued_natCast_le_of_mem_asIdeal P m hm) ((h2 _).1 hy P)
          _ = _ := mul_one _
      have e4 : ((atFin P (k P) : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) - 1 =
          (ι (finPart D (x : AE D)) P - 1) - (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) := by
        show algebraMap D.host.E _ (k P : D.host.E) - 1 = _
        ring
      rw [e4]
      exact Valuation.map_sub_le _ c1 b'
    · exact hu P hm _ hun
  show ((χ.loc P (atFin P (k P)) : ℂˣ) : ℂ) = 1
  rw [this, Units.val_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameHeckeChar_trivial_on_finiteUnits_cong_one : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → (∀ P, χ.TameAt P) → ∀ m : ℕ, (∀ P : HeightOneSpectrum (𝓞 D.host.E), (m : 𝓞 D.host.E) ∉ P.asIdeal → χ.UnrAt P) → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = m • y) → c x = 1 := by
  first | exact @GlobalTheory.tame_heckeChar_eq_one_of_finUnit | exact GlobalTheory.tame_heckeChar_eq_one_of_finUnit | (intros; apply GlobalTheory.tame_heckeChar_eq_one_of_finUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharOrderFin

theorem locK_pow_eq_one {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ}
    (h : χ.OrderDvd n) (P : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : χ.locK P k ^ n = 1 := by
  have h1 : (χ.1 : _ →* ℂˣ) ^ n = 1 := by
    have := congrArg Subtype.val h
    simpa using this
  have h2 : ∀ y, χ.1 y ^ n = 1 := fun y => by
    have := DFunLike.congr_fun h1 y
    simpa [MonoidHom.pow_apply] using this
  exact h2 _

theorem char_pow_eq_one_of_orderDvd : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E),
    ChrEq c χ → ∀ n : ℕ, χ.OrderDvd n → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x ^ n = 1 := by
  intro D c χ hc n hn x hx
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have h4 := GlobalTheory.T.exists_finitePlaceIdempotent_baseChangeAdeles D ι h1 h2 h3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2 h4 c χ hc
  let y : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨ι (finPart D (x : AE D)), ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)),
      by rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one],
      by rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]⟩
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN y
  have h5 := hprod x hx S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Circle.ext
  have h6 : ((c x ^ n : Circle) : ℂ) = ((c x : Circle) : ℂ) ^ n :=
    map_pow Circle.coeHom (c x) n
  rw [h6, h5, ← Finset.prod_pow, Circle.coe_one]
  refine Finset.prod_eq_one fun P _ => ?_
  rw [← Units.val_pow_eq_pow_val, locK_pow_eq_one hn, Units.val_one]

end GlobalTheory.CharOrderFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvdStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idelicCharacter_pow_eq_one_finiteIdeles_of_orderDvd : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∀ n : ℕ, χ.OrderDvd n → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → c x ^ n = 1 := by
  first | exact @GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd | exact GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd | (intros; apply GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd <;> assumption)
end
end
