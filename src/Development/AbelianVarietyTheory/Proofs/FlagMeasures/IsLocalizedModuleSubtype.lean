module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitian
public import Formalism.HermitianLattices.FinalMass

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnimodQuot

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_rep (H : HermSpace K V) (f : V →ₗ[K] K) : ∃ y, ∀ x, H.B x y = f x := by
  have h1 : (LinearMap.range H.B.flip).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    exact H.nondeg x fun y => hx _ ⟨y, rfl⟩
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range H.B.flip)
  rw [h1, Submodule.dualAnnihilator_bot] at h2
  have h3 : f ∈ LinearMap.range H.B.flip := h2 ▸ Submodule.mem_top
  obtain ⟨y, hy⟩ := h3
  exact ⟨y, fun x => by rw [← hy]; rfl⟩

theorem mem_of_perp_perp (H : HermSpace K V) (I : Submodule K V) {v : V}
    (hv : ∀ x ∈ perp H I, H.B x v = 0) : v ∈ I := by
  by_contra h
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  obtain ⟨w, hw⟩ := exists_rep H f
  have hwI : w ∈ perp H I := by
    rw [mem_perp_iff]
    intro x hx
    have : f x = 0 := by
      have : f x ∈ I.map f := Submodule.mem_map_of_mem hx
      rwa [hf0, Submodule.mem_bot] at this
    rw [← H.herm, hw, this, star_zero]
  apply hf
  rw [← hw, ← H.herm, hv w hwI, star_zero]

omit [StarRing K] [FiniteDimensional K V] in
theorem mem_one_iff (x : K) : x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.isIntegral_coe
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem star_mem_one {x : K} (h : x ∈ (1 : Submodule (𝓞 K) K)) : star x ∈ (1 : Submodule (𝓞 K) K) := by
  rw [mem_one_iff] at h ⊢
  exact map_isIntegral_int (starRingEnd K) h

variable [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in
theorem exists_smul_mem {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) (y : V) :
    ∃ s : nonZeroDivisors (𝓞 K), s • y ∈ L := by
  have hy : y ∈ Submodule.span K (L : Set V) := by rw [hL.span_eq_top]; trivial
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (L : Set V) y hy
  rw [Submodule.span_eq] at hs
  exact ⟨s, hs⟩

omit [StarRing K] [FiniteDimensional K V] in
theorem isLocalizedModule_subtype {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) :
    IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype := by
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro s
    have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
    exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
  · intro y
    obtain ⟨s, hs⟩ := exists_smul_mem hL y
    exact ⟨(⟨_, hs⟩, s), rfl⟩
  · intro x₁ x₂ h
    exact ⟨1, by rw [Subtype.ext h]⟩

omit [StarRing K] [FiniteDimensional K V] in
theorem exists_extension {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) (S : Submodule K V)
    (φ : ↥(L ⊓ rs (𝓞 K) S) →ₗ[𝓞 K] 𝓞 K) :
    ∃ ψ : L →ₗ[𝓞 K] 𝓞 K, ∀ x : ↥(L ⊓ rs (𝓞 K) S), ψ ⟨x, x.2.1⟩ = φ x := by
  let N : Submodule (𝓞 K) L := (rs (𝓞 K) S).comap L.subtype
  have hflat : Module.Flat (𝓞 K) (L ⧸ N) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro q ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    have h1 : N.mkQ ((a : 𝓞 K) • x) = 0 := by rw [map_smul]; exact ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have h2 : (algebraMap (𝓞 K) K a) • (x : V) ∈ S := by
      rw [algebraMap_smul]; exact h1
    have h3 : algebraMap (𝓞 K) K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    exact (S.smul_mem_iff h3).1 h2
  have : Module.Finite (𝓞 K) L := Submodule.IsLattice.finite K L
  have : Module.FinitePresentation (𝓞 K) (L ⧸ N) := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) (L ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  let ρ : L →ₗ[𝓞 K] V := L.subtype ∘ₗ (LinearMap.id - s ∘ₗ N.mkQ)
  have hρ : ∀ x, ρ x ∈ L ⊓ rs (𝓞 K) S := by
    intro x
    refine ⟨(x - s (N.mkQ x)).2, ?_⟩
    have : x - s (N.mkQ x) ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
      have := LinearMap.congr_fun hs (N.mkQ x)
      rw [LinearMap.comp_apply] at this
      rw [this, LinearMap.id_apply, sub_self]
    exact this
  refine ⟨φ ∘ₗ ρ.codRestrict _ hρ, fun x => ?_⟩
  rw [LinearMap.comp_apply]
  congr 1
  apply Subtype.ext
  have h0 : N.mkQ ⟨x, x.2.1⟩ = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact x.2.2
  show ((⟨x, x.2.1⟩ - s (N.mkQ ⟨x, x.2.1⟩) : L) : V) = x
  rw [h0, map_zero, sub_zero]

theorem exists_lattice_rep (H : HermSpace K V) {L : Submodule (𝓞 K) V} (hU : IsUnimod H L) (S : Submodule K V)
    (φ : ↥(L ⊓ rs (𝓞 K) S) →ₗ[𝓞 K] 𝓞 K) :
    ∃ y ∈ L, ∀ x : ↥(L ⊓ rs (𝓞 K) S), H.B x y = (φ x : K) := by
  have hL : Submodule.IsFullLattice K L := by
    obtain ⟨⟨N, hN, hLN⟩, hspan⟩ := hU.1
    have h : L = N := by simpa only [rs, Submodule.restrictScalars_bot, sup_bot_eq] using hLN
    exact { toIsLattice := Submodule.IsLattice.of_fg K (h.symm ▸ hN), span_eq_top := hspan }
  obtain ⟨ψ, hψ⟩ := exists_extension hL S φ
  have := isLocalizedModule_subtype hL
  have hu : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) K) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (Algebra.linearMap (𝓞 K) K) x
  let f : V →ₗ[K] K := LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K
      (IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) L.subtype (Algebra.linearMap (𝓞 K) K ∘ₗ ψ) hu)
  have hf : ∀ y : L, f y = algebraMap (𝓞 K) K (ψ y) := fun y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 K)) L.subtype _ hu y
  obtain ⟨y, hy⟩ := exists_rep H f
  refine ⟨y, ?_, fun x => ?_⟩
  · rw [← hU.2, mem_dual_iff]
    refine ⟨by rw [hL.span_eq_top]; trivial, fun x hx => ?_⟩
    rw [← H.herm, hy]
    apply star_mem_one
    rw [hf ⟨x, hx⟩]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  · rw [hy, ← hψ]
    exact hf ⟨x, x.2.1⟩

theorem isUnimodMod_quot (H : HermSpace K V) {L : Submodule (𝓞 K) V} (hU : IsUnimod H L) {I : Submodule K V}
    (hI : ∀ x ∈ I, ∀ y ∈ I, H.B x y = 0) :
    IsUnimodMod H ((L ⊓ rs (𝓞 K) (perp H I)) ⊔ rs (𝓞 K) I) (perp H I) I := by
  have hL : Submodule.IsFullLattice K L := by
    obtain ⟨⟨N, hN, hLN⟩, hspan⟩ := hU.1
    have h : L = N := by simpa only [rs, Submodule.restrictScalars_bot, sup_bot_eq] using hLN
    exact { toIsLattice := Submodule.IsLattice.of_fg K (h.symm ▸ hN), span_eq_top := hspan }
  have hint : ∀ y ∈ L, ∀ x ∈ L, H.B y x ∈ (1 : Submodule (𝓞 K) K) := by
    intro y hy
    rw [← hU.2, mem_dual_iff] at hy
    exact hy.2
  have hIp : I ≤ perp H I := fun x hx => (mem_perp_iff H I x).2 (hI x hx)
  have hsat : ∀ v ∈ perp H I, ∃ c : K, c ≠ 0 ∧ c • v ∈ L ⊓ rs (𝓞 K) (perp H I) := by
    intro v hv
    obtain ⟨s, hs⟩ := exists_smul_mem hL v
    refine ⟨algebraMap (𝓞 K) K s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, ?_,
      (perp H I).smul_mem _ hv⟩
    rw [algebraMap_smul]
    exact hs
  have hspan : Submodule.span K (((L ⊓ rs (𝓞 K) (perp H I)) ⊔ rs (𝓞 K) I : Submodule (𝓞 K) V) : Set V)
      = perp H I := by
    apply le_antisymm
    · rw [Submodule.span_le]
      have : (L ⊓ rs (𝓞 K) (perp H I)) ⊔ rs (𝓞 K) I ≤ rs (𝓞 K) (perp H I) := sup_le inf_le_right hIp
      exact this
    · intro v hv
      obtain ⟨c, hc, h⟩ := hsat v hv
      rw [← Submodule.smul_mem_iff _ hc]
      exact Submodule.subset_span (Submodule.mem_sup_left h)
  refine ⟨⟨⟨_, ?_, rfl⟩, hspan⟩, ?_⟩
  · have : Module.Finite (𝓞 K) L := Submodule.IsLattice.finite K L
    have : IsNoetherian (𝓞 K) L := inferInstance
    have : IsNoetherian (𝓞 K) ↥(L ⊓ rs (𝓞 K) (perp H I)) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  ext y
  rw [mem_dual_iff, hspan]
  constructor
  · rintro ⟨hy, hyM⟩
    have hx : ∀ x : ↥(L ⊓ rs (𝓞 K) (perp H I)), IsIntegral ℤ (H.B x y) := by
      intro x
      rw [← mem_one_iff, ← H.herm]
      exact star_mem_one (hyM x (Submodule.mem_sup_left x.2))
    let φ : ↥(L ⊓ rs (𝓞 K) (perp H I)) →ₗ[𝓞 K] 𝓞 K :=
      { toFun := fun x => ⟨H.B x y, hx x⟩
        map_add' := fun a b => by
          apply RingOfIntegers.ext
          show H.B ((a : V) + b) y = H.B a y + H.B b y
          simp
        map_smul' := fun a b => by
          apply RingOfIntegers.ext
          show H.B (a • (b : V)) y = algebraMap (𝓞 K) K a * H.B b y
          rw [← algebraMap_smul K a, map_smul]
          rfl }
    obtain ⟨y', hy', h'⟩ := exists_lattice_rep H hU (perp H I) φ
    have hd : y - y' ∈ I := by
      apply mem_of_perp_perp H I
      intro v hv
      obtain ⟨c, hc, h⟩ := hsat v hv
      have h1 : H.B (c • v) y' = H.B (c • v) y := h' ⟨_, h⟩
      rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply] at h1
      rw [map_sub, smul_right_injective K hc h1, sub_self]
    have hy'p : y' ∈ perp H I := by
      have := (perp H I).sub_mem hy (hIp hd)
      simpa using this
    exact Submodule.mem_sup.2 ⟨y', ⟨hy', hy'p⟩, y - y', hd, by abel⟩
  · intro hy
    obtain ⟨a, ⟨haL, hap⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    refine ⟨(perp H I).add_mem hap (hIp hb), fun x hx => ?_⟩
    obtain ⟨c, ⟨hcL, hcp⟩, d, hd, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 : H.B a d = 0 := (mem_perp_iff H I a).1 hap d hd
    have h2 : H.B b c = 0 := by rw [← H.herm, (mem_perp_iff H I c).1 hcp b hb, star_zero]
    have h3 : H.B b d = 0 := hI b hb d hd
    simp only [map_add (f := _), LinearMap.add_apply, h1, h2, h3, add_zero]
    exact hint a haL c hcL

end GlobalTheory.UnimodQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMass
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.GenusOrb

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem _root_.GlobalTheory.Mass.GenusOrb.trace_pos_of_PD (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hp : _root_.GlobalTheory.Mass.PD h) (x : V) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (h x x) := by
  have hp' : ∀ (τ : K →+* ℂ) (x : V), x ≠ 0 → 0 < (τ ((h x) x)).re := hp
  have hsum := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := h x x)
  have hre : (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re =
      (Algebra.trace ℚ K (h x x) : ℝ) := by simp
  have hpos : (0 : ℝ) < (Algebra.trace ℚ K (h x x) : ℝ) := by
    rw [← hre, hsum, Complex.re_sum]
    obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
    haveI : Nonempty (K →ₐ[ℚ] ℂ) := ⟨φ.toRatAlgHom⟩
    exact Finset.sum_pos (fun σ _ => hp' σ.toRingHom x hx) Finset.univ_nonempty
  exact_mod_cast hpos

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def autEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) :
    Formalism.ThetaLiftIndependence.autL h M ≃ MulAction.stabilizer (isom h) M where
  toFun g := ⟨⟨g.1, g.2.1⟩, g.2.2⟩
  invFun g := ⟨g.1.1, g.1.2, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end

theorem _root_.GlobalTheory.Mass.GenusOrb.main : ∀ (K V : Type) [Field K] [NumberField K]
    [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm →
    _root_.GlobalTheory.Mass.PD h → ∀ L : Submodule (𝓞 K) V, Submodule.IsFullLattice K L →
    ENNReal.ofReal (_root_.Formalism.HermitianLatticesTheory.mass h L) = _root_.GlobalTheory.Mass.orbMass (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) ∧
    0 < _root_.Formalism.HermitianLatticesTheory.mass h L ∧ _root_.GlobalTheory.Mass.Stable (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) ∧
    (∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M →
      Finite (MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) M)) ∧
    ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞), _root_.Formalism.ThetaLiftIndependence.IsClassReps h L s →
      (∀ (g : _root_.Formalism.HermitianLatticesTheory.isom h) M, N (g • M) = N M) →
      ∑ M ∈ s, ENNReal.ofReal ((Nat.card (_root_.Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M =
        _root_.GlobalTheory.Mass.orbSum (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) N := by
  intro K V _ _ _ _ _ _ _ _ h _ hsymm hp L hL
  have htr : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) :=
    _root_.GlobalTheory.Mass.GenusOrb.trace_pos_of_PD h hp
  have hmass := by
    first
    | exact _root_.Formalism.HermitianLatticesTheory.final_massBasic K V h hsymm htr L hL
    | exact _root_.Formalism.HermitianLatticesTheory.final_massBasic K V h hsymm htr L hL.toIsLattice
  obtain ⟨hmass_ex, hmass_eq, hmass_pos⟩ := hmass
  have hgen : ∀ g ∈ _root_.Formalism.HermitianLatticesTheory.isom h, ∀ M ∈ _root_.Formalism.HermitianLatticesTheory.genus h L, _root_.Formalism.HermitianLatticesTheory.gmap g M ∈ _root_.Formalism.HermitianLatticesTheory.genus h L := by
    intro g hg M hM
    obtain ⟨hML, hLM⟩ := hM
    obtain ⟨heq, hinv, -⟩ := _root_.Formalism.HermitianLatticesTheory.final_genusBasic (𝓞 K) K V h hsymm _root_.Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
    have hfull : Submodule.IsFullLattice K (_root_.Formalism.HermitianLatticesTheory.gmap g M) := by
      refine { toIsLattice := (_root_.Formalism.HermitianLatticesTheory.final_isomAct (𝓞 K) K V h g hg M).2.2.2.2.mpr hML.toIsLattice, span_eq_top := ?_ }
      have he : ((_root_.Formalism.HermitianLatticesTheory.gmap g M : Submodule (𝓞 K) V) : Set V) = g '' (M : Set V) := by
        ext x
        simp [_root_.Formalism.HermitianLatticesTheory.gmap]
      rw [he]
      change Submodule.span K ((g : V →ₗ[K] V) '' (M : Set V)) = ⊤
      rw [← Submodule.map_span, hML.span_eq_top, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr g.surjective
    exact show Submodule.IsFullLattice K (_root_.Formalism.HermitianLatticesTheory.gmap g M) ∧ _root_.Formalism.HermitianLatticesTheory.SameGenus h L (_root_.Formalism.HermitianLatticesTheory.gmap g M) from
      ⟨hfull, heq.trans hLM (hinv M g hg)⟩
  have hstab : _root_.GlobalTheory.Mass.Stable (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) := fun g M hM => hgen g.1 g.2 M hM
  have hfin : ∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M →
      Finite (MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) M) := by
    intro M hM
    have hS := _root_.Formalism.HermitianLatticesTheory.final_autFinite K V h hsymm htr M hM
    haveI := hS.to_subtype
    refine Finite.of_injective (fun g : MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) M =>
      (⟨g.1.1, g.1.2, g.2⟩ : {g | g ∈ _root_.Formalism.HermitianLatticesTheory.isom h ∧ _root_.Formalism.HermitianLatticesTheory.gmap g M = M})) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have hsum : ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞),
      _root_.Formalism.ThetaLiftIndependence.IsClassReps h L s → (∀ (g : _root_.Formalism.HermitianLatticesTheory.isom h) M, N (g • M) = N M) →
      ∑ M ∈ s, ENNReal.ofReal ((Nat.card (_root_.Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M =
        _root_.GlobalTheory.Mass.orbSum (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) N := by
    intro s N hs hN
    obtain ⟨hsub, huniq⟩ := hs
    rw [_root_.GlobalTheory.Mass.orbSum_eq_sum_reps (_root_.Formalism.HermitianLatticesTheory.isom h) _ _ N hstab hN s hsub ?_]
    · refine Finset.sum_congr rfl fun M hM => ?_
      congr 1
      obtain ⟨hMlat, -⟩ := hsub M hM
      haveI := hfin M hMlat
      haveI : Finite (_root_.Formalism.ThetaLiftIndependence.autL h M) :=
        Finite.of_equiv _ (_root_.GlobalTheory.Mass.GenusOrb.autEquiv h M).symm
      haveI : Nonempty (_root_.Formalism.ThetaLiftIndependence.autL h M) := ⟨(_root_.GlobalTheory.Mass.GenusOrb.autEquiv h M).symm 1⟩
      have hpos : (0 : ℝ) < (Nat.card (_root_.Formalism.ThetaLiftIndependence.autL h M) : ℝ) := by exact_mod_cast Nat.card_pos
      rw [← ENat.card_congr (_root_.GlobalTheory.Mass.GenusOrb.autEquiv h M), ENat.card_eq_coe_natCard,
        ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_natCast]
      norm_cast
    · intro M hM
      obtain ⟨y, ⟨hy, g, hg, hgy⟩, huy⟩ := huniq M hM
      exact ⟨y, ⟨hy, ⟨g, hg⟩, hgy⟩, fun z ⟨hz, g', hg'⟩ => huy z ⟨hz, g'.1, g'.2, hg'⟩⟩
  obtain ⟨s, hs⟩ := hmass_ex
  have h1 : ENNReal.ofReal (_root_.Formalism.HermitianLatticesTheory.mass h L) = _root_.GlobalTheory.Mass.orbMass (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) := by
    rw [hmass_eq s hs, ENNReal.ofReal_sum_of_nonneg (fun M _ => by positivity)]
    have := hsum s (fun _ => 1) hs (fun _ _ => rfl)
    simp only [mul_one] at this
    rw [this]
    rfl
  exact ⟨h1, hmass_pos, hstab, hfin, hsum⟩

end GlobalTheory.Mass.GenusOrb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianGenusMassEqOrbitStabilizerMassStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianGenusMass_eq_orbitStabilizerMass : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, Submodule.IsFullLattice K L → ENNReal.ofReal (mass h L) = orbMass (isom h) (genus h L) ∧ 0 < mass h L ∧ Stable (isom h) (genus h L) ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M → Finite (MulAction.stabilizer (isom h) M)) ∧ ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞), Formalism.ThetaLiftIndependence.IsClassReps h L s → (∀ (g : isom h) M, N (g • M) = N M) → ∑ M ∈ s, ENNReal.ofReal ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M = orbSum (isom h) (genus h L) N := by
  first
  | exact @GlobalTheory.Mass.GenusOrb.main
  | intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL
    obtain ⟨a, b, c, d, e⟩ := GlobalTheory.Mass.GenusOrb.main K V h hK hs hp L hL.toIsLattice
    exact ⟨a, b, c, fun M hM => d M hM.toIsLattice, e⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetFromBlocksSingle
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Matrix

namespace GlobalTheory.SA.TransvG

section Det

variable {K : Type} [CommRing K]

theorem det_fromBlocks_swap {n : Type} [Fintype n] [DecidableEq n] (P A B D : Matrix n n K) :
    (fromBlocks P A B D).det = (fromBlocks (-A) P (-D) B).det := by
  have h : fromBlocks (-A) P (-D) B = fromBlocks P A B D * (fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 *
      fromBlocks 1 1 0 1 : Matrix (n ⊕ n) (n ⊕ n) K) := by
    simp [fromBlocks_multiply]
  rw [h]
  simp [det_mul]

theorem det_updateRow_last {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (X.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).det = (X.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h : (X.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      X.submatrix Fin.castSucc Fin.castSucc := by
    ext a b
    simp
  simp [Fin.castSucc_ne_last, h, ← two_mul]

theorem det_fromBlocks_single {n : Type} [Fintype n] [DecidableEq n] (l : n) (X Y : Matrix n n K) (t s : K) :
    (fromBlocks X (diagonal fun a => if a = l then t else 0) (diagonal fun a => if a = l then s else 0) Y).det =
      X.det * Y.det - t * s * ((X.updateRow l (Pi.single l 1)).det * (Y.updateRow l (Pi.single l 1)).det) := by
  have e1 : fromBlocks X (diagonal fun a => if a = l then t else 0) (diagonal fun a => if a = l then s else 0) Y =
      (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y).updateRow (Sum.inl l)
        (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y (Sum.inl l) +
          t • Pi.single (Sum.inr l) 1) := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, ha, hb, @eq_comm _ l b]
  have e2 : (fromBlocks X 0 (diagonal fun a => if a = l then s else 0) Y).updateRow (Sum.inl l)
        (Pi.single (Sum.inr l) 1) =
      (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y).updateRow (Sum.inr l)
        (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y (Sum.inr l) +
          s • Pi.single (Sum.inl l) 1) := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, ha, hb, @eq_comm _ l b]
  have e3 : (fromBlocks (X.updateRow l 0) (diagonal fun a => if a = l then 1 else 0) 0 Y).updateRow (Sum.inr l)
        (Pi.single (Sum.inl l) 1) =
      (fromBlocks (X.updateRow l (Pi.single l 1)) 0 0 (Y.updateRow l (Pi.single l 1))).submatrix
        (Equiv.swap (Sum.inl l) (Sum.inr l)) id := by
    ext (a | a) (b | b) <;> by_cases ha : a = l <;> by_cases hb : b = l <;>
      simp [updateRow_apply, diagonal_apply, Pi.single_apply, Equiv.swap_apply_def, ha, hb, @eq_comm _ l b]
  have e4 : (X.updateRow l 0).det = 0 := det_eq_zero_of_row_eq_zero l fun j => by simp
  rw [e1, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, det_fromBlocks_zero₁₂, e2,
    det_updateRow_add, det_updateRow_smul, updateRow_eq_self, det_fromBlocks_zero₂₁, e3, det_permute,
    det_fromBlocks_zero₂₁, Equiv.Perm.sign_swap (by simp), e4]
  simp
  ring

theorem det_fromBlocks_last {r : ℕ} (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (T T' : K) :
    (fromBlocks (diagonal fun a => if a = Fin.last r then -T else 0) A B
      (diagonal fun a => if a = Fin.last r then -T' else 0)).det =
      (-1) ^ (r + 1) * (A.det * B.det - T * T' *
        ((A.submatrix Fin.castSucc Fin.castSucc).det * (B.submatrix Fin.castSucc Fin.castSucc).det)) := by
  have h : (-diagonal fun a => if a = Fin.last r then -T' else 0) =
      diagonal fun a => if a = Fin.last r then T' else 0 := by
    ext a b
    simp only [Matrix.neg_apply, diagonal_apply]
    split_ifs <;> simp
  have h2 : (-A).submatrix Fin.castSucc Fin.castSucc = -A.submatrix Fin.castSucc Fin.castSucc := rfl
  rw [det_fromBlocks_swap, h, det_fromBlocks_single, det_updateRow_last, det_updateRow_last, h2, det_neg, det_neg]
  simp only [Fintype.card_fin]
  ring

end Det

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

end GlobalTheory.SA.TransvG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolEqInfMulSupAndMono
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.IndexProd

theorem relIndex_eq_of_forall_mul {G : Type*} [Group G] {D N E : Subgroup G} (hNE : N ≤ E)
    (h : ∀ e ∈ E, ∃ n ∈ N, ∃ d ∈ D, n * d = e) : D.relIndex E = D.relIndex N := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (Subgroup.quotientSubgroupOfEmbeddingOfLE D hNE)
    ⟨(Subgroup.quotientSubgroupOfEmbeddingOfLE D hNE).injective, ?_⟩)
  intro q
  induction q using QuotientGroup.induction_on with
  | H e =>
    obtain ⟨n, hn, d, hd, hnd⟩ := h e e.2
    refine ⟨QuotientGroup.mk ⟨n, hn⟩, ?_⟩
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [← hnd] using hd

theorem exists_mul_of_mem_sup {G : Type*} [Group G] {A M : Subgroup G}
    (h : ∀ s ∈ A, ∀ t ∈ M, s * t * s⁻¹ ∈ M) {x : G} (hx : x ∈ A ⊔ M) :
    ∃ a ∈ A, ∃ m ∈ M, a * m = x := by
  have hle : A ≤ Subgroup.normalizer M := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨h s hs t, fun ht => ?_⟩
    have := h s⁻¹ (A.inv_mem hs) _ ht
    simpa [mul_assoc] using this
  have hx' : x ∈ ((A ⊔ M : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A M hle] at hx'
  obtain ⟨a, ha, m, hm, e⟩ := hx'
  exact ⟨a, ha, m, hm, e⟩

theorem relIndex_eq_inf_mul_sup {G : Type*} [Group G] {D A M : Subgroup G} (hDA : D ≤ A)
    (h : ∀ s ∈ A, ∀ t ∈ M, s * t * s⁻¹ ∈ M) :
    D.relIndex A = (D ⊓ M).relIndex (A ⊓ M) * (D ⊔ M).relIndex (A ⊔ M) := by
  have h1 : (D ⊔ M).relIndex (A ⊔ M) = (D ⊔ M).relIndex A :=
    relIndex_eq_of_forall_mul le_sup_left fun e he => by
      obtain ⟨a, ha, m, hm, e⟩ := exists_mul_of_mem_sup h he
      exact ⟨a, ha, m, (le_sup_right : M ≤ D ⊔ M) hm, e⟩
  have h2 : D.relIndex ((D ⊔ M) ⊓ A) = D.relIndex (A ⊓ M) :=
    relIndex_eq_of_forall_mul (le_inf (inf_le_right.trans le_sup_right) inf_le_left)
      fun e he => by
        obtain ⟨d, hd, m, hm, e'⟩ := exists_mul_of_mem_sup (fun s hs => h s (hDA hs)) he.1
        refine ⟨d * m * d⁻¹, ⟨?_, h d (hDA hd) m hm⟩, d, hd, by rw [← e']; simp⟩
        rw [e']
        exact A.mul_mem he.2 (A.inv_mem (hDA hd))
  have h3 : (D ⊓ M).relIndex (A ⊓ M) = D.relIndex (A ⊓ M) := by
    rw [← Subgroup.inf_relIndex_right D, ← Subgroup.inf_relIndex_right (D ⊓ M)]
    congr 1
    rw [inf_comm A M, ← inf_assoc, ← inf_assoc, inf_assoc D M M, inf_idem]
  rw [h1, h3, ← h2, Subgroup.relIndex_inf_mul_relIndex, inf_eq_left.2 le_sup_left]

theorem invVol_eq_inf_mul_sup_and_mono : ∀ (G : Type) [Group G] (R M A B : Subgroup G), M ≤ R → A ≤ R → B ≤ R → (∀ s ∈ R, ∀ t ∈ M, s * t * s⁻¹ ∈ M) → A.relIndex B ≠ 0 → B.relIndex A ≠ 0 → GlobalTheory.HL.invVol A B = GlobalTheory.HL.invVol (A ⊓ M) (B ⊓ M) * GlobalTheory.HL.invVol (A ⊔ M) (B ⊔ M) ∧ ∀ B' ≤ B, B'.relIndex A ≠ 0 → A.relIndex B' ≠ 0 → GlobalTheory.HL.invVol A B ≤ GlobalTheory.HL.invVol A B' ∧ GlobalTheory.HL.invVol A B ≤ (B'.relIndex A : ℝ) := by
  intro G _ R M A B _ hA hB hn hAB hBA
  constructor
  · have eA := relIndex_eq_inf_mul_sup (D := A ⊓ B) (M := M) inf_le_left
      (fun s hs => hn s (hA hs))
    have eB := relIndex_eq_inf_mul_sup (D := A ⊓ B) (M := M) inf_le_right
      (fun s hs => hn s (hB hs))
    have dA : (A ⊓ B).relIndex A ≠ 0 := by rwa [Subgroup.inf_relIndex_left]
    have dA' := dA
    rw [eA, mul_ne_zero_iff] at dA'
    rw [GlobalTheory.HL.invVol_eq_div_of_le inf_le_left inf_le_right dA,
      GlobalTheory.HL.invVol_eq_div_of_le (inf_le_inf_right M inf_le_left)
        (inf_le_inf_right M inf_le_right) dA'.1,
      GlobalTheory.HL.invVol_eq_div_of_le (sup_le_sup_right inf_le_left M)
        (sup_le_sup_right inf_le_right M) dA'.2, eA, eB]
    push_cast
    rw [div_mul_div_comm]
  · intro B' hB' h1 h2
    have dA : (A ⊓ B').relIndex A ≠ 0 := by rwa [Subgroup.inf_relIndex_left]
    have dB : (A ⊓ B').relIndex B ≠ 0 :=
      Subgroup.relIndex_inf_ne_zero hAB (Subgroup.relIndex_ne_zero_trans h1 hAB)
    have dB' : (A ⊓ B').relIndex B' ≠ 0 := by rwa [Subgroup.inf_relIndex_right]
    have hle : GlobalTheory.HL.invVol A B ≤ GlobalTheory.HL.invVol A B' := by
      rw [GlobalTheory.HL.invVol_eq_div_of_le inf_le_left (inf_le_right.trans hB') dA,
        GlobalTheory.HL.invVol_eq_div_of_le inf_le_left inf_le_right dA]
      refine div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.pos_of_ne_zero dB') ?_
      exact_mod_cast Subgroup.relIndex_le_of_le_right hB' dB
    refine ⟨hle, hle.trans ?_⟩
    rw [GlobalTheory.HL.invVol]
    exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast Nat.pos_of_ne_zero h2)

end GlobalTheory.IndexProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexCongruenceSubgroupLeAbsNormPow
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexCongruenceSubgroupLeAbsNormPow
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.CongIndex

open scoped TensorProduct in
theorem quot_smul_top_span_card {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    (∃ v : Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N), Submodule.span R (Set.range v) = ⊤) ∧
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  refine ⟨⟨(TensorProduct.quotTensorEquivQuotSMul N I) ∘ b, ?_⟩, ?_⟩
  · have h1 : Submodule.span R (Set.range b) = ⊤ := by
      rw [← Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective, b.span_eq,
        Submodule.restrictScalars_top]
    have h2 := congrArg (Submodule.map (TensorProduct.quotTensorEquivQuotSMul N I).toLinearMap) h1
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h2
    rw [Set.range_comp]
    exact h2
  · rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv,
      Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem card_hom_quot_smul_top {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Finite (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) ∧
    Nat.card (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) ≤ Nat.card (R ⧸ I) ^ (Module.finrank R N ^ 2) := by
  obtain ⟨⟨v, hv⟩, hc⟩ := quot_smul_top_span_card (R := R) (N := N) I
  have : Finite (N ⧸ (I • ⊤ : Submodule R N)) := Submodule.finite_quotient_smul I Module.Finite.fg_top
  have hk : ∀ f : N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N), (I • ⊤ : Submodule R N) ≤ LinearMap.ker f := by
    intro f
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (f x)
    rw [LinearMap.mem_ker, map_smul, ← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  let Φ : (N →ₗ[R] N ⧸ (I • ⊤ : Submodule R N)) → (Fin (Module.finrank R N) → N ⧸ (I • ⊤ : Submodule R N)) :=
    fun f i => Submodule.liftQ _ f (hk f) (v i)
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    have : Submodule.liftQ _ f (hk f) = Submodule.liftQ _ g (hk g) :=
      LinearMap.ext_on_range hv fun i => congrFun hfg i
    ext x
    simpa using LinearMap.congr_fun this (Submodule.Quotient.mk x)
  refine ⟨Finite.of_injective Φ hΦ, (Nat.card_le_card_of_injective Φ hΦ).trans_eq ?_⟩
  rw [Nat.card_fun, hc, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin, ← pow_mul, sq]

theorem finrank_le_finrank_span {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) :
    Module.finrank (𝓞 K) M ≤ Module.finrank K (Submodule.span K (M : Set V)) := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := M) le_rfl
  have h1 : LinearIndependent (𝓞 K) (M.subtype ∘ f) := hf.map' _ (Submodule.ker_subtype M)
  have h2 : LinearIndependent K (M.subtype ∘ f) := (LinearIndependent.iff_fractionRing (𝓞 K) K).1 h1
  let g : Fin (Module.finrank (𝓞 K) M) → Submodule.span K (M : Set V) :=
    fun i => ⟨f i, Submodule.subset_span (f i).2⟩
  have h3 : LinearIndependent K g :=
    LinearIndependent.of_comp (Submodule.span K (M : Set V)).subtype h2
  simpa using h3.fintype_card_le_finrank

theorem relIndex_le : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (G : Subgroup (V ≃ₗ[K] V)) (M : Submodule (𝓞 K) V) (𝔪 : Ideal (𝓞 K)) (B : Subgroup (V ≃ₗ[K] V)), M.FG → 𝔪 ≠ ⊥ → (∀ s ∈ G, s • M = M) → (∀ s ∈ G, (∀ x ∈ M, s x - x ∈ 𝔪 • M) → s ∈ B) → B.relIndex G ≠ 0 ∧ B.relIndex G ≤ Ideal.absNorm 𝔪 ^ (Module.finrank K (Submodule.span K (M : Set V)) ^ 2) := by
  intro K V _ _ _ _ _ _ _ G M 𝔪 B hM h𝔪 hG hB
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.2 hM
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.Flat (𝓞 K) M := inferInstance
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 K ⧸ 𝔪) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪 h𝔪
  obtain ⟨hfin, hcard⟩ := card_hom_quot_smul_top (R := 𝓞 K) (N := M) 𝔪
  have hmem : ∀ s ∈ G, ∀ x ∈ M, s x ∈ M := by
    intro s hs x hx
    rw [← hG s hs]
    exact Submodule.smul_mem_pointwise_smul x s M hx
  have hmem' : ∀ s ∈ G, ∀ x ∈ 𝔪 • M, s x ∈ 𝔪 • M := by
    intro s hs x hx
    refine Submodule.smul_induction_on hx (fun a ha y hy => ?_) (fun y z hy hz => ?_)
    · rw [LinearMapClass.map_smul_of_tower]
      exact Submodule.smul_mem_smul ha (hmem s hs y hy)
    · rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  let ρ : G → (M →ₗ[𝓞 K] M) := fun s =>
    (((s : V ≃ₗ[K] V) : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict (hmem s s.2)
  let Φ : G → (M →ₗ[𝓞 K] M ⧸ (𝔪 • ⊤ : Submodule (𝓞 K) M)) := fun s => (Submodule.mkQ _).comp (ρ s)
  have hΦ : ∀ s t : G, Φ s = Φ t → s⁻¹ * t ∈ B.subgroupOf G := by
    intro s t hst
    refine hB _ (s⁻¹ * t).2 fun x hx => ?_
    have h1 : ρ t ⟨x, hx⟩ - ρ s ⟨x, hx⟩ ∈ (𝔪 • ⊤ : Submodule (𝓞 K) M) :=
      (Submodule.Quotient.eq _).1 (LinearMap.congr_fun hst ⟨x, hx⟩).symm
    have h2 : (t : V ≃ₗ[K] V) x - (s : V ≃ₗ[K] V) x ∈ 𝔪 • M := by
      have := Submodule.mem_map_of_mem (f := M.subtype) h1
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
      exact this
    have h3 := hmem' _ (s⁻¹).2 _ h2
    simpa using h3
  let Ψ : G ⧸ B.subgroupOf G → _ := fun q => Φ q.out
  have hΨ : Function.Injective Ψ := by
    intro q q' h
    rw [← q.out_eq, ← q'.out_eq]
    exact QuotientGroup.eq.2 (hΦ _ _ h)
  have : Finite (G ⧸ B.subgroupOf G) := Finite.of_injective Ψ hΨ
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  refine (Nat.card_le_card_of_injective Ψ hΨ).trans (hcard.trans ?_)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.pow_le_pow_right Nat.card_pos (Nat.pow_le_pow_left (finrank_le_finrank_span M) 2)

end GlobalTheory.CongIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexCongruenceSubgroupLeAbsNormPowStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_congruence_subgroup_le_absNorm_pow : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (G : Subgroup (V ≃ₗ[K] V)) (M : Submodule (𝓞 K) V) (𝔪 : Ideal (𝓞 K)) (B : Subgroup (V ≃ₗ[K] V)), M.FG → 𝔪 ≠ ⊥ → (∀ s ∈ G, s • M = M) → (∀ s ∈ G, (∀ x ∈ M, s x - x ∈ 𝔪 • M) → s ∈ B) → B.relIndex G ≠ 0 ∧ B.relIndex G ≤ Ideal.absNorm 𝔪 ^ (Module.finrank K (Submodule.span K (M : Set V)) ^ 2) := by
  first | exact @GlobalTheory.CongIndex.relIndex_le | exact GlobalTheory.CongIndex.relIndex_le | (intros; apply GlobalTheory.CongIndex.relIndex_le <;> assumption)
end
end
