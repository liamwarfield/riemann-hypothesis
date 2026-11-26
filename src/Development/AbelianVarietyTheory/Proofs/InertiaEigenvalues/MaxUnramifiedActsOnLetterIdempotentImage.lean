module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxUnramifiedActsOnLetterIdempotentImage
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxUnramifiedActsOnLetterIdempotentImage
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

namespace GlobalTheory.HWL.Letter

variable {l : ℕ} [Fact l.Prime]

theorem lin_ext (K : FinExt l) {M : Type} [AddCommGroup M] [Module ℚ_[l] M] (σ τ : ↥(K0 K) →ₗ[ℚ_[l]] M)
    (h : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 → σ c = τ c) (c : ↥(K0 K)) :
    σ c = τ c := by
  have h1 : ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 → σ c = τ c := by
    intro c hc
    obtain ⟨n, z, ω, hω, hsum⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K c c.2 hc
    have h2 : c = ∑ i, (z i : ℚ_[l]) • (⟨ω i, (hω i).1⟩ : ↥(K0 K)) := by
      apply Subtype.ext
      rw [hsum]
      push_cast
      simp only [Algebra.smul_def]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨m, hm, hl, hx⟩ := (hω i).2
    rw [map_smul, map_smul, h _ m hm hl hx]
  have hl : ‖(l : Om l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖(c : Om l)‖
  rw [zero_mul] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds one_pos)).exists
  have h3 := h1 (((l : ℚ_[l]) ^ n) • c) (by
    rw [Algebra.smul_def]
    push_cast
    rwa [norm_mul, norm_pow])
  rw [map_smul, map_smul] at h3
  have h0 : ((l : ℚ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  rw [← inv_smul_smul₀ h0 (σ c), h3, inv_smul_smul₀ h0]

theorem mul_ext (K : FinExt l) {L B : Type} [Field L] [Algebra ℚ_[l] L] [CommRing B] [Algebra ℚ_[l] B]
    (e : ↥(K0 K) →ₐ[ℚ_[l]] L) (f : ↥(K0 K) →ₐ[ℚ_[l]] B) (x : L ⊗[ℚ_[l]] B)
    (h : ∀ (c : ↥(K0 K)) (m : ℕ), 0 < m → ¬ l ∣ m → (c : Om l) ^ m = 1 →
      ((1 : L) ⊗ₜ[ℚ_[l]] f c) * x = e c • x) (c : ↥(K0 K)) : ((1 : L) ⊗ₜ[ℚ_[l]] f c) * x = e c • x :=
  lin_ext K ((LinearMap.mulRight ℚ_[l] x).comp ((TensorProduct.mk ℚ_[l] L B 1).comp f.toLinearMap))
    (((LinearMap.toSpanSingleton L _ x).restrictScalars ℚ_[l]).comp e.toLinearMap) h c

theorem const_mul_letE {O : Type} [CommRing O] {n : ℕ} (o : ZMod n → O) (i : ZMod n) :
    (fun j => PowerSeries.C (o j) : LetA O n) * letE i = algebraMap O (LetA O n) (o i) * letE i := by
  funext j
  by_cases hj : j = i
  · subst hj; rfl
  · simp [letE, hj]

theorem step {O R Q L B : Type} [CommRing O] [CommRing R] [Algebra O R] [Field Q] [Field L] [Algebra Q L]
    [CommRing B] [Algebra Q B] {n : ℕ} (io : LetA O n →ₐ[O] R) (β : R →+* L ⊗[Q] B) (o : ZMod n → O)
    (i : ZMod n) (a : L) (b : B) (h3 : β (io (fun j => PowerSeries.C (o j))) = (1 : L) ⊗ₜ[Q] b)
    (h5 : β (algebraMap O R (o i)) = a ⊗ₜ[Q] (1 : B)) :
    ((1 : L) ⊗ₜ[Q] b) * β (io (letE i)) = a • β (io (letE i)) := by
  rw [← h3, ← map_mul, ← map_mul, const_mul_letE, map_mul, AlgHom.commutes, map_mul, h5, Algebra.smul_def]
  rfl

theorem letter : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (c : ↥(K0 K)), ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.B c) * β (I.io (letE i)) = Γ.emb i c • β (I.io (letE i)) := by
  intro l _ P AI _ K s LL _ Γ R I hI β hβ i c
  refine mul_ext K (Γ.emb i) (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B) _ (fun c m hm hl hc => ?_) c
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hc
  have hc' : c ^ m = 1 := by exact_mod_cast hc
  obtain ⟨o, ho⟩ := GlobalTheory.UnramIdem.exists_vec Γ.emb hm hc'
  have h1 := hI c m hm hl hc xb hxb o ho
  have h2 : AI.ιA (WittVector.teichmuller l xb) = algebraMap ↥(K0 K) P.R.B c :=
    AI.ιA_teich ⟨c, c.2.2⟩ m hm hl hc xb hxb
  have h3 := hβ 1 (WittVector.teichmuller l xb)
  have h5 := hβ (o i) 1
  rw [map_one, ho] at h5
  rw [h2] at h3
  exact step I.io β o i _ _ ((congrArg β h1).trans h3) h5

end GlobalTheory.HWL.Letter
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxUnramifiedActsOnLetterIdempotentImageStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxUnramified_acts_on_letterIdempotent_image : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (c : ↥(K0 K)), ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.B c) * β (I.io (letE i)) = Γ.emb i c • β (I.io (letE i)) := by
  first | exact @GlobalTheory.HWL.Letter.letter | exact GlobalTheory.HWL.Letter.letter | (intros; apply GlobalTheory.HWL.Letter.letter <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelAllLeInf
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology Pointwise

namespace GlobalTheory.SelInfl

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))} {R : Type} [CommRing R] {M : Type}
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M] [T2Space M] (rhoS : Representation R (GS Ω S) M) (A : Places F Ω)

theorem vanish {f : G F Ω → M} (hf : f ∈ Z1 (rhoS.comp (toGS Ω S) : Representation R (G F Ω) M))
    (hv0 : ∀ v ∉ S, ∃ m, ∀ g ∈ Ine (F := F) (A.1 v), f g = rhoS (toGS Ω S g) m - m) (n : G F Ω)
    (hn : n ∈ NS Ω S) : f n = 0 := by
  obtain ⟨hfc, hfco⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ f).1 hf
  have ht : ∀ g ∈ NS Ω S, toGS Ω S g = 1 := fun g hg => (QuotientGroup.eq_one_iff g).2 hg
  have hρ : ∀ g ∈ NS Ω S, ∀ x : M, (rhoS.comp (toGS Ω S)) g x = x := by
    intro g hg x
    rw [MonoidHom.comp_apply, ht g hg, map_one, Module.End.one_apply]
  have h1 : f 1 = 0 := by
    have := hfco 1 1
    rw [mul_one, map_one, Module.End.one_apply] at this
    simpa using this
  have hinv : ∀ a ∈ NS Ω S, f a = 0 → f a⁻¹ = 0 := by
    intro a ha h0
    have := hfco a a⁻¹
    rw [mul_inv_cancel, h1, h0, zero_add, hρ a ha] at this
    exact this.symm
  let H : Subgroup (G F Ω) :=
    { carrier := {g | g ∈ NS Ω S ∧ f g = 0}
      one_mem' := ⟨(NS Ω S).one_mem, h1⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨(NS Ω S).mul_mem ha.1 hb.1, by rw [hfco, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨(NS Ω S).inv_mem ha.1, hinv a ha.1 ha.2⟩ }
  have hconj : ∀ n ∈ H, ∀ g : G F Ω, g * n * g⁻¹ ∈ H := by
    intro n hn g
    refine ⟨(normal_NS S).conj_mem n hn.1 g, ?_⟩
    have e1 := hfco (g * n) g⁻¹
    have e2 := hfco g n
    have e3 := hfco g g⁻¹
    rw [map_mul, Module.End.mul_apply, hρ n hn.1, e2, hn.2, map_zero, add_zero] at e1
    rw [mul_inv_cancel, h1] at e3
    rw [e1, ← e3]
  have hHn : H.Normal := ⟨hconj⟩
  have hclosed : IsClosed (H : Set (G F Ω)) :=
    (isClosed_NS Ω S).inter (isClosed_singleton.preimage hfc)
  have hsub : (⋃ v ∈ Sᶜ, ⋃ A' ∈ {A' : ValuationSubring Ω | IsPlaceOver A' v}, Inertia (F := F) A') ⊆ H := by
    intro σ hσ
    have hσN : σ ∈ NS Ω S :=
      Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hσ)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hσ
    obtain ⟨v, hv, A', hA', hσA'⟩ := hσ
    obtain ⟨γ, hγ⟩ := exists_smul_eq_of_isPlaceOver (A.2 v) hA'
    have hσI : σ ∈ Ine (F := F) (γ • A.1 v) := by
      rw [hγ]
      exact mem_Ine.2 hσA'
    have hτ := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hσI
    have hτN : γ⁻¹ * σ * γ ∈ NS Ω S := by
      have := (normal_NS S).conj_mem σ hσN γ⁻¹
      rwa [inv_inv] at this
    obtain ⟨m, hm⟩ := hv0 v hv
    have hfτ : f (γ⁻¹ * σ * γ) = 0 := by
      rw [hm _ hτ, ht _ hτN, map_one, Module.End.one_apply, sub_self]
    have := hconj _ ⟨hτN, hfτ⟩ γ
    have e : γ * (γ⁻¹ * σ * γ) * γ⁻¹ = σ := by group
    rw [e] at this
    exact this
  have hle : NS Ω S ≤ H :=
    Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hsub) hclosed
  exact (hle hn).2

theorem selAllLeInf : Formalism.GaloisCohomology.SelAllLeInf := by
  intro F Ω _ _ _ _ _ S R _ M _ _ _ _ _ _ rhoS _ A L hL x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hloc := (ReciprocityTheory.Gal.mem_Sel _ _ _ _ _).1 hx
  have hv0 : ∀ v ∉ S, ∃ m, ∀ g ∈ Ine (F := F) (A.1 v), z.1 g = rhoS (toGS Ω S g) m - m := by
    intro v hv
    have h1 := hL v hv (hloc v)
    have h2 : (Submodule.Quotient.mk (restrictCocycles1 _ ((Ine (F := F) (A.1 v)).subgroupOf (Dec (F := F) (A.1 v))).subtype
        continuous_subtype_val (restrictCocycles1 _ (Dec (F := F) (A.1 v)).subtype continuous_subtype_val z)) :
        H1 _) = 0 := h1
    have h3 := (Submodule.Quotient.mk_eq_zero _).1 h2
    rw [Submodule.mem_comap] at h3
    obtain ⟨m, hm⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 h3
    refine ⟨m, fun g hg => ?_⟩
    have gD : g ∈ Dec (F := F) (A.1 v) := Ine_le_Dec _ hg
    have gJ : (⟨g, gD⟩ : Dec (F := F) (A.1 v)) ∈ (Ine (F := F) (A.1 v)).subgroupOf (Dec (F := F) (A.1 v)) := by
      rw [Subgroup.mem_subgroupOf]
      exact hg
    exact hm ⟨⟨g, gD⟩, gJ⟩
  have hvan : ∀ n ∈ NS Ω S, z.1 n = 0 := fun n hn => vanish rhoS A z.2 hv0 n hn
  obtain ⟨hzc, hzco⟩ := (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).1 z.2
  have hwd : ∀ a b : G F Ω, a⁻¹ * b ∈ NS Ω S → z.1 a = z.1 b := by
    intro a b hab
    have := hzco a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hvan _ hab, map_zero, add_zero] at this
    exact this.symm
  let z' : GS Ω S → M := fun q =>
    Quotient.liftOn' q z.1 (fun a b hab => hwd a b (QuotientGroup.leftRel_apply.1 hab))
  have hz'c : Continuous z' := Continuous.quotient_liftOn' hzc _
  have hz'co : ∀ p q : GS Ω S, z' (p * q) = z' p + rhoS p (z' q) := by
    intro p q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    exact hzco a b
  let w : Z1 rhoS := ⟨z', (ReciprocityTheory.Gal.mem_Z1_iff_cocycle _ _).2 ⟨hz'c, hz'co⟩⟩
  exact ⟨Submodule.Quotient.mk w, rfl⟩

end GlobalTheory.SelInfl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisOrbitWittTensorLatticeWeakTopolo
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAutCbCbTop
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section
open Filter Topology

namespace GlobalTheory.WeakClosed

theorem continuous_frac_act {A K G : Type} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [TopologicalSpace G] (τ : G → (A ≃+* A))
    (σ : G → (K ≃+* K)) (hσ : ∀ g a, σ g (algebraMap A K a) = algebraMap A K (τ g a))
    (ho : ∀ (x a : A) (g₀ : G), a ≠ 0 → ∀ᶠ g in 𝓝 g₀, ¬ (τ g x - τ g₀ x ∣ a)) :
    letI : Valued K (ValuationRing.ValueGroup A K) := Valued.mk' (ValuationRing.valuation A K)
    Continuous fun p : G × K => σ p.1 p.2 := by
  letI V : Valued K (ValuationRing.ValueGroup A K) := Valued.mk' (ValuationRing.valuation A K)
  have hle : ∀ x y : K, Valued.v x ≤ Valued.v y ↔ ∃ c : A, algebraMap A K c * y = x := by
    intro x y
    change (∃ c : A, c • y = x) ↔ _
    simp only [Algebra.smul_def]
  have hinj := IsFractionRing.injective A K
  refine GlobalTheory.WeakTop.continuous_act_of_orbits σ ?_ ?_
  · intro g x y
    simp only [← not_le, hle]
    rintro h ⟨c, hc⟩
    refine h ⟨(τ g).symm c, (σ g).injective ?_⟩
    rw [map_mul, hσ, RingEquiv.apply_symm_apply, hc]
  · have hA : ∀ x : A, Continuous fun g => σ g (algebraMap A K x) := by
      intro x
      rw [continuous_iff_continuousAt]
      intro g₀ s hs
      obtain ⟨c, hc, hs⟩ := GlobalTheory.WeakTop.mem_nhds_iff_lt.1 hs
      obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective A c
      have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hc
      rw [mem_map]
      filter_upwards [ho x a g₀ ha] with g hg
      apply hs
      change Valued.v (σ g (algebraMap A K x) - σ g₀ (algebraMap A K x)) < _
      rw [← not_le, hle, hσ, hσ, ← map_sub]
      rintro ⟨e, he⟩
      refine hg ⟨e * d, hinj ?_⟩
      rw [eq_div_iff hd0] at he
      rw [← he, map_mul, map_mul]
      ring
    intro x
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective A x
    have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    simp only [map_div₀]
    exact (hA a).div (hA d) fun g => by simpa using hd0

theorem continuous_autCb_cbTop : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P),
    letI := cbTop l; Continuous fun q : GQ l × Cb l => autCb l (AI.actT q.1) q.2 := by
  intro l _ P AI
  refine continuous_frac_act (A := OCb l) (fun g => AI.actT g) (fun g => autCb l (AI.actT g))
    (fun g a => autCb_alg l _ a) fun x a g₀ ha => ?_
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n a ≠ 0 := by
    by_contra! h
    refine ha (Perfection.ext fun n => ?_)
    change PreTilt.coeff n a = PreTilt.coeff n 0
    rw [h, map_zero]
  filter_upwards [GlobalTheory.WeakTop.eventually_coeff_eq AI x n g₀] with g hg
  rintro ⟨c, hc⟩
  apply hn
  rw [hc, map_mul, map_sub, hg, sub_self, zero_mul]

end GlobalTheory.WeakClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisOrbitWittTensorLatticeWeakTopolo
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section
open Filter Topology

namespace GlobalTheory.WeakClosed

theorem continuous_orbit_twTop :
    ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l}
      (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T),
      letI := twTop T b
      Continuous fun g : ↥(GK K) => TWact (AI.gRW LL (g : GQ l)) T g y := by
  intro l _ P AI K LL T d b y

  letI := zlMod T
  haveI := zlTower T
  letI tC : TopologicalSpace (Cb l) := cbTop l
  letI tW : TopologicalSpace (WCb l) := wTop l
  haveI hWr : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  have hW : Continuous (algebraMap ℤ_[l] (WCb l)) :=
    GlobalTheory.WeakTop.continuous_padicInt_witt (zlW l (Cb l))
  have ha : Continuous fun q : GQ l × WCb l => (AI.actWCbHom q.1).toAlgHom q.2 :=
    GlobalTheory.WeakTop.continuous_map_witt (fun g : GQ l => (autCb l (AI.actT g)).toRingHom)
      (continuous_autCb_cbTop AI)
  haveI := LL.2
  have hc : ∀ c : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := fun c =>
    (IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1 c).symm.trans
      (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 c)
  have hemb : Topology.IsInducing (algebraMap ℤ_[l] ℚ_[l]) := Topology.IsInducing.subtypeVal
  have hρ : ∀ i j, Continuous fun g : ↥(GK K) => b.repr (T.actT g (b j)) i := fun i j =>
    hemb.continuous_iff.2 (GlobalTheory.Cyc.continuous_coord_lat hc T b (b j) i)
  have h2 : ∀ w : WCb l, Continuous fun g : ↥(GK K) => (AI.actWCbHom (g : GQ l)).toAlgHom w := fun w =>
    Continuous.comp (g := fun q : GQ l × WCb l => (AI.actWCbHom q.1).toAlgHom q.2)
      (f := fun g : ↥(GK K) => ((g : GQ l), w)) ha (continuous_subtype_val.prodMk continuous_const)
  have hs : ∀ i, Continuous fun g : ↥(GK K) => ∑ j, algebraMap ℤ_[l] (WCb l) (b.repr (T.actT g (b j)) i) *
      (AI.actWCbHom (g : GQ l)).toAlgHom (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b y j) := fun i =>
    continuous_finsetSum _ fun j _ => (hW.comp (hρ i j)).mul (h2 _)
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  refine (hs i).congr fun g => ?_
  exact (GlobalTheory.WeakTop.coords_map b _ _ y i).symm

end GlobalTheory.WeakClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisOrbitWittTensorLatticeWeakTopoloStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_galois_orbit_wittTensorLatticeWeakTopology : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T), letI := twTop T b; Continuous fun g : ↥(GK K) => TWact (AI.gRW LL (g : GQ l)) T g y := by
  first | exact @GlobalTheory.WeakClosed.continuous_orbit_twTop | exact GlobalTheory.WeakClosed.continuous_orbit_twTop | (intros; apply GlobalTheory.WeakClosed.continuous_orbit_twTop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleDeRhamPeriodMatrixOfIsDR
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleDeRhamPeriodMatrixOfIsDR
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per Matrix

noncomputable section

namespace GlobalTheory.DRMat

theorem exists_fixed_of_stable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (S : Set (F →+* F)) (N : Submodule F (ι → F))
    (hN : ∀ σ ∈ S, ∀ v ∈ N, (fun j => σ (v j)) ∈ N) (v₀ : ι → F) (hv₀ : v₀ ∈ N) (h0 : v₀ ≠ 0) :
    ∃ v ∈ N, v ≠ 0 ∧ ∀ σ ∈ S, ∀ j, σ (v j) = v j := by
  classical
  have hex : ∃ k, ∃ v ∈ N, v ≠ 0 ∧ (Finset.univ.filter fun j => v j ≠ 0).card = k :=
    ⟨_, v₀, hv₀, h0, rfl⟩
  obtain ⟨w, hwN, hw0, hwk⟩ := Nat.find_spec hex
  obtain ⟨j₀, hj₀⟩ : ∃ j, w j ≠ 0 := by
    by_contra h; push_neg at h; exact hw0 (funext h)
  set v := (w j₀)⁻¹ • w with hv
  have hvN : v ∈ N := N.smul_mem _ hwN
  have hvj : v j₀ = 1 := by simp [hv, hj₀]
  have hsupp : ∀ j, v j ≠ 0 ↔ w j ≠ 0 := by
    intro j; simp [hv, hj₀]
  refine ⟨v, hvN, fun h => by simp [h] at hvj, fun σ hσ => ?_⟩
  by_contra hne
  push_neg at hne
  set u : ι → F := (fun j => σ (v j)) - v with hu
  have huN : u ∈ N := N.sub_mem (hN σ hσ v hvN) hvN
  have hu0 : u ≠ 0 := by
    obtain ⟨j, hj⟩ := hne
    intro h; apply hj; have := congrFun h j; simpa [hu, sub_eq_zero] using this
  have hlt : (Finset.univ.filter fun j => u j ≠ 0).card < Nat.find hex := by
    rw [← hwk]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨j₀, by simp [hj₀], by simp [hu, hvj]⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [← hsupp]; intro hvj0; apply hj; simp [hu, hvj0]
  exact Nat.find_min hex hlt ⟨u, huN, hu0, rfl⟩

theorem exists_period_matrix_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V), Formalism.MainNotions.N.IsDR (P.PD K) ρ → ∃ Q : GL n P.R.BdR, ∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q := by
  intro l _ P AI T n _ _ K V _ _ b ρ hDR
  set M : ↥(GK K) → Matrix n n P.R.BdR := fun g =>
    (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) with hM
  have hKact : ∀ (g : ↥(GK K)) (k : ↥K.1) (x : P.R.BdR),
      P.actQdR (g : GQ l) (algebraMap ↥K.1 P.R.BdR k * x) = algebraMap ↥K.1 P.R.BdR k * P.actQdR (g : GQ l) x := by
    intro g k x
    rw [← P.PD_actdR, ← P.PD_actdR, map_mul, AlgEquiv.commutes]
  let D : Submodule ↥K.1 (n → P.R.BdR) :=
    { carrier := {c | ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c}
      add_mem' := by
        intro x y hx hy g
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        have : (fun i => P.actQdR (g : GQ l) ((x + y) i)) =
            (fun i => P.actQdR (g : GQ l) (x i)) + (fun i => P.actQdR (g : GQ l) (y i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, hx g, hy g]
      zero_mem' := by
        intro g
        simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      smul_mem' := by
        intro k x hx g
        simp only [Set.mem_setOf_eq] at hx ⊢
        have : (fun i => P.actQdR (g : GQ l) ((k • x) i)) = k • (fun i => P.actQdR (g : GQ l) (x i)) := by
          funext i; simp only [Pi.smul_apply, Algebra.smul_def, hKact]
        rw [this, Matrix.mulVec_smul, hx g] }
  have hmemD : ∀ c, c ∈ D ↔ ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c := fun c => Iff.rfl

  let e : V ⊗[ℚ_[l]] P.R.BdR ≃ₗ[ℚ_[l]] (n → P.R.BdR) :=
    TensorProduct.congr b.equivFun (LinearEquiv.refl ℚ_[l] P.R.BdR) ≪≫ₗ
      TensorProduct.comm ℚ_[l] (n → ℚ_[l]) P.R.BdR ≪≫ₗ TensorProduct.piScalarRight ℚ_[l] ℚ_[l] P.R.BdR n
  have he_tmul : ∀ v β, e (v ⊗ₜ β) = fun i => b.repr v i • β := by
    intro v β
    simp [e]
  have he : ∀ (g : ↥(GK K)) x, e (actVdR (P.PD K) ρ g x) = M g *ᵥ fun i => P.actQdR (g : GQ l) (e x i) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]; exact (Matrix.mulVec_zero _).symm
    | tmul v β =>
      have h1 : actVdR (P.PD K) ρ g (v ⊗ₜ β) = ρ g v ⊗ₜ P.actQdR (g : GQ l) β := by
        simp [actVdR, P.PD_actdR]
      rw [h1, he_tmul, he_tmul]
      funext i
      rw [← LinearMap.toMatrix_mulVec_repr b b (ρ g) v]
      simp only [hM, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, map_mul, AlgEquiv.commutes]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by rw [map_mul]; ring
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, ← Matrix.mulVec_add]
      congr 1; funext i; simp
  have hmap : (DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)) = D.restrictScalars ℚ_[l] := by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.restrictScalars_mem, hmemD]
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun g => ?_
    rw [← e.injective.eq_iff, he, LinearEquiv.apply_symm_apply]
  have hfr : Module.finrank ℚ_[l] ↥D = Module.finrank ℚ_[l] K.1 * Fintype.card n := by
    have h1 := hDR
    unfold Formalism.MainNotions.N.IsDR at h1
    rw [Module.finrank_eq_card_basis b, LinearEquiv.finrank_eq (e.submoduleMap (DdR (P.PD K) ρ)), hmap] at h1
    exact h1

  rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    refine ⟨1, fun g => ?_⟩
    ext i; exact isEmptyElim i
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hKpos : 0 < Module.finrank ℚ_[l] ↥K.1 := Module.finrank_pos
  haveI : Module.Finite ℚ_[l] ↥D := Module.finite_of_finrank_pos (by rw [hfr]; positivity)
  haveI : Module.Finite ↥K.1 ↥D := Module.Finite.of_restrictScalars_finite ℚ_[l] ↥K.1 ↥D
  have hrank : Module.finrank ↥K.1 ↥D = Fintype.card n := by
    have := Module.finrank_mul_finrank ℚ_[l] ↥K.1 ↥D
    rw [hfr] at this
    exact Nat.eq_of_mul_eq_mul_left hKpos this
  let bK : Module.Basis n ↥K.1 ↥D :=
    (Module.finBasisOfFinrankEq ↥K.1 ↥D hrank).reindex (Fintype.equivFin n).symm
  let Q0 : Matrix n n P.R.BdR := Matrix.of fun i j => (bK j : n → P.R.BdR) i
  have hQ : ∀ g : ↥(GK K), M g * Q0.map (P.actQdR (g : GQ l)) = Q0 := by
    intro g
    ext i j
    have h := congrFun ((hmemD _).1 (bK j).2 g) i
    simpa [Q0, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  have hdet : IsUnit Q0.det := by
    letI : Field P.R.BdR := (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1.toField
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    obtain ⟨v, hv0, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    let S : Set (P.R.BdR →+* P.R.BdR) :=
      Set.range fun g : ↥(GK K) => ((P.actQdR (g : GQ l)) : P.R.BdR →+* P.R.BdR)
    have hstab : ∀ σ ∈ S, ∀ u ∈ LinearMap.ker (Matrix.mulVecLin Q0), (fun j => σ (u j)) ∈ LinearMap.ker (Matrix.mulVecLin Q0) := by
      rintro σ ⟨g, rfl⟩ u hu
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hu ⊢
      rw [← hQ g, ← Matrix.mulVec_mulVec]
      have : (Q0.map (P.actQdR (g : GQ l)) *ᵥ fun j => (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR) (u j)) = 0 := by
        funext i
        have := congrArg (P.actQdR (g : GQ l)) (congrFun hu i)
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [Matrix.mulVec, dotProduct, map_sum, map_mul] using this
      rw [this, Matrix.mulVec_zero]
    obtain ⟨w, hwN, hw0, hwfix⟩ :=
      exists_fixed_of_stable S (LinearMap.ker (Matrix.mulVecLin Q0)) hstab v (by simpa using hQv) hv0
    have hwK : ∀ j, ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c = w j := fun j =>
      (P.PD K).invdR (w j) fun g => by rw [P.PD_actdR]; exact hwfix _ ⟨g, rfl⟩ j
    choose c hc using hwK
    have hQw : Q0 *ᵥ w = 0 := by simpa using hwN
    set_option synthInstance.maxHeartbeats 100000 in
    have hsum : ∑ j, c j • bK j = 0 := by
      apply Subtype.ext
      funext i
      have := congrFun hQw i
      simp only [Matrix.mulVec, dotProduct, Q0, Matrix.of_apply, Pi.zero_apply] at this
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        Algebra.smul_def, Submodule.coe_zero, Pi.zero_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => by rw [← hc j]; exact mul_comm _ _
    have hc0 := Fintype.linearIndependent_iff.mp bK.linearIndependent c hsum
    exact hw0 (funext fun j => by rw [← hc j, hc0 j, map_zero]; rfl)
  refine ⟨((Matrix.isUnit_iff_isUnit_det Q0).mpr hdet).unit, fun g => ?_⟩
  rw [IsUnit.unit_spec]
  exact hQ g

end GlobalTheory.DRMat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvertibleDeRhamPeriodMatrixOfIsDRStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invertible_deRhamPeriodMatrix_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V), Formalism.MainNotions.N.IsDR (P.PD K) ρ → ∃ Q : GL n P.R.BdR, ∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q := by
  first | exact @GlobalTheory.DRMat.exists_period_matrix_of_isDR | exact GlobalTheory.DRMat.exists_period_matrix_of_isDR | (intros; apply GlobalTheory.DRMat.exists_period_matrix_of_isDR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrthKerEqRangeAdjoint
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.TypeSum

theorem orth_ker_eq_range_adjoint {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) : (LinearMap.ker A)ᗮ = LinearMap.range (LinearMap.adjoint A) := by
  have h : (LinearMap.range (LinearMap.adjoint A))ᗮ = LinearMap.ker A := by
    ext x
    simp only [Submodule.mem_orthogonal, LinearMap.mem_range, LinearMap.mem_ker, forall_exists_index,
      forall_apply_eq_imp_iff, LinearMap.adjoint_inner_left]
    constructor
    · intro hx
      exact ext_inner_left ℂ (fun y => by rw [hx y, inner_zero_right])
    · intro hx y
      rw [hx, inner_zero_right]
  rw [← h, Submodule.orthogonal_orthogonal]

variable {D : D7}

def eqvMt {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) :
    D.what₂.Mt μ' j' ≃ₗ[ℂ] D.what₂.Mt μ j := by
  subst hμ; subst hj; exact LinearEquiv.refl ℂ _

theorem map_eqvMt_self {μ : D.what₂.Tup} {j : ℕ} (hμ : μ = μ) (hj : j = j) (V : Submodule ℂ (D.what₂.Mt μ j)) :
    V.map (eqvMt hμ hj).toLinearMap = V :=
  Submodule.map_id V

theorem map_eqvMt_thetaT_isot {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) (σ : D.what₂.FT) :
    ((D.what₂.isot j' σ).map (D.what₂.thetaT μ' j')).map (eqvMt hμ hj).toLinearMap =
      (D.what₂.isot j σ).map (D.what₂.thetaT μ j) := by
  subst hμ; subst hj; exact map_eqvMt_self _ _ _

theorem map_eqvMt_range_thetaT {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) :
    (LinearMap.range (D.what₂.thetaT μ' j')).map (eqvMt hμ hj).toLinearMap =
      LinearMap.range (D.what₂.thetaT μ j) := by
  subst hμ; subst hj; exact map_eqvMt_self _ _ _

theorem isoTyp_eq_of_isoRep {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) {S S' : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (h : NG.IsoRep S S') : NG.isoTyp ρ S = NG.isoTyp ρ S' := by
  unfold NG.isoTyp
  congr 1
  ext T
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (h.symm hS).trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h.trans h2⟩⟩

variable {M : MtFam D}

theorem typeV_of_transport (A : AVTied D M) (i : D.nd.Loc) {μ' : D.what₂.Tup} {j' : ℕ}
    (hμ : μ' = D.nd.mu i) (hj : j' = D.nd.j i) (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m)
    (S' : Submodule ℂ (GAf D.host.E D.R.nV → (M μ' j' h1 h2).wt.W))
    (hirr : NG.IsIrrRep (M μ' j' h1 h2).wt.ρ S')
    (hne : (NG.isoTyp (M μ' j' h1 h2).wt.ρ S').comap (M μ' j' h1 h2).real ≠ ⊥) :
    ∃ P, ((NG.isoTyp (M μ' j' h1 h2).wt.ρ S').comap (M μ' j' h1 h2).real).map (eqvMt hμ hj).toLinearMap =
      D.naut.typeV i P := by
  subst hμ; subst hj
  obtain ⟨P, hP⟩ := A.surj i S' hirr hne
  refine ⟨P, ?_⟩
  have e := isoTyp_eq_of_isoRep (M.loc i).wt.ρ (A.irr i P).1.stable hP
  rw [map_eqvMt_self, A.typeV i P, e]
  rfl

theorem eig_of_transport (A : AVTied D M) (i : D.nd.Loc) (P : D.naut.AV i) (x : D.nd.X i)
    (hx : D.naut.ptV i P = some x) {μ' : D.what₂.Tup} {j' : ℕ}
    (hμ : μ' = D.nd.mu i) (hj : j' = D.nd.j i) (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m)
    (V : Submodule ℂ (D.what₂.Mt μ' j')) (hV : V.map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P)
    (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E))
    (hw : SplitOut D.nd i w) (hc : IsConjPl D.host w s.w) (hu : IsUnif D.host.E s.v ϖ) (k1 : 1 ≤ k)
    (k2 : k ≤ D.R.nV) (c : ℂ)
    (hV' : ∀ y ∈ V, NG.tN (M μ' j' h1 h2).J s ϖ k ((M μ' j' h1 h2).real y) = c • (M μ' j' h1 h2).real y) :
    c = iotaOC D i ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x) := by
  subst hμ; subst hj
  rw [map_eqvMt_self] at hV
  subst hV
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i P)
  have e1 := A.eigen i P x hx w k s ϖ hw hc hu k1 k2 y hy
  have e2 := hV' y hy
  have hr : (M.loc i).real y ≠ 0 := fun h => hy0 ((M.loc i).real_inj (h.trans (map_zero _).symm))
  exact smul_left_injective ℂ hr (e2.symm.trans e1)

end GlobalTheory.EtaJoin.TypeSum

namespace GlobalTheory.EtaJoin.TypeSum

theorem main : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → AVTied D M → SplitUnif D → TypeOrth D i →
    ThetaCut D (D.nd.mu i) (D.nd.j i) → Rows.IsotInternal D.what₂ → Formalism.MainNotions.SumRepresentations.ConclusionZ D →
    (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i),
      Formalism.MainNotions.N.HG D.nd D.naut i' ∧ Formalism.MainNotions.N.AtM D.nd D.naut i' σ) → ZSpec D i := by
  intro D M i HT A SU TO TC II PZ EX
  have hZ0 : Idx.Z0 D (D.nd.mu i) (D.nd.j i) = LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
    unfold Idx.Z0
    rw [orth_ker_eq_range_adjoint]
    exact inf_eq_left.2 TC
  have hmu : ∀ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), D.nd.mu i' = D.nd.mu i := fun i' hi' => by
    rw [D.nd.mu_w, D.nd.mu_w, ((D.nd.locs_mem _ _ i').1 hi').2]
  let G : Set (D.naut.AV i) := {P | ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), ∃ x' ∈ Formalism.MainNotions.N.ZgoodN D.nd D.naut i',
    ∃ P' : D.naut.AV i', D.naut.ptV i' P' = some x' ∧ ∃ (hμ : D.nd.mu i' = D.nd.mu i) (hj : D.nd.j i' = D.nd.j i),
      (D.naut.typeV i' P').map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P}

  have hin : ∀ P ∈ G, D.naut.typeV i P ≤ LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
    rintro P ⟨i', hi', x', hx', P', hP', hμ, hj, he⟩
    have hZ := (PZ i' ⟨x', hx'⟩).2.1
    have h1 : D.naut.typeV i' P' ≤ LinearMap.range (D.what₂.thetaT (D.nd.mu i') (D.nd.j i')) := by
      refine le_trans ?_ (LinearMap.map_le_range (f := D.what₂.thetaT (D.nd.mu i') (D.nd.j i'))
        (p := Formalism.MainNotions.N.goodPartM D.nd D.naut i'))
      rw [hZ]
      refine le_trans ?_ (le_biSup (fun x => Formalism.MainNotions.N.eigC D.nd D.naut i' x) hx')
      unfold Formalism.MainNotions.N.eigC
      exact le_biSup (fun Q => D.naut.typeV i' Q) (show P' ∈ {Q | D.naut.ptV i' Q = some x'} from hP')
    rw [← he, ← map_eqvMt_range_thetaT hμ hj]
    exact Submodule.map_mono h1

  have hsub : LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) ≤ ⨆ P ∈ G, D.naut.typeV i P := by
    rw [LinearMap.range_eq_map, ← ((II (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2).submodule_iSup_eq_top),
      Submodule.map_iSup]
    refine iSup_le fun σ => ?_
    by_cases h0 : D.what₂.isot (D.nd.j i) σ = ⊥
    · rw [h0, Submodule.map_bot]; exact bot_le
    obtain ⟨hg, i', hi', hHG, hAt⟩ := EX σ h0
    have hj : D.nd.j i' = D.nd.j i := ((D.nd.locs_mem _ _ i').1 hi').1
    have hμ := hmu i' hi'
    have h1 : D.what₂.isot (D.nd.j i') σ ≤ Formalism.MainNotions.N.goodPartM D.nd D.naut i' :=
      le_biSup (fun τ => D.what₂.isot (D.nd.j i') τ) (show σ ∈ {τ | D.nd.goodRow τ ∧ Formalism.MainNotions.N.AtM D.nd D.naut i' τ} from ⟨hg, hAt⟩)
    have h2 := Submodule.map_mono (f := D.what₂.thetaT (D.nd.mu i') (D.nd.j i')) h1
    rw [(PZ i' hHG).2.1] at h2
    rw [← map_eqvMt_thetaT_isot hμ hj]
    refine le_trans (Submodule.map_mono h2) ?_
    rw [Submodule.map_le_iff_le_comap]
    refine iSup₂_le fun x' hx' => ?_
    unfold Formalism.MainNotions.N.eigC
    refine iSup₂_le fun P' hP' => ?_
    rw [← Submodule.map_le_iff_le_comap]
    have hne : (NG.isoTyp (M.loc i').wt.ρ (A.S i' P')).comap (M.loc i').real ≠ ⊥ := by
      rw [← A.typeV i' P']; exact D.naut.typeV_ne i' P'
    obtain ⟨P, hP⟩ := typeV_of_transport A i hμ hj (D.nd.j_range i').1 (D.nd.j_range i').2 (A.S i' P') (A.irr i' P') hne
    have hT : (D.naut.typeV i' P').map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P := by
      rw [A.typeV i' P']; exact hP
    rw [hT]
    exact le_biSup (fun Q => D.naut.typeV i Q) (show P ∈ G from ⟨i', hi', x', hx', P', hP', hμ, hj, hT⟩)
  have hZG : LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) = ⨆ P ∈ G, D.naut.typeV i P :=
    le_antisymm hsub (iSup₂_le hin)
  have hout : ∀ P, P ∉ G → D.naut.typeV i P ≤ (LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)))ᗮ := by
    intro P hP
    rw [← Submodule.isOrtho_iff_le]
    apply Submodule.IsOrtho.symm
    rw [Submodule.isOrtho_iff_le, hZG]
    refine iSup₂_le fun Q hQ => ?_
    rw [← Submodule.isOrtho_iff_le]
    exact TO Q P (fun h => hP (h ▸ hQ))
  unfold ZSpec
  rw [hZ0]
  intro P
  refine ⟨(em (P ∈ G)).elim (fun h => Or.inl (hin P h)) (fun h => Or.inr (hout P h)), fun x hx => ⟨fun hg => ?_, fun hb => hout P ?_⟩⟩
  · exact hin P ⟨i, (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩, x, (D.Zgood_tie i x).1 hg, P, hx, rfl, rfl, map_eqvMt_self _ _ _⟩
  · rintro ⟨i', hi', x', hx', P', hP', hμ, hj, he⟩
    obtain ⟨hj', hw'⟩ := (D.nd.locs_mem _ _ i').1 hi'
    by_cases hii : i' = i
    · subst hii
      rw [map_eqvMt_self] at he
      have hPP : P' = P := by
        by_contra hne
        have hd : Disjoint (D.naut.typeV i' P') (D.naut.typeV i' P) := (D.naut.typeV_indep i').pairwiseDisjoint hne
        rw [he] at hd
        exact D.naut.typeV_ne i' P (disjoint_self.1 hd)
      subst hPP
      rw [hx] at hP'
      cases hP'
      exact hb ((D.Zgood_tie _ _).2 hx')
    · obtain ⟨φ, hφ⟩ := HT.sameO i i' hj'.symm hw'.symm
      obtain ⟨v, k, hv, hv', k1, k2, hunit⟩ := HT.sep i i' φ hφ hj'.symm hw'.symm (Ne.symm hii) x x'
      obtain ⟨s, ϖ, hc, hu⟩ := SU v hv.1
      have e := eig_of_transport A i P x hx hμ hj (D.nd.j_range i').1 (D.nd.j_range i').2 (D.naut.typeV i' P') he
        v k s ϖ hv hc hu k1 k2 _ (fun y hy => A.eigen i' P' x' hP' v k s ϖ hv' hc hu k1 k2 y hy)
      rw [hφ] at e
      have hinj : Function.Injective (iotaOC D i') := by
        intro a b h
        simp only [iotaOC, RingHom.coe_comp, Function.comp_apply] at h
        exact IsFractionRing.injective (D.nd.O i') (FractionRing (D.nd.O i'))
          ((D.naut.iotaQ i').injective ((D.naut.iotaQC i').injective h))
      rw [hinj e, sub_self] at hunit
      exact not_isUnit_zero hunit

end GlobalTheory.EtaJoin.TypeSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionLatticeColumnsConditionLinearIndepend
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionLatticeColumnsConditionLinearIndepend
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

theorem colv_latC_and_linearIndependent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → (∀ c, LatC P U x y (colv P ω A₀ c)) ∧ LinearIndependent ℚ_[l] (colv P ω A₀) := by
  intro l _ P r ω hω hdet n _ _ U x y A₀ hA W₀ hW hev
  have hit : ∀ (m : ℕ) (b : P.R.B), P.φB^[m] b = (P.φB ^ m) b := fun m b => by rw [AlgHom.coe_pow]
  have hfix : ∀ (m : ℕ) i j, P.φB^[m] ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) =
      (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j :=
    fun m i j => Function.iterate_fixed (hA i j) m
  have hφcol : ∀ (m : ℕ) c i, P.φB^[m] (colv P ω A₀ c i) =
      ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (fr l m (ω k)) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) (i, k) c := by
    intro m c i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hit, colv, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← hit, ← hit, phi_iter_kur, hfix]
  have hsum : ∀ {R : Type} [CommRing R] (f : ↥(MaximalUnramifiedExtension l) →+* R) (X : Matrix (n × Fin r) (n × Fin r) R) (m : Fin r) (i : n) c,
      ∑ k, f (fr l m (ω k)) * X (i, k) c = ((resMat n ω).map f * X) (i, m) c := by
    intro R _ f X m i c
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp [resMat_apply, apply_ite f, ite_mul]
  have hpU : (resMat n ω).map (kd P) * (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) =
      Matrix.blockDiagonal fun m => (U m : Matrix n n P.R.BdR) := by
    have e : (resMat n ω).map (kd P) = ((Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+*
        Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom (resGL n ω hdet) : GL (n × Fin r) P.R.BdR) :
        Matrix (n × Fin r) (n × Fin r) P.R.BdR) := rfl
    rw [e, U0, Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rfl
  have h0 : ∀ e f, P.ιB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) e f) =
      ((U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) *
        Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR)) e f := by
    intro e f; rw [← hev]; rfl
  have hcol : ∀ (m : Fin r) c i, ev P m (colv P ω A₀ c i) =
      ∑ j, (U m : Matrix n n P.R.BdR) i j * tz P (eps x y (m, j)) *
        (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) (j, m) c := by
    intro m c i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ev, hφcol, map_sum]
    simp only [map_mul, iota_kur, h0]
    rw [hsum, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hpU, Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type]
    simp [Matrix.blockDiagonal_apply, Matrix.diagonal_mul, ite_mul, mul_assoc]
  refine ⟨fun c => ⟨fun i => ?_, fun m => ⟨fun j => (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) (j, m) c,
    fun j => hW.1 _ _, funext fun i => ?_⟩⟩, ?_⟩
  · rw [hφcol]; simp only [hω]; rfl
  · rw [hcol]; simp [Matrix.mulVec, dotProduct, Matrix.mul_diagonal]
  · haveI : Nontrivial P.R.BdR := ⟨⟨(P.PD (botExt l)).ι (P.PD (botExt l)).t, 0, fun h =>
      (P.PD (botExt l)).not_mem_filtration_two (by rw [h]; exact zero_mem _)⟩⟩
    haveI : Nontrivial P.R.B := ⟨⟨1, 0, fun h => one_ne_zero (by simpa using congrArg P.ιB h : (1 : P.R.BdR) = 0)⟩⟩
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∀ i, ∑ c, g c • colv P ω A₀ c i = 0 := fun i => by
      have := congrFun hg i; simpa [Finset.sum_apply] using this
    have hYe : ∀ i (m : Fin r) c, Ymat P ω A₀ (i, m) c = P.φB^[m] (colv P ω A₀ c i) := by
      intro i m c
      rw [hφcol, hsum, Ymat]
    have hY : (Ymat P ω A₀).mulVec (fun c => algebraMap ℚ_[l] P.R.B (g c)) = 0 := by
      funext ⟨i, m⟩
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      calc ∑ c, Ymat P ω A₀ (i, m) c * algebraMap ℚ_[l] P.R.B (g c)
          = (P.φB ^ (m : ℕ)) (∑ c, g c • colv P ω A₀ c i) := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum]; refine Finset.sum_congr rfl fun c _ => ?_
            rw [hYe, hit, map_smul, Algebra.smul_def, mul_comm]
        _ = 0 := by rw [hg' i, map_zero]
    have hdetY : IsUnit (Ymat P ω A₀).det := by
      rw [Ymat, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ((isUnit_det_resMat n ω hdet).map _).mul ((Matrix.isUnit_iff_isUnit_det _).1 A₀.isUnit)
    have hv0 : (fun c => algebraMap ℚ_[l] P.R.B (g c)) = 0 := by
      have := congrArg (Matrix.mulVec (Ymat P ω A₀)⁻¹) hY
      rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetY, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    intro c
    exact (algebraMap ℚ_[l] P.R.B).injective (by simpa using congrFun hv0 c)

end GlobalTheory.PMon.ResR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionLatticeColumnsConditionLinearIndependStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictionLattice_columns_condition_linearIndependent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → (∀ c, LatC P U x y (colv P ω A₀ c)) ∧ LinearIndependent ℚ_[l] (colv P ω A₀) := by
  first | exact @GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent | exact GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent | (intros; apply GlobalTheory.PMon.ResR.colv_latC_and_linearIndependent <;> assumption)
end
end
