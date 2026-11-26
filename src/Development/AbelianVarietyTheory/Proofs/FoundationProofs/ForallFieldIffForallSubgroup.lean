module

public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TameGeneratorProjectors
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitSemisimpleCuspForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ForallFieldIffForallSubgroup
noncomputable section

namespace GlobalTheory.PointIrredCompare

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open scoped Pointwise

section Galois

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem mem_smul_iff (A : ValuationSubring Ω) (g : G F Ω) (y : Ω) :
    y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

theorem valuation_smul_lt_one_iff (A : ValuationSubring Ω) (g : G F Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', mem_smul_iff, mem_smul_iff, map_inv₀,
    map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]

theorem conj_mem_Ine_of_smul {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, mem_smul_iff]
      have : (g⁻¹ : G F Ω) (g x) = x := by
        show (g⁻¹ * g) x = x
        simp
      rw [this]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (valuation_smul_lt_one_iff A g _).1 (hσ.2 _ hx')
    have e : (g⁻¹ : G F Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
      rw [map_sub]
      congr 1
      show (g⁻¹ * g) x = x
      simp
    rwa [e] at h

theorem Ine_le_of_normal [IsAlgClosure F Ω] {A B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A w) (hB : IsPlaceOver B w) (Hs : Subgroup (G F Ω)) [hn : Hs.Normal]
    (h : Ine (F := F) A ≤ Hs) : Ine (F := F) B ≤ Hs := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver hA hB
  intro σ hσ
  have := hn.conj_mem _ (h (conj_mem_Ine_of_smul hσ)) g
  simpa [mul_assoc] using this

end Galois

section Hyps

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem lpDim_spehLoc (p : Part A.CG) (w : PlE H) : A.lpDim (spehLoc N A p w) = p.a * p.d := by
  have h : ∀ l : List ℝ, A.lpDim (l.foldr
      (fun k acc => A.lpSum (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) acc) (A.lpZero w)) =
      p.a * l.length := by
    intro l
    induction l with
    | nil => simp [A.lpDim_zero]
    | cons a l ih => simp only [List.foldr_cons, A.lpDim_sum, A.lpDim_tw, A.locG_dim, ih, List.length_cons]; ring
  unfold spehLoc
  rw [h]
  simp

theorem lpDim_isoLoc (P : List (Part A.CG)) (w : PlE H) : A.lpDim (isoLoc N A P w) = rankIso N A P := by
  induction P with
  | nil => simp [isoLoc, rankIso, A.lpDim_zero]
  | cons p P ih =>
    have : isoLoc N A (p :: P) w = A.lpSum (spehLoc N A p w) (isoLoc N A P w) := rfl
    rw [this, A.lpDim_sum, ih, lpDim_spehLoc]
    simp [rankIso]

theorem rank_of_hasParamX {i : N.Loc} {x : N.X i} {Sig : List (Part A.CG)} (h : HasParamX N A i x Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso N A Sig = R.r := by
  obtain ⟨P, -, h1, -, h3, -⟩ := h
  refine ⟨fun p hp => ?_, ?_⟩
  · have := h1 ⟨p.a, A.tw p.π A.etaTinv, p.d⟩
      (List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩)
    exact ⟨this.1, this.2.1⟩
  · simp only [rankIso, twistIso, muPart, List.map_map, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Ranks.nV] at h3 ⊢
    have e : List.map ((fun p : Part A.CG => p.a * p.d) ∘
        fun p : Part A.CG => (⟨p.a, A.tw p.π A.etaTinv, p.d⟩ : Part A.CG)) Sig =
        List.map (fun p : Part A.CG => p.a * p.d) Sig := rfl
    rw [e] at h3
    omega

def FullLabels (Sig : List (Part A.CG)) : Prop :=
  ∀ (k : Fin 2) (v : N.PlG k),
    (A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))).natDegree = A.lpDim (isoLoc N A Sig (A.plGw k v))

theorem fullLabels_of_good {i : N.Loc} {x : N.X i} {Sig : List (Part A.CG)} (h : HasParamX N A i x Sig)
    (hg : goodSig N A Sig) : FullLabels N A Sig := fun k v => by
  rw [lpDim_isoLoc, (rank_of_hasParamX N A h).2]
  exact ((hg k).1.1 v).2.1


end Hyps

end GlobalTheory.PointIrredCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlace
open Module NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.LatBasisAt

variable {K : Type} [Field K] [NumberField K]

abbrev locRing (w : HeightOneSpectrum (𝓞 K)) : Subalgebra (𝓞 K) K :=
  haveI := w.isPrime
  Localization.subalgebra.ofField K w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors

lemma mem_locRing (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locRing w ↔ ∃ (a s : 𝓞 K) (_ : s ∉ w.asIdeal),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ :=
  Iff.rfl

lemma algebraMap_ne_zero (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∉ w.asIdeal) : algebraMap (𝓞 K) K s ≠ 0 := by
  intro h
  have : s = 0 := (IsFractionRing.injective (𝓞 K) K) (by simpa using h)
  exact hs (this ▸ w.asIdeal.zero_mem)

lemma mem_localization_iff (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ M :=
  Iff.rfl

lemma mem_localization_iff_mem_span (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ↔ x ∈ Submodule.span (locRing w) (M : Set (Fin d → K)) := by
  constructor
  · intro h
    obtain ⟨s, hs, hsx⟩ := (mem_localization_iff w M x).mp h
    have hs0 := algebraMap_ne_zero w hs
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top
    have hu : (algebraMap (𝓞 K) K s)⁻¹ ∈ locRing w := (mem_locRing w _).mpr ⟨1, s, hs, by simp⟩
    have hx : x = (⟨_, hu⟩ : locRing w) • (s • x) := by
      rw [Subalgebra.smul_def, ← algebraMap_smul K s x, smul_smul]
      simp [hs0]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)
  · intro hx
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact (mem_localization_iff w M y).mpr ⟨1, h1, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy =>
      obtain ⟨s, hs, hsy⟩ := (mem_localization_iff w M y).mp hy
      obtain ⟨r, t, ht, hat⟩ := (mem_locRing w a).mp a.2
      refine (mem_localization_iff w M _).mpr ⟨t * s, fun h => (w.isPrime.mem_or_mem h).elim ht hs, ?_⟩
      have ht0 := algebraMap_ne_zero w ht
      have he : (t * s) • (a • y) = r • (s • y) := by
        rw [Subalgebra.smul_def, hat, ← algebraMap_smul K (t * s), ← algebraMap_smul K r,
          ← algebraMap_smul K s, smul_smul, smul_smul]
        congr 1
        rw [map_mul]
        field_simp
      rw [he]
      exact M.smul_mem r hsy

theorem basisAtEx :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
      (M : Submodule (𝓞 K) (Fin n → K)), Submodule.IsFullLattice K M →
      ∀ w : HeightOneSpectrum (𝓞 K), ∃ B : GL (Fin n) K, Formalism.L2.DIV.IsBasisAt w M B := by
  intro K _ _ d L hL w
  haveI := w.isPrime
  have : IsDiscreteValuationRing (locRing w) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) w.ne_bot (locRing w)
  set N : Submodule (locRing w) (Fin d → K) := Submodule.span (locRing w) (L : Set (Fin d → K))
    with hN
  have : Module.Finite (locRing w) N := by
    obtain ⟨s, hs⟩ := hL.fg
    rw [Module.Finite.iff_fg]
    refine ⟨s, ?_⟩
    rw [hN, ← hs, Submodule.span_span_of_tower]
  have : Module.IsTorsionFree (locRing w) N := inferInstance
  let b := Module.Free.chooseBasis (locRing w) N
  let v : Module.Free.ChooseBasisIndex (locRing w) N → Fin d → K := fun i => (b i : Fin d → K)
  have hliA : LinearIndependent (locRing w) v := b.linearIndependent.map' N.subtype N.ker_subtype
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing (locRing w) K).mp hliA
  have hspanA : Submodule.span (locRing w) (Set.range v) = N := by
    have : Set.range v = N.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hL.span_eq_top, Submodule.span_le]
    intro x hx
    have hxN : x ∈ Submodule.span (locRing w) (Set.range v) := by
      rw [hspanA]; exact Submodule.subset_span hx
    exact Submodule.span_le_restrictScalars (locRing w) K _ hxN
  let bK : Basis _ K (Fin d → K) := Basis.mk hli hspan
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex (locRing w) N) = d := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e := Fintype.equivFinOfCardEq hcard
  have hli' : LinearIndependent K (v ∘ e.symm) := hli.comp _ e.symm.injective
  let P : Matrix (Fin d) (Fin d) K := Matrix.of fun a j => (v ∘ e.symm) j a
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
  refine ⟨hP.unit, ?_⟩
  have hcol : Formalism.L2.DIV.colLat hP.unit = Submodule.span (𝓞 K) (Set.range (v ∘ e.symm)) := rfl
  unfold Formalism.L2.DIV.IsBasisAt
  ext x
  rw [hcol, mem_localization_iff_mem_span, mem_localization_iff_mem_span, Submodule.span_span_of_tower,
    EquivLike.range_comp, hspanA]

end GlobalTheory.LatBasisAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
noncomputable section

namespace GlobalTheory.JumpDescent

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

theorem descent {G M Ω : Type} [Group G] [AddCommGroup M] [Field Ω] (H : Subgroup G)
    [Finite (G ⧸ H)] (A : G → M →+ M) (hA1 : ∀ x, A 1 x = x)
    (hAm : ∀ g h x, A (g * h) x = A g (A h x))
    (m : Ω → M →+ M) (hm1 : ∀ x, m 1 x = x) (hmm : ∀ a b x, m (a * b) x = m a (m b x))
    (hma : ∀ a b x, m (a + b) x = m a x + m b x)
    (ε : G → (Ω →* Ω)) (hεm : ∀ g h a, ε (g * h) a = ε g (ε h a)) (hε1 : ∀ a, ε 1 a = a)
    (hε : ∀ g a x, A g (m a x) = m (ε g a) (A g x))
    (S : Submonoid Ω) (hH : ∀ g, g ∈ H ↔ ∀ a ∈ S, ε g a = a)
    (F F' : AddSubgroup M) (hFA : ∀ g, ∀ x ∈ F, A g x ∈ F) (hFm : ∀ a, ∀ x ∈ F, m a x ∈ F)
    (hF'A : ∀ g, ∀ x ∈ F', A g x ∈ F') (hF'm : ∀ a, ∀ x ∈ F', m a x ∈ F')
    (hfix : ∀ y ∈ F, (∀ g, A g y = y) → y ∈ F')
    (x : M) (hx : x ∈ F) (hxH : ∀ h ∈ H, A h x = x) : x ∈ F' := by
  classical
  haveI := Fintype.ofFinite (G ⧸ H)
  have hm0 : ∀ x, m 0 x = 0 := fun x => by
    have := hma 0 0 x
    rw [add_zero] at this
    exact left_eq_add.1 this
  let T : Submodule Ω (G ⧸ H → Ω) :=
    { carrier := {v | ∑ q, m (v q) (A q.out x) ∈ F'}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Pi.add_apply, hma, Finset.sum_add_distrib] at *
        exact F'.add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, Pi.zero_apply, hm0, Finset.sum_const_zero]
        exact F'.zero_mem
      smul_mem' := fun c a ha => by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, hmm, ← map_sum] at *
        exact hF'm _ _ ha }
  let φ : G ⧸ H → (S →* Ω) := fun q => (ε q.out).comp S.subtype
  have hφ : Function.Injective φ := by
    intro q q' hq
    rw [← q.out_eq, ← q'.out_eq]
    apply QuotientGroup.eq.2
    rw [hH]
    intro a ha
    have h1 : ε q.out a = ε q'.out a := DFunLike.congr_fun hq ⟨a, ha⟩
    rw [hεm, ← h1, ← hεm, inv_mul_cancel, hε1]
  have hli : LinearIndependent Ω (fun q => (φ q : S → Ω)) :=
    (linearIndependent_monoidHom S Ω).comp φ hφ
  have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    change ∑ q : G ⧸ H, m (ε q.out a) (A q.out x) ∈ F'
    simp only [← hε]
    have hz : ∀ h ∈ H, A h (m a x) = m a x := fun h hh => by
      rw [hε, hxH h hh, (hH h).1 hh a a.2]
    apply hfix _ (F.sum_mem fun q _ => hFA _ _ (hFm _ _ hx))
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H => A q.out (m a x))]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H (g * q.out)
    have h2 : (MulAction.toPerm g q : G ⧸ H) = ((g * q.out : G) : G ⧸ H) :=
      (MulAction.Quotient.mk_smul_out H g q).symm
    rw [h2, hh, hAm, hAm, hz _ h.2]
  have h1 : (Pi.single ((1 : G) : G ⧸ H) 1 : G ⧸ H → Ω) ∈ T := hT ▸ Submodule.mem_top
  change ∑ q : G ⧸ H, m ((Pi.single ((1 : G) : G ⧸ H) 1 : G ⧸ H → Ω) q) (A q.out x) ∈ F' at h1
  rw [Finset.sum_eq_single ((1 : G) : G ⧸ H) (fun q _ hq => by rw [Pi.single_eq_of_ne hq, hm0])
    (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, hm1] at h1
  have h2 := hF'A (((1 : G) : G ⧸ H).out)⁻¹ _ h1
  rwa [← hAm, inv_mul_cancel, hA1] at h2

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

section
variable {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem map_mem_FilV (K K' : FinExt l) (a : ℤ) (f : V →ₗ[LL] V) (g : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR)
    (hg : ∀ b ∈ (P.PD K).Fil a, g b ∈ (P.PD K').Fil a) (x : V ⊗[ℚ_[l]] P.R.BdR)
    (hx : x ∈ FilV (P.PD K) (LL := LL) (V := V) a) :
    AlgebraTensorModule.map f g x ∈ FilV (P.PD K') (LL := LL) (V := V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | tmul v b => exact ⟨f v ⊗ₜ ⟨g b.1, hg _ b.2⟩, rfl⟩
  | add y z hy hz => simp only [map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem FilV_eq (K K' : FinExt l) (a : ℤ) :
    FilV (P.PD K') (LL := LL) (V := V) a = FilV (P.PD K) (LL := LL) (V := V) a := by
  have key : ∀ K K' : FinExt l,
      FilV (P.PD K) (LL := LL) (V := V) a ≤ FilV (P.PD K') (LL := LL) (V := V) a := by
    intro K K' x hx
    have := map_mem_FilV P K K' a LinearMap.id LinearMap.id (fun b hb => by
      have h : b ∈ (((P.PD K).Fil a : Submodule ↥K.1 P.R.BdR) : Set P.R.BdR) := hb
      rw [P.PD_Fil K K' a] at h
      exact h) x hx
    rwa [AlgebraTensorModule.map_id] at this
  exact le_antisymm (key _ _) (key _ _)

theorem FilV_anti (K : FinExt l) (a : ℤ) :
    FilV (P.PD K) (LL := LL) (V := V) (a + 1) ≤ FilV (P.PD K) (LL := LL) (V := V) a := by
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, (P.PD K).Fil_anti a b.2⟩, rfl⟩
  | add y z hy hz => simp only [map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem mul_mem_Fil (K : FinExt l) (a : ℤ) (c : Om l) (b : P.R.BdR) (hb : b ∈ (P.PD K).Fil a) :
    algebraMap (Om l) P.R.BdR c * b ∈ (P.PD K).Fil a := by
  obtain ⟨E, hc⟩ : ∃ E : FinExt l, c ∈ E.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {c},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral c)⟩,
    IntermediateField.mem_adjoin_simple_self _ c⟩
  have h : b ∈ (((P.PD K).Fil a : Submodule ↥K.1 P.R.BdR) : Set P.R.BdR) := hb
  rw [P.PD_Fil K E a] at h
  have h2 : (⟨c, hc⟩ : ↥E.1) • b ∈
      (((P.PD E).Fil a : Submodule ↥E.1 P.R.BdR) : Set P.R.BdR) := Submodule.smul_mem _ _ h
  rw [P.PD_Fil E K a, Algebra.smul_def] at h2
  exact h2

theorem mem_DdR (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    x ∈ DdR (P.PD K) ρ ↔ ∀ g, actVdR (P.PD K) ρ g x = x := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem actVdR_tmul (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (g : ↥(GK K)) (v : V)
    (b : P.R.BdR) : actVdR (P.PD K) ρ g (v ⊗ₜ b) = ρ g v ⊗ₜ P.actQdR g b := by
  rw [← P.PD_actdR K g b]
  rfl

theorem actVdR_comp {K K' : FinExt l} (h : K.1 ≤ K'.1) (ρ : Representation LL ↥(GK K) V)
    (g : ↥(GK K')) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    actVdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) g x =
      actVdR (P.PD K) ρ (Subgroup.inclusion (GK_le h) g) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => rw [actVdR_tmul, actVdR_tmul]; rfl
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

def mulOm (c : Om l) : V ⊗[ℚ_[l]] P.R.BdR →ₗ[LL] V ⊗[ℚ_[l]] P.R.BdR :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft ℚ_[l] (algebraMap (Om l) P.R.BdR c))

theorem mulOm_tmul (c : Om l) (v : V) (b : P.R.BdR) :
    mulOm (LL := LL) P c (v ⊗ₜ b) = v ⊗ₜ (algebraMap (Om l) P.R.BdR c * b) := rfl

theorem mem_succ_of_fixed {K K' : FinExt l} (h : K.1 ≤ K'.1) (ρ : Representation LL ↥(GK K) V)
    (u : ℤ)
    (hfix : ∀ y ∈ FilV (P.PD K) (LL := LL) (V := V) u, y ∈ DdR (P.PD K) ρ →
      y ∈ FilV (P.PD K) (LL := LL) (V := V) (u + 1))
    (x : V ⊗[ℚ_[l]] P.R.BdR) (hx : x ∈ FilV (P.PD K) (LL := LL) (V := V) u)
    (hxH : x ∈ DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :
    x ∈ FilV (P.PD K) (LL := LL) (V := V) (u + 1) := by
  haveI : FiniteDimensional ℚ_[l] ↥K'.1 := K'.2
  haveI : Finite (GQ l ⧸ GK K') :=
    Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen K'.1)
  haveI : (GK K').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hA : ∀ (a : ℤ) (g : ↥(GK K)), ∀ x ∈ FilV (P.PD K) (LL := LL) (V := V) a,
      actVdR (P.PD K) ρ g x ∈ FilV (P.PD K) (LL := LL) (V := V) a := fun a g x hx =>
    map_mem_FilV P K K a _ _ (fun b hb => (P.PD K).Fil_G g a b hb) x hx
  have hM : ∀ (a : ℤ) (c : Om l), ∀ x ∈ FilV (P.PD K) (LL := LL) (V := V) a,
      mulOm (LL := LL) P c x ∈ FilV (P.PD K) (LL := LL) (V := V) a := fun a c x hx =>
    map_mem_FilV P K K a _ _ (fun b hb => mul_mem_Fil P K a c b hb) x hx
  refine descent (Ω := Om l) ((GK K').subgroupOf (GK K))
    (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom) ?_ ?_
    (fun c => (mulOm (LL := LL) P c).toAddMonoidHom) ?_ ?_ ?_
    (fun g => ((g : GQ l) : Om l →* Om l)) (fun _ _ _ => rfl) (fun _ => rfl) ?_
    K'.1.toSubalgebra.toSubsemiring.toSubmonoid ?_
    (FilV (P.PD K) (LL := LL) (V := V) u).toAddSubgroup
    (FilV (P.PD K) (LL := LL) (V := V) (u + 1)).toAddSubgroup (hA u) (hM u) (hA _) (hM _)
    (fun y hy hy' => hfix y hy ((mem_DdR P K ρ y).2 hy')) x hx ?_
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp [actVdR_tmul]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp [actVdR_tmul]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp [mulOm_tmul]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp [mulOm_tmul, mul_assoc]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, add_zero]
    | tmul v b => simp [mulOm_tmul, add_mul, tmul_add]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]; abel
  · intro g c x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp [mulOm_tmul, actVdR_tmul, P.actQdR_Om]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  · intro g
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun hg a ha => hg ⟨a, ha⟩, fun hg a => hg a.1 a.2⟩
  · intro g hg
    have := (mem_DdR P K' _ x).1 hxH ⟨g.1, hg⟩
    rw [actVdR_comp P h] at this
    exact this

theorem de_rham_jump_iff_extension {K K' : FinExt l} (h : K.1 ≤ K'.1) (ρ : Representation LL ↥(GK K) V)
    (u : ℤ) :
    (DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
        FilV (P.PD K') (LL := LL) (V := V) (u + 1) ≠
      DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
        FilV (P.PD K') (LL := LL) (V := V) u) ↔
    (DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) (u + 1) ≠
      DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) u) := by
  rw [FilV_eq P K K', FilV_eq P K K', not_iff_not]
  constructor
  · intro he
    refine le_antisymm (inf_le_inf_left _ (FilV_anti P K u)) fun x hx => ⟨hx.1, ?_⟩
    have hx' : x ∈ DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
      rw [mem_DdR]
      intro g
      rw [actVdR_comp P h]
      exact (mem_DdR P K _ x).1 hx.1 _
    exact (he.ge ⟨hx', hx.2⟩).2
  · intro he
    refine le_antisymm (inf_le_inf_left _ (FilV_anti P K u)) fun x hx => ⟨hx.1, ?_⟩
    exact mem_succ_of_fixed P h ρ u (fun y hy hy' => (he.ge ⟨hy', hy⟩).2) x hx.2 hx.1

end

theorem jump_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1)
    (Y : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (u : ℤ),
    (DdR (P.PD K') (Y.ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
        FilV (P.PD K') (LL := ↥LL.1) (V := Y.V) (u + 1) ≠
      DdR (P.PD K') (Y.ρ.comp (Subgroup.inclusion (GK_le h))) ⊓
        FilV (P.PD K') (LL := ↥LL.1) (V := Y.V) u) ↔
    (DdR (P.PD K) Y.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := Y.V) (u + 1) ≠
      DdR (P.PD K) Y.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := Y.V) u) :=
  fun _ _ P _ _ _ h Y u => de_rham_jump_iff_extension P h Y.ρ u

end GlobalTheory.JumpDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InclWFrobIter
noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem TWact_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (g : G) (r : RW) (y : TW RW T) :
    TWact f T g (r • y) = f r • TWact f T g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWact, TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

theorem TWmap_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (r : RW) (y : TW RW T) :
    TWmap f T (r • y) = f r • TWmap f T y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWmap, TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

theorem unit_cancel (hO : Function.Injective (algebraMap O LL)) :
    ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      ∀ r r' : RW, r • ((1 : RW) ⊗ₜ[O] e₀) = r' • ((1 : RW) ⊗ₜ[O] e₀) → r = r' := by
  obtain ⟨e, e₀, h1, h2, -⟩ := E.one_e
  obtain ⟨x, hx, hT⟩ := W.one_line
  have h0 : (e₀ : W.one.V) ≠ 0 := by
    intro h
    have hm : (⟨x, by rw [hT]; exact Submodule.mem_span_singleton_self x⟩ : ↥W.one.L.T) ∈
        Submodule.span O {e₀} := by rw [h1]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    have := congrArg Subtype.val hc
    simp only [SetLike.val_smul, h, smul_zero] at this
    exact hx this.symm
  have hb : Function.Bijective (LinearMap.toSpanSingleton O _ e₀) := by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc => ?_, ?_⟩
    · have := congrArg Subtype.val hc
      simp only [LinearMap.toSpanSingleton_apply, SetLike.val_smul, ZeroMemClass.coe_zero] at this
      rw [← algebraMap_smul LL, smul_eq_zero] at this
      exact hO (by rw [this.resolve_right h0, map_zero])
    · rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, h1]
  let lam := (LinearEquiv.ofBijective _ hb).symm
  have hl : lam e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]; simp
  refine ⟨e, e₀, h2, fun r r' h => ?_⟩
  have := congrArg (fun y => TensorProduct.rid O RW (LinearMap.lTensor RW lam.toLinearMap y)) h
  simpa [TensorProduct.smul_tmul', hl] using this

theorem ioE_φ (hO : Function.Injective (algebraMap O LL)) (a : W.EE) :
    E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h1, h2⟩ := unit_cancel E hO
  have h3 : TWmap φR W.one ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWmap]
  have := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, TWmap_smul, h1, h3] at this
  exact h2 _ _ this

theorem ioE_γ (hO : Function.Injective (algebraMap O LL)) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h1, h2⟩ := unit_cancel E hO
  have h4 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
  have h3 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWact, h4]
  have := E.jD_act W.one g (a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, TWact_smul, h1, h3] at this
  exact h2 _ _ this

def sc : LetA O n →ₐ[O] RW := inclR.comp E.io

theorem sc_φ (hO : Function.Injective (algebraMap O LL)) (a : LetA O n) :
    sc E (W.φA a) = φR (sc E a) := by
  have := ioE_φ E hO (algebraMap _ _ a)
  rwa [W.φE_ext, E.ioE_ext, E.ioE_ext] at this

def cst (c : ZMod n → O) : LetA O n := fun i => PowerSeries.C (c i)

theorem φA_cst (c : ZMod n → O) : W.φA (cst c) = cst fun i => c (i - 1) := by
  funext i
  exact W.φ₀.commutes (c (i - 1))

theorem iter_sc_cst (hO : Function.Injective (algebraMap O LL)) (c : ZMod n → O) (k : ℕ) :
    φR^[k] (sc E (cst c)) = sc E (cst fun i => c (i - k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ← sc_φ E hO, φA_cst]
    congr 2
    funext i
    congr 1
    push_cast
    ring

end Generic

section Comp

variable {Z O R R' : Type} [CommRing Z] [CommRing O] [CommRing R] [CommRing R'] [Algebra Z O]
  [Algebra Z R] [Algebra Z R']

def cf (lam : O →ₗ[Z] Z) : O ⊗[Z] R →ₗ[Z] R :=
  (TensorProduct.lid Z R).toLinearMap ∘ₗ lam.rTensor R

end Comp

section Situation

open GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

variable {l : ℕ} [Fact l.Prime]

theorem inclW_frob (a : Ainf l) : inclW l (WittVector.frobenius a) = frobW l (inclW l a) := by
  ext n
  change ((WittVector.map _ _ : WCb l)).coeff n = (WittVector.map (frobenius (Cb l) l) (inclW l a)).coeff n
  simp [inclW, WittVector.map_coeff, frobenius_def]

theorem tmul_iter (LL : FinExt l) (k : ℕ) (x : WCb l) :
    (φRW LL)^[k] ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (frobW l)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
  (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piS AI s))

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l (x ^ l) := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

end Situation

end GlobalTheory.TorsionBoundCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TeichmullerRoots
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FactorSeriesSupport
noncomputable section

open Polynomial

namespace GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

open Formalism.BasicNotions

def IsLabel (N : ℕ) {g : ℕ} (f : (ZMod g)[X]) : Prop :=
  f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0

def rootExp (N g : ℕ) : ℕ := (Finset.Icc 1 N).lcm fun d => g ^ d - 1

def IsPowLabel {g : ℕ} [Fact g.Prime] (a : ℤ) (f f' : (ZMod g)[X]) : Prop :=
  Formalism.CyclotomicNorms.rootsBar f' = (Formalism.CyclotomicNorms.rootsBar f).map fun x => x ^ a


variable (D : D7)

theorem IsPowLabel.unique {g : ℕ} [Fact g.Prime] {a : ℤ} {f f₁ f₂ : (ZMod g)[X]}
    (h₁ : IsPowLabel a f f₁) (h₂ : IsPowLabel a f f₂) (m₁ : f₁.Monic) (m₂ : f₂.Monic) : f₁ = f₂ := by
  have h : Formalism.CyclotomicNorms.rootsBar f₁ = Formalism.CyclotomicNorms.rootsBar f₂ := h₁.trans h₂.symm
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  have e : ∀ p : (ZMod g)[X], p.Monic → p.map (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) =
      ((Formalism.CyclotomicNorms.rootsBar p).map fun x => X - C x).prod := fun p hp =>
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp.map _)
      (IsAlgClosed.card_roots_eq_natDegree)).symm
  rw [e f₁ m₁, e f₂ m₂, h]

theorem rootExp_ne_zero (N g : ℕ) (hg : 2 ≤ g) : rootExp N g ≠ 0 := by
  unfold rootExp
  rw [Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨d, hd, h⟩
  have hd1 : d ≠ 0 := by have := (Finset.mem_Icc.1 hd).1; omega
  have : 1 < g ^ d := Nat.one_lt_pow hd1 (by omega)
  omega

end GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

end
end

noncomputable section

open Polynomial

namespace GlobalTheory.Compare.TeichmullerRoots

open Formalism.BasicNotions Formalism.CyclotomicNorms GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem zero_mem_rootsBar {f : (ZMod g)[X]} (hf : f.Monic) : 0 ∈ rootsBar f ↔ f.coeff 0 = 0 := by
  unfold rootsBar
  rw [mem_roots (hf.map _).ne_zero, IsRoot, ← coeff_zero_eq_eval_zero, coeff_map]
  exact map_eq_zero_iff _ (RingHom.injective _)

theorem exists_monic_of_stable (S : Multiset (Fbar g)) (hS : S.map (fun x => x ^ g) = S) :
    ∃ f : (ZMod g)[X], f.Monic ∧ rootsBar f = S := by
  set P : (Fbar g)[X] := (S.map fun x => X - C x).prod with hP
  have hm : P.Monic := monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x
  have hfix : P.map (frobenius (Fbar g) g) = P := by
    rw [hP, Polynomial.map_multiset_prod, Multiset.map_map]
    conv_rhs => rw [← hS, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp [frobenius_def]
  have hl : P ∈ lifts (algebraMap (ZMod g) (Fbar g)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have h1 : P.coeff n ^ g = P.coeff n := by
      have := congrArg (fun q => q.coeff n) hfix
      simpa [frobenius_def] using this
    have h2 : P.coeff n ∈ (⊥ : Subfield (Fbar g)) := (Subfield.mem_bot_iff_pow_eq_self _ g).2 h1
    rw [Subfield.bot_eq_of_zMod_algebra g] at h2
    exact h2
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  unfold rootsBar
  rw [hq, hP, roots_multiset_prod_X_sub_C]

theorem root_pow_rootExp {N : ℕ} {f : (ZMod g)[X]} (hf : IsLabel N f) {x : Fbar g} (hx : x ∈ rootsBar f) :
    x ^ rootExp N g = 1 := by
  have hx0 : x ≠ 0 := fun h => hf.2.2 ((zero_mem_rootsBar hf.1).1 (h ▸ hx))
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hroot : aeval x f = 0 := by
    have := (mem_roots (hf.1.map _).ne_zero).1 hx
    rwa [IsRoot, eval_map_algebraMap] at this
  have hd : (minpoly (ZMod g) x).natDegree ≤ N := by
    rw [← hf.2.1]
    exact natDegree_le_of_dvd (minpoly.dvd _ _ hroot) hf.1.ne_zero
  have hd1 : 1 ≤ (minpoly (ZMod g) x).natDegree := minpoly.natDegree_pos hint
  set K := IntermediateField.adjoin (ZMod g) ({x} : Set (Fbar g))
  haveI : FiniteDimensional (ZMod g) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ (minpoly (ZMod g) x).natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hint]
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one y hy
  rw [hc] at h1
  have h2 : x ^ (g ^ (minpoly (ZMod g) x).natDegree - 1) = 1 := by
    have := congrArg Subtype.val h1
    simpa [y] using this
  obtain ⟨c, hc⟩ : g ^ (minpoly (ZMod g) x).natDegree - 1 ∣ rootExp N g :=
    Finset.dvd_lcm (f := fun d => g ^ d - 1) (Finset.mem_Icc.2 ⟨hd1, hd⟩)
  rw [hc, pow_mul, h2, one_pow]

theorem roots_reverse_prod {F : Type} [Field F] (S : Multiset F) (hS : 0 ∉ S) :
    ((S.map fun x => X - C x).prod.reverse).roots = S.map fun x => x⁻¹ := by
  induction S using Multiset.induction_on with
  | empty => simp [reverse]
  | cons x S ih =>
    have hx : x ≠ 0 := fun h => hS (h ▸ Multiset.mem_cons_self _ _)
    have hS' : 0 ∉ S := fun h => hS (Multiset.mem_cons_of_mem h)
    have hm : (S.map fun x => X - C x).prod.Monic :=
      monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x
    have e : (X - C x).reverse = C (-x) * (X - C x⁻¹) := by
      have : (X - C x) = X + C (-x) := by simp [sub_eq_add_neg]
      rw [this, reverse_add_C, natDegree_X]
      have hX : (X : F[X]).reverse = 1 := by
        have := reverse_mul_X (1 : F[X])
        simpa [reverse] using this
      rw [hX, mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ hx]
      simp; ring
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, roots_mul, ih hS', e,
      roots_C_mul _ (neg_ne_zero.2 hx), roots_X_sub_C, Multiset.map_cons, Multiset.singleton_add]
    exact mul_ne_zero (by rw [Ne, reverse_eq_zero]; exact X_sub_C_ne_zero x)
      (by rw [Ne, reverse_eq_zero]; exact hm.ne_zero)

theorem dual_spec {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    (C (f.coeff 0)⁻¹ * f.reverse).Monic ∧ IsPowLabel (-1) f (C (f.coeff 0)⁻¹ * f.reverse) := by
  constructor
  · apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0, inv_mul_cancel₀ h0]
  · have e : f.map (algebraMap (ZMod g) (Fbar g)) = ((rootsBar f).map fun x => X - C x).prod :=
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hm.map _)
        (IsAlgClosed.card_roots_eq_natDegree)).symm
    have e2 : f.reverse.map (algebraMap (ZMod g) (Fbar g)) = (f.map (algebraMap (ZMod g) (Fbar g))).reverse := by
      rw [reverse, reverse, natDegree_map, reflect_map]
    unfold IsPowLabel
    simp only [zpow_neg_one]
    rw [← roots_reverse_prod _ (fun h => h0 ((zero_mem_rootsBar hm).1 h)), ← e, ← e2]
    unfold rootsBar
    rw [Polynomial.map_mul, map_C, roots_C_mul]
    exact (_root_.map_ne_zero _).2 (inv_ne_zero h0)

theorem teich_injective (t : Fbar g →* ℂ) (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) :
    Function.Injective t := by
  have hne : ∀ x, x ≠ 0 → t x ≠ 0 := fun x hx => ((IsUnit.mk0 x hx).map t).ne_zero
  have h0 : t 0 = 0 := by
    classical
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Fbar g))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    by_contra h
    have : t 0 * t y = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
    exact hy.2 (ht _ _ hy.1 one_ne_zero (mul_left_cancel₀ h this))
  intro x y h
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · rw [hx, hy]
    · exact absurd (by rw [← h, hx, h0]) (hne y hy)
  · by_cases hy : y = 0
    · exact absurd (by rw [h, hy, h0]) (hne x hx)
    · exact ht x y hx hy h

theorem teich_zpow (t : Fbar g →* ℂ) {x : Fbar g} (hx : x ≠ 0) (a : ℤ) : t (x ^ a) = t x ^ a := by
  have h1 : t ((Units.mk0 x hx ^ a : (Fbar g)ˣ) : Fbar g) = ((Units.map t (Units.mk0 x hx) ^ a : ℂˣ) : ℂ) := by
    rw [← map_zpow]; rfl
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val] at h1
  exact h1

end Roots

variable (D : D7)

theorem labAct_eq (k : Fin 2) (α : ℂ ≃+* ℂ) (a : ℤ)
    (ha : ∀ ζ : ℂ, ζ ^ rootExp D.R.r (D.host.g k) = 1 → α ζ = ζ ^ a)
    {f f' : (ZMod (D.host.g k))[X]} (hf : IsLabel D.R.r f) (hm : f'.Monic)
    (hp : haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; IsPowLabel a f f') :
    Formalism.MainNotions.ArithmeticCylinders.labAct D α k f = f' := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hinj := teich_injective (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
  have e : (rootsBar f).map
      (fun x => Function.invFun (D.ntypes.teichC k) (α (D.ntypes.teichC k x))) =
      (rootsBar f).map fun x => x ^ a := by
    apply Multiset.map_congr rfl
    intro x hx
    have hx0 : x ≠ 0 := fun h => hf.2.2 ((zero_mem_rootsBar hf.1).1 (h ▸ hx))
    rw [ha _ (by rw [← map_pow, root_pow_rootExp hf hx, map_one]), ← teich_zpow _ hx0]
    exact Function.leftInverse_invFun hinj _
  have hs := Classical.epsilon_spec (p := fun q : (ZMod (D.host.g k))[X] => q.Monic ∧
    rootsBar q = (rootsBar f).map
      (fun x => Function.invFun (D.ntypes.teichC k) (α (D.ntypes.teichC k x))))
    ⟨f', hm, hp.trans e.symm⟩
  exact IsPowLabel.unique (a := a) (f := f) (hs.2.trans e) hp hs.1 hm

end GlobalTheory.Compare.TeichmullerRoots

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitSemisimpleCuspFormsStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTOperatorExplicit_semisimple_cuspForms : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (c : ℂ) (n : ℕ), 0 < N → 0 < l → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, (fun h => GlobalTheory.Hk.heckeT k q σ h - c • h)^[n] ⇑f = 0 → GlobalTheory.Hk.heckeT k q σ ⇑f = c • ⇑f := by
  first | exact @GlobalTheory.Hk.Semisimple.heckeT_semisimple | exact GlobalTheory.Hk.Semisimple.heckeT_semisimple | (intros; apply GlobalTheory.Hk.Semisimple.heckeT_semisimple <;> assumption)
end
