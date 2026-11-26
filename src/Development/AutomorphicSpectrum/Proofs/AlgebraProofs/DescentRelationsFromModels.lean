module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelComparison
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowerSeriesPowPFrobenius
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFamPull
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticeEigenSplit

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelFacts
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FamGood1

open GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC

section Span

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem span_le {S : Set E} {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (hS : ∀ e ∈ S, e ∈ L) : spanOver R S ≤ L := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, e, he, rfl⟩
  exact hL a ha e (hS e he)

theorem span_stable (S : Set E) : ∀ a ∈ R, ∀ v ∈ spanOver R S, a • v ∈ spanOver R S :=
  fun _ ha _ hv => smul_mem_spanOver R S ha hv

theorem span_self {L : AddSubgroup E} (hL : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) :
    spanOver R (L : Set E) = L :=
  le_antisymm (span_le R hL fun _ h => h) fun _ h => mem_spanOver_of_mem R h

theorem map_span (f : E →ₗ[Ω] E') (S : Set E) :
    (spanOver R S).map f.toAddMonoidHom = spanOver R (f '' S) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, f e, ⟨e, he, rfl⟩, by simp⟩
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a • e, ⟨a, ha, e, he, rfl⟩, by simp⟩

theorem sup_stable {A B : AddSubgroup E} (hA : ∀ a ∈ R, ∀ v ∈ A, a • v ∈ A)
    (hB : ∀ a ∈ R, ∀ v ∈ B, a • v ∈ B) : ∀ a ∈ R, ∀ v ∈ A ⊔ B, a • v ∈ A ⊔ B := by
  intro a ha v hv
  obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
  rw [smul_add]
  exact AddSubgroup.add_mem_sup (hA a ha y hy) (hB a ha z hz)

theorem span_union (S T : Set E) : spanOver R (S ∪ T) = spanOver R S ⊔ spanOver R T := by
  apply le_antisymm
  · refine span_le R (sup_stable R (span_stable R S) (span_stable R T)) ?_
    rintro e (he | he)
    · exact AddSubgroup.mem_sup_left (mem_spanOver_of_mem R he)
    · exact AddSubgroup.mem_sup_right (mem_spanOver_of_mem R he)
  · exact sup_le (span_le R (span_stable R _) fun e he => mem_spanOver_of_mem R (Or.inl he))
      (span_le R (span_stable R _) fun e he => mem_spanOver_of_mem R (Or.inr he))

theorem span_span {R' : Subalgebra o Ω} (h : R ≤ R') (S : Set E) :
    spanOver R' (spanOver R S : Set E) = spanOver R' S := by
  apply le_antisymm
  · exact span_le R' (span_stable R' _) fun e he =>
      span_le R (fun a ha => span_stable R' S a (h ha)) (fun _ h => mem_spanOver_of_mem R' h) he
  · exact span_le R' (span_stable R' _) fun e he =>
      mem_spanOver_of_mem R' (mem_spanOver_of_mem R he)

theorem fg_of_locFree {r : ℕ} {L : AddSubgroup E} (h : LocFree R r L) :
    ∃ S : Finset E, L = spanOver R (S : Set E) ∧ Submodule.span Ω (S : Set E) = ⊤ := by
  classical
  obtain ⟨-, k, φ, v, hv, hφ, hs⟩ := PositivityTheory.Xgn.A_summand_of_quot.exists_dual R h
  refine ⟨Finset.univ.image v, le_antisymm (fun e he => ?_) (span_le R h.1 ?_), ?_⟩
  · rw [← hs e]
    exact sum_mem fun i _ => smul_mem_spanOver R _ (hφ i e he) (mem_spanOver_of_mem R (by simp))
  · intro e he
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at he
    obtain ⟨i, rfl⟩ := he
    exact hv i
  · rw [eq_top_iff]
    intro e _
    rw [← hs e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem locFree_of_bot {r : ℕ} {L : AddSubgroup E} (hL : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L)
    (h : LocFree R r (L.map (⊥ : Submodule Ω E).mkQ.toAddMonoidHom)) : LocFree R r L := by
  let e := Submodule.quotEquivOfEqBot (⊥ : Submodule Ω E) rfl
  have := locFree_baseChange R R (fun a ha => ha) e.toLinearMap (IsBaseChange.ofEquiv e) r _ h
  have h2 : (e.toLinearMap '' (L.map (⊥ : Submodule Ω E).mkQ.toAddMonoidHom : Set _)) = (L : Set E) := by
    ext v
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      simpa [e] using hw
    · intro hv
      exact ⟨_, ⟨v, hv, rfl⟩, by simp [e]⟩
  rwa [h2, span_self R hL] at this

theorem mulLat_std (c : Ω) (J : Type) [Fintype J] [DecidableEq J] :
    mulLat c (stdLat R J) = spanOver R (Set.range fun j : J => (Pi.single j c : J → Ω)) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have : (DistribSMul.toAddMonoidHom (J → Ω) c) v = ∑ j, v j • (Pi.single j c : J → Ω) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, mul_comm]
    rw [this]
    exact sum_mem fun j _ => smul_mem_spanOver R _ (hv j (Set.mem_univ j))
      (mem_spanOver_of_mem R ⟨j, rfl⟩)
  · refine span_le R ?_ ?_
    · rintro a ha _ ⟨v, hv, rfl⟩
      refine ⟨a • v, fun j _ => R.mul_mem ha (hv j (Set.mem_univ j)), ?_⟩
      simp [smul_comm a c]
    · rintro _ ⟨j, rfl⟩
      refine ⟨Pi.single j 1, fun i _ => ?_, ?_⟩
      · by_cases h : i = j
        · subst h; simpa using R.one_mem
        · simpa [h] using R.zero_mem
      · ext i
        simp [Pi.single_apply]

end Span

section Fam

variable (O : Type) [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω)
  {E E' : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω E']

theorem chart_trans {s t : ∀ k, ι k} (hs : mseg x s ≠ 0) {a : Ω} (ha : a ∈ chartRing O (mseg x) s) :
    ∃ m : ℕ, (mseg x s / mseg x t) ^ m * a ∈ chartRing O (mseg x) t := by
  have hf : mseg x s / mseg x t ∈ chartRing O (mseg x) t :=
    ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
  unfold chartRing at ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    refine ⟨1, ?_⟩
    have : (mseg x s / mseg x t) ^ 1 * (mseg x u / mseg x s) = mseg x u / mseg x t := by
      rw [pow_one, mul_comm, div_mul_div_cancel₀ hs]
    beta_reduce
    rw [this]
    exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
  | algebraMap r => exact ⟨0, by simpa using Subalgebra.algebraMap_mem _ r⟩
  | add a b _ _ ha hb => exact frac_add _ hf ha hb
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    refine ⟨m + n, ?_⟩
    have := Subalgebra.mul_mem _ hm hn
    convert this using 1
    ring

theorem fam_span (S : Set E) : IsLatFamily O x fun c => spanOver (chartRing O (mseg x) c) S := by
  refine ⟨fun s _ => span_stable _ S, fun s t hs _ v hv => ?_⟩
  have hf : mseg x s / mseg x t ∈ chartRing O (mseg x) t :=
    ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
  induction hv using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, e, he, rfl⟩ := hy
    obtain ⟨m, hm⟩ := chart_trans O x (t := t) hs ha
    exact ⟨m, by rw [smul_smul]; exact smul_mem_spanOver _ _ hm (mem_spanOver_of_mem _ he)⟩
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb => exact loc_add _ _ (span_stable _ S) hf ha hb
  | neg a _ ha =>
    obtain ⟨m, hm⟩ := ha
    exact ⟨m, by rw [smul_neg]; exact neg_mem hm⟩

theorem fam_sup {A B : (∀ k, ι k) → AddSubgroup E} (hA : IsLatFamily O x A) (hB : IsLatFamily O x B) :
    IsLatFamily O x fun c => A c ⊔ B c := by
  refine ⟨fun s hs => sup_stable _ (hA.1 s hs) (hB.1 s hs), fun s t hs ht v hv => ?_⟩
  have hf : mseg x s / mseg x t ∈ chartRing O (mseg x) t :=
    ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
  obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
  obtain ⟨m, hm⟩ := hA.2 s t hs ht y hy
  obtain ⟨n, hn⟩ := hB.2 s t hs ht z hz
  exact loc_add _ _ (sup_stable _ (hA.1 t ht) (hB.1 t ht)) hf
    ⟨m, AddSubgroup.mem_sup_left hm⟩ ⟨n, AddSubgroup.mem_sup_right hn⟩

theorem fam_map {A : (∀ k, ι k) → AddSubgroup E} (hA : IsLatFamily O x A) (f : E →ₗ[Ω] E') :
    IsLatFamily O x fun c => (A c).map f.toAddMonoidHom := by
  refine ⟨?_, ?_⟩
  · rintro s hs a ha _ ⟨v, hv, rfl⟩
    exact ⟨a • v, hA.1 s hs a ha v hv, by simp⟩
  · rintro s t hs ht _ ⟨v, hv, rfl⟩
    obtain ⟨m, hm⟩ := hA.2 s t hs ht v hv
    exact ⟨m, _, hm, by simp⟩

end Fam

theorem flatten_summand (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d : ℕ)
    (hm : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d)
    (hf : fnField O x = ⊤) (I : Type) [Fintype I] (E : Type) [AddCommGroup E] [Module Ω E]
    (U : I → Submodule Ω E) (Γ : I → (∀ k, ι k) → AddSubgroup E)
    (hΓ : ∀ j, IsLatFamily O x (Γ j) ∧ ∀ c, mseg x c ≠ 0 → ∃ S : Finset E,
      Γ j c = spanOver (chartRing O (mseg x) c) (S : Set E) ∧ Submodule.span Ω (S : Set E) = ⊤) :
    ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k))
      (z : (Σ k, ι' k) → Ω),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧
      ∀ j c, mseg (joinCoord x z) c ≠ 0 →
        LocFree (chartRing O (mseg (joinCoord x z)) c) (Module.finrank Ω E)
          (spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set E)) ∧
        Summand (spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ j (restrictChart c) : Set E)) (U j) := by
  classical
  let W : Bool × I → Submodule Ω E := fun q => if q.1 then U q.2 else ⊥
  obtain ⟨K', i1, i2, ι', i3, z, hz, hfree⟩ := PositivityTheory.Xgn.t_flatten_many O Ω K ι x d hm hf (Bool × I)
    (fun q => Module.finrank Ω (E ⧸ W q)) (fun q => E ⧸ W q)
    (fun q c => (Γ q.2 c).map (W q).mkQ.toAddMonoidHom) (fun q => ⟨rfl, fam_map O x (hΓ q.2).1 _, by
      intro c hc
      obtain ⟨S, hS, hT⟩ := (hΓ q.2).2 c hc
      refine ⟨S.image (W q).mkQ, ?_, ?_⟩
      · rw [hS, map_span, Finset.coe_image]
      · rw [Finset.coe_image, ← Submodule.map_span, hT, Submodule.map_top, Submodule.range_mkQ]⟩)
  refine ⟨K', i1, i2, ι', i3, z, hz, fun j c hc => ?_⟩
  have key : ∀ q : Bool × I, LocFree (chartRing O (mseg (joinCoord x z)) c) (Module.finrank Ω (E ⧸ W q))
      ((spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ q.2 (restrictChart c) : Set E)).map
        (W q).mkQ.toAddMonoidHom) := by
    intro q
    rw [map_span]
    exact hfree q c hc
  have h0 := locFree_of_bot _ (span_stable _ _) (key (false, j))
  have h1 := h0
  rw [← (PositivityTheory.Xgn.A_summand_of_quot.exists_dual _ h0).1] at h1
  exact ⟨h1, (PositivityTheory.Xgn.summand_iff_locFree_quot _ (U j) _ _ _ h1).1 (key (true, j))⟩

theorem bc_image {Ω : Type} [Field Ω] (J : Type) (S : Set (J → Ω)) : bcMap Ω Ω J '' S = S := by
  have : ∀ v, bcMap Ω Ω J v = v := fun v => rfl
  simp [this]

theorem vanSub_min (Ω F : Type) [Field Ω] [Zero F] (n i : ℕ) :
    vanSub Ω F n (min i n) = vanSub Ω F n i := by
  unfold vanSub
  congr 1
  ext y
  refine forall_congr' fun j => imp_congr_left ?_
  have := j.2
  omega

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₁ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) := by
  classical
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hm hf F _ _ _ n Sg _ r s p _ w χ φ D hD
  let E := (Fin n → F) → Ω
  let T : Set E := Set.range fun j : Fin n → F => (Pi.single j (p : Ω) : E)
  have hl1 : ∀ (R : Subalgebra O Ω) (D' : LieLatticeData Ω F n Sg r s), D'.l1 R p = D'.M ⊔ spanOver R T := by
    intro R D'
    rw [LieLatticeData.l1, mulLat_std]
  let U : Option (Sg ⊕ Fin (n + 1) ⊕ Sg × Fin n) → Submodule Ω E
    | none => ⊥
    | some (.inl τ) => LinearMap.range (linMap n fun a => algebraMap O Ω (χ τ a))
    | some (.inr (.inl i)) => vanSub Ω F n i
    | some (.inr (.inr q)) => charSub (fun a => algebraMap O Ω (χ q.1 a)) q.2
  let Γ : Bool → (∀ k, ι k) → AddSubgroup E
    | true => fun c => (D c).M ⊔ spanOver (chartRing O (mseg x) c) T
    | false => fun c => (D c).M
  obtain ⟨K', i1, i2, ι', i3, z, hz, hfree⟩ := flatten_summand O Ω K ι x d hm hf
    (Bool × Option (Sg ⊕ Fin (n + 1) ⊕ Sg × Fin n)) E (fun q => U q.2) (fun q => Γ q.1) (by
      rintro ⟨b, j⟩
      cases b
      · exact ⟨hD.famM, fun c hc => fg_of_locFree _ (hD.base c hc).freeM⟩
      · refine ⟨fam_sup O x hD.famM (fam_span O x T), fun c hc => ?_⟩
        obtain ⟨S, hS, hT⟩ := fg_of_locFree _ (hD.base c hc).freeM
        refine ⟨S ∪ Finset.univ.image fun j : Fin n → F => (Pi.single j (p : Ω) : E), ?_, ?_⟩
        · rw [Finset.coe_union, span_union, ← hS, Finset.coe_image, Finset.coe_univ, Set.image_univ]
        · rw [Finset.coe_union, Submodule.span_union, hT, top_sup_eq])
  refine ⟨K', i1, i2, ι', i3, z, hz, fun c hc => ?_⟩
  obtain ⟨hc0, hle⟩ := ((PositivityTheory.Xgn.t_chart_noeth_frac O Ω K ι x).2.2 K' ι' z).2 c hc
  have hM : (pullFamily O x z D c).M =
      spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ false (restrictChart c) : Set E) := by
    show spanOver _ (bcMap Ω Ω _ '' _) = _
    rw [bc_image]
  have hL : (pullFamily O x z D c).l1 (chartRing O (mseg (joinCoord x z)) c) p =
      spanOver (chartRing O (mseg (joinCoord x z)) c) (Γ true (restrictChart c) : Set E) := by
    rw [hl1, hM, ← span_union]
    have hst := (hD.base _ hc0).freeM.1
    have : Γ true (restrictChart c) =
        spanOver (chartRing O (mseg x) (restrictChart c)) (((D (restrictChart c)).M : Set E) ∪ T) := by
      rw [span_union, span_self _ hst]
    rw [this, span_span _ hle]
  have hr : Module.finrank Ω E = Fintype.card F ^ n := by simp [E]
  refine ⟨?_, fun τ => ?_, fun i => ?_, fun τ i => ?_⟩
  · rw [hL, ← hr]
    exact (hfree (true, none) c hc).1
  · rw [hL]
    exact (hfree (true, some (.inl τ)) c hc).2
  · rw [hM, ← vanSub_min]
    exact (hfree (false, some (.inr (.inl ⟨min i n, by omega⟩))) c hc).2
  · rw [hM]
    exact (hfree (false, some (.inr (.inr (τ, i)))) c hc).2

end GlobalTheory.CompanionTheory.Ar.FamGood1
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyModelFactsStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_family_model_facts : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∃ (K' : Type) (_ : Fintype K') (_ : DecidableEq K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d ∧ (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₁ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FamGood1.main | exact GlobalTheory.CompanionTheory.Ar.FamGood1.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FamGood1.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModel
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModel
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.FamPull

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), IsLatticeFamily O (joinCoord x z) p w χ φ (pullFamily O x z D) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₁ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg (joinCoord x z)) c) _) ≤ (pullFamily O x z D c).af (chartRing O (mseg (joinCoord x z)) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))))) ∧ ((∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O (joinCoord x z) u a fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i))) ∧ ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → ∃ (Lie' W' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (r τ) (Fin (r τ) → Ω)) (Om' OmHT' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (s τ) (Fin (s τ) → Ω)), HasBundles O (joinCoord x z) (pullFamily O x z D) Lie' W' Om' OmHT' ∧ ∀ τ, IsPull O x z (Lie τ) (Lie' τ) ∧ IsPull O x z (W τ) (W' τ) ∧ IsPull O x z (Om τ) (Om' τ) ∧ IsPull O x z (OmHT τ) (OmHT' τ) :=
  @PositivityTheory.Xgn.t_fam_pull

end GlobalTheory.CompanionTheory.Ar.FamPull
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_family_injective_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), IsLatticeFamily O (joinCoord x z) p w χ φ (pullFamily O x z D) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₁ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg (joinCoord x z)) c) _) ≤ (pullFamily O x z D c).af (chartRing O (mseg (joinCoord x z)) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg (joinCoord x z) c ≠ 0 → (pullFamily O x z D c).Good₂ (chartRing O (mseg (joinCoord x z)) c) p (fun τ a => algebraMap O Ω (χ τ a))))) ∧ ((∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O (joinCoord x z) u a fun c => (pullFamily O x z D c).xId (fun a => algebraMap O Ω (χ τ a)) i))) ∧ ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → ∃ (Lie' W' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (r τ) (Fin (r τ) → Ω)) (Om' OmHT' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (s τ) (Fin (s τ) → Ω)), HasBundles O (joinCoord x z) (pullFamily O x z D) Lie' W' Om' OmHT' ∧ ∀ τ, IsPull O x z (Lie τ) (Lie' τ) ∧ IsPull O x z (W τ) (W' τ) ∧ IsPull O x z (Om τ) (Om' τ) ∧ IsPull O x z (OmHT τ) (OmHT' τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FamPull.main | exact GlobalTheory.CompanionTheory.Ar.FamPull.main | (intros; apply GlobalTheory.CompanionTheory.Ar.FamPull.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFactsOfNormalHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeDivisorIdealLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemOfTestIdeal
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HaTest

theorem mem_of_test_ideal : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ (L : AddSubgroup Ω), LocFree R 1 L → ∀ v : Ω, (∃ m : ℕ, (p : Ω) ^ m * v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → algebraMap Ω C v ∈ spanOver RC (algebraMap Ω C '' L)) → v ∈ L := by
  intro o Ω _ _ _ R p hp hp0 hN hF hI L hL v hm htest
  let e : Ω ≃ₗ[Ω] (Unit → Ω) := (LinearEquiv.funUnique Unit Ω Ω).symm
  have hL' : LocFree R 1 (L.map e.toLinearMap.toAddMonoidHom) :=
    LatticeGoodness.locFree_map_equiv R e hL
  have hmem : ∀ x : Ω, e x ∈ L.map e.toLinearMap.toAddMonoidHom ↔ x ∈ L := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e.injective hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine (hmem v).1 (GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI 1 _ hL' (e v) ?_ ?_)
  · obtain ⟨m, hm⟩ := hm
    refine ⟨m, ?_⟩
    have : (p : Ω) ^ m • e v = e ((p : Ω) ^ m * v) := by
      rw [← smul_eq_mul, map_smul]
    rw [this]
    exact (hmem _).2 hm
  · intro C _ _ _ _ RC ht
    let g : C →+ (Unit → C) :=
      (LinearEquiv.funUnique Unit C C).symm.toLinearMap.toAddMonoidHom
    have hg : bcMap Ω C Unit (e v) = g (algebraMap Ω C v) := by
      funext u
      simp [bcMap, e, g]
    rw [hg]
    have h1 := AddSubgroup.mem_map_of_mem g (htest C RC ht)
    unfold spanOver at h1 ⊢
    rw [AddMonoidHom.map_closure] at h1
    refine (AddSubgroup.closure_mono ?_) h1
    rintro _ ⟨_, ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    refine ⟨a, ha, bcMap Ω C Unit (e x), ⟨e x, (hmem x).2 hx, rfl⟩, ?_⟩
    funext u
    simp [bcMap, e, g]

end GlobalTheory.CompanionTheory.Ar.Num.HaTest
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowSpanLocFreeBaseChange
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem powSpan_locFree_baseChange : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ (p : ℕ) (X : AddSubgroup Ω), LocFree R 1 X → LocFree R 1 (powSpan R p X) ∧ powSpan RC p (spanOver RC (algebraMap Ω C '' X)) = spanOver RC (algebraMap Ω C '' powSpan R p X) :=
  @PositivityTheory.Xgn.t_powspan

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeDivisorIdealLattice
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HaSteps.SlopeTestRemainingChoices

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_span {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {e : E}
    (h : e ∈ S) : e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, R.one_mem, e, h, (one_smul _ _).symm⟩

theorem ideal_le (R : Subalgebra o Ω) (p : ℕ) (hp : p.Prime) (hp0 : (p : Ω) ≠ 0)
    (hN : IsNoetherianRing R) (hF : IsFractionRing R Ω) (hI : IsIntegrallyClosedIn R Ω)
    (A B : AddSubgroup Ω) (hB : LocFree R 1 B) (hA : ∀ a ∈ A, a ∈ R) (hm : ∃ m : ℕ, (p : Ω) ^ m ∈ B)
    (h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C),
      IsTestPt p R RC → spanOver RC (algebraMap Ω C '' A) = spanOver RC (algebraMap Ω C '' B)) :
    A ≤ B := by
  intro v hv
  obtain ⟨m, hm⟩ := hm
  refine GlobalTheory.CompanionTheory.Ar.Num.HaTest.mem_of_test_ideal R p hp hp0 hN hF hI B hB v ⟨m, ?_⟩ ?_
  · have := hB.1 v (hA v hv) _ hm
    rwa [smul_eq_mul, mul_comm] at this
  · intro C _ _ _ _ RC hRC
    rw [← h C RC hRC]
    exact mem_span RC ⟨v, hv, rfl⟩

theorem lattice_le (R : Subalgebra o Ω) (p : ℕ) (hp : p.Prime) (hp0 : (p : Ω) ≠ 0)
    (hN : IsNoetherianRing R) (hF : IsFractionRing R Ω) (hI : IsIntegrallyClosedIn R Ω)
    {k N : ℕ} (L A B : AddSubgroup (Fin k → Ω)) (hB : LocFree R N B) (hA : A ≤ L)
    (hm : mulLat (p : Ω) L ≤ B)
    (h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C),
      IsTestPt p R RC → spanOver RC (bcMap Ω C (Fin k) '' A) = spanOver RC (bcMap Ω C (Fin k) '' B)) :
    A ≤ B := by
  intro v hv
  refine GlobalTheory.CompanionTheory.Ar.Num.HaLattice.main R p hp hp0 hN hF hI N B hB v ⟨1, ?_⟩ ?_
  · rw [pow_one]
    exact hm ⟨v, hA hv, rfl⟩
  · intro C _ _ _ _ RC hRC
    rw [← h C RC hRC]
    exact mem_span RC ⟨v, hv, rfl⟩

omit [Algebra o Ω] in
theorem map_snd_span {C : Type} [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C) {k : ℕ}
    (G : AddSubgroup (Ω × (Fin k → Ω))) :
    (spanOver RC (Prod.map (algebraMap Ω C) (bcMap Ω C (Fin k)) '' G)).map (AddMonoidHom.snd _ _) =
      spanOver RC (bcMap Ω C (Fin k) '' (G.map (AddMonoidHom.snd _ _))) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, _, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, _, ⟨g.2, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨a, ha, _, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩

variable {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}
  {D : LieLatticeData Ω F n Sg r s} {R : Subalgebra o Ω} {p : ℕ} {w : Ω} {χ : Sg → F → Ω}

theorem xId_le (hc : CharData R p w χ) (hb : D.Base R p w) (τ : Sg) (i : Fin n) :
    ∀ c ∈ D.xId (χ τ) i, c ∈ R := by
  intro c hc'
  have h : (c • fun x : Fin n → F => χ τ (x i)) ∈
    D.M ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup := hc'
  obtain ⟨g, hg, v, hv, e⟩ := AddSubgroup.mem_sup.1 h
  have hx : (Pi.single i (1 : F) : Fin n → F) ∈
      {x : Fin n → F | ∀ j : Fin n, (i : ℕ) + 1 ≤ (j : ℕ) → x j = 0} := by
    intro j hj
    have : j ≠ i := by
      rintro rfl
      omega
    exact Pi.single_eq_of_ne this _
  have hv0 : v (Pi.single i 1) = 0 := hv _ hx
  have hgR : g (Pi.single i 1) ∈ R := hb.M_le hg _ (Set.mem_univ _)
  have e1 := congrFun e (Pi.single i 1)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, hv0, add_zero, smul_eq_mul,
    (hc.2.2.2.2 τ).2.1, mul_one] at e1
  rwa [← e1]

theorem pow_smul_mem (hc : CharData R p w χ) (hb : D.Base R p w) (τ : Sg) (i : Fin n) :
    ∃ m : ℕ, ((p : Ω) ^ m • fun x : Fin n → F => χ τ (x i)) ∈ D.M := by
  obtain ⟨m, hm⟩ := hb.le_M
  exact ⟨m, hm ⟨fun x => χ τ (x i), fun x _ => (hc.2.2.2.2 τ).2.2 _, rfl⟩⟩

theorem pow_mem_xId (hc : CharData R p w χ) (hb : D.Base R p w) (τ : Sg) (i : Fin n) :
    ∃ m : ℕ, (p : Ω) ^ m ∈ D.xId (χ τ) i := by
  obtain ⟨m, hm⟩ := pow_smul_mem hc hb τ i
  exact ⟨m, AddSubgroup.mem_sup_left hm⟩

theorem pow_mem_dId (hc : CharData R p w χ) (τ : Sg) (i : Fin n) :
    ∃ m : ℕ, (p : Ω) ^ m ∈ D.dId R p (χ τ) i := by
  refine ⟨1, (p : Ω) • Pi.single i 1, ⟨?_, ?_⟩, ?_⟩
  · show linMap n (χ τ) ((p : Ω) • Pi.single i 1) ∈ D.l1 R p
    rw [map_smul]
    refine AddSubgroup.mem_sup_right ⟨linMap n (χ τ) (Pi.single i 1), fun x _ => ?_, rfl⟩
    show linMap n (χ τ) (Pi.single i 1) x ∈ R
    simp only [linMap, Fintype.linearCombination_apply_single, one_smul]
    exact (hc.2.2.2.2 τ).2.2 _
  · intro j hj
    have : j ≠ i := by
      rintro rfl
      exact Nat.lt_irrefl _ hj
    show ((p : Ω) • Pi.single i (1 : Ω) : Fin n → Ω) j = 0
    simp [Pi.single_eq_of_ne this]
  · simp

omit [One F] in
theorem kk_le (hb : D.Base R p w) (τ : Sg) (i : ℕ) : D.kk τ i ≤ dotDual R (D.lie τ) := by
  rintro _ ⟨⟨g, m⟩, ⟨h, -⟩, rfl⟩
  exact ((hb.th τ).2.1 m).1 ⟨g, h⟩

omit [One F] in
theorem le_kk (hb : D.Base R p w) (τ : Sg) (i : ℕ) :
    mulLat (p : Ω) (dotDual R (D.lie τ)) ≤ D.kk τ i := by
  intro m hm
  exact ⟨(0, m), ⟨((hb.th τ).2.2 m).2 hm, zero_mem _, trivial⟩, rfl⟩

omit [One F] in
theorem step_le (hb : D.Base R p w) (τ : Sg) (ψ : F → Ω) (i : Fin n) :
    (D.stepGraph τ ψ i).map (AddMonoidHom.snd _ _) ≤ dotDual R (D.lie τ) := by
  rintro _ ⟨⟨c, m⟩, h, rfl⟩
  have h' : ((c • fun x : Fin n → F => ψ (x i)), m) ∈
    D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥ := h
  obtain ⟨⟨g, m1⟩, hg, ⟨v, m2⟩, ⟨-, hv⟩, e⟩ := AddSubgroup.mem_sup.1 h'
  have h2 : m2 = 0 := hv
  have h1 : m1 + m2 = m := congrArg Prod.snd e
  rw [h2, add_zero] at h1
  subst h1
  exact ((hb.th τ).2.1 m1).1 ⟨g, hg⟩

omit [One F] in
theorem le_step (hb : D.Base R p w) (τ : Sg) (ψ : F → Ω) (i : Fin n) :
    mulLat (p : Ω) (dotDual R (D.lie τ)) ≤ (D.stepGraph τ ψ i).map (AddMonoidHom.snd _ _) := by
  intro m hm
  refine ⟨(0, m), ?_, rfl⟩
  show (((0 : Ω) • fun x : Fin n → F => ψ (x i)), m) ∈
    D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥
  rw [zero_smul]
  exact AddSubgroup.mem_sup_left (((hb.th τ).2.2 m).2 hm)

omit [One F] in
theorem ker_le (hb : D.Base R p w) (τ : Sg) (ψ : F → Ω) (i : Fin n) :
    (D.stepGraph τ ψ i).comap (AddMonoidHom.inl _ _) ≤ D.xId ψ i := by
  intro c h
  have h' : ((c • fun x : Fin n → F => ψ (x i)), (0 : Fin (r τ) → Ω)) ∈
    D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥ := h
  obtain ⟨⟨g, m1⟩, hg, ⟨v, m2⟩, ⟨hv, -⟩, e⟩ := AddSubgroup.mem_sup.1 h'
  have h1 : g + v = c • fun x : Fin n → F => ψ (x i) := congrArg Prod.fst e
  show (c • fun x : Fin n → F => ψ (x i)) ∈ D.M ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup
  rw [← h1]
  exact AddSubgroup.add_mem_sup (((hb.th τ).1 g).1 ⟨m1, hg⟩).1 hv

theorem pow_mem_ker (hc : CharData R p w χ) (hb : D.Base R p w) (τ : Sg) (i : Fin n) :
    ∃ m : ℕ, (p : Ω) ^ m ∈ (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _) := by
  obtain ⟨m, hm⟩ := pow_smul_mem hc hb τ i
  obtain ⟨u, hu⟩ := ((hb.th τ).1 _).2 ⟨hm, by simp [(hc.2.2.2.2 τ).1]⟩
  have h1 := (hb.stable τ (p : Ω) (natCast_mem R p)).2.2 _ hu
  have h2 := ((hb.th τ).2.2 ((p : Ω) • u)).2 ⟨u, ((hb.th τ).2.1 u).1 ⟨_, hu⟩, rfl⟩
  have h3 := sub_mem h1 h2
  refine ⟨m + 1, ?_⟩
  show (((p : Ω) ^ (m + 1) • fun x : Fin n → F => χ τ (x i)), (0 : Fin (r τ) → Ω)) ∈
    D.Th τ ⊔ (vanSub Ω F n ((i : ℕ) + 1)).toAddSubgroup.prod ⊥
  refine AddSubgroup.mem_sup_left ?_
  rw [Prod.smul_mk, Prod.mk_sub_mk, sub_zero, sub_self, smul_smul, ← pow_succ'] at h3
  exact h3

theorem powSpan_le (R : Subalgebra o Ω) (p : ℕ) (X : AddSubgroup Ω) (hX : ∀ c ∈ X, c ∈ R) :
    ∀ c ∈ powSpan R p X, c ∈ R := by
  have : powSpan R p X ≤ R.toSubring.toAddSubgroup := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    exact R.mul_mem ha (R.pow_mem (hX x hx) p)
  exact fun c hc => this hc

end GlobalTheory.CompanionTheory.Ar.Num.HaSteps.SlopeTestRemainingChoices


open GlobalTheory.CompanionTheory.Ar.Num.HaSteps.SlopeTestRemainingChoices in
theorem GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, D.dId R p (χ τ) i = D.xId (χ τ) i) ∧ (∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i) ∧ ∀ τ i, (D.stepGraph (φ τ) (χ (φ τ)) i).comap (AddMonoidHom.inl _ _) = powSpan R p (D.xId (χ τ) i) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hN hF hI φ hT hG hG2
  obtain ⟨hf1, hbc1⟩ := GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodBaseChange.main D R p w χ hc hb hG
  have hk := GlobalTheory.CompanionTheory.Ar.Num.kernel_graph_base_change D R p w χ hc hb hG
  obtain ⟨hf2, hbc2⟩ := GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.main D R p w χ hc hb hG hG2
    (GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice D R p w χ hc hb hp hN hF hI φ hT hG)
  have hp0 := hc.1
  refine ⟨fun τ i => ?_, fun τ i => ?_, fun τ i => ?_⟩
  · have h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C]
        (RC : Subalgebra o C), IsTestPt p R RC →
        spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) =
          spanOver RC (algebraMap Ω C '' D.xId (χ τ) i) := by
      intro C _ _ _ _ RC hRC
      rw [← (((hbc2 C RC hRC.2.2.2).2 τ).2 i).1, ← ((hbc1 C RC hRC.2.2.2).2 τ).2.2 i]
      exact (hT C RC hRC).dx τ i
    refine le_antisymm
      (ideal_le R p hp hp0 hN hF hI _ _ ((hf1 τ).2.2.2 i) ?_ (pow_mem_xId hc hb τ i) h)
      (ideal_le R p hp hp0 hN hF hI _ _ ((hf2 τ).2 i).1 (xId_le hc hb τ i) (pow_mem_dId hc τ i)
        fun C _ _ _ _ RC hRC => (h C RC hRC).symm)
    rintro _ ⟨l, ⟨hl, -⟩, rfl⟩
    exact (hf1 τ).2.2.1 hl i (Set.mem_univ _)
  · have h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C]
        (RC : Subalgebra o C), IsTestPt p R RC →
        spanOver RC (bcMap Ω C (Fin (r τ)) '' (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _)) =
          spanOver RC (bcMap Ω C (Fin (r τ)) '' D.kk τ i) := by
      intro C _ _ _ _ RC hRC
      rw [← map_snd_span, ← (hk C RC hRC.2.2.2 τ).2 i, ← (hk C RC hRC.2.2.2 τ).1 i]
      exact (hT C RC hRC).onto τ i
    exact le_antisymm
      (lattice_le R p hp hp0 hN hF hI _ _ _ (hG2.kk τ i) (step_le hb τ _ i) (le_kk hb τ i) h)
      (lattice_le R p hp hp0 hN hF hI _ _ _ (hG2.step τ i) (kk_le hb τ i) (le_step hb τ _ i)
        fun C _ _ _ _ RC hRC => (h C RC hRC).symm)
  · have h : ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C]
        (RC : Subalgebra o C), IsTestPt p R RC →
        spanOver RC (algebraMap Ω C ''
            (D.stepGraph (φ τ) (χ (φ τ)) i).comap (AddMonoidHom.inl _ _)) =
          spanOver RC (algebraMap Ω C '' powSpan R p (D.xId (χ τ) i)) := by
      intro C _ _ _ _ RC hRC
      rw [← (((hbc2 C RC hRC.2.2.2).2 (φ τ)).2 i).2,
        ← (GlobalTheory.CompanionTheory.Ar.Num.powSpan_locFree_baseChange R RC hRC.2.2.2 p _ ((hf1 τ).2.2.2 i)).2,
        ← ((hbc1 C RC hRC.2.2.2).2 τ).2.2 i]
      exact (hT C RC hRC).inj τ i
    obtain ⟨m, hm⟩ := pow_mem_xId hc hb τ i
    refine le_antisymm
      (ideal_le R p hp hp0 hN hF hI _ _
        (GlobalTheory.CompanionTheory.Ar.Num.powSpan_locFree_baseChange (C := Ω) R R (fun _ ha => ha) p _ ((hf1 τ).2.2.2 i)).1
        (fun a ha => xId_le hc hb (φ τ) i a (ker_le hb _ _ i ha)) ⟨m * p, ?_⟩ h)
      (ideal_le R p hp hp0 hN hF hI _ _ ((hf2 (φ τ)).2 i).2
        (powSpan_le R p _ (xId_le hc hb τ i)) (pow_mem_ker hc hb (φ τ) i)
        fun C _ _ _ _ RC hRC => (h C RC hRC).symm)
    rw [pow_mul]
    exact mem_span R ⟨_, hm, rfl⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeDivisorIdealLatticeStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_divisor_ideal_lattice : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, D.dId R p (χ τ) i = D.xId (χ τ) i) ∧ (∀ τ (i : Fin n), (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) = D.kk τ i) ∧ ∀ τ i, (D.stepGraph (φ τ) (χ (φ τ)) i).comap (AddMonoidHom.inl _ _) = powSpan R p (D.xId (χ τ) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main | exact GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeImageLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeImageLattice
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_span {E : Type} [AddCommGroup E] [Module Ω E] (R : Subalgebra o Ω) {S : Set E} {e : E}
    (h : e ∈ S) : e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, R.one_mem, e, h, (one_smul _ _).symm⟩

theorem bc_smul {C : Type} [Field C] [Algebra Ω C] {ι : Type} (w : Ω) (v : ι → Ω) :
    bcMap Ω C ι (w • v) = algebraMap Ω C w • bcMap Ω C ι v := by
  funext i
  show algebraMap Ω C (w * v i) = algebraMap Ω C w * algebraMap Ω C (v i)
  rw [map_mul]

theorem pow_one_smul_mem {E : Type} [AddCommGroup E] [Module Ω E] {R : Subalgebra o Ω} {N : ℕ}
    {L : AddSubgroup E} (hL : LocFree R N L) {p : ℕ} {w : Ω} (hw : ∃ c ∈ R, (p : Ω) = c * w) {v : E}
    (hv : w • v ∈ L) : ∃ m : ℕ, (p : Ω) ^ m • v ∈ L := by
  obtain ⟨c, hc, e⟩ := hw
  refine ⟨1, ?_⟩
  rw [pow_one, e, mul_smul]
  exact hL.1 c hc _ hv

end GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence


open GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence in
theorem GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → ∀ τ, D.imH R p τ (χ τ) = D.om τ ∧ D.kerH R p τ (χ τ) = divLat w (D.lie τ) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hN hF hI φ hT hG hG2 τ
  have hle := GlobalTheory.T.hodge_annihilator_lattice_holds D R p w χ hc hb hp hN hF hI φ hT hG
  have hbc1 := GlobalTheory.T.lattice_image_base_change D R p w χ hc hb hG hle
  obtain ⟨hf2, hbc2⟩ := GlobalTheory.T.lattice_second_goodness D R p w χ hc hb hG hG2 hle
  have hp0 := hc.1
  have hw := hc.2.2.1
  obtain ⟨flie, -, fom, -⟩ := hb.free τ
  obtain ⟨i1, i2, i3, i4⟩ := hb.incl τ
  refine ⟨le_antisymm (fun v hv => ?_) (fun v hv => ?_), le_antisymm (fun v hv => ?_) (fun v hv => ?_)⟩
  · refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ fom v (pow_one_smul_mem fom hw ?_) ?_
    · obtain ⟨⟨b, c⟩, ⟨h, -⟩, rfl⟩ := hv
      exact i3 (((hb.del τ).2.1 c).1 ⟨b, h⟩)
    · intro C _ _ _ _ RC hRC
      have h : bcMap Ω C _ v ∈ (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) := by
        rw [hbc1 C RC hRC.2.2.2 τ]
        exact mem_span RC ⟨v, hv, rfl⟩
      have e := (hT C RC hRC).im τ
      exact e.le h
  · refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ (hG2.im τ) v (pow_one_smul_mem (hG2.im τ) hw ?_) ?_
    · exact ⟨(0, w • v), ⟨((hb.del τ).2.2.1 _).2 (i4 hv), zero_mem _, trivial⟩, rfl⟩
    · intro C _ _ _ _ RC hRC
      rw [← hbc1 C RC hRC.2.2.2 τ]
      have e := (hT C RC hRC).im τ
      exact e.ge (mem_span RC ⟨v, hv, rfl⟩)
  · show w • v ∈ D.lie τ
    refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ flie _ (pow_one_smul_mem flie hw ?_) ?_
    · obtain ⟨⟨a, b⟩, ⟨h, -⟩, rfl⟩ := hv
      exact i2 (((hb.gam τ).1 a).1 ⟨b, h⟩)
    · intro C _ _ _ _ RC hRC
      have h : bcMap Ω C _ v ∈ (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a)) := by
        rw [((hbc2 C RC hRC.2.2.2).2 τ).1]
        exact mem_span RC ⟨v, hv, rfl⟩
      have e := (hT C RC hRC).ker τ
      rw [bc_smul]
      exact e.le h
  · have hv' : w • v ∈ D.lie τ := hv
    refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI _ _ (hf2 τ).1 v (pow_one_smul_mem (hf2 τ).1 hw ?_) ?_
    · exact ⟨(w • v, 0), ⟨((hb.gam τ).2.2 _).2 (i1 hv'), trivial, zero_mem _⟩, rfl⟩
    · intro C _ _ _ _ RC hRC
      rw [← ((hbc2 C RC hRC.2.2.2).2 τ).1]
      have e := (hT C RC hRC).ker τ
      refine e.ge ?_
      show algebraMap Ω C w • bcMap Ω C _ v ∈ (D.bc RC).lie τ
      rw [← bc_smul]
      exact mem_span RC ⟨_, hv', rfl⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeImageLatticeStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_image_lattice : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → ∀ τ, D.imH R p τ (χ τ) = D.om τ ∧ D.kerH R p τ (χ τ) = divLat w (D.lie τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFactsOfNormalHolds
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem lattice_facts_of_normal : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → D.Facts R p w χ φ := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hn hf hi φ ht h1 h2
  have hleaf := GlobalTheory.T.hodge_annihilator_lattice_holds D R p w χ hc hb hp hn hf hi φ ht h1
  have hseq := GlobalTheory.T.hodge_image_lattice D R p w χ hc hb hp hn hf hi φ ht h1 h2
  obtain ⟨hdx, honto, hinj⟩ := GlobalTheory.T.hodge_divisor_ideal_lattice D R p w χ hc hb hp hn hf hi φ ht h1 h2
  exact
    { le_af := hleaf
      im := fun τ => (hseq τ).1
      ker := fun τ => (hseq τ).2
      dx := hdx
      onto := honto
      inj := hinj }

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFactsOfNormalHoldsStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_facts_of_normal_holds : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → D.Facts R p w χ φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.lattice_facts_of_normal | exact GlobalTheory.CompanionTheory.Ar.Num.lattice_facts_of_normal | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.lattice_facts_of_normal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DescentRelationsFromModels
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.CkTop

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

theorem inj_of_model {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {x : (Σ k, ι k) → Ω} {d : ℕ}
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) :
    Function.Injective (algebraMap O Ω) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  have hmem : c ∈ (mcIdeal O x).comap (MvPolynomial.C : O →+* MvPolynomial (Σ k, ι k) O) := by
    rw [Ideal.mem_comap]
    simp only [mcIdeal, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap, RingHom.mem_ker]
    simp [hc]
  rw [h.2.2.1] at hmem
  exact (Ideal.mem_bot).1 hmem

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {d : ℕ}
  {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ}
  {p : ℕ} {w : O} {χ : Sg → F → O} {φ : Equiv.Perm Sg} {D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s}

theorem charData_of (hinj : Function.Injective (algebraMap O Ω)) (hp : p.Prime)
    (hfam : IsLatticeFamily O x p w χ φ D) (c : ∀ k, ι k) :
    CharData (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) := by
  obtain ⟨hp0, ⟨u, hu, hw⟩, -, h01, hχ⟩ := hfam.char
  refine ⟨?_, Subalgebra.algebraMap_mem _ _, ?_, h01, fun τ => ⟨?_, ?_, fun a => Subalgebra.algebraMap_mem _ _⟩⟩
  · rw [← map_natCast (algebraMap O Ω) p]
    exact fun h => hp0 (hinj (h.trans (map_zero _).symm))
  · refine ⟨algebraMap O Ω (↑hu.unit⁻¹ * w ^ (p - 2)), Subalgebra.algebraMap_mem _ _, ?_⟩
    rw [← map_natCast (algebraMap O Ω), ← map_mul]
    congr 1
    have h2 : p - 1 = p - 2 + 1 := by have := hp.two_le; omega
    rw [mul_assoc, ← pow_succ, ← h2, hw, ← mul_assoc, hu.val_inv_mul, one_mul]
  · simp [(hχ τ).1]
  · simp [(hχ τ).2]

theorem sameGeneric_of (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D)
    (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω))
    (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω))
    (hb : HasBundles O x D Lie W Om OmHT) :
    ∀ τ, SameGeneric O x (Lie τ) (W τ) ∧ SameGeneric O x (Om τ) (OmHT τ) := by
  have hw0 : w ≠ 0 := by
    obtain ⟨u, hu, hw⟩ := hfam.char.2.1
    intro h
    rw [h, zero_pow (by have := hp.two_le; omega)] at hw
    rcases mul_eq_zero.1 hw.symm with h' | h'
    · exact hu.ne_zero h'
    · exact hfam.char.1 h'
  intro τ
  constructor
  · intro c hc
    obtain ⟨h1, h2, -, -⟩ := hb τ c hc
    have hB := ((hfam.base c hc).incl τ)
    refine ⟨fun v hv => ⟨1, one_ne_zero, ?_⟩, fun v hv => ⟨w, hw0, ?_⟩⟩
    · rw [map_one, one_smul, h2]; rw [h1] at hv; exact hB.1 hv
    · rw [h1]; rw [h2] at hv; exact hB.2.1 hv
  · intro c hc
    obtain ⟨-, -, h3, h4⟩ := hb τ c hc
    have hB := ((hfam.base c hc).incl τ)
    refine ⟨fun v hv => ⟨w, hw0, ?_⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
    · rw [h4]; rw [h3] at hv; exact hB.2.2.2 hv
    · rw [map_one, one_smul, h3]; rw [h4] at hv; exact hB.2.2.1 hv

theorem descend (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D)
    {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω)
    (hmod' : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d)
    (h : ∀ (Lie' W' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (r τ) (Fin (r τ) → Ω))
      (Om' OmHT' : ∀ τ, ChartBundle O (mseg (joinCoord x z)) (s τ) (Fin (s τ) → Ω)),
      HasBundles O (joinCoord x z) (pullFamily O x z D) Lie' W' Om' OmHT' →
        CkRelations O (joinCoord x z) d p φ Lie' W' Om' OmHT') :
    ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  intro Lie W Om OmHT hb
  obtain ⟨-, -, hpull⟩ := GlobalTheory.T.lattice_family_injective_model O Ω K ι x (inj_of_model hmod) p hp w χ φ D hfam K' ι' z
  obtain ⟨Lie', W', Om', OmHT', hb', hP⟩ := hpull Lie W Om OmHT hb
  have hfn' := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).1 hfn
  exact GlobalTheory.T.model_over_prime_perm_module_lattice O Ω K ι x d hmod p hfam.char.1 φ Lie W Om OmHT
    (sameGeneric_of hp hfam Lie W Om OmHT hb) K' ι' z hmod' (hfn'.trans hfn.symm)
    Lie' W' Om' OmHT' hP (h _ _ _ _ hb')

theorem stage5 (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D) (hN : NormalCharts O x) (h1 : (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) (h2 : (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))))
    (hl : (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i)) : ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT :=
  GlobalTheory.T.model_over_mod_p_lattice_eigen_split O Ω K ι x d hmod p hp w χ φ D hfam h1 h2
    (fun c hc => GlobalTheory.T.lattice_facts_of_normal_holds (D c) (chartRing O (mseg x) c) p _ _
      (charData_of (inj_of_model hmod) hp hfam c) (hfam.base c hc) hp
      ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).1 c) ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.1 hfn c hc) (hN c hc) φ
      (hfam.test c hc) (h1 c hc) (h2 c hc)) hl

end GlobalTheory.CompanionTheory.Ar.Num.CkTop

namespace GlobalTheory.CompanionTheory.Ar.Num.CkTop

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {d : ℕ}
  {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ}
  {p : ℕ} {w : O} {χ : Sg → F → O} {φ : Equiv.Perm Sg} {D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s}

theorem stage4 [CharZero O] (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D) (h1 : (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) (haf : (∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)))) (h2 : (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))))
    (hl : (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i)) : ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  obtain ⟨K', _, _, ι', _, z, hmod', hN⟩ := GlobalTheory.T.model_refinement_exists O Ω K ι x d hmod hfn
  obtain ⟨hfam', hg, -⟩ := GlobalTheory.T.lattice_family_injective_model O Ω K ι x (inj_of_model hmod) p hp w χ φ D hfam K' ι' z
  have hfn' := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).1 hfn
  obtain ⟨h1', hg', hln⟩ := hg h1
  obtain ⟨-, hg2⟩ := hg' haf
  exact descend hmod hfn hp hfam z hmod' (stage5 hmod' hfn' hp hfam' hN h1' (hg2 h2) (hln hl))

theorem stage3 [CharZero O] (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D) (h1 : (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) (haf : (∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)))) (h2 : (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) :
    ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  obtain ⟨K', _, _, ι', _, z, hmod', hl'⟩ := GlobalTheory.T.lattice_family_model_chern O Ω K ι x d hmod hfn p hp w χ φ D hfam h1
  obtain ⟨hfam', hg, -⟩ := GlobalTheory.T.lattice_family_injective_model O Ω K ι x (inj_of_model hmod) p hp w χ φ D hfam K' ι' z
  have hfn' := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).1 hfn
  obtain ⟨h1', hg', hln⟩ := hg h1
  obtain ⟨haf', hg2⟩ := hg' haf
  exact descend hmod hfn hp hfam z hmod' (stage4 hmod' hfn' hp hfam' h1' haf' (hg2 h2) hl')

theorem stage2 [CharZero O] (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D) (h1 : (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) (haf : (∀ c, mseg x c ≠ 0 → ∀ τ, mulLat (algebraMap O Ω w) (stdLat (chartRing O (mseg x) c) _) ≤ (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)))) : ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  obtain ⟨K', _, _, ι', _, z, hmod', h2'⟩ := GlobalTheory.T.lattice_family_model_comparison O Ω K ι x d hmod hfn p hp w χ φ D hfam h1 haf
  obtain ⟨hfam', hg, -⟩ := GlobalTheory.T.lattice_family_injective_model O Ω K ι x (inj_of_model hmod) p hp w χ φ D hfam K' ι' z
  have hfn' := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).1 hfn
  obtain ⟨h1', hg', hln⟩ := hg h1
  obtain ⟨haf', -⟩ := hg' haf
  exact descend hmod hfn hp hfam z hmod' (stage3 hmod' hfn' hp hfam' h1' haf' h2')

theorem stage1b [CharZero O] (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D) (h1 : (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) (hN : NormalCharts O x) : ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT :=
  stage2 hmod hfn hp hfam h1 (fun c hc τ => GlobalTheory.T.hodge_annihilator_lattice_holds (D c) (chartRing O (mseg x) c) p _ _
      (charData_of (inj_of_model hmod) hp hfam c) (hfam.base c hc) hp
      ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).1 c) ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.1 hfn c hc) (hN c hc) φ
      (hfam.test c hc) (h1 c hc) τ)

theorem stage1 [CharZero O] (hmod : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d) (hfn : fnField O x = ⊤) (hp : p.Prime) (hfam : IsLatticeFamily O x p w χ φ D) (h1 : (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a)))) : ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  obtain ⟨K', _, _, ι', _, z, hmod', hN⟩ := GlobalTheory.T.model_refinement_exists O Ω K ι x d hmod hfn
  obtain ⟨hfam', hg, -⟩ := GlobalTheory.T.lattice_family_injective_model O Ω K ι x (inj_of_model hmod) p hp w χ φ D hfam K' ι' z
  have hfn' := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).1 hfn
  obtain ⟨h1', -, -⟩ := hg h1
  exact descend hmod hfn hp hfam z hmod' (stage1b hmod' hfn' hp hfam' h1' hN)

theorem ckRelations_of_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) [CharZero O] (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ d hmod hfn F _ _ _ n Sg _ r s p hp w χ φ D hfam
  obtain ⟨K', _, _, ι', _, z, hmod', h1'⟩ := GlobalTheory.T.lattice_family_model_facts O Ω K ι x d hmod hfn p hp w χ φ D hfam
  obtain ⟨hfam', -, -⟩ := GlobalTheory.T.lattice_family_injective_model O Ω K ι x (inj_of_model hmod) p hp w χ φ D hfam K' ι' z
  have hfn' := ((GlobalTheory.T.chart_rings_noetherian_fraction O Ω K ι x).2.2 K' ι' z).1 hfn
  exact descend hmod hfn hp hfam z hmod' (stage1 hmod' hfn' hp hfam' h1')

end GlobalTheory.CompanionTheory.Ar.Num.CkTop
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DescentRelationsFromModelsStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_family_ckRelations : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) [CharZero O] (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → fnField O x = ⊤ → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → CkRelations O x d p φ Lie W Om OmHT := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.CkTop.ckRelations_of_model | exact GlobalTheory.CompanionTheory.Ar.Num.CkTop.ckRelations_of_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.CkTop.ckRelations_of_model <;> assumption)
end
