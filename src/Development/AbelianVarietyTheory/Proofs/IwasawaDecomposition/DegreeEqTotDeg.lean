module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntMulMemInvHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemVGsOfMemQE
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GmapToAddSubgroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgJetSet
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetSdLatReps
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

namespace GlobalTheory.Mem.Col2.JetEx

theorem exists_finset_sdLat_reps : ∀ (X : Fields), X.Ok → ∀ n : ℕ, ∃ T : Finset (Submodule (𝓞 X.E) (Sp X.E n)), (∀ N ∈ T, IsSdLat N) ∧ ∀ N : Submodule (𝓞 X.E) (Sp X.E n), IsSdLat N → ∃ N₀ ∈ T, ∃ γ : UF X.E n, N = gmap γ.1 N₀ := by
  intro X hX n
  obtain ⟨s, hs, H⟩ := unimod_finite (E := X.E) (posStar_of_conj hX.conjE) n
  refine ⟨s, hs, fun N hN => ?_⟩
  obtain ⟨N₀, h₀, g, hg, e⟩ := H N hN.1 hN.2
  exact ⟨N₀, h₀, ⟨g, hg⟩, e.symm⟩

end GlobalTheory.Mem.Col2.JetEx
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

namespace GlobalTheory.Mem.Col2.JetFin

theorem finAlg_range {E : Type} [Field E] [NumberField E] (f : E →+* ℂ) : FinAlg (Set.range f) := by
  classical
  let b := Module.finBasis ℚ E
  refine (finAlg_of_finite (T := Set.range (f ∘ b)) (Set.finite_range _) ?_).closure.mono ?_
  · rintro _ ⟨i, rfl⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom f.toRatAlgHom
  · rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul, Rat.smul_def]
    exact mul_mem (SubfieldClass.ratCast_mem _ _) (Subfield.subset_closure ⟨i, rfl⟩)

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))

theorem thInd_congr (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x x' : HomE X.E a b)
    (h : x - x' ∈ mulLat c (homAt S N N')) : A.thInd S N N' c x = A.thInd S N N' c x' := by
  unfold Amb.thInd Amb.liftW
  rw [isLift_congr A S N N' c x x' h]

theorem finite_thInd (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (M c : ℕ)
    (hN : IsSdLat N) (hN' : IsSdLat N') (hM : 0 < M) (hc : 0 < c) :
    (A.thInd S N N' c '' (divLat M (homAt S N N') : Set (HomE X.E a b))).Finite := by
  have := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S N N' M c hN.1 hN'.1 hM hc).1
  refine (Set.finite_range fun q : (↥(divLat M (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype) =>
    A.thInd S N N' c (Quotient.out q).1).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, thInd_congr A S N N' c _ _ ?_⟩
  have := (Submodule.Quotient.eq ((mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype)).1
    (Quotient.out_eq (Submodule.Quotient.mk ⟨x, hx⟩ : (↥(divLat M (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype)))
  exact this

noncomputable def pullLin (γ : Sp X.E a ≃ₗ[X.E] Sp X.E a) (γ' : Sp X.E b ≃ₗ[X.E] Sp X.E b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b where
  toFun := A.pullV a b γ γ'
  map_add' z w := by
    funext τ i j
    simp only [Amb.pullV, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' t z := by
    funext τ i j
    simp only [Amb.pullV, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem finAlg_jetSet : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M n : ℕ), X.Ok → 0 < M → A.ESmooth a b → A.ThIndEq a b S M → A.ChiLaw a b → JetAlg A a b S M → (∀ τ, IsAlgebraic ℚ (A.cD τ)) → FinAlg (jetSet A a b S M n) := by
  intro X A a b S M n hX hM hE hT hC hJ hD
  classical
  obtain ⟨Ta, hTa, hTa'⟩ := GlobalTheory.Mem.Col2.JetEx.exists_finset_sdLat_reps X hX a
  obtain ⟨Tb, hTb, hTb'⟩ := GlobalTheory.Mem.Col2.JetEx.exists_finset_sdLat_reps X hX b
  let Z₀ : Set ℂ := ⋃ N ∈ (Ta : Set _), ⋃ N' ∈ (Tb : Set _), ⋃ c ∈ (M.divisors : Set ℕ),
    ⋃ G ∈ A.thInd S N N' c '' (divLat M (homAt S N N') : Set (HomE X.E a b)),
      ⋃ e ∈ {e : DVar X.Tau a b →₀ ℕ | e.degree ≤ n}, {(A.chiF a b N N')⁻¹ * derivAt0 G e}
  have hZ₀ : FinAlg Z₀ := by
    refine finAlg_biUnion Ta.finite_toSet fun N hN => finAlg_biUnion Tb.finite_toSet fun N' hN' =>
      finAlg_biUnion (Finset.finite_toSet _) fun c hc => ?_
    have hc' : c ∣ M := Nat.dvd_of_mem_divisors hc
    have hc0 : 0 < c := Nat.pos_of_mem_divisors hc
    refine finAlg_biUnion (finite_thInd A S N N' M c (hTa N hN) (hTb N' hN') hM hc0) ?_
    rintro _ ⟨x, hx, rfl⟩
    refine finAlg_biUnion (Finsupp.finite_of_degree_le n) fun e _ => finAlg_of_finite (Set.finite_singleton _) ?_
    rintro _ rfl
    exact hJ N N' c x ⟨hTa N hN, hTb N' hN', hc0, hc', hx⟩ e
  have h1 : FinAlg (Set.range A.cD) := finAlg_of_finite (Set.finite_range _) (by rintro _ ⟨τ, rfl⟩; exact hD τ)
  have h2 : FinAlg (⋃ τ ∈ (Set.univ : Set X.Tau), Set.range (X.embC A.σ₀ τ)) :=
    finAlg_biUnion Set.finite_univ fun τ _ => finAlg_range _
  refine ((hZ₀.union h1).union h2).closure.mono ?_
  set K₀ := Subfield.closure ((Z₀ ∪ Set.range A.cD) ∪ ⋃ τ ∈ (Set.univ : Set X.Tau), Set.range (X.embC A.σ₀ τ)) with hK₀
  have hemb : ∀ τ x, X.embC A.σ₀ τ x ∈ K₀ := fun τ x =>
    Subfield.subset_closure (Or.inr (Set.mem_biUnion (Set.mem_univ τ) ⟨x, rfl⟩))
  have hcD : ∀ τ, A.cD τ ∈ K₀ := fun τ => Subfield.subset_closure (Or.inl (Or.inr ⟨τ, rfl⟩))
  rintro _ ⟨N, N', c, x, e, hr, he, rfl⟩
  obtain ⟨N₀, hN₀, γ, rfl⟩ := hTa' N hr.1
  obtain ⟨N₀', hN₀', γ', rfl⟩ := hTb' N' hr.2.1
  obtain ⟨x₀, rfl⟩ : ∃ x₀ : HomE X.E a b, x = γ'.1.toLinearMap ∘ₗ x₀ ∘ₗ γ.1.symm.toLinearMap :=
    ⟨γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap, by ext v; simp⟩
  have hr₀ : InRange S M c N₀ N₀' x₀ :=
    ⟨hTa _ hN₀, hTb _ hN₀', hr.2.2.1, hr.2.2.2.1, (divLat_gmap_iff S M _ _ _ _ _).1 hr.2.2.2.2⟩
  have hth : A.thInd S (gmap γ.1 N₀) (gmap γ'.1 N₀') c (γ'.1.toLinearMap ∘ₗ x₀ ∘ₗ γ.1.symm.toLinearMap) =
      fun z => A.thInd S N₀ N₀' c x₀ (pullLin A γ.1 γ'.1 z) := funext (hT γ γ' N₀ N₀' c x₀ hr₀)
  have key : (A.chiF a b N₀ N₀')⁻¹ * derivAt0 (fun z => A.thInd S N₀ N₀' c x₀ (pullLin A γ.1 γ'.1 z)) e ∈ K₀ := by
    refine GlobalTheory.Mem.JetChain.derivAt0_comp_mem X.Tau a b n K₀ _ _ _ (indSmooth_of A a b S M hE N₀ N₀' c x₀ hr₀) ?_ ?_ e he
    · intro k τ i j
      show A.pullV a b γ.1 γ'.1 (coordX k) τ i j ∈ K₀
      unfold Amb.pullV
      refine sum_mem fun k' _ => sum_mem fun l _ => mul_mem (mul_mem (hemb _ _) ?_) (hemb _ _)
      unfold coordX
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro e' he'
      refine Subfield.subset_closure (Or.inl (Or.inl ?_))
      refine Set.mem_biUnion hN₀ (Set.mem_biUnion hN₀' (Set.mem_biUnion (x := c) ?_ (Set.mem_biUnion ⟨x₀, hr₀.2.2.2.2, rfl⟩
        (Set.mem_biUnion (x := e') he'.le rfl))))
      exact Finset.mem_coe.2 (Nat.mem_divisors.2 ⟨hr₀.2.2.2.1, hM.ne'⟩)
  show _ ∈ K₀
  rw [hth, hC γ γ' N₀ N₀' hr₀.1 hr₀.2.1, jetC, mul_inv, mul_assoc, mul_left_comm (A.chiF a b N₀ N₀')⁻¹]
  refine mul_mem (inv_mem (mul_mem (zpow_mem (prod_mem fun τ _ => hemb _ _) _) (zpow_mem (prod_mem fun τ _ => hemb _ _) _)))
    (mul_mem (prod_mem fun k _ => pow_mem (hcD _) _) key)

end GlobalTheory.Mem.Col2.JetFin
end

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker
open ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar)

namespace JetEx

@[reducible] def hostFields {R : Ranks} (H : Host R) : Fields where
  F := H.F
  E := H.E
  K := H.E
  starE := H.cmStar
  starK := H.cmStar
  Tau := Tau R
  deTau := Classical.decEq _
  emb τ := (H.sigmaOf (τ : R.GG) : H.E →+* H.E)

def hostAmb {R : Ranks} {H : Host R} (J : AmbIn H) (χ : Submodule (𝓞 H.E) H.E → ℂ) : Amb (hostFields H) where
  σ₀ := H.φ₀
  δ := J.δ
  d := H.d
  sc := (TaylorLogMetric.area (Th.lamOf H ⊤ J.δ))⁻¹
  AA := Th.perAA H ⊤
  cD := J.cD
  e a b N N' := J.V.eNat χ a b N N'
  chiF a b N N' := Th.chiFac H χ a b N N'

theorem jetSet_amb (B : Base) (J : AmbIn B.host) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (a b : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 B.host.E))) (M n : ℕ) :
    jetSet (J.amb B χ) a b S M n = jetSet (hostAmb J χ) a b S M n := by
  have h : B.fields.embC (J.amb B χ).σ₀ = (hostFields B.host).embC (hostAmb J χ).σ₀ := funext fun τ => B.fields_embC τ
  have h2 : ∀ N N' c x, (J.amb B χ).thInd (a := a) (b := b) S N N' c x = (hostAmb J χ).thInd S N N' c x := by
    intro N N' c x
    unfold Amb.thInd
    rw [h]
    rfl
  unfold jetSet
  simp only [h2]
  rfl


open Classical in
@[reducible] def hostWts (P : Pre) : Wts (hostFields P.host) P.Word P.R where
  row := fun τ => RowPar.of (P.hc τ)
  hc := P.hcW
  tops := Finset.univ.filter fun τ : Tau P.R => (τ : P.R.GG) ∈ P.host.topPlaces

def totDeg (P : Pre) (u : P.Word) (i : ℕ) : ℕ := (∑ τ, ∑ r, ((hostWts P).nuW u (i + 1) τ).w r).toNat

theorem degree_eq_totDeg (B : Base) (u : B.Word) (i : ℕ) (e : DVar B.fields.Tau (B.R.N i) (B.R.N (i + 1)) →₀ ℕ)
    (he : ∀ τ, (monoDeg e τ : ℤ) = nuDeg B u i τ) : e.degree = totDeg B.toPre u i := by
  have h1 : e.degree = ∑ τ, monoDeg e τ := by
    simp only [monoDeg_eq_sum]
    rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun τ _ => Fintype.sum_prod_type _
  have h2 : ((∑ τ, monoDeg e τ : ℕ) : ℤ) = ∑ τ, ∑ r, ((hostWts B.toPre).nuW u (i + 1) τ).w r := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun τ _ => he τ
  rw [h1, totDeg, ← h2, Int.toNat_natCast]

def ramSet {R : Ranks} (H : Host R) (ξ : HChar H.E) : Set (HeightOneSpectrum (𝓞 H.F)) :=
  {v | ¬ ∀ a : Ideles H.E, finAf H.F H.E a ∈ inertAt H.E v → ξ.1 a = 1}

theorem qprime_eq_ramSet {R : Ranks} (H : Host R) {K : Type} [Field K] {σ : K →+* ℂ} {μ : Chr H.F H.E K} {ξ : HChar H.E}
    (h : Reads σ μ ξ) : Qprime μ = ramSet H ξ := by
  have key : ∀ a, ξ.1 a = 1 ↔ μ (finAf H.F H.E a) = 1 := fun a => by
    rw [Units.ext_iff, h a, Units.ext_iff, Units.val_one, Units.val_one, map_eq_one_iff _ σ.injective]
  ext v
  refine not_congr ⟨fun h1 a ha => (key a).2 (h1 ha), fun h1 y hy => ?_⟩
  obtain ⟨a, rfl⟩ := finAf_surjective H.F H.E y
  exact (key a).1 (h1 a hy)

def badP (P : Pre) (Ξ : Set (HChar P.host.E)) : Set (HeightOneSpectrum (𝓞 P.host.E)) :=
  (⋃ u, {Q | ((P.T u : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal}) ∪ (⋃ i, {Q | ((P.host.g i : ℕ) : 𝓞 P.host.E) ∈ Q.asIdeal}) ∪
    ⋃ ξ ∈ {ξ ∈ Ξ | (ramSet P.host ξ).Finite}, ⋃ v ∈ ramSet P.host ξ, {Q | Q.asIdeal.under (𝓞 P.host.F) = v.asIdeal}

theorem finite_mem {E : Type} [Field E] [NumberField E] {a : 𝓞 E} (ha : a ≠ 0) :
    {Q : HeightOneSpectrum (𝓞 E) | a ∈ Q.asIdeal}.Finite := by
  simpa only [Ideal.dvd_span_singleton] using Ideal.finite_factors (I := Ideal.span {a}) (by simpa using ha)

theorem badPrimes_finite₂ (P : Pre) {Ξ : Set (HChar P.host.E)} (h : Ξ.Finite) : (badP P Ξ).Finite := by
  have hfin : {ξ ∈ Ξ | (ramSet P.host ξ).Finite}.Finite := h.subset fun _ hξ => hξ.1
  refine ((Set.finite_iUnion fun u => finite_mem ?_).union (Set.finite_iUnion fun i => finite_mem ?_)).union
    (hfin.biUnion fun ξ hξ => Set.Finite.biUnion hξ.2 fun v _ => ?_)
  · exact Nat.cast_ne_zero.2 (P.T_prime u).ne_zero
  · exact Nat.cast_ne_zero.2 (P.host.g_prime i).ne_zero
  · obtain ⟨a, ha, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    refine (finite_mem (a := algebraMap (𝓞 P.host.F) (𝓞 P.host.E) a) ?_).subset fun Q hQ => ?_
    · exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 h0
    · have : a ∈ Q.asIdeal.under (𝓞 P.host.F) := hQ ▸ ha
      exact this

theorem mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {Q : HeightOneSpectrum A} (h : Q ∈ divs a) :
    a ∈ Q.asIdeal := by
  unfold divs at h
  split_ifs at h with h1
  · exact h1.mem_toFinset.1 h
  · simp at h

variable {B : Base} {X : PreX B.toPre}

theorem rowSG_subset {I : ColIn B X} (h : I.Ok) (a : I.ι) :
    ∀ Q ∈ rowSG (B.primes X) I.sel (I.tup a), Q ∈ badP B.toPre (Set.range I.xi) := by
  classical
  intro Q hQ
  rcases Finset.mem_union.1 hQ with hQ | hQ
  · obtain ⟨i, hi⟩ : ∃ i, Q ∈ (B.primes X).vG i := by
      rcases Finset.mem_union.1 hQ with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    refine Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, ?_⟩))
    have := Q.asIdeal.mul_mem_left ((B.primes X).piG i) (mem_of_mem_divs hi)
    rwa [B.primes_piG_norm X i] at this
  · unfold QE at hQ
    split_ifs at hQ with h1
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hQ
      have e := qprime_eq_ramSet B.host (h.xi_reads a)
      exact Or.inr (Set.mem_iUnion₂.2 ⟨I.xi a, ⟨⟨a, rfl⟩, e ▸ h1⟩,
        Set.mem_iUnion₂.2 ⟨v, e ▸ h1.mem_toFinset.1 hv, h.sel_ok v⟩⟩)
    · simp at hQ

theorem Sb_subset {I : ColIn B X} (h : I.Ok) (a : I.ι) (u : B.Word) :
    ∀ Q ∈ I.Sb a u, Q ∈ badP B.toPre (Set.range I.xi) := by
  classical
  intro Q hQ
  rcases Finset.mem_union.1 hQ with hQ | hQ
  · refine Or.inl (Or.inl (Set.mem_iUnion.2 ⟨u, ?_⟩))
    have := Q.asIdeal.mul_mem_right (B.fields.conjO ((B.primes X).piT u)) (mem_of_mem_divs hQ)
    rwa [B.primes_piT_norm X u] at this
  · exact rowSG_subset h a Q hQ

section Lat

open Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.ThetaMove.SeamMoves

theorem eNat_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (V : Formalism.L2.Ker.Base D cc δ) (hc : StandardLatticesGL3.Crv D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (hL : StandardLatticesGL3.SD D L) (hL' : StandardLatticesGL3.SD D L') : V.eNat χ a b L L' ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) L L' := by
  have s0 := GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.VacuumScalar.moves_one D a)
  have s0' := GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.VacuumScalar.moves_one D b)
  have h0 := WeilVac.thZero_mem V (GlobalTheory.FourthRootStd.stdOK_of_crv D cc δ V hc) a b
  have h1 := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc a b _ _ (Or.inr ⟨_, _, s0, s0', rfl⟩)
    (Or.inr ⟨_, _, hL, s0', rfl⟩) _ h0).2.1
  have h2 := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc a b _ _ (Or.inr ⟨_, _, hL, s0', rfl⟩)
    (Or.inr ⟨_, _, hL, hL', rfl⟩) _ h1).2.1
  exact GlobalTheory.InertSign.ThSp_smul (Formalism.L2.Ker.Base.chiFac χ a b L L') h2

theorem laHyp_empty {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (V : Formalism.L2.Ker.Base D cc δ)
    (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) {a b : ℕ} (hX : X.Ok) (hs : s.Ok) (hc : StandardLatticesGL3.Crv D cc δ) (ha : Even a) (hb : Even b) :
    (ambOf s V χ cD).LaHyp a b ∅ := by
  have hL := LatticeFacts.latAll V hc.1 hc.2
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ V χ cD hs
  have hq := qIntAll_of_latAll D cc δ V hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨delta_ne_zero V, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s V χ cD, fun N N' h h' => ?_⟩
  obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s V χ cD).sc)
    (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s V χ cD).d (ambOf s V χ cD).sc) (TaylorLogMetric.al D V.tor)
    (lam (ambOf s V χ cD) N N') (lam (ambOf s V χ cD) N N') (TaylorLogMetric.La D V.tor (s.lat N) (s.lat N'))
    (TaylorLogMetric.La D V.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
    (fun x hx => by
      obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
      exact alV_eq s V x hm)
    (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
  exact ⟨h3 (V.eNat χ a b (s.lat N) (s.lat N')) (eNat_mem V hc χ (hsd _ _ h) (hsd _ _ h')).2, h1, h2⟩

end Lat

theorem finAlg_step (hL : StagesInhab.HasLetters B.toPre) {I : ColIn B X} (h : I.Ok) (a : I.ι) (u : B.Word) (i j M n : ℕ)
    (hM : 0 < M) : FinAlg (jetSet I.A (B.R.N i) (B.R.N j) (I.Sb a u) M n) := by
  obtain ⟨⟨B, C, W, V, S, N, G⟩, rfl, -⟩ := StagesInhab.exists_stages_over B hL 1
  have hs := seamOf_ok B C W V S N G
  obtain ⟨hδ, hc⟩ := (AmbIn.ok_iff B C W V S N G I.J).1 h.amb_ok
  have hcc : TaylorLogMetric.IsCurveIdeal (assemble B C W V S N G) ⊤ := ⟨top_ne_bot, by simp⟩
  have hχ : TaylorLogMetric.IsChi (assemble B C W V S N G) I.chi := GlobalTheory.Mem.ChiIdeal.isChi_chiId _ _ I.C.isChi
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hi := GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N B.R i
  have hj := GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.even_N B.R j
  have hA : I.A = ambOf (seamOf B C W V S N G) (I.J.toRec B C W V S N G) I.chi I.J.cD :=
    AmbIn.amb_eq_ambOf B C W V S N G I.J I.chi
  have hne : I.A.AA ≠ ⊥ := by
    rw [hA]
    exact GlobalTheory.ThetaMove.SeamMoves.aa_ne_bot _ _ _ _ top_ne_bot
  have hLa : I.A.LaHyp (B.R.N i) (B.R.N j) (I.Sb a u) := by
    have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes _ (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
    have h0 := laHyp_empty (seamOf B C W V S N G) (I.J.toRec B C W V S N G) I.chi I.J.cD hX hs ⟨hcc, hδ⟩ hi hj
    rw [hA]
    exact ⟨h0.1, h0.2.1, fun P hP => (bad P hP).1, fun P hP => GlobalTheory.PeriodIdealUnit.locP_AA_eq_one _ _ _ _ _ _ _ _ P
      (bad P hP).2.1 (bad P hP).2.2.1 (by rw [Ideal.absNorm_top]; exact Nat.coprime_one_left _), h0.2.2.2.2⟩
  have hE := GlobalTheory.T.normalisedFamily_satisfies_equivarianceLaws _ _ _ (I.J.toRec B C W V S N G) _ hcc hδ hχ
  have hJ := GlobalTheory.T.vacuum_entire_and_normalizedJets_algebraic _ _ (seamOf B C W V S N G) _ _ (I.J.toRec B C W V S N G) I.chi I.J.cD _ _ hX hs hcc hδ hχ hi hj
  rw [← hA] at hJ
  refine JetFin.finAlg_jetSet _ _ _ _ _ _ _ hX hM hJ.1 (IndEq.thIndEq_of_vacEq _ _ _ _ _ _ hX hLa hne hM ?_) ?_ (hJ.2 _ _)
    fun τ => ?_
  · rw [hA]
    exact VacEqPf.vacEq_ambOf _ _ _ _ _ _ _ _ _ _ hs hE hi hj
  · rw [hA]
    exact ChiFacLaw.chiLaw_ambOf _ _ _ _ _ _ _ _ _ _ hs hχ
  · obtain ⟨K, _, -, hK⟩ := h.amb_ok.dgen
    obtain ⟨s, hs, -⟩ := hK τ
    rw [I.A_cD, ← hs]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) s).algHom K.val

def amb0 {R : Ranks} (H : Host R) : AmbIn H := (exists_ambIn_ok H).choose

theorem qPow_ne_zero {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) : qOf Q ^ n ≠ 0 :=
  pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 Q.ne_bot)


end JetEx

end GlobalTheory.Mem.Col2

end
