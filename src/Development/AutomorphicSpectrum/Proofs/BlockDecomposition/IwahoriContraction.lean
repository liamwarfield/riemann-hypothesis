module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriContraction
open ValuativeRel Matrix Topology MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.IwContract

open PositivityTheory.Rg.Tf.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

theorem mem_iwahori_iff {g : GL (Fin n) F} :
    g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F ↔ g ∈ GlobalTheory.SmGL.iwahori F (Fin n) := by
  rw [GlobalTheory.SmGL.mem_iwahori]; rfl


end GlobalTheory.CompanionTheory.IwContract
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsDomMonoid
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem isDom_monoid : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), D.IsDom 1 ∧ ∀ t t' : D.T, D.IsDom t → D.IsDom t' → D.IsDom (t * t') := by
  intro G _ _ _ D
  refine ⟨⟨fun n hn => by simpa using hn, fun n hn => by simpa using hn,
    fun x hx => ⟨by simpa using hx, by simpa using hx⟩⟩, ?_⟩
  rintro t t' ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
  refine ⟨fun n hn => ?_, fun n hn => ?_, fun x hx => ⟨?_, ?_⟩⟩
  · have h := h1 _ (h1' n hn)
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := h2' _ (h2 n hn)
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := (h3 _ (h3' x hx).1).1
    rw [Subgroup.coe_mul]
    convert h using 1
    group
  · have h := (h3' _ (h3 x hx).2).2
    rw [Subgroup.coe_mul]
    convert h using 1
    group

end GlobalTheory.CompanionTheory.Cass
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JhMultMulLeOfSteps
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.CsStages

variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

theorem jhMult_add_le {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (h0 : ∀ u, p (ι u) = 0) :
    jhMult σ ρ₁ + jhMult σ ρ₂ ≤ jhMult σ ρ := by
  refine ENat.biSup_add_biSup_le' ⟨0, occurs_zero _ _⟩ ⟨0, occurs_zero _ _⟩ fun a ha b hb => ?_
  rw [← Nat.cast_add]
  exact le_iSup₂_of_le _ (occurs_add ι p hι hp h0 ha hb) le_rfl

theorem jhMult_mul_le_of_steps (σ : Representation F G W) (ρ : Representation F G V)
    (A : Subrepresentation ρ → ℕ∞) (m : ℕ∞) (hmono : ∀ S T : Subrepresentation ρ, T ≤ S → A T ≤ A S)
    (hstep : ∀ S T : Subrepresentation ρ, T ≤ S → Nonempty ((subQuot S T).Equiv σ) → A T + m ≤ A S) :
    jhMult σ ρ * m ≤ A ⊤ := by
  have key : ∀ r, OccursTimes σ ρ r → (r : ℕ∞) * m ≤ A ⊤ := by
    rintro r ⟨S, T, h1, h2, h3⟩
    have hi : ∀ (i : ℕ) (hi : i < r), ((i + 1 : ℕ) : ℕ∞) * m ≤ A (S ⟨i, hi⟩) := by
      intro i
      induction i with
      | zero =>
        intro hi
        have := hstep _ _ (h1 ⟨0, hi⟩) (h3 ⟨0, hi⟩)
        simpa using le_trans le_add_self this
      | succ i ih =>
        intro hi
        have h4 := ih (by omega)
        have h5 := hmono _ _ (h2 ⟨i, by omega⟩ ⟨i + 1, hi⟩ (by simp [Fin.lt_def]))
        have h6 := hstep _ _ (h1 ⟨i + 1, hi⟩) (h3 ⟨i + 1, hi⟩)
        refine le_trans ?_ h6
        have : (((i + 1 + 1 : ℕ)) : ℕ∞) * m = ((i + 1 : ℕ) : ℕ∞) * m + m := by
          push_cast; ring
        rw [this]
        exact add_le_add (h4.trans h5) le_rfl
    rcases r with _ | r
    · simp
    · exact (hi r (by omega)).trans (hmono _ _ le_top)
  unfold jhMult
  rw [ENat.iSup_mul]
  refine iSup_le fun r => ?_
  rw [ENat.iSup_mul]
  exact iSup_le fun hr => key r hr

end GlobalTheory.CompanionTheory.CsStages
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCharacterSeparatingLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCharacterSeparatingLattice
open MeasureTheory Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi

noncomputable section
namespace GlobalTheory.CompanionTheory.CharacterBiduality

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem indicator_mem_SB {n : ℕ} (A : AddSubgroup (Fin n → k))
    (hAc : IsCompact (A : Set (Fin n → k))) (hAo : IsOpen (A : Set (Fin n → k))) :
    (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) ∈ SB (Fin n → k) := by
  have hcl : IsClopen (A : Set (Fin n → k)) := ⟨AddSubgroup.isClosed_of_isOpen A hAo, hAo⟩
  exact ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hcl).isLocallyConstant,
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _⟩

theorem fourier_sub_translate_eq_zero [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    (ψ : AddChar k Circle) (hψ : Continuous ψ) (μ : Measure (Fin n → k)) [μ.IsAddHaarMeasure]
    (A : AddSubgroup (Fin n → k)) (hAc : IsCompact (A : Set (Fin n → k)))
    (hAo : IsOpen (A : Set (Fin n → k))) (x : Fin n → k)
    (hx : ∀ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) → ψ (η ⬝ᵥ x) = 1) (y : Fin n → k) :
    ∫ z, ((A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) z -
        (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) (z + x)) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
  haveI := secondCountable k
  haveI := t2Space k
  set g : (Fin n → k) → ℂ := (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) with hgdef
  have hg : g ∈ SB (Fin n → k) := indicator_mem_SB A hAc hAo
  have hc : Continuous fun z : Fin n → k => (ψ (z ⬝ᵥ y) : ℂ) :=
    continuous_subtype_val.comp (hψ.comp (continuous_id.dotProduct continuous_const))
  have hi1 : Integrable (fun z => g z * (ψ (z ⬝ᵥ y) : ℂ)) μ :=
    (hg.1.continuous.mul hc).integrable_of_hasCompactSupport hg.2.mul_right
  have hgx : HasCompactSupport fun z => g (z + x) := hg.2.comp_homeomorph (Homeomorph.addRight x)
  have hi2 : Integrable (fun z => g (z + x) * (ψ (z ⬝ᵥ y) : ℂ)) μ :=
    ((hg.1.continuous.comp (continuous_id.add continuous_const)).mul hc).integrable_of_hasCompactSupport
      hgx.mul_right
  have e1 : ∫ z, g (z + x) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ =
      (ψ (-(x ⬝ᵥ y)) : ℂ) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ := by
    have h := integral_add_right_eq_self (μ := μ) (fun w => g w * (ψ ((w - x) ⬝ᵥ y) : ℂ)) x
    simp only [add_sub_cancel_right] at h
    rw [h, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have hwx : (w - x) ⬝ᵥ y = w ⬝ᵥ y + -(x ⬝ᵥ y) := by rw [sub_dotProduct, sub_eq_add_neg]
    beta_reduce
    rw [hwx, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp only [sub_mul]
  rw [integral_sub hi1 hi2, e1]
  by_cases hy : ∀ a ∈ A, ψ (y ⬝ᵥ a) = 1
  · have h1 : ψ (x ⬝ᵥ y) = 1 := by rw [dotProduct_comm]; exact hx y hy
    have h2 : ψ (-(x ⬝ᵥ y)) = 1 := by rw [AddChar.map_neg_eq_inv, h1, inv_one]
    simp [h2]
  · push Not at hy
    obtain ⟨a, haA, hne⟩ := hy
    have h0 : ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
      have h := integral_add_right_eq_self (μ := μ) (fun w => g w * (ψ (w ⬝ᵥ y) : ℂ)) a
      have h3 : ∫ z, g (z + a) * (ψ ((z + a) ⬝ᵥ y) : ℂ) ∂μ =
          (ψ (y ⬝ᵥ a) : ℂ) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        have hga : g (w + a) = g w := by
          by_cases hw : w ∈ A
          · simp [hgdef, Set.indicator, hw, A.add_mem hw haA]
          · have : w + a ∉ A := fun h => hw (by simpa using A.sub_mem h haA)
            simp [hgdef, Set.indicator, hw, this]
        simp only [hga, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, dotProduct_comm a y]
        ring
      rw [h3] at h
      have h4 : (1 - (ψ (y ⬝ᵥ a) : ℂ)) * ∫ z, g z * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 := by
        rw [sub_mul, one_mul, h, sub_self]
      refine (mul_eq_zero.1 h4).resolve_left fun h5 => hne (Circle.ext ?_)
      simpa using (sub_eq_zero.1 h5).symm
    simp [h0]

theorem exists_annihilator_ne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A →
    ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by
  intro k _ _ _ _ ψ hψ h1 n A hAc hAo x hxA
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := secondCountable k
  haveI := t2Space k
  let μ : Measure (Fin n → k) := Measure.addHaar
  set g : (Fin n → k) → ℂ := (A : Set (Fin n → k)).indicator (fun _ => (1 : ℂ)) with hgdef
  have hg : g ∈ SB (Fin n → k) := indicator_mem_SB A hAc hAo
  have hgx : (fun z => g (z + x)) ∈ SB (Fin n → k) :=
    ⟨hg.1.comp_continuous (continuous_id.add continuous_const),
      hg.2.comp_homeomorph (Homeomorph.addRight x)⟩
  have hf : (fun z => g z - g (z + x)) ∈ SB (Fin n → k) := (SB (Fin n → k)).sub_mem hg hgx
  obtain ⟨s, hs⟩ := fourier_inversion_pi μ hc hf
  have hz : ∀ y : Fin n → k, ∫ z, (g z - g (z + x)) * (ψ (z ⬝ᵥ y) : ℂ) ∂μ = 0 :=
    fourier_sub_translate_eq_zero ψ hψ μ A hAc hAo x hcon
  simp only [hz, integral_zero] at hs
  have hpos : ∀ r : kˣ, 0 < μ.real (box (Fin n) r) := fun r => by
    have h1 : (0 : Fin n → k) ∈ box (Fin n) r := fun i _ => by simp [cball]
    have h2 : 0 < μ (box (Fin n) r) := (isOpen_box r).measure_pos μ ⟨0, h1⟩
    exact ENNReal.toReal_pos h2.ne' (isCompact_box r).measure_lt_top.ne
  have hne : ((μ.real (box (Fin n) s) * μ.real (box (Fin n) (c * s⁻¹)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (hpos s) (hpos _)).ne'
  have h0 : g 0 - g (0 + x) = 0 := (mul_eq_zero.mp hs.symm).resolve_left hne
  have hg0 : g 0 = 1 := Set.indicator_of_mem (SetLike.mem_coe.2 A.zero_mem) _
  have hgx0 : g (0 + x) = 0 := by
    rw [zero_add]
    exact Set.indicator_of_notMem (fun h => hxA h) _
  rw [hg0, hgx0] at h0
  simp at h0

end GlobalTheory.CompanionTheory.CharacterBiduality
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCharacterSeparatingLatticeStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_separating_lattice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → ∀ x : Fin n → k, x ∉ A → ∃ η : Fin n → k, (∀ a ∈ A, ψ (η ⬝ᵥ a) = 1) ∧ ψ (η ⬝ᵥ x) ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne | exact GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne | (intros; apply GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinianLimitLiftOfCompatibleStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinianLimitLiftOfCompatible
open CrystallineSemistableComparison

namespace GlobalTheory.CompanionTheory.ArtinTower

universe w

theorem coset_chain {W : Type} [CommRing W] {M : Type w} [AddCommGroup M] [Module W M]
    [IsArtinian W M] (K : ℕ → Submodule W M) (hK : ∀ k, K (k + 1) ≤ K k) (c : ℕ → M)
    (hc : ∀ k, c (k + 1) - c k ∈ K k) : ∃ x, ∀ k, x - c k ∈ K k := by
  have hanti : Antitone K := antitone_nat_of_succ_le hK
  obtain ⟨m, hm⟩ := IsArtinian.monotone_stabilizes
    (⟨fun k => OrderDual.toDual (K k), hanti.dual_right⟩ : ℕ →o (Submodule W M)ᵒᵈ)
  have hdiff : ∀ k j, c (k + j) - c k ∈ K k := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : c (k + j + 1) - c (k + j) ∈ K k := hanti (Nat.le_add_right k j) (hc (k + j))
      have h2 := add_mem h1 ih
      rw [sub_add_sub_cancel] at h2
      exact h2
  refine ⟨c m, fun k => ?_⟩
  rcases le_total k m with hkm | hmk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
    exact hdiff k j
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmk
    have hKeq : K m = K (m + j) := hm (m + j) (Nat.le_add_right m j)
    rw [← hKeq]
    have h3 := neg_mem (hdiff m j)
    rw [neg_sub] at h3
    exact h3

section
variable {W : Type} [CommRing W] (S : Sys.{w} W) (N : ∀ n, Submodule W (S.M n))
  (y : ∀ n, S.M n)

noncomputable def imgSub : ℕ → ∀ n, Submodule W (S.M n)
  | 0, n => N n
  | k + 1, n => (imgSub k (n + 1)).map (S.r n)

noncomputable def imgPt : ℕ → ∀ n, S.M n
  | 0, n => y n
  | k + 1, n => S.r n (imgPt k (n + 1))

def stable (n : ℕ) : Set (S.M n) := {x | ∀ k, x - imgPt S y k n ∈ imgSub S N k n}

variable {S N y}

theorem imgSub_succ_le (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) :
    ∀ k n, imgSub S N (k + 1) n ≤ imgSub S N k n := by
  intro k
  induction k with
  | zero =>
    intro n
    show Submodule.map (S.r n) (N (n + 1)) ≤ N n
    exact Submodule.map_le_iff_le_comap.mpr (fun u hu => hN n u hu)
  | succ k ih =>
    intro n
    show Submodule.map (S.r n) (imgSub S N (k + 1) (n + 1)) ≤
      Submodule.map (S.r n) (imgSub S N k (n + 1))
    exact Submodule.map_mono (ih (n + 1))

theorem imgPt_step (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) :
    ∀ k n, imgPt S y (k + 1) n - imgPt S y k n ∈ imgSub S N k n := by
  intro k
  induction k with
  | zero => intro n; exact hy n
  | succ k ih =>
    intro n
    show S.r n (imgPt S y (k + 1) (n + 1)) - S.r n (imgPt S y k (n + 1)) ∈
      Submodule.map (S.r n) (imgSub S N k (n + 1))
    rw [← map_sub]
    exact Submodule.mem_map_of_mem (ih (n + 1))

theorem stable_nonempty (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n)
    (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) (n : ℕ) [IsArtinian W (S.M n)] :
    ∃ x, x ∈ stable S N y n := by
  obtain ⟨x, hx⟩ := coset_chain (fun k => imgSub S N k n) (fun k => imgSub_succ_le hN k n)
    (fun k => imgPt S y k n) (fun k => imgPt_step hy k n)
  exact ⟨x, hx⟩

theorem stable_surj (hN : ∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n)
    (hy : ∀ n, S.r n (y (n + 1)) - y n ∈ N n) {n : ℕ} [IsArtinian W (S.M (n + 1))]
    {x : S.M n} (hx : x ∈ stable S N y n) :
    ∃ x' ∈ stable S N y (n + 1), S.r n x' = x := by
  have hxk : ∀ k, x - imgPt S y k n ∈ imgSub S N k n := hx
  have hA : ∀ k, ∃ u : S.M (n + 1),
      S.r n u = x ∧ u - imgPt S y k (n + 1) ∈ imgSub S N k (n + 1) := by
    intro k
    have h1 : x - imgPt S y (k + 1) n ∈ Submodule.map (S.r n) (imgSub S N k (n + 1)) :=
      hxk (k + 1)
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.mp h1
    refine ⟨v + imgPt S y k (n + 1), ?_, ?_⟩
    · rw [map_add (f := _), hve]
      show x - S.r n (imgPt S y k (n + 1)) + S.r n (imgPt S y k (n + 1)) = x
      exact sub_add_cancel _ _
    · rw [add_sub_cancel_right]
      exact hv
  choose c hc1 hc2 using hA
  have hKanti : ∀ k, LinearMap.ker (S.r n) ⊓ imgSub S N (k + 1) (n + 1) ≤
      LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1) :=
    fun k => inf_le_inf_left _ (imgSub_succ_le hN k (n + 1))
  have hstep : ∀ k, c (k + 1) - c k ∈ LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1) := by
    intro k
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hc1, hc1, sub_self]
    · have e : c (k + 1) - c k = (c (k + 1) - imgPt S y (k + 1) (n + 1)) +
          (imgPt S y (k + 1) (n + 1) - imgPt S y k (n + 1)) - (c k - imgPt S y k (n + 1)) := by
        abel
      rw [e]
      exact sub_mem (add_mem (imgSub_succ_le hN k (n + 1) (hc2 (k + 1)))
        (imgPt_step hy k (n + 1))) (hc2 k)
  obtain ⟨x', hx'⟩ := coset_chain (fun k => LinearMap.ker (S.r n) ⊓ imgSub S N k (n + 1))
    hKanti c hstep
  refine ⟨x', fun k => ?_, ?_⟩
  · have e : x' - imgPt S y k (n + 1) = (x' - c k) + (c k - imgPt S y k (n + 1)) := by abel
    rw [e]
    exact add_mem (Submodule.mem_inf.mp (hx' k)).2 (hc2 k)
  · have h0 := (Submodule.mem_inf.mp (hx' 0)).1
    rw [LinearMap.mem_ker, map_sub, hc1, sub_eq_zero] at h0
    exact h0

end

theorem exists_compatible : ∀ (W : Type) [CommRing W] (S : Sys.{1} W),
    (∀ n, IsArtinian W (S.M n)) → ∀ (N : ∀ n, Submodule W (S.M n)) (y : ∀ n, S.M n),
    (∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) → (∀ n, S.r n (y (n + 1)) - y n ∈ N n) →
    ∃ z : S.lim, ∀ n, z.1 n - y n ∈ N n := by
  intro W _ S hA N y hN hy
  have h0 : ∃ x, x ∈ stable S N y 0 := by
    haveI := hA 0
    exact stable_nonempty hN hy 0
  have hs : ∀ n (x : S.M n), x ∈ stable S N y n →
      ∃ x' ∈ stable S N y (n + 1), S.r n x' = x := fun n x hx => by
    haveI := hA (n + 1)
    exact stable_surj hN hy hx
  let f : ∀ n, {x : S.M n // x ∈ stable S N y n} := fun n =>
    Nat.rec (motive := fun n => {x : S.M n // x ∈ stable S N y n})
      ⟨h0.choose, h0.choose_spec⟩
      (fun n p => ⟨(hs n p.1 p.2).choose, (hs n p.1 p.2).choose_spec.1⟩) n
  have hf : ∀ n, S.r n (f (n + 1)).1 = (f n).1 := fun n =>
    (hs n (f n).1 (f n).2).choose_spec.2
  refine ⟨⟨fun n => (f n).1, ?_⟩, fun n => (f n).2 0⟩
  unfold CrystallineSemistableComparison.Sys.lim
  exact fun n => hf n

end GlobalTheory.CompanionTheory.ArtinTower
end

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artinian_limit_lift_of_compatible : ∀ (W : Type) [CommRing W] (S : Sys.{1} W), (∀ n, IsArtinian W (S.M n)) → ∀ (N : ∀ n, Submodule W (S.M n)) (y : ∀ n, S.M n), (∀ n x, x ∈ N (n + 1) → S.r n x ∈ N n) → (∀ n, S.r n (y (n + 1)) - y n ∈ N n) → ∃ z : S.lim, ∀ n, z.1 n - y n ∈ N n := by
  first | exact @GlobalTheory.CompanionTheory.ArtinTower.exists_compatible | exact GlobalTheory.CompanionTheory.ArtinTower.exists_compatible | (intros; apply GlobalTheory.CompanionTheory.ArtinTower.exists_compatible <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutTranslate
noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise

namespace GlobalTheory.CompanionTheory.HeckeMul

section Generic

variable {G : Type} [Group G]

theorem out_mk_of_right_inv {M : Type} (K : Subgroup G) (φ : G → M)
    (hφ : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (x : G) :
    φ (QuotientGroup.mk x : G ⧸ K).out = φ x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hh]
  exact hφ x h h.2

theorem finsum_out_translate {M : Type} [AddCommMonoid M] (K : Subgroup G) (φ : G → M)
    (hφ : ∀ x, ∀ k ∈ K, φ (x * k) = φ x) (a : G) :
    ∑ᶠ q : G ⧸ K, φ (a * q.out) = ∑ᶠ q : G ⧸ K, φ q.out := by
  rw [← finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) (f := fun q : G ⧸ K => φ q.out)]
  refine finsum_congr fun q => ?_
  have h : (MulAction.toPerm a : Equiv.Perm (G ⧸ K)) q = (QuotientGroup.mk (a * q.out) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [h, out_mk_of_right_inv K φ hφ]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_out_mem (K : Subgroup G) (hK : IsOpen (K : Set G)) {C : Set G} (hC : IsCompact C) :
    {q : G ⧸ K | q.out ∈ C}.Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K) '' C) :=
    hC.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, hq, QuotientGroup.out_eq' q⟩

end Generic

section Hecke

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isHk_right {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (h : IsHk K e) (x : GL ι F)
    {k : GL ι F} (hk' : k ∈ K) : e (x * k) = e x := by
  simpa using h.2.2.2 1 K.one_mem k hk' x

theorem isHk_left {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (h : IsHk K e) (x : GL ι F)
    {k : GL ι F} (hk' : k ∈ K) : e (k * x) = e x := by
  simpa using h.2.2.2 k hk' 1 K.one_mem x

theorem support_hconv (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ) :
    Function.support (hconv K e₁ e₂) ⊆ tsupport e₁ * tsupport e₂ := by
  intro g hg
  obtain ⟨q, hq⟩ : ∃ q : GL ι F ⧸ K, e₁ q.out * e₂ (q.out⁻¹ * g) ≠ 0 := by
    by_contra h
    push_neg at h
    refine (Function.mem_support.1 hg) ?_
    unfold hconv
    simp only [h]
    exact finsum_zero
  exact Set.mem_mul.2 ⟨q.out, subset_tsupport _ (left_ne_zero_of_mul hq), q.out⁻¹ * g,
    subset_tsupport _ (right_ne_zero_of_mul hq), mul_inv_cancel_left _ _⟩

theorem hconv_biinv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂)
    {k₁ k₂ : GL ι F} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (g : GL ι F) :
    hconv K e₁ e₂ (k₁ * g * k₂) = hconv K e₁ e₂ g := by
  have hφ : ∀ x, ∀ k ∈ K, (fun y => e₁ y * e₂ (y⁻¹ * g)) (x * k) = (fun y => e₁ y * e₂ (y⁻¹ * g)) x := by
    intro x k hk'
    show e₁ (x * k) * e₂ ((x * k)⁻¹ * g) = e₁ x * e₂ (x⁻¹ * g)
    rw [isHk_right h₁ x hk', mul_inv_rev, mul_assoc, isHk_left h₂ _ (K.inv_mem hk')]
  have ht := finsum_out_translate K (fun y => e₁ y * e₂ (y⁻¹ * g)) hφ k₁⁻¹
  unfold hconv
  rw [← ht]
  refine finsum_congr fun q => ?_
  show e₁ q.out * e₂ (q.out⁻¹ * (k₁ * g * k₂)) = e₁ (k₁⁻¹ * q.out) * e₂ ((k₁⁻¹ * q.out)⁻¹ * g)
  rw [isHk_left h₁ _ (K.inv_mem hk₁), ← mul_assoc, isHk_right h₂ _ hk₂]
  simp [mul_assoc]

theorem isHk_hconv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂) :
    IsHk K (hconv K e₁ e₂) := by
  refine ⟨h₁.1, h₁.2.1, ?_, fun k₁ hk₁ k₂ hk₂ g => hconv_biinv h₁ h₂ hk₁ hk₂ g⟩
  have hc : IsCompact (tsupport e₁ * tsupport e₂) := IsCompact.mul h₁.2.2.1 h₂.2.2.1
  exact HasCompactSupport.of_support_subset_isCompact hc (support_hconv K e₁ e₂)

theorem hk_eq_sum {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V)
    (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) (w : V) (A : Finset (GL ι F ⧸ K))
    (hA : ∀ q : GL ι F ⧸ K, e q.out ≠ 0 → q ∈ A) :
    hk ρ K e w = ∑ q ∈ A, e q.out • ρ q.out w := by
  unfold hk
  refine finsum_eq_sum_of_support_subset _ ?_
  intro q hq
  refine Finset.mem_coe.2 (hA q fun h0 => (Function.mem_support.1 hq) ?_)
  show e q.out • ρ q.out w = 0
  rw [h0, zero_smul]

theorem hk_hconv {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) {v : V}
    (hv : v ∈ fixed ρ K) :
    hk ρ K (hconv K e₁ e₂) v = hk ρ K e₁ (hk ρ K e₂ v) := by
  have hvk : ∀ k ∈ K, ρ k v = v := fun k hk' => by
    have := hv ⟨k, hk'⟩
    simpa using this
  have c1 : IsCompact (tsupport e₁) := h₁.2.2.1
  have c2 : IsCompact (tsupport e₂) := h₂.2.2.1
  have c12 : IsCompact (tsupport e₁ * tsupport e₂) := IsCompact.mul c1 c2
  let A := (finite_out_mem K h₁.1 c1).toFinset
  let A₂ := (finite_out_mem K h₁.1 c2).toFinset
  let B := (finite_out_mem K h₁.1 c12).toFinset
  have memA : ∀ q : GL ι F ⧸ K, q ∈ A ↔ q.out ∈ tsupport e₁ := fun q => by simp [A]
  have memA₂ : ∀ q : GL ι F ⧸ K, q ∈ A₂ ↔ q.out ∈ tsupport e₂ := fun q => by simp [A₂]
  have memB : ∀ q : GL ι F ⧸ K, q ∈ B ↔ q.out ∈ tsupport e₁ * tsupport e₂ := fun q => by simp [B]
  have hc : ∀ g, hconv K e₁ e₂ g = ∑ q ∈ A, e₁ q.out * e₂ (q.out⁻¹ * g) := fun g => by
    unfold hconv
    refine finsum_eq_sum_of_support_subset _ ?_
    intro q hq
    exact Finset.mem_coe.2 ((memA q).2 (subset_tsupport _ (left_ne_zero_of_mul hq)))
  have hL := hk_eq_sum ρ K (hconv K e₁ e₂) v B
    (fun s hs => (memB s).2 (support_hconv K e₁ e₂ hs))
  have hT : ∀ x : GL ι F, ∑ᶠ r : GL ι F ⧸ K, e₂ r.out • ρ (x * r.out) v
      = ∑ᶠ s : GL ι F ⧸ K, e₂ (x⁻¹ * s.out) • ρ s.out v := fun x => by
    have hr : ∀ y, ∀ k ∈ K, (fun y => e₂ (x⁻¹ * y) • ρ y v) (y * k) = (fun y => e₂ (x⁻¹ * y) • ρ y v) y := by
      intro y k hk'
      show e₂ (x⁻¹ * (y * k)) • ρ (y * k) v = e₂ (x⁻¹ * y) • ρ y v
      rw [← mul_assoc, isHk_right h₂ _ hk', map_mul, Module.End.mul_apply, hvk k hk']
    have ht := finsum_out_translate K (fun y => e₂ (x⁻¹ * y) • ρ y v) hr x
    simpa only [inv_mul_cancel_left] using ht
  have hI : ∀ q ∈ A, ρ q.out (hk ρ K e₂ v) = ∑ s ∈ B, e₂ (q.out⁻¹ * s.out) • ρ s.out v := by
    intro q hq
    have hq' := (memA q).1 hq
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hk_eq_sum ρ K e₂ v A₂ (fun r hr => (memA₂ r).2 (subset_tsupport _ hr)), map_sum]
    have h1 : ∑ r ∈ A₂, ρ q.out (e₂ r.out • ρ r.out v) = ∑ᶠ r : GL ι F ⧸ K, e₂ r.out • ρ (q.out * r.out) v := by
      symm
      rw [finsum_eq_sum_of_support_subset (s := A₂)]
      · refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_smul, map_mul, Module.End.mul_apply]
      · intro r hr
        refine Finset.mem_coe.2 ((memA₂ r).2 (subset_tsupport _ fun h0 => (Function.mem_support.1 hr) ?_))
        show e₂ r.out • ρ (q.out * r.out) v = 0
        rw [h0, zero_smul]
    rw [h1, hT]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro s hs
    refine Finset.mem_coe.2 ((memB s).2 (Set.mem_mul.2 ⟨q.out, hq', q.out⁻¹ * s.out,
      subset_tsupport _ fun h0 => (Function.mem_support.1 hs) ?_, mul_inv_cancel_left _ _⟩))
    show e₂ (q.out⁻¹ * s.out) • ρ s.out v = 0
    rw [h0, zero_smul]
  have hR : hk ρ K e₁ (hk ρ K e₂ v)
      = ∑ q ∈ A, e₁ q.out • ∑ s ∈ B, e₂ (q.out⁻¹ * s.out) • ρ s.out v := by
    rw [hk_eq_sum ρ K e₁ _ A (fun q hq => (memA q).2 (subset_tsupport _ hq))]
    exact Finset.sum_congr rfl (fun q hq => by rw [hI q hq])
  rw [hL, hR]
  simp only [hc, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

end Hecke

end GlobalTheory.CompanionTheory.HeckeMul
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfUnipotentSumsVanish
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfUnipotentSumsVanish
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.CuspIff

def stdRadical (K : Type) [Field K] [Fintype K] [DecidableEq K] (d a : ℕ) : Subgroup (GL (Fin d) K) :=
  have hmul : ∀ u v : GL (Fin d) K,
      (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ))) →
      (∀ i j : Fin d, (v : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ))) →
      ∀ i j : Fin d, ((u * v : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
        ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
    intro u v hu hv i j
    by_cases hij : (i : ℕ) < a ∧ a ≤ (j : ℕ)
    · exact Or.inr hij
    left
    rw [Units.val_mul, Matrix.mul_apply]
    by_cases hi : (i : ℕ) < a
    · have hk : ∀ k, (v : Matrix (Fin d) (Fin d) K) k j = if k = j then 1 else 0 :=
        fun k => (hv k j).resolve_right (by omega)
      simp only [hk]
      simpa using (hu i j).resolve_right hij
    · have hk : ∀ k, (u : Matrix (Fin d) (Fin d) K) i k = if i = k then 1 else 0 :=
        fun k => (hu i k).resolve_right (by omega)
      simp only [hk]
      simpa using (hv i j).resolve_right hij
  have hone : ∀ i j : Fin d, ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := fun i j => Or.inl (by simp [Matrix.one_apply])
  { carrier := {u | ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ))}
    one_mem' := hone
    mul_mem' := fun {u v} hu hv => hmul u v hu hv
    inv_mem' := by
      intro u hu
      have hpow : ∀ n : ℕ, ∀ i j : Fin d, ((u ^ n : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j =
          (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := by
        intro n
        induction n with
        | zero => simpa using hone
        | succ n ih => rw [pow_succ]; exact hmul _ _ ih hu
      have hinv : u⁻¹ = u ^ (orderOf u - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos u), pow_orderOf_eq_one]
      show ∀ i j : Fin d, ((u⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = _ ∨ _
      rw [hinv]
      exact hpow _ }

theorem mem_stdRadical {K : Type} [Field K] [Fintype K] [DecidableEq K] {d a : ℕ} {u : GL (Fin d) K} :
    u ∈ stdRadical K d a ↔ ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := Iff.rfl

theorem pm_conj {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (g : GL ι K) : pm (K := K) σ * g * (pm (K := K) σ)⁻¹ = glEquiv K σ g := by
  have hp : ∀ i j, (pm (K := K) σ : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by
    intro i j
    show (Equiv.toPEquiv σ⁻¹).toMatrix i j = _
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    exact if_congr Equiv.Perm.inv_eq_iff_eq rfl rfl
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  have hg : ∀ x : GL ι K, ((glEquiv K σ x : GL ι K) : Matrix ι ι K) = (x : Matrix ι ι K).submatrix σ.symm σ.symm :=
    fun _ => rfl
  simp only [Units.val_mul, Matrix.mul_apply, hp, hg, Matrix.submatrix_apply]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm i) (fun x _ hx => if_neg (fun h => hx (by simp [h]))) (by simp)]
  simp

theorem eq_zero_of_sum_char {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) [DecidablePred (· ∈ U)]
    (h : (∑ u : G, if u ∈ U then ρ.character u else 0) = 0) (v : V) (hv : ∀ u ∈ U, ρ u v = v) : v = 0 := by
  have hc : (Nat.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have := invertibleOfNonzero hc
  have h1 := Representation.card_inv_mul_sum_char_eq_finrank (ρ.comp U.subtype : Representation ℂ U V)
  have hs : (∑ u : G, if u ∈ U then ρ.character u else 0) =
      ∑ g : U, Representation.character (ρ.comp U.subtype : Representation ℂ U V) g := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) (fun g => ρ.character g)
  rw [hs] at h
  rw [h, mul_zero] at h1
  have h2 : Representation.invariants (ρ.comp U.subtype : Representation ℂ U V) = ⊥ := by
    rw [← Submodule.finrank_eq_zero, ← Nat.cast_eq_zero (R := ℂ)]
    exact h1.symm
  have hm : v ∈ Representation.invariants (ρ.comp U.subtype : Representation ℂ U V) := by
    rw [Representation.mem_invariants]
    exact fun u => hv u.1 u.2
  rw [h2] at hm
  simpa using hm

theorem isCuspidal_of_sum_char : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)),
    (∀ a, 0 < a → a < d → (open Classical in ∑ u : GL (Fin d) K,
      if (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)))
      then τ.character u else 0) = 0) → IsCuspidal K τ := by
  classical
  intro K _ _ _ d τ h s b hb hs v hv
  let c0 : Fin s := ⟨0, by omega⟩
  let c1 : Fin s := ⟨1, by omega⟩
  have hc : c0 ≠ c1 := by simp [c0, c1, Fin.ext_iff]
  obtain ⟨i0, hi0⟩ := hb c0
  obtain ⟨i1, hi1⟩ := hb c1
  set a := Fintype.card {i // b i = c0} with ha
  have ha0 : 0 < a := Fintype.card_pos_iff.2 ⟨⟨i0, hi0⟩⟩
  have had : a < d := by
    have := Fintype.card_subtype_lt (p := fun i => b i = c0) (x := i1) (by rw [hi1]; exact hc.symm)
    simpa using this
  have hcard : Fintype.card {i // b i = c0} = Fintype.card {i : Fin d // (i : ℕ) < a} := by
    rw [← ha]
    exact (Fintype.card_fin a).symm.trans (Fintype.card_congr
      { toFun := fun k => ⟨⟨k, by omega⟩, k.2⟩
        invFun := fun i => ⟨i.1, i.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
  let e := Fintype.equivOfCardEq hcard
  let σ : Equiv.Perm (Fin d) := e.extendSubtype
  have hσ : ∀ i, (σ i : ℕ) < a ↔ b i = c0 := by
    intro i
    by_cases hi : b i = c0
    · exact ⟨fun _ => hi, fun _ => e.extendSubtype_mem i hi⟩
    · exact ⟨fun h' => absurd h' (e.extendSubtype_not_mem i hi), fun h' => absurd h' hi⟩
  have hfix : ∀ w : τ, (∀ u ∈ stdRadical K d a, τ.ρ u w = w) → w = 0 := by
    refine eq_zero_of_sum_char τ.ρ (stdRadical K d a) ?_
    refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) (h a ha0 had)
    by_cases hu : u ∈ stdRadical K d a
    · rw [if_pos hu, if_pos (mem_stdRadical.1 hu)]; rfl
    · rw [if_neg hu, if_neg (fun h' => hu (mem_stdRadical.2 h'))]

  have hent : ∀ (x : GL (Fin d) K) (i j : Fin d),
      ((pm (K := K) σ * x * (pm (K := K) σ)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (σ i) (σ j) =
        (x : Matrix (Fin d) (Fin d) K) i j := by
    intro x i j
    rw [pm_conj]
    show (x : Matrix (Fin d) (Fin d) K) (σ.symm (σ i)) (σ.symm (σ j)) = _
    simp
  have key : ∀ x : GL (Fin d) K, pm (K := K) σ * x * (pm (K := K) σ)⁻¹ ∈ stdRadical K d a → ∀ i j,
      (x : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ (b i = c0 ∧ b j ≠ c0) := by
    intro x hx i j
    have := hx (σ i) (σ j)
    rw [hent] at this
    rcases this with h1 | ⟨h1, h2⟩
    · left; simpa [σ.injective.eq_iff] using h1
    · right
      refine ⟨(hσ i).1 h1, fun h3 => ?_⟩
      have := (hσ j).2 h3
      omega
  have hut : ∀ x : GL (Fin d) K, pm (K := K) σ * x * (pm (K := K) σ)⁻¹ ∈ stdRadical K d a →
      IsBlockUT K b (x : Matrix (Fin d) (Fin d) K) := by
    intro x hx i j hij
    rcases key x hx i j with h1 | ⟨h1, -⟩
    · have : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
      simpa [this] using h1
    · rw [h1] at hij
      exact absurd hij (by simp [c0, Fin.lt_def])
  have hun : ∀ x : GL (Fin d) K, pm (K := K) σ * x * (pm (K := K) σ)⁻¹ ∈ stdRadical K d a → x ∈ unip K b := by
    intro x hx
    refine ⟨⟨hut x hx, hut x⁻¹ ?_⟩, ?_⟩
    · have : pm (K := K) σ * x⁻¹ * (pm (K := K) σ)⁻¹ = (pm (K := K) σ * x * (pm (K := K) σ)⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hx
    · intro i j hij
      rcases key x hx i j with h1 | ⟨h1, h2⟩
      · exact h1
      · exact absurd (hij ▸ h1) h2
  have hw := hfix (τ.ρ (pm (K := K) σ) v) (by
    intro u hu
    have hx : (pm (K := K) σ)⁻¹ * u * pm (K := K) σ ∈ unip K b := by
      apply hun
      have : pm (K := K) σ * ((pm (K := K) σ)⁻¹ * u * pm (K := K) σ) * (pm (K := K) σ)⁻¹ = u := by group
      rw [this]
      exact hu
    have hh : u * pm (K := K) σ = pm (K := K) σ * ((pm (K := K) σ)⁻¹ * u * pm (K := K) σ) := by group
    rw [← Module.End.mul_apply, ← map_mul, hh, map_mul, Module.End.mul_apply, hv _ hx])
  have h3 := congrArg (τ.ρ (pm (K := K) σ)⁻¹) hw
  simpa [← Module.End.mul_apply, ← map_mul] using h3

end GlobalTheory.CompanionTheory.TyFin.CuspIff
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfUnipotentSumsVanishStatement
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_of_unipotent_sums_vanish : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)),
    (∀ a, 0 < a → a < d → (open Classical in ∑ u : GL (Fin d) K,
      if (∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨ ((i : ℕ) < a ∧ a ≤ (j : ℕ)))
      then τ.character u else 0) = 0) → IsCuspidal K τ := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char | exact GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char | (intros; apply GlobalTheory.CompanionTheory.TyFin.CuspIff.isCuspidal_of_sum_char <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfLseqFirst
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfLseqFirst
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerLen

theorem isFiniteLength_of_ker_le_range {W : Type} [CommRing W] {A B C : Type 1}
    [AddCommGroup A] [Module W A] [AddCommGroup B] [Module W B] [AddCommGroup C] [Module W C]
    (v : A →ₗ[W] B) (f : B →ₗ[W] C) (h : LinearMap.ker f ≤ LinearMap.range v)
    (hA : IsFiniteLength W A) (hC : IsFiniteLength W C) : IsFiniteLength W B := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hA hC ⊢
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hC
  have n1 : IsNoetherian W (LinearMap.range v) :=
    isNoetherian_of_surjective v.rangeRestrict (LinearMap.range_rangeRestrict v)
  have a1 : IsArtinian W (LinearMap.range v) :=
    isArtinian_of_surjective A v.rangeRestrict v.surjective_rangeRestrict
  have n2 : IsNoetherian W (LinearMap.ker f) :=
    isNoetherian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
  have a2 : IsArtinian W (LinearMap.ker f) :=
    isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
  have hr : LinearMap.range (LinearMap.ker f).subtype = LinearMap.ker f.rangeRestrict := by
    rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]
  exact ⟨isNoetherian_of_range_eq_ker _ _ hr, isArtinian_of_range_eq_ker _ _ hr⟩

theorem isFiniteLength_level : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'),
    IsFiniteLength W (S.M 1) → ∀ n, IsFiniteLength W (S.M n) := by
  intro W _ l S S' L h1 n
  induction n with
  | zero =>
    have : Subsingleton (S.M 0) := ⟨fun x y => by
      have hx := L.kill 0 x
      have hy := L.kill 0 y
      simp only [pow_zero, one_smul] at hx hy
      rw [hx, hy]⟩
    exact IsFiniteLength.of_subsingleton
  | succ n ih =>
    refine isFiniteLength_of_ker_le_range (L.ν 1 (n + 1)) (L.ρ (n + 1) n) ?_ h1 ih
    intro x hx
    obtain ⟨y, hy⟩ := L.ex₁ 1 n (n + 1) (by omega) x hx
    exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.TowerLen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfLseqFirstStatement
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_of_lseq_first : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → ∀ n, IsFiniteLength W (S.M n) := by
  first | exact @GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level | exact GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level | (intros; apply GlobalTheory.CompanionTheory.TowerLen.isFiniteLength_level <;> assumption)
end
end
