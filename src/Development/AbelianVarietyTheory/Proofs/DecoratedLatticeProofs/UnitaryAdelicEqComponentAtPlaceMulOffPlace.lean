module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicEqComponentAtPlaceMulOffPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicEqComponentAtPlaceMulOffPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.FinPl

section Mix

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mix_mul_decompAt (e : A) (hee : e * e = e) (a b : Matrix n n A) :
    (e • a + (1 - e) • (1 : Matrix n n A)) * (e • b + (1 - e) • 1) = e • (a * b) + (1 - e) • 1 := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, hee, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one, one_mul]

theorem cT_mix_decompAt (s : A →+* A) (e : A) (hs : s e = e) (a : Matrix n n A) :
    Formalism.UG.cT s (e • a + (1 - e) • (1 : Matrix n n A)) = e • Formalism.UG.cT s a + (1 - e) • 1 := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, map_add, map_mul, map_sub, map_one, hs]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem mix_mem_decompAt (s : A →+* A) (J : Matrix n n A) (e : A) (hee : e * e = e) (hs : s e = e) (g : GL n A)
    (hg : g ∈ Formalism.UG.UJ s J) :
    ∃ g' ∈ Formalism.UG.UJ s J, (g' : Matrix n n A) = e • (g : Matrix n n A) + (1 - e) • 1 := by
  refine ⟨⟨e • (g : Matrix n n A) + (1 - e) • 1, e • ((g⁻¹ : GL n A) : Matrix n n A) + (1 - e) • 1, ?_, ?_⟩, ?_, rfl⟩
  · rw [mix_mul_decompAt e hee, Units.mul_inv, ← add_smul, add_sub_cancel, one_smul]
  · rw [mix_mul_decompAt e hee, Units.inv_mul, ← add_smul, add_sub_cancel, one_smul]
  · have hg' : Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
    show Formalism.UG.cT s (e • (g : Matrix n n A) + (1 - e) • 1) * J * (e • (g : Matrix n n A) + (1 - e) • 1) = J
    have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
    have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
    have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
    rw [cT_mix_decompAt s e hs]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_mul, mul_one] at hg' ⊢
    rw [hg', hee, h1, h2, h3, zero_smul, zero_smul, add_zero, zero_add, ← add_smul, add_sub_cancel, one_smul]

theorem map_mk_decompAt (I : Ideal A) (g : GL n A) (hg : ∀ i j, ((g : Matrix n n A) - 1) i j ∈ I) :
    Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g = 1 := by
  ext i j
  have key : (1 : Matrix n n (A ⧸ I)) i j = Ideal.Quotient.mk I ((1 : Matrix n n A) i j) := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one]
  rw [key]
  exact Ideal.Quotient.eq.mpr (by simpa [Matrix.sub_apply] using hg i j)

end Mix

theorem sigR_algebraMap_decompAt {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]


set_option maxHeartbeats 1000000 in
theorem decompAt : ∀ (D : D7) (S : HSp D) (h : GA D S) (v : Pl D), ∃ hv ∈ grpAt S (· = v), ∃ h' ∈ grpOff S (· = v),
    h = hv * h' := by
  intro D S h v
  obtain ⟨ε, α, hε, hv1, hv0⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hε
  have hea : algebraMap (AF D.host.F) (AE D) ε = ε ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  set e : AE D := algebraMap (AF D.host.F) (AE D) ε with he_def
  have c1 : compAt D v e = 1 := by rw [hc, hv1]; rfl
  have c0 : ∀ w, w ≠ v → compAt D w e = 0 := fun w hw => by rw [hc, hv0 w hw, TensorProduct.zero_tmul]
  have heAt : e ∈ idAt D (· = v) := (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ e).2 ⟨h0, fun w hw => c0 w hw⟩
  have hee : e * e = e := (mem_supportedAtPlace_iff_placeIdempotent_mul D v e h0 c1 c0 e).1 heAt
  have heOff : 1 - e ∈ idOff D (· = v) := by
    refine (Submodule.mem_iInf _).2 fun w => ?_
    rcases w with ⟨w, hw⟩
    change w = v at hw
    subst hw
    rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, c1, sub_self]
  have hee' : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
  have hσ : ∀ σ' : D.host.E →ₐ[D.host.F] D.host.E, sigR (AF D.host.F) σ' e = e := by
    intro σ'
    exact sigR_algebraMap_decompAt (AF D.host.F) σ' ε
  have hσ' : ∀ σ' : D.host.E →ₐ[D.host.F] D.host.E, sigR (AF D.host.F) σ' (1 - e) = 1 - e := by
    intro σ'; rw [map_sub, map_one, hσ]
  have hmem : h.1 ∈ Formalism.UG.UJ (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) := h.2
  obtain ⟨g₁, hg₁, hg₁v⟩ := mix_mem_decompAt (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) e hee
    (hσ _) h.1 hmem
  obtain ⟨g₂, hg₂, hg₂v⟩ := mix_mem_decompAt (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) (1 - e)
    hee' (hσ' _) h.1 hmem
  have hcong : ∀ (I : Ideal (AE D)) (g : GA D S), (∀ i j, (mt S g - 1) i j ∈ I) → g ∈ congGrp S I := by
    intro I g hg
    rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact map_mk_decompAt I _ hg
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  refine ⟨⟨g₁, hg₁⟩, hcong _ _ ?_, ⟨g₂, hg₂⟩, hcong _ _ ?_, ?_⟩
  · intro i j
    show (g₁.val - 1) i j ∈ _
    have : e • h.1.val + (1 - e) • 1 - 1 = e • (h.1.val - 1) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hg₁v, this, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ heAt
  · intro i j
    show (g₂.val - 1) i j ∈ _
    have : (1 - e) • h.1.val + (1 - (1 - e)) • 1 - 1 =
        (1 - e) • (h.1.val - 1) := by
      rw [smul_sub, sub_smul (1 : AE D) (1 - e), one_smul]; abel
    rw [hg₂v, this, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ heOff
  · apply Subtype.ext
    apply Units.ext
    show h.1.val = g₁.val * g₂.val
    rw [hg₁v, hg₂v, sub_sub_cancel]
    simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, hee, hee', h1, h2, zero_smul, zero_add,
      add_zero]
    rw [add_comm, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.FinPl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicEqComponentAtPlaceMulOffPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelic_eq_componentAtPlace_mul_offPlace : ∀ (D : D7) (S : HSp D) (h : GA D S) (v : Pl D), ∃ hv ∈ grpAt S (· = v), ∃ h' ∈ grpOff S (· = v), h = hv * h' := by
  first | exact @GlobalTheory.FinPl.decompAt | exact GlobalTheory.FinPl.decompAt | (intros; apply GlobalTheory.FinPl.decompAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorCosetIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorCosetIndicator
noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum Lifts InDual)
open GlobalTheory.FinPl.Comm (fpair)

namespace GlobalTheory.FinPl.CosetPairing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]

theorem exists_lifts [DecidableEq n] (P : Pair k n) : ∃ F, Lifts P.lat F P.red := by
  haveI := Submodule.IsLattice.free k P.lat
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (Algebra.linearMap 𝒪[k] 𝓀[k]) P.fn residue_surjective
  let b := Module.Free.chooseBasis 𝒪[k] P.lat
  let G : (n → k) →ₗ[k] k := (b.extendOfIsFullLattice k).constr k fun i => (g (b i) : k)
  have h1 : (G.restrictScalars 𝒪[k]) ∘ₗ P.lat.subtype = (Algebra.linearMap 𝒪[k] k) ∘ₗ g := b.ext fun i => by
    have := (b.extendOfIsFullLattice k).constr_basis k (fun i => (g (b i) : k)) i
    rw [Module.Basis.extendOfIsFullLattice_apply] at this
    exact this
  refine ⟨fun i => G (Pi.single i 1), fun y => ⟨g y, ?_, LinearMap.congr_fun hg y⟩⟩
  have h2 : G y = (g y : k) := LinearMap.congr_fun h1 y
  rw [← h2, LinearMap.pi_apply_eq_sum_univ G]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

theorem inDual_of_lifts (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {f : Module.Dual 𝓀[k] (Red L)} {F F' : n → k}
    (hF : Lifts L F f) (hF' : Lifts L F' f) : InDual L (q.inv • F - q.inv • F') := fun y hy => by
  obtain ⟨s, hs, hr⟩ := hF ⟨y, hy⟩
  obtain ⟨t, ht, hr'⟩ := hF' ⟨y, hy⟩
  obtain ⟨u, hu⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff (s - t)).1 (by rw [map_sub, hr, hr', sub_self]))
  have hu' : (s : k) - t = q.1 * u := by exact_mod_cast congrArg Subtype.val hu
  rw [← smul_sub, smul_dotProduct, sub_dotProduct, ← hs, ← ht, hu', smul_eq_mul, Unif.inv,
    inv_mul_cancel_left₀ q.ne_zero]
  exact u.2

theorem cosetInd_add (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {f : Module.Dual 𝓀[k] (Red L)} {F : n → k}
    (hF : Lifts L F f) (η : n → k) : cosetInd q L f (η + q.inv • F) = dualInd L η := by
  classical
  refine if_congr ⟨?_, fun h => ⟨F, hF, by simpa using h⟩⟩ rfl rfl
  rintro ⟨F', hF', h⟩ y hy
  have := sub_mem (h y hy) (inDual_of_lifts q hF hF' y hy)
  rwa [← sub_dotProduct, show η + q.inv • F - q.inv • F' - (q.inv • F - q.inv • F') = η by abel] at this

variable {χ : AddChar k Circle} (hχ : HasConductor χ 1) {e : k}


include hχ in
theorem char_dual (he : e = 1 ∨ e = -1) {L : Submodule 𝒪[k] (n → k)} {η y : n → k} (hη : InDual L η) (hy : y ∈ L) :
    χ (e * (η ⬝ᵥ y)) = 1 := by
  rcases he with rfl | rfl
  · simpa using apply_int_eq_one hχ ⟨_, hη y hy⟩
  · simpa using apply_int_eq_one hχ (-⟨_, hη y hy⟩)

theorem char_coset (q : Unif k) {ε : 𝓀[k]ˣ} (he : (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) {P : Pair k n} {F η y : n → k}
    (hF : Lifts P.lat F P.red) (hη : InDual P.lat η) (hy : y ∈ P.lat) :
    (χ (e * ((η + q.inv • F) ⬝ᵥ y)) : ℂ) = resChar χ hχ q (ε * P.ev y) := by
  obtain ⟨s, hs, hr⟩ := hF ⟨y, hy⟩
  have hr' : P.ev y = residue 𝒪[k] s := ((P.hasVal_fn ⟨y, hy⟩).ev_eq).trans hr.symm
  rw [add_dotProduct, mul_add, AddChar.map_add_eq_mul, char_dual hχ (he.imp And.left And.left) hη hy, one_mul,
    smul_dotProduct, ← hs, hr']
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [resChar_residue]
  · have := resChar_residue hχ q (-s)
    simpa using this.symm

theorem exists_char_ne (q : Unif k) {ε : 𝓀[k]ˣ} (hε : ε = 1 ∨ ε = -1) {Q Q'' : Pair k n} (h : Q''.lat = Q.lat)
    (hne : Q'' ≠ ε • Q) : ∃ y ∈ Q.lat, resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ≠ 1 := by
  have hi : ε⁻¹ = ε := by rcases hε with rfl | rfl <;> simp
  obtain ⟨y, hy, hc⟩ : ∃ y ∈ Q.lat, -Q.ev y + ε * Q''.ev y ≠ 0 := by
    by_contra hc
    push Not at hc
    refine hne (Pair.ext fun x a => ?_)
    rw [Pair.dia_hasVal, hi]
    constructor
    · intro hx
      have hx' := h ▸ hx.mem
      have := hc x hx'
      rw [hx.ev_eq, neg_add_eq_zero] at this
      exact this ▸ Pair.hasVal_ev hx'
    · intro hx
      have := hc x hx.mem
      rw [hx.ev_eq, neg_add_eq_zero, Units.mul_right_inj] at this
      exact this ▸ Pair.hasVal_ev (h ▸ hx.mem)
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.1 (resChar_ne_one hχ q)
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (a * (-Q.ev y + ε * Q''.ev y)⁻¹)
  refine ⟨s • y, Q.lat.smul_mem s hy, ?_⟩
  rw [((Pair.hasVal_ev hy).smul s).ev_eq, ((Pair.hasVal_ev (h ▸ hy : y ∈ Q''.lat)).smul s).ev_eq]
  convert ha using 2
  rw [← inv_mul_cancel_right₀ hc a, ← hs]
  ring

theorem fpair_charInd_cosetInd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle)
    (hχ : HasConductor χ 1) (e : k) (ε : 𝓀[k]ˣ) (he : (e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) (μ : Measure (n → k))
    [μ.IsAddHaarMeasure] (Q Q'' : Pair k n) (h : Q''.lat = Q.lat) :
    (Q'' = ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) =
      fpair χ e μ (vecInd Q.lat) (dualInd Q.lat)) ∧
    (Q'' ≠ ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) = 0) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := secondCountable k
  obtain ⟨F, hF⟩ := exists_lifts Q''
  have hε : ε = 1 ∨ ε = -1 := he.imp And.right And.right
  have key : fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) =
      ∫ η, (∫ y, vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ∂μ) * dualInd Q.lat η ∂μ := by
    unfold fpair
    rw [← integral_add_right_eq_self _ (q.inv • F)]
    congr 1
    funext η
    rw [cosetInd_add q hF, h]
    by_cases hη : InDual Q.lat η
    swap
    · rw [dualInd, if_neg hη, mul_zero, mul_zero]
    congr 2
    funext y
    by_cases hy : y ∈ Q.lat
    · rw [char_coset hχ q he hF (h ▸ hη) (h ▸ hy), charInd, AddChar.map_add_eq_mul]
      ring
    · rw [charInd, vecInd, if_neg hy, mul_zero, zero_mul, zero_mul]
  rw [key]
  constructor
  · rintro rfl
    unfold fpair
    congr 1
    funext η
    by_cases hη : InDual Q.lat η
    swap
    · rw [dualInd, if_neg hη, mul_zero, mul_zero]
    congr 2
    funext y
    by_cases hy : y ∈ Q.lat
    · have h1 : Q.ev y = (ε⁻¹ : 𝓀[k]ˣ) * (ε • Q).ev y := (Pair.dia_hasVal.1 (Pair.hasVal_ev (P := ε • Q) hy)).ev_eq
      have hi : ε⁻¹ = ε := by rcases hε with rfl | rfl <;> simp
      rw [hi] at h1
      rw [char_dual hχ (he.imp And.left And.left) hη hy, ← h1, neg_add_cancel]
      simp
    · rw [vecInd, if_neg hy, zero_mul, zero_mul]
  · intro hne
    obtain ⟨y₀, hy₀, hc⟩ := exists_char_ne hχ q hε h hne
    have e1 := integral_add_right_eq_self (μ := μ)
      (fun y => vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y)) y₀
    have e2 : ∀ y, vecInd Q.lat (y + y₀) * resChar χ hχ q (-Q.ev (y + y₀) + ε * Q''.ev (y + y₀)) =
        resChar χ hχ q (-Q.ev y₀ + ε * Q''.ev y₀) * (vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y)) := fun y => by
      by_cases hy : y ∈ Q.lat
      · rw [vecInd, vecInd, if_pos hy, if_pos (add_mem hy hy₀), one_mul, one_mul, ← AddChar.map_add_eq_mul,
          ((Pair.hasVal_ev hy).add (Pair.hasVal_ev hy₀)).ev_eq,
          ((Pair.hasVal_ev (h ▸ hy : y ∈ Q''.lat)).add (Pair.hasVal_ev (h ▸ hy₀ : y₀ ∈ Q''.lat))).ev_eq]
        congr 1
        ring
      · rw [vecInd, vecInd, if_neg hy, if_neg fun h' => hy ((Q.lat.add_mem_iff_left hy₀).1 h')]
        simp
    simp only [e2] at e1
    rw [integral_const_mul] at e1
    have h0 : ∫ y, vecInd Q.lat y * resChar χ hχ q (-Q.ev y + ε * Q''.ev y) ∂μ = 0 := by
      by_contra h0
      exact hc ((mul_eq_right₀ h0).1 e1)
    simp [h0]

end GlobalTheory.FinPl.CosetPairing

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorCosetIndicatorStatement
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierPairing_pairCharIndicator_cosetIndicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k) (ε : 𝓀[k]ˣ), ((e = 1 ∧ ε = 1) ∨ (e = -1 ∧ ε = -1)) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q Q'' : Pair k n), Q''.lat = Q.lat → (Q'' = ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) = fpair χ e μ (vecInd Q.lat) (dualInd Q.lat)) ∧ (Q'' ≠ ε • Q → fpair χ e μ (charInd (resChar χ hχ q) Q) (cosetInd q Q''.lat Q''.red) = 0) := by
  first | exact @GlobalTheory.FinPl.CosetPairing.fpair_charInd_cosetInd | exact GlobalTheory.FinPl.CosetPairing.fpair_charInd_cosetInd | (intros; apply GlobalTheory.FinPl.CosetPairing.fpair_charInd_cosetInd <;> assumption)
end
end
