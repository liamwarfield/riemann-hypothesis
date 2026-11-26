module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BochnerTheorem.RMKComplex
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnTau
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PtMulComplSelf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteBadScalar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixEqBlockDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NpowHalfAddHalf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvSubtypeSum

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinianFields
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta GlobalTheory.AdelicU PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.UnitCell

theorem artinian_fields {ι : Type} [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, IsArtinianRing (A i)]
    {R : Type} [CommRing R] (c : ∀ i, R →+* A i) :
    ∃ (m : ℕ) (Ω : Fin m → Type) (_ : ∀ k, Field (Ω k)) (φ : ∀ k, R →+* Ω k),
      (∀ x, (∀ i, c i x = 1) → ∀ k, φ k x = 1) ∧
      ∀ z, (∀ k, φ k z ≠ 0) ↔ ∀ i, IsUnit (c i z) := by
  obtain ⟨m, ⟨q⟩⟩ := Finite.exists_equiv_fin (Σ i, MaximalSpectrum (A i))
  have hmax : ∀ k : Fin m, (q.symm k).2.asIdeal.IsMaximal := fun k => (q.symm k).2.isMaximal
  refine ⟨m, fun k => A (q.symm k).1 ⧸ (q.symm k).2.asIdeal, fun k => Ideal.Quotient.field _,
    fun k => (Ideal.Quotient.mk _).comp (c (q.symm k).1), fun x hx k => ?_, fun z => ⟨fun hz i => ?_, fun hz k h => ?_⟩⟩
  · simp [hx]
  · by_contra hu
    obtain ⟨M, hM, hzM⟩ := exists_max_ideal_of_mem_nonunits hu
    obtain ⟨k, hk⟩ : ∃ k, q.symm k = ⟨i, ⟨M, hM⟩⟩ := ⟨q _, q.symm_apply_apply _⟩
    refine hz k (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
    rw [hk]
    exact hzM
  · have hk := hmax k
    have h' : c (q.symm k).1 z ∈ (q.symm k).2.asIdeal := Ideal.Quotient.eq_zero_iff_mem.1 h
    exact hk.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (hz _))

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def sc {R : Type} [CommRing R] (r : Rˣ) : GL (Fin 1) R := Units.map (Matrix.scalar (Fin 1)).toMonoidHom r

theorem sc_apply {R : Type} [CommRing R] (r : Rˣ) : (sc r).1 0 0 = r := by simp [sc]

theorem exists_adele (S : Finset (HeightOneSpectrum (𝓞 F))) (b : ∀ v : HeightOneSpectrum (𝓞 F), (Fv F v ⊗[F] E)ˣ)
    (hb : ∀ v ∉ S, b v = 1) (c : ∀ w : InfinitePlace F, (w.Completion ⊗[F] E)ˣ) :
    ∃ x : AF F ⊗[F] E, (∀ v, compFin F E v x = b v) ∧ ∀ w, compInf F E w x = c w := by
  obtain ⟨a, ha, hc⟩ := GlobalTheory.AdelicU.Frames.exists_GL_of_components S (fun v => sc (b v))
    (fun v hv => by rw [hb v hv]; exact map_one _) (fun w => sc (c w))
  refine ⟨a.1 0 0, fun v => ?_, fun w => ?_⟩
  · have h := congrArg (fun g : GL (Fin 1) (Fv F v ⊗[F] E) => g.1 0 0) (ha v)
    exact h.trans (sc_apply _)
  · have h := congrArg (fun g : GL (Fin 1) (w.Completion ⊗[F] E) => g.1 0 0) (hc w)
    exact h.trans (sc_apply _)


variable (F E) in
def LocR (S : Finset (HeightOneSpectrum (𝓞 F))) : InfinitePlace F ⊕ S → Type
  | .inl w => w.Completion ⊗[F] E
  | .inr v => Fv F v.1 ⊗[F] E

instance locRing (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ c, CommRing (LocR F E S c)
  | .inl w => inferInstanceAs (CommRing (w.Completion ⊗[F] E))
  | .inr v => inferInstanceAs (CommRing (Fv F v.1 ⊗[F] E))


variable (F E) in
def locC (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ c, AF F ⊗[F] E →+* LocR F E S c
  | .inl w => compInf F E w
  | .inr v => compFin F E v.1

instance locArt (S : Finset (HeightOneSpectrum (𝓞 F))) : ∀ c, IsArtinianRing (LocR F E S c) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rintro (w | v)
  · exact IsArtinianRing.of_finite w.Completion (w.Completion ⊗[F] E)
  · exact IsArtinianRing.of_finite (Fv F v.1) (Fv F v.1 ⊗[F] E)


open Classical in
theorem crit (S : Finset (HeightOneSpectrum (𝓞 F))) (e : AF F ⊗[F] E) (h1 : ∀ w, compInf F E w e = 1)
    (h2 : ∀ v, compFin F E v e = if v ∈ S then 1 else 0) :
    ∃ (m : ℕ) (Ω : Fin m → Type) (_ : ∀ i, Field (Ω i)) (φ : ∀ i, AF F ⊗[F] E →+* Ω i), (∀ i, φ i e = 1) ∧
      ∀ z : AF F ⊗[F] E, IsUnit (1 - e + e * z) ↔ ∀ i, φ i z ≠ 0 := by
  obtain ⟨m, Ω, fld, φ, hφ, hu⟩ := artinian_fields (LocR F E S) (locC F E S)
  have he : ∀ k, φ k e = 1 := hφ e (by
    rintro (w | ⟨v, hv⟩)
    · exact h1 w
    · exact (h2 v).trans (if_pos hv))
  refine ⟨m, Ω, fld, φ, he, fun z => ⟨fun h k => ?_, fun h => ?_⟩⟩
  · have h' := h.map (φ k)
    rw [map_add (f := _), map_sub, map_mul, map_one, he, sub_self, zero_add, one_mul] at h'
    exact h'.ne_zero
  · have hz := (hu z).1 h
    have hI : ∀ w, IsUnit (compInf F E w z) := fun w => hz (.inl w)
    have hS : ∀ v (h : v ∈ S), IsUnit (compFin F E v z) := fun v h => hz (.inr ⟨v, h⟩)
    obtain ⟨x, hxf, hxi⟩ := exists_adele (E := E) S
      (fun v => if h : v ∈ S then (hS v h).unit⁻¹ else 1) (fun v hv => dif_neg hv) (fun w => (hI w).unit⁻¹)
    refine isUnit_iff_exists_inv.2 ⟨x, GlobalTheory.AdelicU.Supp.adTens_eq_one' (fun w => ?_) fun v => ?_⟩
    · rw [map_mul, map_add (f := _), map_sub, map_mul, map_one, h1, hxi, sub_self, zero_add, one_mul]
      exact (hI w).mul_val_inv
    · rw [map_mul, map_add (f := _), map_sub, map_mul, map_one, h2, hxf]
      by_cases hv : v ∈ S
      · simp only [if_pos hv, dif_pos hv, sub_self, zero_add, one_mul]
        exact (hS v hv).mul_val_inv
      · simp [if_neg hv, dif_neg hv]

end Glue

theorem unitCrit : PositivityTheory.Rg.Rsw.L.IdemEx → PositivityTheory.Rg.Rsw.Cell.UnitCrit := fun _ D S e he =>
  crit S e he.1 (by convert he.2 using 4)

end GlobalTheory.CompanionTheory.UnitCell

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDivRp
noncomputable section

open MeasureTheory Topology
open scoped ComplexOrder ComplexConjugate

namespace GlobalTheory.CompanionTheory.RswCell

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G] [TopologicalSpace G]

def secOf (P : Subgroup G) (h : G → ℝ) (F : G ⧸ P → ℂ) (g : G) : ℂ :=
  F (QuotientGroup.mk g⁻¹) * (h g : ℂ)

theorem mk_inv_mul {P : Subgroup G} {p : G} (hp : p ∈ P) (g : G) :
    (QuotientGroup.mk (p * g)⁻¹ : G ⧸ P) = QuotientGroup.mk g⁻¹ := by
  rw [mul_inv_rev]
  exact QuotientGroup.mk_mul_of_mem _ (P.inv_mem hp)

theorem div_rp {P : Subgroup G} {h : G → ℝ} {f : G → ℂ} (hpos : ∀ g, 0 < h g) (hf : Sec P h f) (g : G) :
    f (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) / (h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) : ℂ) =
      f g / (h g : ℂ) := by
  obtain ⟨p, hp⟩ := QuotientGroup.mk_out_eq_mul P g⁻¹
  have hr : rp (QuotientGroup.mk g⁻¹ : G ⧸ P) = (p : G)⁻¹ * g := by
    show (Quotient.out (QuotientGroup.mk g⁻¹ : G ⧸ P))⁻¹ = _
    rw [hp, mul_inv_rev, inv_inv]
  rw [hr]
  have key := hf.2 (p : G)⁻¹ (P.inv_mem p.2) g
  have h1 : (h ((p : G)⁻¹ * g) : ℂ) ≠ 0 := by exact_mod_cast (hpos _).ne'
  have h2 : (h g : ℂ) ≠ 0 := by exact_mod_cast (hpos _).ne'
  rw [div_eq_div_iff h1 h2]
  exact key

variable [IsTopologicalGroup G]

theorem secOf_sec {P : Subgroup G} {h : G → ℝ} (hc : Continuous h) {F : G ⧸ P → ℂ}
    (hF : Continuous F) : Sec P h (secOf P h F) := by
  refine ⟨?_, fun p hp g => ?_⟩
  · unfold secOf
    exact (hF.comp (QuotientGroup.continuous_mk.comp continuous_inv)).mul
      (Complex.continuous_ofReal.comp hc)
  · unfold secOf
    rw [mk_inv_mul hp g]
    ring

theorem compact_quot {P : Subgroup G}
    (hco : ∃ C : Set G, IsCompact C ∧ ∀ g, ∃ q ∈ P, ∃ c ∈ C, g = q * c) : CompactSpace (G ⧸ P) := by
  obtain ⟨C, hC, hcov⟩ := hco
  have huniv : (Set.univ : Set (G ⧸ P)) = (fun c => (QuotientGroup.mk c⁻¹ : G ⧸ P)) '' C := by
    ext x
    simp only [Set.mem_univ, Set.mem_image, true_iff]
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q, hq, c, hc, hac⟩ := hcov a⁻¹
    refine ⟨c, hc, ?_⟩
    have ha : a = c⁻¹ * q⁻¹ := by rw [← mul_inv_rev, ← hac, inv_inv]
    rw [ha, QuotientGroup.mk_mul_of_mem _ (P.inv_mem hq)]
  refine ⟨?_⟩
  rw [huniv]
  exact hC.image (QuotientGroup.continuous_mk.comp continuous_inv)

theorem continuous_div_rp {P : Subgroup G} {h : G → ℝ} {f : G → ℂ} (hc : Continuous h)
    (hpos : ∀ g, 0 < h g) (hf : Sec P h f) :
    Continuous fun q : G ⧸ P => f (rp q) / (h (rp q) : ℂ) := by
  rw [(QuotientGroup.isQuotientMap_mk P).continuous_iff]
  have hcomp : ((fun q : G ⧸ P => f (rp q) / (h (rp q) : ℂ)) ∘ QuotientGroup.mk) =
      fun a => f a⁻¹ / (h a⁻¹ : ℂ) := by
    funext a
    have := div_rp hpos hf a⁻¹
    rw [inv_inv] at this
    exact this
  rw [hcomp]
  exact (hf.1.comp continuous_inv).div (Complex.continuous_ofReal.comp (hc.comp continuous_inv))
    fun a => by exact_mod_cast (hpos _).ne'

theorem exists_repr [T2Space G] (P : Subgroup G) [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)]
    (h : G → ℝ) (mu : (G → ℂ) → ℂ) (S : Setup P h mu) : ∃ ν, Repr P h mu ν := by
  haveI : CompactSpace (G ⧸ P) := compact_quot S.cocpt
  haveI : IsClosed (P : Set G) := S.closed
  let Λ : C(G ⧸ P, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun F => mu (secOf P h F)
      map_add' := fun F F' => by
        have he : secOf P h ⇑(F + F') = secOf P h F + secOf P h F' := by
          funext g
          simp only [secOf, ContinuousMap.add_apply, Pi.add_apply]
          ring
        rw [he]
        exact S.add _ _ (secOf_sec S.cont F.continuous) (secOf_sec S.cont F'.continuous)
      map_smul' := fun c F => by
        have he : secOf P h ⇑(c • F) = c • secOf P h F := by
          funext g
          simp only [secOf, ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [he]
        exact S.smul c _ (secOf_sec S.cont F.continuous) }
  have hpos : ∀ F : C(G ⧸ P, ℂ), 0 ≤ Λ (star F * F) := by
    intro F
    have hval : ∀ g, secOf P h ⇑(star F * F) g =
        ((Complex.normSq (F (QuotientGroup.mk g⁻¹)) * h g : ℝ) : ℂ) := by
      intro g
      simp only [secOf, ContinuousMap.mul_apply, ContinuousMap.star_apply]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    have hnn := S.nonneg (secOf P h ⇑(star F * F)) (secOf_sec S.cont (star F * F).continuous)
      (fun g => by
        rw [hval g, Complex.ofReal_re, Complex.ofReal_im]
        exact ⟨mul_nonneg (Complex.normSq_nonneg _) (S.pos g).le, rfl⟩)
    exact Complex.nonneg_iff.2 ⟨hnn.1, hnn.2.symm⟩
  obtain ⟨ν, hfin, hrep⟩ := PI.Bochner.exists_measure_of_positive Λ hpos
  refine ⟨ν, hfin, fun f hf => ?_⟩
  let Fc : C(G ⧸ P, ℂ) := ⟨fun q => f (rp q) / (h (rp q) : ℂ), continuous_div_rp S.cont S.pos hf⟩
  have hsec : secOf P h ⇑Fc = f := by
    funext g
    show f (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) / (h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) : ℂ) * (h g : ℂ) = f g
    rw [div_rp S.pos hf g]
    have h2 : (h g : ℂ) ≠ 0 := by exact_mod_cast (S.pos g).ne'
    field_simp
  refine ⟨?_, ?_⟩
  · exact Fc.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · calc mu f = Λ Fc := by
          show mu f = mu (secOf P h ⇑Fc)
          rw [hsec]
      _ = ∫ q, Fc q ∂ν := hrep Fc

theorem riesz : Riesz := by
  intro G _ _ _ _ _ _ P _ _ h mu S
  exact exists_repr P h mu S

end GlobalTheory.CompanionTheory.RswCell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFormulaOfInvM
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RswCell

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G] [TopologicalSpace G]

lemma rp_mk (P : Subgroup G) (g : G) : ∃ p ∈ P, rp (QuotientGroup.mk g : G ⧸ P) = p * g⁻¹ := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul P g
  refine ⟨(k : G)⁻¹, P.inv_mem k.2, ?_⟩
  have : Quotient.out (QuotientGroup.mk g : G ⧸ P) = g * k := hk
  simp [rp, this]

lemma rp_smul (P : Subgroup G) (x : G) (q : G ⧸ P) : ∃ p ∈ P, rp (x⁻¹ • q) = p * (rp q * x) := by
  obtain ⟨p, hp, e⟩ := rp_mk P (x⁻¹ * Quotient.out q)
  refine ⟨p, hp, ?_⟩
  have hq : (QuotientGroup.mk (x⁻¹ * Quotient.out q) : G ⧸ P) = x⁻¹ • q := by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [← hq, e]
  simp [rp]

lemma rp_mk_mem_iff {P : Subgroup G} {Ω : Set G} (hl : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) (g : G) :
    rp (QuotientGroup.mk g : G ⧸ P) ∈ Ω ↔ g⁻¹ ∈ Ω := by
  obtain ⟨p, hp, e⟩ := rp_mk P g
  rw [e]
  refine ⟨fun H => ?_, hl p hp _⟩
  simpa using hl p⁻¹ (P.inv_mem hp) _ H

def coord {N : Type} [Zero N] {P : Subgroup G} (Ω : Set G) (τ : G → N) (q : G ⧸ P) : N :=
  open Classical in if rp q ∈ Ω then τ (rp q) else 0

lemma coord_of_mem {N : Type} [Zero N] {P : Subgroup G} {Ω : Set G} {τ : G → N} {q : G ⧸ P}
    (hq : rp q ∈ Ω) : coord Ω τ q = τ (rp q) := by
  simp [coord, hq]

lemma isOpen_bar [IsTopologicalGroup G] {N : Type} [TopologicalSpace N] {P : Subgroup G} {Ω : Set G}
    {τ : G → N} (hΩ : IsOpen Ω) (hl : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω ∧ τ (p * x) = τ x)
    (hτ : ContinuousOn τ Ω) {U : Set N} (hU : IsOpen U) :
    IsOpen {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} := by
  have hl' : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω := fun p hp x hx => (hl p hp x hx).1
  rw [← (QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.isOpen_preimage]
  have : (QuotientGroup.mk : G → G ⧸ P) ⁻¹' {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U}
      = (fun g : G => g⁻¹) ⁻¹' (Ω ∩ τ ⁻¹' U) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [rp_mk_mem_iff hl' g]
    obtain ⟨p, hp, e⟩ := rp_mk P g
    refine and_congr_right fun hg => ?_
    rw [e, (hl p hp _ hg).2]
  rw [this]
  exact (hτ.isOpen_inter_preimage hΩ hU).preimage continuous_inv

lemma measurable_coord [IsTopologicalGroup G] {N : Type} [AddCommGroup N] [TopologicalSpace N]
    [MeasurableSpace N] [BorelSpace N] {P : Subgroup G} [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)]
    {Ω : Set G} {τ : G → N} (hΩ : IsOpen Ω) (hl : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω ∧ τ (p * x) = τ x)
    (hτ : ContinuousOn τ Ω) : Measurable (coord Ω τ : G ⧸ P → N) := by
  refine measurable_of_isOpen fun U hU => ?_
  have hA := (isOpen_bar (P := P) hΩ hl hτ hU).measurableSet
  have hB : MeasurableSet {q : G ⧸ P | rp q ∈ Ω} := by
    have := (isOpen_bar (P := P) hΩ hl hτ (isOpen_univ (X := N))).measurableSet
    simpa using this
  by_cases h0 : (0 : N) ∈ U
  · have : (coord Ω τ : G ⧸ P → N) ⁻¹' U = {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} ∪ {q : G ⧸ P | rp q ∈ Ω}ᶜ := by
      ext q
      by_cases hq : rp q ∈ Ω <;> simp [coord, hq, h0]
    rw [this]
    exact hA.union hB.compl
  · have : (coord Ω τ : G ⧸ P → N) ⁻¹' U = {q : G ⧸ P | rp q ∈ Ω ∧ τ (rp q) ∈ U} := by
      ext q
      by_cases hq : rp q ∈ Ω <;> simp [coord, hq, h0]
    rw [this]
    exact hA

theorem cellFormula_of_invM (hI : InvM) : CellFormula := by
  intro G _ _ _ _ _ _ P _ _ h mu hs ν hν N _ _ _ _ _ _ _ _ lam _ Ω τ w nb hc hInv hh hnull
  haveI : IsFiniteMeasure ν := hν.1
  have ρc : Continuous fun y => h (w * nb y) := hs.cont.comp (continuous_const.mul hc.nbCont)
  have ρpos : ∀ y, 0 < h (w * nb y) := fun y => hs.pos _
  let D : N → ℝ≥0 := fun y => (1 / h (w * nb y)).toNNReal
  have Dc : Continuous D :=
    continuous_real_toNNReal.comp (continuous_const.div ρc fun y => (ρpos y).ne')
  have Dm : Measurable D := Dc.measurable
  let T : G ⧸ P → N := coord Ω τ
  have Tm : Measurable T := measurable_coord hc.isOpen hc.left hc.cont
  let lam' : Measure N := (ν.map T).withDensity fun y => (D y : ℝ≥0∞)
  have hlin : ∀ φ : N → ℝ≥0∞, Measurable φ →
      ∫⁻ y, φ y ∂lam' = ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (T q) ∂ν := by
    intro φ hφ
    have h1 : Measurable fun y => (D y : ℝ≥0∞) := Dm.coe_nnreal_ennreal
    rw [lintegral_withDensity_eq_lintegral_mul _ h1 hφ, lintegral_map (h1.mul hφ) Tm]
    rfl
  have hae : ∀ᵐ q ∂ν, rp q ∈ Ω := by
    rw [ae_iff]
    exact hnull
  have hshift : ∀ (a : N) (φ : N → ℝ≥0∞), Measurable φ →
      ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (a + T q) ∂ν = ∫⁻ q, (D (T q) : ℝ≥0∞) * φ (T q) ∂ν := by
    intro a φ hφ
    have hF : Measurable fun q => (D (T q) : ℝ≥0∞) * φ (T q) :=
      ((Dm.comp Tm).coe_nnreal_ennreal).mul (hφ.comp Tm)
    rw [← (hI G P h mu hs ν hν (nb a) (hInv a)).2 _ hF]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with q hq
    obtain ⟨p, hp, e⟩ := rp_smul P (nb a) q
    have hr := hc.right a _ hq
    have hl := hc.left p hp _ hr.1
    have hmem : rp ((nb a)⁻¹ • q) ∈ Ω := e ▸ hl.1
    have e1 : T ((nb a)⁻¹ • q) = τ (rp q) + a := by
      change coord Ω τ _ = _
      rw [coord_of_mem hmem, e, hl.2, hr.2]
    have e0 : T q = τ (rp q) := coord_of_mem hq
    rw [e1, e0, add_comm a]
    have hq1 := hh a _ hq
    set y := τ (rp q)
    have p1 := ρpos y
    have p2 := ρpos (y + a)
    have p3 := hs.pos (rp q)
    have hD : (D y : ℝ≥0∞) = (D (y + a) : ℝ≥0∞) * ENNReal.ofReal (h (rp q * nb a) / h (rp q)) := by
      change ENNReal.ofReal _ = ENNReal.ofReal _ * _
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      linarith
    rw [hD]
    ring
  haveI hinv : lam'.IsAddLeftInvariant := by
    refine ⟨fun a => Measure.ext fun S hS => ?_⟩
    rw [Measure.map_apply (measurable_const_add a) hS]
    have hS' : MeasurableSet ((fun y => a + y) ⁻¹' S) := measurable_const_add a hS
    have hi : Measurable (S.indicator (1 : N → ℝ≥0∞)) := measurable_one.indicator hS
    have hi' : ((fun y => a + y) ⁻¹' S).indicator (1 : N → ℝ≥0∞)
        = fun y => S.indicator (1 : N → ℝ≥0∞) (a + y) := by
      ext y
      by_cases hy : a + y ∈ S
      · rw [Set.indicator_of_mem (show y ∈ (fun y => a + y) ⁻¹' S from hy), Set.indicator_of_mem hy]
        rfl
      · rw [Set.indicator_of_notMem (show y ∉ (fun y => a + y) ⁻¹' S from hy),
          Set.indicator_of_notMem hy]
    have hi2 : Measurable fun y => S.indicator (1 : N → ℝ≥0∞) (a + y) :=
      hi.comp (measurable_const_add a)
    rw [← lintegral_indicator_one hS', ← lintegral_indicator_one hS, hi', hlin _ hi2, hlin _ hi]
    exact hshift a _ hi
  haveI : IsLocallyFiniteMeasure lam' := IsLocallyFiniteMeasure.withDensity_coe Dc
  have e := Measure.isAddLeftInvariant_eq_smul lam' lam
  refine ⟨Measure.addHaarScalarFactor lam' lam, fun f hf hoc => ?_⟩
  rw [← e]
  have gc : Continuous fun y => f (w * nb y) := hf.1.comp (continuous_const.mul hc.nbCont)
  have ψc : Continuous fun y => D y • f (w * nb y) := Dc.smul gc
  have hcomp : (fun q => D (T q) • f (w * nb (T q))) =ᵐ[ν] fun q => f (rp q) / h (rp q) := by
    filter_upwards [hae] with q hq
    have e0 : T q = τ (rp q) := coord_of_mem hq
    rw [e0]
    have h1 := hoc _ hq
    set y := τ (rp q)
    have p1 := ρpos y
    have p3 := hs.pos (rp q)
    have hDy : ((D y : ℝ≥0) : ℝ) = 1 / h (w * nb y) := Real.coe_toNNReal _ (by positivity)
    have c1 : (h (w * nb y) : ℂ) ≠ 0 := by exact_mod_cast p1.ne'
    have c3 : (h (rp q) : ℂ) ≠ 0 := by exact_mod_cast p3.ne'
    rw [NNReal.smul_def, Complex.real_smul, hDy]
    push_cast
    field_simp
    linear_combination -h1
  obtain ⟨hint, hmu⟩ := hν.2 f hf
  constructor
  · refine (integrable_withDensity_iff_integrable_smul Dm).2 ?_
    refine (integrable_map_measure ψc.aestronglyMeasurable Tm.aemeasurable).2 ?_
    exact hint.congr hcomp.symm
  · rw [hmu]
    change _ = ∫ y, f (w * nb y) ∂((ν.map T).withDensity fun y => (D y : ℝ≥0∞))
    rw [integral_withDensity_eq_integral_smul Dm, integral_map Tm.aemeasurable ψc.aestronglyMeasurable]
    exact (integral_congr_ae hcomp).symm

end GlobalTheory.CompanionTheory.RswCell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NullCOfInvM
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RswCell.NullCompl

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G]

theorem rp_mk_inv (P : Subgroup G) (g : G) : ∃ p ∈ P, rp (P := P) (((g⁻¹ : G)) : G ⧸ P) = p * g := by
  refine ⟨(Quotient.out ((g⁻¹ : G) : G ⧸ P))⁻¹ * g⁻¹, ?_, ?_⟩
  · exact QuotientGroup.eq.mp (QuotientGroup.out_eq' ((g⁻¹ : G) : G ⧸ P))
  · simp [rp]

theorem rp_smul (P : Subgroup G) (x : G) (q : G ⧸ P) : ∃ p ∈ P, rp (x⁻¹ • q) = p * (rp q * x) := by
  refine ⟨(Quotient.out (x⁻¹ • q))⁻¹ * (x⁻¹ * Quotient.out q), ?_, ?_⟩
  · rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_coe,
      QuotientGroup.out_eq']
  · simp [rp, mul_assoc]

variable [TopologicalSpace G]

theorem isOpen_rp [IsTopologicalGroup G] (P : Subgroup G) {Ω : Set G} (hΩ : IsOpen Ω)
    (hP : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) : IsOpen {q : G ⧸ P | rp q ∈ Ω} := by
  have hset : {q : G ⧸ P | rp q ∈ Ω} = ((↑) : G → G ⧸ P) '' {g | g⁻¹ ∈ Ω} := by
    ext q
    constructor
    · intro hq
      refine ⟨(rp q)⁻¹, by simpa using hq, ?_⟩
      simp only [rp, inv_inv]
      exact QuotientGroup.out_eq' q
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨p, hp, hrp⟩ := rp_mk_inv P g⁻¹
      simp only [inv_inv] at hrp
      show rp (g : G ⧸ P) ∈ Ω
      rw [hrp]
      exact hP p hp _ hg
  rw [hset]
  exact QuotientGroup.isOpenMap_coe _ (hΩ.preimage continuous_inv)

theorem ratio_bound {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} [IsTopologicalGroup G]
    (hS : Setup P h mu) {V : Set G} (hV : IsCompact V) :
    ∃ B : ℝ, ∀ g, ∀ x ∈ V, h (g * x) / h g ≤ B := by
  obtain ⟨C, hC, hcov⟩ := hS.cocpt
  have hcont : Continuous (fun z : G × G => h (z.1 * z.2) / h z.1) :=
    (hS.cont.comp continuous_mul).div (hS.cont.comp continuous_fst) (fun z => (hS.pos _).ne')
  obtain ⟨B, hB⟩ := (hC.prod hV).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨B, fun g x hx => ?_⟩
  obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
  have hlaw := hS.law q hq c (c * x)
  have heq : h (q * c * x) / h (q * c) = h (c * x) / h c := by
    rw [div_eq_div_iff (hS.pos _).ne' (hS.pos _).ne', mul_assoc]
    linear_combination (-1 : ℝ) * hlaw
  rw [heq]
  have hb := hB (c, x) ⟨hc, hx⟩
  simp only [Real.norm_eq_abs] at hb
  exact le_trans (le_abs_self _) hb

theorem local_null [IsTopologicalGroup G] [LocallyCompactSpace G] {P : Subgroup G}
    [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)] {h : G → ℝ} {mu : (G → ℂ) → ℂ}
    (hS : Setup P h mu) {ν : Measure (G ⧸ P)} [IsFiniteMeasure ν]
    (hInv : ∀ x, Inv P h mu x → ∀ F : G ⧸ P → ℝ≥0∞, Measurable F →
      ∫⁻ q, F (x⁻¹ • q) * ENNReal.ofReal (h (rp q * x) / h (rp q)) ∂ν = ∫⁻ q, F q ∂ν)
    {Ω : Set G} (hΩ : IsOpen Ω) (hP : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) (hF : Few P h mu Ω) (q0 : G ⧸ P) :
    ∃ W : Set (G ⧸ P), IsOpen W ∧ q0 ∈ W ∧ ν ({q | rp q ∉ Ω} ∩ W) = 0 := by
  classical
  obtain ⟨U, d, hUo, hgU, hUP, hfew⟩ := hF (rp q0)
  have hφ : Continuous (fun z : G × G => rp q0 * z.1 * z.2⁻¹) :=
    (continuous_const.mul continuous_fst).mul continuous_snd.inv
  have hmem : (fun z : G × G => rp q0 * z.1 * z.2⁻¹) ⁻¹' U ∈ 𝓝 ((1 : G), (1 : G)) :=
    hφ.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by simpa using hgU))
  obtain ⟨N0, hN0, N1, hN1, hsub⟩ := mem_nhds_prod_iff.mp hmem
  obtain ⟨V, hV1, hVN1, hVc⟩ := local_compact_nhds hN1
  obtain ⟨B, hB⟩ := ratio_bound hS hVc
  have hNo : IsOpen (interior N0) := isOpen_interior
  have h1N : (1 : G) ∈ interior N0 := mem_interior_iff_mem_nhds.mpr hN0
  let U' : Set G := {y | ∃ p ∈ P, ∃ n ∈ interior N0, y = p * (rp q0 * n)}
  have hU'o : IsOpen U' := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨p, hp, n, hn, rfl⟩
    refine ⟨(fun z => (p * rp q0)⁻¹ * z) ⁻¹' interior N0, ?_, ?_, ?_⟩
    · intro z hz
      exact ⟨p, hp, (p * rp q0)⁻¹ * z, hz, by group⟩
    · exact hNo.preimage (continuous_const.mul continuous_id)
    · show (p * rp q0)⁻¹ * (p * (rp q0 * n)) ∈ interior N0
      simpa [mul_assoc] using hn
  have hU'P : ∀ p ∈ P, ∀ x ∈ U', p * x ∈ U' := by
    rintro p hp x ⟨p', hp', n, hn, rfl⟩
    exact ⟨p * p', P.mul_mem hp hp', n, hn, (mul_assoc _ _ _).symm⟩
  have hgU' : rp q0 ∈ U' := ⟨1, P.one_mem, 1, h1N, by simp⟩
  have hshift : ∀ y ∈ U', ∀ γ ∈ V, y * γ⁻¹ ∈ U := by
    rintro y ⟨p, hp, n, hn, rfl⟩ γ hγ
    have h1 := hsub (Set.mk_mem_prod (interior_subset hn) (hVN1 hγ))
    simp only [Set.mem_preimage] at h1
    have h2 := hUP p hp _ h1
    simpa [mul_assoc] using h2
  refine ⟨{q | rp q ∈ U'}, isOpen_rp P hU'o hU'P, hgU', ?_⟩
  have hopenU : IsOpen {q : G ⧸ P | rp q ∈ U} := isOpen_rp P hUo hUP
  have hopenΩ0 : IsOpen {q : G ⧸ P | rp q ∈ Ω} := isOpen_rp P hΩ hP
  have hopenR : ∀ (S : Set G), IsOpen S → (∀ p ∈ P, ∀ x ∈ S, p * x ∈ S) → ∀ γ : G,
      IsOpen {q : G ⧸ P | rp q * γ ∈ S} := fun S hSo hSP γ =>
    isOpen_rp P (hSo.preimage (continuous_mul_const γ)) (fun p hp x hx => by
      show p * x * γ ∈ S
      rw [mul_assoc]
      exact hSP p hp _ hx)
  let A : G → Set (G ⧸ P) := fun γ => {q | rp q ∈ U} ∩ {q | rp q * γ ∈ Ω}ᶜ
  let E' : G → Set (G ⧸ P) := fun γ => {q | rp q ∈ Ω}ᶜ ∩ {q | rp q * γ⁻¹ ∈ U}
  have hAm : ∀ γ, MeasurableSet (A γ) := fun γ =>
    hopenU.measurableSet.inter (hopenR Ω hΩ hP γ).measurableSet.compl
  have hE'm : ∀ γ, MeasurableSet (E' γ) := fun γ =>
    hopenΩ0.measurableSet.compl.inter (hopenR U hUo hUP γ⁻¹).measurableSet
  have hEsub : ∀ γ ∈ V, {q | rp q ∉ Ω} ∩ {q | rp q ∈ U'} ⊆ E' γ := by
    rintro γ hγ q ⟨hq1, hq2⟩
    exact ⟨hq1, hshift _ hq2 γ hγ⟩
  have htrans : ∀ γ q, γ⁻¹ • q ∈ E' γ → q ∈ A γ := by
    rintro γ q ⟨h1, h2⟩
    obtain ⟨p, hp, hrp⟩ := rp_smul P γ q
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at h1 h2
    rw [hrp] at h1 h2
    refine ⟨?_, ?_⟩
    · have h3 := hUP p⁻¹ (P.inv_mem hp) _ h2
      show rp q ∈ U
      simpa [mul_assoc] using h3
    · show ¬ (rp q * γ ∈ Ω)
      intro h4
      exact h1 (hP p hp _ h4)
  have hfin : ENNReal.ofReal B * ((d : ℝ≥0∞) * ν univ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (measure_ne_top ν univ))
  by_contra hne
  obtain ⟨M, hM⟩ := ENNReal.exists_nat_mul_gt hne hfin
  obtain ⟨γ, hγ, hcnt⟩ := hfew V hV1 M
  have hstep : ∀ j, ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'}) ≤ ENNReal.ofReal B * ν (A (γ j)) := by
    intro j
    have hI := hInv (γ j) (hγ j).2 ((E' (γ j)).indicator 1) (measurable_one.indicator (hE'm _))
    calc ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'}) ≤ ν (E' (γ j)) := measure_mono (hEsub _ (hγ j).1)
      _ = ∫⁻ q, (E' (γ j)).indicator 1 q ∂ν := (lintegral_indicator_one (hE'm _)).symm
      _ = ∫⁻ q, (E' (γ j)).indicator 1 ((γ j)⁻¹ • q) *
            ENNReal.ofReal (h (rp q * γ j) / h (rp q)) ∂ν := hI.symm
      _ ≤ ∫⁻ q, (A (γ j)).indicator 1 q * ENNReal.ofReal B ∂ν := by
          apply lintegral_mono
          intro q
          apply mul_le_mul'
          · simp only [Set.indicator_apply, Pi.one_apply]
            split_ifs with h1 h2 <;>
              first | exact le_rfl | exact zero_le | exact absurd (htrans _ _ h1) h2
          · exact ENNReal.ofReal_le_ofReal (hB _ _ (hγ j).1)
      _ = ν (A (γ j)) * ENNReal.ofReal B := by
          rw [lintegral_mul_const _ (measurable_one.indicator (hAm _)), lintegral_indicator_one (hAm _)]
      _ = ENNReal.ofReal B * ν (A (γ j)) := mul_comm _ _
  have hpt : ∀ q, ∑ j, (A (γ j)).indicator 1 q ≤ (d : ℝ≥0∞) := by
    intro q
    by_cases hq : rp q ∈ U
    · have hc := hcnt (rp q) hq
      have e : (↑(Finset.univ.filter (fun j => rp q * γ j ∉ Ω)) : Set (Fin M))
          = {j | rp q * γ j ∉ Ω} := by
        ext j
        simp
      rw [← e, Set.ncard_coe_finset] at hc
      calc ∑ j, (A (γ j)).indicator (1 : G ⧸ P → ℝ≥0∞) q
          ≤ ∑ j, (if rp q * γ j ∉ Ω then (1 : ℝ≥0∞) else 0) := by
            apply Finset.sum_le_sum
            intro j _
            simp only [Set.indicator_apply, Pi.one_apply]
            split_ifs with h1 h2 <;> first | exact le_rfl | exact zero_le | exact absurd h2 h1.2
        _ = ((Finset.univ.filter (fun j => rp q * γ j ∉ Ω)).card : ℝ≥0∞) := by
            rw [Finset.sum_boole]
        _ ≤ d := by exact_mod_cast hc
    · calc ∑ j, (A (γ j)).indicator (1 : G ⧸ P → ℝ≥0∞) q = 0 :=
            Finset.sum_eq_zero (fun j _ => Set.indicator_of_notMem (by exact fun h => hq h.1) _)
        _ ≤ d := zero_le
  have hsumA : ∑ j, ν (A (γ j)) ≤ (d : ℝ≥0∞) * ν univ := by
    calc ∑ j, ν (A (γ j)) = ∑ j, ∫⁻ q, (A (γ j)).indicator 1 q ∂ν :=
          Finset.sum_congr rfl (fun j _ => (lintegral_indicator_one (hAm _)).symm)
      _ = ∫⁻ q, ∑ j, (A (γ j)).indicator 1 q ∂ν :=
          (lintegral_finsetSum _ (fun j _ => measurable_one.indicator (hAm _))).symm
      _ ≤ ∫⁻ _q, (d : ℝ≥0∞) ∂ν := lintegral_mono hpt
      _ = (d : ℝ≥0∞) * ν univ := lintegral_const _
  have hMle : (M : ℝ≥0∞) * ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'})
      ≤ ENNReal.ofReal B * ((d : ℝ≥0∞) * ν univ) := by
    calc (M : ℝ≥0∞) * ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'})
        = ∑ _j : Fin M, ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'}) := by simp
      _ ≤ ∑ j, ENNReal.ofReal B * ν (A (γ j)) := Finset.sum_le_sum (fun j _ => hstep j)
      _ = ENNReal.ofReal B * ∑ j, ν (A (γ j)) := (Finset.mul_sum _ _ _).symm
      _ ≤ ENNReal.ofReal B * ((d : ℝ≥0∞) * ν univ) := by gcongr
  exact absurd hM (not_lt.mpr hMle)

theorem nullC_of_invM : InvM → NullC := by
  intro hInvM
  unfold NullC ForSet
  intro G _ _ _ _ _ _ P _ _ h mu hS ν hRepr Ω hΩ hP hF
  have : IsFiniteMeasure ν := hRepr.1
  have hInv : ∀ x : G, Inv P h mu x → ∀ F : G ⧸ P → ℝ≥0∞, Measurable F →
      ∫⁻ q, F (x⁻¹ • q) * ENNReal.ofReal (h (rp q * x) / h (rp q)) ∂ν = ∫⁻ q, F q ∂ν :=
    fun x hx => (hInvM G P h mu hS ν hRepr x hx).2
  apply measure_null_of_locally_null
  intro q0 _
  obtain ⟨W, hWo, hq0W, hWnull⟩ := local_null hS hInv hΩ hP hF q0
  exact ⟨{q | rp q ∉ Ω} ∩ W, inter_mem_nhdsWithin _ (hWo.mem_nhds hq0W), hWnull⟩

end GlobalTheory.CompanionTheory.RswCell.NullCompl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSmulQuot
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RswCellInv

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G] [TopologicalSpace G]

theorem mk_inv_mul' {P : Subgroup G} {p : G} (hp : p ∈ P) (g : G) :
    (QuotientGroup.mk (p * g)⁻¹ : G ⧸ P) = QuotientGroup.mk g⁻¹ := by
  rw [QuotientGroup.eq]
  simpa using hp

theorem mk_inv_rp' {P : Subgroup G} (q : G ⧸ P) : (QuotientGroup.mk (rp q)⁻¹ : G ⧸ P) = q := by
  simp [rp]

theorem rp_mk_inv {P : Subgroup G} (g : G) :
    ∃ p ∈ P, rp (QuotientGroup.mk g⁻¹ : G ⧸ P) = p * g := by
  have hmem : rp (QuotientGroup.mk g⁻¹ : G ⧸ P) * g⁻¹ ∈ P := by
    have := mk_inv_rp' (QuotientGroup.mk g⁻¹ : G ⧸ P)
    rw [QuotientGroup.eq] at this
    simpa using this
  exact ⟨_, hmem, by simp⟩

theorem mk_inv_rp_mul {P : Subgroup G} (q : G ⧸ P) (x : G) :
    (QuotientGroup.mk (rp q * x)⁻¹ : G ⧸ P) = x⁻¹ • q := by
  conv_rhs => rw [← mk_inv_rp' q]
  rw [mul_inv_rev]
  rfl

theorem density_rp {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} (S : Setup P h mu) (x g : G) :
    h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P) * x) / h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) =
      h (g * x) / h g := by
  obtain ⟨p, hp, e⟩ := rp_mk_inv (P := P) g
  rw [e]
  have h1 := (S.pos (p * g)).ne'
  have h2 := (S.pos g).ne'
  rw [div_eq_div_iff h1 h2]
  have := S.law p hp g (g * x)
  rw [mul_assoc]
  linarith

theorem sec_translate {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} [ContinuousMul G] (S : Setup P h mu)
    {f : G → ℂ} (hf : Sec P h f) (x : G) : Sec P h (fun g => f (g * x)) := by
  refine ⟨hf.1.comp (continuous_mul_const x), fun p hp g => ?_⟩
  have h1 := hf.2 p hp (g * x)
  have h2 : ((h (p * g) : ℂ)) * h (g * x) = h g * h (p * (g * x)) := by
    exact_mod_cast S.law p hp g (g * x)
  have h3 : (h (g * x) : ℂ) ≠ 0 := by exact_mod_cast (S.pos _).ne'
  apply mul_right_cancel₀ h3
  show f (p * g * x) * (h g : ℂ) * (h (g * x) : ℂ) = f (g * x) * (h (p * g) : ℂ) * (h (g * x) : ℂ)
  rw [mul_assoc p g x]
  linear_combination (h g : ℂ) * h1 - f (g * x) * h2

variable [IsTopologicalGroup G]

theorem sec_of_real {P : Subgroup G} {h : G → ℝ} (hc : Continuous h) {F : G ⧸ P → ℝ} (hF : Continuous F) :
    Sec P h (fun g => ((F (QuotientGroup.mk g⁻¹) : ℝ) : ℂ) * (h g : ℂ)) := by
  refine ⟨?_, fun p hp g => ?_⟩
  · have : Continuous fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P) :=
      QuotientGroup.continuous_mk.comp continuous_inv
    exact (Complex.continuous_ofReal.comp (hF.comp this)).mul (Complex.continuous_ofReal.comp hc)
  · simp only [mk_inv_mul' hp]
    ring

theorem continuous_density {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} (S : Setup P h mu) (x : G) :
    Continuous fun q : G ⧸ P => h (rp q * x) / h (rp q) := by
  have hq : IsQuotientMap fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P) :=
    (QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.comp (Homeomorph.inv G).isQuotientMap
  rw [hq.continuous_iff]
  have : ((fun q : G ⧸ P => h (rp q * x) / h (rp q)) ∘ fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P)) =
      fun g => h (g * x) / h g := by
    funext g
    exact density_rp S x g
  rw [this]
  exact (S.cont.comp (continuous_mul_const x)).div S.cont fun g => (S.pos g).ne'

theorem continuous_smul_quot {P : Subgroup G} (x : G) : Continuous fun q : G ⧸ P => x • q := by
  rw [(QuotientGroup.isOpenQuotientMap_mk (N := P)).isQuotientMap.continuous_iff]
  exact QuotientGroup.continuous_mk.comp (continuous_const_mul x)

theorem compact_quot' {P : Subgroup G}
    (hco : ∃ C : Set G, IsCompact C ∧ ∀ g, ∃ q ∈ P, ∃ c ∈ C, g = q * c) : CompactSpace (G ⧸ P) := by
  obtain ⟨C, hC, hcov⟩ := hco
  have hK : IsCompact ((fun g : G => (QuotientGroup.mk g⁻¹ : G ⧸ P)) '' C) :=
    hC.image (QuotientGroup.continuous_mk.comp continuous_inv)
  refine ⟨?_⟩
  convert hK using 1
  symm
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨q, hq, c, hc, hqc⟩ := hcov y⁻¹
  refine ⟨c, hc, ?_⟩
  have : y = (q * c)⁻¹ := by rw [← hqc, inv_inv]
  rw [this, QuotientGroup.eq]
  simpa using hq

theorem integral_translate {P : Subgroup G} [MeasurableSpace (G ⧸ P)] {h : G → ℝ} {mu : (G → ℂ) → ℂ}
    (S : Setup P h mu) {ν : Measure (G ⧸ P)} (hR : Repr P h mu ν) {x : G} (hx : Inv P h mu x)
    {F : G ⧸ P → ℝ} (hF : Continuous F) :
    ∫ q, h (rp q * x) / h (rp q) * F (x⁻¹ • q) ∂ν = ∫ q, F q ∂ν := by
  have hs := sec_of_real (P := P) S.cont hF
  have h1 := (hR.2 _ hs).2
  have h2 := (hR.2 _ (sec_translate S hs x)).2
  have h3 := hx _ hs
  rw [h1, h2] at h3
  have e1 : ∀ q : G ⧸ P, (((F (QuotientGroup.mk (rp q)⁻¹) : ℝ) : ℂ) * (h (rp q) : ℂ)) / (h (rp q) : ℂ) =
      ((F q : ℝ) : ℂ) := fun q => by
    have : (h (rp q) : ℂ) ≠ 0 := by exact_mod_cast (S.pos _).ne'
    rw [mk_inv_rp', mul_div_cancel_right₀ _ this]
  have e2 : ∀ q : G ⧸ P, (((F (QuotientGroup.mk (rp q * x)⁻¹) : ℝ) : ℂ) * (h (rp q * x) : ℂ)) / (h (rp q) : ℂ) =
      ((h (rp q * x) / h (rp q) * F (x⁻¹ • q) : ℝ) : ℂ) := fun q => by
    rw [mk_inv_rp_mul]
    push_cast
    ring
  simp only [e1, e2] at h3
  rw [integral_complex_ofReal, integral_complex_ofReal] at h3
  exact_mod_cast h3

theorem inv_measure [T2Space G] [SecondCountableTopology G] (P : Subgroup G) [MeasurableSpace (G ⧸ P)]
    [BorelSpace (G ⧸ P)] (h : G → ℝ) (mu : (G → ℂ) → ℂ) (S : Setup P h mu) (ν : Measure (G ⧸ P))
    (hR : Repr P h mu ν) (x : G) (hx : Inv P h mu x) :
    (ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))).map (fun q => x⁻¹ • q) = ν := by
  have : IsClosed (P : Set G) := S.closed
  have : CompactSpace (G ⧸ P) := compact_quot' S.cocpt
  have : IsFiniteMeasure ν := hR.1
  have hj := continuous_density S x
  have hsm := continuous_smul_quot (P := P) x⁻¹
  have hjm : Measurable fun q : G ⧸ P => ENNReal.ofReal (h (rp q * x) / h (rp q)) :=
    ENNReal.measurable_ofReal.comp hj.measurable
  have hjnn : ∀ q : G ⧸ P, 0 ≤ h (rp q * x) / h (rp q) := fun q => (div_pos (S.pos _) (S.pos _)).le
  have hfin : IsFiniteMeasure (ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))) :=
    isFiniteMeasure_withDensity_ofReal
      (hj.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).2
  have hfin' : IsFiniteMeasure
      ((ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))).map (fun q => x⁻¹ • q)) :=
    Measure.isFiniteMeasure_map _ _
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map hsm.aemeasurable f.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hjm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have := integral_translate S hR hx f.continuous
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [ENNReal.toReal_ofReal (hjnn q), smul_eq_mul]

theorem invM : InvM := by
  intro G _ _ _ _ _ _ P _ _ h mu S ν hR x hx
  refine ⟨continuous_density S x, fun F hF => ?_⟩
  have hsm := continuous_smul_quot (P := P) x⁻¹
  have hjm : Measurable fun q : G ⧸ P => ENNReal.ofReal (h (rp q * x) / h (rp q)) :=
    ENNReal.measurable_ofReal.comp (continuous_density S x).measurable
  have key : ∫⁻ q, F q ∂((ν.withDensity fun q => ENNReal.ofReal (h (rp q * x) / h (rp q))).map
      (fun q => x⁻¹ • q)) = ∫⁻ q, F q ∂ν := by rw [inv_measure P h mu S ν hR x hx]
  rw [lintegral_map hF hsm.measurable,
    lintegral_withDensity_eq_lintegral_mul ν hjm
      (show Measurable fun a => F (x⁻¹ • a) from hF.comp hsm.measurable)] at key
  rw [← key]
  refine lintegral_congr fun q => ?_
  simp only [Pi.mul_apply, mul_comm]

end GlobalTheory.CompanionTheory.RswCellInv

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.MuCellOf
noncomputable section

open scoped Matrix NNReal ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.Cell

theorem muCell_of (hR : Riesz) (hN : NullC) (hF : CellFormula) (hA : CellAlg) (hD : Decomp) (hW : FewC) (hS : SetC)
    (hT : TopC) : MuCell := by
  intro D p mu hmu nb hnb w hw
  refine ⟨∅, fun S _ e he lam hlam => ?_⟩
  obtain ⟨hG2, hGlc, hGsc, hH2, hHlc, hHsc, hHb⟩ := hT D p e
  haveI := hlam
  obtain ⟨h, hSet, hRho, hKh, hInv⟩ := hS D p mu hmu
  letI : MeasurableSpace (G D p ⧸ P D p) := borel _
  haveI : BorelSpace (G D p ⧸ P D p) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := hR (G D p) (P D p) h mu hSet
  obtain ⟨τ, hcell, -, hmm⟩ := hA D p nb hnb w hw S e he
  have hfew : Few (P D p) h mu (cell e) :=
    hW D p mu h nb hnb w hw (fun y => (hInv nb hnb w hw y).2) S e he
  have hnull : ν {q | rp q ∉ cell e} = 0 :=
    hN (G D p) (P D p) h mu hSet ν hν (cell e) hcell.isOpen
      (fun q hq x hx => (hcell.left q hq x hx).1) hfew
  have hdec : ∀ x ∈ cell e, ∃ q ∈ P D p, ∃ u ∈ KOff D p S, x = q * (w * nb (τ x).1) * u ∧
      ∀ z : hermS D p e, nb z.1 * u = u * nb z.1 :=
    fun x hx => hD D p nb hnb w hw S e he x hx (τ x) (hmm x hx)
  have hrel : ∀ (y : hermS D p e), ∀ x ∈ cell e,
      h (x * nb y.1) * h (w * nb (τ x).1) = h (w * nb (τ x + y).1) * h x := by
    intro y x hx
    obtain ⟨q, hq, u, hu, ex, hcomm⟩ := hdec x hx
    have hadd : nb (τ x + y).1 = nb (τ x).1 * nb y.1 := hcell.nbAdd (τ x) y
    have e0 : h (x * nb y.1) = h (q * (w * nb (τ x).1) * u * nb y.1) :=
      congrArg (fun z => h (z * nb y.1)) ex
    have e1 : q * (w * nb (τ x).1) * u * nb y.1 = q * (w * nb (τ x + y).1) * u := by
      rw [hadd]
      simp only [mul_assoc]
      rw [← hcomm y]
    have hx1 : h (x * nb y.1) = h (q * (w * nb (τ x + y).1)) := by
      rw [e0, e1, hKh S u hu]
    have hx2 : h x = h (q * (w * nb (τ x).1)) := (congrArg h ex).trans (hKh S u hu _)
    rw [hx1, hx2]
    exact hSet.law q hq _ _
  obtain ⟨c, hc⟩ := hF (G D p) (P D p) h mu hSet ν hν (hermS D p e) lam (cell e) τ w
    (fun y => nb y.1) hcell (fun y => (hInv nb hnb w hw y.1).1) hrel hnull
  have hOn : ∀ f, IsRho f → (∀ u ∈ KOff D p S, ∀ g, f (g * u) = f g) →
      OnCell h (cell e) τ w (fun y => nb y.1) f := by
    intro f hf hfK x hx
    obtain ⟨q, hq, u, hu, ex, -⟩ := hdec x hx
    have hsec := (hRho f).mp hf
    have hf1 : f x = f (q * (w * nb (τ x).1)) := (congrArg f ex).trans (hfK u hu _)
    have hh1 : h x = h (q * (w * nb (τ x).1)) := (congrArg h ex).trans (hKh S u hu _)
    show f x * h (w * nb (τ x).1) = f (w * nb (τ x).1) * h x
    rw [hf1, hh1]
    exact hsec.2 q hq _
  by_cases hc0 : c = 0
  · left
    intro f hf hfK
    have hmu' := (hc f ((hRho f).mp hf) (hOn f hf hfK)).2
    rw [hmu', hc0, zero_smul, integral_zero_measure]
  · right
    refine ⟨c, NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc0), fun f hf hfK => ?_⟩
    obtain ⟨hi, heq⟩ := hc f ((hRho f).mp hf) (hOn f hf hfK)
    refine ⟨?_, ?_⟩
    · have hi' := hi.smul_measure_nnreal (c := c⁻¹)
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hi'
    · rw [heq, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end PositivityTheory.Rg.Rsw.Cell

end
end

namespace PositivityTheory.Rg.Rsw.Cell

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

theorem muCell : HtExist → IdemEx → MuCell := fun hH hI =>
  have hU := GlobalTheory.CompanionTheory.UnitCell.unitCrit hI
  have hA := GlobalTheory.CompanionTheory.CellTop.cellAlg hI
  muCell_of GlobalTheory.CompanionTheory.RswCell.riesz (GlobalTheory.CompanionTheory.RswCell.NullCompl.nullC_of_invM GlobalTheory.CompanionTheory.RswCellInv.invM) (GlobalTheory.CompanionTheory.RswCell.cellFormula_of_invM GlobalTheory.CompanionTheory.RswCellInv.invM) hA (GlobalTheory.CompanionTheory.CellDecomp.decomp hI)
    (GlobalTheory.CompanionTheory.CellFew.fewC hI hU (GlobalTheory.CompanionTheory.MoveCell.move_of_unitCrit hU) (GlobalTheory.CompanionTheory.SmallRatCell.smallRat hI) hA) (GlobalTheory.CompanionTheory.SetCell.setC hH) GlobalTheory.CompanionTheory.RswTop.topC

end PositivityTheory.Rg.Rsw.Cell
