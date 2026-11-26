module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TermBasic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem mem_smul (n : S.GLV) (Λ : Submodule L.O S.V) (x : S.V) :
    x ∈ n • Λ ↔ ∃ y ∈ Λ, n y = x :=
  Submodule.mem_smul_pointwise_iff_exists x n Λ

theorem smul_eq_map (n : S.GLV) (Λ : Submodule L.O S.V) :
    n • Λ = Λ.map (n.toLinearMap.restrictScalars L.O) := by
  ext x
  rw [mem_smul, Submodule.mem_map]
  rfl

theorem isSD_smul {n : S.GLV} (hn : n ∈ isomG L S.Hm) {Λ : Submodule L.O S.V} (h : IsSD L S.Hm Λ) :
    IsSD L S.Hm (n • Λ) := by
  obtain ⟨⟨hfg, hsp⟩, hd⟩ := h
  have hn' : ∀ x y, hf L S.Hm (n x) (n y) = hf L S.Hm x y := hn
  refine ⟨⟨by rw [smul_eq_map]; exact hfg.map _, ?_⟩, fun y => ?_⟩
  · have : ((n • Λ : Submodule L.O S.V) : Set S.V) = n.toLinearMap '' (Λ : Set S.V) := by
      rw [smul_eq_map]; rfl
    rw [this, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨y, rfl⟩ := n.surjective y
    constructor
    · intro h
      refine (mem_smul S n Λ _).2 ⟨y, (hd y).1 fun x hx => ?_, rfl⟩
      rw [← hn']
      exact h _ ((mem_smul S n Λ _).2 ⟨x, hx, rfl⟩)
    · intro h x hx
      obtain ⟨y', hy', e⟩ := (mem_smul S n Λ _).1 h
      obtain ⟨x', hx', rfl⟩ := (mem_smul S n Λ _).1 hx
      rw [← e, hn']
      exact (hd y').2 hy' x' hx'

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun a (ha : (a : ℕ) < i) => lt_of_lt_of_le ha h)

theorem self_mem (g : Fin (r + 1) → S.V) {i : Fin (r + 1)} {j : ℕ} (h : (i : ℕ) < j) :
    g i ∈ S.spanTo g j := Submodule.subset_span ⟨i, h, rfl⟩

theorem spanTo_top (g : Fin (r + 1) → S.V) :
    S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
  have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
    ext i; simpa using i.2
  rw [Frames.spanTo, hs, Set.image_univ]

section
variable {S} {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
include hg

theorem sub_mem {n : S.GLV} (hn : n ∈ S.Nof g) (i : Fin (r + 1)) : n (g i) - g i ∈ S.spanTo g i := by
  obtain ⟨⟨-, h2⟩, h3⟩ := hn
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine h3.2 _ ?_
    rw [Frames.spanTo, StdLat.image_lt, StdLat.mem_perp_span]
    exact hg _
  · exact (Subgroup.mem_iInf.1 h2 i).2 _ (self_mem S g (by simp))

theorem map_mem {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) {x : S.V} (hx : x ∈ S.spanTo g j) :
    n x ∈ S.spanTo g j := by
  have : S.spanTo g j ≤ (S.spanTo g j).comap n.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, hi, rfl⟩
    have h1 := (S.spanTo g j).add_mem (spanTo_mono S g (le_of_lt hi) (sub_mem hg hn i))
      (self_mem S g hi)
    rw [sub_add_cancel] at h1
    exact h1
  exact this hx

theorem map_mem_iff {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) (x : S.V) :
    n x ∈ S.spanTo g j ↔ x ∈ S.spanTo g j := by
  refine ⟨fun h => ?_, map_mem hg hn j⟩
  have := map_mem hg ((S.Nof g).inv_mem hn) j h
  have e : n⁻¹ (n x) = x := n.symm_apply_apply x
  rwa [e] at this

theorem trace_smul {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V} {j : ℕ}
    (h : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g j) ↔ x ∈ Submodule.span L.O (g '' {i | (i : ℕ) < j})) (x : S.V) :
    (x ∈ n • Λ ∧ x ∈ S.spanTo g j) ↔
      x ∈ Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}) := by
  have e : Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}) =
      n • Submodule.span L.O (g '' {i | (i : ℕ) < j}) := by
    rw [smul_eq_map, Submodule.map_span, Set.image_image]; rfl
  rw [e, mem_smul, mem_smul]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h2⟩
    exact ⟨y, (h y).1 ⟨hy, (map_mem_iff hg hn j y).1 h2⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, ((h y).2 hy).1, rfl⟩, map_mem hg hn j ((h y).2 hy).2⟩

end

theorem inner_smul {g : Fin (r + 1) → S.V} {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V}
    (x : S.V) :
    (∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r) ↔
      ∃ y ∈ n • Λ, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  obtain ⟨h1, h2⟩ := hn.2
  constructor
  · rintro ⟨y, hy, hp, hx⟩
    refine ⟨n y, (mem_smul S n Λ _).2 ⟨y, hy, rfl⟩, (h1 y).2 hp, ?_⟩
    have := (S.spanTo g r).add_mem (h2 y hp) hx
    rwa [sub_add_sub_cancel] at this
  · rintro ⟨_, hy, hp, hx⟩
    obtain ⟨y, hy0, rfl⟩ := (mem_smul S n Λ _).1 hy
    refine ⟨y, hy0, (h1 y).1 hp, ?_⟩
    have := (S.spanTo g r).sub_mem hx (h2 y ((h1 y).1 hp))
    rwa [sub_sub_sub_cancel_left] at this

theorem term_basic : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → IsSD L S.Hm Λ ∧ S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 ∧ S.M d Λ ≤ S.sat Λ ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f j) ↔ x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < j})) ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' j) ↔ x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < j})) ∧ LinearIndependent E (Sum.elim (S.fr d Λ) (S.fr' d Λ)) ∧ S.IsIntCls (S.Fr d Λ) ∧ ∀ d', S.IsTerm d' Λ → d' = d := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  have hW : S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 := by
    rw [Frames.wit, dite_eq_left hT]
    exact hT.choose_spec
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  obtain ⟨hli, -, -, -, -, hth, -⟩ := FrameBasic.main L r k S
  have det : ∀ d : S.Datum, S.IsTerm d Λ →
      (∀ x, x ∈ d.1 ↔ ∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo S.f r) ∧ y - x ∈ S.spanTo S.f r) ∧
      (∀ x, x ∈ d.2.1 ↔ ∃ y ∈ Λ, y ∈ perp L S.Hm (S.spanTo S.f' r) ∧ y - x ∈ S.spanTo S.f' r) ∧
      d.2.2 = S.graphOf Λ := by
    rintro d ⟨p, hA, hA', hn, hn', e, e', -, hgr⟩
    refine ⟨fun x => ?_, fun x => ?_, hgr⟩
    · rw [(StdLat.stdLat_spec L r k S _ _ (Or.inl ⟨rfl, rfl⟩) _ hA).2.2 x, inner_smul S hn, ← e]
    · rw [(StdLat.stdLat_spec L r k S _ _ (Or.inr ⟨rfl, rfl⟩) _ hA').2.2 x, inner_smul S hn', ← e']
  obtain ⟨hA, hA', hn, hn', e, e', hth', hgr⟩ := id hW
  obtain ⟨s1, s2, -⟩ := StdLat.stdLat_spec L r k S _ _ (Or.inl ⟨rfl, rfl⟩) _ hA
  obtain ⟨-, s2', -⟩ := StdLat.stdLat_spec L r k S _ _ (Or.inr ⟨rfl, rfl⟩) _ hA'
  have hSD : IsSD L S.Hm Λ := by
    have := isSD_smul S hn.1.1 s1
    rwa [← e] at this
  have t : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f j) ↔
      x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < j}) := fun j hj x => by
    have := trace_smul hg hn (s2 j hj) x
    rwa [← e] at this
  have t' : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' j) ↔
      x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < j}) := fun j hj x => by
    have := trace_smul hg' hn' (s2' j hj) x
    rwa [← e'] at this
  have m : ∀ b, S.fr d Λ b ∈ Λ ∧ S.fr d Λ b ∈ S.spanTo S.f (r + 1) := fun b =>
    (t _ le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)
  have m' : ∀ b, S.fr' d Λ b ∈ Λ ∧ S.fr' d Λ b ∈ S.spanTo S.f' (r + 1) := fun b =>
    (t' _ le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩)
  refine ⟨hSD, hW, ?_, t, t', ?_, ⟨⟨_, hn, _, hn', rfl⟩, ?_⟩, fun d' hd' => ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨(m b).1, Submodule.mem_sup_left (m b).2⟩
    · refine ⟨?_, S.ME.smul_mem _ (S.ME.sub_mem (Submodule.mem_sup_right (m' b).2)
        (Submodule.mem_sup_left (m b).2))⟩
      obtain ⟨y, hy, e2⟩ := hth' b
      have e3 : S.fr' d Λ b - S.fr d Λ b = algebraMap F E S.th • y := e2
      simp only [e3, smul_smul, ← map_mul, inv_mul_cancel₀ hth, map_one, one_smul]
      exact hy
  · obtain ⟨l1, l2, l3⟩ := linearIndependent_sum.1 hli
    refine LinearIndependent.sum_type (l1.map' (S.wit d Λ).1.toLinearMap (LinearEquiv.ker _))
      (l2.map' (S.wit d Λ).2.toLinearMap (LinearEquiv.ker _)) (l3.mono ?_ ?_)
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      have := (m b).2
      rw [spanTo_top] at this
      exact this
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b, rfl⟩
      have := (m' b).2
      rw [spanTo_top] at this
      exact this
  · rintro p ⟨A, A', hi, hi', -, -, -, h1, h2⟩ a b
    refine (hSD.2 _).2 ?_ _ ?_
    · rw [h1]
      exact Λ.sum_mem fun i _ => Λ.smul_mem (⟨_, hi i a⟩ : L.O) (m i).1
    · rw [h2]
      exact Λ.sum_mem fun i _ => Λ.smul_mem (⟨_, hi' i b⟩ : L.O) (m' i).1
  · obtain ⟨a1, a2, a3⟩ := det d hT
    obtain ⟨b1, b2, b3⟩ := det d' hd'
    exact Prod.ext (Submodule.ext fun x => (b1 x).trans (a1 x).symm)
      (Prod.ext (Submodule.ext fun x => (b2 x).trans (a2 x).symm) (b3.trans a3.symm))

end GlobalTheory.HL.TermBasic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFactsStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_double_coset_term_basic_facts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → IsSD L S.Hm Λ ∧ S.IsTermW d Λ (S.wit d Λ).1 (S.wit d Λ).2 ∧ S.M d Λ ≤ S.sat Λ ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f j) ↔ x ∈ Submodule.span L.O (S.fr d Λ '' {i | (i : ℕ) < j})) ∧ (∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' j) ↔ x ∈ Submodule.span L.O (S.fr' d Λ '' {i | (i : ℕ) < j})) ∧ LinearIndependent E (Sum.elim (S.fr d Λ) (S.fr' d Λ)) ∧ S.IsIntCls (S.Fr d Λ) ∧ ∀ d', S.IsTerm d' Λ → d' = d := by
  first | exact @GlobalTheory.HL.TermBasic.term_basic | exact GlobalTheory.HL.TermBasic.term_basic | (intros; apply GlobalTheory.HL.TermBasic.term_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.RatExt

section General
variable {E R : Type} [Field E] [CommRing R] (ι : E →+* R)

theorem single_comp {n : ℕ} (i : Fin n) :
    (fun j => ι ((Pi.single i 1 : Fin n → E) j)) = (Pi.single i 1 : Fin n → R) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem span_range {n : ℕ} :
    Submodule.span R (Set.range fun (x : Fin n → E) (i : Fin n) => ι (x i)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun R (Fin n)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Pi.single i 1, by simpa using single_comp ι i⟩

theorem lin_ext {n : ℕ} {M : Type} [AddCommGroup M] [Module R M] (a b : (Fin n → R) →ₗ[R] M)
    (h : ∀ x : Fin n → E, a (fun i => ι (x i)) = b (fun i => ι (x i))) : a = b :=
  LinearMap.ext_on_range (span_range ι) h

theorem _root_.GlobalTheory.HL.RatExt.exists_equiv {n : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    ∃ g' : (Fin n → R) ≃ₗ[R] (Fin n → R), ∀ x, g' (fun i => ι (x i)) = fun i => ι (g x i) := by
  set M := LinearMap.toMatrix' (g : (Fin n → E) →ₗ[E] (Fin n → E))
  set N := LinearMap.toMatrix' (g.symm : (Fin n → E) →ₗ[E] (Fin n → E))
  have hMN : M * N = 1 := by
    simp only [M, N, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hNM : N * M = 1 := by
    simp only [M, N, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  refine ⟨LinearEquiv.ofLinear (Matrix.toLin' (M.map ι)) (Matrix.toLin' (N.map ι)) ?_ ?_, ?_⟩
  · rw [← Matrix.toLin'_mul, ← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero ι) (map_one ι),
      Matrix.toLin'_one]
  · rw [← Matrix.toLin'_mul, ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero ι) (map_one ι),
      Matrix.toLin'_one]
  · intro x
    funext i
    simp only [LinearEquiv.ofLinear_apply, Matrix.toLin'_apply]
    have h := LinearMap.toMatrix'_mulVec (g : (Fin n → E) →ₗ[E] (Fin n → E)) x
    rw [show g x = M.mulVec x from h.symm, RingHom.map_mulVec]
    rfl

end General

private theorem exists_dual_family_of_linearIndependent {E : Type} [Field E] {n m : ℕ} {v : Fin m → Fin n → E}
    (hv : LinearIndependent E v) :
    ∃ φ : Fin m → (Fin n → E) →ₗ[E] E, ∀ a b, φ b (v a) = if a = b then 1 else 0 := by
  choose φ hφ using fun b =>
    LinearMap.exists_extend ((Module.Basis.span hv).coord b)
  refine ⟨φ, fun a b => ?_⟩
  have h := LinearMap.congr_fun (hφ b) ⟨v a, Submodule.subset_span (Set.mem_range_self a)⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h
  rw [h]
  have hb : (⟨v a, Submodule.subset_span (Set.mem_range_self a)⟩ : Submodule.span E (Set.range v))
      = Module.Basis.span hv a := by
    ext; simp [Module.Basis.span_apply]
  rw [hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

theorem _root_.GlobalTheory.HL.RatExt.rational_extend : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : _root_.GlobalTheory.HL.Places F E sig), ∀ (n : ℕ) (p : HeightOneSpectrum (𝓞 F)), Function.Injective (A.bc (n := n) p) ∧ Submodule.span (A.loc p).Ep (Set.range (A.bc (n := n) p)) = ⊤ ∧ (∀ g : (Fin n → E) ≃ₗ[E] (Fin n → E), ∃! g', A.Ext p g g') ∧ (∀ (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) g' (Λ : Submodule (𝓞 E) (Fin n → E)), A.Ext p g g' → A.lat p (Λ.map ((g : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) = g' • A.lat p Λ) ∧ (∀ (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E), _root_.GlobalTheory.HL.hf (A.L p) (Hm.map (A.loc p).ιE) (A.bc p x) (A.bc p y) = (A.loc p).ιE (∑ i, ∑ j, x i * Hm i j * sig (y j))) ∧ ∀ (m : ℕ) (v : Fin m → Fin n → E), LinearIndependent E v ↔ LinearIndependent (A.loc p).Ep fun a => A.bc p (v a) := by
  intro F E _ _ _ _ _ sig A n p
  have hbc : ∀ x : Fin n → E, A.bc p x = fun i => (A.loc p).ιE (x i) := fun _ => rfl
  haveI : Nontrivial (A.loc p).Ep := by
    have h := (A.L p).rank
    exact Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by omega)
  have hinj : Function.Injective (A.bc (n := n) p) := by
    intro x y h
    funext i
    exact (A.loc p).ιE.injective (congrFun h i)
  have hspan : Submodule.span (A.loc p).Ep (Set.range (A.bc (n := n) p)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun (A.loc p).Ep (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    rw [hbc, Pi.basisFun_apply]
    funext j
    rcases eq_or_ne j i with rfl | h <;> simp [*]
  have hext : ∀ g : (Fin n → E) ≃ₗ[E] (Fin n → E), ∃ g', A.Ext p g g' := by
    intro g
    obtain ⟨g', hg'⟩ := _root_.GlobalTheory.HL.RatExt.exists_equiv (A.loc p).ιE g
    exact ⟨g', fun x => hg' x⟩
  refine ⟨hinj, hspan, fun g => ?_, fun g g' Λ hg => ?_, fun Hm x y => ?_, fun m v => ?_⟩
  · obtain ⟨g', hg'⟩ := hext g
    refine ⟨g', hg', fun g'' hg'' => ?_⟩
    apply LinearEquiv.toLinearMap_injective
    refine LinearMap.ext_on_range hspan fun x => ?_
    simp only [LinearEquiv.coe_coe]
    rw [hg'' x, hg' x]
  · unfold _root_.GlobalTheory.HL.Places.lat
    rw [Submodule.smul_span]
    congr 1
    rw [Submodule.map_coe, Set.image_image, ← Set.image_smul, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [LinearEquiv.smul_def, hg x]
    rfl
  · unfold _root_.GlobalTheory.HL.hf
    rw [_root_.GlobalTheory.HL.Places.L_cj]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hbc, map_sum, map_mul, Matrix.map_apply, _root_.Formalism.MainNotions.S.Loc.LocAt.cj_ιE]
  · constructor
    · intro hv
      obtain ⟨φ, hφ⟩ := exists_dual_family_of_linearIndependent hv
      rw [Fintype.linearIndependent_iff]
      intro c hc b
      have key : ∀ a, ∑ j, (A.loc p).ιE (v a j) *
          (A.loc p).ιE (φ b (fun k => if j = k then 1 else 0)) = if a = b then 1 else 0 := by
        intro a
        have h := congrArg (A.loc p).ιE (LinearMap.pi_apply_eq_sum_univ (φ b) (v a))
        rw [hφ] at h
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, smul_eq_mul, map_mul] at h
        rw [← h]
        split_ifs <;> simp
      calc c b = ∑ a, c a * (if a = b then 1 else 0) := by simp
        _ = ∑ a, c a * ∑ j, (A.loc p).ιE (v a j) *
              (A.loc p).ιE (φ b (fun k => if j = k then 1 else 0)) := by simp only [key]
        _ = ∑ j, (∑ a, c a • A.bc p (v a)) j *
              (A.loc p).ιE (φ b (fun k => if j = k then 1 else 0)) := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hbc, Finset.mul_sum,
            Finset.sum_mul, mul_assoc]
          exact Finset.sum_comm
        _ = 0 := by rw [hc]; simp
    · intro hv
      rw [Fintype.linearIndependent_iff] at hv ⊢
      intro c hc a
      have h := hv (fun a => (A.loc p).ιE (c a)) (by
        funext j
        have hj := congrFun hc j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hbc] at hj ⊢
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_zero (A.loc p).ιE, ← hj, map_sum]
        simp [map_mul])
      exact (map_eq_zero_iff _ (A.loc p).ιE.injective).mp (h a)

end GlobalTheory.HL.RatExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PlacesInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem val_le_iff (T : LocAt F E sig p) (x y : F) :
    valuation T.Fp (T.ιF x) ≤ valuation T.Fp (T.ιF y) ↔ p.valuation F x ≤ p.valuation F y := by
  rw [← T.val, (valuation T.Fp).vle_iff_le]

theorem mem_int_iff (T : LocAt F E sig p) (x : F) :
    T.ιF x ∈ 𝒪[T.Fp] ↔ p.valuation F x ≤ 1 := by
  have h := val_le_iff T x 1
  simp only [map_one] at h
  rw [← h]; rfl

theorem val_lt_one_iff (T : LocAt F E sig p) (x : F) :
    valuation T.Fp (T.ιF x) < 1 ↔ p.valuation F x < 1 := by
  have h := val_le_iff T 1 x
  simp only [map_one] at h
  rw [← not_le, ← not_le, h]

theorem resQ_eq_absNorm (T : LocAt F E sig p) (ϖ : 𝒪[T.Fp]) (h : Irreducible ϖ) :
    resQ ϖ = Ideal.absNorm p.asIdeal := by
  haveI := T.lf
  have hm : ∀ z : 𝒪[T.Fp], z ∈ Ideal.span {ϖ} ↔ valuation T.Fp (z : T.Fp) < 1 := by
    intro z
    rw [← h.maximalIdeal_eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  let φ : 𝓞 F →+* 𝒪[T.Fp] := (T.ιF.comp (algebraMap (𝓞 F) F)).codRestrict _
    (fun a => (mem_int_iff T _).2 (p.valuation_le_one a))
  have hφ : ∀ a, ((φ a : 𝒪[T.Fp]) : T.Fp) = T.ιF (algebraMap (𝓞 F) F a) := fun a => rfl
  let ψ : 𝓞 F →+* 𝒪[T.Fp] ⧸ Ideal.span {ϖ} := (Ideal.Quotient.mk _).comp φ
  have hker : RingHom.ker ψ = p.asIdeal := by
    ext a
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (φ a) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, hm, hφ, val_lt_one_iff]
    exact p.valuation_lt_one_iff_mem (K := F) a
  have hsurj : Function.Surjective ψ := by
    intro w
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hn : {z : T.Fp | valuation T.Fp (z - y) < 1} ∈ nhds (y : T.Fp) :=
      IsValuativeTopology.mem_nhds_iff'.2 ⟨1, fun z hz => by simpa using hz⟩
    obtain ⟨x, hx⟩ := T.dense.mem_nhds hn
    have hx' : valuation T.Fp (T.ιF x - y) < 1 := hx
    have hy : valuation T.Fp (y : T.Fp) ≤ 1 := y.2
    have hx1 : valuation T.Fp (T.ιF x) ≤ 1 := by
      have : T.ιF x = (T.ιF x - y) + y := by ring
      rw [this]
      exact (valuation T.Fp).map_add_le hx'.le hy
    obtain ⟨a, ha⟩ := p.exists_valuation_sub_lt_of_integer ((mem_int_iff T x).1 hx1) 1
    refine ⟨a, ?_⟩
    change Ideal.Quotient.mk _ (φ a) = _
    rw [Ideal.Quotient.eq, hm]
    have ha' := (val_lt_one_iff T _).2 (by simpa using ha : p.valuation F (algebraMap (𝓞 F) F a - x) < 1)
    have : ((φ a - y : 𝒪[T.Fp]) : T.Fp) = T.ιF (algebraMap (𝓞 F) F a - x) + (T.ιF x - y) := by
      rw [map_sub, ← hφ]; push_cast; ring
    rw [this]
    exact (valuation T.Fp).map_add_lt ha' hx'
  rw [resQ, Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hker]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm

theorem nontrivial_Ep (T : LocAt F E sig p) : Nontrivial T.Ep :=
  Module.nontrivial_of_finrank_pos (R := T.Fp) (by rw [T.rank]; norm_num)

theorem exists_trace_norm (A : Places F E sig) (x : E) :
    ∃ t n : F, algebraMap F E t = x + sig x ∧ algebraMap F E n = x * sig x := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  haveI := nontrivial_Ep (A.loc p)
  have hss : ∀ y, sig (sig y) = y := by
    intro y
    apply (A.loc p).ιE.injective
    rw [← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]
  have hfix : ∀ y, sig y = y → ∃ a, algebraMap F E a = y := by
    haveI := Subalgebra.isSimpleOrder_of_finrank A.quad
    rcases eq_bot_or_eq_top (AlgHom.equalizer sig (AlgHom.id F E)) with h | h
    · intro y hy
      have : y ∈ AlgHom.equalizer sig (AlgHom.id F E) := hy
      rw [h, Algebra.mem_bot] at this
      exact this
    · exfalso
      have h1 : ∀ y, sig y = y := fun y => by
        have : y ∈ AlgHom.equalizer sig (AlgHom.id F E) := by rw [h]; trivial
        exact this
      have h2 : ∀ z, (A.loc p).cj z = z := by
        intro z
        have hz : z ∈ Submodule.span (A.loc p).Fp (Set.range (A.loc p).ιE) := by
          rw [(A.loc p).span]; trivial
        induction hz using Submodule.span_induction with
        | mem z hz => obtain ⟨y, rfl⟩ := hz; rw [(A.loc p).cj_ιE, h1]
        | zero => simp
        | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
        | smul c a _ ha => rw [map_smul, ha]
      have h3 : Function.Surjective (Algebra.linearMap (A.loc p).Fp (A.loc p).Ep) := by
        intro z
        exact ((A.L p).cj_fix z).1 (by rw [A.L_cj]; exact h2 z)
      have h4 := LinearMap.finrank_le_finrank_of_surjective h3
      rw [(A.loc p).rank, Module.finrank_self] at h4
      omega
  obtain ⟨t, ht⟩ := hfix (x + sig x) (by rw [map_add (f := _), hss, add_comm])
  obtain ⟨n, hn⟩ := hfix (x * sig x) (by rw [map_mul, hss, mul_comm])
  exact ⟨t, n, ht, hn⟩

theorem isIntegral_of_quad {R S : Type} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S]
    (x y : S) (t n : R) (ht : algebraMap R S t = x + y) (hn : algebraMap R S n = x * y) :
    IsIntegral R x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
  · monicity!
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, ht, hn]
    ring

theorem mem_O_iff (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (x : E) (t n : F)
    (ht : algebraMap F E t = x + sig x) (hn : algebraMap F E n = x * sig x) :
    (A.loc p).ιE x ∈ (A.L p).O ↔ p.valuation F t ≤ 1 ∧ p.valuation F n ≤ 1 := by
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  haveI := nontrivial_Ep (A.loc p)
  have ht' : algebraMap _ (A.loc p).Ep ((A.loc p).ιF t)
      = (A.loc p).ιE x + (A.L p).cj ((A.loc p).ιE x) := by
    rw [← (A.loc p).compat, ht, map_add (f := _), A.L_cj, (A.loc p).cj_ιE]
  have hn' : algebraMap _ (A.loc p).Ep ((A.loc p).ιF n)
      = (A.loc p).ιE x * (A.L p).cj ((A.loc p).ιE x) := by
    rw [← (A.loc p).compat, hn, map_mul, A.L_cj, (A.loc p).cj_ιE]
  rw [← mem_int_iff (A.loc p), ← mem_int_iff (A.loc p)]
  constructor
  · intro hx
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[(A.loc p).Fp]
    obtain ⟨-, ⟨c, hc⟩, d, hd⟩ := (GlobalTheory.UnramOrder.order_facts (A.L p) ϖ hϖ).2.1 _ hx
    have hinj := (algebraMap (A.loc p).Fp (A.loc p).Ep).injective
    rw [hinj (ht'.trans hc), hinj (hn'.trans hd)]
    exact ⟨c.2, d.2⟩
  · rintro ⟨h1, h2⟩
    rw [(A.L p).O_def]
    exact isIntegral_of_quad (R := 𝒪[(A.loc p).Fp]) _ _ ⟨_, h1⟩ ⟨_, h2⟩ ht' hn'

theorem integers_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), (∀ x : E, (∀ p, (A.loc p).ιE x ∈ (A.L p).O) ↔ ∃ o : 𝓞 E, (o : E) = x) ∧ (∀ x : E, {p | (A.loc p).ιE x ∉ (A.L p).O}.Finite) ∧ (∀ (x : F) p, (A.loc p).ιF x ∈ 𝒪[(A.loc p).Fp] ↔ p.valuation F x ≤ 1) ∧ ∀ p (ϖ : 𝒪[(A.loc p).Fp]), Irreducible ϖ → resQ ϖ = Ideal.absNorm p.asIdeal := by
  intro F E _ _ _ _ _ sig A
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun x => ?_, fun x p => mem_int_iff _ x,
    fun p ϖ h => resQ_eq_absNorm _ ϖ h⟩
  · obtain ⟨t, n, ht, hn⟩ := exists_trace_norm A x
    have h := fun p => (mem_O_iff A p x t n ht hn).1 (hx p)
    obtain ⟨t', ht'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F t
      (fun p => (h p).1)
    obtain ⟨n', hn'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F n
      (fun p => (h p).2)
    have hi : IsIntegral (𝓞 F) x := isIntegral_of_quad x (sig x) t' n'
      (by rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, ht', ht])
      (by rw [IsScalarTower.algebraMap_apply (𝓞 F) F E, hn', hn])
    exact ⟨⟨x, isIntegral_trans (R := ℤ) x hi⟩, rfl⟩
  · rintro ⟨o, rfl⟩ p
    rw [(A.L p).O_def]
    have h : IsIntegral ℤ ((A.loc p).ιE (o : E)) :=
      map_isIntegral_int (A.loc p).ιE o.isIntegral_coe
    exact h.tower_top
  · obtain ⟨t, n, ht, hn⟩ := exists_trace_norm A x
    refine ((HeightOneSpectrum.Support.finite (𝓞 F) t).union
      (HeightOneSpectrum.Support.finite (𝓞 F) n)).subset fun p hp => ?_
    have hp' : ¬ ((A.loc p).ιE x ∈ (A.L p).O) := hp
    rw [mem_O_iff A p x t n ht hn, not_and_or, not_le, not_le] at hp'
    exact hp'

end GlobalTheory.HL.PlacesInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordExist

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

noncomputable def linL (H : HermSp M V) (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' a b := H.h_add_left a b y
  map_smul' a x := H.h_smul_left a x y

lemma h_sum_left (H : HermSp M V) {n : ℕ} (c : Fin n → E) (b : Fin n → V) (y : V) :
    H.h (∑ i, c i • b i) y = ∑ i, c i * H.h (b i) y := by
  show linL H y (∑ i, c i • b i) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

lemma hf_eq (H : HermSp M V) {n : ℕ} (b : Fin n → V) (c d : Fin n → E) :
    hf M.L (Matrix.of fun i j => H.h (b i) (b j)) c d = H.h (∑ i, c i • b i) (∑ j, d j • b j) := by

  have hr : ∀ (x : V) (d : Fin n → E), H.h x (∑ j, d j • b j) = ∑ j, M.L.cj (d j) * H.h x (b j) := by
    intro x d
    set_option synthInstance.maxHeartbeats 100000 in
      rw [H.h_herm, h_sum_left, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← H.h_herm]
  rw [h_sum_left]
  unfold GlobalTheory.HL.hf
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.of_apply]
  ring

lemma hf_basis (H : HermSp M V) {n : ℕ} (b : Module.Basis (Fin n) E V) (x y : V) :
    hf M.L (Matrix.of fun i j => H.h (b i) (b j)) (b.equivFun x) (b.equivFun y) = H.h x y := by
  rw [hf_eq, b.sum_equivFun, b.sum_equivFun]

lemma nontriv (L : LocE F E) : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)

lemma hermND (H : HermSp M V) {n : ℕ} (b : Module.Basis (Fin n) E V) :
    IsHermND M.L (Matrix.of fun i j => H.h (b i) (b j)) := by
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.HL.IsHerm GlobalTheory.HL.cT
    ext i j
    exact (H.h_herm (b j) (b i)).symm
  · have := M.L.free
    have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
    set G : Matrix (Fin n) (Fin n) E := Matrix.of fun i j => H.h (b i) (b j) with hGdef
    have hvec : ∀ (v : Fin n → E) j, (Matrix.vecMul v G) j = H.h (∑ i, v i • b i) (b j) := by
      intro v j
      rw [h_sum_left]
      simp only [Matrix.vecMul, dotProduct, hGdef, Matrix.of_apply]
    have hright : ∀ x y : V, H.h x y = ∑ j, M.L.cj (b.repr y j) * H.h x (b j) := by
      intro x y
      conv_lhs => rw [← b.sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [H.h_herm, h_sum_left, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← H.h_herm]

    have hinj : Function.Injective (Matrix.vecMulLinear G) := by
      intro v v' hvv
      have hvv' : Matrix.vecMul v G = Matrix.vecMul v' G := hvv
      have hd : ∀ j, (Matrix.vecMul (v - v') G) j = 0 := by
        intro j
        rw [Matrix.sub_vecMul, hvv', sub_self]
        rfl
      have hx : ∑ i, (v - v') i • b i = 0 := by
        apply H.nondeg
        intro y
        rw [hright]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← hvec, hd, mul_zero]
      have h0 := Fintype.linearIndependent_iff.mp b.linearIndependent (v - v') hx
      funext i
      exact sub_eq_zero.mp (h0 i)

    have hsurj : Function.Surjective (Matrix.vecMulLinear G) := by
      have h2 : Function.Injective ((Matrix.vecMulLinear G).restrictScalars F) := hinj
      exact LinearMap.injective_iff_surjective.mp h2
    exact (Matrix.isUnit_iff_isUnit_det G).mp (Matrix.vecMul_surjective_iff_isUnit.mp hsurj)

lemma not_field (L : LocE F E) (g : SplitG L) : ¬ IsField E := by
  intro hE
  have hx : g.e.symm (1, 0) ≠ 0 := by
    intro h0
    have h1 := congrArg g.e h0
    simp at h1
  obtain ⟨x', hx'⟩ := hE.mul_inv_cancel hx
  have hxy : g.e.symm (1, 0) * g.e.symm (0, 1) = 0 := by
    rw [← map_mul]
    simp
  have hy : g.e.symm (0, 1) = 0 := by
    calc g.e.symm (0, 1) = (x' * g.e.symm (1, 0)) * g.e.symm (0, 1) := by
          rw [mul_comm x', hx', one_mul]
      _ = 0 := by rw [mul_assoc, hxy, mul_zero]
  have h1 := congrArg g.e hy
  simp at h1

lemma gram_eq {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a b : Fin (r + 1)) :
    H.h (A.f a) (A.f b) = if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E A.T else 0 := by
  split_ifs with hab
  · rw [hab.1, hab.2]
    exact A.h_zz
  · exact A.h_iso a b (not_and_or.mp hab)

lemma dual_eq {H : HermSp M V} {r : ℕ} (A : LocNG.FrameD H r) (a : Fin (r + 1)) (j : Fin r) :
    H.h (A.f a) (A.es j) = if a = j.castSucc then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    rw [if_neg (Fin.castSucc_lt_last j).ne', H.h_herm, A.h_sz, map_zero]
  | cast i =>
    rw [A.h_es i j]
    simp only [Fin.castSucc_inj]

lemma unit_of {T : F} (hT : T ∈ 𝒪[F]) (u : 𝒪[F]) (h : (u : F) * T = 1) :
    ∃ v : (𝒪[F])ˣ, ((v : 𝒪[F]) : F) = T := by
  refine ⟨⟨⟨T, hT⟩, u, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    show T * (u : F) = 1
    rw [mul_comm]
    exact h
  · apply Subtype.ext
    show (u : F) * T = 1
    exact h

end

theorem exists_coord : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∃ S : Frames M.L r k, Nonempty (Coord P S) := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r k P hrank hrel
  have := hOK.loc
  have : Nontrivial E := nontriv M.L
  have := H.free
  have := H.fin
  unfold LocNG.FPair.RelG LocNG.FPair.IsPoint LocNG.FPair.NormsOK at hrel
  obtain ⟨-, -, hG, -, -, ⟨w, hw⟩, hAT, hA0, hBT, hB0, hsp⟩ := hrel

  obtain ⟨ϖ, hϖ, hϖs⟩ : ∃ ϖ : 𝒪[F], Irreducible ϖ ∧ ∀ g, M.split = some g → ϖ = g.q := by
    cases hs : M.split with
    | none =>
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
      exact ⟨ϖ, hϖ, fun g hg => by cases hg⟩
    | some g =>
      exact ⟨g.q, g.q_irr, fun g' hg => by cases hg; rfl⟩
  let bs : Module.Basis (Fin (k + 2 * r + 1)) E V := Module.finBasisOfFinrankEq E V hrank
  have hZ : (Matrix.of fun a c => hf M.L (Matrix.of fun i j => H.h (bs i) (bs j))
      (bs.equivFun (P.B.f c)) (bs.equivFun (P.A.f a))) = H.Zhat P.A.f P.B.f := by
    ext a c
    simp only [Matrix.of_apply, hf_basis]
    rfl
  have hD1 : lead (H.Zhat P.A.f P.B.f) (Fin.last (r + 1)) = H.Dl P.A.f P.B.f (r + 1) := by
    unfold GlobalTheory.HL.lead HermSp.Dl
    rw [dite_eq_left le_rfl]
  have hD0 : lead (H.Zhat P.A.f P.B.f) (Fin.last r).castSucc = H.Dl P.A.f P.B.f r := by
    unfold GlobalTheory.HL.lead HermSp.Dl
    rw [dite_eq_left (Nat.le_succ r)]
  have hG' := hG
  unfold LocNG.FPair.Gv HermSp.Gdet HermSp.normE at hG'
  rw [← hD1, ← hD0, ← hZ] at hG'
  let S : Frames M.L r k :=
    { ϖ := ϖ
      ϖ_irr := hϖ
      Hm := Matrix.of fun i j => H.h (bs i) (bs j)
      herm := hermND H bs
      T := Units.mk0 P.A.T hA0
      T' := Units.mk0 P.B.T hB0
      f := fun a => bs.equivFun (P.A.f a)
      f' := fun a => bs.equivFun (P.B.f a)
      es := fun j => bs.equivFun (P.A.es j)
      es' := fun j => bs.equivFun (P.B.es j)
      gram := fun a c => by
        rw [hf_basis, gram_eq]
        rfl
      gram' := fun a c => by
        rw [hf_basis, gram_eq]
        rfl
      dual := fun a j => by rw [hf_basis, dual_eq]
      dual' := fun a j => by rw [hf_basis, dual_eq]
      iso := fun i j => by rw [hf_basis, P.A.h_ss]
      iso' := fun i j => by rw [hf_basis, P.B.h_ss]
      w := w
      relevant := fun a c => by
        rw [hf_basis, ← hw a c]
        have hsq : ((-1 : E) ^ (r - (c : ℕ))) * (-1) ^ (r - (c : ℕ)) = 1 := by
          rw [← mul_pow]
          simp
        show H.h (P.B.f c) (P.A.f a) =
          (-1) ^ (r - (c : ℕ)) * H.h (P.B.f c) (P.A.f a) * (-1) ^ (r - (c : ℕ))
        linear_combination (-(H.h (P.B.f c) (P.A.f a))) * hsq
      G_ne := hG'
      gg := M.split.isSome
      gg_ok := by
        intro hgg
        obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp hgg
        obtain ⟨⟨u, v, hu, hv⟩, -⟩ := hsp g hg
        exact ⟨not_field M.L g, unit_of hAT u hu, unit_of hBT v hv⟩ }
  refine ⟨S, ⟨{ e := bs.equivFun
                h_eq := fun x y => hf_basis H bs x y
                f_eq := fun a => rfl
                f'_eq := fun a => rfl
                es_eq := fun a => rfl
                es'_eq := fun a => rfl
                T_eq := rfl
                T'_eq := rfl
                gg_none := fun h => ?_
                gg_some := fun g hg => ⟨?_, hϖs g hg⟩ }⟩⟩
  · show M.split.isSome = false
    rw [h]
    rfl
  · show M.split.isSome = true
    rw [hg]
    rfl

end GlobalTheory.HL.CoordExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumPiProdEnnreal
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem tsum_pi_prod_ennreal : ∀ {ι : Type} [Fintype ι] {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
    ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y := by
  intro ι _
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ {X : ι → Type} (φ : ∀ i, X i → ℝ≥0∞),
      ∑' x : ∀ i, X i, ∏ i, φ i (x i) = ∏ i, ∑' y, φ i y) ?_ ?_ ?_ ι
  · intro α β _ e h X φ
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have h1 := h (X := fun a => X (e a)) (fun a => φ (e a))
    rw [← (Equiv.piCongrLeft X e).tsum_eq]
    calc ∑' x : ∀ a, X (e a), ∏ b, φ b (Equiv.piCongrLeft X e x b)
        = ∑' x : ∀ a, X (e a), ∏ a, φ (e a) (x a) := by
          congr 1; ext x
          rw [← Fintype.prod_equiv e (fun a => φ (e a) (Equiv.piCongrLeft X e x (e a)))
            (fun b => φ b (Equiv.piCongrLeft X e x b)) (fun _ => rfl)]
          simp only [Equiv.piCongrLeft_apply_apply]
      _ = ∏ a, ∑' y, φ (e a) y := h1
      _ = ∏ b, ∑' y, φ b y := Fintype.prod_equiv e _ _ (fun _ => rfl)
  · intro X φ
    simp
  · intro α _ h X φ
    rw [← (Equiv.piOptionEquivProd (β := X)).symm.tsum_eq, Fintype.prod_option]
    rw [← h (X := fun a => X (some a)) (fun a => φ (some a))]
    rw [← ENNReal.tsum_mul_right]
    simp only [Fintype.prod_option]
    rw [ENNReal.tsum_prod']
    congr 1; ext y
    rw [← ENNReal.tsum_mul_left]
    rfl

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.HL.StdPlace

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

def coordLat {L : LocE F E} {r k : ℕ} (S : Frames L r k) : Submodule L.O S.V :=
  Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V))

structure Good {L : LocE F E} {r k : ℕ} (S : Frames L r k) : Prop where
  gg : S.gg = false
  Hm_int : IsIntM L S.Hm
  Hm_unit : ∃ y ∈ L.O, S.Hm.det * y = 1
  f_int : ∀ a i, S.f a i ∈ L.O
  f'_int : ∀ a i, S.f' a i ∈ L.O
  es_int : ∀ a i, S.es a i ∈ L.O
  es'_int : ∀ a i, S.es' a i ∈ L.O
  G_unit : S.G ∈ L.O ∧ ∃ y ∈ L.O, S.G * y = 1
  D_unit : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1

end GlobalTheory.HL.StdPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransferenceCoverHolds
namespace GlobalTheory

theorem transferenceCover_holds : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StMatSpec
open NumberField GlobalTheory.HL
open scoped Classical

noncomputable section

namespace GlobalTheory.HL.TraceConjugationCover

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {A : Places F E sig} {r k : ℕ}

def stMat (G : GFrames A r k) (x : G.GLV) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  if h : ∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a then h.choose else 0

theorem stMat_spec (G : GFrames A r k) (x : G.GLV)
    (h : ∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) :
    ∀ b, x (G.f' b) = ∑ a, stMat G x a b • G.f' a := by
  unfold stMat; rw [dite_eq_left h]; exact h.choose_spec

end GlobalTheory.HL.TraceConjugationCover

end
end
