module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
open NumberField IsDedekindDomain Matrix Formalism.L2.Col GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.VolBridge

variable {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {N : ℕ} (e : A ≃ Fin N)

def locHom : (Sp E N ≃ₗ[E] Sp E N) →* GL A k where
  toFun x := ⟨toLoc ι e e x.toLinearMap, toLoc ι e e (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap,
    by
      rw [← toLoc_comp_square]
      have h : x.toLinearMap ∘ₗ (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap = LinearMap.id := by
        ext v i; simp [LinearEquiv.coe_inv]
      rw [h, toLoc_id_square],
    by
      rw [← toLoc_comp_square]
      have h : (x⁻¹ : Sp E N ≃ₗ[E] Sp E N).toLinearMap ∘ₗ x.toLinearMap = LinearMap.id := by
        ext v i; simp [LinearEquiv.coe_inv]
      rw [h, toLoc_id_square]⟩
  map_one' := by
    ext1
    show toLoc ι e e (LinearEquiv.refl E (Sp E N)).toLinearMap = 1
    exact toLoc_id_square ι e
  map_mul' x y := by
    ext1
    show toLoc ι e e (x * y).toLinearMap = toLoc ι e e x.toLinearMap * toLoc ι e e y.toLinearMap
    rw [← toLoc_comp_square]
    rfl

theorem locHom_val (x : Sp E N ≃ₗ[E] Sp E N) : (locHom ι e x).val = toLoc ι e e x.toLinearMap := rfl

section Num
variable {A : Type} {N c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (N + c')) (hcc : c' = c)
  (he : ∀ i : Fin c, (e (Sum.inr i)).val = N + i.val)

include hcc he in
theorem eX_lt (a : A) : (e (Sum.inl a)).val < N := by
  by_contra h
  push Not at h
  have hc : (e (Sum.inl a)).val - N < c := by have := (e (Sum.inl a)).isLt; omega
  have h2 : e (Sum.inr ⟨_, hc⟩) = e (Sum.inl a) := Fin.ext (by rw [he]; simp; omega)
  exact absurd (e.injective h2) (by simp)

def eX : A ≃ Fin N :=
  Equiv.ofBijective (fun a => ⟨(e (Sum.inl a)).val, eX_lt e hcc he a⟩) (by
    constructor
    · intro a b hab
      have : e (Sum.inl a) = e (Sum.inl b) := Fin.ext (by simpa using congrArg Fin.val hab)
      simpa using e.injective this
    · intro m
      rcases hm : e.symm (Fin.castAdd c' m) with a | i
      · refine ⟨a, Fin.ext ?_⟩
        have := congrArg (fun z => (e z).val) hm
        simp at this
        simp [← this]
      · exfalso
        have := congrArg (fun z => (e z).val) hm
        simp [he] at this
        have := m.isLt
        omega)

theorem eX_val (a : A) : ((eX e hcc he a : Fin N) : ℕ) = (e (Sum.inl a)).val := rfl

end Num

section Ext
variable {E : Type} [Field E] {N c : ℕ}

def extX (c : ℕ) (y : Sp E N ≃ₗ[E] Sp E N) : Sp E (N + c) ≃ₗ[E] Sp E (N + c) :=
  (LinearEquiv.funCongrLeft E E finSumFinEquiv) ≪≫ₗ (LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin c) E E) ≪≫ₗ
    (y.prodCongr (LinearEquiv.refl E (Fin c → E))) ≪≫ₗ (LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin c) E E).symm ≪≫ₗ
    (LinearEquiv.funCongrLeft E E finSumFinEquiv).symm

theorem extX_castAdd (y : Sp E N ≃ₗ[E] Sp E N) (v : Sp E (N + c)) (i : Fin N) :
    extX c y v (Fin.castAdd c i) = y (fun i => v (Fin.castAdd c i)) i := by
  simp [extX, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, LinearEquiv.sumArrowLequivProdArrow, LinearEquiv.funCongrLeft, Equiv.sumArrowEquivProdArrow]
  rfl

theorem extX_natAdd (y : Sp E N ≃ₗ[E] Sp E N) (v : Sp E (N + c)) (i : Fin c) :
    extX c y v (Fin.natAdd N i) = v (Fin.natAdd N i) := by
  simp [extX, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft, LinearEquiv.sumArrowLequivProdArrow, LinearEquiv.funCongrLeft, Equiv.sumArrowEquivProdArrow]

end Ext

end GlobalTheory.VolBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPowHeckeCharUnramifiedEverywhere
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPowHeckeCharUnramifiedEverywhere
open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.Corev.UnrPow

theorem exists_pow_unrAt : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L),
    ∃ N : ℕ, 0 < N ∧ ∀ v : HeightOneSpectrum (𝓞 L), (χ ^ N).UnrAt v := by
  intro L _ _ χ
  obtain ⟨hfin, hlev⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level L χ
  have hm : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ x, IsUnitAt v x → χ.loc v x ^ m = 1 := by
    intro v
    obtain ⟨n, hn⟩ := hlev v
    obtain ⟨m, hm, hx⟩ := GlobalTheory.Mem.FinOrder.exists_pow_congr v n
    refine ⟨m, hm, fun x hu => ?_⟩
    rw [← map_pow]
    exact hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hu m) (hx x hu)
  choose m hm0 hm using hm
  refine ⟨∏ v ∈ hfin.toFinset, m v, Finset.prod_pos fun v _ => hm0 v, fun v x hx => ?_⟩
  show χ.loc v x ^ (∏ v ∈ hfin.toFinset, m v) = 1
  by_cases hv : χ.UnrAt v
  · rw [hv x hx, one_pow]
  · obtain ⟨d, hd⟩ : m v ∣ ∏ v ∈ hfin.toFinset, m v := Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.2 hv)
    rw [hd, pow_mul, hm v x hx, one_pow]

end GlobalTheory.Corev.UnrPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsPowHeckeCharUnramifiedEverywhereStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_heckeChar_unramified_everywhere : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), ∃ N : ℕ, 0 < N ∧ ∀ v : HeightOneSpectrum (𝓞 L), (χ ^ N).UnrAt v := by
  first | exact @GlobalTheory.Corev.UnrPow.exists_pow_unrAt | exact GlobalTheory.Corev.UnrPow.exists_pow_unrAt | (intros; apply GlobalTheory.Corev.UnrPow.exists_pow_unrAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLIffIsUnitDetAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLIffIsUnitDetAtPrime
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

namespace GlobalTheory.SymBridge

theorem mem_KO_iff_intAt_isUnit_det : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l τ j : ℕ) (M : ℕ → ℕ → E), (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = Matrix.of fun a b => ι (M (zPos a) (zPos b))) ↔ (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) ∧ IsUnit (redP P (Matrix.det (Matrix.of fun s s' : Fin (κ + l + j * τ) => M s.1 s'.1))) := by
  intro E k _ _ _ _ _ _ _ P q ι ϖ hC hU κ l τ j M
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.T.residues_of_completionAtPrimeWithUniformizer E k P q ι ϖ hC hU
  let e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin (κ + l + j * τ) :=
    (Equiv.sumCongr finSumFinEquiv finProdFinEquiv).trans finSumFinEquiv
  have he : ∀ a, ((e a : Fin _) : ℕ) = zPos a := by
    rintro ((i | i) | ⟨i, u⟩) <;> simp [e, zPos, finProdFinEquiv] <;> ring
  let A : Matrix (Fin (κ + l + j * τ)) (Fin (κ + l + j * τ)) E := Matrix.of fun s s' => M s.1 s'.1
  let T : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k :=
    Matrix.of fun a b => ι (M (zPos a) (zPos b))
  have hT : T = (A.map ι).submatrix e e := by
    ext a b; simp [T, A, he]
  have hdet : T.det = ι A.det := by
    rw [hT, Matrix.det_submatrix_equiv_self, RingHom.map_det]; rfl
  have hint : ∀ x : k, valuation k x = 1 → x ∈ 𝒪[k] := fun x hx =>
    (Valuation.mem_integer_iff (valuation k) x).2 hx.le
  change (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = T) ↔ _
  constructor
  · rintro ⟨g, hg, hgv⟩
    have hI := intM_of_mem_KO hg
    rw [hgv] at hI
    refine ⟨fun p p' hp hp' => ?_, ?_⟩
    · have h := hI (e.symm ⟨p, hp⟩) (e.symm ⟨p', hp'⟩)
      simp only [T, Matrix.of_apply] at h
      rw [← he, ← he, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      exact (hC.int _).1 h
    · have hv := valuation_det_of_mem_KO hg
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, hdet] at hv
      exact (h3 _ ((hC.int _).1 (hint _ hv))).1 hv
  · rintro ⟨hent, hunit⟩
    have hTint : ∀ a b, T a b ∈ 𝒪[k] := fun a b =>
      (hC.int _).2 (hent _ _ (he a ▸ (e a).2) (he b ▸ (e b).2))
    let B : Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) j) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) 𝒪[k] :=
      Matrix.of fun a b => ⟨T a b, hTint a b⟩
    have hB : B.map (algebraMap 𝒪[k] k) = T := by ext a b; rfl
    have hBdet : algebraMap 𝒪[k] k B.det = ι A.det := by
      rw [RingHom.map_det]; change (B.map (algebraMap 𝒪[k] k)).det = _; rw [hB, hdet]
    have hAint : IntAt P A.det := (hC.int _).1 (hBdet ▸ (B.det).2)
    have hv : valuation k (ι A.det) = 1 := (h3 _ hAint).2 hunit
    have hBu : IsUnit B.det :=
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 (by rw [hBdet]; exact hv)
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (B.nonsingInvUnit hBu), ⟨_, rfl⟩, ?_⟩
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply]
    rfl

end GlobalTheory.SymBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLIffIsUnitDetAtPrimeStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralGL_iff_isUnit_det_at_prime : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (κ l τ j : ℕ) (M : ℕ → ℕ → E), (∃ g ∈ KO k (Ix (Fin κ ⊕ Fin l) (Fin τ) j), g.val = Matrix.of fun a b => ι (M (zPos a) (zPos b))) ↔ (∀ p p', p < κ + l + j * τ → p' < κ + l + j * τ → IntAt P (M p p')) ∧ IsUnit (redP P (Matrix.det (Matrix.of fun s s' : Fin (κ + l + j * τ) => M s.1 s'.1))) := by
  first | exact @GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det | exact GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det | (intros; apply GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det <;> assumption)
end
end
