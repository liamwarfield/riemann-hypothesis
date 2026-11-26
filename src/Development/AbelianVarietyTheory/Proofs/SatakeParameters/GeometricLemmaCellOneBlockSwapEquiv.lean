module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingParIndOfJacquetNontrivial
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.OneBlockCell

def valEquiv {β : Type} {n : β → ℕ} {t : ℕ} (a₀ : β) (ha₀ : n a₀ = t) (h0 : ∀ j, j ≠ a₀ → n j = 0) :
    (Σ j, Fin (n j)) ≃ Fin t where
  toFun p := ⟨p.2.val, by
    by_cases hp : p.1 = a₀
    · have h1 := p.2.2
      have h2 : n p.1 = t := hp ▸ ha₀
      omega
    · have h1 := p.2.2
      have h2 := h0 _ hp
      omega⟩
  invFun x := ⟨a₀, ⟨x.val, by have := x.2; omega⟩⟩
  left_inv p := by
    obtain ⟨a, s⟩ := p
    by_cases ha : a = a₀
    · subst ha
      rfl
    · have h1 := s.2
      have h2 := h0 _ ha
      omega
  right_inv x := rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deltaHalf_eq_one_of_single {β : Type} [Fintype β] [LinearOrder β] {n : β → ℕ} (a₀ : β)
    (h0 : ∀ j, j ≠ a₀ → n j = 0) (g : Levi k (fun j => Fin (n j))) :
    deltaHalf k (fun j => Fin (n j)) g = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  by_cases ha : a = a₀
  · subst ha
    have hs : ∀ s : Finset β, a ∉ s → ∑ b ∈ s, (Fintype.card (Fin (n b)) : ℤ) = 0 := fun s hs =>
      Finset.sum_eq_zero fun b hb => by
        have hba : b ≠ a := fun e => hs (e ▸ hb)
        simp [h0 b hba]
    have hm : modExp (fun j => Fin (n j)) a = 0 := by
      unfold modExp
      rw [hs _ (by simp), hs _ (by simp), sub_zero]
    rw [hm]
    simp
  · haveI : IsEmpty (Fin (n a)) := ⟨fun x => absurd x.2 (by have := x.2; have := h0 a ha; omega)⟩
    have : Matrix.GeneralLinearGroup.det (g a) = 1 := by
      ext
      simp [Matrix.det_isEmpty]
    rw [this, map_one]

theorem mem_parab_of_single {R : Type} [CommRing R] {β : Type} [LinearOrder β] {n : β → ℕ} {t : ℕ}
    (e : (Σ j, Fin (n j)) ≃ Fin t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0) (x : GL (Fin t) R) :
    x ∈ parab R e := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  by_cases ha : a = a₀
  · have hb : b ≠ a₀ := fun e => by rw [e, ha] at hab; exact lt_irrefl _ hab
    exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

theorem eq_one_of_mem_unipRad_single {R : Type} [CommRing R] {β : Type} [Fintype β] [LinearOrder β]
    {n : β → ℕ} {t : ℕ} (e : (Σ j, Fin (n j)) ≃ Fin t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0)
    {g : GL (Fin t) R} (hg : g ∈ unipRad R e) : g = 1 := by
  obtain ⟨-, h2⟩ := mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases ha : a = a₀
  · by_cases hb : b = a₀
    · obtain rfl : b = a := hb.trans ha.symm
      rw [h2 b i j]
      simp [Matrix.one_apply]
    · exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

open scoped TensorProduct

theorem reindex_piTensor {d : Fin 2 → ℕ} (σ : ∀ i, Irr k (d i)) (γ : ∀ i, GL (Fin (d i)) k)
    (p : ∀ j, GL (Fin (d (Equiv.swap 0 1 j))) k) (h : ∀ j, γ (Equiv.swap 0 1 j) = p j)
    (y : ⨂[ℂ] i, (σ i).V) :
    PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1) ((piTensor fun i => (σ i).π) γ y) =
      (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p
        (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1) y) := by
  suffices H : (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)).toLinearMap ∘ₗ
      (piTensor fun i => (σ i).π) γ = (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p ∘ₗ
      (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)).toLinearMap from
    LinearMap.congr_fun H y
  refine PiTensorProduct.ext (MultilinearMap.ext fun z => ?_)
  have e1 : (((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p ∘ₗ
      (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)).toLinearMap).compMultilinearMap
        (PiTensorProduct.tprod ℂ)) z = (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p
          (PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1) (PiTensorProduct.tprod ℂ z)) := rfl
  have e2 := PiTensorProduct.reindex_tprod (R := ℂ) (s := fun i => (σ i).V) (Equiv.swap 0 1) z
  have e3 := piTensor_tprod (fun j => (σ (Equiv.swap 0 1 j)).π) p (fun j => z (Equiv.swap 0 1 j))
  refine Eq.trans ?_ e1.symm
  refine Eq.trans ?_ (congrArg (fun w => (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p w) e2).symm
  refine Eq.trans ?_ e3.symm
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    piTensor_tprod, PiTensorProduct.reindex_tprod]
  refine congrArg (PiTensorProduct.tprod ℂ (s := fun j => (σ (Equiv.swap 0 1 j)).V)) (funext fun j => ?_)
  show (σ (Equiv.swap 0 1 j)).π (γ (Equiv.swap 0 1 j)) (z (Equiv.swap 0 1 j)) = _
  rw [h j]

theorem cellFunctor_swap_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), d 1 = 1 →
    ∀ (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j)))), b.1 1 0 = 1 →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))),
      Nonempty ((cellFunctor f g (piTensor fun i => (σ i).π)).Equiv
        (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)) := by
  intro k _ _ _ _ d σ hd b hb
  have r0 := b.2.1 0
  have r1 := b.2.1 1
  have c0 := b.2.2 0
  have c1 := b.2.2 1
  simp only [Fin.sum_univ_two, Fintype.card_fin, Equiv.swap_apply_left, Equiv.swap_apply_right] at r0 r1 c0 c1
  have h00 : b.1 0 0 = 0 := by omega
  have h11 : b.1 1 1 = 0 := by omega
  have hrz : ∀ i j, j ≠ Equiv.swap 0 1 i → b.1 i j = 0 := by
    intro i j hj
    fin_cases i <;> fin_cases j <;> simp_all
  have hcz : ∀ j i, i ≠ Equiv.swap 0 1 j → b.1 i j = 0 := by
    intro j i hi
    fin_cases i <;> fin_cases j <;> simp_all
  have hrf : ∀ i, b.1 i (Equiv.swap 0 1 i) = d i := by
    intro i
    fin_cases i <;> simp <;> omega
  have hcf : ∀ j, b.1 (Equiv.swap 0 1 j) j = d (Equiv.swap 0 1 j) := by
    intro j
    fin_cases j <;> simp <;> omega

  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i) := fun i =>
    valEquiv (Equiv.swap 0 1 i) (hrf i) (fun j hj => hrz i j hj)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j)) := fun j =>
    valEquiv (Equiv.swap 0 1 j) (hcf j) (fun i hi => hcz j i hi)
  refine ⟨f, g, ?_⟩
  have hbot : twKer (piTensor fun i => (σ i).π) (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k (fun i => Fin (d i))) = 1 := funext fun i =>
      eq_one_of_mem_unipRad_single (f i) (Equiv.swap 0 1 i) (fun j hj => hrz i j hj) (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      deltaHalf_eq_one_of_single (Equiv.swap 0 1 i) (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      deltaHalf_eq_one_of_single (Equiv.swap 0 1 j) (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    mem_parab_of_single (g j) (Equiv.swap 0 1 j) (fun i hi => hcz j i hi) (x j)
  have hγ : ∀ (p : relParab k g) j,
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) (Equiv.swap 0 1 j) =
        (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) j := by
    intro p j
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f (Equiv.swap 0 1 j)).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f (Equiv.swap 0 1 j)).surjective y
    have ha : a = j := by
      by_contra hne
      have h1 := hrz (Equiv.swap 0 1 j) a (by rwa [Equiv.swap_apply_self])
      have h2 := t.2
      omega
    have ha' : a' = j := by
      by_contra hne
      have h1 := hrz (Equiv.swap 0 1 j) a' (by rwa [Equiv.swap_apply_self])
      have h2 := s.2
      omega
    subst ha
    subst ha'
    rw [leviEmb_apply_same]
    rfl

  have hsm : IsSmooth (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) :=
    isSmooth_piTensor fun j => (σ (Equiv.swap 0 1 j)).smooth
  let R := PiTensorProduct.reindex ℂ (fun i => (σ i).V) (Equiv.swap 0 1)
  let Ψ : (⨂[ℂ] j, (σ (Equiv.swap 0 1 j)).V) ≃ₗ[ℂ]
      Jacquet (piTensor fun i => (σ i).π) (relUnip k f) :=
    R.symm.trans (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk (R.symm u) := fun u => rfl
  let τ := (GlobalTheory.SmGL.twist ((relJac f (piTensor fun i => (σ i).π)).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) =
        Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ]
    simp only [inv_one, Units.val_one, one_smul]
    congr 1
    apply R.injective
    rw [reindex_piTensor σ _ (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) (hγ p)]
    exact (congrArg (fun w => (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)
      (p : Levi k (fun j => Fin (d (Equiv.swap 0 1 j)))) w) (R.apply_symm_apply u)).trans
        (R.apply_symm_apply _).symm
  let F : (piTensor fun j => (σ (Equiv.swap 0 1 j)).π).IntertwiningMap
      (cellFunctor f g (piTensor fun i => (σ i).π)) :=
    { toFun := fun u => ⟨⟨fun x => Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x u), fun p x => by
          show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : (piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (y * x) u) =
            Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x
            ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) h u)) =
          Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) 1 u) =
        Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) 1 w) := congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ ((piTensor fun j => (σ (Equiv.swap 0 1 j)).π) x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

end GlobalTheory.OneBlockCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquivStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricLemmaCell_one_block_swap_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : Fin 2 → ℕ) (σ : ∀ i, Irr k (d i)), d 1 = 1 →
    ∀ (b : SizeMatrix (fun i : Fin 2 => Fin (d i)) (fun j : Fin 2 => Fin (d (Equiv.swap 0 1 j)))), b.1 1 0 = 1 →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (d (Equiv.swap 0 1 j))),
      Nonempty ((cellFunctor f g (piTensor fun i => (σ i).π)).Equiv
        (piTensor fun j => (σ (Equiv.swap 0 1 j)).π)) := by
  first | exact @GlobalTheory.OneBlockCell.cellFunctor_swap_equiv | exact GlobalTheory.OneBlockCell.cellFunctor_swap_equiv | (intros; apply GlobalTheory.OneBlockCell.cellFunctor_swap_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WdConjAbove
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ConjGal
open Formalism.BasicNotions.Loc GlobalTheory.Pst

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces B)

theorem wdPst_equiv {L : FinExt l} {m : ℕ} {ρ₁ ρ₂ : Representation ↥L.1 ↥(GK B.Kw) (Fin m → ↥L.1)}
    (e : (Fin m → ↥L.1) ≃ₗ[↥L.1] (Fin m → ↥L.1)) (he : ∀ g x, e (ρ₁ g x) = ρ₂ g (e x))
    (h₁ : IsPst P ρ₁) (h₂ : IsPst P ρ₂) :
    wdPst P ι B h hj ρ₁ = wdPst P ι B h hj ρ₂ := by
  haveI := h₁.finite
  haveI := h₂.finite
  let f : (Fin m → ↥L.1) →ₗ[ℚ_[l]] (Fin m → ↥L.1) := (e : (Fin m → ↥L.1) →ₗ[↥L.1] (Fin m → ↥L.1)).restrictScalars ℚ_[l]
  have hf : ∀ g v, f (ρ₁ g v) = ρ₂ g (f v) := he
  let π : Fin 1 → (Fin m → ↥L.1) →ₗ[ℚ_[l]] (Fin m → ↥L.1) :=
    fun _ => (e.symm : (Fin m → ↥L.1) →ₗ[↥L.1] (Fin m → ↥L.1)).restrictScalars ℚ_[l]
  have hπ : ∀ j g v, π j (ρ₂ g v) = ρ₁ g (π j v) := by
    intro j g v
    apply e.injective
    change e (e.symm (ρ₂ g v)) = e (ρ₁ g (e.symm v))
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hsum : ∀ v, ∑ j, (fun _ : Fin 1 => (1 : ↥L.1)) j • f (π j v) = v := by
    intro v
    change ∑ _j : Fin 1, (1 : ↥L.1) • e (e.symm v) = v
    simp
  refine BridgeParam.wdPst_eq_of_map P ι B B h hj hj h₁ h₂ rfl (RingHom.id _) (fun _ => rfl)
    (EnlargeCoeff.dQ P hf)
    (fun a x => Subtype.ext (EnlargeCoeff.tensQ_smul P (RingHom.id _) (fun a v => e.map_smul a v) a x.1))
    (EnlargeCoeff.dQ_mulD P hf) (EnlargeCoeff.dQ_weilD P B h hf) 1 one_ne_zero (fun x => ?_) fun x => ?_
  · have e1 : EnlargeCoeff.dQ P hf (monD P ρ₁ x) = monD P ρ₂ (EnlargeCoeff.dQ P hf x) :=
      Subtype.ext (EnlargeCoeff.tensQ_onB P _ _ x.1)
    exact e1.trans (Subtype.ext (one_smul ↥L.1 (monD P ρ₂ (EnlargeCoeff.dQ P hf x)).1).symm)
  · exact BridgeParam.mem_span_dQ P ι hf (fun _ => 1) π hπ hsum x

theorem wdAt_conj {a : ℕ} (r r' : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (M : GL (Fin a) (Om l))
    (hc : ∀ g, r' g = M * r g * M⁻¹) (hr : IsPstAt P B r) (hr' : IsPstAt P B r') :
    wdAt P ι B h hj r' = wdAt P ι B h hj r := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj hr
  obtain ⟨L₃, r₃, hm₃, hV₃, e₃⟩ := wdAt_of_isPstAt ι B h hj hr'
  have hA : L₁.1 ≤ (supExt L₁ L₃).1 := le_sup_left
  have hB : L₃.1 ≤ (supExt L₁ L₃).1 := le_sup_right
  have hm₁' : IsModel B r (supExt L₁ L₃) (mapRep (IntermediateField.inclusion hA).toRingHom r₁) :=
    ⟨hm₁.1.trans hA, by rw [← hm₁.2]; ext g i j; rfl⟩
  obtain ⟨L₂, hL, r₂, hm₂, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model M hc hm₁'
  have hC : L₃.1 ≤ L₂.1 := hB.trans hL
  have hr₃ : mapRep (IntermediateField.inclusion hC).toRingHom r₃ = r₂ :=
    IsModel.unique B r' ⟨hm₃.1.trans hC, by rw [← hm₃.2]; ext g i j; rfl⟩ hm₂
  have p₁ := GlobalTheory.PstExt.isPst_enlarge P B hA r₁ hV₁
  have p₁' := GlobalTheory.PstExt.isPst_enlarge P B hL _ p₁
  have p₃ := GlobalTheory.PstExt.isPst_enlarge P B hC r₃ hV₃
  rw [e₁, e₃, BridgeParam.wdPst_enlarge P ι B h hj hC r₃ hV₃, hr₃,
    BridgeParam.wdPst_enlarge P ι B h hj hA r₁ hV₁, BridgeParam.wdPst_enlarge P ι B h hj hL _ p₁]
  rw [hr₃] at p₃
  exact (wdPst_equiv P ι B h hj e he p₁' p₃).symm

end Local
end GlobalTheory.ConjGal

namespace GlobalTheory.ConjGal
open Formalism.BasicNotions.Loc

section W
variable (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

theorem cont_conj {a : ℕ} (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (Pm : GL (Fin a) (Qbar l))
    (hc : ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm)
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)))) :
    Continuous (fun g => ((ρ' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) := by
  have e : (fun g => ((ρ' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) = fun g =>
      ((Pm⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) *
        ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) * (Pm : Matrix (Fin a) (Fin a) (Qbar l)) := by
    funext g
    rw [hc]
    rfl
  rw [e]
  exact (continuous_const.matrix_mul hρ).matrix_mul continuous_const

theorem dR_conj {a : ℕ} (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (Pm : GL (Fin a) (Qbar l))
    (hc : ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm)
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) :
    W.IsdRW l ι ρ' w ↔ W.IsdRW l ι ρ w := by
  have hρ' := cont_conj D l ρ ρ' Pm hc hρ
  obtain ⟨LL, Bw, hj, -⟩ := W.above l ι ρ w hw
  rw [GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D T W l ι w hw _ Bw hj a ρ' hρ',
    GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D T W l ι w hw _ Bw hj a ρ hρ]
  constructor
  · refine (GlobalTheory.ConjLocal.local_conj l (D.loc l) D.host.E D.nd.Om _ _ Bw a _ _ Pm fun g => ?_).1
    change ρ g = Pm * ρ' g * Pm⁻¹
    rw [hc]
    group
  · refine (GlobalTheory.ConjLocal.local_conj l (D.loc l) D.host.E D.nd.Om _ _ Bw a _ _ Pm⁻¹ fun g => ?_).1
    change ρ' g = Pm⁻¹ * ρ g * Pm⁻¹⁻¹
    rw [hc, inv_inv]

theorem wd_conj_away {a : ℕ} (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (Pm : GL (Fin a) (Qbar l))
    (hc : ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm) (w : PlE D.host) (hw : w ∉ placesOver D.host.E l) :
    W.wdOf l ι ρ' w = W.wdOf l ι ρ w := by
  apply (T.e w).injective
  rw [W.away l ι ρ' w hw, W.away l ι ρ w hw]
  exact (GlobalTheory.WeilDeligne.wdOf_eq_of_conj (r := ρ) (ι := ι) hw Pm⁻¹ fun g => by rw [hc]; group).symm

theorem pst_of_dR (hB : GlobalTheory.Published.DeRhamPotSemistable) {m : ℕ} (r : G D.host.E D.nd.Om →* GL (Fin m) (Qbar l))
    (hr : Continuous (fun g => ((r g : GL (Fin m) (Qbar l)) : Matrix (Fin m) (Fin m) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) (hd : W.IsdRW l ι r w) {LL : FinExt l}
    (B : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(OL LL)) (hj : GlobalTheory.Pst.Induces B) :
    GlobalTheory.Pst.IsPstAt (D.loc l) B (GlobalTheory.Pst.resDec D.nd.plOm.1 r w) :=
  hB.isPstAt (D.locT l) B _ (hr.comp continuous_subtype_val)
    ((GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D T W l ι w hw _ B hj m r hr).1 hd)

theorem wd_conj_above (hB : GlobalTheory.Published.DeRhamPotSemistable) {a : ℕ} (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (Pm : GL (Fin a) (Qbar l)) (hc : ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm)
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) (d : W.IsdRW l ι ρ w) :
    W.wdOf l ι ρ' w = W.wdOf l ι ρ w := by
  have hρ' := cont_conj D l ρ ρ' Pm hc hρ
  have d' := (dR_conj D T W l ι ρ ρ' Pm hc hρ w hw).2 d
  obtain ⟨p_power_smul_sub_sum, B1, j1, E1⟩ := W.above l ι ρ w hw
  obtain ⟨logJacobianTwoPoints, B2, j2, E2⟩ := W.above l ι ρ' w hw
  have tie : Nonempty (LocTied l (D.loc l) (D.locA l)) := ⟨D.locT l⟩
  apply (T.e w).injective
  rw [E1, E2]
  have p22 := pst_of_dR D T W l ι hB ρ' hρ' w hw d' B2 j2
  have p21 := pst_of_dR D T W l ι hB ρ' hρ' w hw d' B1 j1
  have p11 := pst_of_dR D T W l ι hB ρ hρ w hw d B1 j1
  rw [GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge l (D.loc l) (D.locA l) tie ι D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _
    B2 B1 (D.nd.plOm.2 w) j2 j1 a _ (hρ'.comp continuous_subtype_val) p22 p21]
  exact wdAt_conj (D.loc l) ι B1 (D.nd.plOm.2 w) j1 _ _ Pm⁻¹ (fun g => by
    change ρ' g = Pm⁻¹ * ρ g * Pm⁻¹⁻¹
    rw [hc, inv_inv]) p11 p21

theorem jumps_conj {a : ℕ} (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (Pm : GL (Fin a) (Qbar l))
    (hc : ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm)
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (τ : D.host.E →+* Qbar l)
    (hτ : ∀ w : PlE D.host, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → W.IsdRW l ι ρ w) :
    W.jumpsW l ι ρ' τ = W.jumpsW l ι ρ τ := by
  have hρ' := cont_conj D l ρ ρ' Pm hc hρ
  obtain ⟨w, hw, hτw⟩ := GlobalTheory.PlaceOfEmb.exists_place_of_emb D l τ
  have d₁ := hτ w hτw
  have d₂ := (dR_conj D T W l ι ρ ρ' Pm hc hρ w hw).2 d₁
  obtain ⟨LL, Bw, hj, -⟩ := W.above l ι ρ w hw
  obtain ⟨L₁, hL₁, ρ₁, c₁, e₁⟩ := GlobalTheory.CompactRepField.exists_continuous_model D l a ρ hρ Bw.LL
  obtain ⟨L₂, hL₂, ρ₂, c₂, e₂⟩ := GlobalTheory.CompactRepField.exists_continuous_model D l a ρ' hρ' Bw.LL
  obtain ⟨τ₁, hτ₁⟩ := GlobalTheory.EmbExt.main D l w _ Bw hj τ hτw L₁ hL₁
  obtain ⟨τ₂, hτ₂⟩ := GlobalTheory.EmbExt.main D l w _ Bw hj τ hτw L₂ hL₂
  obtain ⟨-, H⟩ := W.loc l ι w hw _ Bw hj ((algebraMap ↥Bw.LL.1 (Om l)).comp Bw.toLL) (fun _ => rfl)
  obtain ⟨-, dd₁, -, J₁⟩ := H L₁ hL₁ a ρ₁ c₁
  obtain ⟨-, dd₂, -, J₂⟩ := H L₂ hL₂ a ρ₂ c₂
  rw [e₁] at dd₁ J₁
  rw [e₂] at dd₂ J₂
  have hm₁ : GlobalTheory.Pst.IsModel Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ w) L₁
      (ρ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL₁, by rw [← e₁]; rfl⟩
  have hm₂ : GlobalTheory.Pst.IsModel Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ' w) L₂
      (ρ₂.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL₂, by rw [← e₂]; rfl⟩
  have k₁ := (J₁ τ τ₁ hτ₁).2 (dd₁.1 d₁)
  have k₂ := (J₂ τ τ₂ hτ₂).2 (dd₂.1 d₂)
  have J : GlobalTheory.Pst.IsJumpsAt (D.loc l) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ w) τ (W.jumpsW l ι ρ τ) :=
    ⟨L₁, _, hm₁, dd₁.1 d₁, τ₁, hτ₁, k₁⟩
  have J' := (GlobalTheory.ConjLocal.local_conj l (D.loc l) D.host.E D.nd.Om _ _ Bw a (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ w)
    (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ' w) Pm⁻¹ (fun g => by
    change ρ' g = Pm⁻¹ * ρ g * Pm⁻¹⁻¹
    rw [hc, inv_inv])).2.2.2 τ _ J
  ext c
  have k₃ := GlobalTheory.Pst.IsJumpsAt.count_eq (D.loc l) hm₂ hτ₂ J' c
  have k₄ := k₂ c
  exact_mod_cast k₄.trans k₃.symm

end W

end GlobalTheory.ConjGal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBridge
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.AboveLRes

section Res

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω]
  [Algebra K L] [IsScalarTower K L Ω]

def decRes (A : ValuationSubring Ω) : ↥(Dec (F := L) A) →* ↥(Dec (F := K) A) where
  toFun g := ⟨AlgEquiv.restrictScalars K (g : G L Ω), by
    have hg := mem_Dec.mp g.2
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    conv_rhs => rw [← hg, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl

end Res

end GlobalTheory.AboveLRes

noncomputable section

namespace GlobalTheory.AboveLRes

section Bridge

variable {l : ℕ} [Fact l.Prime] {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem exists_bridge (Bw : LocBridge l K Ω (Dec (F := K) A) O) (hj : Induces Bw) (S : FinExt l) :
    ∃ (LL' : FinExt l) (Bw' : LocBridge l L Ω (Dec (F := L) A) ↥(OL LL')), Bw'.j = Bw.j ∧ S.1 ≤ Bw'.LL.1 ∧ Bw.Kw.1 ≤ Bw'.Kw.1 := by
  let K' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : L => Bw.j (algebraMap L Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (Bw.j.comp (algebraMap L Ω))⟩
  have := K'.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := L) hj K' rfl
  refine ⟨_, {
    Kw := K'
    j := Bw.j
    j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
    j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (Bw.j.comp (algebraMap L Ω))
    e := e
    e_cont := he
    e_symm_cont := he'
    e_comm := hec
    LL := supExt S ⟨IntermediateField.normalClosure ℚ_[l] K'.1 (PadicAlgCl l), inferInstance⟩
    LL_split := fun τ x => (le_sup_right : _ ≤ (supExt S ⟨IntermediateField.normalClosure ℚ_[l] K'.1 (PadicAlgCl l),
      inferInstance⟩).1) (AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩)
    eO := RingEquiv.refl _
    eO_alg := fun _ => rfl
    eO_cont := continuous_id
    eO_symm_cont := continuous_id }, rfl, le_sup_left, ?_⟩
  show Bw.Kw.1 ≤ K'.1
  rw [BridgeInd.kw_eq_adjoin Bw, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  refine IntermediateField.subset_adjoin _ _ ⟨algebraMap K L x, ?_⟩
  show Bw.j (algebraMap L Ω (algebraMap K L x)) = Bw.j (algebraMap K Ω x)
  rw [← IsScalarTower.algebraMap_apply]

variable {O' : Type} [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
  (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O')
  (hjj : Bw'.j = Bw.j) (hle : Bw.Kw.1 ≤ Bw'.Kw.1)
include hjj hle

theorem decRes_e_symm (g' : ↥(GK Bw'.Kw)) :
    decRes (K := K) A (Bw'.e.symm g') = Bw.e.symm ⟨g', GK_le hle g'.2⟩ := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply Bw.j.injective
  have h1 := Bw'.e_comm (Bw'.e.symm g') x
  have h2 := Bw.e_comm (Bw.e.symm ⟨g', GK_le hle g'.2⟩) x
  rw [MulEquiv.apply_symm_apply] at h1 h2
  rw [hjj] at h1
  exact h1.symm.trans h2

theorem repE_decRes (T : FinExt l) {m : ℕ} (t : ↥(Dec (F := K) A) →* GL (Fin m) ↥T.1) :
    Bw'.repE T (t.comp (decRes A)) = GlobalTheory.Pst.resTo (Bw.repE T t) hle := by
  ext g' v i
  simp only [LocBridge.repE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, GlobalTheory.Pst.resTo]
  rw [decRes_e_symm Bw Bw' hjj hle]
  rfl

variable {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v')

theorem weilToGK_eq (σ : Weil h) (σ' : Weil h') (hσ : ∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) :
    (weilToGK Bw' h' σ' : GQ l) = (weilToGK Bw h σ : GQ l) := by
  have e1 := decRes_e_symm Bw Bw' hjj hle (weilToGK Bw' h' σ')
  have e2 : decRes (K := K) A (Bw'.e.symm (weilToGK Bw' h' σ')) = Subgroup.inclusion (Weil_le_Dec h) σ := by
    rw [weilToGK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact Subtype.ext (AlgEquiv.ext fun z => (hσ z).symm)
  rw [e2, MulEquiv.eq_symm_apply] at e1
  exact (congrArg Subtype.val e1).symm

end Bridge

end GlobalTheory.AboveLRes
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SmGL.Relabel

section General

variable {F G H V : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]

def indPull {P : Subgroup G} {Q : Subgroup H}
    {σ : Representation F P V} {τ : Representation F Q V} (φ : H →* G) (hφ : Continuous φ)
    (h : ∀ q : Q, ∃ p : P, (p : G) = φ q ∧ σ p = τ q) :
    smoothPart (ind P σ) →ₗ[F] smoothPart (ind Q τ) where
  toFun f := ⟨⟨fun g => f.1.1 (φ g), fun q g => by
      obtain ⟨p, hp, hs⟩ := h q
      show f.1.1 (φ (q * g)) = τ q (f.1.1 (φ g))
      rw [map_mul, ← hp, f.1.2 p, hs]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      (IsOpen.mem_nhds (IsOpen.preimage hφ f.2) (by simp)) fun g hg => by
        have hg' : ind P σ (φ g) f.1 = f.1 := hg
        apply Subtype.ext
        funext x
        have := congrFun (congrArg Subtype.val hg') (φ x)
        show f.1.1 (φ (x * g)) = f.1.1 (φ x)
        rw [map_mul]
        exact this)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem smInd_equiv_comp {P : Subgroup G} {Q : Subgroup H}
    {σ : Representation F P V} {τ : Representation F Q V} (φ : G →* H) (φ' : H →* G)
    (hφ : Continuous φ) (hφ' : Continuous φ') (h1 : ∀ x, φ (φ' x) = x) (h2 : ∀ x, φ' (φ x) = x)
    (h : ∀ q : Q, ∃ p : P, (p : G) = φ' q ∧ σ p = τ q)
    (h' : ∀ p : P, ∃ q : Q, (q : H) = φ p ∧ τ q = σ p) :
    Nonempty ((smInd P σ).Equiv ((smInd Q τ).comp φ)) := by
  refine ⟨.mk (LinearEquiv.ofLinear (indPull φ' hφ' h) (indPull φ hφ h') ?_ ?_) fun g => ?_⟩
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (φ (φ' x)) = f.1.1 x
    rw [h1]
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (φ' (φ x)) = f.1.1 x
    rw [h2]
  · refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (φ' x * g) = f.1.1 (φ' (x * φ g))
    rw [map_mul, h2]

end General

section Blocks

open GlobalTheory.EmptyFirstBlock

variable {R : Type} [CommRing R] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem continuous_reindexGL [TopologicalSpace R] (ψ : n ≃ n') :
    Continuous (reindexGL (R := R) ψ) :=
  Continuous.units_map _ (continuous_pi fun i => continuous_pi fun j =>
    continuous_apply_apply (ψ.symm i) (ψ.symm j))

theorem reindexGL_symm_reindexGL (ψ : n ≃ n') (g : GL n R) :
    reindexGL ψ.symm (reindexGL ψ g) = g :=
  Units.ext (Matrix.ext fun i j => by simp [val_reindexGL])

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

theorem exists_parab_reindexGL {e : (Σ a, m a) ≃ n} {e' : (Σ a, m a) ≃ n'} (ψ : n ≃ n')
    (h : ∀ x, ψ.symm (e' x) = e x) (p : parab R e) :
    ∃ q : parab R e', (q : GL n' R) = reindexGL ψ p ∧ leviProj R e' q = leviProj R e p := by
  refine ⟨⟨reindexGL ψ p, mem_parab_iff.2 fun a b i j hab => ?_⟩, rfl, ?_⟩
  · rw [val_reindexGL, h, h]
    exact mem_parab_iff.1 p.2 a b i j hab
  · funext a
    ext i j
    show (reindexGL ψ (p : GL n R) : Matrix n' n' R) (e' ⟨a, i⟩) (e' ⟨a, j⟩) =
      ((p : GL n R) : Matrix n n R) (e ⟨a, i⟩) (e ⟨a, j⟩)
    rw [val_reindexGL, h, h]

end Blocks

theorem parInd_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (e : (Σ a, m a) ≃ n) (ψ : n ≃ n')
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    Nonempty ((parInd e ρ).Equiv ((parInd (e.trans ψ) ρ).comp (GlobalTheory.EmptyFirstBlock.reindexGL (R := k) ψ))) := by
  intro k _ _ _ _ α _ _ m _ _ n n' _ _ _ _ e ψ W _ _ ρ
  refine smInd_equiv_comp _ (GlobalTheory.EmptyFirstBlock.reindexGL (R := k) ψ.symm)
    (continuous_reindexGL ψ) (continuous_reindexGL ψ.symm)
    (reindexGL_symm_reindexGL ψ.symm) (reindexGL_symm_reindexGL ψ) (fun q => ?_) (fun p => ?_)
  · obtain ⟨p, hp, hl⟩ := exists_parab_reindexGL (e' := e) ψ.symm (fun x => rfl) q
    exact ⟨p, hp, congrArg (twist ρ (deltaHalf k m)) hl⟩
  · obtain ⟨q, hq, hl⟩ := exists_parab_reindexGL (e' := e.trans ψ) ψ (fun x => by simp) p
    exact ⟨q, hq, congrArg (twist ρ (deltaHalf k m)) hl⟩

end GlobalTheory.SmGL.Relabel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquivStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedParabolicInduction_reindex_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (e : (Σ a, m a) ≃ n) (ψ : n ≃ n')
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    Nonempty ((parInd e ρ).Equiv ((parInd (e.trans ψ) ρ).comp (GlobalTheory.EmptyFirstBlock.reindexGL (R := k) ψ))) := by
  first | exact @GlobalTheory.SmGL.Relabel.parInd_reindex | exact GlobalTheory.SmGL.Relabel.parInd_reindex | (intros; apply GlobalTheory.SmGL.Relabel.parInd_reindex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight
set_option synthInstance.maxHeartbeats 200000
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section

open Polynomial Module

namespace GlobalTheory.Pst.TwistLetters

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {L : FinExt l}
  (V : Type) [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

def smulEnd : (Fin 1 → ↥L.1) →ₗ[ℚ_[l]] End ℚ_[l] V where
  toFun v' := ((LinearMap.lsmul ↥L.1 V) (v' 0)).restrictScalars ℚ_[l]
  map_add' x y := by ext v; simp [add_smul]
  map_smul' c x := by ext v; simp [smul_assoc]

def mulB : ((Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) →ₗ[ℚ_[l]] End ℚ_[l] (V ⊗[ℚ_[l]] Bst P) :=
  TensorProduct.lift ((TensorProduct.mapBilinear (RingHom.id ℚ_[l]) V (Bst P) V (Bst P)).compl₁₂ (smulEnd V)
    (LinearMap.mul ℚ_[l] (Bst P)))

@[simp] theorem mulB_tmul (v' : Fin 1 → ↥L.1) (b' : Bst P) (v : V) (b : Bst P) :
    mulB (L := L) P V (v' ⊗ₜ b') (v ⊗ₜ b) = (v' 0 • v) ⊗ₜ (b' * b) := by
  simp [mulB, smulEnd]

variable {P V}

theorem mulB_smul (a : ↥L.1) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB (L := L) P V y (a • x) = a • mulB (L := L) P V y x := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [TensorProduct.smul_tmul', mulB_tmul, mulB_tmul, TensorProduct.smul_tmul', smul_smul, smul_smul, mul_comm]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_smul_left (a : ↥L.1) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB (L := L) P V (a • y) x = a • mulB (L := L) P V y x := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [TensorProduct.smul_tmul', mulB_tmul, mulB_tmul, TensorProduct.smul_tmul', Pi.smul_apply, smul_eq_mul, mul_smul]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_mulV (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB (L := L) P V y (mulV P ↥L.1 V c x) = mulV P ↥L.1 V c (mulB (L := L) P V y x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulV_tmul, mulB_tmul, mulB_tmul, mulV_tmul, mul_left_comm]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulV_mulB (c : ↥(MaximalUnramifiedExtension l)) (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    mulB (L := L) P V (mulV P ↥L.1 (Fin 1 → ↥L.1) c y) x = mulV P ↥L.1 V c (mulB (L := L) P V y x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulV_tmul, mulB_tmul, mulB_tmul, mulV_tmul, mul_assoc]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem phiV_mulB (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    phiV P ↥L.1 V (mulB (L := L) P V y x) = mulB (L := L) P V (phiV P ↥L.1 (Fin 1 → ↥L.1) y) (phiV P ↥L.1 V x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, phiV_tmul, phiV_tmul, phiV_tmul, mulB_tmul, map_mul]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem monV_mulB (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    monV P ↥L.1 V (mulB (L := L) P V y x) = mulB (L := L) P V (monV P ↥L.1 (Fin 1 → ↥L.1) y) x +
      mulB (L := L) P V y (monV P ↥L.1 V x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, monV_tmul, monV_tmul, monV_tmul, mulB_tmul, mulB_tmul, ← TensorProduct.tmul_add]
      congr 1
      simp only [monSt_apply, derivative_mul]
      ring
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

variable {K : FinExt l} (ρs ρt : Representation ↥L.1 ↥(GK K) V)
  (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1)

theorem stRep_mulB (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) (g : ↥(GK K))
    (y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P) (x : V ⊗[ℚ_[l]] Bst P) :
    stRep P ρt g (mulB (L := L) P V y x) = mulB (L := L) P V (stRep P ρm g y) (stRep P ρs g x) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b' =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [mulB_tmul, stRep_tmul, stRep_tmul, stRep_tmul, mulB_tmul, map_mul, ht, hm, map_smul, Pi.smul_apply,
        smul_eq_mul, smul_smul, mul_smul]
    | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hx, hx'] <;> abel
  | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hy, hy'] <;> abel

theorem mulB_mem_Dpst (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)
    {x : V ⊗[ℚ_[l]] Bst P} {y : (Fin 1 → ↥L.1) ⊗[ℚ_[l]] Bst P} (hx : x ∈ Dpst P ρs) (hy : y ∈ Dpst P ρm) :
    mulB (L := L) P V y x ∈ Dpst P ρt := by
  obtain ⟨K₁, h₁⟩ := (mem_Dpst P ρs).mp hx
  obtain ⟨K₂, h₂⟩ := (mem_Dpst P ρm).mp hy
  refine (mem_Dpst P ρt).mpr ⟨supExt K₁ K₂, fun g hg => ?_⟩
  rw [stRep_mulB ρs ρt ρm χ hm ht, h₁ g (GK_le (K' := supExt K₁ K₂) le_sup_left hg),
    h₂ g (GK_le (K' := supExt K₁ K₂) le_sup_right hg)]

variable (P)

set_option synthInstance.maxHeartbeats 100000 in
def dmul (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v) :
    ↥(Dpst P ρs) →ₗ[↥L.1] ↥(Dpst P ρm) →ₗ[↥L.1] ↥(Dpst P ρt) :=
  LinearMap.mk₂ ↥L.1 (fun x y => ⟨mulB (L := L) P V y.1 x.1, mulB_mem_Dpst ρs ρt ρm χ hm ht x.2 y.2⟩)
    (fun x x' y => Subtype.ext (by simp))
    (fun a x y => Subtype.ext (by simp [mulB_smul]))
    (fun x y y' => Subtype.ext (by simp))
    (fun a x y => Subtype.ext (by simp [mulB_smul_left]))

variable (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)

@[simp] theorem coe_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    (dmul P ρs ρt ρm χ hm ht x y : V ⊗[ℚ_[l]] Bst P) = mulB (L := L) P V y.1 x.1 := rfl

theorem dmul_mulD_left (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    dmul P ρs ρt ρm χ hm ht (mulD P ρs c x) y = mulD P ρt c (dmul P ρs ρt ρm χ hm ht x y) :=
  Subtype.ext (by simp [mulB_mulV])

theorem dmul_mulD_right (c : ↥(MaximalUnramifiedExtension l)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    dmul P ρs ρt ρm χ hm ht x (mulD P ρm c y) = mulD P ρt c (dmul P ρs ρt ρm χ hm ht x y) :=
  Subtype.ext (by simp [mulV_mulB])

theorem phiD_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    phiD P ρt (dmul P ρs ρt ρm χ hm ht x y) = dmul P ρs ρt ρm χ hm ht (phiD P ρs x) (phiD P ρm y) :=
  Subtype.ext (by simp [phiV_mulB])

theorem monD_dmul (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    monD P ρt (dmul P ρs ρt ρm χ hm ht x y) =
      dmul P ρs ρt ρm χ hm ht (monD P ρs x) y + dmul P ρs ρt ρm χ hm ht x (monD P ρm y) :=
  Subtype.ext ((monV_mulB y.1 x.1).trans (add_comm _ _))

theorem actD_dmul (g : ↥(GK K)) (x : ↥(Dpst P ρs)) (y : ↥(Dpst P ρm)) :
    actD P ρt g (dmul P ρs ρt ρm χ hm ht x y) = dmul P ρs ρt ρm χ hm ht (actD P ρs g x) (actD P ρm g y) :=
  Subtype.ext (by simp [stRep_mulB ρs ρt ρm χ hm ht])

end GlobalTheory.Pst.TwistLetters
end
end
