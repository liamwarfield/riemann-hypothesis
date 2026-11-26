module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA

namespace UpperTheory.TP.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure IsLatRepL {nS nT : ℕ} (σ : E →ₐ[F] E) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (hc : HeisClosedF σ JS JT ξ₀ ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
    (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)) : Prop where
  hw : w + sgOF σ w = 1
  sd : SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ)
  span : Submodule.span ℂ {m | ∃ x e, Fixes (opFF hc w) (latF F E nS nT Λ) e ∧ m = opFF hc w x e} = ⊤
  fin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0
  op : ∀ p x v, Om p (opFF hc w x v) = opFF hc w (rhoFF σ JS JT p x) (Om p v)
  sd' : ∀ p, SelfDual (gamFF σ JS JT ξ₀ ψ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p))
  vac : ∀ p e, Fixes (opFF hc w) (latF F E nS nT Λ) e →
    Om p e = normOp lam (opFF hc w) (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) e
  good : GoodNorm (sgOF σ) lam
  lev : ∀ x : XFF F E nS nT, ∃ N : ℕ, 0 < N ∧ ∀ l ∈ latF F E nS nT Λ,
    ψ (symplOHF σ JS JT ξ₀ (x : WOF F E nS nT) (N • (l : WOF F E nS nT))) = 1
  near : ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), ∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ
  near' : ∀ (x : XFF F E nS nT) (N : ℕ), 0 < N → ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT),
    ∃ l ∈ latF F E nS nT Λ, rhoFF σ JS JT p x = x + N • l
  splitStab : ∀ e, IsSplitIdemF σ e → ∀ a ∈ latF F E nS nT Λ,
    mulFF e a ∈ latF F E nS nT Λ ∧ mulFF (cAF σ e) a ∈ latF F E nS nT Λ

end UpperTheory.TP.W

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.TLiftK
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions

namespace UpperTheory.TP

def TLiftK : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E), W.GoodK (cj E) B →
    ∀ (n : ℕ), 1 ≤ n → ∀ X : Spc (maximalRealSubfield E) E n, X.J = 1 → X.IsHerm (cj E) B n 0 →
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (W : Spc (maximalRealSubfield E) E d) (δ : E), W.J = δ • (1 : Matrix (Fin d) (Fin d) E) →
      W.IsSkew (cj E) B d 0 → ∀ (χX χW : Chr (maximalRealSubfield E) E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ),
      IsHecke (maximalRealSubfield E) E χX → IsHecke (maximalRealSubfield E) E χW →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χW d →
      HasExp B.emb χX mX → HasExp B.emb χW mW →
      ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n),
        GlobalTheory.UnitaryBC.IsAutRepU U → (∀ w, GlobalTheory.UnitaryBC.HasWeightAt U (B.emb w).1 (lam w)) →
        (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) → ∃ U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ), IsLift B χX χW mX mW lam U U'

end UpperTheory.TP

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.DatumK
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA

namespace UpperTheory.TP.W

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
variable {η κ χS χT : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}

theorem resEta_mul (h2 : ResEtaF η 1) (hκ : IsKap σ lam κ) : ResEtaF (η * κ) 1 :=
  ⟨h2.1, fun e he a => by rw [MonoidHom.mul_apply, hκ.base a, mul_one]; exact h2.2 e he a⟩

end UpperTheory.TP.W

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.CardDet
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

private theorem card_quot_span_mul {R : Type} [CommRing R] [IsDomain R] {a b : R} (ha : a ≠ 0) :
    Nat.card (R ⧸ Ideal.span {a * b}) =
      Nat.card (R ⧸ Ideal.span {a}) * Nat.card (R ⧸ Ideal.span {b}) := by
  let f : R →+ R := AddMonoidHom.mulLeft a
  have hle : (Ideal.span {a * b}).toAddSubgroup ≤ (Ideal.span {a}).toAddSubgroup := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact Ideal.mem_span_singleton'.2 ⟨y * b, by ring⟩
  have hcomap : (Ideal.span {a * b}).toAddSubgroup.comap f = (Ideal.span {b}).toAddSubgroup := by
    ext x
    change a * x ∈ Ideal.span {a * b} ↔ x ∈ Ideal.span {b}
    rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    exact mul_dvd_mul_iff_left ha
  have hmap : (⊤ : AddSubgroup R).map f = (Ideal.span {a}).toAddSubgroup := by
    ext x
    change x ∈ (⊤ : AddSubgroup R).map f ↔ x ∈ Ideal.span {a}
    rw [Ideal.mem_span_singleton, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, trivial, rfl⟩
  have hrel : (Ideal.span {a * b}).toAddSubgroup.relIndex (Ideal.span {a}).toAddSubgroup =
      (Ideal.span {b}).toAddSubgroup.index := by
    rw [← hmap, ← AddSubgroup.relIndex_comap, hcomap, AddSubgroup.relIndex_top_right]
  have hmul := AddSubgroup.relIndex_mul_index hle
  rw [hrel] at hmul
  change (Ideal.span {a * b}).toAddSubgroup.index =
    (Ideal.span {a}).toAddSubgroup.index * (Ideal.span {b}).toAddSubgroup.index
  rw [← hmul, Nat.mul_comm]

private theorem card_quot_span_prod {R ι : Type} [CommRing R] [IsDomain R] (s : Finset ι) (c : ι → R)
    (hc : ∀ i ∈ s, c i ≠ 0) :
    Nat.card (R ⧸ Ideal.span {∏ i ∈ s, c i}) = ∏ i ∈ s, Nat.card (R ⧸ Ideal.span {c i}) := by
  induction s using Finset.induction_on with
  | empty =>
    have h : Ideal.span {(1 : R)} = ⊤ := Ideal.span_singleton_one
    simp only [Finset.prod_empty]
    rw [h]
    exact Nat.card_unique
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      card_quot_span_mul (hc i (Finset.mem_insert_self i s)),
      ih fun j hj => hc j (Finset.mem_insert_of_mem hj)]

theorem UpperTheory.TP.W.cardDet :
    CardDet := by
  intro R M _ _ _ _ _ _ _ f hinj
  set N := LinearMap.range f with hN
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hinj
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R N = Module.finrank R M := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let cb := Submodule.smithNormalFormBotBasis b h
  have cb_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : M ≃ₗ[R] N := b'.equiv cb (Equiv.refl _)
  let g : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
  have hg : ∀ i, g (b' i) = c i • b' i := by
    intro i
    have : g (b' i) = b'.equiv cb (Equiv.refl _) (b' i) := rfl
    rw [this, b'.equiv_apply, Equiv.refl_apply]
    exact cb_eq i
  have hm : LinearMap.toMatrix b' b' g = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, hg, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, _root_.mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hass := LinearMap.associated_det_comp_equiv N.subtype e e'
  have h0 : N.subtype ∘ₗ (e : M →ₗ[R] N) = f := by
    ext x; rfl
  rw [h0] at hass
  have h1 : LinearMap.det g = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix b', hm, Matrix.det_diagonal]
  change Associated (LinearMap.det f) (LinearMap.det g) at hass
  rw [h1] at hass
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i hi
    apply cb.ne_zero i
    apply Subtype.ext
    rw [cb_eq i]
    change c i • b' i = 0
    rw [hi, zero_smul]
  have hcq : Nat.card (M ⧸ N) = ∏ i, Nat.card (R ⧸ Ideal.span {c i}) := by
    rw [← Nat.card_pi]
    exact Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv
  rw [hcq, Ideal.span_singleton_eq_span_singleton.2 hass,
    card_quot_span_prod _ c fun i _ => hc0 i]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IdxHalf
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

private theorem idxHalf_half {X : Type} [AddCommGroup X] (γ : X → X → ℂ)
    (al : ∀ x y z, γ (x + y) z = γ x z * γ y z) (ar : ∀ x y z, γ x (y + z) = γ x y * γ x z)
    (nz : ∀ x y, γ x y ≠ 0) (P P0 Q Q0 : AddSubgroup X)
    (h1 : ∀ p ∈ P, ∀ q ∈ Q, q ∈ Q0 → γ p q = 1)
    (h3 : ∀ p ∈ P, (∀ q ∈ Q, γ p q = 1) → p ∈ P0)
    (hfin : Q0.relIndex Q ≠ 0) :
    P0.relIndex P ≠ 0 ∧ P0.relIndex P ≤ Q0.relIndex Q := by
  classical
  have g0 : ∀ x, γ x 0 = 1 := fun x => by
    have h := ar x 0 0
    rw [add_zero] at h
    exact mul_left_cancel₀ (nz x 0) (h.symm.trans (mul_one _).symm)
  have g0' : ∀ y, γ 0 y = 1 := fun y => by
    have h := al 0 0 y
    rw [add_zero] at h
    exact mul_left_cancel₀ (nz 0 y) (h.symm.trans (mul_one _).symm)
  have hfinQ : Finite (↥Q ⧸ Q0.addSubgroupOf Q) := Nat.finite_of_card_ne_zero hfin
  letI : Fintype (↥Q ⧸ Q0.addSubgroupOf Q) := Fintype.ofFinite _
  let f : ↥P → ↥Q →+ Additive ℂˣ := fun p =>
    { toFun := fun q => Additive.ofMul (Units.mk0 (γ p q) (nz p q))
      map_zero' := by
        show _ = Additive.ofMul 1
        congr 1
        ext
        simp [g0]
      map_add' := fun q1 q2 => by
        rw [← ofMul_mul]
        congr 1
        ext
        simp [ar] }
  have hker : ∀ p, Q0.addSubgroupOf Q ≤ (f p).ker := by
    intro p q hq
    rw [AddSubgroup.mem_addSubgroupOf] at hq
    rw [AddMonoidHom.mem_ker]
    show Additive.ofMul _ = Additive.ofMul 1
    congr 1
    ext
    simp [h1 p p.2 q q.2 hq]
  let χ : ↥P → AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ := fun p =>
    { toFun := fun g => ((Additive.toMul (QuotientAddGroup.lift _ (f p) (hker p) g) : ℂˣ) : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by simp }
  have hχ : ∀ p (q : ↥Q), χ p (q : ↥Q ⧸ Q0.addSubgroupOf Q) = γ p q := by
    intro p q
    show ((Additive.toMul (QuotientAddGroup.lift _ (f p) (hker p) (q : ↥Q ⧸ Q0.addSubgroupOf Q)) : ℂˣ) : ℂ) = _
    rw [QuotientAddGroup.lift_mk]
    rfl
  let Φ : ↥P →+ Additive (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ) :=
    { toFun := fun p => Additive.ofMul (χ p)
      map_zero' := by
        show _ = Additive.ofMul 1
        congr 1
        ext g
        obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective g
        rw [hχ, AddChar.one_apply]
        simp [g0']
      map_add' := fun p1 p2 => by
        rw [← ofMul_mul]
        congr 1
        ext g
        obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective g
        rw [AddChar.mul_apply, hχ, hχ, hχ]
        simp [al] }
  have hkerΦ : Φ.ker ≤ P0.addSubgroupOf P := by
    intro p hp
    rw [AddMonoidHom.mem_ker] at hp
    have hp' : χ p = 1 := hp
    rw [AddSubgroup.mem_addSubgroupOf]
    apply h3 p p.2
    intro q hq
    have h4 := congrArg (fun c : AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ => c ((⟨q, hq⟩ : ↥Q) : ↥Q ⧸ Q0.addSubgroupOf Q)) hp'
    rw [hχ, AddChar.one_apply] at h4
    exact h4
  haveI : Finite (Additive (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ)) :=
    inferInstanceAs (Finite (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ))
  have hΦfin : Nat.card Φ.range ≤ Q0.relIndex Q := by
    calc Nat.card Φ.range ≤ Nat.card (Additive (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ)) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = Nat.card (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ) := rfl
      _ = Fintype.card (AddChar (↥Q ⧸ Q0.addSubgroupOf Q) ℂ) := Nat.card_eq_fintype_card
      _ ≤ Fintype.card (↥Q ⧸ Q0.addSubgroupOf Q) := AddChar.card_addChar_le _ _
      _ = Q0.relIndex Q := Nat.card_eq_fintype_card.symm
  haveI : Finite Φ.range := Finite.of_injective _ Subtype.val_injective
  have hkpos : Φ.ker.index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_pos.ne'
  have hdvd := AddSubgroup.index_dvd_of_le hkerΦ
  have hne : (P0.addSubgroupOf P).index ≠ 0 := fun h => hkpos (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  refine ⟨hne, ?_⟩
  calc P0.relIndex P = (P0.addSubgroupOf P).index := rfl
    _ ≤ Φ.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hkpos) hdvd
    _ = Nat.card Φ.range := AddSubgroup.index_ker Φ
    _ ≤ Q0.relIndex Q := hΦfin

theorem UpperTheory.TP.W.idxHalf :
    IdxHalf := by
  intro R X M _ _ _ _ _ σ w γ W hH A B hA hB hidx e e' he he' hee' he'e hadj hAe hBe hf
  have memE : ∀ (S : Submodule R X), (∀ a ∈ S, e a ∈ S ∧ e' a ∈ S) →
      ∀ x, x ∈ Submodule.map e S ↔ x ∈ S ∧ e x = x := by
    intro S hS x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hS y hy).1, he y⟩
    · rintro ⟨hx, hex⟩
      exact ⟨x, hx, hex⟩
  have memE' : ∀ (S : Submodule R X), (∀ a ∈ S, e a ∈ S ∧ e' a ∈ S) →
      ∀ x, x ∈ Submodule.map e' S ↔ x ∈ S ∧ e' x = x := by
    intro S hS x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hS y hy).2, he' y⟩
    · rintro ⟨hx, hex⟩
      exact ⟨x, hx, hex⟩
  have prodF : idx A B = idx (Submodule.map e A) (Submodule.map e B) *
      idx (Submodule.map e' A) (Submodule.map e' B) := by
    let φ : ↥B.toAddSubgroup →+ ↥(Submodule.map e B).toAddSubgroup × ↥(Submodule.map e' B).toAddSubgroup :=
      { toFun := fun b => (⟨e b, Submodule.mem_map_of_mem b.2⟩, ⟨e' b, Submodule.mem_map_of_mem b.2⟩)
        map_zero' := by ext <;> simp
        map_add' := fun x y => by ext <;> simp }
    have hφs : Function.Surjective φ := by
      rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      have hx' := (memE B hBe x).1 hx
      have hy' := (memE' B hBe y).1 hy
      refine ⟨⟨x + y, B.add_mem hx'.1 hy'.1⟩, ?_⟩
      have h1 : e y = 0 := by rw [← hy'.2, hee']
      have h2 : e' x = 0 := by rw [← hx'.2, he'e]
      ext <;> simp [φ, map_add (f := _), hx'.2, hy'.2, h1, h2]
    have hcomap : A.toAddSubgroup.addSubgroupOf B.toAddSubgroup =
        AddSubgroup.comap φ (((Submodule.map e A).toAddSubgroup.addSubgroupOf
          (Submodule.map e B).toAddSubgroup).prod
          ((Submodule.map e' A).toAddSubgroup.addSubgroupOf (Submodule.map e' B).toAddSubgroup)) := by
      ext b
      simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf,
        Submodule.mem_toAddSubgroup]
      constructor
      · intro hb
        exact ⟨Submodule.mem_map_of_mem hb, Submodule.mem_map_of_mem hb⟩
      · rintro ⟨h1, h2⟩
        have h1' : e b ∈ A := ((memE A hAe _).1 h1).1
        have h2' : e' b ∈ A := ((memE' A hAe _).1 h2).1
        have hbB : (b : X) ∈ B := b.2
        have h3 : (b : X) - e b - e' b ∈ A :=
          (hf b).2 (B.sub_mem (B.sub_mem hbB (hBe _ hbB).1) (hBe _ hbB).2)
        convert A.add_mem (A.add_mem h3 h1') h2' using 1
        abel
    show (A.toAddSubgroup.addSubgroupOf B.toAddSubgroup).index = _
    rw [hcomap, AddSubgroup.index_comap_of_surjective _ hφs, AddSubgroup.index_prod]
    rfl
  have hfin2 : idx (Submodule.map e' A) (Submodule.map e' B) ≠ 0 := fun h => hidx (by rw [prodF, h, mul_zero])
  have s1h1 : ∀ p ∈ (Submodule.map e A).toAddSubgroup, ∀ q ∈ (Submodule.map e' B).toAddSubgroup,
      q ∈ (Submodule.map e' A).toAddSubgroup → γ p q = 1 := by
    intro p hp q _ hq
    exact hH.iso hA ((memE A hAe p).1 hp).1 ((memE' A hAe q).1 hq).1
  have s1h3 : ∀ p ∈ (Submodule.map e A).toAddSubgroup,
      (∀ q ∈ (Submodule.map e' B).toAddSubgroup, γ p q = 1) → p ∈ (Submodule.map e B).toAddSubgroup := by
    intro p hp hq
    have hp' := (memE A hAe p).1 hp
    have hpB : p ∈ B := by
      refine (hB p).2 (fun b hb => ?_)
      rw [← hp'.2, hadj]
      exact hq _ ((memE' B hBe _).2 ⟨(hBe b hb).2, he' b⟩)
    exact (memE B hBe p).2 ⟨hpB, hp'.2⟩
  have st1 := idxHalf_half γ hH.add_left hH.add_right hH.ne_zero _ _ _ _ s1h1 s1h3 hfin2
  have s2h1 : ∀ p ∈ (Submodule.map e' B).toAddSubgroup, ∀ q ∈ (Submodule.map e A).toAddSubgroup,
      q ∈ (Submodule.map e B).toAddSubgroup → γ p q = 1 := by
    intro p hp q _ hq
    exact hH.iso hB ((memE' B hBe p).1 hp).1 ((memE B hBe q).1 hq).1
  have s2h3 : ∀ p ∈ (Submodule.map e' B).toAddSubgroup,
      (∀ q ∈ (Submodule.map e A).toAddSubgroup, γ p q = 1) → p ∈ (Submodule.map e' A).toAddSubgroup := by
    intro p hp hq
    have hp' := (memE' B hBe p).1 hp
    have hpA : p ∈ A := by
      refine (hA p).2 (fun a ha => hH.swap_eq_one ?_)
      rw [← hp'.2, ← hadj]
      exact hH.swap_eq_one (hq _ ((memE A hAe _).2 ⟨(hAe a ha).1, he a⟩))
    exact (memE' A hAe p).2 ⟨hpA, hp'.2⟩
  have st2 := idxHalf_half γ hH.add_left hH.add_right hH.ne_zero _ _ _ _ s2h1 s2h3 st1.1
  rw [prodF]
  congr 1
  exact le_antisymm st2.2 st1.2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.ContinuousOfWE
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
open UpperTheory.TP.W

noncomputable section

namespace UpperTheory.TP.W

private theorem exists_signChar {ι G : Type} [CommGroup G] (w : ι → G →* WithZero (Multiplicative ℤ))
    (hne : ∀ i g, w i g ≠ 0) (hfin : ∀ g, {i | w i g ≠ 1}.Finite) (s : ι → Circle) :
    ∃ κ : G →* Circle, ∀ g, κ g = ∏ᶠ i, s i ^ WithZero.log (w i g) := by
  have hsup : ∀ g, (Function.mulSupport fun i => s i ^ WithZero.log (w i g)).Finite := fun g =>
    (hfin g).subset fun i hi h => hi (by simp [h])
  refine ⟨{ toFun := fun g => ∏ᶠ i, s i ^ WithZero.log (w i g), map_one' := ?_, map_mul' := ?_ }, fun _ => rfl⟩
  · simp
  · intro x y
    rw [← finprod_mul_distrib (hsup x) (hsup y)]
    refine finprod_congr fun i => ?_
    rw [map_mul, WithZero.log_mul (hne i x) (hne i y), _root_.zpow_add]

private theorem finprod_invol {ι : Type} (c : ι → ι) (hc : ∀ i, c (c i) = i) (f : ι → Circle)
    (hf : (Function.mulSupport f).Finite) (h1 : ∀ i, f i * f (c i) = 1) (h2 : ∀ i, f i ≠ 1 → c i ≠ i) :
    ∏ᶠ i, f i = 1 := by
  rw [finprod_eq_prod f hf]
  refine Finset.prod_involution (fun i _ => c i) (fun i _ => h1 i) (fun i _ => h2 i) (fun i hi => ?_) (fun i _ => hc i)
  rw [Set.Finite.mem_toFinset, Function.mem_mulSupport] at hi ⊢
  intro h
  exact hi (by simpa [h] using h1 i)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private def cj (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  ⟨P.asIdeal.comap (sgOF σ), Ideal.comap_isPrime _ _, by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro hb
    have : sgOF σ x ∈ P.asIdeal.comap (sgOF σ) := by
      show sgOF σ (sgOF σ x) ∈ P.asIdeal
      rw [sgOF_sgOF h]; exact hx
    rw [hb, Ideal.mem_bot] at this
    exact hx0 (by rw [← sgOF_sgOF h x, this, map_zero])⟩

private theorem mem_cj (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    r ∈ (cj h P).asIdeal ↔ sgOF σ r ∈ P.asIdeal := Iff.rfl

private theorem cj_cj (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) : cj h (cj h P) = P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun r => ?_)
  rw [mem_cj, mem_cj, sgOF_sgOF h]

private theorem cj_fx (h : IsCMExt F E σ) {P : HeightOneSpectrum (𝓞 E)} (hP : Fx σ P) : Fx σ (cj h P) := by
  intro r hr
  rw [mem_cj] at hr ⊢
  rw [sgOF_sgOF h]
  have := hP _ hr
  rwa [sgOF_sgOF h] at this

private theorem fx_of_cj_eq (h : IsCMExt F E σ) {P : HeightOneSpectrum (𝓞 E)} (hP : cj h P = P) : Fx σ P := by
  intro r hr
  have h1 : r ∈ (cj h P).asIdeal := by rw [hP]; exact hr
  exact h1

private theorem under_cj (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    (cj h P).under (𝓞 F) = P.under (𝓞 F) := by
  refine HeightOneSpectrum.ext ?_
  show (P.asIdeal.comap (sgOF σ)).comap (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  rw [Ideal.comap_comap]
  congr 1
  exact RingHom.ext sgOF_alg

private theorem absNorm_cj (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (cj h P).asIdeal = Ideal.absNorm P.asIdeal := by
  let e : 𝓞 E ≃+* 𝓞 E := RingEquiv.ofRingHom (sgOF σ) (sgOF σ)
    (RingHom.ext (sgOF_sgOF h)) (RingHom.ext (sgOF_sgOF h))
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine Nat.card_congr (Ideal.quotientEquiv (cj h P).asIdeal P.asIdeal e ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (e : 𝓞 E →+* 𝓞 E) e.surjective P.asIdeal).symm

private theorem ram_cj (h : IsCMExt F E σ) (P : HeightOneSpectrum (𝓞 E)) :
    (cj h P).asIdeal.ramificationIdx (𝓞 F) = P.asIdeal.ramificationIdx (𝓞 F) := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have e1 := Ideal.ramificationIdxIn_eq_ramificationIdx ((cj h P).asIdeal.under (𝓞 F)) (cj h P).asIdeal (E ≃ₐ[F] E)
  have e2 := Ideal.ramificationIdxIn_eq_ramificationIdx (P.asIdeal.under (𝓞 F)) P.asIdeal (E ≃ₐ[F] E)
  have e3 : (cj h P).asIdeal.under (𝓞 F) = P.asIdeal.under (𝓞 F) := congrArg HeightOneSpectrum.asIdeal (under_cj h P)
  rw [← e1, ← e2, e3]

private def sgn (σ : E →ₐ[F] E) (lam : ℕ →* ℂ) (P : HeightOneSpectrum (𝓞 E)) : Circle :=
  if Fx σ P then 1 else
    if lam (Ideal.absNorm P.asIdeal) = (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) then 1 else -1

private theorem sgn_mul (lam : ℕ →* ℂ) (P : HeightOneSpectrum (𝓞 E)) : sgn σ lam P * sgn σ lam P = 1 := by
  unfold sgn
  split_ifs <;> simp

private theorem sgn_cj (h : IsCMExt F E σ) (lam : ℕ →* ℂ) (P : HeightOneSpectrum (𝓞 E)) :
    sgn σ lam (cj h P) = sgn σ lam P := by
  have : Fx σ (cj h P) ↔ Fx σ P := ⟨fun a => cj_cj h P ▸ cj_fx h a, cj_fx h⟩
  unfold sgn
  simp only [this, absNorm_cj]

private theorem lam_eq {lam : ℕ →* ℂ} (hlam : GoodNorm (sgOF σ) lam) {P : HeightOneSpectrum (𝓞 E)} (hP : ¬ Fx σ P) :
    lam (Ideal.absNorm P.asIdeal) = (sgn σ lam P : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) := by
  have h2 : lam (Ideal.absNorm P.asIdeal) ^ 2 = (Ideal.absNorm P.asIdeal : ℂ) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (hlam.2 P.asIdeal P.isMaximal (Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot)).1
  have h3 : ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) ^ 2 = (Ideal.absNorm P.asIdeal : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  unfold sgn
  rw [if_neg hP]
  split_ifs with h
  · simpa using h
  · have h4 := sq_eq_sq_iff_eq_or_eq_neg.1 (h2.trans h3.symm)
    simpa using h4.resolve_left h

private theorem wv_ne (Q : HeightOneSpectrum (𝓞 E)) (z : (AEF F E)ˣ) : wv F E Q z ≠ 0 :=
  ((Group.isUnit z).map (wv F E Q)).ne_zero

private theorem wv_eq_one {Q : HeightOneSpectrum (𝓞 E)} {z : (AEF F E)ˣ} (h1 : Valued.v (ev F E Q z) ≤ 1)
    (h2 : Valued.v (ev F E Q ((z⁻¹ : (AEF F E)ˣ) : AEF F E)) ≤ 1) : wv F E Q z = 1 := by
  have e : wv F E Q z * wv F E Q z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = wv F E Q z * wv F E Q z⁻¹ := e.symm
    _ ≤ wv F E Q z := mul_le_of_le_one_right' h2

private theorem ev_int (y : AEF F E) : ∀ᶠ Q in Filter.cofinite, Valued.v (ev F E Q y) ≤ 1 := by
  filter_upwards [(GlobalTheory.LFun.finAdEquiv F E (finPartF F E y)).2] with Q hQ
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hQ

private theorem wv_fin (z : (AEF F E)ˣ) : {Q | wv F E Q z ≠ 1}.Finite := by
  refine (Filter.eventually_cofinite.1 ((ev_int (z : AEF F E)).and (ev_int ((z⁻¹ : (AEF F E)ˣ) : AEF F E)))).subset ?_
  intro Q hQ hc
  exact hQ (wv_eq_one hc.1 hc.2)

private theorem fin_of_SE {z : AF F ⊗[F] E} (hz : z ∈ GlobalTheory.HeckeExtend.SE F E) : finPartF F E z ∈ Formalism.IndefR.LiftF.intAEF F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem g hg =>
    obtain ⟨t, ⟨c, hc, e⟩, o, rfl⟩ := hg
    rw [one_smul] at e
    refine AddSubgroup.subset_closure ⟨c, hc, o, ?_⟩
    rw [map_mul, PositivityTheory.ThKW.Eta.fin_j, e]
    show (c ⊗ₜ[F] (1 : E)) * ((1 : Af F) ⊗ₜ[F] (o : E)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

private theorem wv_of_WE {z : (AEF F E)ˣ} (hz : z ∈ GlobalTheory.HeckeExtend.WE F E 1) (Q : HeightOneSpectrum (𝓞 E)) :
    wv F E Q z = 1 :=
  wv_eq_one ((int_iff _).1 (fin_of_SE (PositivityTheory.ThKW.Eta.mem_SE_of_CE hz.1)) Q)
    ((int_iff _).1 (fin_of_SE (PositivityTheory.ThKW.Eta.mem_SE_of_CE hz.2)) Q)

private theorem continuous_of_WE (κ : (AEF F E)ˣ →* Circle) (h : ∀ z ∈ GlobalTheory.HeckeExtend.WE F E 1, κ z = 1) :
    Continuous κ := by
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hWo : IsOpen (GlobalTheory.HeckeExtend.WE F E 1 : Set (AF F ⊗[F] E)ˣ) := by
    have ho := GlobalTheory.HeckeExtend.CE_isOpen F E 1 one_pos
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  refine continuous_of_continuousAt_one _ ?_
  unfold ContinuousAt
  rw [map_one]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hWo.mem_nhds (one_mem _)] with z hz
  exact (h z hz).symm

private theorem wv_idFF {v : HeightOneSpectrum (𝓞 F)} {Q : HeightOneSpectrum (𝓞 E)} (hv : Q.under (𝓞 F) = v)
    (a : (AF F)ˣ) : wv F E Q (idFF F E a) =
      Valued.v ((sndA F (a : AF F)) v) ^ Q.asIdeal.ramificationIdx (𝓞 F) := by
  subst hv
  have h0 : (sndA F (a : AF F)) (Q.under (𝓞 F)) ≠ 0 :=
    (a.isUnit.map ((evalV F (Q.under (𝓞 F))).comp (sndA F))).ne_zero
  rw [wv_apply]
  change Valued.v (ev F E Q (algebraMap (AF F) (AEF F E) (a : AF F))) = _
  rw [ev_alg]
  exact valued_complMap rfl h0

theorem kapEx : KapEx := by
  intro F E _ _ _ _ _ σ h lam hlam
  obtain ⟨κ, hκ⟩ := exists_signChar (wv F E) wv_ne wv_fin (sgn σ lam)
  have hsup : ∀ z, (Function.mulSupport fun Q => sgn σ lam Q ^ WithZero.log (wv F E Q z)).Finite := fun z =>
    (wv_fin z).subset fun i hi h => hi (by simp [h])
  refine ⟨κ, ?_, fun z => ?_, fun a => ?_, fun z hz => ?_, fun P hP z h1 h2 => ?_⟩
  · exact continuous_of_WE κ fun z hz => by
      rw [hκ]
      simp [wv_of_WE hz]
  · rw [hκ, ← finprod_mul_distrib (hsup z) (hsup z)]
    have : ∀ Q, sgn σ lam Q ^ WithZero.log (wv F E Q z) * sgn σ lam Q ^ WithZero.log (wv F E Q z) = 1 := fun Q => by
      rw [← _root_.mul_zpow, sgn_mul, _root_.one_zpow]
    simp [this]
  · rw [hκ]
    refine finprod_invol (cj h) (cj_cj h) _ (hsup _) (fun P => ?_) (fun P hP hc => hP ?_)
    · by_cases hP : Fx σ P
      · have a1 : sgn σ lam P = 1 := if_pos hP
        have a2 : sgn σ lam (cj h P) = 1 := if_pos (cj_fx h hP)
        rw [a1, a2, _root_.one_zpow, _root_.one_zpow, one_mul]
      · have e : wv F E (cj h P) (idFF F E a) = wv F E P (idFF F E a) := by
          rw [wv_idFF (under_cj h P), ram_cj, wv_idFF rfl]
        rw [sgn_cj, e, ← _root_.mul_zpow, sgn_mul, _root_.one_zpow]
    · have : sgn σ lam P = 1 := if_pos (fx_of_cj_eq h hc)
      rw [this, _root_.one_zpow]
  · rw [hκ]
    have : ∀ Q, sgn σ lam Q ^ WithZero.log (wv F E Q z) = 1 := fun Q => by
      by_cases hQ : Fx σ Q
      · have a1 : sgn σ lam Q = 1 := if_pos hQ
        rw [a1, _root_.one_zpow]
      · simp [hz Q hQ]
    simp [this]
  · have e : κ z = sgn σ lam P := by
      rw [hκ, finprod_eq_single _ P (fun Q hQ => by simp [h2 Q hQ]), h1, WithZero.log_exp, _root_.zpow_neg, zpow_one]
      exact inv_eq_of_mul_eq_one_left (sgn_mul lam P)
    rw [e]
    exact lam_eq hlam hP

end UpperTheory.TP.W

end
end
