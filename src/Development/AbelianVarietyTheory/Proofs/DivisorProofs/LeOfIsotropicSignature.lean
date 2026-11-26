module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedLastEntry
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCompactDualHaar
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIdentityComponentsSmoothGroupScheme

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfIsotropicSignature
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.ThetaInner
open scoped InnerProductSpace
open Matrix

namespace GlobalTheory.WittSignature


open scoped ComplexOrder in
theorem le_of_isotropic_standard {p q k : ℕ} (N : Matrix (Fin p ⊕ Fin q) (Fin k) ℂ) (L : Matrix (Fin k) (Fin p ⊕ Fin q) ℂ)
    (hL : L * N = 1) (h : Nᴴ * Formalism.UG.Jpq p q * N = 0) : k ≤ p ∧ k ≤ q := by
  have key : ∀ v : Fin k → ℂ, star ((N *ᵥ v) ∘ Sum.inl) ⬝ᵥ ((N *ᵥ v) ∘ Sum.inl) =
      star ((N *ᵥ v) ∘ Sum.inr) ⬝ᵥ ((N *ᵥ v) ∘ Sum.inr) := by
    intro v
    have h1 : star (N *ᵥ v) ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ (N *ᵥ v)) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
      simp
    generalize N *ᵥ v = x at h1 ⊢
    rw [Formalism.UG.Jpq, Matrix.fromBlocks_mulVec] at h1
    simp only [dotProduct, Fintype.sum_sum_type, Matrix.one_mulVec, Matrix.zero_mulVec, Matrix.neg_mulVec, add_zero, zero_add,
      Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at h1
    simp only [dotProduct]
    exact add_neg_eq_zero.1 h1
  have inj : ∀ v : Fin k → ℂ, (N *ᵥ v) ∘ Sum.inl = 0 → (N *ᵥ v) ∘ Sum.inr = 0 → v = 0 := by
    intro v h1 h2
    have h3 : N *ᵥ v = 0 := by
      funext i
      rcases i with i | i
      · exact congrFun h1 i
      · exact congrFun h2 i
    have : (L * N) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]
    simpa [hL] using this
  constructor
  · have hf : Function.Injective ((LinearMap.funLeft ℂ ℂ (Sum.inl : Fin p → Fin p ⊕ Fin q)).comp N.mulVecLin) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : (N *ᵥ v) ∘ Sum.inl = 0 := hv
      have h2 := key v
      rw [h1, dotProduct_zero] at h2
      exact inj v h1 (dotProduct_star_self_eq_zero.1 h2.symm)
    simpa using LinearMap.finrank_le_finrank_of_injective hf
  · have hf : Function.Injective ((LinearMap.funLeft ℂ ℂ (Sum.inr : Fin q → Fin p ⊕ Fin q)).comp N.mulVecLin) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : (N *ᵥ v) ∘ Sum.inr = 0 := hv
      have h2 := key v
      rw [h1, dotProduct_zero] at h2
      exact inj v (dotProduct_star_self_eq_zero.1 h2) h1
    simpa using LinearMap.finrank_le_finrank_of_injective hf

theorem le_of_isotropic_signature {n p q k : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (hJ : Formalism.UG.HasSignature J p q)
    (M : Matrix (Fin n) (Fin k) ℂ) (L : Matrix (Fin k) (Fin n) ℂ)
    (hL : L * M = 1) (h : Mᴴ * J * M = 0) : k ≤ p ∧ k ≤ q := by
  obtain ⟨e, P, hP⟩ := hJ
  have hP' : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * J.submatrix e.symm e.symm *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hP
  have hPP : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * (P⁻¹ : GL _ ℂ) = 1 := P.mul_inv
  have hN : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ).val * M.submatrix e.symm id) = M.submatrix e.symm id := by
    rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  refine le_of_isotropic_standard ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ).val * M.submatrix e.symm id) (L.submatrix id e.symm * P.val) ?_ ?_
  · rw [Matrix.mul_assoc, hN, Matrix.submatrix_mul_equiv, hL, Matrix.submatrix_id_id]
  · rw [← hP']
    generalize ((P⁻¹ : GL _ ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * M.submatrix e.symm id = N at hN ⊢
    calc _ = ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * N)ᴴ * J.submatrix e.symm e.symm *
          ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * N) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by
          rw [hN, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h]
          rfl

theorem wittIdx_le_signature : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E), S.SigOK → ∀ τ : E →+* ℂ, (∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) → wittIdx S ≤ (S.sig τ).1 ∧ wittIdx S ≤ (S.sig τ).2 := by
  intro E _ _ _ S hS τ hτ
  have main : ∀ W : Submodule E S.V, (∀ x ∈ W, ∀ y ∈ W, S.hT x y = 0) →
      Module.finrank E W ≤ (S.sig τ).1 ∧ Module.finrank E W ≤ (S.sig τ).2 := by
    intro W hW
    let b := Module.finBasis E W
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype
    let M := LinearMap.toMatrix b S.frame W.subtype
    let L := LinearMap.toMatrix S.frame b g
    have hL : L * M = 1 := by
      rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
    have hb : ∀ i, (b i : S.V) = ∑ a, M a i • S.frame a := by
      intro i
      simp only [M, LinearMap.toMatrix_apply, Submodule.subtype_apply]
      exact (S.frame.sum_repr _).symm
    have h : Mᴴ * S.gram * M = 0 := by
      ext i j
      have h0 := hW _ (b i).2 _ (b j).2
      rw [hb i, hb j] at h0
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
        starRingEnd_apply] at h0
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, HSpace.gram, Matrix.zero_apply]
      rw [← h0]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    refine le_of_isotropic_signature _ (hS τ) (M.map τ) (L.map τ) ?_ ?_
    · rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero τ) (map_one τ)]
    · have : (M.map τ)ᴴ = (Mᴴ).map τ := by
        ext i j
        simp [Matrix.conjTranspose_apply, hτ]
      rw [this, ← Matrix.map_mul, ← Matrix.map_mul, h, Matrix.map_zero _ (map_zero τ)]
  constructor
  · refine csSup_le' ?_
    rintro k ⟨W, rfl, hW⟩
    exact (main W hW).1
  · refine csSup_le' ?_
    rintro k ⟨W, rfl, hW⟩
    exact (main W hW).2

end GlobalTheory.WittSignature
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudePrimeToPPullbackSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudePrimeToPPullbackSquare
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

def TateIsoO.transport {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (Φ : Q ≃* Q') (hact : ∀ c x, Φ (act c x) = act' c (Φ x)) (he : ∀ n x y z, e n x y z → e' n (Φ x) (Φ y) z)
    (I : TateIsoO D k Q act e) : TateIsoO D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n x := Φ (I.ev n x)
  add n x y := by rw [I.add, map_mul]
  lin n b x := by rw [I.lin, hact]
  ker n hn hc x := by rw [map_eq_one_iff Φ Φ.injective]; exact I.ker n hn hc x
  onto n hn hc q := by
    obtain ⟨q, rfl⟩ := Φ.surjective q
    rw [← map_pow, map_eq_one_iff Φ Φ.injective, I.onto n hn hc]
    exact exists_congr fun x => Φ.injective.eq_iff.symm
  tower n m hn hm hc x := by rw [← map_pow, I.tower n m hn hm hc]
  isom n hn hc x y := he _ _ _ _ (I.isom n hn hc x y)

@[simp] theorem TateIsoO.transport_ev {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q Q' : Type}
    [Group Q] [Group Q'] {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop}
    {e' : ℕ → Q' → Q' → kˣ → Prop} (Φ : Q ≃* Q') (hact : ∀ c x, Φ (act c x) = act' c (Φ x))
    (he : ∀ n x y z, e n x y z → e' n (Φ x) (Φ y) z) (I : TateIsoO D k Q act e) (n : ℕ) (y : D.La) :
    (I.transport Φ hact he).ev n y = Φ (I.ev n y) := rfl

theorem tateIsoO_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N' s') (f : S' ⟶ S) (φ : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left), IsGrpPullback o'.A o.A f φ → IsSquare φ φ₂ → (∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left) → LBIso o'.P (o.P.pull φ₂) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S'), (∀ I' : TateIsoO D k (Over.mk x ⟶ o'.A) (fun c g => g ≫ o'.act.act c) (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z)), ∃ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) ∧ (∀ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∃ I' : TateIsoO D k (Over.mk x ⟶ o'.A) (fun c g => g ≫ o'.act.act c) (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z)), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) := by
  intro p _ D R _ b N N' S S' s s' o o' f φ φ₂ hp hsq hact hpol k _ _ x
  have e : φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left = (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ φ₂ := by
    apply pullback.hom_ext
    · change (φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left) ≫ (fst o.A o.A).left =
        ((lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ φ₂) ≫ (fst o.A o.A).left
      rw [Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id, Category.assoc, hsq.1,
        ← Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp]
    · change (φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left) ≫ (snd o.A o.A).left =
        ((lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ φ₂) ≫ (snd o.A o.A).left
      rw [Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id, Category.assoc, hsq.2,
        ← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp]
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hL' : (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left).IsLB := pull_isLB o'.isLB _
  have H1 : LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (o.P.pull (φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    LBIso.chartPull (chartPullPull o'.P _ _ rfl) (chartPullSame o.P _ (fun _ => φ₂) _ _ fun _ => e) hpol
  have hw : LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull φ) :=
    LBIso.chartPull (chartPullId _) (chartPullOut o.P (fun _ => (lift (𝟙 o.A) (𝟙 o.A)).left) (fun _ => 1) φ
      (fun _ => φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left) fun _ => rfl) H1
  let Φ := GlobalTheory.ObjPull.pushEquiv hp (Over.mk x)
  have hW : ∀ (n : ℕ) (g g' : Over.mk x ⟶ o'.A) (z : kˣ),
      Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z) ↔
        Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n (Φ g) (Φ g') (unitOn z) :=
    fun n g g' z => GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ f φ _ _ hL hL' hp hw (Over.mk x) n g g' (Φ g) (Φ g')
      _ rfl rfl
  have hA : ∀ c (g : Over.mk x ⟶ o'.A), Φ (g ≫ o'.act.act c) = Φ g ≫ o.act.act c := fun c g =>
    Over.OverMorphism.ext (by
      show (g ≫ o'.act.act c).left ≫ φ = (Φ g ≫ o.act.act c).left
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact c, GlobalTheory.ObjPull.pushEquiv_left, Category.assoc])
  refine ⟨fun I' => ⟨I'.transport Φ hA fun n g g' z h => (hW n g g' z).1 h, fun n y => rfl⟩,
    fun I => ⟨I.transport Φ.symm (fun c g => Φ.injective ?_) (fun n g g' z h => (hW n _ _ z).2 ?_), fun n y => ?_⟩⟩
  · rw [MulEquiv.apply_symm_apply, hA, MulEquiv.apply_symm_apply]
  · rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]; exact h
  · rw [TateIsoO.transport_ev]
    exact (GlobalTheory.ObjPull.pushEquiv_symm_left hp (Over.mk x) (I.ev n y)).symm

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudePrimeToPPullbackSquareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateSimilitude_prime_to_p_pullback_square : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N' s') (f : S' ⟶ S) (φ : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left), IsGrpPullback o'.A o.A f φ → IsSquare φ φ₂ → (∀ c, (o'.act.act c).left ≫ φ = φ ≫ (o.act.act c).left) → LBIso o'.P (o.P.pull φ₂) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S'), (∀ I' : TateIsoO D k (Over.mk x ⟶ o'.A) (fun c g => g ≫ o'.act.act c) (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z)), ∃ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) ∧ (∀ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∃ I' : TateIsoO D k (Over.mk x ⟶ o'.A) (fun c g => g ≫ o'.act.act c) (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z)), ∀ n y, (I.ev n y).left = (I'.ev n y).left ≫ φ) := by
  first | exact @GlobalTheory.UPel.HT.tateIsoO_pullback | exact GlobalTheory.UPel.HT.tateIsoO_pullback | (intros; apply GlobalTheory.UPel.HT.tateIsoO_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightSequenceGuards
noncomputable section

namespace GlobalTheory.Proof.WeightSequenceEntries

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

theorem padZero_eq {a : ℕ} (b : ℕ) (ν : DomWeight a) (j : Fin b) :
    PaddedWittNormSquare.padZero b ν j = PaddedLastEntry.padZero b ν j := rfl

theorem lastEntry_eq {a : ℕ} (ν : DomWeight a) : PaddedWittNormSquare.lastEntry ν = PaddedLastEntry.lastEntry ν := rfl

theorem normSq_eq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (v : VV ℂ lam) :
    PaddedWittNormSquare.normSq lam v = PaddedLastEntry.invNormSq lam v := rfl

theorem unitSq_eq {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) :
    PaddedWittNormSquare.unitNormSq r z = PaddedLastEntry.unitSq r z := rfl

theorem tmax_eq {ι : Type} [Fintype ι] {a : ℕ} (b : ℕ) (ν : ι → DomWeight a) (Om : ι → ℝ) (S : ℝ) :
    PaddedWittNormSquare.tmax b ν Om S = PaddedLastEntry.tmax b ν S Om := rfl

theorem opNormSqLe_iff {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (t : ℝ) :
    PaddedWittNormSquare.OpNormSqLe lam lam' T t ↔ PaddedLastEntry.OpNormSqLe lam lam' T t := by
  unfold PaddedWittNormSquare.OpNormSqLe PaddedLastEntry.OpNormSqLe
  simp only [normSq_eq]

theorem stepWeights_iff {a b : ℕ} (lam ν : DomWeight a) (lam' : DomWeight b) :
    (∃ s' s : ℤ, PaddedWittNormSquare.IsStepWeight lam ν lam' s' s) ↔ PaddedLastEntry.StepWeights lam ν lam' := by
  unfold PaddedWittNormSquare.IsStepWeight PaddedLastEntry.StepWeights
  constructor
  · rintro ⟨s', s, hν, hpos, hpad⟩
    exact ⟨hpos, ⟨s', hν⟩, ⟨s, fun j => (hpad j).trans (padZero_eq b ν j)⟩⟩
  · rintro ⟨hpos, ⟨s', hν⟩, ⟨s, hpad⟩⟩
    exact ⟨s', s, hν, hpos, fun j => (hpad j).trans (padZero_eq b ν j).symm⟩

theorem stepWeights_family_iff {ι : Type} {a b : ℕ} (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b) :
    (∃ s' s : ι → ℤ, ∀ τ, PaddedWittNormSquare.IsStepWeight (lam τ) (ν τ) (lam' τ) (s' τ) (s τ)) ↔
      ∀ τ, PaddedLastEntry.StepWeights (lam τ) (ν τ) (lam' τ) := by
  constructor
  · rintro ⟨s', s, h⟩ τ
    exact (stepWeights_iff (lam τ) (ν τ) (lam' τ)).1 ⟨s' τ, s τ, h τ⟩
  · intro h
    choose s' s hs using fun τ => (stepWeights_iff (lam τ) (ν τ) (lam' τ)).2 (h τ)
    exact ⟨s', s, hs⟩

theorem guard_iff {ι : Type} {a b : ℕ} (hab : a ≤ b) (ν : ι → DomWeight a) :
    (∀ τ, a < b ∨ PaddedWittNormSquare.lastEntry (ν τ) = 0) ↔ (a = b → ∀ τ, PaddedLastEntry.lastEntry (ν τ) = 0) := by
  constructor
  · intro h heq τ
    rcases h τ with hlt | h0
    · exact absurd heq (ne_of_lt hlt)
    · exact (lastEntry_eq (ν τ)).symm.trans h0
  · intro h τ
    rcases lt_or_eq_of_le hab with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ((lastEntry_eq (ν τ)).trans (h heq τ))

theorem growth_iff {ι : Type} [Fintype ι] {a b : ℕ} (G : VCx ι a b → ℂ) (S : ℝ) (r : ι → ℝ) :
    (∀ z, ‖G z‖ ≤ S * Real.exp (PaddedWittNormSquare.unitNormSq r z / 2)) ↔
      ∀ z, ‖G z‖ ≤ S * Real.exp (PaddedLastEntry.unitSq r z / 2) := by
  simp only [unitSq_eq]

theorem conclusion_iff {ι : Type} [Fintype ι] {a b : ℕ} (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b)
    (G : VCx ι a b → ℂ) (S : ℝ) (Om : ι → ℝ) (cD : ι → ℂ) :
    PaddedWittNormSquare.OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => PaddedWittNormSquare.lastEntry (ν τ)) (PaddedWittNormSquare.tmax b ν Om S) ↔
      PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => PaddedLastEntry.lastEntry (ν τ)) (PaddedLastEntry.tmax b ν S Om) := by
  simp only [opNormSqLe_iff, tmax_eq, lastEntry_eq]

theorem blockBound_iff : PaddedWittNormSquare.BlockBound ↔ PaddedLastEntry.BlockBound := by
  unfold PaddedWittNormSquare.BlockBound PaddedLastEntry.BlockBound
  constructor
  · intro h ι _ a b hab lam ν lam' hstep hguard r Om cD hr hOm hc G S hG hgrowth
    obtain ⟨s', s, hs⟩ := (stepWeights_family_iff lam ν lam').2 hstep
    exact (conclusion_iff lam ν lam' G S Om cD).1
      (h ι a b hab lam ν lam' s' s hs ((guard_iff hab ν).2 hguard) G S r Om cD hG hr
        ((growth_iff G S r).2 hgrowth) hOm hc)
  · intro h ι _ a b hab lam ν lam' s' s hs hguard G S r Om cD hG hr hgrowth hOm hc
    exact (conclusion_iff lam ν lam' G S Om cD).2
      (h ι a b hab lam ν lam' ((stepWeights_family_iff lam ν lam').1 ⟨s', s, hs⟩)
        ((guard_iff hab ν).1 hguard) r Om cD hr hOm hc G S hG ((growth_iff G S r).1 hgrowth))

end GlobalTheory.Proof.WeightSequenceEntries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMember
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMember
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg.MinSecond

section Transport

variable {p q : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isHW_equiv (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (μ : Ix p q → ℚ) (v : V) (hv : IsHW a μ v) : IsHW b μ (e v) := by
  obtain ⟨h0, h1⟩ := hv
  refine ⟨fun h' => h0 (e.map_eq_zero_iff.mp h'), ?_⟩
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1 ⊢
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [← h, ← map_smul, ← map_sub, h1.1 i, map_zero]
  · rw [← h, h1.2 i j hij, map_zero]

theorem symm_equivariant (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v)) (Z : Mat p q) (w : W) :
    e.symm (b Z w) = a Z (e.symm w) := by
  apply e.injective
  rw [h, e.apply_symm_apply, e.apply_symm_apply]

theorem ofType_equiv (e : V ≃ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (μ : Ix p q → ℚ) (v : V) (hv : OfType a μ v) : OfType b μ (e v) := by
  obtain ⟨U, hf, hvU, hst, hw⟩ := hv
  refine ⟨U.map (e : V →ₗ[ℂ] W), inferInstance, ⟨v, hvU, rfl⟩, ?_, ?_⟩
  · rintro X hX _ ⟨u, hu, rfl⟩
    exact ⟨a X u, hst X hX u hu, h X u⟩
  · rintro ν _ ⟨u, hu, rfl⟩ hν
    refine hw ν u hu ?_
    have := isHW_equiv e.symm b a (symm_equivariant e a b h) ν _ hν
    simpa using this

theorem genSub_map (e : V →ₗ[ℂ] W) (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (b : Mat p q →ₗ[ℂ] Module.End ℂ W) (h : ∀ Z v, e (a Z v) = b Z (e v))
    (S : Set V) (T : Set W) (hST : ∀ v ∈ S, e v ∈ T) (v : V) (hv : v ∈ genSub a S) :
    e v ∈ genSub b T := by
  simp only [genSub, Submodule.mem_sInf, Set.mem_ofPred_eq] at hv ⊢
  intro N hN
  refine hv (N.comap e) ⟨fun x hx => hN.1 (hST x hx), fun Z y hy => ?_⟩
  rw [Submodule.mem_comap, h]
  exact hN.2 Z _ hy

end Transport

noncomputable def swapPol (p q r s : ℕ) : Pol p q r s ≃ₗ[ℂ] Pol r s p q :=
  (renameEquiv ℂ (Equiv.prodComm (Ix p q) (Ix r s))).toLinearEquiv

end GlobalTheory.FockAlg.MinSecond


open GlobalTheory.FockAlg.MinSecond in
theorem GlobalTheory.FockAlg.min_second : ∀ (p q r s : ℕ) (M1 : GKMod p q) (M2 : GKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V), IrrGK M2 → AdmGK M2 → Intw M1 M2 f → f ≠ 0 → ∀ (μ' : Ix r s → ℚ), (∃ v, IsHW M2.act μ' v) → (∀ ν w, IsHW M2.act ν w → degW (cPair p q) μ' ≤ degW (cPair p q) ν) → (∃ (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ jointHarm p q r s ∧ IsHW (fockAct1 p q r s) μ P ∧ IsHW (fockAct2 p q r s) μ' P ∧ f P ≠ 0) ∧ ∀ P, OfType (fockAct2 p q r s) μ' P → f P ∈ Submodule.map f (genSub (fockAct1 p q r s) {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}) := by
  intro p q r s M1 M2 f hirr hadm hf hf0 μ' hμ hmin
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.fock_dualPair_swap_symmetry r s p q
  set e := swapPol r s p q with he
  have h1 : ∀ Z v, e (fockAct1 r s p q Z v) = fockAct2 p q r s Z (e v) := s1
  have h2 : ∀ Z v, e (fockAct2 r s p q Z v) = fockAct1 p q r s Z (e v) := s2
  have hJ : ∀ P, P ∈ jointHarm r s p q → e P ∈ jointHarm p q r s := fun P hP =>
    ⟨(s3 P).1.mp hP.2, (s3 P).2.mp hP.1⟩
  set c := TensorProduct.comm ℂ M1.V M2.V with hc
  let g : Pol r s p q →ₗ[ℂ] TensorProduct ℂ M2.V M1.V :=
    (c : _ →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e : _ →ₗ[ℂ] _)
  have hg : ∀ P, g P = c (f (e P)) := fun _ => rfl
  have hcm : ∀ (A : Module.End ℂ M1.V) (B : Module.End ℂ M2.V) x,
      c (TensorProduct.map A B x) = TensorProduct.map B A (c x) := by
    intro A B x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hc]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hgI : Intw M2 M1 g := by
    refine ⟨fun X => LinearMap.ext fun P => ?_, fun X => LinearMap.ext fun P => ?_⟩
    · have := LinearMap.congr_fun (hf.2 X) (e P)
      simp only [LinearMap.comp_apply] at this ⊢
      rw [hg, hg, h1, this, hcm]
    · have := LinearMap.congr_fun (hf.1 X) (e P)
      simp only [LinearMap.comp_apply] at this ⊢
      rw [hg, hg, h2, this, hcm]
  have hg0 : g ≠ 0 := by
    intro h
    apply hf0
    refine LinearMap.ext fun P => ?_
    have := LinearMap.congr_fun h (e.symm P)
    rw [hg, e.apply_symm_apply, LinearMap.zero_apply] at this
    exact c.map_eq_zero_iff.mp this
  obtain ⟨⟨μ, P, hP, hP1, hP2, hP0⟩, hB⟩ := GlobalTheory.T.exists_jointHarm_highestWeight_and_map_mem_genSub r s p q M2 M1 g hirr hadm hgI hg0 μ' hμ hmin
  refine ⟨⟨μ, e P, hJ P hP, isHW_equiv e _ _ h2 _ _ hP2, isHW_equiv e _ _ h1 _ _ hP1, ?_⟩, ?_⟩
  · intro h
    apply hP0
    rw [hg, h, map_zero]
  · intro R hR
    obtain ⟨Q, hQ, hQe⟩ := hB (e.symm R)
      (ofType_equiv e.symm _ _ (symm_equivariant e _ _ h1) _ _ hR)
    refine ⟨e Q, ?_, ?_⟩
    · exact genSub_map e.toLinearMap (fockAct2 r s p q) (fockAct1 p q r s) h2
        {Q | Q ∈ jointHarm r s p q ∧ OfType (fockAct1 r s p q) μ' Q}
        {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}
        (fun v hv => ⟨hJ v hv.1, ofType_equiv e _ _ h1 _ _ hv.2⟩) Q hQ
    · rw [hg, hg, e.apply_symm_apply] at hQe
      exact c.injective hQe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMinimalKTypeSecondMemberStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_minimal_KType_second_member : ∀ (p q r s : ℕ) (M1 : GKMod p q) (M2 : GKMod r s) (f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ M1.V M2.V), IrrGK M2 → AdmGK M2 → Intw M1 M2 f → f ≠ 0 → ∀ (μ' : Ix r s → ℚ), (∃ v, IsHW M2.act μ' v) → (∀ ν w, IsHW M2.act ν w → degW (cPair p q) μ' ≤ degW (cPair p q) ν) → (∃ (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ jointHarm p q r s ∧ IsHW (fockAct1 p q r s) μ P ∧ IsHW (fockAct2 p q r s) μ' P ∧ f P ≠ 0) ∧ ∀ P, OfType (fockAct2 p q r s) μ' P → f P ∈ Submodule.map f (genSub (fockAct1 p q r s) {Q | Q ∈ jointHarm p q r s ∧ OfType (fockAct2 p q r s) μ' Q}) := by
  first | exact @GlobalTheory.FockAlg.min_second | exact GlobalTheory.FockAlg.min_second | (intros; apply GlobalTheory.FockAlg.min_second <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMassUpperBound
open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open Formalism.MainNotions.StandardLattice (stdForm stdLat)
open Formalism.HermitianLatticesTheory (gmap isom genus)

namespace GlobalTheory

namespace StdMassBound

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

noncomputable def matEquiv (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    (Fin n → E) ≃ₗ[E] (Fin n → E) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin γ) (Matrix.mulVecLin γ.conjTranspose)
    (by rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, mul_eq_one_comm.1 h, Matrix.mulVecLin_one])

theorem matEquiv_mem (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    matEquiv γ h ∈ isom (stdForm E n) := by
  intro x y
  change star (γ.mulVec x) ⬝ᵥ (γ.mulVec y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, mul_eq_one_comm.1 h, Matrix.one_mulVec]

theorem diagForm_eq : Examples₂.diagForm (E := E) n (fun _ => false) = stdForm E n := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  change ∑ i, star (x i) * Examples₂.sgn false * y i = ∑ i, star (x i) * y i
  simp [Examples₂.sgn]

variable [NumberField E]

omit [StarRing E] in
theorem stdLat_eq : Examples₂.stdLat (E := E) n = stdLat E n := by
  unfold Examples₂.stdLat stdLat
  congr 2
  funext i
  exact Pi.basisFun_apply E (Fin n) i

omit [StarRing E] in
theorem mem_one_iff (a : E) : a ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ a := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨r, rfl⟩
    exact r.isIntegral_coe
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

theorem selfDual_of_mem_genus {M : Submodule (𝓞 E) (Fin n → E)} (hM : M ∈ genus (stdForm E n) (stdLat E n))
    (y : Fin n → E) : y ∈ M ↔ ∀ x ∈ M, IsIntegral ℤ (∑ i, star (x i) * y i) := by
  have hsym : (stdForm E n).IsSymm := diagForm_eq (E := E) (n := n) ▸ Examples₂.diagForm_isSymm n _
  obtain ⟨-, -, hinv⟩ := Formalism.HermitianLatticesTheory.genusBasic (𝓞 E) E (Fin n → E) (stdForm E n) hsym
    (Examples₂.star_integral Examples₂.star_isIntegral)
  have h0 : Formalism.HermitianLatticesTheory.IsUnimodular (stdForm E n) (stdLat E n) := by
    rw [← diagForm_eq, ← stdLat_eq]
    exact Examples₂.stdLat_unimod Examples₂.star_isIntegral n _
  have hfg : (stdLat E n).FG := Submodule.fg_span (Set.finite_range _)
  have hu : Formalism.HermitianLatticesTheory.dual (stdForm E n) M = M := ((hinv _ _ hfg hM.1.fg hM.2).1).1 h0
  conv_lhs => rw [← hu]
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, mem_one_iff]
  rfl

end StdMassBound


open StdMassBound in
theorem mass_stdLat_le :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E],
    (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ,
    Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) ≤
      (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ E * n ^ 2) := by
  intro E _ _ _ _ hs n
  have hexists : ∃ R : Finset (Submodule (𝓞 E) (Fin n → E)),
      (R.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG →
        (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (∑ i, IsCMField.complexConj E (x i) * y i)) →
        ∃ L₀ ∈ R, ∃ γ : Matrix (Fin n) (Fin n) E,
          γ * (γ.map (IsCMField.complexConj E)).transpose = 1 ∧
          ∀ x, x ∈ L₀ ↔ γ.mulVec x ∈ L := by
    open RootClassCount ReciprocityTheory.ChartRestriction.G.FD in
    obtain ⟨R, -, h2, h3⟩ := ClassCount.exists_finset_classes (K := E) (r := n) (G := 1)
      {L | L.FG ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (herm 1 y x)}
      (B := 4 * (fdeg E : ℝ) ^ 3 * n ^ 4 * rdE E ^ 2) (by positivity) fun L hL =>
        ⟨by simp, fun x hx => (hL.2 x).1 hx,
          exists_bounded_basis L hL.1 (fun x hx => (hL.2 x).1 hx) fun x hx => (hL.2 x).2 hx⟩
    refine ⟨R, h3.trans ?_, fun L hfg hsd => ?_⟩
    · have h := bound_le (fdeg E) n ClassCount.fdeg_pos (one_le_rootDiscr (E := E))
      rw [← ShortVectors.finrank_eq] at h
      rw [rdE_eq, ← ShortVectors.finrank_eq]
      exact h
    · obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := h2 L ⟨hfg, fun y => by
        simp only [isIntegral_herm_iff]; exact hsd y⟩
      exact ⟨L₀, hL₀, γ, mul_conjTranspose_eq_one _ hγ, hm⟩
  obtain ⟨R, hR, H⟩ := hexists
  refine le_trans ?_ hR
  unfold Formalism.HermitianLatticesTheory.mass
  split_ifs with hex
  swap
  · positivity
  obtain ⟨h1, h2⟩ := hex.choose_spec
  generalize hex.choose = s at h1 h2
  have key : ∀ M ∈ s, ∃ L₀ ∈ R, ∃ g ∈ isom (stdForm E n), gmap g L₀ = M := by
    intro M hM
    obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := H M (h1 M hM).1.fg (fun y => by
      simpa only [hs] using selfDual_of_mem_genus (h1 M hM) y)
    have hγ' : γ * γ.conjTranspose = 1 := by
      rw [← hγ]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply, hs]
    refine ⟨L₀, hL₀, matEquiv γ hγ', matEquiv_mem γ hγ', ?_⟩
    ext x
    obtain ⟨x, rfl⟩ := (matEquiv γ hγ').surjective x
    constructor
    · rintro ⟨z, hz, e⟩
      rw [← e]
      exact (hm z).1 hz
    · intro hx
      exact ⟨x, (hm x).2 hx, rfl⟩
  choose! f hf g hg hfg using key
  have hcard : s.card ≤ R.card := by
    refine Finset.card_le_card_of_injOn f (fun M hM => hf M hM) fun M hM N hN e => ?_
    have hM' : M ∈ s := hM
    have hN' : N ∈ s := hN
    refine (h2 M (h1 M hM')).unique ⟨hM', 1, one_mem _, Formalism.HermitianLatticesTheory.genusBasic_gmap_one _⟩
      ⟨hN', g M * (g N)⁻¹, mul_mem (hg M hM') (inv_mem (hg N hN')), ?_⟩
    have e1 : gmap (g N)⁻¹ N = f N := by
      conv_lhs => rw [← hfg N hN']
      rw [hfg N hN']
      have := Formalism.HermitianLatticesTheory.genusBasic_gmap_inv (g N) (f N)
      rwa [hfg N hN'] at this
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, e1, ← e, hfg M hM']
  calc ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm E n) M) : ℕ) : ℝ)⁻¹ ≤ ∑ M ∈ s, (1 : ℝ) :=
        Finset.sum_le_sum fun M _ => Nat.cast_inv_le_one _
    _ = s.card := by simp
    _ ≤ R.card := by exact_mod_cast hcard

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHCharN
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits infIdele HChar IsUnitAt ordF upF aboveF atFin atInf infDiag unif etaInf etaFin aboveInf OverP embPsi PiBar Omg EtaTExists Mu0Exists IsMu0 IsChiPsi IsDelta IsEtaT DeltaExists
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Col2.SplitChar

namespace GlobalTheory.SplitCharGen

variable {D : D7}

def ofHChar (N : ℕ) (χ : HChar D.host.E) (n : D.what₂.Tau → ℤ) (hu : χ.IsUnitary)
    (hi : χ.HasInf (embTau D) n) (hp : ∀ τ, Even (n τ - (N : ℤ)))
    (hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) → χ.1 (finIdl D u) = 1)
    (hn : ∀ x, χ.1 (finIdl D (x * sgU D x)) = 1)
    (hr : ∀ u, IntU D u → (∀ q : ℕ, q.Prime → ¬ InertQ D q → ZeroAt D q ((u : AE D) - 1)) → χ.1 (finIdl D u) = 1) :
    HeckeU D N where
  f := χ.1.comp (finIdl D)
  n := n
  unitary := fun _ => hu _
  cont := hc
  aut := fun a => by
    have h1 := χ.2.2 a
    rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU, mul_comm] at h1
    have h2 := hi a
    have h3 := congrArg (Units.val : ℂˣ → ℂ) h1
    rw [Units.val_mul, Units.val_one] at h3
    rw [← h3]
    exact congrArg _ h2.symm
  norm := hn
  par := hp
  unr := hr

end GlobalTheory.SplitCharGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleModuleInfId
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Polynomial GroundTheory.Automorphic UpperTheory.V
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin)
open UpperTheory.V.TR (Rinf Lie chart infGL pInf toL rmul invSet CuspSub)
open scoped ContDiff
open GlobalTheory.HenQ

namespace GlobalTheory.HenQ.DetSplit

variable {K : Type} [Field K] [NumberField K] [IsTotallyReal K] {n : ℕ}

omit [NumberField K] in
theorem norm_realSymm (w : InfinitePlace K) (r : ℝ) :
    ‖((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm r : w.Completion)‖ = |r| := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.dist_eq r 0
  have h0 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm 0 : w.Completion) = 0 :=
    map_zero _
  rw [← dist_zero_right, ← Real.norm_eq_abs, ← dist_zero_right, ← h0]
  exact h

theorem ideleModule_infId (u : (Rinf K)ˣ) :
    (GroundTheory.Global.IdeleGroup.ideleModule K (UpperTheory.V.TR.infId K u) : ℝ) = ∏ w, |u.val w| := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h1 : ((UpperTheory.V.TR.infId K u : (Ad K)ˣ) : Ad K).1 = UpperTheory.V.TR.infEq K u.val := by
    show (1 : InfiniteAdeleRing K) - UpperTheory.V.TR.infEq K 1 + UpperTheory.V.TR.infEq K u.val = _
    simp
  have h2 : ((UpperTheory.V.TR.infId K u : (Ad K)ˣ) : Ad K).2 = 1 := by
    show (1 : Af K) - 0 + 0 = 1
    simp
  rw [h1, h2]
  have h3 : ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(1 : Af K) v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by exact norm_one
  rw [h3, mul_one]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  exact norm_realSymm w (u.val w)

end GlobalTheory.HenQ.DetSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMemIdentityComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupSchemeOfIsOpenStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupSchemeOfIsOpenStable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.OpenSubgroup

theorem exists_open_subgroup : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (Z : Set G.left), IsOpen Z → (∀ s : S, (η[G]).left s ∈ Z) → (∀ w : (G ⊗ G).left, (fst G G).left w ∈ Z → (snd G G).left w ∈ Z → (μ[G]).left w ∈ Z) → (∀ y ∈ Z, (ι[G]).left y ∈ Z) → ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧ Set.range j.left = Z := by
  intro S G _ Z hZ h1 hmul hinv
  let U : G.left.Opens := ⟨Z, hZ⟩
  let G₀ : Over S := Over.mk (U.ι ≫ G.hom)
  let j : G₀ ⟶ G := Over.homMk U.ι rfl
  have hjo : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hr : Set.range j.left = Z := U.range_ι
  have : Mono j := Over.mono_of_mono_left j
  have lift : ∀ (X : Over S) (φ : X ⟶ G), Set.range φ.left ⊆ Z → ∃ ψ : X ⟶ G₀, ψ ≫ j = φ := by
    intro X φ hsub
    have hsub' : Set.range φ.left ⊆ Set.range j.left := hr ▸ hsub
    refine ⟨Over.homMk (IsOpenImmersion.lift j.left φ.left hsub') ?_, ?_⟩
    · rw [← j.w, IsOpenImmersion.lift_fac_assoc, φ.w]
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac j.left φ.left hsub')
  have inZ : ∀ x : G₀.left, j.left x ∈ Z := fun x => hr ▸ Set.mem_range_self x
  obtain ⟨e, he⟩ := lift (𝟙_ _) η[G] (by
    rintro _ ⟨s, rfl⟩
    exact h1 s)
  obtain ⟨m, hm⟩ := lift (G₀ ⊗ G₀) ((j ⊗ₘ j) ≫ μ[G]) (by
    rintro _ ⟨w, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    apply hmul
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, tensorHom_fst, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact inZ _
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, tensorHom_snd, Over.comp_left,
        Scheme.Hom.comp_apply]
      exact inZ _)
  obtain ⟨i, hi⟩ := lift G₀ (j ≫ ι[G]) (by
    rintro _ ⟨x, rfl⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact hinv _ (inZ x))
  obtain ⟨Gs, hG⟩ := exists_grpObj_of_mono_of_fac j e m i he hm hi
  exact ⟨G₀, Gs, j, hG, hjo, hr⟩

end GlobalTheory.OpenSubgroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupSchemeOfIsOpenStableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openSubgroupScheme_of_isOpen_stable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (Z : Set G.left), IsOpen Z → (∀ s : S, (η[G]).left s ∈ Z) → (∀ w : (G ⊗ G).left, (fst G G).left w ∈ Z → (snd G G).left w ∈ Z → (μ[G]).left w ∈ Z) → (∀ y ∈ Z, (ι[G]).left y ∈ Z) → ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧ Set.range j.left = Z := by
  first | exact @GlobalTheory.OpenSubgroup.exists_open_subgroup | exact GlobalTheory.OpenSubgroup.exists_open_subgroup | (intros; apply GlobalTheory.OpenSubgroup.exists_open_subgroup <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem unit_mem_identityComponents (S : Scheme.{0}) (G : Over S) [GrpObj G] (s : S) :
    (η[G]).left s ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  have hs : G.hom ((η[G]).left s) = s := by
    have h := Over.w (η[G])
    have h2 : (𝟙_ (Over S)).hom = 𝟙 S := rfl
    rw [h2] at h
    rw [← Scheme.Hom.comp_apply, h]
    rfl
  show (η[G]).left s ∈ connectedComponentIn (G.hom ⁻¹' {G.hom ((η[G]).left s)}) ((η[G]).left (G.hom ((η[G]).left s)))
  rw [hs]
  exact mem_connectedComponentIn hs

theorem identityComponentOpen : GlobalTheory.Published.IdentityComponentOpen := by
  intro S G _ hG
  obtain ⟨G₀, i, j, h1, h2, h3⟩ := GlobalTheory.T.exists_openSubgroupScheme_of_isOpen_stable S G
    {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}
    (GlobalTheory.T.isOpen_identityComponents_smooth_groupScheme S G hG) (unit_mem_identityComponents S G) (GlobalTheory.T.identityComponents_smooth_groupScheme_mul_mem S G hG) (GlobalTheory.T.inv_mem_identity_component_fibre S G)
  refine ⟨G₀, i, j, h1, h2, fun x => ?_⟩
  rw [h3]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem blkMat_one_mem (hr : r ≤ a) (k : Kinf E (a - r)) :
    blkMat (Cinf E) hr (1, k.1) ∈ Matrix.unitaryGroup (Fin a) (Cinf E) := by
  have hs : star (blkMat (Cinf E) hr (1, k.1)) = blkMat (Cinf E) hr (1, star k.1) := by
    change Matrix.conjTranspose (Matrix.reindex (blkEquiv hr) (blkEquiv hr) (Matrix.fromBlocks 1 0 0 k.1)) =
      Matrix.reindex (blkEquiv hr) (blkEquiv hr) (Matrix.fromBlocks 1 0 0 (Matrix.conjTranspose k.1))
    rw [Matrix.conjTranspose_reindex, Matrix.fromBlocks_conjTranspose]
    simp
  rw [Matrix.mem_unitaryGroup_iff', hs, ← map_mul]
  have : ((1 : Matrix (Fin r) (Fin r) (Cinf E)), star k.1) * (1, k.1) = 1 :=
    Prod.ext (mul_one _) (Matrix.mem_unitaryGroup_iff'.1 k.2)
  rw [this, map_one]

def blkK (hr : r ≤ a) (k : Kinf E (a - r)) : Kinf E a := ⟨blkMat (Cinf E) hr (1, k.1), blkMat_one_mem hr k⟩

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem toUnits_blkK (hr : r ≤ a) (k : Kinf E (a - r)) :
    Unitary.toUnits (blkK hr k) = blkGL hr (1, Unitary.toUnits k) := Units.ext rfl


variable (E) in
def slice [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E))
    (hr : r ≤ a) (φ : GA E a → ℂ) (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a) : GA E (a - r) → ℂ :=
  fun m₂ => ∫ x in 𝓕, φ (unip x * (blkGL hr (m₁, m₂) * finGL E a t * infGL E a (Unitary.toUnits κ))) ∂μ

def levelSub (hr : r ≤ a) (t : GL (Fin a) (Af E)) (L : Subgroup (GL (Fin a) (Af E))) :
    Subgroup (GL (Fin (a - r)) (Af E)) :=
  (L.map (MulAut.conj t).toMonoidHom).comap ((blkGL hr).comp (MonoidHom.inr _ _))

theorem mem_levelSub (hr : r ≤ a) (t : GL (Fin a) (Af E)) (L : Subgroup (GL (Fin a) (Af E)))
    (l : GL (Fin (a - r)) (Af E)) : l ∈ levelSub hr t L ↔ t⁻¹ * blkGL hr (1, l) * t ∈ L := by
  simp only [levelSub, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, hk, e⟩
    rw [← e]; simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by group⟩

def ktypeSub (hr : r ≤ a) (κ : Kinf E a) (W : Submodule ℂ (Kinf E a → ℂ)) : Submodule ℂ (Kinf E (a - r) → ℂ) :=
  W.map (LinearMap.funLeft ℂ ℂ fun k => κ⁻¹ * blkK hr k * κ)

instance (hr : r ≤ a) (κ : Kinf E a) (W : Submodule ℂ (Kinf E a → ℂ)) [FiniteDimensional ℂ W] :
    FiniteDimensional ℂ (ktypeSub hr κ W) := by
  unfold ktypeSub; infer_instance

theorem blkGL_one_corner {R S : Type} [CommRing R] [CommRing S] (hr : r ≤ a) (s : R →ₙ+* S)
    (l : GL (Fin (a - r)) R) : blkGL hr (1, cornerGL (a - r) s l) = cornerGL a s (blkGL hr (1, l)) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (blkEquiv hr).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv hr).surjective j
  rw [blkGL_apply]
  change _ = (1 : Matrix (Fin a) (Fin a) S) _ _ - s ((1 : Matrix (Fin a) (Fin a) R) _ _) + s ((blkGL hr (1, l) : Matrix (Fin a) (Fin a) R) _ _)
  rw [blkGL_apply]
  have e1 : ∀ {T : Type} [CommRing T] (i j : Fin r ⊕ Fin (a - r)),
      (1 : Matrix (Fin a) (Fin a) T) (blkEquiv hr i) (blkEquiv hr j) = (1 : Matrix (Fin r ⊕ Fin (a - r)) _ T) i j := by
    intro T _ i j
    simp [Matrix.one_apply, (blkEquiv hr).injective.eq_iff]
  rw [e1, e1]
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.one_apply]
  · simp
  · simp
  · change (1 : Matrix _ _ S) i j - s ((1 : Matrix _ _ R) i j) + s (l i j) = _
    simp [Matrix.one_apply]

theorem blkGL_mul_finGL (hr : r ≤ a) (m₁ : GA E r) (m₂ : GA E (a - r)) (l : GL (Fin (a - r)) (Af E)) :
    blkGL hr (m₁, m₂ * finGL E (a - r) l) = blkGL hr (m₁, m₂) * finGL E a (blkGL hr (1, l)) := by
  rw [show (m₁, m₂ * finGL E (a - r) l) = (m₁, m₂) * (1, finGL E (a - r) l) by simp, map_mul]
  exact congrArg _ (blkGL_one_corner hr _ l)

theorem blkGL_mul_infGL (hr : r ≤ a) (m₁ : GA E r) (m₂ : GA E (a - r)) (y : GL (Fin (a - r)) (Cinf E)) :
    blkGL hr (m₁, m₂ * infGL E (a - r) y) = blkGL hr (m₁, m₂) * infGL E a (blkGL hr (1, y)) := by
  rw [show (m₁, m₂ * infGL E (a - r) y) = (m₁, m₂) * (1, infGL E (a - r) y) by simp, map_mul]
  exact congrArg _ (blkGL_one_corner hr _ y)

theorem slice_mul_finGL [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)) (hr : r ≤ a) (φ : GA E a → ℂ) (L : Subgroup (GL (Fin a) (Af E)))
    (hφ : ∀ k ∈ L, ∀ g, φ (g * finGL E a k) = φ g) (m₁ : GA E r) (t : GL (Fin a) (Af E)) (κ : Kinf E a)
    (l : GL (Fin (a - r)) (Af E)) (hl : l ∈ levelSub hr t L) (g : GA E (a - r)) :
    slice E μ 𝓕 hr φ m₁ t κ (g * finGL E (a - r) l) = slice E μ 𝓕 hr φ m₁ t κ g := by
  unfold slice
  congr 1
  funext x
  have hk := hφ _ ((mem_levelSub hr t L l).1 hl)
    (unip x * (blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)))
  rw [← hk, blkGL_mul_finGL]
  congr 1
  have e : finGL E a t * finGL E a (t⁻¹ * blkGL hr (1, l) * t) = finGL E a (blkGL hr (1, l)) * finGL E a t := by
    rw [← map_mul, ← map_mul]; congr 1; group
  calc unip x * (blkGL hr (m₁, g) * finGL E a (blkGL hr (1, l)) * finGL E a t * infGL E a (Unitary.toUnits κ))
      = unip x * (blkGL hr (m₁, g) * (finGL E a t * finGL E a (t⁻¹ * blkGL hr (1, l) * t)) *
          infGL E a (Unitary.toUnits κ)) := by rw [e]; simp only [mul_assoc]
    _ = unip x * (blkGL hr (m₁, g) * finGL E a t * (infGL E a (Unitary.toUnits κ) *
          finGL E a (t⁻¹ * blkGL hr (1, l) * t))) := by rw [infGL_comm]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem slice_mul_cpt [MeasurableSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E))
    (𝓕 : Set (BlockIx a r → Ad E)) (hr : r ≤ a) (φ : GA E a → ℂ) (m₁ : GA E r) (t : GL (Fin a) (Af E))
    (κ : Kinf E a) (g : GA E (a - r)) (k : Kinf E (a - r)) :
    slice E μ 𝓕 hr φ m₁ t κ (g * infGL E (a - r) (Unitary.toUnits k)) =
      ∫ x in 𝓕, φ (unip x * ((blkGL hr (m₁, g) * finGL E a t * infGL E a (Unitary.toUnits κ)) *
        infGL E a (Unitary.toUnits (κ⁻¹ * blkK hr k * κ)))) ∂μ := by
  unfold slice
  congr 1
  funext x
  congr 2
  rw [blkGL_mul_infGL]
  simp only [map_mul, map_inv, toUnits_blkK]
  simp only [mul_assoc, mul_inv_cancel_left]
  rw [← mul_assoc (infGL E a (blkGL hr (1, Unitary.toUnits k))) (finGL E a t),
    infGL_comm (blkGL hr (1, Unitary.toUnits k)) t]
  simp only [mul_assoc]

end GlobalTheory.SliceTwo

end
end
