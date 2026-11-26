module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepSumRepAwayFromLHost
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepSumRepAwayFromLHost
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent

namespace GlobalTheory.WeilDeligne.SumParam

section Blocks

variable (k : Type) [CommRing k] (a b : ℕ)

def blk : Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k →+*
    Matrix (Fin (a + b)) (Fin (a + b)) k :=
  (Matrix.reindexAlgEquiv k k finSumFinEquiv).toRingEquiv.toRingHom.comp
    { toFun := fun p => Matrix.fromBlocks p.1 0 0 p.2
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun p q => by simp [Matrix.fromBlocks_multiply]
      map_zero' := by simp
      map_add' := fun p q => by simp [Matrix.fromBlocks_add] }

variable {k a b}

theorem blk_apply (p : Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k) :
    blk k a b p = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.1 0 0 p.2) :=
  rfl

theorem blk_smul (c : k) (p : Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k) :
    blk k a b (c • p) = c • blk k a b p := by
  rw [blk_apply, blk_apply]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, Prod.smul_fst,
    Prod.smul_snd]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem coe_sumRep {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      blk k a b ((ρ g : Matrix (Fin a) (Fin a) k), (ρ' g : Matrix (Fin b) (Fin b) k)) :=
  rfl

end Blocks

theorem isNilpotent_pair {R S : Type*} [MonoidWithZero R] [MonoidWithZero S] {x : R} {y : S}
    (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x, y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  exact ⟨m + n, Prod.ext (by simp [pow_add, hm]) (by simp [pow_add, hn])⟩

theorem exp_pair {R S : Type*} [Ring R] [Ring S] [Module ℚ R] [Module ℚ S] {x : R} {y : S}
    (hx : IsNilpotent x) (hy : IsNilpotent y) : exp (x, y) = (exp x, exp y) := by
  have hp := isNilpotent_pair hx hy
  exact Prod.ext (map_exp hp (RingHom.fst R S)) (map_exp hp (RingHom.snd R S))

def eqv (a b : ℕ) : ((Fin a → ℂ) × (Fin b → ℂ)) ≃ₗ[ℂ] (Fin (a + b) → ℂ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℂ ℂ).symm.trans
    (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)

theorem eqv_toEndC {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a b : ℕ}
    (M : Matrix (Fin a) (Fin a) (Qbar l)) (M' : Matrix (Fin b) (Fin b) (Qbar l))
    (v : (Fin a → ℂ) × (Fin b → ℂ)) :
    eqv a b ((toEndC ι M).prodMap (toEndC ι M') v) = toEndC ι (blk _ a b (M, M')) (eqv a b v) := by
  obtain ⟨v1, v2⟩ := v
  funext i
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  simp only [eqv, LinearEquiv.trans_apply, toEndC_apply, blk_apply, Matrix.reindex_apply,
    Matrix.toLin'_apply, LinearMap.prodMap_apply, LinearEquiv.funCongrLeft_apply]
  rw [← Matrix.submatrix_map, Matrix.submatrix_mulVec_equiv]
  rcases k with k | k <;> simp [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Function.comp_def,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {l : ℕ} [Fact l.Prime] {a b : ℕ}

theorem isMonodromy_sum {t : Ine (F := E) A →* Multiplicative ℤ_[l]}
    {ρ : G E Ω →* GL (Fin a) (Qbar l)} {ρ' : G E Ω →* GL (Fin b) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {N' : Matrix (Fin b) (Fin b) (Qbar l)}
    (hN : IsMonodromy t ρ N) (hN' : IsMonodromy t ρ' N') :
    IsMonodromy t (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') (blk _ a b (N, N')) := by
  obtain ⟨h1, U, hU, H⟩ := hN
  obtain ⟨h1', U', hU', H'⟩ := hN'
  have hp := isNilpotent_pair h1 h1'
  refine ⟨hp.map _, U ⊓ U', hU.inter hU', fun σ hσ => ?_⟩
  rw [coe_sumRep, H σ hσ.1, H' σ hσ.2, ← blk_smul, ← map_exp (hp.smul _), Prod.smul_mk,
    exp_pair (h1.smul _) (h1'.smul _)]

theorem wdMat_sum {t : Ine (F := E) A →* Multiplicative ℤ_[l]} {φ : Weil h} (hφ : deg φ = 1)
    {ρ : G E Ω →* GL (Fin a) (Qbar l)} {ρ' : G E Ω →* GL (Fin b) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {N' : Matrix (Fin b) (Fin b) (Qbar l)}
    (h1 : IsNilpotent N) (h1' : IsNilpotent N') (g : Weil h) :
    wdMat t hφ (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') (blk _ a b (N, N')) g =
      blk _ a b (wdMat t hφ ρ N g, wdMat t hφ ρ' N' g) := by
  have hp := isNilpotent_pair h1 h1'
  rw [wdMat, wdMat, wdMat, coe_sumRep, ← blk_smul, ← map_exp (hp.smul _), ← map_mul, Prod.smul_mk,
    exp_pair (h1.smul _) (h1'.smul _)]
  rfl

theorem isFrobSS_sum {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    {ρ₁ : Weil h → Module.End ℂ V} {N₁ : Module.End ℂ V} {x : WDRep h V}
    {ρ₂ : Weil h → Module.End ℂ V'} {N₂ : Module.End ℂ V'} {y : WDRep h V'}
    (hx : IsFrobSS ρ₁ N₁ x) (hy : IsFrobSS ρ₂ N₂ y) :
    IsFrobSS (fun g => (ρ₁ g).prodMap (ρ₂ g)) (N₁.prodMap N₂) (x.sum y) := by
  refine ⟨by rw [WDRep.sum_N, hx.1, hy.1], fun g => ⟨?_, ?_⟩⟩
  · rw [WDRep.sum_ρ]
    have hc : Commute ((x.ρ g, y.ρ g) : Module.End ℂ V × Module.End ℂ V') (ρ₁ g, ρ₂ g) :=
      Prod.ext (hx.2 g).1.eq (hy.2 g).1.eq
    exact hc.map (LinearMap.prodMapRingHom ℂ V V')
  · rw [WDRep.sum_ρ]
    have hn := (isNilpotent_pair (hx.2 g).2 (hy.2 g).2).map (LinearMap.prodMapRingHom ℂ V V')
    have e : (ρ₁ g).prodMap (ρ₂ g) - (x.ρ g).prodMap (y.ρ g) =
        LinearMap.prodMapRingHom ℂ V V' (ρ₁ g - x.ρ g, ρ₂ g - y.ρ g) := by
      rw [← Prod.mk_sub_mk, map_sub]; rfl
    show IsNilpotent ((ρ₁ g).prodMap (ρ₂ g) - (x.ρ g).prodMap (y.ρ g))
    rw [e]; exact hn

theorem wdOf_sumRep (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ)
    (ρ : G E Ω →* GL (Fin a) (Qbar l)) (ρ' : G E Ω →* GL (Fin b) (Qbar l))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)))
    (hc' : Continuous fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))) :
    wdOf h hl ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') = (wdOf h hl ι ρ).lpSum (wdOf h hl ι ρ') := by
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hc
  obtain ⟨N', hN'⟩ := exists_isMonodromy h hl ht hc'
  have hS := isMonodromy_sum hN hN'
  obtain ⟨x, hx⟩ := hN.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  obtain ⟨y, hy⟩ := hN'.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  obtain ⟨z, hz⟩ := hS.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  rw [IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N, x, hN, hx, rfl⟩,
    IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N', y, hN', hy, rfl⟩,
    IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, _, z, hS, hz, rfl⟩, WD.lpSum_mk]
  refine (WD.sound ((isFrobSS_sum hx hy).iso hz (eqv a b) (fun g v => ?_) fun v => ?_)).symm
  · rw [wdMat_sum deg_frob hN.1 hN'.1]
    exact eqv_toEndC ι _ _ v
  · exact eqv_toEndC ι _ _ v

end GlobalTheory.WeilDeligne.SumParam

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.WeilDeligne.wdOf_sumRep_awayFrom : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a b : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l)) (w : PlE D.host) (hw : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') = (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ).lpSum (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ') :=
  fun D l _ ι a b ρ ρ' w hw hc hc' =>
    GlobalTheory.WeilDeligne.SumParam.wdOf_sumRep (h := D.nd.plOm.2 w) hw ι ρ ρ' hc hc'
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepSumRepAwayFromLHostStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligneParamOfLadicRep_sumRep_awayFrom_l_host : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a b : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l)) (w : PlE D.host) (hw : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') = (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ).lpSum (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ') := by
  first | exact @GlobalTheory.WeilDeligne.wdOf_sumRep_awayFrom | exact GlobalTheory.WeilDeligne.wdOf_sumRep_awayFrom | (intros; apply GlobalTheory.WeilDeligne.wdOf_sumRep_awayFrom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqAlgebraMapOfCharpoly
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent

namespace GlobalTheory.WeilDeligne.InertiaSplit

variable {l : ℕ} [Fact l.Prime]

theorem toEndC_coord (ι : Qbar l ≃+* ℂ) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Qbar l)) (v : n → Qbar l) :
    toEndC ι M (fun k => ι (v k)) = fun i => ι ((M.mulVec v) i) := by
  funext i
  rw [toEndC_apply, Matrix.toLin'_apply]
  exact (RingHom.map_mulVec ι.toRingHom M v i).symm

theorem mem_of_exp (ι : Qbar l ≃+* ℂ) {n : Type} [Fintype n] [DecidableEq n]
    (S : Submodule ℂ (n → ℂ)) {M : Matrix n n (Qbar l)} (hM : IsNilpotent M)
    (hS : ∀ v ∈ S, toEndC ι M v ∈ S) : ∀ v ∈ S, toEndC ι (exp M) v ∈ S := by
  obtain ⟨k, hk⟩ := hM
  intro v hv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [exp_eq_sum hk, map_sum, LinearMap.sum_apply]
  refine S.sum_mem fun i hi => ?_
  clear hi
  rw [map_rat_smul, LinearMap.smul_apply, map_pow]
  refine S.smul_of_tower_mem _ ?_
  induction i with
  | zero => simpa using hv
  | succ i ih => rw [pow_succ', mul_apply_eq_comp]; exact hS _ ih

theorem exp_apply_of_eq_zero (ι : Qbar l ≃+* ℂ) {n : Type} [Fintype n] [DecidableEq n]
    {M : Matrix n n (Qbar l)} (hM : IsNilpotent M) {v : n → ℂ} (hv : toEndC ι M v = 0) :
    toEndC ι (exp M) v = v := by
  obtain ⟨k, hk⟩ := hM
  set_option synthInstance.maxHeartbeats 100000 in
    rw [exp_eq_sum (k := k + 1) (pow_eq_zero_of_le (Nat.le_succ k) hk), Finset.sum_range_succ', map_add (f := _),
    map_sum, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_eq_zero]
  · simp
  · intro i _
    rw [map_rat_smul, LinearMap.smul_apply, map_pow, _root_.pow_succ, mul_apply_eq_comp, hv, map_zero,
      smul_zero]

theorem eq_algebraMap_of_charpoly {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {x : Module.End ℂ V} (hs : x.IsSemisimple) {z : ℂ}
    (hc : x.charpoly = (X - C z) ^ finrank ℂ V) : x = algebraMap ℂ (Module.End ℂ V) z := by
  have h0 := LinearMap.aeval_self_charpoly x
  rw [hc, map_pow, map_sub, aeval_X, aeval_C] at h0
  have hs' : (x - algebraMap ℂ (Module.End ℂ V) z).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hs
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs')

def pull (ι : Qbar l ≃+* ℂ) {a n m : ℕ} (f : (Fin a → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ)) :
    (Fin a → Qbar l) ≃ₗ[Qbar l] (Fin n → Qbar l) × (Fin m → Qbar l) where
  toFun v := (fun j => ι.symm ((f (fun k => ι (v k))).1 j), fun j => ι.symm ((f (fun k => ι (v k))).2 j))
  invFun y := fun k => ι.symm (f.symm (fun j => ι (y.1 j), fun j => ι (y.2 j)) k)
  map_add' v v' := by
    have e : (fun k => ι ((v + v') k)) = (fun k => ι (v k)) + fun k => ι (v' k) := by
      funext k; simp
    simp only [e, map_add (f := _)]
    ext j <;> simp
  map_smul' c v := by
    have e : (fun k => ι ((c • v) k)) = ι c • fun k => ι (v k) := by funext k; simp
    simp only [e, map_smul]
    ext j <;> simp
  left_inv v := by
    funext k; simp
  right_inv y := by
    ext j <;> simp

theorem pull_apply (ι : Qbar l ≃+* ℂ) {a n m : ℕ} (f : (Fin a → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ))
    (v : Fin a → Qbar l) :
    pull ι f v = (fun j => ι.symm ((f (fun k => ι (v k))).1 j),
      fun j => ι.symm ((f (fun k => ι (v k))).2 j)) := rfl

theorem pull_fst_eq_zero (ι : Qbar l ≃+* ℂ) {a n m : ℕ} (f : (Fin a → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ))
    (v : Fin a → Qbar l) : (pull ι f v).1 = 0 ↔ (f (fun k => ι (v k))).1 = 0 := by
  rw [pull_apply]
  constructor
  · intro e; funext j; simpa using congrFun e j
  · intro e; funext j; simp [e]

theorem pull_snd_eq_zero (ι : Qbar l ≃+* ℂ) {a n m : ℕ} (f : (Fin a → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ))
    (v : Fin a → Qbar l) : (pull ι f v).2 = 0 ↔ (f (fun k => ι (v k))).2 = 0 := by
  rw [pull_apply]
  constructor
  · intro e; funext j; simpa using congrFun e j
  · intro e; funext j; simp [e]

end GlobalTheory.WeilDeligne.InertiaSplit

namespace GlobalTheory.WeilDeligne.InertiaSplit

variable {l : ℕ} [Fact l.Prime]
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem split_away (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (r : G E Ω →* GL (Fin a) (Qbar l))
    (hr : Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)))
    (x y : WD h) (hxy : wdOf (h := h) hl ι r = x.lpSum y) :
    ∃ U U' : Submodule (Qbar l) (Fin a → Qbar l), IsCompl U U' ∧ finrank (Qbar l) U = x.lpDim ∧
      finrank (Qbar l) U' = y.lpDim ∧
      (∀ σ ∈ Ine (F := E) A,
        (∀ v ∈ U, ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).mulVec v ∈ U) ∧
        (∀ v ∈ U', ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).mulVec v ∈ U')) ∧
      (y.mono0 → ∀ σ ∈ Ine (F := E) A, ∀ c : Qbar l, y.inePol σ = (X - C (ι c)) ^ y.lpDim →
        ∀ v ∈ U', ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).mulVec v = c • v) := by
  induction x using WD.ind with | hP n b => ?_
  induction y using WD.ind with | hP m c => ?_
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hr
  obtain ⟨z, hz⟩ := IsMonodromy.exists_isFrobSS hl ht hN (deg_frob (h := h)) ι
  have e : wdOf (h := h) hl ι r = WD.mk z := by
    have hz' : IsWDOf ι r (WD.mk z) := ⟨_, ht, _, deg_frob, N, z, hN, hz, rfl⟩
    have hex : ∃ x : WD h, IsWDOf ι r x := ⟨WD.mk z, hz'⟩
    rw [wdOf, dite_eq_left hex]
    exact IsWDOf.unique hl hex.choose_spec hz'
  rw [e, WD.lpSum_mk, WD.mk_eq_mk] at hxy
  obtain ⟨f, hfρ, hfN⟩ := hxy

  have hin : ∀ σ (hσ : σ ∈ Ine (F := E) A) (u : Fin a → ℂ),
      toEndC ι ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) u =
        z.ρ (ineIncl h ⟨σ, hσ⟩) (toEndC ι (exp (tval (tameL h hl) ⟨σ, hσ⟩ • N)) u) := by
    intro σ hσ u
    have hm : ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) =
        wdMat (tameL h hl) (deg_frob (h := h)) r N (ineIncl h ⟨σ, hσ⟩) *
          exp (tval (tameL h hl) ⟨σ, hσ⟩ • N) := by
      rw [wdMat_ineIncl, mul_assoc, ← exp_add_smul hN.1, neg_add_cancel, zero_smul,
        IsNilpotent.exp_zero, mul_one]
    rw [hm, map_mul, mul_apply_eq_comp, ← hN.rep_apply hl ht deg_frob ι,
      ← hz.ρ_ineIncl (hN.isSmooth_rep hl ht deg_frob ι)]

  have stρ2 : ∀ g u, (f u).2 = 0 → (f (z.ρ g u)).2 = 0 := fun g u hu => by
    rw [hfρ]; simp [hu]
  have stρ1 : ∀ g u, (f u).1 = 0 → (f (z.ρ g u)).1 = 0 := fun g u hu => by
    rw [hfρ]; simp [hu]
  have stN2 : ∀ u, (f u).2 = 0 → (f (z.N u)).2 = 0 := fun u hu => by
    rw [hfN]; simp [hu]
  have stN1 : ∀ u, (f u).1 = 0 → (f (z.N u)).1 = 0 := fun u hu => by
    rw [hfN]; simp [hu]
  have ste2 : ∀ (s : Qbar l) u, (f u).2 = 0 → (f (toEndC ι (exp (s • N)) u)).2 = 0 := by
    intro s u hu
    have := mem_of_exp ι (LinearMap.ker ((LinearMap.snd ℂ (Fin n → ℂ) (Fin m → ℂ)).comp
      (f : (Fin a → ℂ) →ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ)))) (hN.1.smul s) (fun v hv => by
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply,
          LinearEquiv.coe_coe] at hv ⊢
        rw [toEndC_smul, LinearMap.smul_apply, ← hz.1, map_smul, Prod.smul_snd, stN2 v hv, smul_zero])
      u (by simpa using hu)
    simpa using this
  have ste1 : ∀ (s : Qbar l) u, (f u).1 = 0 → (f (toEndC ι (exp (s • N)) u)).1 = 0 := by
    intro s u hu
    have := mem_of_exp ι (LinearMap.ker ((LinearMap.fst ℂ (Fin n → ℂ) (Fin m → ℂ)).comp
      (f : (Fin a → ℂ) →ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ)))) (hN.1.smul s) (fun v hv => by
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply,
          LinearEquiv.coe_coe] at hv ⊢
        rw [toEndC_smul, LinearMap.smul_apply, ← hz.1, map_smul, Prod.smul_fst, stN1 v hv, smul_zero])
      u (by simpa using hu)
    simpa using this

  have hC : IsCompl (LinearMap.ker (LinearMap.snd (Qbar l) (Fin n → Qbar l) (Fin m → Qbar l)))
      (LinearMap.ker (LinearMap.fst (Qbar l) (Fin n → Qbar l) (Fin m → Qbar l))) := by
    rw [← LinearMap.range_inl, ← LinearMap.range_inr]
    exact LinearMap.isCompl_range_inl_inr
  have hC' := (Submodule.orderIsoMapComap (pull ι f).symm).isCompl hC
  simp only [Submodule.orderIsoMapComap_apply] at hC'
  have memU : ∀ v : Fin a → Qbar l, v ∈ (LinearMap.ker (LinearMap.snd (Qbar l) (Fin n → Qbar l) (Fin m → Qbar l))).map
      ((pull ι f).symm : (Fin n → Qbar l) × (Fin m → Qbar l) →ₗ[Qbar l] (Fin a → Qbar l)) ↔ (f (fun k => ι (v k))).2 = 0 := fun v => by
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearMap.mem_ker, LinearMap.snd_apply,
      pull_snd_eq_zero]
  have memU' : ∀ v : Fin a → Qbar l, v ∈ (LinearMap.ker (LinearMap.fst (Qbar l) (Fin n → Qbar l) (Fin m → Qbar l))).map
      ((pull ι f).symm : (Fin n → Qbar l) × (Fin m → Qbar l) →ₗ[Qbar l] (Fin a → Qbar l)) ↔ (f (fun k => ι (v k))).1 = 0 := fun v => by
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearMap.mem_ker, LinearMap.fst_apply,
      pull_fst_eq_zero]
  refine ⟨_, _, hC', ?_, ?_, fun σ hσ => ⟨fun v hv => ?_, fun v hv => ?_⟩, ?_⟩
  · rw [WD.lpDim_mk, Module.finrank_fin_fun, LinearEquiv.finrank_map_eq, ← LinearMap.range_inl,
      LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_fin_fun]
  · rw [WD.lpDim_mk, Module.finrank_fin_fun, LinearEquiv.finrank_map_eq, ← LinearMap.range_inr,
      LinearMap.finrank_range_of_inj LinearMap.inr_injective, Module.finrank_fin_fun]
  · rw [memU] at hv ⊢
    rw [← toEndC_coord, hin σ hσ]
    exact stρ2 _ _ (ste2 _ _ hv)
  · rw [memU'] at hv ⊢
    rw [← toEndC_coord, hin σ hσ]
    exact stρ1 _ _ (ste1 _ _ hv)
  · intro hm σ hσ c0 hc v hv
    rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hm
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk] at hc
    have hsc := eq_algebraMap_of_charpoly (c.semisimple _) hc
    rw [memU'] at hv
    set u : Fin a → ℂ := fun k => ι (v k) with hu
    have hNu : z.N u = 0 := by
      rw [← f.map_eq_zero_iff, hfN]
      ext j <;> simp [hv, hm]
    suffices H : (fun i => ι ((((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).mulVec v) i)) =
        fun i => ι ((c0 • v) i) by
      funext i; exact ι.injective (congrFun H i)
    have hcu : (fun i => ι ((c0 • v) i)) = ι c0 • u := by funext i; simp [hu]
    rw [← toEndC_coord, hin σ hσ, exp_apply_of_eq_zero ι (hN.1.smul _)
      (by rw [toEndC_smul, LinearMap.smul_apply, ← hz.1, hNu, smul_zero]), hcu]
    apply f.injective
    rw [hfρ, map_smul]
    refine Prod.ext ?_ ?_
    · rw [WDRep.sum_ρ, LinearMap.prodMap_apply, Prod.smul_fst, hv, map_zero, smul_zero]
    · rw [WDRep.sum_ρ, LinearMap.prodMap_apply, Prod.smul_snd, hsc, Module.algebraMap_end_apply]

end GlobalTheory.WeilDeligne.InertiaSplit

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRepParabolicChar
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsKillTensor
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.AugmentationEigenvector

section General

variable {K X Y : Type} [Group K] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

def aug (ψ : K →* ℂˣ) : MonoidAlgebra ℂ K →ₐ[ℂ] ℂ :=
  MonoidAlgebra.lift ℂ ℂ K ((Units.coeHom ℂ).comp ψ)

theorem aug_single (ψ : K →* ℂˣ) (g : K) (r : ℂ) :
    aug ψ (MonoidAlgebra.single g r) = r * (ψ g : ℂ) := by
  simp [aug]

theorem act_eigen (σ : Representation ℂ K X) (ψ : K →* ℂˣ) (y : X)
    (hy : ∀ g, σ g y = (ψ g : ℂ) • y) (c : MonoidAlgebra ℂ K) :
    σ.asAlgebraHom c y = aug ψ c • y := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, ha, hb, add_smul]
  | single g r => rw [aug_single, Representation.asAlgebraHom_single, LinearMap.smul_apply, hy, smul_smul]

theorem act_comm (σ : Representation ℂ K X) (τ : Representation ℂ K Y) (f : X →ₗ[ℂ] Y)
    (hf : ∀ g x, f (σ g x) = τ g (f x)) (c : MonoidAlgebra ℂ K) (x : X) :
    f (σ.asAlgebraHom c x) = τ.asAlgebraHom c (f x) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
  | single g r => simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, map_smul, hf]

theorem exists_kill [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    (σ : Representation ℂ K X) (ψ : K →* ℂˣ) (hσ : IsSmooth σ) (hψ : IsSmoothChar ψ)
    (h0 : ∀ z, (∀ g, σ g z = (ψ g : ℂ) • z) → z = 0) (z : X) :
    ∃ c, aug ψ c ≠ 0 ∧ σ.asAlgebraHom c z = 0 := by
  classical
  let π := SmGL.twist σ ψ⁻¹
  have hπ : IsSmooth π := isSmooth_twist hσ hψ.inv
  have hlc : IsLocallyConstant fun g : K => π g z := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have h : {g : K | π g z = z} ∈ nhds ((fun y => x⁻¹ * y) x) :=
      IsOpen.mem_nhds (hπ z) (by simp)
    filter_upwards [(continuous_const_mul x⁻¹).continuousAt.preimage_mem_nhds h] with y hy
    have hy' : π (x⁻¹ * y) z = z := hy
    calc π y z = π x (π (x⁻¹ * y) z) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = π x z := by rw [hy']
  have hfin := hlc.range_finite
  let O : Finset X := hfin.toFinset
  have hO : ∀ w, w ∈ O ↔ ∃ g, π g z = w := fun w => by simp [O]
  have hmem : ∀ g, ∀ w ∈ O, π g w ∈ O := fun g w hw => by
    obtain ⟨x, rfl⟩ := (hO w).1 hw
    exact (hO _).2 ⟨g * x, by rw [map_mul, Module.End.mul_apply]⟩
  have hinv : ∀ g, π g (∑ w ∈ O, w) = ∑ w ∈ O, w := fun g => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_nbij' (fun w => π g w) (fun w => π g⁻¹ w) (hmem g) (hmem g⁻¹)
      (fun w _ => ?_) (fun w _ => ?_) (fun _ _ => rfl)
    · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hz : ∑ w ∈ O, w = 0 := h0 _ fun g => by
    have h1 := hinv g
    have h2 : π g (∑ w ∈ O, w) = ((ψ g)⁻¹ : ℂˣ).val • σ g (∑ w ∈ O, w) := rfl
    rw [h2] at h1
    conv_rhs => rw [← h1]
    rw [smul_smul, Units.mul_inv, one_smul]
  choose s hs using fun w : O => (hO w).1 w.2
  refine ⟨∑ w : O, MonoidAlgebra.single (s w) ((ψ (s w))⁻¹ : ℂˣ).val, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [aug_single, Units.inv_mul]
    have : O.Nonempty := ⟨z, (hO z).2 ⟨1, by simp⟩⟩
    simpa using this.ne_empty
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply, ← hz, ← Finset.sum_coe_sort O]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Representation.asAlgebraHom_single, LinearMap.smul_apply]
    exact hs w

end General

section Tensor

variable {β : Type} [DecidableEq β] {Γ X : β → Type} [∀ j, Group (Γ j)] [∀ j, AddCommGroup (X j)]
  [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (Γ j) (X j)) (a : β) {K : Type} [Group K]
  (i : K →* Γ a)

def viaFactor : Representation ℂ K (⨂[ℂ] j, X j) :=
  (piTensor ρ).comp ((MonoidHom.mulSingle Γ a).comp i)

theorem viaFactor_tprod (x : ∀ j, X j) (g : K) (z : X a) :
    viaFactor ρ a i g (PiTensorProduct.tprod ℂ (Function.update x a z)) =
      PiTensorProduct.tprod ℂ (Function.update x a (ρ a (i g) z)) := by
  show piTensor ρ (Pi.mulSingle a (i g)) _ = _
  rw [piTensor_tprod]
  congr 1
  funext j
  by_cases h : j = a
  · subst h; simp
  · simp [Pi.mulSingle_eq_of_ne h, Function.update_of_ne h]

theorem viaFactor_alg (x : ∀ j, X j) (c : MonoidAlgebra ℂ K) (z : X a) :
    (viaFactor ρ a i).asAlgebraHom c (PiTensorProduct.tprod ℂ (Function.update x a z)) =
      PiTensorProduct.tprod ℂ
        (Function.update x a (Representation.asAlgebraHom ((ρ a).comp i) c z)) :=
  (act_comm ((ρ a).comp i) (viaFactor ρ a i) ((PiTensorProduct.tprod ℂ).toLinearMap x a)
    (fun g z => (viaFactor_tprod ρ a i x g z).symm) c z).symm

theorem exists_kill_tensor (ψ : K →* ℂˣ)
    (h : ∀ z, ∃ c, aug ψ c ≠ 0 ∧ Representation.asAlgebraHom ((ρ a).comp i) c z = 0)
    (v : ⨂[ℂ] j, X j) (b : MonoidAlgebra ℂ K) :
    ∃ c, aug ψ c ≠ 0 ∧
      (viaFactor ρ a i).asAlgebraHom c ((viaFactor ρ a i).asAlgebraHom b v) = 0 := by
  induction v using PiTensorProduct.induction_on generalizing b with
  | smul_tprod r x =>
    obtain ⟨c, hc, hc'⟩ := h (Representation.asAlgebraHom ((ρ a).comp i) b (x a))
    refine ⟨c, hc, ?_⟩
    rw [← Function.update_eq_self a x, map_smul, map_smul, viaFactor_alg, viaFactor_alg, hc',
      MultilinearMap.map_update_zero, smul_zero]
  | add v w hv hw =>
    obtain ⟨c, hc, hc'⟩ := hv b
    obtain ⟨d, hd, hd'⟩ := hw (c * b)
    refine ⟨d * c, by rw [map_mul]; exact mul_ne_zero hd hc, ?_⟩
    rw [map_mul, Module.End.mul_apply] at hd'
    rw [map_mul, Module.End.mul_apply, map_add (f := _), map_add (f := _), hc', zero_add, hd']

end Tensor

theorem exists_eigenvector (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type)
    [(j : β) → Fintype (m j)] [(j : β) → DecidableEq (m j)] (X : β → Type)
    [(j : β) → AddCommGroup (X j)] [(j : β) → Module ℂ (X j)]
    (ρ : (j : β) → Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y)
    (hρ : ∀ j, IsSmooth (ρ j)) (hχ : IsSmoothChar χ) (hs : IsSubquotient τ (piTensor ρ))
    (hy : y ≠ 0)
    (he : ∀ g ∈ KO k (m a),
      τ (Pi.mulSingle a g) y = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • y) :
    ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a),
      ρ a g z = ((χ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • z := by
  by_contra hne
  haveI : CompactSpace (KO k (m a)) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  let i := (KO k (m a)).subtype
  let ψ : KO k (m a) →* ℂˣ := χ.comp (Matrix.GeneralLinearGroup.det.comp i)
  have hψ : IsSmoothChar ψ :=
    hχ.comp _ (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  have h1 := exists_kill ((ρ a).comp i) ψ (isSmooth_comp (hρ a) i continuous_subtype_val) hψ
    fun z hz => by
      by_contra h
      exact hne ⟨z, h, fun g hg => hz ⟨g, hg⟩⟩
  obtain ⟨S, f, hf⟩ := hs
  obtain ⟨v, rfl⟩ := hf y
  obtain ⟨c, hc, hc'⟩ := exists_kill_tensor ρ a i ψ h1 v.1 1
  rw [map_one, Module.End.one_apply] at hc'
  let e : KO k (m a) →* Levi k m := (MonoidHom.mulSingle (fun j => GL (m j) k) a).comp i
  have h2 := act_comm (S.toRepresentation.comp e) (viaFactor ρ a i) S.toSubmodule.subtype
    (fun _ _ => rfl) c v
  have h3 : Representation.asAlgebraHom (S.toRepresentation.comp e) c v = 0 :=
    Subtype.ext (h2.trans hc')
  have h4 := act_comm (S.toRepresentation.comp e) (τ.comp e) f.toLinearMap
    (fun g x => f.isIntertwining _ _ (e g) x) c v
  rw [h3, map_zero, act_eigen (τ.comp e) ψ (f.toLinearMap v) (fun g => he g.1 g.2)] at h4
  exact hy ((smul_eq_zero.1 h4.symm).resolve_left hc)

end GlobalTheory.AugmentationEigenvector
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRepParabolicChar
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EigenFactor

section Avg

variable {H W W' : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Avg

section Tensor

variable {β : Type} [Fintype β] [DecidableEq β] {Γ X : β → Type} [∀ j, Group (Γ j)] [∀ j, AddCommGroup (X j)]
  [∀ j, Module ℂ (X j)]

end Tensor

theorem exists_eig_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type) [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] (X : β → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y), (∀ j, IsSmooth (ρ j)) → IsSmoothChar χ → IsSubquotient τ (piTensor ρ) → y ≠ 0 → (∀ g ∈ KO k (m a), τ (Pi.mulSingle a g) y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a), ρ a g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z := by
  first
  | exact @_root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector
  | exact _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector
  | (apply _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> assumption)
  | (intros; apply _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AugmentationEigenvector.exists_eigenvector ..)

end GlobalTheory.EigenFactor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRepParabolicCharStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_rep_parabolic_char : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (β : Type) [Fintype β] [DecidableEq β] (m : β → Type) [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)] (X : β → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (ρ : ∀ j, Representation ℂ (GL (m j) k) (X j)) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k m) Y) (a : β) (χ : kˣ →* ℂˣ) (y : Y), (∀ j, IsSmooth (ρ j)) → IsSmoothChar χ → IsSubquotient τ (piTensor ρ) → y ≠ 0 → (∀ g ∈ KO k (m a), τ (Pi.mulSingle a g) y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ z : X a, z ≠ 0 ∧ ∀ g ∈ KO k (m a), ρ a g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z := by
  first | exact @GlobalTheory.EigenFactor.exists_eig_factor | exact GlobalTheory.EigenFactor.exists_eig_factor | (intros; apply GlobalTheory.EigenFactor.exists_eig_factor <;> assumption)
end
end
