module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.LocalBasisChangeDecompCompatible
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.CrdLBwLe
section -- merged from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.IsCrdExists
section -- merged from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.LenLen2OfCoord
section -- merged from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.PairingAdjointness
section -- merged from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.PairingEqLimitPairing
section -- merged from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.PairingContinuityBound
namespace Formalism.L2.GlobalTheoryTheory.LemB

theorem len_equiv_semilinear {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] M') : Module.length R M = Module.length R' M' := by
  let e' : Submodule R M ≃o Submodule R' M' := Submodule.orderIsoMapComap e
  unfold Module.length
  congr 1
  exact Order.krullDim_eq_of_orderIso e'

noncomputable def quotEquivSL {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] M') (P : Submodule R M) (Q : Submodule R' M') (h : P.map (e : M →ₛₗ[σ] M') = Q) :
    (M ⧸ P) ≃ₛₗ[σ] (M' ⧸ Q) :=
  LinearEquiv.ofLinearMap
    (P.mapQ Q (e : M →ₛₗ[σ] M') (by rw [← h]; exact Submodule.le_comap_map _ _))
    (Q.mapQ P (e.symm : M' →ₛₗ[σ'] M) (by
      rw [← h]; rintro _ ⟨x, hx, rfl⟩
      show e.symm (e x) ∈ P
      rw [e.symm_apply_apply]; exact hx))
    (by ext x; simp) (by ext x; simp)

theorem len_quot_semilinear {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (f : M →ₛₗ[σ] M') (hf : Function.Injective f) (A B : Submodule R M) :
    Module.length R (A ⧸ B.comap A.subtype) =
      Module.length R' (A.map f ⧸ (B.map f).comap (A.map f).subtype) := by
  let eA : A ≃ₛₗ[σ] A.map f := Submodule.equivMapOfInjective f hf A
  refine len_equiv_semilinear (quotEquivSL eA _ _ ?_)
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨x, hxA⟩, hxB, hxy⟩
    exact ⟨x, hxB, congrArg Subtype.val hxy⟩
  · rintro ⟨x, hxB, hfx⟩
    obtain ⟨x', hx'A, hx'⟩ := hy
    have hxx : x = x' := hf (hfx.trans hx'.symm)
    subst hxx
    refine ⟨⟨x, hx'A⟩, hxB, ?_⟩
    apply Subtype.ext
    exact hfx

theorem len_pi_sum {R : Type*} [CommRing R] {G : Type*} [Fintype G] [DecidableEq G] {M : G → Type*}
    [∀ g, AddCommGroup (M g)] [∀ g, Module R (M g)] (A B : ∀ g, Submodule R (M g)) :
    Module.length R ((Submodule.pi Set.univ A) ⧸
        (Submodule.pi Set.univ B).comap (Submodule.pi Set.univ A).subtype) =
      ∑ g, Module.length R (A g ⧸ (B g).comap (A g).subtype) := by
  classical
  let φ : (Submodule.pi Set.univ A) →ₗ[R] (∀ g, A g ⧸ (B g).comap (A g).subtype) :=
    LinearMap.pi (fun g => ((B g).comap (A g).subtype).mkQ ∘ₗ
      (((LinearMap.proj g).comp (Submodule.pi Set.univ A).subtype).codRestrict (A g)
        (fun x => x.2 g (Set.mem_univ g))))
  have hφ : Function.Surjective φ := by
    intro y
    choose x hx using fun g => Submodule.Quotient.mk_surjective _ (y g)
    refine ⟨⟨fun g => (x g : M g), fun g _ => (x g).2⟩, ?_⟩
    funext g
    rw [← hx g]
    rfl
  have hker : LinearMap.ker φ =
      (Submodule.pi Set.univ B).comap (Submodule.pi Set.univ A).subtype := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi,
      Set.mem_univ, true_implies]
    rw [funext_iff]
    refine forall_congr' (fun g => ?_)
    change Submodule.Quotient.mk _ = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    rfl
  let e := (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hφ)
  rw [len_equiv_semilinear e]
  first
  | exact Module.length_pi
  | exact Module.length_pi_of_fintype _
  | simp [Module.length_pi]

end Formalism.L2.GlobalTheoryTheory.LemB
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

section Cls

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
  [∀ τ, DecidableEq (κ τ)] (b : ∀ τ, κ τ → MvPolynomial (Fin N × Fin N) ℂ) (O : Subring ℂ)

def tenSpan : Submodule O (MvPolynomial (ι × Fin N × Fin N) ℂ) :=
  Submodule.span O (Set.range fun g : (∀ τ, κ τ) => Formalism.L2.Forms.ten (fun τ => b τ (g τ)))

def gRest (g : ∀ τ, κ τ) : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1 := fun τ => g τ.1

def gExt (g : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1) (k : κ τ₀) : ∀ τ, κ τ :=
  fun τ => if h : τ = τ₀ then (by subst h; exact k) else g ⟨τ, h⟩

theorem gRest_gExt (g : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1) (k : κ τ₀) : gRest τ₀ κ (gExt τ₀ κ g k) = g := by
  funext τ
  unfold gRest gExt
  rw [dite_eq_right τ.2]

theorem gExt_self (g : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1) (k : κ τ₀) : gExt τ₀ κ g k τ₀ = k := by
  unfold gExt
  rw [dite_eq_left rfl]

theorem ten_eq_psi (g : ∀ τ, κ τ) :
    Formalism.L2.Forms.ten (fun τ => b τ (g τ)) = mvPolynomialProductExtension τ₀ κ b (Pi.single (gRest τ₀ κ g) (b τ₀ (g τ₀))) := by
  classical
  unfold Formalism.L2.Forms.ten
  simp only [mvPolynomialProductExtension, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single (gRest τ₀ κ g)]
  · rw [Pi.single_eq_same]
    exact Fintype.prod_eq_mul_prod_subtype_ne _ τ₀
  · intro g' _ hg'
    rw [Pi.single_eq_of_ne hg', map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem tenSpan_eq_psi (Λ : Submodule O (MvPolynomial (Fin N × Fin N) ℂ))
    (hΛ : Λ = Submodule.span O (Set.range (b τ₀))) :
    tenSpan κ b O = (Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ).map
      ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) := by
  classical
  apply le_antisymm
  · rw [tenSpan, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    dsimp only
    rw [ten_eq_psi τ₀ κ b g]
    refine ⟨Pi.single (gRest τ₀ κ g) (b τ₀ (g τ₀)), ?_, rfl⟩
    intro g' _
    by_cases hg : g' = gRest τ₀ κ g
    · subst hg
      rw [Pi.single_eq_same, hΛ]
      exact Submodule.subset_span ⟨g τ₀, rfl⟩
    · rw [Pi.single_eq_of_ne hg]
      exact Λ.zero_mem
  · rintro _ ⟨h, hh, rfl⟩
    have hsingle : ∀ (g' : ∀ τ : {τ // τ ≠ τ₀}, κ τ.1) (v : MvPolynomial (Fin N × Fin N) ℂ), v ∈ Λ →
        mvPolynomialProductExtension τ₀ κ b (Pi.single g' v) ∈ tenSpan κ b O := by
      intro g' v hv
      have hle : Λ ≤ (tenSpan κ b O).comap (((mvPolynomialProductExtension τ₀ κ b).restrictScalars O).comp
          (LinearMap.single O (fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => MvPolynomial (Fin N × Fin N) ℂ) g')) := by
        rw [hΛ, Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        have h1 := ten_eq_psi τ₀ κ b (gExt τ₀ κ g' k)
        rw [gRest_gExt, gExt_self] at h1
        show mvPolynomialProductExtension τ₀ κ b (Pi.single g' (b τ₀ k)) ∈ tenSpan κ b O
        rw [← h1]
        exact Submodule.subset_span ⟨gExt τ₀ κ g' k, rfl⟩
      exact hle hv
    have hsum : h = ∑ g', Pi.single g' (h g') := (Finset.univ_sum_single h).symm
    show mvPolynomialProductExtension τ₀ κ b h ∈ tenSpan κ b O
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    exact Submodule.sum_mem _ fun g' _ => hsingle g' (h g') (hh g' (Set.mem_univ _))

theorem psi_subP (o : ι → Matrix (Fin N) (Fin N) ℂ) (ho : ∀ τ, τ ≠ τ₀ → o τ = 1)
    (h : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) → MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.L2.Forms.subP o (mvPolynomialProductExtension τ₀ κ b h) = mvPolynomialProductExtension τ₀ κ b (fun g => Formalism.GradedWeylDivisibility.rowAct ℂ (o τ₀) (h g)) := by
  have hren : ∀ (τ : ι) (q : MvPolynomial (Fin N × Fin N) ℂ),
      Formalism.L2.Forms.subP o (rename (Prod.mk τ) q) = rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (o τ) q) := by
    intro τ q
    have h1 : (Formalism.L2.Forms.subP o).comp (rename (Prod.mk τ)) = (rename (Prod.mk τ)).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (o τ)) := by
      apply MvPolynomial.algHom_ext
      intro v
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Formalism.L2.Forms.subP, Formalism.GradedWeylDivisibility.rowAct, rename_X, map_sum]
    exact AlgHom.congr_fun h1 q
  have hone : ∀ q : MvPolynomial (Fin N × Fin N) ℂ, Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) q = q := by
    intro q
    have h1 : Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (1 : Matrix (Fin N) (Fin N) ℂ) = AlgHom.id ℂ _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
    rw [h1, AlgHom.id_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mvPolynomialProductExtension, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul, map_prod, hren]
  refine Finset.sum_congr rfl fun g _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [ho τ.1 τ.2, hone]

theorem map_psi_pi (L : MvPolynomial (Fin N × Fin N) ℂ →ₗ[O] MvPolynomial (Fin N × Fin N) ℂ)
    (L' : MvPolynomial (ι × Fin N × Fin N) ℂ →ₗ[O] MvPolynomial (ι × Fin N × Fin N) ℂ)
    (hc : ∀ h, L' (mvPolynomialProductExtension τ₀ κ b h) = mvPolynomialProductExtension τ₀ κ b (fun g => L (h g)))
    (Λ : Submodule O (MvPolynomial (Fin N × Fin N) ℂ)) :
    ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ).map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).map L' =
      (Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ.map L).map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) := by
  classical
  ext x
  constructor
  · rintro ⟨y, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨fun g => L (h g), fun g _ => ⟨h g, hh g (Set.mem_univ _), rfl⟩, ?_⟩
    exact (hc h).symm
  · rintro ⟨h', hh', rfl⟩
    have hh'' : ∀ g, ∃ y ∈ Λ, L y = h' g := fun g => hh' g (Set.mem_univ _)
    choose h hh hhe using hh''
    refine ⟨mvPolynomialProductExtension τ₀ κ b h, ⟨h, fun g _ => hh g, rfl⟩, ?_⟩
    show L' (mvPolynomialProductExtension τ₀ κ b h) = mvPolynomialProductExtension τ₀ κ b h'
    rw [hc]
    congr 1
    funext g
    exact hhe g

abbrev scO (σ : Type) (c : ℂ) : MvPolynomial σ ℂ →ₗ[O] MvPolynomial σ ℂ :=
  (c • LinearMap.id : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ).restrictScalars O

theorem cls_len (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent ℂ (b τ)) (Λ : Submodule O (MvPolynomial (Fin N × Fin N) ℂ))
    (hΛ : Λ = Submodule.span O (Set.range (b τ₀))) (o : ι → Matrix (Fin N) (Fin N) ℂ) (ho : ∀ τ, τ ≠ τ₀ → o τ = 1)
    (c₁ c₂ : ℂ) :
    Module.length O
      ((((tenSpan κ b O).map ((Formalism.L2.Forms.subP o).toLinearMap.restrictScalars O)).map (scO O _ c₁)) ⧸
        ((tenSpan κ b O).map (scO O _ c₂)).comap
          (((tenSpan κ b O).map ((Formalism.L2.Forms.subP o).toLinearMap.restrictScalars O)).map (scO O _ c₁)).subtype) =
      (∏ τ : {τ // τ ≠ τ₀}, Fintype.card (κ τ.1)) •
        Module.length O (((Λ.map (mvPolynomialRowLinearMap O (o τ₀))).map (mvPolynomialScalingMap O c₁)) ⧸
          (Λ.map (mvPolynomialScalingMap O c₂)).comap ((Λ.map (mvPolynomialRowLinearMap O (o τ₀))).map (mvPolynomialScalingMap O c₁)).subtype) := by
  have hrow : (tenSpan κ b O).map ((Formalism.L2.Forms.subP o).toLinearMap.restrictScalars O) =
      (Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ.map (mvPolynomialRowLinearMap O (o τ₀))).map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) := by
    rw [tenSpan_eq_psi τ₀ κ b O Λ hΛ]
    exact map_psi_pi τ₀ κ b O (mvPolynomialRowLinearMap O (o τ₀)) ((Formalism.L2.Forms.subP o).toLinearMap.restrictScalars O)
      (fun h => psi_subP τ₀ κ b o ho h) Λ
  have hsc : ∀ (c : ℂ) (Λ' : Submodule O (MvPolynomial (Fin N × Fin N) ℂ)),
      ((Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ').map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O)).map (scO O _ c) =
      (Submodule.pi Set.univ fun _ : (∀ τ : {τ // τ ≠ τ₀}, κ τ.1) => Λ'.map (mvPolynomialScalingMap O c)).map
        ((mvPolynomialProductExtension τ₀ κ b).restrictScalars O) := by
    intro c Λ'
    refine map_psi_pi τ₀ κ b O (mvPolynomialScalingMap O c) (scO O _ c) (fun h => ?_) Λ'
    show c • mvPolynomialProductExtension τ₀ κ b h = mvPolynomialProductExtension τ₀ κ b (fun g => c • h g)
    rw [← map_smul]
    rfl
  rw [hrow, hsc, tenSpan_eq_psi τ₀ κ b O Λ hΛ, hsc]
  exact length_quot_map_positionMap τ₀ κ b hb O _ _

end Cls

end Formalism.L2.GlobalTheoryTheory.LemB
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable (D : D7)

def intSubm (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) :
    Submodule (bwA_Ow D w) (MvPolynomial (D.what₂.Tau × Fin N × Fin N) ℂ) :=
  Submodule.span (bwA_Ow D w) (Formalism.L2.Forms.IntSpan D w lam : Set _)

theorem intSubm_eq (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) (κ : D.what₂.Tau → Type)
    [∀ τ, Fintype (κ τ)] (b : ∀ τ, Module.Basis (κ τ) ℤ (delSq ℤ N (lam τ))) :
    intSubm D w lam = tenSpan κ (fun τ k => MvPolynomial.map (Int.castRingHom ℂ)
      ((b τ k : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ)) (bwA_Ow D w) := by
  classical
  unfold intSubm Formalism.L2.Forms.IntSpan tenSpan Formalism.L2.Forms.ten bwA_Ow
  apply le_antisymm
  · rw [Submodule.span_le]
    intro p hp
    rw [SetLike.mem_coe] at hp
    induction hp using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hx
      have hfe : ∀ τ, rename (Prod.mk τ) (map (Int.castRingHom ℂ) (f τ)) =
          ∑ k, (b τ).repr ⟨f τ, hf τ⟩ k • rename (Prod.mk τ) (map (Int.castRingHom ℂ)
            ((b τ k : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ)) := by
        intro τ
        have h2 := congrArg Subtype.val ((b τ).sum_repr ⟨f τ, hf τ⟩)
        rw [Submodule.coe_sum] at h2
        simp only [Submodule.coe_smul] at h2
        conv_lhs => rw [← h2]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum]
        simp only [map_zsmul]
      simp only [hfe]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      refine Submodule.smul_mem _ (⟨_, Subring.mem_map.2 ⟨r, hr, rfl⟩⟩ : ↥(Subring.map D.what₂.embLL (intW D.what₂.places w))) ?_
      refine Submodule.sum_mem _ fun g _ => ?_
      simp only [zsmul_eq_mul, Finset.prod_mul_distrib, ← Int.cast_prod]
      rw [← zsmul_eq_mul]
      apply zsmul_mem
      apply Submodule.subset_span
      exact ⟨g, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | neg x _ hx => exact Submodule.neg_mem _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    apply Submodule.subset_span
    apply AddSubgroup.subset_closure
    refine ⟨1, fun τ => ((b τ (g τ) : delSq ℤ N (lam τ)) : MvPolynomial (Fin N × Fin N) ℤ), Subring.one_mem _,
      fun τ => (b τ (g τ)).2, ?_⟩
    rw [map_one, one_smul]

theorem bwA_span_basis (O : Subring ℂ) {N : ℕ} (ν : Fin N → ℕ) {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν)) :
    bwA_span (K := ℂ) O le_rfl ν = Submodule.span O (Set.range fun k => MvPolynomial.map (Int.castRingHom ℂ)
      ((b k : Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν) : MvPolynomial (Fin N × Fin N) ℤ)) := by
  unfold bwA_span
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have h2 := congrArg Subtype.val (b.sum_repr ⟨p, hp⟩)
    rw [Submodule.coe_sum] at h2
    simp only [Submodule.coe_smul] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h2, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    apply zsmul_mem
    apply Submodule.subset_span
    exact ⟨i, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span (Set.mem_image_of_mem _ (b k).2)

variable (u : D.what₂.Word)

theorem cls_len_D (A : AtTTied u) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (v : (D.mem u).A.vT) (Lv : LvTied u A 0 (Nat.zero_le _)) (c : (D.mem u).C.cls 0)
    (hLc0 : clsCrd D u 0 (Nat.zero_le _) c ≤ Ld D u 0 (Nat.zero_le _) c) (B B' : GL (Fin (D.R.N 0)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk A 0 (Nat.zero_le _) v c : Set _) B')
    (hunit : ((((B⁻¹ * B' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w ∧
      ((D.mem u).A.T : ℂ) * (((((B⁻¹ * B' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det)⁻¹ ∈ bwA_Ow D w) :
    ∃ n : ℕ, Module.length (bwA_Ow D w)
      ((((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) B B')).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift))) ⧸
        ((intSubm D w ((D.fm u).lam 0)).map
            (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)))).comap
          (((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) B B')).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) B B' ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift))).subtype) = n ∧
      (D.R.k : ℚ) * n = (D.what₂.places.ramIdx w : ℚ) *
        ((∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) : ℕ) : ℚ) *
        ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) := by
  classical
  choose κ hκ b0 _ _ _ _ using fun τ => weyl_homogeneous_basis (r := D.R.N 0) (n := D.R.N 0) le_rfl ((D.fm u).lam 0 τ).natW
    (dominant_natWeight_antitone ((D.fm u).lam 0 τ))
  let _ := hκ
  let b : ∀ τ, Module.Basis (κ τ) ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) := b0
  obtain ⟨n, hn, hrel⟩ := length_factor_local_basis D u A w hw v Lv c hLc0 B B' hB hB' hunit _ rfl
  have hli : ∀ τ, τ ≠ (D.fm u).tauOf w v → LinearIndependent ℂ (fun k => MvPolynomial.map (Int.castRingHom ℂ)
      ((b τ k : delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) : MvPolynomial (Fin (D.R.N 0) × Fin (D.R.N 0)) ℤ)) := fun τ _ =>
    weyl_basis_lin_indep_field le_rfl ((D.fm u).lam 0 τ).natW (dominant_natWeight_antitone ((D.fm u).lam 0 τ)) ℂ (b0 τ)
  have ho : ∀ τ, τ ≠ (D.fm u).tauOf w v → bwA_N D ((D.fm u).tauOf w v) B B' τ = 1 := by
    intro τ h
    unfold bwA_N
    rw [ite_eq_right h]
  have hcard : ∀ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) = Fintype.card (κ τ) := fun τ =>
    Module.finrank_eq_card_basis (b τ)
  refine ⟨(∏ τ : {τ // τ ≠ (D.fm u).tauOf w v}, Fintype.card (κ τ.1)) * n, ?_, ?_⟩
  · rw [intSubm_eq D w ((D.fm u).lam 0) κ b]
    refine (cls_len ((D.fm u).tauOf w v) κ _ (bwA_Ow D w) hli _
      (bwA_span_basis (bwA_Ow D w) ((D.fm u).lam 0 ((D.fm u).tauOf w v)).natW (b0 ((D.fm u).tauOf w v)))
      (bwA_N D ((D.fm u).tauOf w v) B B') ho _ _).trans ?_
    rw [hn]
    simp
  · have hprod : (∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ))) =
        Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 ((D.fm u).tauOf w v))) *
          ∏ τ : {τ // τ ≠ (D.fm u).tauOf w v}, Fintype.card (κ τ.1) := by
      simp only [hcard]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ((D.fm u).tauOf w v))]
      congr 1
      exact Finset.prod_subtype (Finset.univ.erase ((D.fm u).tauOf w v)) (p := fun τ => τ ≠ (D.fm u).tauOf w v)
        (fun x => by simp) (fun τ => Fintype.card (κ τ))
    rw [hprod]
    push_cast
    linear_combination (∏ τ : {τ // τ ≠ (D.fm u).tauOf w v}, (Fintype.card (κ τ.1) : ℚ)) * hrel

end Formalism.L2.GlobalTheoryTheory.LemB
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable (D : D7)

def owEquiv (w : D.what₂.places.Pl) : Ow D w ≃+* bwA_Ow D w :=
  Subring.equivMapOfInjective (intW D.what₂.places w) D.what₂.embLL D.what₂.embLL.injective

instance owPair (w : D.what₂.places.Pl) :
    RingHomInvPair ((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w)
      ((owEquiv D w).symm : bwA_Ow D w →+* Ow D w) :=
  RingHomInvPair.of_ringEquiv (owEquiv D w)

instance owPair' (w : D.what₂.places.Pl) :
    RingHomInvPair ((owEquiv D w).symm : bwA_Ow D w →+* Ow D w)
      ((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w) where
  comp_eq := by ext x; simp
  comp_eq₂ := by ext x; simp

variable (u : D.what₂.Word)

theorem lenLen2_of_coord (A : AtTTied u) (Lv : LvTied u A 0 (Nat.zero_le _)) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (v : (D.mem u).A.vT)
    (hLc0 : ∀ c, clsCrd D u 0 (Nat.zero_le _) c ≤ Ld D u 0 (Nat.zero_le _) c)
    (B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c))
    (hB' : ∀ c, IsLocBasis (D.mem u).A.T (Lk A 0 (Nat.zero_le _) v c : Set _) (B' c))
    (hunit : ∀ c, (((((B c)⁻¹ * B' c : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w ∧
      ((D.mem u).A.T : ℂ) * ((((((B c)⁻¹ * B' c : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det)⁻¹ ∈ bwA_Ow D w)
    (Φ : Vl D u 0 →ₛₗ[((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w)]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ))
    (hΦ : Function.Injective Φ)
    (hA : ((D.fm u).Bw 0 w v).map Φ = Submodule.pi Set.univ fun c =>
      ((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c))).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift)))
    (hS : (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)).map Φ = Submodule.pi Set.univ fun _ =>
      (intSubm D w ((D.fm u).lam 0)).map
            (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v))))
    (hd : D.duS u = Fintype.card ((D.mem u).C.cls 0) *
      ∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ))) :
    ∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
      (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
        ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
          (D.R.k : ℚ)) := by
  classical
  have hkpos : (0 : ℚ) < (D.R.k : ℚ) := by
    have h := D.R.m_add_three_le_k
    exact_mod_cast (show 0 < D.R.k by omega)
  choose n hn hnq using fun c => cls_len_D D u A w hw v Lv c (hLc0 c) (B c) (B' c) (hB c) (hB' c) (hunit c)
  refine ⟨∑ c, n c, ?_, ?_⟩
  · unfold Formalism.MainNotions.product_first_zeroth_parts.len
    rw [len_quot_semilinear (σ' := ((owEquiv D w).symm : bwA_Ow D w →+* Ow D w)) Φ hΦ, hA, hS, len_pi_sum,
      Nat.cast_sum]
    exact Finset.sum_congr rfl fun c _ => hn c
  · have e : ∀ c, (n c : ℚ) = (D.what₂.places.ramIdx w : ℚ) *
        ((∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ)) : ℕ) : ℚ) *
        ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
          (D.R.k : ℚ) := fun c => by
      rw [eq_div_iff hkpos.ne', mul_comm]; exact hnq c
    rw [Nat.cast_sum, Finset.sum_congr rfl fun c _ => e c, Finset.sum_const, Finset.card_univ, hd, nsmul_eq_mul]
    push_cast
    ring

end Formalism.L2.GlobalTheoryTheory.LemB
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable {D : D7} {u : D.what₂.Word}

def IsCrd (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) : Prop :=
  ∀ z, (D.fm u).emb 0 x c z = fnOf (gramC (gramN D 0 (Nat.zero_le _)) (Forms.embT D)) (shiftOf (lamT u 0))
    (atInf (Forms.embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) Q (T.val0.eY z)

theorem atInf_unit (B : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    IsUnit (atInf (Forms.embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det := by
  exact (Matrix.isUnit_iff_isUnit_det _).1 ((Units.isUnit B).map (RingHom.mapMatrix (Forms.embT D τ)))

theorem isCrd_unique (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) {Q Q' : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ}
    (h : IsCrd T B x c Q) (h' : IsCrd T B x c Q') : Q = Q' := by
  apply polynomial_function_frames_injective _ _ _ (atInf_unit (B⁻¹))
  funext y
  obtain ⟨z, rfl⟩ := T.val0.eY.surjective y
  rw [← h z, h' z]

theorem isCrd_exists (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) : ∃ Q, IsCrd T B x c Q := by
  obtain ⟨P, -, hP⟩ := ((T.val0.5 ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩).2 c
  refine ⟨MvPolynomial.C (∏ τ, (atInf (Forms.embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^
      shiftOf (lamT u 0) τ) * subP (atInf (Forms.embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) P, fun z => ?_⟩
  have hN : (fun τ => atInf (Forms.embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ *
      atInf (Forms.embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ) = 1 := by
    funext τ
    simp only [atInf, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Pi.one_apply]
  rw [hP z, ← fnOf_mul _ _ (atInf (Forms.embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)), hN]

theorem isCrd_add (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) {x y : ((D.fm u).lat 0).V}
    {c : (D.mem u).C.cls 0} {Q Q' : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ}
    (h : IsCrd T B x c Q) (h' : IsCrd T B y c Q') : IsCrd T B (x + y) c (Q + Q') := by
  intro z
  rw [map_add (f := _), Pi.add_apply, Pi.add_apply, h z, h' z, map_add (f := _), Pi.add_apply]

theorem isCrd_smul (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) {x : ((D.fm u).lat 0).V}
    {c : (D.mem u).C.cls 0} {Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ}
    (h : IsCrd T B x c Q) (r : D.what₂.LL) : IsCrd T B (r • x) c (D.what₂.embLL r • Q) := by
  intro z
  rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, h z, map_smul, Pi.smul_apply]

def crd (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V) :
    (D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ :=
  fun c => Classical.choose (isCrd_exists T (B c) x c)

theorem crd_spec (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) : IsCrd T (B c) x c (crd T B x c) :=
  Classical.choose_spec (isCrd_exists T (B c) x c)

theorem crd_eq (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) {x : ((D.fm u).lat 0).V}
    {c : (D.mem u).C.cls 0} {Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ}
    (h : IsCrd T (B c) x c Q) : crd T B x c = Q :=
  isCrd_unique T (B c) x c (crd_spec T B x c) h

theorem owEquiv_coe (w : D.what₂.places.Pl) (r : Ow D w) :
    ((((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w) r : bwA_Ow D w) : ℂ) =
      D.what₂.embLL (r : D.what₂.LL) := by
  rfl

theorem crd_add (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (x y : ((D.fm u).lat 0).V) :
    crd T B (x + y) = crd T B x + crd T B y :=
  funext fun c => crd_eq T B (isCrd_add T (B c) (crd_spec T B x c) (crd_spec T B y c))

theorem crd_smul (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (r : D.what₂.LL)
    (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) : crd T B (r • x) c = D.what₂.embLL r • crd T B x c :=
  crd_eq T B (isCrd_smul T (B c) (crd_spec T B x c) r)

def crdL (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (w : D.what₂.places.Pl) :
    Vl D u 0 →ₛₗ[((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w)]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) where
  toFun := crd T B
  map_add' x y := crd_add T B x y
  map_smul' r x := by
    funext c
    have h := crd_smul T B (r : D.what₂.LL) x c
    rw [Pi.smul_apply, Subring.smul_def r x, h, Subring.smul_def, owEquiv_coe]

theorem crdL_inj (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (w : D.what₂.places.Pl) :
    Function.Injective (crdL T B w) := by
  intro x y hxy
  apply (D.fm u).emb_inj 0
  funext c z
  have hc : crd T B x c = crd T B y c := congrFun hxy c
  rw [crd_spec T B x c z, crd_spec T B y c z, hc]

end Formalism.L2.GlobalTheoryTheory.LemB
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable {D : D7} {u : D.what₂.Word}

theorem crd_Bw (T : Forms0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (hs : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) (B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c))
    (hB' : ∀ c, IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) (B' c))
    (x : ((D.fm u).lat 0).V) (hx : x ∈ (D.fm u).Bw 0 w v) (c : (D.mem u).C.cls 0) :
    crd T B x c ∈ ((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c))).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift)) := by
  obtain ⟨P, hP, hPe⟩ := (T.bw0 w hw hs v x).1 hx c (B c) (B' c) (hB c) (hB' c)
  have hc : IsCrd T (B c) x c (MvPolynomial.C (∏ τ, (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ).det ^
      shiftOf (lamT u 0) τ) * Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c)) P) := by
    intro z
    rw [hPe z, ← bwA_N_mul, fnOf_mul]
  rw [crd_eq T B hc]
  have ho : ∀ τ, τ ≠ (D.fm u).tauOf w v → bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ = 1 := by
    intro τ h
    unfold bwA_N
    rw [if_neg h]
  have hprod : ∏ τ, (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) τ).det ^ shiftOf (lamT u 0) τ =
      (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
        ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift := by
    rw [Fintype.prod_eq_single ((D.fm u).tauOf w v) (fun τ h => by rw [ho τ h, Matrix.det_one, one_zpow]), lamT_zero]
    rfl
  rw [hprod, MvPolynomial.C_mul']
  exact ⟨_, ⟨P, Submodule.subset_span hP, rfl⟩, rfl⟩

theorem crd_S (T : Forms0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c))
    (x : ((D.fm u).lat 0).V) (hx : x ∈ (D.fm u).S 0 w) (c : (D.mem u).C.cls 0) :
    crd T B x c ∈ intSubm D w ((D.fm u).lam 0) := by
  have hB'' : IsLocBasis (D.what₂.places.resChar w)
      (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) (clsCrd D u 0 (Nat.zero_le _) c)) (B c) := by
    rw [← bwG_Ld_coe D u 0 (Nat.zero_le _) c]
    have hw' : D.what₂.places.resChar w = (D.mem u).A.T := hw
    rw [hw']
    exact hB c
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨P, hP, hPe⟩ := (T.val0.lat y).1 hy w c (B c) hB''
    rw [crd_eq T B (c := c) hPe]
    exact Submodule.subset_span hP
  | zero =>
    rw [show crd T B 0 c = 0 from congrFun (map_zero (crdL T B w)) c]
    exact Submodule.zero_mem _
  | add y y' _ _ hy hy' =>
    rw [show crd T B (y + y') c = crd T B y c + crd T B y' c from congrFun (crd_add T B y y') c]
    exact Submodule.add_mem _ hy hy'
  | smul r y _ hy =>
    rw [show crd T B (r • y) c = crd T B ((r : D.what₂.LL) • y) c from rfl, crd_smul T B (r : D.what₂.LL) y c]
    exact Submodule.smul_mem _ (⟨D.what₂.embLL (r : D.what₂.LL), ⟨r, r.2, rfl⟩⟩ : bwA_Ow D w) hy

theorem crd_tL (T : Forms0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c)) (b : ℤ)
    (y : ((D.fm u).lat 0).V) (hy : y ∈ tL D u w b ((D.fm u).S 0 w)) (c : (D.mem u).C.cls 0) :
    crd T B y c ∈ (intSubm D w ((D.fm u).lam 0)).map (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ b)) := by
  obtain ⟨x, hx, hxy⟩ := hy
  have hc : IsCrd T (B c) y c ((((D.mem u).A.T : ℂ) ^ b) • crd T B x c) := by
    intro z
    rw [hxy, map_smul]
    show (((D.mem u).A.T : ℂ) ^ b) * (D.fm u).emb 0 x c z = _
    rw [crd_spec T B x c z]
    rfl
  rw [crd_eq T B hc]
  exact ⟨_, crd_S T w hw B hB x hx c, rfl⟩

theorem crdL_Bw_le (T : Forms0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (hs : (D.fm u).seenP w = true)
    (v : (D.mem u).A.vT) (B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c))
    (hB' : ∀ c, IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) (B' c)) :
    ((D.fm u).Bw 0 w v).map (crdL T B w) ≤ Submodule.pi Set.univ fun c =>
      ((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c))).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_comap, Submodule.mem_pi]
  intro c _
  exact crd_Bw T w hw hs v B B' hB hB' x hx c

theorem crdL_tL_le (T : Forms0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c)) (b : ℤ) :
    (tL D u w b ((D.fm u).S 0 w)).map (crdL T B w) ≤ Submodule.pi Set.univ fun _ =>
      (intSubm D w ((D.fm u).lam 0)).map (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ b)) := by
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  rw [Submodule.mem_comap, Submodule.mem_pi]
  intro c _
  exact crd_tL T w hw B hB b y hy c

end Formalism.L2.GlobalTheoryTheory.LemB
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

def OntoAt {D : D7} {u : D.what₂.Word} (T : Forms0 D u) (w : D.what₂.places.Pl) (v : (D.mem u).A.vT)
    (B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) : Prop :=
  (Submodule.pi Set.univ fun c =>
      ((intSubm D w ((D.fm u).lam 0)).map
            ((Formalism.L2.Forms.subP (bwA_N D ((D.fm u).tauOf w v) (B c) (B' c))).toLinearMap.restrictScalars (bwA_Ow D w))).map
          (scO (bwA_Ow D w) _ ((bwA_N D ((D.fm u).tauOf w v) (B c) (B' c) ((D.fm u).tauOf w v)).det ^
            ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift))) ≤ ((D.fm u).Bw 0 w v).map (crdL T B w) ∧
  (Submodule.pi Set.univ fun _ => (intSubm D w ((D.fm u).lam 0)).map
      (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)))) ≤
    (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)).map (crdL T B w)

def SecondBranchCoordinates (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ T : Forms0 D u, admS D u → ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
    ∃ B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E,
      (∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c)) ∧
      (∀ c, IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) (B' c)) ∧
      (∀ c, (((((B c)⁻¹ * B' c : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map
          (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w ∧
        ((D.mem u).A.T : ℂ) * ((((((B c)⁻¹ * B' c : GL (Fin (D.R.N 0)) D.host.E) :
          Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)).map (embT D ((D.fm u).tauOf w v))).det)⁻¹ ∈ bwA_Ow D w) ∧
      OntoAt T w v B B'

def DuCount (D : D7) (u : D.what₂.Word) : Prop :=
  D.duS u = Fintype.card ((D.mem u).C.cls 0) * ∏ τ, Module.finrank ℤ (delSq ℤ (D.R.N 0) ((D.fm u).lam 0 τ))

theorem lenLen2_of_coordOnto {D : D7} {u : D.what₂.Word} (T : Forms0 D u) (hA : admS D u) (hC : SecondBranchCoordinates D u)
    (hd : DuCount D u) : SeenPlaceLatticeLengthFormula D u := by
  intro w hw hs v hb
  obtain ⟨B, B', hB, hB', hu, hO1, hO2⟩ := hC T hA w hw hs v hb
  exact lenLen2_of_coord D u T.atT T.lv0 w hw v (fun c => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.bwL_lcInt0 D u T 0 (Nat.zero_le _) rfl c) B B' hB hB' hu
    (crdL T B w) (crdL_inj T B w) (le_antisymm (crdL_Bw_le T w hw hs v B B' hB hB') hO1)
    (le_antisymm (crdL_tL_le T w hw B hB _) hO2) hd

theorem second_branch_of_coordinates_and_count (hC : ∀ (D : D7) (u : D.what₂.Word), SecondBranchCoordinates D u)
    (hd : ∀ (D : D7) (u : D.what₂.Word), Forms0 D u → admS D u → DuCount D u) :
    ∀ (D : D7) (u : D.what₂.Word), Formalism.MainNotions.RT.SecondBranchIntegralityUnderForms D u := fun D u =>
  Formalism.MainNotions.lemmaB_second_branch_of_length_formula D u fun _ hT => by
    obtain ⟨⟨Ch, chOf, T, -⟩, hA⟩ := hT
    exact lenLen2_of_coordOnto T.to0 hA (hC D u) (hd D u T.to0 hA)

end Formalism.L2.GlobalTheoryTheory.LemB
