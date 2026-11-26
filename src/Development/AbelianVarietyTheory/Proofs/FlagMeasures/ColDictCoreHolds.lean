module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRationalPointsStabiliserFrame
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemUJsetOfKset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivariantUnitaryCoefficientMapOnto
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerPreimageEqOfLocalInnerLatticeEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRepresentsClassesWeightOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinAdeleAlgebraMapInj
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ClassDict

theorem exu_rep {G Γ Gf : Type} [Group G] [Group Γ] [Group Gf] (P R U : Subgroup G) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (Φ : Gf ≃* P) (h0 : P)
    (hK : ∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : P) : G) ∈ U)
    (h1 : ∀ γ : Γ, (Φ (ιf γ)).1 ∈ R) (h2 : ∀ r ∈ R, ∃ γ : Γ, (Φ (ιf γ)).1 = r)
    {C : Type} (yc : C → P)
    (hb : Function.Bijective
      (fun c => (Quotient.mk'' (yc c) : ClassSet (R.subgroupOf P) (U.subgroupOf P)))) (h : Gf) :
    ∃! c : C, ∃ (γ : Γ) (κ : K), h = ιf γ * Φ.symm (yc c * h0⁻¹) * (κ : Gf) := by
  have key : ∀ a b : P, (Quotient.mk'' a : ClassSet (R.subgroupOf P) (U.subgroupOf P)) = Quotient.mk'' b ↔
      ∃ x ∈ R.subgroupOf P, ∃ y ∈ U.subgroupOf P, b = x * a * y := fun a b => @DoubleCoset.eq _ _ _ _ a b
  have fwd : ∀ (c : C) (γ : Γ) (κ : K), h = ιf γ * Φ.symm (yc c * h0⁻¹) * (κ : Gf) →
      (Quotient.mk'' (yc c) : ClassSet (R.subgroupOf P) (U.subgroupOf P)) = Quotient.mk'' (Φ h * h0) := by
    intro c γ κ hc
    rw [key]
    refine ⟨Φ (ιf γ), ?_, h0⁻¹ * Φ κ * h0, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact h1 γ
    · rw [Subgroup.mem_subgroupOf]
      exact (hK κ).1 κ.2
    · simp only [hc, map_mul, MulEquiv.apply_symm_apply, mul_assoc]
  obtain ⟨c, hc⟩ := hb.2 (Quotient.mk'' (Φ h * h0))
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := (key _ _).1 hc
    rw [Subgroup.mem_subgroupOf] at hx hy
    obtain ⟨γ, hγ⟩ := h2 _ hx
    have hκ : Φ.symm (h0 * y * h0⁻¹) ∈ K := by
      rw [hK, MulEquiv.apply_symm_apply]
      have e : h0⁻¹ * (h0 * y * h0⁻¹) * h0 = y := by group
      rw [e]
      exact hy
    refine ⟨γ, ⟨_, hκ⟩, ?_⟩
    apply Φ.injective
    have hγ' : Φ (ιf γ) = x := Subtype.ext hγ
    have hΦ : Φ h = x * yc c * y * h0⁻¹ := by
      rw [← hxy]
      group
    simp only [map_mul, MulEquiv.apply_symm_apply, hγ', hΦ]
    group
  · rintro c' ⟨γ, κ, hc'⟩
    exact hb.1 ((fwd c' γ κ hc').trans hc.symm)

theorem stab_triv {G Γ Gf : Type} [Group G] [Group Γ] [Group Gf] (P U : Subgroup G) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (Φ : Gf ≃* P) (h0 : P)
    (hK : ∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : P) : G) ∈ U)
    (hn : ∀ (x : Gf) (γ : Γ), x⁻¹ * ιf γ * x ∈ K → γ = 1) (y : P) (γ : Γ)
    (hγ : (Φ (ιf γ)).1 ∈ U.map (MulAut.conj y.1).toMonoidHom) : (Φ (ιf γ)).1 = 1 := by
  obtain ⟨u, hu, hyu⟩ := Subgroup.mem_map.1 hγ
  have e : ((Φ (ιf γ) : P) : G) = (y : G) * u * (y : G)⁻¹ := by
    rw [← hyu]
    simp [MulAut.conj_apply]
  have hmem : (Φ.symm (y * h0⁻¹))⁻¹ * ιf γ * Φ.symm (y * h0⁻¹) ∈ K := by
    rw [hK]
    convert hu using 1
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    push_cast
    rw [e]
    group
  rw [hn _ _ hmem]
  simp

theorem bc_inj_of_inj {A B : Type} [CommRing A] [CommRing B] {k : ℕ} {φ : A →+* B}
    (hφ : Function.Injective φ) : Function.Injective (bc (n := Fin k) φ) := by
  intro a b h
  apply Units.ext
  have h' := congrArg Units.val h
  funext i j
  exact hφ (congrFun (congrFun h' i) j)

theorem finAdele_algebraMap_inj (F : Type) [Field F] [NumberField F] :
    Function.Injective (algebraMap F (FiniteAdeleRing (𝓞 F) F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  have : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg (fun x : FiniteAdeleRing (𝓞 F) F => x v) h
    rw [← map_zero (algebraMap F (FiniteAdeleRing (𝓞 F) F)),
      ← map_one (algebraMap F (FiniteAdeleRing (𝓞 F) F))] at h'
    simp only [FiniteAdeleRing.algebraMap_apply] at h'
    rw [HeightOneSpectrum.adicCompletion.coe_zero, HeightOneSpectrum.adicCompletion.coe_one] at h'
    exact zero_ne_one h'
  exact (algebraMap F _).injective

theorem classReps_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gf : Type) [Group Γ] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)), (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ γ : Γ, ∃ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J ∧ (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J → ∃ γ : Γ, (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → ∀ (C : Type) (yc : C → UPts σ J (FiniteAdeleRing (𝓞 F) F)), Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)) → (∀ h : Gf, ∃! c : C, ∃ (γ : Γ) (κ : K), h = ιf γ * Φ.symm (yc c * h0⁻¹) * (κ : Gf)) ∧ ((∀ (x : Gf) (γ : Γ), x⁻¹ * ιf γ * x ∈ K → γ = 1) → ∀ (c : C) (g : GL (Fin n) E), g ∈ UJ (σ : E →+* E) J → bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g ∈ S.U.map (MulAut.conj (yc c).1).toMonoidHom → g = 1) := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gf _ _ ιf K Φ h0 hK h1 h2 C yc hb
  have hR1 : ∀ γ : Γ, (Φ (ιf γ)).1 ∈ ratPts σ J (FiniteAdeleRing (𝓞 F) F) := by
    intro γ
    obtain ⟨g, hg, hgγ⟩ := h1 γ
    rw [hgγ]
    unfold ratPts
    exact Subgroup.mem_map_of_mem _ hg
  have hR2 : ∀ r ∈ ratPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ γ : Γ, (Φ (ιf γ)).1 = r := by
    intro r hr
    unfold ratPts at hr
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hr
    exact h2 g hg
  refine ⟨fun h => exu_rep _ _ S.U ιf K Φ h0 hK hR1 hR2 yc hb h, fun hn c g hg hgU => ?_⟩
  obtain ⟨γ, hγ⟩ := h2 g hg
  have hs := stab_triv _ S.U ιf K Φ h0 hK hn (yc c) γ (by rw [hγ]; exact hgU)
  rw [hγ] at hs
  have hinj : Function.Injective (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) := by
    intro a b hab
    exact Algebra.TensorProduct.includeLeft_injective (S := F) (finAdele_algebraMap_inj F) hab
  exact bc_inj_of_inj hinj (hs.trans (map_one _).symm)

end GlobalTheory.ClassDict
end

section -- local restoration of frame_action_mulEquiv
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FrameActionLocal

variable {R R' : Type} [CommRing R] [CommRing R']
  {N ι κ : Type} [Fintype N] [DecidableEq N] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private def frameAct_local (Q : Matrix N (ι ⊕ κ) R) (Qi : Matrix (ι ⊕ κ) N R) (y : Matrix ι ι R) : Matrix N N R :=
  Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi

variable {Q : Matrix N (ι ⊕ κ) R} {Qi : Matrix (ι ⊕ κ) N R}

private theorem frameAct_mul_frame_local (h2 : Qi * Q = 1) (y : Matrix ι ι R) :
    frameAct_local Q Qi y * Q = Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) := by
  simp only [frameAct_local, Matrix.mul_assoc, h2, Matrix.mul_one]

private theorem frameAct_one_local (h1 : Q * Qi = 1) : frameAct_local Q Qi (1 : Matrix ι ι R) = 1 := by
  simp only [frameAct_local, Matrix.fromBlocks_one, Matrix.mul_one, h1]

private theorem frameAct_mul_local (h2 : Qi * Q = 1) (y y' : Matrix ι ι R) :
    frameAct_local Q Qi (y * y') = frameAct_local Q Qi y * frameAct_local Q Qi y' := by
  have hB : Matrix.fromBlocks (y * y') 0 0 (1 : Matrix κ κ R) =
      Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Matrix.fromBlocks y' 0 0 (1 : Matrix κ κ R) := by
    rw [Matrix.fromBlocks_multiply]; simp
  simp only [frameAct_local, hB, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Qi Q, h2, Matrix.one_mul]

private theorem frame_block_inj_local (h2 : Qi * Q = 1) {y y' : Matrix ι ι R}
    (hc : ∀ l j, (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)) l (Sum.inl j) =
      (Q * Matrix.fromBlocks y' 0 0 (1 : Matrix κ κ R)) l (Sum.inl j)) : y = y' := by
  ext i j
  have key : ∀ z : Matrix ι ι R,
      (Qi * (Q * Matrix.fromBlocks z 0 0 (1 : Matrix κ κ R))) (Sum.inl i) (Sum.inl j) = z i j := by
    intro z
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
    simp
  rw [← key y, ← key y', Matrix.mul_apply (M := Qi), Matrix.mul_apply (M := Qi)]
  exact Finset.sum_congr rfl fun l _ => by rw [hc l j]

private theorem frameAct_col_inr_local (h2 : Qi * Q = 1) (y : Matrix ι ι R) (b : κ) :
    frameAct_local Q Qi y *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b) := by
  funext i
  have h := congrFun (congrFun (frameAct_mul_frame_local h2 y) i) (Sum.inr b)
  show ∑ x, frameAct_local Q Qi y i x * Q x (Sum.inr b) = Q i (Sum.inr b)
  rw [← Matrix.mul_apply, h]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private theorem frame_rep_iff_local (M : Matrix N N R) (y : Matrix ι ι R) :
    (∀ j, M *ᵥ (fun l => Q l (Sum.inl j)) = ∑ i, y i j • (fun l => Q l (Sum.inl i))) ↔
      ∀ l j, (M * Q) l (Sum.inl j) = (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)) l (Sum.inl j) := by
  have e1 : ∀ j l, (M *ᵥ fun l => Q l (Sum.inl j)) l = (M * Q) l (Sum.inl j) := fun _ _ => rfl
  have e2 : ∀ j l, (∑ i, y i j • fun l => Q l (Sum.inl i)) l =
      (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R)) l (Sum.inl j) := by
    intro j l
    simp [Finset.sum_apply, Matrix.mul_apply, Fintype.sum_sum_type, mul_comm]
  constructor
  · intro h l j
    rw [← e1, ← e2, h j]
  · intro h j
    funext l
    rw [e1, e2, h l j]

private theorem map_mul_equiv_local {l m n : Type} [Fintype m] (e : R ≃+* R') (A : Matrix l m R) (B : Matrix m n R) :
    (A * B).map e = A.map e * B.map e := by
  ext i j
  simp [Matrix.mul_apply]

private theorem unitary_map_equiv_local (s : R →+* R) (s' : R' →+* R') (e : R ≃+* R') (he : ∀ a, e (s a) = s' (e a))
    (G y : Matrix ι ι R) (hy : (y.map s)ᵀ * G * y = G) :
    ((y.map e).map s')ᵀ * G.map e * y.map e = G.map e := by
  have h1 : (y.map e).map s' = (y.map s).map e := by
    ext i j; simp [he]
  rw [h1, ← Matrix.transpose_map, ← map_mul_equiv_local, ← map_mul_equiv_local, hy]

private theorem frame_stabiliser_mulEquiv_local (s : R →+* R) (s' : R' →+* R') (e : R ≃+* R')
    (he : ∀ a, e (s a) = s' (e a)) (J : Matrix N N R) (G : Matrix ι ι R) (G' : Matrix κ κ R)
    (h1 : Q * Qi = 1) (h2 : Qi * Q = 1)
    (hD : (Q.map s)ᵀ * J * Q = Matrix.fromBlocks G 0 0 G') (hG' : IsUnit G'.det)
    (U : Subgroup (GL N R)) (hU : ∀ g : GL N R, g ∈ U ↔ (g.1.map s)ᵀ * J * g.1 = J)
    (U' : Subgroup (GL ι R'))
    (hU' : ∀ g : GL ι R', g ∈ U' ↔ (g.1.map s')ᵀ * G.map e * g.1 = G.map e)
    (H : Subgroup U)
    (hH : ∀ x : U, x ∈ H ↔ ∀ b, x.1.1 *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b)) :
    ∃ Φ : H ≃* U', ∀ (h : H) (y : U'),
      (∀ j, h.1.1.1 *ᵥ (fun l => Q l (Sum.inl j)) =
        ∑ i, e.symm (y.1.1 i j) • (fun l => Q l (Sum.inl i))) ↔ Φ h = y := by
  classical
  obtain ⟨hfwd, hbwd⟩ := GlobalTheory.unitary_stabiliser_orthogonal_summand R s N ι κ J G G' Q Qi h1 h2 hD hG'

  let yOf : Matrix N N R → Matrix ι ι R := fun M => (Qi * M * Q).toBlocks₁₁
  have yOf_frame : ∀ y, yOf (frameAct_local Q Qi y) = y := by
    intro y
    show (Qi * (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi) * Q).toBlocks₁₁ = y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qi Q, h2, Matrix.one_mul, Matrix.mul_one]
    exact Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

  have memH : ∀ x : U, x ∈ H →
      ((yOf x.1.1).map s)ᵀ * G * yOf x.1.1 = G ∧ x.1.1 = frameAct_local Q Qi (yOf x.1.1) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hbwd x.1.1 ((hU x.1).1 x.2) ((hH x).1 hx)
    have hyx : yOf x.1.1 = y := by rw [hxy]; exact yOf_frame y
    rw [hyx]
    exact ⟨hy, hxy⟩

  let φ0 : H →* Matrix ι ι R :=
    { toFun := fun h => yOf h.1.1.1
      map_one' := by
        have h1' := yOf_frame 1
        rw [frameAct_one_local h1] at h1'
        exact h1'
      map_mul' := by
        intro a b
        obtain ⟨-, ha⟩ := memH a.1 a.2
        obtain ⟨-, hb⟩ := memH b.1 b.2
        show yOf (a.1.1.1 * b.1.1.1) = yOf a.1.1.1 * yOf b.1.1.1
        conv_lhs => rw [ha, hb, ← frameAct_mul_local h2, yOf_frame] }
  let φ1 : H →* GL ι R' :=
    (Units.map (e.mapMatrix (m := ι)).toMonoidHom).comp φ0.toHomUnits
  have φ1_val : ∀ h : H, ((φ1 h : GL ι R') : Matrix ι ι R') = (yOf h.1.1.1).map e := fun _ => rfl
  have memU' : ∀ h : H, φ1 h ∈ U' := by
    intro h
    rw [hU', φ1_val]
    exact unitary_map_equiv_local s s' e he G _ (memH h.1 h.2).1
  let Φ0 : H →* U' := φ1.codRestrict U' memU'
  have hinj : Function.Injective Φ0 := by
    intro a b hab
    have e1 : (yOf a.1.1.1).map e = (yOf b.1.1.1).map e := by
      rw [← φ1_val, ← φ1_val]
      exact congrArg (fun z : U' => ((z : GL ι R') : Matrix ι ι R')) hab
    have e2 : yOf a.1.1.1 = yOf b.1.1.1 := by
      ext i j
      exact e.injective (congrFun (congrFun e1 i) j)
    have e3 : a.1.1.1 = b.1.1.1 := by
      rw [(memH a.1 a.2).2, (memH b.1 b.2).2, e2]
    exact Subtype.ext (Subtype.ext (Units.ext e3))
  have hsurj : Function.Surjective Φ0 := by
    intro y
    have he' : ∀ a, e.symm (s' a) = s (e.symm a) := by
      intro a
      apply e.injective
      rw [RingEquiv.apply_symm_apply, he, RingEquiv.apply_symm_apply]
    have hGG : (G.map e).map e.symm = G := by
      ext i j; simp
    have hzu : ((((y : GL ι R') : Matrix ι ι R').map e.symm).map s)ᵀ * G *
        ((y : GL ι R') : Matrix ι ι R').map e.symm = G := by
      have h3 := unitary_map_equiv_local s' s e.symm he' (G.map e) _ ((hU' y.1).1 y.2)
      rwa [hGG] at h3
    have hinv : ∀ a b : U', a * b = 1 →
        ((a : GL ι R') : Matrix ι ι R').map e.symm * ((b : GL ι R') : Matrix ι ι R').map e.symm = 1 := by
      intro a b hab
      rw [← map_mul_equiv_local]
      have hab' : ((a : GL ι R') : Matrix ι ι R') * ((b : GL ι R') : Matrix ι ι R') = 1 := by
        have := congrArg (fun z : U' => ((z : GL ι R') : Matrix ι ι R')) hab
        exact this
      rw [hab']
      ext i j
      simp [Matrix.one_apply]
    let g : GL N R :=
      ⟨frameAct_local Q Qi (((y : GL ι R') : Matrix ι ι R').map e.symm),
        frameAct_local Q Qi ((((y⁻¹ : U') : GL ι R') : Matrix ι ι R').map e.symm),
        by rw [← frameAct_mul_local h2, hinv y y⁻¹ (mul_inv_cancel y), frameAct_one_local h1],
        by rw [← frameAct_mul_local h2, hinv y⁻¹ y (inv_mul_cancel y), frameAct_one_local h1]⟩
    have gU : g ∈ U := (hU g).2 (hfwd _ hzu)
    have gH : (⟨g, gU⟩ : U) ∈ H := (hH _).2 (fun b => frameAct_col_inr_local h2 _ b)
    refine ⟨⟨⟨g, gU⟩, gH⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    show (yOf (frameAct_local Q Qi (((y : GL ι R') : Matrix ι ι R').map e.symm))).map e = ((y : GL ι R') : Matrix ι ι R')
    rw [yOf_frame]
    ext i j
    simp
  let Φ : H ≃* U' := MulEquiv.ofBijective Φ0 ⟨hinj, hsurj⟩
  refine ⟨Φ, fun h y => ?_⟩
  have hΦ : (((Φ h : U') : GL ι R') : Matrix ι ι R') = (yOf h.1.1.1).map e := rfl
  obtain ⟨-, hh⟩ := memH h.1 h.2
  have hm : h.1.1.1 * Q = Q * Matrix.fromBlocks (yOf h.1.1.1) 0 0 (1 : Matrix κ κ R) := by
    conv_lhs => rw [hh]
    exact frameAct_mul_frame_local h2 _
  show (∀ j, h.1.1.1 *ᵥ (fun l => Q l (Sum.inl j)) =
      ∑ i, (((y : GL ι R') : Matrix ι ι R').map e.symm) i j • (fun l => Q l (Sum.inl i))) ↔ Φ h = y
  rw [frame_rep_iff_local]
  constructor
  · intro hc
    have hy : yOf h.1.1.1 = ((y : GL ι R') : Matrix ι ι R').map e.symm := by
      apply frame_block_inj_local h2
      intro l j
      rw [← hm]
      exact hc l j
    apply Subtype.ext
    apply Units.ext
    rw [hΦ, hy]
    ext i j
    simp
  · intro hΦy l j
    have hy : yOf h.1.1.1 = ((y : GL ι R') : Matrix ι ι R').map e.symm := by
      rw [← hΦy, hΦ]
      ext i j
      simp
    rw [hm, hy]

end FrameActionLocal

private theorem frame_action_mulEquiv_local : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F), WittX X u wt → IsAdeleIso X ιA → (∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a)) → ∃ (Φ : Hfin X u ≃* Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ (h : Hfin X u) y, RepF X wt ιA (h : X.B.I.Gf) y ↔ Φ h = y) := by
  intro D X u wt ιA hW hA hσ
  obtain ⟨Q, Qi, G', h1, h2, hQl, hQe, hQf, hQz, hG', hD⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hW
  set f : X.B.I.E →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) with hf
  have hA1 : Q.map f * Qi.map f = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f)]
  have hA2 : Qi.map f * Q.map f = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero f) (map_one f)]
  have hsf : ∀ x, sigA X.B.I (f x) = f (star x) := by
    intro x
    simp only [hf, sigA, Formalism.UG.sigR, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have hDA : ((Q.map f).map (sigA X.B.I))ᵀ * X.B.I.J.map f * Q.map f =
      Matrix.fromBlocks (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).map f) 0 0 (G'.map f) := by
    have hs : (Q.map f).map (sigA X.B.I) = (Q.map (starRingEnd X.B.I.E)).map f := by
      ext i j
      exact hsf (Q i j)
    rw [hs, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hD, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero f), Matrix.map_zero _ (map_zero f)]
  have hGA : IsUnit (G'.map f).det := by
    have h3 := hG'.map f
    rwa [RingHom.map_det] at h3
  have hGm : (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).map f).map ιA =
      (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map
        (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    ext i j
    simp only [Matrix.map_apply]
    rw [hf, hA.1, RingEquiv.apply_symm_apply]
  have hH : ∀ x : X.B.I.Gf, x ∈ Hfin X u ↔
      ∀ b, x.1.1 *ᵥ (fun i => (Q.map f) i (Sum.inr b)) = fun i => (Q.map f) i (Sum.inr b) := by
    intro x
    have hcol : ∀ b, (fun i => (Q.map f) i (Sum.inr b)) = incl X.B.I (fun i => Q i (Sum.inr b)) :=
      fun _ => rfl
    have ce : ∀ a, (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := fun a => funext fun i => hQe a i
    have cf : ∀ a, (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a :=
      fun a => funext fun i => hQf a i
    have cz : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext fun i => hQz i
    show (∀ y ∈ fixSet X u, X.B.I.fmat x *ᵥ incl X.B.I y = incl X.B.I y) ↔ _
    constructor
    · intro hx b
      rw [hcol]
      apply hx
      simp only [fixSet, Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
      rcases b with a | a | ⟨⟩
      · rw [ce]; exact Or.inl (Or.inl ⟨a, rfl⟩)
      · rw [cf]; exact Or.inl (Or.inr ⟨a, rfl⟩)
      · rw [cz]; exact Or.inr rfl
    · intro hx y hy
      simp only [fixSet, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hy
      rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl
      · have h4 := hx (Sum.inl a)
        rwa [hcol, ce] at h4
      · have h4 := hx (Sum.inr (Sum.inl a))
        rwa [hcol, cf] at h4
      · have h4 := hx (Sum.inr (Sum.inr ()))
        rwa [hcol, cz] at h4
  obtain ⟨Φ, hΦ⟩ := frame_stabiliser_mulEquiv_local (Q := Q.map f) (Qi := Qi.map f) (sigA X.B.I)
    (Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ιA hσ
    (X.B.I.J.map f) (((Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm).map f) (G'.map f)
    hA1 hA2 hDA hGA (Formalism.UG.UPts X.B.I.cm.sig X.B.I.J (Af X.B.I.F)) (fun _ => Iff.rfl)
    (Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (fun g => by rw [hGm]; exact Iff.rfl) (Hfin X u) hH
  refine ⟨Φ, fun h y => ?_⟩
  rw [← hΦ h y]
  have hq : ∀ j, qA X wt j = fun l => (Q.map f) l (Sum.inl j) := by
    intro j
    funext l
    show f (X.crd (qFr wt j) l) = f (Q l (Sum.inl j))
    rw [hQl]
  show (∀ j, X.B.I.fmat (h : X.B.I.Gf) *ᵥ qA X wt j = ∑ i, ιA.symm (y.1.1 i j) • qA X wt i) ↔ _
  simp only [hq]

end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRepresentsClassesWeightOne
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColClass

theorem classes_and_weight : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ClsMatch X Tr hK ∧ (Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ c, (D.mem u).C.wt 0 c = 1) := by
  intro D X u F Tr hK hsig hLM
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  obtain ⟨Φ, hΦ⟩ := frame_action_mulEquiv_local D X u Tr.wt Tr.ιA hW hA hsig
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
  have hc : ∀ c, Tr.hc c = Φ.symm (F.cls0.y c * Tr.h0⁻¹) := fun c => by
    rw [MulEquiv.eq_symm_apply]
    exact (hΦ _ _).1 (Tr.hc_rep c)
  have hKu : ∀ h : Hfin X u, h ∈ Ku X u hK ↔
      (((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) : GL _ _) ∈ F.cls0.lev.U :=
    fun h => (hLM.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).1
  have key := GlobalTheory.ClassDict.classReps_dictionary D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hfin X u) (iotaF X u) (Ku X u hK)
    Φ Tr.h0 hKu h1 h2 ((D.mem u).C.cls 0) F.cls0.y F.cls0.y_bij
  refine ⟨fun h => ?_, fun hst c => ?_⟩
  · obtain ⟨c, hc1, hc2⟩ := key.1 h
    refine ⟨c, ?_, fun c' hc' => hc2 c' ?_⟩
    · obtain ⟨γ, κ, e⟩ := hc1
      exact ⟨γ, κ, by rw [hc]; exact e⟩
    · obtain ⟨γ, κ, e⟩ := hc'
      exact ⟨γ, κ, by rw [← hc]; exact e⟩
  · have hsub : Subsingleton ((D.mem u).C.stab 0 c) := by
      refine ⟨fun s t => ?_⟩
      have h1' : ∀ s : (D.mem u).C.stab 0 c, s = 1 := by
        intro s
        apply F.cls0.stabI_inj c
        rw [map_one]
        apply Subtype.ext
        have hr := (F.cls0.stabI_range c (F.cls0.stabI c s)).1 ⟨s, rfl⟩
        exact key.2 hst c _ (F.cls0.stabI c s).2 hr
      rw [h1' s, h1' t]
    have : Nat.card ((D.mem u).C.stab 0 c) = 1 := by
      haveI : Unique ((D.mem u).C.stab 0 c) := uniqueOfSubsingleton 1
      exact Nat.card_unique
    simp [Formalism.BasicNotions.ColumnChain.wt, this]

end GlobalTheory.ColClass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRepresentsClassesWeightOneStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transport_represents_classes_weight_one : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ClsMatch X Tr hK ∧ (Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ c, (D.mem u).C.wt 0 c = 1) := by
  first | exact @GlobalTheory.ColClass.classes_and_weight | exact GlobalTheory.ColClass.classes_and_weight | (intros; apply GlobalTheory.ColClass.classes_and_weight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryBijectiveOfLevelMatch
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportCoeffMapBijectiveOntoValues
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjLinearOntoOfInjectiveOfLeRange
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem conjLinear_onto_of_injective_of_le_range :
    ∀ (W M : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (J₀ J₁ : W →ₗ⋆[ℂ] M), (∀ p ∈ S, ∃ ξ, J₀ ξ = p) → Function.Injective J₁ → (∀ ξ, J₁ ξ ∈ S) → ∀ p ∈ S, ∃ ξ, J₁ ξ = p := by
  intro W M _ _ _ _ _ S J₀ J₁ h0 hinj hS
  let f0 : W →ₗ[ℝ] M :=
    { toFun := J₀
      map_add' := J₀.map_add
      map_smul' := fun r x => by
        show J₀ (r • x) = r • J₀ x
        rw [← Complex.coe_smul, J₀.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }
  let f1 : W →ₗ[ℝ] M :=
    { toFun := J₁
      map_add' := J₁.map_add
      map_smul' := fun r x => by
        show J₁ (r • x) = r • J₁ x
        rw [← Complex.coe_smul, J₁.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul] }

  have hle0 : S.restrictScalars ℝ ≤ LinearMap.range f0 := fun p hp => h0 p hp
  have hle1 : LinearMap.range f1 ≤ S.restrictScalars ℝ := by
    rintro _ ⟨ξ, rfl⟩
    exact hS ξ
  have hf1 : Function.Injective f1 := hinj
  have : FiniteDimensional ℝ (S.restrictScalars ℝ) := Submodule.finiteDimensional_of_le hle0
  have hdim : Module.finrank ℝ (S.restrictScalars ℝ) ≤ Module.finrank ℝ (LinearMap.range f1) := by
    rw [LinearMap.finrank_range_of_inj hf1]
    exact (Submodule.finrank_mono hle0).trans (LinearMap.finrank_range_le f0)

  have heq : LinearMap.range f1 = S.restrictScalars ℝ := Submodule.eq_of_le_of_finrank_le hle1 hdim
  intro p hp
  have hp' : p ∈ LinearMap.range f1 := heq ▸ hp
  obtain ⟨ξ, hξ⟩ := hp'
  exact ⟨ξ, hξ⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportCoeffMapBijectiveOntoValues
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem transport_J_bijective_onto :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F),
      Function.Injective Tr.J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, Tr.J ξ = p := by
  intro D X u F Tr
  obtain ⟨c, -⟩ := F.cls0.y_bij.2 (Quotient.mk'' 1)
  have hinj : Function.Injective Tr.J := by
    intro ξ η h
    have h1 := Tr.J_isom c ξ η
    have h2 := Tr.J_isom c ξ ξ
    have h3 := Tr.J_isom c η ξ
    have h4 := Tr.J_isom c η η
    rw [h] at h1 h2 h3
    rw [h4] at h1 h2 h3
    have h0 : ⟪ξ - η, ξ - η⟫_ℂ = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, ← h1, ← h2, ← h3]
      ring
    exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)
  refine ⟨hinj, ?_⟩
  obtain ⟨J₀, -, hJ₀⟩ := GlobalTheory.T.exists_equivariant_unitary_coefficientMap_onto D X u F Tr.wt ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  exact GlobalTheory.conjLinear_onto_of_injective_of_le_range (X.Vpi u) _ _ J₀ Tr.J hJ₀ hinj Tr.J_val

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportCoeffMapBijectiveOntoValuesStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportCoeffMap_bijective_onto_values : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F), Function.Injective Tr.J ∧ ∀ p ∈ Formalism.L2.Forms.ValC (Formalism.L2.Forms.gramC (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Formalism.L2.Forms.embT D)) (Formalism.L2.Forms.lamT u 0), ∃ ξ, Tr.J ξ = p := by
  first | exact @GlobalTheory.transport_J_bijective_onto | exact GlobalTheory.transport_J_bijective_onto | (intros; apply GlobalTheory.transport_J_bijective_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdFormFromEquivariant
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem adForm_from_equivariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (Φ : Gf ≃* UPts σ J (FiniteAdeleRing (𝓞 F) F)) (h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (ι : Type) [Fintype ι] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W) (Jm : W →ₗ⋆[ℂ] (Frames (gramC J emb) → ℂ)), (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → (∀ h : Gf, h ∈ K ↔ ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U) → (∀ (h : Gf) (hk : h ∈ K) (hy : ((h0⁻¹ * Φ h * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U), ((ψ ⟨h, hk⟩ : ℂˣ) : ℂ) = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ)) → (∀ γ : Γ, ∃ g : GL (Fin n) E, g ∈ UJ (σ : E →+* E) J ∧ (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g) → (∀ (γ : Γ) (g : GL (Fin n) E), (Φ (ιf γ)).1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) g → ∀ (ξ : W) (y y' : Frames (gramC J emb)), IsTr (atInf emb g.1) y' y → Jm (π (ιi γ) ξ) y = Jm ξ y') → Function.Injective Jm → (∀ p ∈ ValC (gramC J emb) lam, ∃ ξ, Jm ξ = p) → ∀ g ∈ AdForms S emb lam, ∃ φ : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) ∧ ∀ y : UPts σ J (FiniteAdeleRing (𝓞 F) F), g y = Jm (φ (Φ.symm (y * h0⁻¹))) := by
  intro F E _ _ _ _ _ σ n J T f bad S Γ Gi Gf _ _ _ ιi ιf K ψ Φ h0 ι _ emb lam W _ _ π Jm
    hψ hK hχ hrat hint hinj hsurj g hg

  have hval : ∀ z, g z ∈ ValC (gramC J emb) lam := fun z => (Submodule.mem_inf.mp hg).2 z (Set.mem_univ z)
  have hfun := (Submodule.mem_inf.mp hg).1
  choose pre hpre using fun z => hsurj (g z) (hval z)
  refine ⟨fun x => pre (Φ x * h0), ?_, ?_⟩
  · intro γ x κ
    obtain ⟨gr, hgrU, hgr⟩ := hrat γ
    apply hinj
    rw [hpre, LinearMap.map_smulₛₗ]
    funext y
    obtain ⟨y', hy'⟩ := exists_isTr' emb gr y
    rw [Pi.smul_apply, hint γ gr hgr (pre (Φ x * h0)) y y' hy', hpre]

    have hconj : (starRingEnd ℂ) ((((ψ κ)⁻¹ : ℂˣ) : ℂ)) = ((ψ κ : ℂˣ) : ℂ) := by
      rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hψ κ), Complex.conj_conj]
    rw [smul_eq_mul, hconj]
    have hk : ((h0⁻¹ * Φ κ.1 * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈ S.U :=
      (hK κ.1).1 κ.2
    have hx : (Φ (ιf γ * x * κ.1) * h0 : UPts σ J (FiniteAdeleRing (𝓞 F) F)) =
        Φ (ιf γ) * (Φ x * h0) * (h0⁻¹ * Φ κ.1 * h0) := by
      simp only [map_mul]; group
    have key := hfun gr hgrU (Φ x * h0) (Φ (ιf γ * x * κ.1) * h0) ⟨_, hk⟩
      (by rw [hx, Subgroup.coe_mul, Subgroup.coe_mul, hgr]) y y' hy'
    rw [key, ← hχ κ.1 κ.2 hk]
  · intro y
    rw [hpre]
    congr 1
    simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryBijectiveOfLevelMatch
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDict_bij_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictBij X Tr hK := by
  intro D X u F Tr hK hσ hL
  obtain ⟨hψ, -, hEq, hDet, hOnto⟩ := cols_sharp_dictionary D X u hK
  obtain ⟨hJinj, hJsurj⟩ := GlobalTheory.T.transportCoeffMap_bijective_onto_values D X u F Tr
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    have hcls := (GlobalTheory.T.transport_represents_classes_weight_one D X u F Tr hK hσ hL).1
    have h1 : ∀ c, shP X u T.1 (Tr.hc c) = 0 := by
      intro c
      apply hJinj
      rw [map_zero]
      funext y
      have := congrFun (congrFun hT c) (F.val0.eY.symm y)
      simpa [colDictL, dictA] using this
    apply hDet T
    intro x
    obtain ⟨c, ⟨γ, κ, hx⟩, -⟩ := hcls x
    rw [hx, hEq, h1, map_zero, smul_zero]
  · intro φ hφ
    rw [Formalism.L2.Forms.Mu0_iff F.val0] at hφ
    obtain ⟨g, hg, hres⟩ := Submodule.mem_map.1 hφ
    obtain ⟨Φ, hΦ⟩ := frame_action_mulEquiv_local D X u Tr.wt Tr.ιA hW hA hσ
    obtain ⟨hΓ, -, hs⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
    have hKm : ∀ h : Hfin X u, h ∈ Ku X u hK ↔ ((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
        F.cls0.lev.U :=
      fun h => (hL.2 h (Φ h) ((hΦ h _).2 rfl)).1
    have hχ : ∀ (h : Hfin X u) (hk : h ∈ Ku X u hK) (hy : ((Tr.h0⁻¹ * Φ h * Tr.h0 : Formalism.UG.UPts (Formalism.L2.Forms.sigD D)
        (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : GL _ _) ∈
        F.cls0.lev.U), ((psiK X u hK ⟨h, hk⟩ : ℂˣ) : ℂ) = ((F.cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) :=
      fun h hk hy => (hL.2 h (Φ h) ((hΦ h _).2 rfl)).2 hk hy
    have hπ : ∀ (γ : Gam X u) (g : GL (Fin (D.R.N 0)) D.host.E),
        (Φ (iotaF X u γ)).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) g →
        ∀ (ξ : X.Vpi u) (y y' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)),
          Formalism.L2.Forms.IsTr (Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT D) g.1) y' y →
          Tr.J (piRep X u (iotaI X u γ) ξ) y = Tr.J ξ y' := by
      intro γ g e ξ y y' hy
      have h2 := hs γ g e
      exact Tr.J_eqv (iotaI X u γ) (iotaI X u γ).2 ξ y y' (by rw [h2]; exact hy)
    rw [Formalism.L2.Forms.lamT_zero] at hJsurj
    obtain ⟨φ', hφ'eq, hφ'g⟩ := GlobalTheory.adForm_from_equivariant _ _ (Formalism.L2.Forms.sigD D) _ _ _ _ _ F.cls0.lev
      (Gam X u) (Hinf X u) (Hfin X u) (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 _
      (Formalism.L2.Forms.embT D) ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ hKm hχ hΓ hπ hJinj hJsurj g hg
    obtain ⟨T, hT⟩ := hOnto φ' hφ'eq
    refine ⟨T, ?_⟩
    funext c z
    have hc : Φ (Tr.hc c) = F.cls0.y c * Tr.h0⁻¹ := (hΦ _ _).1 (Tr.hc_rep c)
    have e1 := congrFun (congrFun hres c) (F.val0.eY z)
    have e2 := hφ'g (F.cls0.y c)
    have e3 : Φ.symm (F.cls0.y c * Tr.h0⁻¹) = Tr.hc c := (MulEquiv.symm_apply_eq Φ).2 hc.symm
    rw [e3] at e2
    show Tr.J (shP X u T.1 (Tr.hc c)) (F.val0.eY z) = φ c z
    rw [hT, ← e2]
    simpa [Formalism.L2.Forms.res] using e1

end GlobalTheory.St
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryBijectiveOfLevelMatchStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnDictionary_bijective_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictBij X Tr hK := by
  first | exact @GlobalTheory.St.colDict_bij_of_levelMatch | exact GlobalTheory.St.colDict_bij_of_levelMatch | (intros; apply GlobalTheory.St.colDict_bij_of_levelMatch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIsometricOfRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumInnerClassRepsIndep
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

theorem sum_inner_classReps_indep : ∀ (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* ℂˣ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : Representation ℂ Gi W), (∀ h v w, ⟪π h v, π h w⟫_ℂ = ⟪v, w⟫_ℂ) → (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) → ∀ (C C' : Type) [Fintype C] [Fintype C'] (s : C → Gf) (s' : C' → Gf), (∀ h : Gf, ∃! c, ∃ (γ : Γ) (κ : K), h = ιf γ * s c * (κ : Gf)) → (∀ h : Gf, ∃! c, ∃ (γ : Γ) (κ : K), h = ιf γ * s' c * (κ : Gf)) → ∀ φ φ' : Gf → W, (∀ (γ : Γ) (x : Gf) (κ : K), φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) → (∀ (γ : Γ) (x : Gf) (κ : K), φ' (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ' x)) → ∑ c, ⟪φ (s c), φ' (s c)⟫_ℂ = ∑ c, ⟪φ (s' c), φ' (s' c)⟫_ℂ := by
  intro Γ Gi Gf _ _ _ ιi ιf K ψ W _ _ π hπ hψ C C' _ _ s s' hs hs' φ φ' hφ hφ'
  have hf : ∀ (γ : Γ) (x : Gf) (κ : K),
      ⟪φ (ιf γ * x * κ), φ' (ιf γ * x * κ)⟫_ℂ = ⟪φ x, φ' x⟫_ℂ := by
    intro γ x κ
    rw [hφ, hφ', inner_smul_left, inner_smul_right, hπ, ← mul_assoc]
    have hn : ‖(((ψ κ)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
      rw [Units.val_inv_eq_inv_val, norm_inv, hψ κ, inv_one]
    have : (starRingEnd ℂ) (((ψ κ)⁻¹ : ℂˣ) : ℂ) * (((ψ κ)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [RCLike.conj_mul, hn]; simp
    rw [this, one_mul]
  obtain ⟨g, hg⟩ : ∃ g : C → C', ∀ c, ∃ (γ : Γ) (κ : K), s c = ιf γ * s' (g c) * (κ : Gf) :=
    ⟨fun c => (hs' (s c)).exists.choose, fun c => (hs' (s c)).exists.choose_spec⟩
  have hbij : Function.Bijective g := by
    constructor
    · intro c1 c2 h
      obtain ⟨γ1, κ1, h1⟩ := hg c1
      obtain ⟨γ2, κ2, h2⟩ := hg c2
      rw [h] at h1
      refine (hs (s c2)).unique ?_ ⟨1, 1, by simp⟩
      refine ⟨γ2 * γ1⁻¹, κ1⁻¹ * κ2, ?_⟩
      rw [h2, h1]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    · intro c'
      obtain ⟨c, ⟨γ, κ, h⟩, -⟩ := hs (s' c')
      refine ⟨c, (hs' (s c)).unique (hg c) ⟨γ⁻¹, κ⁻¹, ?_⟩⟩
      rw [h]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
  refine Fintype.sum_bijective g hbij _ _ (fun c => ?_)
  obtain ⟨γ, κ, h⟩ := hg c
  have := hf γ (s' (g c)) κ
  rw [← h] at this
  exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIsometricOfRepresentatives
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colDict_isometric_of_reps :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (cs : Formalism.L2.SG.TermOp.ColSys X u what₂) (hinj : Function.Injective (Formalism.L2.SG.TermOp.sharp hK cs)), Formalism.L2.SG.TermOp.ColReps hK cs → ColDictIsom X Tr hK cs hinj := by
  intro D X u F Tr hK hsig hL hS what₂ cs hinj hreps T T'
  obtain ⟨hcls, hwt⟩ := GlobalTheory.T.transport_represents_classes_weight_one D X u F Tr hK hsig hL
  have hwt1 := hwt hS
  obtain ⟨hψ, hπ, heq, -, -⟩ := GlobalTheory.St.cols_sharp_dictionary D X u hK
  have key := GlobalTheory.sum_inner_classReps_indep (Gam X u) (Hinf X u) (Hfin X u) (iotaI X u) (iotaF X u)
    (Ku X u hK) (psiK X u hK) (X.Vpi u) (piRep X u) hπ hψ cs.Cl ((D.mem u).C.cls 0) cs.h Tr.hc hreps hcls
    (shP X u (toCu X hK T').1) (shP X u (toCu X hK T).1) (heq _) (heq _)
  have hsh : ∀ (S : Formalism.L2.SG.PackageTie2.ColT hinj) ρ, (Formalism.L2.SG.PackageTie2.shT hinj S).ofLp ρ = shP X u (toCu X hK S).1 (cs.h ρ) := fun S ρ => rfl
  show inner ℂ (Formalism.L2.SG.PackageTie2.shT hinj T') (Formalism.L2.SG.PackageTie2.shT hinj T) = _
  rw [PiLp.inner_apply]
  simp only [hsh]
  rw [key]
  have hd : ∀ (S : Formalism.L2.SG.PackageTie2.ColT hinj) c, colDictL X Tr hK (toCu X hK S) c = fun z => Tr.J (shP X u (toCu X hK S).1 (Tr.hc c)) (F.val0.eY z) := fun S c => rfl
  have hterm : ∀ c, (D.fm u).ipV 0 c (colDictL X Tr hK (toCu X hK T) c) (colDictL X Tr hK (toCu X hK T') c) = ⟪shP X u (toCu X hK T').1 (Tr.hc c), shP X u (toCu X hK T).1 (Tr.hc c)⟫_ℂ := by
    intro c
    rw [hd, hd]
    exact Tr.J_isom c _ _
  unfold Formalism.BasicNotions.MemberForms.ipC
  simp only [hwt1, one_mul, hterm]

end GlobalTheory.St

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIsometricOfRepresentativesStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnDictionary_isometric_of_representatives : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK) → ∀ (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (cs : Formalism.L2.SG.TermOp.ColSys X u what₂) (hinj : Function.Injective (Formalism.L2.SG.TermOp.sharp hK cs)), Formalism.L2.SG.TermOp.ColReps hK cs → ColDictIsom X Tr hK cs hinj := by
  first | exact @GlobalTheory.St.colDict_isometric_of_reps | exact GlobalTheory.St.colDict_isometric_of_reps | (intros; apply GlobalTheory.St.colDict_isometric_of_reps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIntoStepZeroForms
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIntoStepZeroForms
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDictInto_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictInto X Tr hK := by
  intro D X u F Tr hK hσ hL T
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  obtain ⟨Φ, hΦ⟩ := frame_action_mulEquiv_local D X u Tr.wt Tr.ιA hW hA hσ
  obtain ⟨-, hΓ, hsT⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
  obtain ⟨hψ, -, hφ, -, -⟩ := cols_sharp_dictionary D X u hK
  have key := GlobalTheory.adForms_of_equivariant D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hinf X u) (Hfin X u)
    (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 D.what₂.Tau (Formalism.L2.Forms.embT D)
    ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ
    (fun h => (hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).1)
    (fun h hk hy => (hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).2 hk hy)
    hΓ
    (fun γ g hγ ξ y y' hy => Tr.J_eqv _ (iotaI X u γ).2 ξ y y' (by rw [hsT γ g hγ]; exact hy))
    (fun ξ => by rw [← Formalism.L2.Forms.lamT_zero]; exact Tr.J_val ξ)
    (shP X u T.1) (hφ T)
  rw [Formalism.L2.Forms.Mu0_iff F.val0]
  refine ⟨_, key, ?_⟩
  funext c z
  have hc : Φ.symm (F.cls0.y c * Tr.h0⁻¹) = Tr.hc c :=
    Φ.symm_apply_eq.2 ((hΦ (Tr.hc c) _).1 (Tr.hc_rep c)).symm
  simp only [Formalism.L2.Forms.res, LinearMap.funLeft_apply, hc]
  show Tr.J (shP X u T.1 (Tr.hc c)) z = Tr.J (shP X u T.1 (Tr.hc c)) (F.val0.eY (F.val0.eY.symm z))
  rw [Equiv.apply_symm_apply]

end GlobalTheory.St
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIntoStepZeroFormsStatement
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnDictionary_into_stepZeroForms : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictInto X Tr hK := by
  first | exact @GlobalTheory.St.colDictInto_of_levelMatch | exact GlobalTheory.St.colDictInto_of_levelMatch | (intros; apply GlobalTheory.St.colDictInto_of_levelMatch <;> assumption)
end
end

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDictCore_holds : ∀ D : D7, ColDictCore D := by
  intro D
  unfold ColDictCore
  intro X u F Tr hK hLev hStab

  have hConj : ∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a) :=
    GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X Tr.ιA ⟨Tr.ιA_rat, Tr.ιA_int⟩
  refine ⟨(GlobalTheory.T.transport_represents_classes_weight_one D X u F Tr hK hConj hLev).1, GlobalTheory.T.columnDictionary_into_stepZeroForms D X u F Tr hK hConj hLev,
    GlobalTheory.T.columnDictionary_bijective_of_levelMatch D X u F Tr hK hConj hLev, ?_⟩
  intro what₂ cs hinj hReps
  exact GlobalTheory.T.columnDictionary_isometric_of_representatives D X u F Tr hK hConj hLev hStab what₂ cs hinj hReps

end GlobalTheory.St
