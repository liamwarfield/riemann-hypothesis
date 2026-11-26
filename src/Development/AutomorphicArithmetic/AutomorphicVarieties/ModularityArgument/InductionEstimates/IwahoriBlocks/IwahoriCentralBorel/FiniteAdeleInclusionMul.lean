module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.BlockFrameConjugationIdentity

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.ParLaw
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical NumberField.AdeleRing

section Ring

variable {R : Type} [CommRing R]

private def topR (X : UPos (2 + 2) 2 → R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j => X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), i.2, Nat.le_add_right 2 j⟩

private theorem unipGL_val (X : UPos (2 + 2) 2 → R) :
    (unipGL X : GL (Fin (2 + 2)) R).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 (topR X) 0 1) := by
  rw [coe_unipGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMatrix, blockEntry_apply, topR] <;> rfl

private theorem topR_surj (B : Matrix (Fin 2) (Fin 2) R) : ∃ X : UPos (2 + 2) 2 → R, topR X = B := by
  refine ⟨fun p => B ⟨p.1.1, p.2.1⟩ ⟨p.1.2 - 2, by have := p.1.2.2; omega⟩, ?_⟩
  ext i j
  simp [topR]

private theorem unip_mul_blk (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    (unipGL X * blk a b : GL (Fin (2 + 2)) R).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a.val (topR X * b.val) 0 b.val) := by
  rw [Units.val_mul, unipGL_val]
  simp only [PositivityTheory.Rg.Tf.Adel.blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem blk_mul_unip (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    (blk a b * unipGL X : GL (Fin (2 + 2)) R).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a.val (a.val * topR X) 0 b.val) := by
  rw [Units.val_mul, unipGL_val]
  simp only [PositivityTheory.Rg.Tf.Adel.blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

private theorem conj_unip (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    ∃ X' : UPos (2 + 2) 2 → R, PositivityTheory.Rg.Tf.Adel.blk a b * unipGL X = unipGL X' * blk a b := by
  obtain ⟨X', h⟩ := topR_surj (a.val * topR X * (b⁻¹).val)
  refine ⟨X', Units.ext ?_⟩
  rw [blk_mul_unip, unip_mul_blk, h, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

private theorem eq_unip_blk (g : GL (Fin (2 + 2)) R) (a b : GL (Fin 2) R)
    (h₁ : ∀ i j : Fin 2, g.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = a.val i j)
    (h₂ : ∀ i j : Fin 2, g.val (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = b.val i j)
    (h₃ : ∀ i j : Fin 2, g.val (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0) :
    ∃ X : UPos (2 + 2) 2 → R, g = unipGL X * blk a b := by
  obtain ⟨X, hX⟩ := topR_surj (Matrix.of (fun i j : Fin 2 => g.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) * (b⁻¹).val)
  refine ⟨X, Units.ext ?_⟩
  rw [unip_mul_blk, hX, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [h₁, h₂, h₃, Matrix.reindex_apply, Matrix.submatrix_apply]

end Ring

variable {K : Type} [Field K] [NumberField K]

private theorem lv_nn (m₁ m₂ : G1 K 2) (t : ℝ) (X : UPos (2 + 2) 2 → 𝔸[K]) :
    ∃ X', lv (K := K) m₁ m₂ t * nn X = nn X' * lv m₁ m₂ t := by
  obtain ⟨X', h⟩ := conj_unip X ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t))
  refine ⟨X', Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, (blkLaws (K := K)).1, coe_unipOne, coe_unipOne, h]

private theorem ad_ext {x y : 𝔸[K]} (h₁ : ∀ w, infEval w x = infEval w y) (h₂ : ∀ v, finEval v x = finEval v y) : x = y := by
  exact Prod.ext (funext h₁) (Subtype.ext (funext h₂))

private theorem infAt_fin {n : ℕ} (w : InfinitePlace K) (x : AdelicGLn.FiniteAdelicGL K n) : infAt w (finEmb K n x) = 1 := by
  show (AdelicGLn.infiniteEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n x)).1) w = 1
  rw [AutomorphicForm.prodEquiv_finEmb, map_one]
  rfl

private theorem ent_inf {n : ℕ} (w : InfinitePlace K) (x : AdelicGLn.AdelicGL K n) (i j) :
    infEval w (x.val i j) = (infAt w x).val i j := rfl

private theorem ent_fin {n : ℕ} (v : Pl K) (x : AdelicGLn.AdelicGL K n) (i j) :
    finEval v (x.val i j) = (finAt v x).val i j := rfl

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem lev_fst (w : Pl K) (x : PW w) (i j : Fin 2) :
    (lev₂ w x).1.val i j = x.1.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) := rfl

private theorem lev_snd (w : Pl K) (x : PW w) (i j : Fin 2) :
    (lev₂ w x).2.val i j = x.1.val (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) := rfl

private theorem par_low (w : Pl K) (x : PW w) (i j : Fin 2) :
    x.1.val (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 :=
  mem_parab_iff.1 x.2 true false i j (by decide)

private theorem fin_dec {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2))
    (hw : Function.Injective w) (h₂ : IsEmb w ι₂) (h₄ : IsEmb w ι₄) (p : ∀ i, PW (w i)) :
    ∃ X : UPos (2 + 2) 2 → 𝔸[K], finEmb K (2 + 2) (ι₄ (piIncl (fun i => PW (w i)) p)) =
      unipGL X * PositivityTheory.Rg.Tf.Adel.blk (finEmb K 2 (ι₂ fun i => (lev₂ (w i) (p i)).1)) (finEmb K 2 (ι₂ fun i => (lev₂ (w i) (p i)).2)) := by
  obtain ⟨-, c₂, d₂, -⟩ := (embEx 2 w hw).2 ι₂ h₂
  obtain ⟨-, c₄, d₄, -⟩ := (embEx (2 + 2) w hw).2 ι₄ h₄
  have c₂' : ∀ (g : GS 2 w) i, finAt (w i) (finEmb K 2 (ι₂ g)) = g i := c₂
  have d₂' : ∀ (g : GS 2 w) v, v ∉ im w → finAt v (finEmb K 2 (ι₂ g)) = 1 := d₂
  have c₄' : ∀ (g : GS (2 + 2) w) i, finAt (w i) (finEmb K (2 + 2) (ι₄ g)) = g i := c₄
  have d₄' : ∀ (g : GS (2 + 2) w) v, v ∉ im w → finAt v (finEmb K (2 + 2) (ι₄ g)) = 1 := d₄
  apply eq_unip_blk
  · intro i j
    refine ad_ext (fun u => ?_) (fun v => ?_)
    · rw [ent_inf, ent_inf, infAt_fin, infAt_fin]
      simp [Matrix.one_apply]
    · rw [ent_fin, ent_fin]
      by_cases hv : v ∈ im w
      · obtain ⟨i₀, -, rfl⟩ := Finset.mem_image.1 hv
        rw [c₄', c₂']
        exact (lev_fst _ _ i j).symm
      · rw [d₄' _ _ hv, d₂' _ _ hv]
        simp [Matrix.one_apply]
  · intro i j
    refine ad_ext (fun u => ?_) (fun v => ?_)
    · rw [ent_inf, ent_inf, infAt_fin, infAt_fin]
      simp [Matrix.one_apply]
    · rw [ent_fin, ent_fin]
      by_cases hv : v ∈ im w
      · obtain ⟨i₀, -, rfl⟩ := Finset.mem_image.1 hv
        rw [c₄', c₂']
        exact (lev_snd _ _ i j).symm
      · rw [d₄' _ _ hv, d₂' _ _ hv]
        simp [Matrix.one_apply]
  · intro i j
    refine ad_ext (fun u => ?_) (fun v => ?_)
    · rw [ent_inf, infAt_fin, map_zero]
      simp [Matrix.one_apply]
    · rw [ent_fin]
      by_cases hv : v ∈ im w
      · obtain ⟨i₀, -, rfl⟩ := Finset.mem_image.1 hv
        rw [c₄', map_zero]
        exact par_low _ _ i j
      · rw [d₄' _ _ hv]
        simp [Matrix.one_apply]
        rfl

private theorem mod_S {n r : ℕ} (w : Fin r → Pl K) (ι : GS n w →* FA K n) (hw : Function.Injective w) (hι : IsEmb w ι) (g : GS n w) :
    (detModule K n (finEmb K n (ι g)) : ℝ) =
      ∏ i, GlobalTheory.SplitWeil.nabs ((w i).adicCompletion K) (Matrix.GeneralLinearGroup.det (g i)) := by
  obtain ⟨-, c, d, -⟩ := (embEx n w hw).2 ι hι
  have c' : ∀ i, finAt (w i) (finEmb K n (ι g)) = g i := c g
  have d' : ∀ v, v ∉ im w → finAt v (finEmb K n (ι g)) = 1 := d g
  set x := finEmb K n (ι g) with hx
  have hi : ∀ u : InfinitePlace K, ((AdelicGLn.det K n x : GroundTheory.Global.IdeleGroup K) : 𝔸[K]).1 u = 1 := fun u => by
    have e : ((AdelicGLn.det K n x : GroundTheory.Global.IdeleGroup K) : 𝔸[K]).1 u = (infAt u x).val.det := by
      rw [AdelicGLn.coe_det]
      exact RingHom.map_det (infEval u) _
    rw [e, hx, infAt_fin]
    simp
  have hf : ∀ v : Pl K, ((AdelicGLn.det K n x : GroundTheory.Global.IdeleGroup K) : 𝔸[K]).2 v = (finAt v x).val.det := fun v => by
    rw [AdelicGLn.coe_det]
    exact RingHom.map_det (finEval v) _
  have hs : Function.mulSupport (fun v : Pl K => ‖(finAt v x).val.det‖) ⊆ ((im w : Finset (Pl K)) : Set (Pl K)) := by
    intro v hv
    by_contra hn
    apply hv
    simp [d' v (by simpa using hn)]
  rw [detModule, MonoidHom.comp_apply, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  simp only [hi, hf, norm_one, one_pow, Finset.prod_const_one, one_mul]
  rw [finprod_eq_prod_of_mulSupport_subset _ hs, Finset.prod_image fun a _ b _ h => hw h]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [c']
  exact ((GlobalTheory.CompletionNorm.norm_nabs_valuation K (w i)).1 (Matrix.GeneralLinearGroup.det (g i))).1

private theorem scal_blk (u : GroundTheory.Global.IdeleGroup K) :
    scalarUnits K (2 + 2) u = PositivityTheory.Rg.Tf.Adel.blk (scalarUnits K 2 u) (scalarUnits K 2 u) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective j
  rw [scalarUnits_apply, scalarUnits_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [PositivityTheory.Rg.Tf.Adel.blk, diagUnits, Matrix.diagonal_apply]

private theorem cen_blk (s : {r : ℝ // 0 < r}) :
    centralSection K (2 + 2) (s * s) = PositivityTheory.Rg.Tf.Adel.blk (centralSection K 2 s) (centralSection K 2 s) := by
  have e : rpowHom (((2 + 2 : ℕ) * Module.finrank ℚ K : ℝ))⁻¹ (s * s) = rpowHom ((2 * Module.finrank ℚ K : ℝ))⁻¹ s := by
    apply Subtype.ext
    have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    change (s.1 * s.1) ^ _ = s.1 ^ _
    rw [Real.mul_rpow s.2.le s.2.le, ← Real.rpow_add s.2]
    congr 1
    push_cast
    field_simp
    norm_num
  simp only [centralSection, MonoidHom.comp_apply]
  rw [e, scal_blk]
  rfl

private theorem dl_val (w : Pl K) (x : PW w) :
    ((dl w x : ℂˣ) : ℂ) =
      ((GlobalTheory.SplitWeil.nabs (w.adicCompletion K) (Matrix.GeneralLinearGroup.det (lev₂ w x).1) /
        GlobalTheory.SplitWeil.nabs (w.adicCompletion K) (Matrix.GeneralLinearGroup.det (lev₂ w x).2) : ℝ) : ℂ) := by
  have e : leviProj (w.adicCompletion K) (two (stdSum (rfl : 2 + 2 = 2 + 2))) x =
      leviTwo (w.adicCompletion K) (Fin 2) (Fin 2) (lev₂ w x) :=
    ((leviTwo (w.adicCompletion K) (Fin 2) (Fin 2)).apply_symm_apply _).symm
  rw [dl, MonoidHom.comp_apply, e, deltaHalf_two, Units.val_mul, val_absPow, val_absPow]
  have h₁ : (((Fintype.card (Fin 2) : ℕ) : ℂ) / 2) = 1 := by simp
  have h₂ : (-((Fintype.card (Fin 2) : ℕ) : ℂ) / 2) = -1 := by simp
  rw [h₁, h₂, Complex.cpow_one, Complex.cpow_neg_one, Complex.ofReal_div, div_eq_mul_inv]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.parLaw :
    ∀ {K : Type} [Field K] [NumberField K] {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₂ → IsEmb w ι₄ →
      (∀ m₁ m₂ t X, ∃ X', lv (K := K) m₁ m₂ t * nn X = nn X' * lv m₁ m₂ t) ∧
      ∀ p : ∀ i, PW (w i), ∃ X t, fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) = nn X * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t ∧ Complex.exp (2 * (t : ℂ)) = (dS w p : ℂ) := by
  intro K _ _ r w ι₂ ι₄ hw h₂ h₄
  refine ⟨lv_nn, fun p => ?_⟩
  obtain ⟨X, hX⟩ := fin_dec w ι₂ ι₄ hw h₂ h₄ p
  have hmA := mod_S w ι₂ hw h₂ fun i => (lev₂ (w i) (p i)).1
  have hmD := mod_S w ι₂ hw h₂ fun i => (lev₂ (w i) (p i)).2
  set a := ι₂ fun i => (lev₂ (w i) (p i)).1 with ha
  set b := ι₂ fun i => (lev₂ (w i) (p i)).2 with hb
  set A := finEmb K 2 a with hA
  set D := finEmb K 2 b with hD
  set α := detModule K 2 A with hα
  set δ := detModule K 2 D with hδ
  set t : ℝ := (Real.log α.1 - Real.log δ.1) / 2 with ht
  let s : {r : ℝ // 0 < r} := ⟨Real.exp ((Real.log α.1 + Real.log δ.1) / 2), Real.exp_pos _⟩
  let e : {r : ℝ // 0 < r} := ⟨Real.exp t, Real.exp_pos _⟩
  let e' : {r : ℝ // 0 < r} := ⟨Real.exp (-t), Real.exp_pos _⟩
  have hse : α = s * e := Subtype.ext (by
    change α.1 = Real.exp _ * Real.exp _
    rw [← Real.exp_add, ht, show (Real.log α.1 + Real.log δ.1) / 2 + (Real.log α.1 - Real.log δ.1) / 2 = Real.log α.1 by ring,
      Real.exp_log α.2])
  have hse' : δ = s * e' := Subtype.ext (by
    change δ.1 = Real.exp _ * Real.exp _
    rw [← Real.exp_add, ht, show (Real.log α.1 + Real.log δ.1) / 2 + -((Real.log α.1 - Real.log δ.1) / 2) = Real.log δ.1 by ring,
      Real.exp_log δ.2])
  have hee : e * e' = 1 := Subtype.ext (by
    change Real.exp _ * Real.exp _ = 1
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero])
  have hdet : detModule K (2 + 2) (finEmb K (2 + 2) (ι₄ (piIncl (fun i => PW (w i)) p))) = s * s := by
    have hu : detModule K (2 + 2) (unipGL X) = 1 := by
      have := mem_normOneGL_iff_detModule.1 (unipOne (K := K) (n := 2 + 2) 2 X).2
      rwa [coe_unipOne] at this
    have hbl := (blkLaws (K := K)).2.2.2.2.1 A D
    rw [hX, map_mul, hu, one_mul, hbl, ← hα, ← hδ, hse, hse']
    calc s * e * (s * e') = s * s * (e * e') := by ac_rfl
      _ = s * s := by rw [hee, mul_one]
  refine ⟨X, t, Subtype.ext ?_, ?_⟩
  · have h1 : ((fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
        finEmb K (2 + 2) (ι₄ (piIncl (fun i => PW (w i)) p)) * (centralSection K (2 + 2) (s * s))⁻¹ := by
      rw [← hdet]; rfl
    have hz : ∀ α' u e'' : {r : ℝ // 0 < r}, u * e'' = α' →
        (centralSection K 2 α')⁻¹ * centralSection K 2 e'' = centralSection K 2 u⁻¹ := by
      intro α' u e'' hu
      rw [← map_inv, ← map_mul, ← hu, mul_inv, mul_assoc, inv_mul_cancel, mul_one]
    have b₁ : (((blocks ι₂ p).1 : G1 K 2) : AdelicGLn.AdelicGL K 2) = A * (centralSection K 2 α)⁻¹ := rfl
    have b₂ : (((blocks ι₂ p).2 : G1 K 2) : AdelicGLn.AdelicGL K 2) = D * (centralSection K 2 δ)⁻¹ := rfl
    have z₁ : zt K t = centralSection K 2 e := rfl
    have z₂ : zt K (-t) = centralSection K 2 e' := rfl
    rw [Subgroup.coe_mul, coe_unipOne, (blkLaws (K := K)).1, h1, hX, b₁, b₂, z₁, z₂, mul_assoc A, mul_assoc D,
      hz α s e hse.symm, hz δ s e' hse'.symm, ← map_inv, mul_inv, cen_blk, mul_assoc,
      (blkLaws (K := K)).2.2.2.2.2.1]
  · have hd : ((dS w p : ℂˣ) : ℂ) = ((α.1 / δ.1 : ℝ) : ℂ) := by
      rw [dS, MonoidHom.finsetProd_apply, Units.coe_prod]
      simp only [MonoidHom.comp_apply, Pi.evalMonoidHom_apply, dl_val]
      rw [← Complex.ofReal_prod, Finset.prod_div_distrib, ← hmA, ← hmD]
    rw [hd, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 1
    rw [ht, show (2 : ℝ) * ((Real.log α.1 - Real.log δ.1) / 2) = Real.log α.1 - Real.log δ.1 by ring, Real.exp_sub,
      Real.exp_log α.2, Real.exp_log δ.2]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.FiniteAdeleInclusionMul
open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem finite_projection_one {K : Type} [Field K] [NumberField K] {n : ℕ} : fin1 (1 : FA K n) = 1 :=
  map_one (MultiplicityOne.finProj K n)

private theorem finite_adele_inclusion_mul {K : Type} [Field K] [NumberField K] {n : ℕ} (a b : FA K n) : fin1 (a * b) = fin1 a * fin1 b :=
  map_mul (MultiplicityOne.finProj K n) a b

private theorem zt0 {K : Type} [Field K] [NumberField K] : zt K 0 = 1 := by
  have h : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext (by simp)
  rw [zt, h, map_one]

private theorem lv0 {K : Type} [Field K] [NumberField K] (a b : G1 K 2) :
    ((lv a b 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (a : AdelicGLn.AdelicGL K 2) (b : AdelicGLn.AdelicGL K 2) := by
  rw [blkLaws.1, neg_zero, zt0, mul_one, mul_one]

private theorem hh0 {K : Type} [Field K] [NumberField K] (a b : G1 K 2) (x : G1 K (2 + 2)) :
    HH (lv a b 0 * x) = HH x := by
  have h := (hpSpec (K := K)).1 0 a b 0 x
  have h0 : (nn 0 : G1 K (2 + 2)) = 1 := unipOne_zero 2
  rwa [h0, one_mul, zero_add] at h

private theorem sec_ray {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
    {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f) (t : ℝ) (g : G1 K (2 + 2)) : f (lv 1 1 t * g) = f g := by
  refine hs.ray ⟨Real.exp t, Real.exp_pos t⟩ _ g ?_
  have h : (⟨Real.exp (-t), Real.exp_pos (-t)⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹ := by
    apply Subtype.ext
    change Real.exp (-t) = (Real.exp t)⁻¹
    rw [Real.exp_neg]
  rw [Subgroup.coe_mul, blkLaws.1, zt, zt, h]
  simp

private theorem reps_comb {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
    (τ : Submodule ℂ (L2 μ)) {ι : Type} (s : Finset ι) (φ : ι → G1 K n → ℂ) (c : ι → ℂ)
    (h : ∀ i, ∃ v ∈ τ, Reps μ v (φ i)) : ∃ v ∈ τ, Reps μ v (fun y => ∑ i ∈ s, c i * φ i y) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, τ.zero_mem, ?_⟩
    filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K n) μ))] with y hy
    simpa only [Finset.sum_empty, Pi.zero_apply] using hy
  | insert i s hi ih =>
    obtain ⟨v, hv, hr⟩ := ih
    obtain ⟨u, hu, hq⟩ := h i
    refine ⟨c i • u + v, τ.add_mem (τ.smul_mem _ hu) hv, ?_⟩
    filter_upwards [MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_add (c i • u) v),
      MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) (Lp.coeFn_smul (c i) u), hr, hq] with y e₁ e₂ e₃ e₄
    rw [e₁, Pi.add_apply, e₂, Pi.smul_apply, e₃, e₄, Finset.sum_insert hi, smul_eq_mul]

private theorem flat_lv {K : Type} [Field K] [NumberField K] (f : G1 K (2 + 2) → ℂ) (a b : G1 K 2) (x : G1 K (2 + 2)) :
    flat 0 f (lv a b 0 * x) = Complex.exp (2 * (HH x : ℂ)) * f (lv a b 0 * x) := by
  simp only [flat, zero_add]
  rw [show HP 2 2 (lv a b 0 * x) = HH x from hh0 a b x]

private theorem val_mem {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {μ₂ : Measure (G1 K 2)} [μ₂.IsHaarMeasure]
    {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {κ : Measure (archCompact K (2 + 2))} {e : archCompact K (2 + 2) → ℂ} {κ₂ p₁ p₂ k₀}
    (hL : ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀) {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2))
    (hw : Function.Injective w) (h₄ : IsEmb w ι₄) {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f) (hfa : FixA κ e f)
    {U : ∀ v : Pl K, Subgroup (Gw (2 + 2) v)} (hU : Lev U) (hfU : FixF (levOn (im w) U) f) (g : GS (2 + 2) w) :
    (fun m : G1 K 2 × G1 K 2 => flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g))) ∈
      tensFn (Xs μ₂ τ₁ κ₂ p₁ (im w)) (Xs μ₂ τ₂ κ₂ p₂ (im w)) := by
  obtain ⟨d, φ, ψ, hφ, hψ, hx⟩ := hs.levi (arc1 k₀ * fin1 (ι₄ g))
  have hx' : ∀ a b, f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g)) = ∑ i, φ i a * ψ i b := fun a b =>
    hx a b _ (by rw [mul_assoc, Subgroup.coe_mul (x := lv a b 0), lv0])
  obtain ⟨U₂, hU₂, hlev⟩ := levBlock w ι₄ hw h₄ U hU g
  have hv := hL.val f hs hfa (ι₄ g)
  have hcl : Continuous fun p : G1 K 2 × G1 K 2 => f (lv p.1 p.2 0 * arc1 k₀ * fin1 (ι₄ g)) :=
    hs.cont.comp (((blkLaws (K := K)).2.2.2.1.comp
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))).mul continuous_const |>.mul continuous_const)
  have hsplit₁ : ∀ a b (u : G1 K 2), lv (a * u) b 0 = lv a b 0 * lv u 1 0 := fun a b u => by
    rw [blkLaws.2.1]; simp
  have hsplit₂ : ∀ a b (u : G1 K 2), lv a (b * u) 0 = lv a b 0 * lv 1 u 0 := fun a b u => by
    rw [blkLaws.2.1]; simp
  have hF : (fun m : G1 K 2 × G1 K 2 => flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g))) =
      Complex.exp (2 * (HH (arc1 k₀ * fin1 (ι₄ g)) : ℂ)) • fun m : G1 K 2 × G1 K 2 => f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ g)) := by
    funext m
    rw [mul_assoc, flat_lv]
    simp [mul_assoc]
  rw [hF]
  refine Submodule.smul_mem _ _ ((tensLaws _ _).2 _ d φ ψ (fun x => hx' x.1 x.2) (fun b => ?_) (fun a => ?_))
  · refine Submodule.subset_span ⟨hcl.comp (continuous_id.prodMk continuous_const), ?_, hv.1 b, U₂, hU₂, fun u hu a => ?_⟩
    · have h := reps_comb μ₂ τ₁ Finset.univ φ (fun i => ψ i b) (fun i => let ⟨v, hv, hr⟩ := (hφ i).2; ⟨v, hv, hr⟩)
      simpa only [hx', mul_comm] using h
    · obtain ⟨u', hu', hk⟩ := hlev u hu 1 (one_mem _)
      have h1 := hk k₀
      rw [finite_projection_one] at h1
      have h2 : lv (a * fin1 u) b 0 * arc1 k₀ * fin1 (ι₄ g) = lv a b 0 * arc1 k₀ * fin1 (ι₄ g) * fin1 u' := by
        rw [hsplit₁, mul_assoc (lv a b 0), mul_assoc (lv a b 0), h1]
        simp only [mul_assoc]
      show f (lv (a * fin1 u) b 0 * arc1 k₀ * fin1 (ι₄ g)) = f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g))
      rw [h2]
      exact hfU u' hu' _
  · refine Submodule.subset_span ⟨hcl.comp (continuous_const.prodMk continuous_id), ?_, hv.2 a, U₂, hU₂, fun u hu b => ?_⟩
    · have h := reps_comb μ₂ τ₂ Finset.univ ψ (fun i => φ i a) (fun i => let ⟨v, hv, hr⟩ := (hψ i).2; ⟨v, hv, hr⟩)
      simpa only [hx'] using h
    · obtain ⟨u', hu', hk⟩ := hlev 1 (one_mem _) u hu
      have h1 := hk k₀
      rw [finite_projection_one] at h1
      have h2 : lv a (b * fin1 u) 0 * arc1 k₀ * fin1 (ι₄ g) = lv a b 0 * arc1 k₀ * fin1 (ι₄ g) * fin1 u' := by
        rw [hsplit₂, mul_assoc (lv a b 0), mul_assoc (lv a b 0), h1]
        simp only [mul_assoc]
      show f (lv a (b * fin1 u) 0 * arc1 k₀ * fin1 (ι₄ g)) = f (lv a b 0 * arc1 k₀ * fin1 (ι₄ g))
      rw [h2]
      exact hfU u' hu' _

private theorem law_eq {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)}
    {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2))
    (hw : Function.Injective w) (h₂ : IsEmb w ι₂) (h₄ : IsEmb w ι₄) {f : G1 K (2 + 2) → ℂ} (hs : IsSec τ₁ τ₂ f)
    (k₀ : archCompact K (2 + 2)) (p : ∀ i, PW (w i)) (g : GS (2 + 2) w) (m : G1 K 2 × G1 K 2) :
    flat 0 f (lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p * g))) =
      (dS w p : ℂ) * flat 0 f (lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 * arc1 k₀ * fin1 (ι₄ g)) := by
  obtain ⟨hA, hB⟩ := parLaw w ι₂ ι₄ hw h₂ h₄
  obtain ⟨X, t, hX, ht⟩ := hB p
  obtain ⟨X', hX'⟩ := hA m.1 m.2 0 X
  have hc : Commute (arc1 k₀) (fin1 (ι₄ (piIncl (fun i => PW (w i)) p))) := (levLaws (K := K) (2 + 2) (im w)).2.2.1 k₀ _
  have key : lv m.1 m.2 0 * arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p * g)) =
      nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g)) := by
    have hl : lv m.1 m.2 0 * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t = lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t := by
      rw [blkLaws.2.1, zero_add]
    rw [map_mul, finite_adele_inclusion_mul, ← hl]
    calc lv m.1 m.2 0 * arc1 k₀ * (fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) * fin1 (ι₄ g))
        = lv m.1 m.2 0 * (arc1 k₀ * fin1 (ι₄ (piIncl (fun i => PW (w i)) p))) * fin1 (ι₄ g) := by simp only [mul_assoc]
      _ = lv m.1 m.2 0 * (fin1 (ι₄ (piIncl (fun i => PW (w i)) p)) * arc1 k₀) * fin1 (ι₄ g) := by rw [hc.eq]
      _ = (lv m.1 m.2 0 * nn X) * lv (blocks ι₂ p).1 (blocks ι₂ p).2 t * (arc1 k₀ * fin1 (ι₄ g)) := by
          rw [hX]; simp only [mul_assoc]
      _ = _ := by rw [hX']; simp only [mul_assoc]
  have hray : lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t =
      lv 1 1 t * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 := by
    rw [blkLaws.2.1]; simp
  have hf : f (nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))) =
      f (lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) 0 * (arc1 k₀ * fin1 (ι₄ g))) := by
    rw [mul_assoc, hs.unip, hray, mul_assoc, sec_ray hs]
  have hh := (hpSpec (K := K)).1 X' (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t (arc1 k₀ * fin1 (ι₄ g))
  rw [key, mul_assoc (lv _ _ 0), flat_lv, ← ht]
  simp only [flat, zero_add]
  rw [show HP 2 2 (nn X' * lv (m.1 * (blocks ι₂ p).1) (m.2 * (blocks ι₂ p).2) t * (arc1 k₀ * fin1 (ι₄ g))) = t + HH (arc1 k₀ * fin1 (ι₄ g)) from hh, hf]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.evMem :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) κ₂ p₁ p₂ k₀, Pair μ₂ τ₁ τ₂ → ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι₂ : GS 2 w →* FA K 2) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₂ → IsEmb w ι₄ →
      ∀ φ ∈ Zs τ₁ τ₂ κ e (im w), ev ι₄ k₀ φ ∈ IndF (piIncl fun i => PW (w i)) (xS ι₂) (tensFn (Xs μ₂ τ₁ κ₂ p₁ (im w)) (Xs μ₂ τ₂ κ₂ p₂ (im w))) := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ _ hL r w ι₂ ι₄ hw h₂ h₄ φ hφ
  obtain ⟨hiff, hsm⟩ := zMem μ₂ τ₁ τ₂ κ e hL.idem
  have hop := (hsm w ι₄ hw h₄ φ hφ).1
  obtain ⟨f, hs, hfa, ⟨U, hU, hfU⟩, rfl⟩ := (hiff _ φ).1 hφ
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · refine ⟨fun g => val_mem hL w ι₄ hw h₄ hs hfa hU hfU g, fun p g => ?_⟩
    funext m
    have h := law_eq (τ₁ := τ₁) (τ₂ := τ₂) w ι₂ ι₄ hw h₂ h₄ hs k₀ p g m
    simpa [ev, xS, twist, rightReg, LinearMap.funLeft] using h
  · have hst : ∀ g, rS ι₄ g (flat 0 f) = flat 0 f →
        rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) g (ev ι₄ k₀ (flat 0 f)) = ev ι₄ k₀ (flat 0 f) := by
      intro g hg
      conv_rhs => rw [← hg]
      funext x m
      simp [ev, rS, rightReg, LinearMap.funLeft, mul_assoc]
    show IsOpen {g | rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) g (ev ι₄ k₀ (flat 0 f)) = ev ι₄ k₀ (flat 0 f)}
    refine isOpen_iff_mem_nhds.2 fun g₀ hg₀ => ?_
    have h1 : (1 : GS (2 + 2) w) ∈ {g | rS ι₄ g (flat 0 f) = flat 0 f} := by simp
    have hn : (fun x => g₀⁻¹ * x) ⁻¹' {g | rS ι₄ g (flat 0 f) = flat 0 f} ∈ 𝓝 g₀ :=
      ((continuous_const.mul continuous_id).continuousAt (x := g₀)).preimage_mem_nhds
        (hop.mem_nhds (by simpa using h1))
    filter_upwards [hn] with x hx
    have h2 := hst _ hx
    have h3 : x = g₀ * (g₀⁻¹ * x) := by group
    show rightReg ℂ (GS (2 + 2) w) (G1 K 2 × G1 K 2 → ℂ) x _ = _
    rw [h3, map_mul, Module.End.mul_apply, h2]
    exact hg₀
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.RayLv
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.IwahoriCentralBorel.FinIwa
section Par

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem unip_corner {a b : ℕ} {R : Type} [CommRing R] (X : UPos (a + b) a → R) :
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 ((unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂ 0 (1 : Matrix (Fin b) (Fin b) R) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [unipMatrix, blockEntry_apply, Matrix.one_apply, Matrix.toBlocks₁₂, Fin.ext_iff] <;> omega

private theorem unip_any {a b : ℕ} {R : Type} [CommRing R] (B : Matrix (Fin a) (Fin b) R) : ∃ X : UPos (a + b) a → R,
    (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks 1 B 0 (1 : Matrix (Fin b) (Fin b) R) := by
  refine ⟨fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 B 0 0) p.1.1 p.1.2, ?_⟩
  rw [unip_corner]
  congr 1
  ext i j
  have : (Fin.castAdd b i : Fin (a + b)) ≠ Fin.natAdd a j := by
    simp [Fin.ext_iff]; omega
  simp [unipMatrix, blockEntry_apply, Matrix.toBlocks₁₂, this]

private theorem split_par {a b : ℕ} {R : Type} [CommRing R] (g : GL (Fin (a + b)) R)
    (h : (g.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : (g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ (c : GL (Fin a) R) (d : GL (Fin b) R) (X : UPos (a + b) a → R), g = unipGL X * blk c d := by
  have e1 : g.val.submatrix finSumFinEquiv finSumFinEquiv * g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv =
      (1 : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) := by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  have hg : ∀ M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R, g.val.submatrix finSumFinEquiv finSumFinEquiv = M →
      g.val = M.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rintro _ rfl
    simp
  generalize g.val.submatrix finSumFinEquiv finSumFinEquiv = M at *
  generalize g⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv = N at *
  have hM := (Matrix.fromBlocks_toBlocks M).symm
  rw [← Matrix.fromBlocks_toBlocks M, ← Matrix.fromBlocks_toBlocks N, h, h', Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at e1
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e1
  obtain ⟨e1, -, -, e2⟩ := e1
  obtain ⟨X, hX⟩ := unip_any (M.toBlocks₁₂ * N.toBlocks₂₂)
  refine ⟨⟨_, _, e1, mul_eq_one_comm.1 e1⟩, ⟨_, _, e2, mul_eq_one_comm.1 e2⟩, X, Units.ext ?_⟩
  have hX' : unipMatrix X = (Matrix.fromBlocks 1 (M.toBlocks₁₂ * N.toBlocks₂₂) 0 1).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hX]; simp
  rw [Units.val_mul, coe_unipGL, hX', hg M rfl]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_assoc, mul_eq_one_comm.1 e2, Matrix.mul_one]
  rw [← h, ← hM]

private theorem par_of_low {K : Type} [Field K] [NumberField K] (s : G1 K (2 + 2))
    (h : ((s : AdelicGLn.AdelicGL K (2 + 2)).val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0)
    (h' : ((s : AdelicGLn.AdelicGL K (2 + 2))⁻¹.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0) :
    ∃ X m₁ m₂ t, s = nn X * lv m₁ m₂ t := by
  obtain ⟨hlv, -, -, -, hdet, -⟩ := blkLaws (K := K)
  obtain ⟨a, d, X, hX⟩ := split_par (s : AdelicGLn.AdelicGL K (2 + 2)) h h'
  refine ⟨X, retractOne a, retractOne d, Real.log (detModule K 2 a).1, ?_⟩
  have h1 : detModule K 2 a * detModule K 2 d = 1 := by
    have := mem_normOneGL_iff_detModule.1 s.2
    rwa [hX, map_mul, mem_normOneGL_iff_detModule.1 (unipGL_mem_normOneGL _), one_mul, hdet] at this
  have z1 : zt K (Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 a) := by
    unfold zt
    congr 1
    exact Subtype.ext (Real.exp_log (detModule K 2 a).2)
  have z2 : zt K (-Real.log (detModule K 2 a).1) = centralSection K 2 (detModule K 2 d) := by
    unfold zt
    congr 1
    refine Subtype.ext ?_
    rw [eq_inv_of_mul_eq_one_right h1]
    show Real.exp (-Real.log _) = _
    rw [Real.exp_neg, Real.exp_log (detModule K 2 a).2]
    rfl
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, hlv, z1, z2, coe_retractOne, coe_retractOne, inv_mul_cancel_right, inv_mul_cancel_right]
  exact hX

private theorem low_of_borel {K : Type} [Field K] [NumberField K] {b : AdelicGLn.AdelicGL K (2 + 2)} (hb : b ∈ adelicBorel) :
    (b.val.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ = 0 := by
  ext i j
  refine mem_adelicBorel.1 hb ?_
  show finSumFinEquiv (Sum.inl j) < finSumFinEquiv (Sum.inr i)
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
  omega

end Par

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical NumberField.AdeleRing

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem snd_entry (x : AdelicGLn.FiniteAdelicGL K n) (a b : Fin n) :
    ((finEmb K n x : AdelicGLn.AdelicGL K n) a b).2 = x a b := by
  have h := AdelicGLn.prodEquiv_apply_snd K n (finEmb K n x) a b
  rw [prodEquiv_finEmb] at h
  exact h.symm

private theorem cf_snd (v : Pl K) (x : AdelicGLn.AdelicGL K n) : GM.cf v (AdelicGLn.prodEquiv K n x).2 = finAt v x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change ((finEmb K n (AdelicGLn.prodEquiv K n x).2 : AdelicGLn.AdelicGL K n) a b).2 v = (x a b).2 v
  rw [snd_entry, AdelicGLn.prodEquiv_apply_snd]

private theorem cf_mul (v : Pl K) (x y : AdelicGLn.FiniteAdelicGL K n) : GM.cf v (x * y) = GM.cf v x * GM.cf v y := by
  unfold GM.cf
  rw [map_mul, finAt_mul]

private theorem central_borel (s : {r : ℝ // 0 < r}) : centralSection K n s ∈ adelicBorel := by
  refine mem_adelicBorel.2 ?_
  rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits]
  exact Matrix.blockTriangular_diagonal _

private theorem fin_borel (y : AdelicGLn.FiniteAdelicGL K n)
    (hy : ∀ v : Pl K, ∀ i j : Fin n, j < i → GM.cf v y i j = 0) : finEmb K n y ∈ adelicBorel := by
  refine mem_adelicBorel.2 fun i j hij => ?_
  have hij' : j < i := hij
  refine adele_ext (fun w => ?_) fun v => ?_
  · have e1 : (finEmb K n y i j).1 = (1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j :=
      congrArg (fun z => z.1 i j) (prodEquiv_finEmb y)
    rw [e1, Matrix.one_apply_ne hij'.ne']
    rfl
  · exact hy v i j hij'

private theorem proj_borel (y : AdelicGLn.FiniteAdelicGL K n) (h : finEmb K n y ∈ adelicBorel) :
    (MultiplicityOne.finProj K n y : AdelicGLn.AdelicGL K n) ∈ adelicBorel := by
  rw [MultiplicityOne.coe_finProj]
  exact mul_mem h (inv_mem (central_borel _))

end

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.finIwa :
    ∀ {K : Type} [Field K] [NumberField K] {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ (h : FA K (2 + 2)) (k : archCompact K (2 + 2)), ∃ X m₁ m₂ t g u, (∀ U, u ∈ levOn (im w) U) ∧
        arc1 k * fin1 h = nn X * lv m₁ m₂ t * arc1 k * fin1 (ι₄ g) * fin1 u := by
  intro K _ _ r w ι hw hι h k
  obtain ⟨-, -, hoff, hdec, hcomm, -⟩ := (embEx (K := K) (2 + 2) w hw).2 ι hι
  obtain ⟨b, hb, c, hc, e⟩ := exists_adelicBorel_mul_maxCompact (finEmb K (2 + 2) h)
  have hh : h = (AdelicGLn.prodEquiv K (2 + 2) b).2 * (AdelicGLn.prodEquiv K (2 + 2) c).2 := by
    have := congrArg (fun x => (AdelicGLn.prodEquiv K (2 + 2) x).2) e
    simpa [prodEquiv_finEmb, map_mul] using this
  obtain ⟨g₁, b', eb, hb'⟩ := hdec (AdelicGLn.prodEquiv K (2 + 2) b).2
  obtain ⟨g₂, u, eu, hu⟩ := hdec (AdelicGLn.prodEquiv K (2 + 2) c).2
  have hcb : ι g₂ * b' = b' * ι g₂ := (hcomm g₂ b' hb').eq
  have hh2 : h = ι (g₁ * g₂) * b' * u := by
    rw [hh, eb, eu, map_mul, mul_assoc (ι g₁), ← mul_assoc b', ← hcb]
    simp only [mul_assoc]

  have hb1 : ∀ v ∉ im w, GM.cf v b' = finAt v b := fun v hv => by
    rw [← cf_snd, eb, cf_mul, hoff g₁ v hv, one_mul]
  have hu1 : ∀ v ∉ im w, GM.cf v u = finAt v c := fun v hv => by
    rw [← cf_snd, eu, cf_mul, hoff g₂ v hv, one_mul]
  have hup : finEmb K (2 + 2) b' ∈ adelicBorel := by
    refine fin_borel b' fun v i j hij => ?_
    by_cases hv : v ∈ im w
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hb' l]
      exact Matrix.one_apply_ne hij.ne'
    · rw [hb1 v hv]
      change (b i j).2 v = 0
      rw [mem_adelicBorel.1 hb hij]
      rfl
  have hs := proj_borel b' hup
  obtain ⟨X, m₁, m₂, t, hX⟩ := par_of_low (fin1 b') (low_of_borel hs) (low_of_borel (inv_mem hs))
  refine ⟨X, m₁, m₂, t, g₁ * g₂, u, fun U v => ?_, ?_⟩
  · by_cases hv : v ∈ im w
    · obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hv
      beta_reduce
      rw [if_pos hv]
      change GM.cf (w l) u ∈ U (w l)
      rw [hu l]
      exact one_mem _
    · beta_reduce
      rw [if_neg hv]
      change GM.cf v u ∈ _
      rw [hu1 v hv]
      exact hc.2 v
  · have c1 : Commute (arc1 k) (fin1 b') := (levLaws (K := K) (2 + 2) (im w)).2.2.1 k b'
    have c2 : fin1 (ι (g₁ * g₂)) * fin1 b' = fin1 b' * fin1 (ι (g₁ * g₂)) := by
      rw [← map_mul, ← map_mul, (hcomm (g₁ * g₂) b' hb').eq]
    have e3 : fin1 (ι (g₁ * g₂) * b' * u) = fin1 (ι (g₁ * g₂)) * fin1 b' * fin1 u :=
      (map_mul _ _ _).trans (congrArg (· * fin1 u) (map_mul _ _ _))
    rw [← hX, hh2, e3, c2, ← c1.eq]
    simp only [mul_assoc]
end

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem ray_lv {K : Type} [Field K] [NumberField K] {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)}
    {f : G1 K (2 + 2) → ℂ} (hf : IsSec τ₁ τ₂ f) (t : ℝ) (g : G1 K (2 + 2)) : f (lv 1 1 t * g) = f g := by
  refine hf.ray ⟨Real.exp t, Real.exp_pos t⟩ ?_ g ?_
  have h : (⟨Real.exp (-t), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) = (⟨Real.exp t, Real.exp_pos t⟩ : {r : ℝ // 0 < r})⁻¹ :=
    Subtype.ext (Real.exp_neg t)
  rw [Subgroup.coe_mul, blkLaws.1, Subgroup.coe_one, one_mul, one_mul, zt, zt, h]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.evInj :
    ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 μ₂)) (κ : Measure (archCompact K (2 + 2))) (e : archCompact K (2 + 2) → ℂ) κ₂ p₁ p₂ k₀, ArchLine τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ →
      ∀ {r : ℕ} (w : Fin r → Pl K) (ι₄ : GS (2 + 2) w →* FA K (2 + 2)), Function.Injective w → IsEmb w ι₄ →
      ∀ φ ∈ Zs τ₁ τ₂ κ e (im w), ev ι₄ k₀ φ = 0 → φ = 0 := by
  intro K _ _ _ μ₂ _ τ₁ τ₂ κ e κ₂ p₁ p₂ k₀ hA r w ι₄ hw hι φ hφ h0
  obtain ⟨f, hf, hfa, ⟨U, -, hU⟩, rfl⟩ := ((zMem μ₂ τ₁ τ₂ κ e hA.idem).1 _ φ).1 hφ
  have h1 : ∀ g m₁ m₂, f (lv m₁ m₂ 0 * arc1 k₀ * fin1 (ι₄ g)) = 0 := fun g m₁ m₂ =>
    (mul_eq_zero.1 (congrFun (congrFun h0 g) (m₁, m₂))).resolve_left (Complex.exp_ne_zero _)
  obtain ⟨ι₂, hι₂⟩ := (embEx (K := K) 2 w hw).1
  have hz : f = 0 := by
    refine hA.inj f hf hfa fun h m₁ m₂ => ?_
    obtain ⟨X, a₁, a₂, t, g, u, hu, hd⟩ := finIwa w ι₄ hw hι h k₀
    obtain ⟨X', hX⟩ := (parLaw w ι₂ ι₄ hw hι₂ hι).1 m₁ m₂ 0 X
    have hl : lv m₁ m₂ 0 * lv a₁ a₂ t = lv 1 1 t * lv (m₁ * a₁) (m₂ * a₂) 0 := by
      rw [blkLaws.2.1, blkLaws.2.1, one_mul, one_mul, zero_add, add_zero]
    have he : lv m₁ m₂ 0 * arc1 k₀ * fin1 h =
        nn X' * (lv 1 1 t * (lv (m₁ * a₁) (m₂ * a₂) 0 * arc1 k₀ * fin1 (ι₄ g))) * fin1 u := by
      rw [mul_assoc, hd]
      simp only [← mul_assoc]
      rw [hX, mul_assoc (nn X'), hl, ← mul_assoc (nn X')]
    rw [he, hU u (hu U), hf.unip, ray_lv hf, h1]
  funext x
  rw [hz]
  exact mul_zero _
end
