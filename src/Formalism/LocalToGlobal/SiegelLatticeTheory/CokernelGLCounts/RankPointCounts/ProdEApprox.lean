module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxMain

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FinIdxAt
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxFin
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GoodPlaces
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemRNone
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxGood
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Good

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem ring_inverse_eq {K : Type*} [CommRing K] {x y : K} (h : x * y = 1) : Ring.inverse x = y := by
  have hx : IsUnit x := ⟨⟨x, y, h, by rw [mul_comm]; exact h⟩, rfl⟩
  calc Ring.inverse x = Ring.inverse x * (x * y) := by rw [h, mul_one]
    _ = y := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hx, one_mul]

theorem cj_mem_O {p : PlF D} {x : (D.s.atP p).Ep} (hx : x ∈ (D.s.atP p).O) : (D.s.atP p).cj x ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def] at hx ⊢
  exact hx.map (((D.s.atP p).cj.toAlgHom).restrictScalars 𝒪[(D.s.atP p).Fp])

theorem lOf_ρOf_int {p : PlF D} (hA : Agree δ M p) (hs : (M p).split = none)
    (hδ : δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (huP : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O)
    (a b : Formalism.L2.SG.PairVal.MatR D) (ha : ∀ i j, (D.s.atP p).ιE (a i j) ∈ (D.s.atP p).O)
    (hb : ∀ i j, (D.s.atP p).ιE (b i j) ∈ (D.s.atP p).O) :
    (∀ i j, lOf δ M p a b i j ∈ (D.s.atP p).O) ∧ ∀ i j, ρOf δ M p a b i j ∈ (D.s.atP p).O := by
  obtain ⟨-, hδ0, hcj, -, -, -⟩ := hA
  set Op := (D.s.atP p).O
  set c : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)
  set ci : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹)
  have hcO : c ∈ Op := Op.mul_mem (alg_mem_O hδ.1) huP.1
  have hciO : ci ∈ Op := Op.mul_mem (alg_mem_O hδ.2) huP.2
  have hcc : c * ci = 1 := by
    have h1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    have h2 : (D.s.atP p).ιE (uP p : D.host.E) * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (unitAt_ne p), map_one]
    calc c * ci = (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹) *
          ((D.s.atP p).ιE (uP p : D.host.E) * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹)) := by ring
      _ = 1 := by rw [h1, h2, mul_one]
  have hfr : ∀ i, frFac δ p i = ci ^ (D.R.rS - i.val) := fun i => by
    unfold frFac
    exact ring_inverse_eq (by rw [← mul_pow, hcc, one_pow])
  have hfri : ∀ i, Ring.inverse (frFac δ p i) = c ^ (D.R.rS - i.val) := fun i => by
    rw [hfr]; exact ring_inverse_eq (by rw [← mul_pow, mul_comm, hcc, one_pow])
  have hcjfr : ∀ i, ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p i) =
      (D.s.atP p).cj ci ^ (D.R.rS - i.val) := fun i => by
    rw [hfr, hcj]; simp
  have hcjfri : ∀ i, Ring.inverse (((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p i)) =
      (D.s.atP p).cj c ^ (D.R.rS - i.val) := fun i => by
    rw [hcjfr]
    refine ring_inverse_eq ?_
    rw [← mul_pow, ← map_mul, mul_comm, hcc, map_one, one_pow]
  have hs1 : ∀ x : D.host.E, (D.s.atP p).ιE x ∈ Op → (D.s.atP p).ιE ((-1) ^ (D.R.rS - 0) * x) ∈ Op := fun x hx => by
    rw [map_mul]; exact Op.mul_mem (by rw [map_pow, map_neg, map_one]; exact Op.pow_mem (Op.neg_mem Op.one_mem) _) hx
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [lOf, hs, lL, Matrix.of_apply]
    rw [hcjfr, hcjfri]
    exact Op.mul_mem (Op.mul_mem (Op.pow_mem (cj_mem_O hciO) _) (ha i j)) (Op.pow_mem (cj_mem_O hcO) _)
  · simp only [ρOf, hs, ρL, Matrix.of_apply]
    rw [hfri, hfr]
    refine Op.mul_mem (Op.mul_mem (Op.pow_mem hcO _) ?_) (Op.pow_mem hciO _)
    rw [map_mul, map_mul]
    have hpm : ∀ k : ℕ, (D.s.atP p).ιE ((-1 : D.host.E) ^ k) ∈ Op := fun k => by
      rw [map_pow, map_neg, map_one]; exact Op.pow_mem (Op.neg_mem Op.one_mem) _
    exact Op.mul_mem (Op.mul_mem (hpm _) (hb i j)) (hpm _)

end Good

end Formalism.L2.SG.Pf.ProdEApprox
end
end

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Good2

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem mem_R_none {p : PlF D} (hA : Agree δ M p) (hs : (M p).split = none) (x : (D.s.atP p).Ep) :
    x ∈ (M p).R ↔ x ∈ (D.s.atP p).O := by
  obtain ⟨-, -, -, hO, -, -⟩ := hA
  show x ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R ↔ _
  rw [hs]
  show x ∈ (M p).L.O ↔ _
  rw [hO]

theorem bOf_int {p : PlF D} (g : Formalism.L2.SG.Pf.VolPinAsm.StG w)
    (hg : ∀ i j, (D.s.atP p).ιE (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) i j) ∈ (D.s.atP p).O)
    (hpv : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (Formalism.L2.SG.Pf.pv w.1 a) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE ((Formalism.L2.SG.Pf.pv w.1 a)⁻¹) ∈ (D.s.atP p).O) :
    ∀ i j, (D.s.atP p).ιE (Formalism.L2.SG.Pf.VolPinAsm.bOf w g i j) ∈ (D.s.atP p).O := by
  set σ := Formalism.L2.SG.Pf.fσ w
  have hσ : ∀ x, σ (σ x) = x := Formalism.L2.SG.Pf.fσ_fσ w
  set ν : Fin (D.R.rS + 1) → D.host.E := fun x => Formalism.L2.SG.Pf.pv w.1 x
  have hν : ∀ x, IsUnit (ν x) := fun x => isUnit_iff_ne_zero.2 (Formalism.L2.SG.Pf.pv_ne' w x)
  set a := ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D)
  set b := Formalism.L2.SG.Pf.VolPinAsm.bOf w g
  obtain ⟨-, hb, hW⟩ := ProdE.bOf_spec w g
  have hfix := fix_cOf hσ ν hν a
  have hWu : IsUnit (ptMat w).det := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit w
  have hcb : cOf σ ν a * b = 1 := by
    have h1 : ptMat w * (cOf σ ν a * b) = ptMat w * 1 := by
      rw [Matrix.mul_one, ← Matrix.mul_assoc]
      conv_lhs => rw [ptMat_mono]
      rw [← hfix, ← ptMat_mono]
      exact hW
    have := congrArg (fun X => (ptMat w)⁻¹ * X) h1
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hWu, Matrix.one_mul] using this
  have hbinv : b = (cOf σ ν a)⁻¹ := (Matrix.inv_eq_right_inv hcb).symm
  have hcU : IsUpUni (cOf σ ν a) := by
    have := (ZsVolGrp.isUpUni_inv hb).1
    rwa [show b⁻¹ = cOf σ ν a from Matrix.inv_eq_left_inv hcb] at this
  have hdet : (cOf σ ν a).det = 1 :=
    ZsVolGrp.det_up (fun x => (hcU x x).2 rfl) (fun x y hxy => (hcU x y).1 hxy)
  have hcO : ∀ x y, (D.s.atP p).ιE (cOf σ ν a x y) ∈ (D.s.atP p).O := by
    intro x y
    simp only [cOf, Matrix.of_apply, Ring.inverse_eq_inv', map_mul]
    exact (D.s.atP p).O.mul_mem ((D.s.atP p).O.mul_mem (hpv (σ x)).2 (hg _ _)) (hpv (σ y)).1
  intro i j
  rw [hbinv, ZsVolGrp.inv_eq_adj hdet]
  have e := congrFun (congrFun (RingHom.map_adjugate (D.s.atP p).ιE (cOf σ ν a)) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e
  rw [e]
  exact ZsVolGrp.adj_mem (D.s.atP p).O (fun x y => by simpa using hcO x y) i j

end Good2

end Formalism.L2.SG.Pf.ProdEApprox
end
end

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Good3

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

set_option maxHeartbeats 1000000 in
theorem good_places (hA : ∀ p, Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    ∃ S : Finset (PlF D), (∀ p, p ∉ S → ProdE.AP M δ u u' w p = ProdE.CPL M δ u u' w (hA p) L U hL hU) ∧
      ∀ p, p ∉ S → ∀ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
        (∀ i j, (D.s.atP p).ιE (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) i j) ∈ (D.s.atP p).O) →
          ProdE.πP M δ u u' w (hA p) g ∈ ProdE.AP M δ u u' w p := by
  classical
  set X : Finset D.host.E := Finset.univ.image (fun a : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.pv w.1 a) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L⁻¹ ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U⁻¹ ij.1 ij.2) with hX
  have hev := Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA X
  have hfin := Filter.eventually_cofinite.1 hev
  refine ⟨hfin.toFinset, ?_⟩
  have key : ∀ p, p ∉ hfin.toFinset → (M p).split = none ∧
      (δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) ∧
      ((D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) ∧
      (∀ t ∈ X, (D.s.atP p).ιE t ∈ (D.s.atP p).O) ∧ (∀ t ∈ X, t ≠ 0 → (D.s.atP p).ιE t⁻¹ ∈ (D.s.atP p).O) := by
    intro p hp
    have hp' : ¬ ¬ _ := fun h => hp (hfin.mem_toFinset.2 h)
    obtain ⟨h1, h2, h3, h4⟩ := not_not.1 hp'
    refine ⟨h1, h2, h3, fun t ht => ?_, fun t ht ht0 => ?_⟩
    · by_cases ht0 : t = 0
      · rw [ht0, map_zero]; exact (D.s.atP p).O.zero_mem
      · have := (h4 t ht 0 (by simpa using ht0)).1
        simpa using this
    · have := (h4 t ht 0 (by simpa using ht0)).2
      simpa using this
  have hpvX : ∀ a : Fin (D.R.rS + 1), Formalism.L2.SG.Pf.pv w.1 a ∈ X := fun a =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem (fun a : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.pv w.1 a) (Finset.mem_univ a)))))
  have hLX : ∀ i j, L i j ∈ X := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L ij.1 ij.2) (Finset.mem_univ (i, j))))))
  have hUX : ∀ i j, U i j ∈ X := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U ij.1 ij.2) (Finset.mem_univ (i, j)))))
  have hLiX : ∀ i j, L⁻¹ i j ∈ X := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L⁻¹ ij.1 ij.2) (Finset.mem_univ (i, j))))
  have hUiX : ∀ i j, U⁻¹ i j ∈ X := fun i j =>
    Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U⁻¹ ij.1 ij.2) (Finset.mem_univ (i, j)))
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  refine ⟨fun p hp => ?_, fun p hp g hg => ?_⟩
  · obtain ⟨hs, hδ, huP, hXi, -⟩ := key p hp
    have hR := mem_R_none M δ (hA p) hs
    have i1 := lOf_ρOf_int M δ (hA p) hs hδ huP L U (fun i j => hXi _ (hLX i j)) (fun i j => hXi _ (hUX i j))
    have i2 := lOf_ρOf_int M δ (hA p) hs hδ huP L⁻¹ U⁻¹ (fun i j => hXi _ (hLiX i j)) (fun i j => hXi _ (hUiX i j))
    have hLp := ProdE.lOf_loUni M δ (hA p) L U hL hU
    have hLpi := ProdE.lOf_loUni M δ (hA p) L⁻¹ U⁻¹ hLi.1 hUi.1
    have hUp := ProdE.ρOf_upUni M δ (hA p) L U hL hU
    have hUpi := ProdE.ρOf_upUni M δ (hA p) L⁻¹ U⁻¹ hLi.1 hUi.1
    have iLp : Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p L U) :=
      ⟨fun a => (hLp a a).2 rfl, fun a b h => (hLp a b).1 h, fun a b => (hR _).2 (i1.1 a b)⟩
    have iLpi : Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p L⁻¹ U⁻¹) :=
      ⟨fun a => (hLpi a a).2 rfl, fun a b h => (hLpi a b).1 h, fun a b => (hR _).2 (i2.1 a b)⟩
    have iUp : Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p L U) :=
      ⟨fun a => (hUp a a).2 rfl, fun a b h => (hUp a b).1 h, fun a b => (hR _).2 (i1.2 a b)⟩
    have iUpi : Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p L⁻¹ U⁻¹) :=
      ⟨fun a => (hUpi a a).2 rfl, fun a b h => (hUpi a b).1 h, fun a b => (hR _).2 (i2.2 a b)⟩
    have hLL := ProdE.lp_inv M δ (hA p) L U hL hU
    have hUU := ProdE.up_inv M δ (hA p) L U hL hU
    ext k
    constructor
    · rintro ⟨hk1, hk2⟩
      exact ⟨ZsVolGrp.intLow_mul _ (ZsVolGrp.intLow_mul _ iLp hk1) iLpi,
        ZsVolGrp.intUp_mul _ (ZsVolGrp.intUp_mul _ iUpi hk2) iUp⟩
    · rintro ⟨hk1, hk2⟩
      refine ⟨?_, ?_⟩
      · have e : ((k.1.1 : ProdE.GLp p) : ProdE.MP p) = lOf δ M p L⁻¹ U⁻¹ *
            (lOf δ M p L U * ((k.1.1 : ProdE.GLp p) : ProdE.MP p) * lOf δ M p L⁻¹ U⁻¹) * lOf δ M p L U := by
          rw [show lOf δ M p L⁻¹ U⁻¹ * (lOf δ M p L U * ((k.1.1 : ProdE.GLp p) : ProdE.MP p) * lOf δ M p L⁻¹ U⁻¹) *
              lOf δ M p L U = (lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U) * ((k.1.1 : ProdE.GLp p) : ProdE.MP p) *
                (lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U) by simp only [Matrix.mul_assoc], hLL, Matrix.one_mul, Matrix.mul_one]
        rw [e]
        exact ZsVolGrp.intLow_mul _ (ZsVolGrp.intLow_mul _ iLpi hk1) iLp
      · have e : ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) = ρOf δ M p L U *
            (ρOf δ M p L⁻¹ U⁻¹ * ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) * ρOf δ M p L U) * ρOf δ M p L⁻¹ U⁻¹ := by
          rw [show ρOf δ M p L U * (ρOf δ M p L⁻¹ U⁻¹ * ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) * ρOf δ M p L U) *
              ρOf δ M p L⁻¹ U⁻¹ = (ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹) * ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) *
                (ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹) by simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one]
        rw [e]
        exact ZsVolGrp.intUp_mul _ (ZsVolGrp.intUp_mul _ iUp hk2) iUpi
  · obtain ⟨hs, hδ, huP, hXi, hXinv⟩ := key p hp
    have hR := mem_R_none M δ (hA p) hs
    have hb := bOf_int w g hg (fun a => ⟨hXi _ (hpvX a), hXinv _ (hpvX a) (Formalism.L2.SG.Pf.pv_ne' w a)⟩)
    have i0 := lOf_ρOf_int M δ (hA p) hs hδ huP _ _ hg hb
    obtain ⟨hπl, hπρ, -⟩ := (ProdE.πP M δ u u' w (hA p) g).2
    exact ⟨⟨fun a => (hπl a a).2 rfl, fun a b h => (hπl a b).1 h, fun a b => (hR _).2 (i0.1 a b)⟩,
      ⟨fun a => (hπρ a a).2 rfl, fun a b h => (hπρ a b).1 h, fun a b => (hR _).2 (i0.2 a b)⟩⟩

end Good3

end Formalism.L2.SG.Pf.ProdEApprox
end
end

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Code

theorem relIndex_ne_zero_of_code {G : Type*} [Group G] (H A : Subgroup G) {Q : Type*} [Finite Q] (φ : A → Q)
    (hφ : ∀ k k' : A, φ k = φ k' → ((k⁻¹ * k' : A) : G) ∈ H) : H.relIndex A ≠ 0 := by
  classical
  have hfin : Finite (A ⧸ H.subgroupOf A) := by
    choose rep hrep using fun v : Set.range φ => v.2
    refine Finite.of_surjective (fun v : Set.range φ => (QuotientGroup.mk (rep v) : A ⧸ H.subgroupOf A)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      refine ⟨⟨φ k, k, rfl⟩, ?_⟩
      show (QuotientGroup.mk (rep ⟨φ k, k, rfl⟩) : A ⧸ H.subgroupOf A) = QuotientGroup.mk k
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact hφ _ _ (hrep _)
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

end Code

section Fin

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem R_sub_O {p : PlF D} (hA : Agree δ M p) {x : (D.s.atP p).Ep} (hx : x ∈ (M p).R) : x ∈ (D.s.atP p).O := by
  obtain ⟨-, -, -, hO, -, hsp⟩ := hA
  revert hx
  show x ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R → _
  rcases hM : (M p).split with _ | g
  · intro hx
    have : x ∈ (M p).L.O := hx
    rwa [hO] at this
  · rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      intro hx
      rw [Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split] at hx
      rw [Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg, ← hsp'.1]
      exact ⟨hx.1, hx.2.1⟩

def dO {p : PlF D} (c : (D.s.atP p).Fp) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).O :=
  ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c, alg_mem_O hc⟩

theorem finite_quot {p : PlF D} (hA : Agree δ M p) (c : (D.s.atP p).Fp) (hc0 : c ≠ 0) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    Finite ((D.s.atP p).O ⧸ (Ideal.span {dO c hc}).toAddSubgroup) := by
  obtain ⟨hOK, -, -, hO, -, -⟩ := hA
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  obtain ⟨hOo, hOc, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top (M p).L
  rw [hO] at hOo hOc
  have : CompactSpace (D.s.atP p).O := isCompact_iff_compactSpace.1 hOc
  have hc' : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  have hopen : IsOpen (((Ideal.span {dO c hc}).toAddSubgroup : AddSubgroup (D.s.atP p).O) : Set (D.s.atP p).O) := by
    have h1 : (((Ideal.span {dO c hc}).toAddSubgroup : AddSubgroup (D.s.atP p).O) : Set (D.s.atP p).O) =
        (fun y : (D.s.atP p).O => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * (y : (D.s.atP p).Ep)) ⁻¹'
          ((D.s.atP p).O : Set (D.s.atP p).Ep) := by
      ext y
      simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, Set.mem_preimage]
      rw [Ideal.mem_span_singleton']
      constructor
      · rintro ⟨z, rfl⟩
        show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * ((z : (D.s.atP p).Ep) * algebraMap _ _ c) ∈ (D.s.atP p).O
        rw [mul_comm (z : (D.s.atP p).Ep), ← mul_assoc, hc', one_mul]
        exact z.2
      · intro hy
        refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
        show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * (y : (D.s.atP p).Ep) * algebraMap _ _ c = y
        rw [mul_comm, ← mul_assoc, mul_comm (algebraMap _ _ c), hc', one_mul]
    rw [h1]
    exact hOo.preimage (by fun_prop)
  exact AddSubgroup.quotient_finite_of_isOpen _ hopen

theorem quot_eq {p : PlF D} {c : (D.s.atP p).Fp} {hc : c ∈ 𝒪[(D.s.atP p).Fp]} {x y : (D.s.atP p).O}
    (h : (QuotientAddGroup.mk x : (D.s.atP p).O ⧸ (Ideal.span {dO c hc}).toAddSubgroup) = QuotientAddGroup.mk y) :
    (y : (D.s.atP p).Ep) - x ∈ latS (D.s.atP p) c := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  refine mem_latS.2 ⟨z, z.2, ?_⟩
  have := congrArg Subtype.val hz
  simp only [Subring.coe_mul, Subring.coe_add, Subring.coe_neg] at this
  rw [show (y : (D.s.atP p).Ep) - x = -x + y by ring, ← this]
  show (z : (D.s.atP p).Ep) * algebraMap _ _ c = _
  ring

theorem entIn_int_mul {p : PlF D} {c : (D.s.atP p).Fp} {B X : ProdE.MP p} (hB : ∀ i j, B i j ∈ (D.s.atP p).O)
    (hX : EntIn (latS (D.s.atP p) c) X) : EntIn (latS (D.s.atP p) c) (B * X) :=
  entIn_mul (J1 := (D.s.atP p).O.toAddSubgroup) (fun x hx y hy => O_mul_latS hx hy) (fun i j => hB i j) hX

theorem entIn_mul_int {p : PlF D} {c : (D.s.atP p).Fp} {B X : ProdE.MP p} (hB : ∀ i j, B i j ∈ (D.s.atP p).O)
    (hX : EntIn (latS (D.s.atP p) c) X) : EntIn (latS (D.s.atP p) c) (X * B) :=
  entIn_mul (J2 := (D.s.atP p).O.toAddSubgroup) (fun x hx y hy => by rw [mul_comm]; exact O_mul_latS hy hx) hX
    (fun i j => hB i j)

end Fin

end Formalism.L2.SG.Pf.ProdEApprox
end
end

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fin2

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

set_option maxHeartbeats 1000000 in
theorem finIdx_at {p : PlF D} (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    (ProdE.CPL M δ u u' w hA L U hL hU).relIndex (ProdE.AP M δ u u' w p) ≠ 0 ∧
      (ProdE.AP M δ u u' w p).relIndex (ProdE.CPL M δ u u' w hA L U hL hU) ≠ 0 := by
  classical
  obtain ⟨c0, hc00, hc0O, hcong⟩ := cong_at M δ u u' w hA L U hL hU
  set Lp := lOf δ M p L U with hLpd
  set Lpi := lOf δ M p L⁻¹ U⁻¹ with hLpid
  set Up := ρOf δ M p L U with hUpd
  set Upi := ρOf δ M p L⁻¹ U⁻¹ with hUpid
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLL : Lp * Lpi = 1 := by rw [hLpd, hLpid, ← lOf_mul δ M hA, hLi.2.2, hUi.2.1, lOf_one δ M hA]
  have hLL' : Lpi * Lp = 1 := ProdE.lp_inv M δ hA L U hL hU
  have hUU : Up * Upi = 1 := ProdE.up_inv M δ hA L U hL hU
  have hUU' : Upi * Up = 1 := by rw [hUpd, hUpid, ← ρOf_mul δ M hA, hLi.2.2, hUi.2.1, ρOf_one δ M hA]
  obtain ⟨s1, hs10, hs1O, hs1⟩ := bounded_mat (L := D.s.atP p) Lp
  obtain ⟨s2, hs20, hs2O, hs2⟩ := bounded_mat (L := D.s.atP p) Lpi
  obtain ⟨s3, hs30, hs3O, hs3⟩ := bounded_mat (L := D.s.atP p) Up
  obtain ⟨s4, hs40, hs4O, hs4⟩ := bounded_mat (L := D.s.atP p) Upi
  have hRO : ∀ {x : (D.s.atP p).Ep}, x ∈ (M p).R → x ∈ (D.s.atP p).O := fun hx => R_sub_O M δ hA hx
  refine ⟨?_, ?_⟩
  · haveI := finite_quot M δ hA c0 hc00 hc0O
    refine relIndex_ne_zero_of_code _ _
      (fun k : ProdE.AP M δ u u' w p =>
        ((fun i j => (QuotientAddGroup.mk (⟨((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) i j,
            hRO (k.2.1.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c0 hc0O}).toAddSubgroup)),
         (fun i j => (QuotientAddGroup.mk (⟨((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) i j,
            hRO (k.2.2.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c0 hc0O}).toAddSubgroup))))
      (fun k k' heq => ?_)
    have e1 : ∀ i j, (((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) - ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p))
        i j ∈ latS (D.s.atP p) c0 := fun i j => by
      rw [Matrix.sub_apply]; exact quot_eq (congrFun (congrFun (congrArg Prod.fst heq) i) j)
    have e2 : ∀ i j, (((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) -
        ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p)) i j ∈ latS (D.s.atP p) c0 := fun i j => by
      rw [Matrix.sub_apply]; exact quot_eq (congrFun (congrFun (congrArg Prod.snd heq) i) j)
    have hki := (k⁻¹).2
    clear heq
    set a := ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set a' := ((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set b := ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    set b' := ((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    have ha : ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (a : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hb : (b : ProdE.MP p) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have m := hcong ((k⁻¹ * k' : ProdE.AP M δ u u' w p) : ProdE.StP M δ u u' w p) ?_ ?_
    · exact m.2
    · show EntIn _ (((a⁻¹ * a' : ProdE.GLp p) : ProdE.MP p) - 1)
      rw [Units.val_mul, show ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (a' : ProdE.MP p) - 1 =
        ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * ((a' : ProdE.MP p) - (a : ProdE.MP p)) by rw [Matrix.mul_sub, ha]]
      exact entIn_int_mul (fun i j => hRO (hki.1.2.2 i j)) e1
    · show EntIn _ (((b' * b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1)
      rw [Units.val_mul, show (b' : ProdE.MP p) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1 =
        ((b' : ProdE.MP p) - (b : ProdE.MP p)) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) by rw [Matrix.sub_mul, hb]]
      exact entIn_mul_int (fun i j => hRO (hki.2.2.2 i j)) e2
  · set c1 := s2 * (s1 * c0) * (s3 * s4) with hc1d
    have hc1O : c1 ∈ 𝒪[(D.s.atP p).Fp] := Subring.mul_mem _ (Subring.mul_mem _ hs2O (Subring.mul_mem _ hs1O hc0O))
      (Subring.mul_mem _ hs3O hs4O)
    have hc10 : c1 ≠ 0 := mul_ne_zero (mul_ne_zero hs20 (mul_ne_zero hs10 hc00)) (mul_ne_zero hs30 hs40)
    haveI := finite_quot M δ hA c1 hc10 hc1O
    refine relIndex_ne_zero_of_code _ _
      (fun k : ProdE.CPL M δ u u' w hA L U hL hU =>
        ((fun i j => (QuotientAddGroup.mk (⟨(Lp * ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) * Lpi) i j,
            hRO (k.2.1.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c1 hc1O}).toAddSubgroup)),
         (fun i j => (QuotientAddGroup.mk (⟨(Upi * ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) * Up) i j,
            hRO (k.2.2.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c1 hc1O}).toAddSubgroup))))
      (fun k k' heq => ?_)
    have e1 : EntIn (latS (D.s.atP p) c1) (Lp * (((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) -
        ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p)) * Lpi) := fun i j => by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
      exact quot_eq (congrFun (congrFun (congrArg Prod.fst heq) i) j)
    have e2 : EntIn (latS (D.s.atP p) c1) (Upi * (((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) -
        ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p)) * Up) := fun i j => by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
      exact quot_eq (congrFun (congrFun (congrArg Prod.snd heq) i) j)
    clear heq
    set a := ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set a' := ((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set b := ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    set b' := ((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    have hki := (k⁻¹).2
    have ha : ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (a : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hb : (b : ProdE.MP p) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have m := hcong ((k⁻¹ * k' : ProdE.CPL M δ u u' w hA L U hL hU) : ProdE.StP M δ u u' w p) ?_ ?_
    · exact m.1
    · show EntIn _ (((a⁻¹ * a' : ProdE.GLp p) : ProdE.MP p) - 1)
      have eq1 : ((a⁻¹ * a' : ProdE.GLp p) : ProdE.MP p) - 1 =
          Lpi * ((Lp * ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * Lpi) * (Lp * ((a' : ProdE.MP p) - (a : ProdE.MP p)) * Lpi)) *
            Lp := by
        rw [show Lpi * ((Lp * ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * Lpi) *
            (Lp * ((a' : ProdE.MP p) - (a : ProdE.MP p)) * Lpi)) * Lp =
            (Lpi * Lp) * ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (Lpi * Lp) * ((a' : ProdE.MP p) - (a : ProdE.MP p)) *
              (Lpi * Lp) by simp only [Matrix.mul_assoc], hLL', Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
          Units.val_mul, Matrix.mul_sub, ha]
      rw [eq1]
      exact entIn_sandwich hs2 hs1 (entIn_latS_of_eq (t := s3 * s4) rfl (Subring.mul_mem _ hs3O hs4O)
        (entIn_int_mul (fun i j => hRO (hki.1.2.2 i j)) e1))
    · show EntIn _ (((b' * b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1)
      have eq2 : ((b' * b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1 =
          Up * ((Upi * ((b' : ProdE.MP p) - (b : ProdE.MP p)) * Up) * (Upi * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) * Up)) *
            Upi := by
        rw [show Up * ((Upi * ((b' : ProdE.MP p) - (b : ProdE.MP p)) * Up) *
            (Upi * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) * Up)) * Upi =
            (Up * Upi) * ((b' : ProdE.MP p) - (b : ProdE.MP p)) * (Up * Upi) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) *
              (Up * Upi) by simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
          Units.val_mul, Matrix.sub_mul, hb]
      rw [eq2]
      exact entIn_sandwich hs3 hs4 (entIn_latS_of_eq (t := s2 * s1) (by rw [hc1d]; ring)
        (Subring.mul_mem _ hs2O hs1O) (entIn_mul_int (fun i j => hRO (hki.2.2.2 i j)) e2))

end Fin2

end Formalism.L2.SG.Pf.ProdEApprox
end
end

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem approxC : ProdE.ApproxC M δ u u' F0 what₂ := by
  intro γ w F' L U hE
  obtain ⟨S, hSAC, hSint⟩ := good_places M δ u u' w hE.1 L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
  exact ⟨S, hSAC, fun p => finIdx_at M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1,
    fun h => approx_core M δ u u' w hE.1 L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1 S hSint h⟩

end Formalism.L2.SG.Pf.ProdEApprox
