module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisAdaptedLatticeSubspace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamily
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTriple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tate_free_of_card :
    ∀ (p : ℕ) [Fact p.Prime] (M : Type) [CommGroup M] (r : ℕ), (∀ n : ℕ, Nat.card {x : M // x ^ p ^ n = 1} = p ^ (r * n)) → Nonempty (Tate p M ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])) ∧ (∀ (n : ℕ) (x : M), x ^ p ^ n = 1 → ∃ t : Tate p M, t.lev n = x) ∧ ∀ (n : ℕ) (t : Tate p M), t.lev n = 1 ↔ ∃ s : Tate p M, t = (p : ℤ_[p]) ^ n • s := by
  intro p _ M _ r h
  obtain ⟨T, _, _, π, hfree, hfin, hrk, hs, h0, hsm, hon, hker, huniq⟩ :=
    GlobalTheory.exists_tateModule_of_card (Additive M) p r (fun n => by
      rw [← h n]
      exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun x => Iff.rfl))
  have hkill : ∀ n x, p ^ n • π n x = 0 := fun n x => by
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [pow_succ, mul_smul, hs, ih]
  let f : T →ₗ[ℤ_[p]] Tate p M :=
    { toFun := fun x => Tate.mk (fun n => Additive.toMul (π n x)) fun n =>
        ⟨congrArg Additive.toMul (hkill n x), congrArg Additive.toMul (hs n x)⟩
      map_add' := fun x y => Tate.ext fun n => congrArg Additive.toMul (map_add (π n) x y)
      map_smul' := fun a x => Tate.ext fun n => congrArg Additive.toMul (hsm n a x) }
  have hf : ∀ x n, (f x).lev n = Additive.toMul (π n x) := fun _ _ => rfl
  have hu : ∀ t : Tate p M, ∃! x, ∀ n, π n x = Additive.ofMul (t.lev n) := fun t =>
    huniq (fun n => Additive.ofMul (t.lev n))
      (by have := t.lev_pow 0
          rw [pow_zero, pow_one] at this
          rw [this]; rfl)
      (fun n => congrArg Additive.ofMul (t.lev_succ n))
  have hsurj : Function.Surjective f := fun t => by
    obtain ⟨x, hx, -⟩ := hu t
    exact ⟨x, Tate.ext fun n => by rw [hf, hx]; rfl⟩
  have hinj : Function.Injective f := fun x y hxy =>
    (hu (f y)).unique (fun n => by rw [← hxy]; rfl) (fun n => rfl)
  refine ⟨⟨(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.trans
    (LinearEquiv.ofFinrankEq _ _ (by simpa using hrk))⟩, fun n x hx => ?_, fun n t => ?_⟩
  · obtain ⟨y, hy⟩ := hon n (Additive.ofMul x) (congrArg Additive.ofMul hx)
    exact ⟨f y, by rw [hf, hy]; rfl⟩
  · obtain ⟨x, rfl⟩ := hsurj t
    have key : ∀ y : T, f (p ^ n • y) = (p : ℤ_[p]) ^ n • f y := fun y => by
      rw [map_nsmul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    refine Iff.trans (hker n x) ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      exact ⟨f y, key y⟩
    · rintro ⟨s, hs'⟩
      obtain ⟨y, rfl⟩ := hsurj s
      exact ⟨y, hinj (hs'.trans (key y).symm)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAmpleGloballyGenerated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVeryAmpleByO1
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjVar

theorem exists_veryAmpleBy_O1 : ∀ Y : Var ℂ, ∃ s : Fin (Y.N + 1) → ((ProjSpace.O1 ℂ Y.N).pull Y.ι).Sec, GlobalTheory.AbLaw.VeryAmpleBy Y.str ((ProjSpace.O1 ℂ Y.N).pull Y.ι) s :=
  fun Y => ⟨_, ProjSpace.veryAmpleBy_secPull_coord Y.ι⟩

end GlobalTheory.ProjVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAmpleGloballyGenerated
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ProjVar

theorem exists_generating_secs_tens_lbPow_O1 : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ (n : ℕ) (u : Fin n → (CechPic.tens L (lbPow ((ProjSpace.O1 ℂ Y.N).pull Y.ι) m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  intro Y L hL
  obtain ⟨s, hs⟩ := exists_veryAmpleBy_O1 Y
  have hH : ((ProjSpace.O1 ℂ Y.N).pull Y.ι).IsLB := pull_isLB (ProjSpace.O1_isLB ℂ Y.N) _
  generalize (ProjSpace.O1 ℂ Y.N).pull Y.ι = H at s hs hH
  obtain ⟨t₀, ht⟩ := GlobalTheory.TwistGen.twist_generated ℂ Y.X Y.str H _ s hH hs L hL
  refine ⟨t₀.toNat, fun m hm => ?_⟩
  obtain ⟨n, u, hu⟩ := ht m (by omega)
  have hP : (lbPow H m).IsLB := DVR.linComb_isLB H hH _ _
  have hT : (CechPic.tens L (lbPow H m)).IsLB := isLB_tens hL hP
  have e : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) =
      cls L hL - cls (AbLaw.pw H (-(m : ℤ))) (AbLaw.isLB_pw hH _) :=
    cls_div hL (AbLaw.isLB_pw hH _) (AbLaw.isLB_tw hL hH _)
  have e' : cls (AbLaw.tw L H m) (AbLaw.isLB_tw hL hH _) = cls _ hT := by
    rw [e, GlobalTheory.AmpleStabFinite.cls_pw hH, cls_tens hL hP, cls_lbPow hH, neg_zsmul, natCast_zsmul, sub_neg_eq_add]
  obtain ⟨v, hv⟩ := exists_generating_secs_of_cls_eq _ _ _ _ hT e' _ u hu
  exact ⟨_, v, hv⟩

end GlobalTheory.ProjVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAmpleGloballyGeneratedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_ample_globally_generated : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ (n : ℕ) (u : Fin n → (CechPic.tens L (lbPow ((ProjSpace.O1 ℂ Y.N).pull Y.ι) m)).Sec), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  first | exact @GlobalTheory.ProjVar.exists_generating_secs_tens_lbPow_O1 | exact GlobalTheory.ProjVar.exists_generating_secs_tens_lbPow_O1 | (intros; apply GlobalTheory.ProjVar.exists_generating_secs_tens_lbPow_O1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSubquotientPrincipalSeries
open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspDetBlocks

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.Whittaker


open GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic in
theorem exists_isGeneric_subrep {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (P : CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (S : Subrepresentation (P.locRep w)) (hS : S.toSubmodule ≠ ⊥) :
    ∃ ψ : AddChar (w.adicCompletion E) Circle, Continuous ψ ∧ ψ ≠ 1 ∧ IsGeneric ψ S.toRepresentation := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_standardAdelicAddChar E
  have hg : ∀ v : P.V, Good ψ (a - 1) v.1.1 := fun v => GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm E a ψ v.1 (P.cusp _ v.2)
  have h0 : a - 1 < a ∨ a - 1 = 0 := by omega
  obtain ⟨v₀, hv₀S, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hv1 : v₀.1.1 ≠ 0 := fun h => hv₀ (Subtype.ext (Subtype.ext h))
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 ((whit_good hψ (a - 1) h0 (hg v₀)).2 hv1)
  obtain ⟨h, gw, e, hc⟩ := GlobalTheory.T.exists_split_adelicMatrix_localComponent E a w g₀
  have hrt : ∀ u (v : P.V) x, whit ψ (a - 1) (P.locRep w u v).1.1 x =
      whit ψ (a - 1) v.1.1 (x * finGL E a (locGL E a w u)) := fun u v x => whit_rt _ _ _ _
  let l : P.V →ₗ[ℂ] ℂ :=
    { toFun := fun v => whit ψ (a - 1) v.1.1 h
      map_add' := fun v v' => congrFun (whit_add hψ (a - 1) h0 (hg v) (hg v')) h
      map_smul' := fun c v => congrFun (whit_smul (a - 1) c v.1.1) h }
  have hl : ∀ v, l v = whit ψ (a - 1) v.1.1 h := fun _ => rfl
  have hne : l (P.locRep w gw v₀) ≠ 0 := by
    rw [hl, hrt, ← e]
    exact hg₀
  have hlaw : ∀ u ∈ unipB (w.adicCompletion E) (Fin a), ∀ v : P.V,
      l (P.locRep w u v) = (locPsi hψ w (superDiag u) : ℂ) * l v := fun u hu v => by
    obtain ⟨u1, u2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
    obtain ⟨t1, t2, t3⟩ := GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent E a w u u1 u2
    have hlw := (whit_good hψ (a - 1) h0 (hg v)).1.law
    have := GlobalTheory.T.whittakerLaw_upperTriangularUnipotent_adelic E a ψ _ (fun k hk => hlw k hk) _ t1 t2 h
    rw [hl, hrt, hc, this, t3, superDiag_eq_sum_pairs]
    rfl
  have hcont : Continuous (locPsi hψ w) := by
    refine Continuous.subtype_mk (hψ.cont.comp ?_) _
    exact (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)).comp
      (CuspSub.continuous_sLoc w)
  have hne1 : locPsi hψ w ≠ 1 := fun h1 => by
    obtain ⟨y, hy⟩ := hψ.loc w
    apply hy
    have := congrArg (fun c : Circle => (c : ℂ)) (DFunLike.congr_fun h1 y)
    simpa [coe_locPsi] using this
  refine ⟨locPsi hψ w, hcont, hne1, l ∘ₗ S.toSubmodule.subtype, fun e' => hne ?_, fun u hu v => ?_⟩
  · exact LinearMap.congr_fun e' ⟨_, S.apply_mem_toSubmodule gw hv₀S⟩
  · exact hlaw u hu v.1

end GlobalTheory.CuspDetBlocks

namespace GlobalTheory.CuspDetBlocks

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.Whittaker

end GlobalTheory.CuspDetBlocks
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKGLIffVal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTwKU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_KGL_iff_val {u : Pl E} (x : GLw n u) :
    x ∈ GlobalTheory.LFun.KGL u (n := n) ↔ (∀ i j, Valued.v (x.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((x⁻¹).val i j) ≤ 1 := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective (Ov E u).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective (Ov E u).subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem mem_Kglob_iff (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    g ∈ GlobalTheory.EulerTw.Kglob E n ↔ ∀ u : Pl E, GeneralLinearGroup.map (pLoc E u) g ∈ GlobalTheory.LFun.KGL u (n := n) := by
  unfold GlobalTheory.EulerTw.Kglob
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap]

theorem pLoc_prjG (T : Finset (Pl E)) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (u : Pl E) :
    GeneralLinearGroup.map (pLoc E u) (GlobalTheory.EulerTw.prjG E n T g) =
      if u ∈ T then GeneralLinearGroup.map (pLoc E u) g else 1 := by
  have hid : pLoc E u (GlobalTheory.EulerTw.idem E T) = if u ∈ T then 1 else 0 := rfl
  split_ifs with hu
  · refine Units.ext (Matrix.ext fun i j => ?_)
    show pLoc E u ((GlobalTheory.EulerTw.idem E T • g.val + (1 - GlobalTheory.EulerTw.idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = pLoc E u (g.val i j)
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, hid, if_pos hu]
    simp
  · refine Units.ext (Matrix.ext fun i j => ?_)
    show pLoc E u ((GlobalTheory.EulerTw.idem E T • g.val + (1 - GlobalTheory.EulerTw.idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, hid, if_neg hu]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]

theorem val_pLoc_thF (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (u : Pl E) (i j : Fin n) :
    Valued.v ((GeneralLinearGroup.map (pLoc E u) (thF E n g)).val i j) =
      Valued.v ((GeneralLinearGroup.map (pLoc E (conjSrc (IsCMField.complexConj E).toRingEquiv u)) g⁻¹).val j.rev i.rev) := by
  show Valued.v (pLoc E u ((thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j)) = _
  rw [GlobalTheory.ThetaPull.thetaGL_apply, map_mul, Valuation.map_mul, pLoc_conjFin, (conjLoc_spec _ u).2.2]
  have : Valued.v (pLoc E u ((-1) ^ ((i : ℕ) + j))) = 1 := by
    rw [map_pow, map_neg, map_one, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow]
  rw [this, one_mul]
  rfl

theorem thF_mem_Kglob (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (hg : g ∈ GlobalTheory.EulerTw.Kglob E n) :
    thF E n g ∈ GlobalTheory.EulerTw.Kglob E n := by
  rw [mem_Kglob_iff] at hg ⊢
  intro u
  have hs := (mem_KGL_iff_val _).1 (hg (conjSrc (IsCMField.complexConj E).toRingEquiv u))
  rw [mem_KGL_iff_val]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [val_pLoc_thF, map_inv]
    exact hs.2 _ _
  · rw [← map_inv, ← map_inv, val_pLoc_thF, inv_inv]
    exact hs.1 _ _

end GlobalTheory.EulerTwKU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefInjective
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftScalarCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Places

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem primeToHost (h : R.toLevCh.Is A.μ0) : AdelicScalarSectionLift.PrimeToHost R := by
  intro PP hP
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  refine GlobalTheory.CoverHalf.not_mem_of_coprime PP.isPrime.ne_top (a := D.host.g k) ?_ (R.C.P.overP hk)
  have hc := D.ntypes.g_cond k
  have h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc, Nat.gcd_one_left]
  refine Nat.Coprime.mul_right h1 ?_
  refine (D.host.ccK_coprime _ ?_).symm
  simp [D.host.g_level k]

end Places

section Coord

variable {V : HSp D} (c : CoefA V) {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

variable {c}

end Coord

theorem adjoint_idem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Representation ℂ G H) (hu : ∀ g x, ‖ρ g x‖ = ‖x‖) {a : G → ℂ} (ha : GoodBasisCentralIdempotents.IsCentralIdem a) {x : H}
    (hx : (∑ g, a g • ρ g) x = x) (y : H) : ⟪x, (∑ g, a g • ρ g) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  set E : H →ₗ[ℂ] H := ∑ g, a g • ρ g with hE
  have hin : ∀ g u w, ⟪ρ g u, ρ g w⟫_ℂ = ⟪u, w⟫_ℂ := fun g => LinearIsometry.inner_map_map ⟨ρ g, hu g⟩
  have hcomm : ∀ g u, E (ρ g u) = ρ g (E u) := fun g u => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hE, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, ← Module.End.mul_apply, ← map_mul]
    refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun h => ?_).symm
    show _ = a (g * h * g⁻¹) • ρ (g * h * g⁻¹ * g) u
    rw [ha.1, inv_mul_cancel_right]
  have hidem : ∀ u, E (E u) = E u := fun u => by
    have h1 : E u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
      simp only [← Finset.sum_smul, ha.2, hE, LinearMap.sum_apply, LinearMap.smul_apply]
    have h2 : E (E u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hE, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
    refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

  have hadj : ∀ u, LinearMap.adjoint E u = ∑ g, star (a g) • ρ g⁻¹ u := fun u => by
    refine ext_inner_right ℂ fun w => ?_
    rw [LinearMap.adjoint_inner_left, sum_inner, hE, LinearMap.sum_apply, inner_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, inner_smul_right, inner_smul_left, ← hin g (ρ g⁻¹ u), ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
    simp
  have hfix : E (LinearMap.adjoint E x) = LinearMap.adjoint E x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hadj, map_sum]
    simp only [map_smul, hcomm, hx]

  have hz : LinearMap.adjoint E x - x = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    have h1 : E (LinearMap.adjoint E x - x) = LinearMap.adjoint E x - x := by rw [map_sub, hfix, hx]
    rw [inner_sub_left, LinearMap.adjoint_inner_left, h1, sub_self]
  rw [← LinearMap.adjoint_inner_left, sub_eq_zero.1 hz]

end GlobalTheory.LiftScalarCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelBlockLevelsSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelBlockLevelsSplitPlace
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_dgM_inl {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous ((dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GLw a w => dgMat h x.val (1 : GLw b w).val
    exact (Continuous.matrix_fromBlocks Units.continuous_val continuous_const continuous_const
      continuous_const).matrix_reindex _ _
  · have : (fun x : GLw a w => (((dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) x)⁻¹.val) =
        fun x => dgMat h (x⁻¹).val ((1 : GLw b w)⁻¹).val := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact (Continuous.matrix_fromBlocks Units.continuous_coe_inv continuous_const continuous_const
      continuous_const).matrix_reindex _ _

theorem continuous_dgM_inr {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous ((dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GLw b w => dgMat h (1 : GLw a w).val x.val
    exact (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const
      Units.continuous_val).matrix_reindex _ _
  · have : (fun x : GLw b w => (((dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) x)⁻¹.val) =
        fun x => dgMat h ((1 : GLw a w)⁻¹).val (x⁻¹).val := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_const
      Units.continuous_coe_inv).matrix_reindex _ _

theorem continuous_det_GLw (m : ℕ) (w : Pl E) :
    Continuous (GeneralLinearGroup.det : GLw m w → (w.adicCompletion E)ˣ) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GLw m w => (x.val).det
    exact Units.continuous_val.matrix_det
  · have : (fun x : GLw m w => ((GeneralLinearGroup.det x)⁻¹ : (w.adicCompletion E)ˣ).val) =
        fun x => ((x⁻¹).val).det := by
      funext x
      rw [← map_inv]
      rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_det

theorem isOpen_detKer (m : ℕ) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (hμ : IsOpen {x | μ x = 1}) :
    IsOpen ((μ.ker.comap GeneralLinearGroup.det : Subgroup (GLw m w)) : Set (GLw m w)) :=
  hμ.preimage (continuous_det_GLw m w)

theorem thL_split (m : ℕ) (w : Pl E) (hw : IsSplitAt w) : thL m w = MonoidHom.id _ := by
  rw [thL, if_pos hw]

end GlobalTheory.BCT.CtLevel

theorem GlobalTheory.BCT.CtLevel.isLevel_lev_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsSplitAt w → IsOpen (N : Set (GLw n w)) →
    IsOpen {x | μ x = 1} →
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) (lev₁ h w N μ) ∧ IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) (lev₂ h w N μ) := by
  intro E _ _ _ a b n h w N μ hw hN hμ
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1.inter
      (hN.preimage (continuous_dgM_inl h w))).inter (isOpen_detKer a w μ hμ))
  · exact inf_le_left.trans inf_le_left
  · intro k hk
    rw [thL_split a w hw]
    exact hk
  · exact (((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1.inter
      (hN.preimage (continuous_dgM_inr h w))).inter (isOpen_detKer b w μ hμ))
  · exact inf_le_left.trans inf_le_left
  · intro k hk
    rw [thL_split b w hw]
    exact hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelBlockLevelsSplitPlaceStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLevel_blockLevels_splitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsSplitAt w → IsOpen (N : Set (GLw n w)) →
    IsOpen {x | μ x = 1} →
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) (lev₁ h w N μ) ∧ IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) (lev₂ h w N μ) := by
  first | exact @GlobalTheory.BCT.CtLevel.isLevel_lev_split | exact GlobalTheory.BCT.CtLevel.isLevel_lev_split | (intros; apply GlobalTheory.BCT.CtLevel.isLevel_lev_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableCharpolyOfTestFunctionNeZeroRegularPlac
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableCharpolyOfTestFunctionNeZeroRegularPlac
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.RegVan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_GLint_of_entries {L : Type} [Field L] {k : ℕ} (O : Subring L) (g : GL (Fin k) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin k) O := by
  have hi : Function.Injective fun A : Matrix (Fin k) (Fin k) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem eventually_toSub_mem (x : finU (E := E) (n := n)) :
    ∀ᶠ w in cofinite, toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w := by
  have h : ∀ y : FiniteAdeleRing (𝓞 E) E, ∀ᶠ w in cofinite, pLoc E w y ∈ Formalism.UG.Ov E w := fun y => y.2
  have h1 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E (((x : UA E n) : GA E n).val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  have h2 : ∀ᶠ w in cofinite, ∀ i j, pLoc E w (pFin E ((((x : UA E n) : GA E n))⁻¹.val i j)) ∈ Formalism.UG.Ov E w := by
    simp only [Filter.eventually_all]; exact fun i j => h _
  filter_upwards [h1, h2] with w a b
  have hK : cLoc w (x : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    refine mem_GLint_of_entries _ _ (fun i j => a i j) (fun i j => ?_)
    rw [← map_inv]
    exact b i j
  unfold toSub
  split_ifs with hU
  · exact Subgroup.mem_subgroupOf.2 hK
  · exact one_mem _

theorem cLoc_finPt_val (w : Pl E) (γ : UE E n) :
    (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)).val = γ.1.val.map (algebraMap E (w.adicCompletion E)) := by
  rw [FinPtLoc.finPt_eq]
  refine Matrix.ext fun i j => ?_
  change pLoc E w (pFin E ((finGL E n (ratF E n γ.1)).val i j)) = algebraMap E _ (γ.1.val i j)
  rw [FinPtLoc.snd_entry]
  rfl

theorem separable_of_monic_natDegree_le_one {K : Type} [Field K] {p : K[X]} (hm : p.Monic) (hd : p.natDegree ≤ 1) :
    p.Separable := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd with h | h
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hm h]; exact separable_one
  · rw [Polynomial.Monic.eq_X_add_C hm h]; exact separable_X_add_C _

end GlobalTheory.BCT.RegVan

theorem GlobalTheory.BCT.regvan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E))
    (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ w ∈ S,
    (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → ∀ (x : finU (E := E) (n := n)) (γ : UE E n),
    globFn S f (x⁻¹ * finPt γ * x) ≠ 0 → γ.1.val.charpoly.Separable := by
  intro E _ _ _ n S K' f hT w hw hsep x γ hne
  set y : finU (E := E) (n := n) := x⁻¹ * finPt γ * x with hy
  set g : Pl E → ℂ := fun u => f u (toSub (UL n u) (cLoc u (y : UA E n))) with hg
  have hev : ∀ᶠ u in cofinite, g u = 1 := by
    filter_upwards [RegVan.eventually_toSub_mem y, hT.2] with u a b
    simp only [hg, b]
    rw [Set.indicator_of_mem a]
    rfl
  have hfin : (Function.mulSupport g).Finite := hev
  have hgw : g w ≠ 0 := by
    intro h0
    apply hne
    unfold globFn
    rw [finprod_mem_def]
    refine finprod_eq_zero (S.mulIndicator g) w (by rw [Set.mulIndicator_of_mem hw]; exact h0) ?_
    exact hfin.subset (by rw [Set.mulSupport_mulIndicator]; exact Set.inter_subset_right)
  have hs := hsep _ hgw
  by_cases hmem : cLoc w (y : UA E n) ∈ UL n w
  · rw [show toSub (UL n w) (cLoc w (y : UA E n)) = ⟨_, hmem⟩ from dif_pos hmem] at hs
    change (cLoc w (y : UA E n)).val.charpoly.Separable at hs
    have hyv : (cLoc w (y : UA E n)).val = (cLoc w (x : UA E n))⁻¹.val *
        (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)).val * (cLoc w (x : UA E n)).val := by
      rw [hy]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, Units.val_mul]
    rw [hyv, Matrix.coe_units_inv, Matrix.charpoly_units_conj', RegVan.cLoc_finPt_val, Matrix.charpoly_map] at hs
    exact (separable_map _).1 hs
  · rw [show toSub (UL n w) (cLoc w (y : UA E n)) = 1 from dif_neg hmem] at hs
    change (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly.Separable at hs
    rw [Matrix.charpoly_one, Fintype.card_fin, ← C_1] at hs
    have hn : n ≤ 1 := by
      rcases hs.of_pow' with h | ⟨_, h⟩ | h
      · exact absurd h (not_isUnit_X_sub_C _)
      · omega
      · omega
    exact RegVan.separable_of_monic_natDegree_le_one (Matrix.charpoly_monic _)
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hn)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableCharpolyOfTestFunctionNeZeroRegularPlacStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_charpoly_of_testFunction_ne_zero_regularPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ w ∈ S, (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → ∀ (x : finU (E := E) (n := n)) (γ : UE E n), globFn S f (x⁻¹ * finPt γ * x) ≠ 0 → γ.1.val.charpoly.Separable := by
  first | exact @GlobalTheory.BCT.regvan | exact GlobalTheory.BCT.regvan | (intros; apply GlobalTheory.BCT.regvan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulReadingOfMovedSectionAtFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneConstRatioOfCommonRatio
namespace GlobalTheory

theorem exists_norm_one_const_ratio_of_common_ratio :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (I : Type) (S : Set V),
      IsOpen S → IsPreconnected S → ∀ (A B : I → V → ℂ) (t : V → ℂ), (∀ i, DifferentiableOn ℂ (A i) S) →
      (∀ i, DifferentiableOn ℂ (B i) S) → (∀ i, ∀ x ∈ S, A i x = t x * B i x) →
      (∀ i, ∀ x ∈ S, ‖A i x‖ = ‖B i x‖) → ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ i, ∀ x ∈ S, A i x = ε * B i x := by
  intro V _ _ _ I S hS hc A B t hA hB ht hn
  by_cases h0 : ∀ i, ∀ x ∈ S, B i x = 0
  · refine ⟨1, norm_one, fun i x hx => ?_⟩
    rw [ht i x hx, h0 i x hx, mul_zero, mul_zero]
  · simp only [not_forall] at h0
    obtain ⟨i₀, x₀, hx₀, hne⟩ := h0
    obtain ⟨_, c, hcc⟩ := exists_eq_const_mul_of_forall_exists_norm_eq V Unit S hS hc ⟨x₀, hx₀⟩ (A i₀)
      (fun _ => B i₀) (hA i₀) (fun _ => hB i₀) (fun x hx => ⟨(), hn i₀ x hx⟩)
    refine ⟨c, ?_, fun i x hx => ?_⟩
    · have h1 := hn i₀ x₀ hx₀
      rw [hcc x₀ hx₀, norm_mul] at h1
      exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hne) (by rw [one_mul]; exact h1)
    · have hd : DifferentiableOn ℂ (fun y => A i y - c * B i y) S := (hA i).sub ((hB i).const_mul c)
      have := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero hS hc (hB i₀) hd (fun y hy => by
        have e1 := ht i y hy
        have e2 := ht i₀ y hy
        have e3 : A i₀ y = c * B i₀ y := hcc y hy
        show B i₀ y * (A i y - c * B i y) = 0
        rw [e1]
        linear_combination (B i y) * (e3 - e2)) hx₀ hne x hx
      exact sub_eq_zero.mp this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulReadingOfMovedSectionAtFrame
set_option autoImplicit false

namespace GlobalTheory.GeoLevel

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix


set_option maxHeartbeats 1000000 in
theorem exists_const_rdU_of_moveMatch : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U U' : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Formalism.L2.PjFree.IsUnf U' → ∀ (k : U.Comp) (k' : U'.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U'.X k') δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U' k k' h ρ ν → (∀ (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 → FrMove ρ ν (U.un k x) y' → FrBor t (U'.un k' ⟨_, h.mem_dom x.2⟩) y' → cabs (t none : CAt σ) = 1) → ∀ n : ℕ, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = ε * Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x)) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U U' hσ hU hU' k k' δ h ρ ν hρ hM hone n
  obtain ⟨hun1, -⟩ := GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ r U hσ hU
  have hex : ∀ x : (U.X k).dom, ∃ (y' : FrPt Xo c (CAt σ)) (t₀ : (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' ∧
      FrBor (fun i => Option.elim i t₀ (fun _ => 1)) (U'.un k' ⟨_, h.mem_dom x.2⟩) y' := fun x => by
    obtain ⟨y', hy'⟩ := (GlobalTheory.exists_unique_frMove E H Dw l Xo c ρ ν hρ (CAt σ) (U.un k x)).1
    obtain ⟨t₀, ht₀⟩ := exists_frBor_gen _ y' (hM x y' hy').1 (hM x y' hy').2
    exact ⟨y', t₀, hy', ht₀⟩
  choose y' t₀ hm hb using hex
  have hla : ∀ (w : (E →+* ℂ) × ℕ → ℕ) (τ : (U'.X k').Ψ) (i : Fin r),
      Formalism.L2.PjFree.laU U' w n k' τ i = Formalism.L2.PjFree.laU U w n k ⟨τ.1, h.mem τ⟩ i := fun w τ i => by
    unfold Formalism.L2.PjFree.laU
    rw [h.p0]
  have key : ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n,
      (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x : (U.X k).dom,
      Formalism.L2.PjFree.rdU U f' k x.1 = Formalism.L2.PjFree.toC (t₀ x : CAt σ) ^ n *
        Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x.1)) := fun w hD f hf f' hf' hv x => by
    have v1 : Formalism.L2.PjFree.rdU U f' k x.1 = Formalism.L2.PjFree.toC (evR Xo c f' (U.un k x)) := dif_pos x.2
    have v2 : Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x.1)) =
      Formalism.L2.PjFree.toC (evR Xo c f (U'.un k' ⟨_, h.mem_dom x.2⟩)) := dif_pos (h.mem_dom x.2)
    have v3 := (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 (CAt σ)
        (inferInstanceAs (IsReduced ℂ)) w n f hf _ _ (y' x) (hb x)
    have v4 : Formalism.L2.PjFree.toC (wchar (ex Dw w n) (fun i => Option.elim i (t₀ x) (fun _ => 1)) : CAt σ) =
        Formalism.L2.PjFree.toC (t₀ x : CAt σ) ^ n := by
      have : Formalism.L2.PjFree.toC (wchar (ex Dw w n) (fun i => Option.elim i (t₀ x) (fun _ => 1)) : CAt σ) =
          ∏ j, Formalism.L2.PjFree.toC (((fun i => Option.elim i (t₀ x) (fun _ => 1) : Ix Dw → (CAt σ)ˣ) j : (CAt σ)ˣ) : CAt σ) ^ ex Dw w n j := rfl
      rw [this, Finset.prod_eq_single none]
      · rfl
      · rintro (_ | j) _ hj
        · exact (hj rfl).elim
        · exact one_pow _
      · intro hn; exact (hn (Finset.mem_univ _)).elim
    rw [v1, v2, hv _ _ (hm x), v3, ← v4]
    rfl
  obtain ⟨ε, hε, hc⟩ := GlobalTheory.exists_norm_one_const_ratio_of_common_ratio (Frame (U.X k).Ψ r)
    {p : ((E →+* ℂ) × ℕ → ℕ) × Rul Xo c × Rul Xo c // Dom p.1 n ∧ p.2.1 ∈ sec Xo c p.1 n ∧ p.2.2 ∈ sec Xo c p.1 n ∧
      ∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c p.2.2 y = evR Xo c p.2.1 y'}
    (U.X k).dom (FourierCoefficientDomain.isOpen_dom _) (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected
    (fun i => Formalism.L2.PjFree.rdU U i.1.2.2 k)
    (fun i x => Formalism.L2.PjFree.rdU U' i.1.2.1 k' (lact δ (castFr h.psi x)))
    (fun x => if hx : x ∈ (U.X k).dom then Formalism.L2.PjFree.toC (t₀ ⟨x, hx⟩ : CAt σ) ^ n else 0)
    (fun i => (hU.2.2.2.2.1 _ n i.2.1 _ i.2.2.2.1 k).1)
    (fun i => (hU'.2.2.2.2.1 _ n i.2.1 _ i.2.2.1 k').1.comp ((GlobalTheory.Dict.Extend.differentiable_lact δ).comp
      (GlobalTheory.Dict.Pull.cast_diff h.psi)).differentiableOn fun x hx => h.mem_dom hx)
    (fun i x hx => by
      rw [dif_pos hx]
      exact key _ i.2.1 _ i.2.2.1 _ i.2.2.2.1 i.2.2.2.2 ⟨x, hx⟩)
    (fun ⟨⟨w, f, f'⟩, hD, hf, hf', hv⟩ x hx => by
      obtain ⟨x₀, hx₀, ⟨b₀, hb₀, e₀⟩, -⟩ := hun1 k ⟨x, hx⟩
      have hsec := hU.2.2.2.2.1 w n hD f' hf' k
      have hQ := hU'.2.2.2.2.1 w n hD f hf k'
      have h1 : ‖Formalism.L2.PjFree.toC (t₀ x₀ : CAt σ)‖ = 1 := hone x₀ _ _ hx₀ (hm x₀) (hb x₀)
      have v5 := congrArg norm (key w hD f hf f' hf' hv x₀)
      rw [norm_mul, norm_pow, h1, one_pow, one_mul, e₀, hsec.2.1 x hx b₀ hb₀,
        GlobalTheory.Dict.Pull.cast_rmul, GlobalTheory.Dict.Extend.lact_rmul,
        hQ.2.1 _ (h.mem_dom hx) _ (GlobalTheory.Dict.Pull.cast_bor h.psi hb₀),
        GlobalTheory.Dict.Pull.cast_bchar h.psi (hla w), norm_mul, norm_mul] at v5
      exact mul_left_cancel₀ (norm_ne_zero_iff.2 (AR.Up.OntoE.bchar_ne _ _ hb₀)) v5)
  exact ⟨ε, hε, fun w hD f hf f' hf' hv x hx => hc ⟨⟨w, f, f'⟩, hD, hf, hf', hv⟩ x hx⟩

end GlobalTheory.GeoLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulReadingOfMovedSectionAtFrameStatement
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_mul_reading_of_moved_section_at_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U U' : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Formalism.L2.PjFree.IsUnf U' → ∀ (k : U.Comp) (k' : U'.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U'.X k') δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U' k k' h ρ ν → (∀ (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 → FrMove ρ ν (U.un k x) y' → FrBor t (U'.un k' ⟨_, h.mem_dom x.2⟩) y' → cabs (t none : CAt σ) = 1) → ∀ n : ℕ, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = ε * Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x)) := by
  first | exact @GlobalTheory.GeoLevel.exists_const_rdU_of_moveMatch | exact GlobalTheory.GeoLevel.exists_const_rdU_of_moveMatch | (intros; apply GlobalTheory.GeoLevel.exists_const_rdU_of_moveMatch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerBlockLeParabolic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerBis
namespace GlobalTheory.IntertwiningOperators

open Polynomial

theorem intertwine {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C)
    (p : K[X]) : aeval B p * C = C * aeval A p := by
  induction p using Polynomial.induction_on with
  | C c =>
    simp only [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c ih =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval B) (Polynomial.C c * X ^ n) X,
      map_mul (aeval A) (Polynomial.C c * X ^ n) X, aeval_X, aeval_X, Matrix.mul_assoc, ← h,
      ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem main : ∀ {K : Type} [inst : Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K),
    IsCoprime (Matrix.charpoly A) (Matrix.charpoly B) → C * A = B * C →
      C = (0 : Matrix (Fin b) (Fin a) K) := by
  intro K _ a b A B C hcop h
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval B u * aeval B (Matrix.charpoly A) = 1 := by
    have := congrArg (aeval B) huv
    rw [map_add (f := _), map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero, map_one] at this
    exact this
  have h2 : aeval B (Matrix.charpoly A) * C = 0 := by
    rw [intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  calc C = (aeval B u * aeval B (Matrix.charpoly A)) * C := by rw [h1, Matrix.one_mul]
    _ = 0 := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero]

end GlobalTheory.IntertwiningOperators
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerBlockLeParabolic
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc

theorem intertwiner_eq_zero_of_isCoprime {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hc : IsCoprime A.charpoly B.charpoly) (hC : C * A = B * C) : C = 0 := by
  first
  | exact @_root_.GlobalTheory.IntertwiningOperators.main
  | exact _root_.GlobalTheory.IntertwiningOperators.main
  | (apply _root_.GlobalTheory.IntertwiningOperators.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwiningOperators.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwiningOperators.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwiningOperators.main ..)

theorem twCent_blk_le_parP : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable →
    twCent (MonoidHom.id (GLw n w)) (blk h w m 0) ≤ GlobalTheory.LeviDesc.parP a n w := by
  intro E _ _ n a b h w m hsep g hg
  have hcop := hsep.isCoprime
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  have hval : ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val) := by
    simp only [blk]
    rw [dite_eq_left hM]
    rfl
  rw [Matrix.mul_zero] at hval
  have hc : (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (blk h w m 0 : GLw n w) =
      ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * g := by
    have := congrArg Units.val (show g * blk h w m 0 = blk h w m 0 * MonoidHom.id _ g from hg)
    simpa using this
  rw [hval] at hc
  set e := finSumFinEquiv.trans (finCongr h) with he
  set g' := Matrix.reindex e.symm e.symm (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hg'
  have hgg : (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.reindex e e g' := by
    simp [hg']
  rw [hgg, ← Matrix.fromBlocks_toBlocks g'] at hc
  have hc2 := congrArg (Matrix.reindex e.symm e.symm) hc
  simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id, Matrix.fromBlocks_multiply] at hc2
  rw [Matrix.fromBlocks_inj] at hc2
  have hC : g'.toBlocks₂₁ * m.1.val = m.2.val * g'.toBlocks₂₁ := by
    have := hc2.2.2.1
    simpa using this
  have hC0 := intertwiner_eq_zero_of_isCoprime _ _ _ hcop hC
  show (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular fun i : Fin n => decide (a ≤ (i : ℕ))
  intro i j hij
  have hi : a ≤ (i : ℕ) := by
    by_contra hc'
    revert hij
    simp only [hc', decide_false]
    cases decide (a ≤ (j : ℕ)) <;> decide
  have hj : ¬ a ≤ (j : ℕ) := by
    intro hc'
    revert hij
    simp only [hc', decide_true]
    cases decide (a ≤ (i : ℕ)) <;> decide
  have hie : i = e (Sum.inr ⟨(i : ℕ) - a, by omega⟩) := by
    ext; simp [he]; omega
  have hje : j = e (Sum.inl ⟨(j : ℕ), by omega⟩) := by
    ext; simp [he]
  rw [hgg, hie, hje]
  have : g'.toBlocks₂₁ ⟨(i : ℕ) - a, by omega⟩ ⟨(j : ℕ), by omega⟩ = 0 := by rw [hC0]; rfl
  simpa [Matrix.toBlocks₂₁] using this

end GlobalTheory.LeviDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerBlockLeParabolicStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_centralizer_block_le_parabolic : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable → twCent (MonoidHom.id (GLw n w)) (blk h w m 0) ≤ GlobalTheory.LeviDesc.parP a n w := by
  first | exact @GlobalTheory.LeviDesc.twCent_blk_le_parP | exact GlobalTheory.LeviDesc.twCent_blk_le_parP | (intros; apply GlobalTheory.LeviDesc.twCent_blk_le_parP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerAbs

variable {G : Type} [Group G] [TopologicalSpace G]

def twTerm (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) : ℂ :=
  (((twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) *
    avg fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))

theorem twOrb_eq_finsum_twTerm (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) :
    twOrb θ K δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G), twTerm θ K δ f (Quotient.out q) :=
  rfl

end GlobalTheory.EulerAbs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTwistBaseOf
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OnCmp

theorem weil_twist_base_of : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (χ : (AE D)ˣ →* Circle) (ω : GlobalTheory.OnTies.WeilRep D i), GlobalTheory.OnCmp.IsWeilTw R i χ ω → ∀ (k : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) k x → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ω (1, k) f = ((χ x : Circle) : ℂ) • R.ωP i A.μ0 (1, k) f := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i χ ω hω k x hx f hf
  have h := GlobalTheory.TwistFactorProof.weil_ratio (GlobalTheory.T.weilDatum_unique_on_thetaFunctions D) (GlobalTheory.WeilChange.exists_weilDatum_twist D)
    (hR.thP.ωP i A.μ0) hω (GlobalTheory.TwistFactorProof.isDetRoot_one _) hx hf
  rw [h]
  congr 2
  show _ * (R.mu0 _ x * χ x * (R.mu0 _ x * R.xi A.μ0 x)⁻¹) = χ x
  rw [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hR.lev.xi_base ▸ hR.lev.xi A.μ0) x]
  simp only [map_one, mul_inv_cancel, inv_one, one_mul, mul_one]
  rw [mul_comm (R.mu0 _ x), mul_inv_cancel_right]

end GlobalTheory.OnCmp
end
