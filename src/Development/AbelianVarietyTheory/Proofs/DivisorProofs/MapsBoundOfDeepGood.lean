module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardMulFinrankEigenspaceLe
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem finrank_le_card_mul_finrank_eigenspace_le :
    ∀ (H K R : Type) [Group H] [Fintype H] [DecidableEq H] [Field K] [CommRing R] [Algebra K R]
      (st : H → R →ₐ[K] R), (∀ x, st 1 x = x) → (∀ h h' x, st (h * h') x = st h' (st h x)) →
      ∀ (χ : H →* Kˣ) (u : R),
      (Matrix.of fun h g : H => st (h * g) u).det ∈ nonZeroDivisors R →
      ∀ (Vm V Vp N : Submodule K R) [FiniteDimensional K Vm] [FiniteDimensional K V]
        [FiniteDimensional K Vp], (∀ h, ∀ x ∈ V, st h x ∈ V) →
      (∀ h, ∀ x ∈ Vm, x * st h u ∈ V) → (∀ h, ∀ x ∈ V, x * st h u ∈ Vp) →
      (∀ x, x ∈ N ↔ x ∈ V ∧ ∀ h, st h x = ((χ h : Kˣ) : K) • x) →
      Module.finrank K Vm ≤ Fintype.card H * Module.finrank K N ∧
        Fintype.card H * Module.finrank K N ≤ Module.finrank K Vp := by
  intro H K R _ _ _ _ _ _ st h1 hmul χ u hdet Vm V Vp N _ _ _ hV hm hp hN
  obtain ⟨hTr, hPhi, hPsi⟩ := GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet H K R st h1 hmul χ u hdet
  have hNV : N ≤ V := fun x hx => ((hN x).1 hx).1
  have : FiniteDimensional K N := Submodule.finiteDimensional_of_le hNV
  have hrk : Module.finrank K (H → N) = Fintype.card H * Module.finrank K N := by
    rw [Module.finrank_pi_fintype]
    simp
  rw [← hrk]
  constructor
  · have hmem : ∀ (f : Vm) (h : H),
        ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g ((f : R) * st h u) ∈ N := fun f h =>
      (hN _).2 ⟨V.sum_mem fun g _ => V.smul_mem _ (hV g _ (hm h _ f.2)), fun g => hTr _ g⟩
    let Φ : Vm →ₗ[K] (H → N) :=
      { toFun := fun f h => ⟨_, hmem f h⟩
        map_add' := fun f f' => by
          funext h
          apply Subtype.ext
          simp only [Submodule.coe_add, add_mul, map_add (f := _), smul_add, Finset.sum_add_distrib,
            Pi.add_apply]
        map_smul' := fun c f => by
          funext h
          apply Subtype.ext
          simp only [Submodule.coe_smul, smul_mul_assoc, map_smul, Pi.smul_apply,
            RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun g _ => smul_comm _ _ _ }
    refine LinearMap.finrank_le_finrank_of_injective (f := Φ) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    apply Subtype.ext
    exact hPhi f fun h => congrArg Subtype.val (congrFun hf h)
  · have hmem : ∀ F : H → N, ∑ h, (F h : R) * st h u ∈ Vp := fun F =>
      Vp.sum_mem fun h _ => hp h _ (hNV (F h).2)
    let Ψ : (H → N) →ₗ[K] Vp :=
      { toFun := fun F => ⟨_, hmem F⟩
        map_add' := fun F F' => by
          apply Subtype.ext
          simp only [Submodule.coe_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]
        map_smul' := fun c F => by
          apply Subtype.ext
          simp only [Submodule.coe_smul, smul_mul_assoc, Pi.smul_apply,
            RingHom.id_apply, Finset.smul_sum] }
    refine LinearMap.finrank_le_finrank_of_injective (f := Ψ) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro F hF
    have := hPsi (fun h => (F h : R)) (fun h g => ((hN _).1 (F h).2).2 g)
      (congrArg Subtype.val hF)
    funext h
    exact Subtype.ext (congrFun this h)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspPhMemChiLat
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LevDesc

theorem cuspPh_mem_chiLat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E) (hG : Even G.2) (hW : Even W.2) (hK : KeepsCusp U (G + W)) (hKW : KeepsCusp U W), (∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U (G + W)), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U (G + W) → g ∈ latW U (G + W)) → (∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U W), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U W → g ∈ latW U W) → ∀ (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W), u ∈ latW U W → ∀ f : cuspW Xo c U G, f ∈ latW U G → ∀ h : S, GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h ∈ GlobalTheory.LevDesc.chiLat S U (G + W) χ := by
  intro E _ _ _ H Dw l Xo c r U S hpq hA G W hG hW hK hKW hGW hWW χ u hu f hf h
  rw [GlobalTheory.LevDesc.mem_chiLat]
  refine ⟨?_, fun g => ?_⟩
  · have hint : ∀ g : S, IsIntegral ℤ ((((χ g)⁻¹ : (c.F)ˣ) : c.F)) := fun g => by
      refine IsIntegral.of_pow (Fintype.card_pos (α := S)) ?_
      rw [← Units.val_pow_eq_pow_val, ← map_inv, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
      exact isIntegral_one
    have hmem : ∀ g : S, pull Xo c g ((f : Rul Xo c) * pull Xo c h u) ∈ cuspW Xo c U (G + W) := fun g =>
      hK _ _ (GlobalTheory.SlopeRec.mul_mem_cuspW hG hW f.2 (hKW _ _ u.2))
    have hlat : ∀ g : S, (⟨_, hmem g⟩ : cuspW Xo c U (G + W)) ∈ latW U (G + W) := fun g => by
      have hu' : (⟨pull Xo c h u, hKW _ _ u.2⟩ : cuspW Xo c U W) ∈ latW U W := hWW h u _ rfl hu
      have hm : (f : Rul Xo c) * pull Xo c h u ∈ cuspW Xo c U (G + W) := GlobalTheory.SlopeRec.mul_mem_cuspW hG hW f.2 (hKW _ _ u.2)
      exact hGW g ⟨_, hm⟩ _ rfl (GlobalTheory.AllWt.mul_mem_supLat hf hu' hm)
    have he : GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h =
        ∑ g : S, (⟨_, hint g⟩ : 𝓞 c.F) • (⟨_, hmem g⟩ : cuspW Xo c U (G + W)) := by
      apply Subtype.ext
      rw [GlobalTheory.LevDesc.coe_cuspPh, GlobalTheory.LevDesc.levPh_apply, GlobalTheory.LevDesc.levTr_apply, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Submodule.coe_smul_of_tower, ← algebraMap_smul (c.F)]
      rfl
    rw [he]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hlat g)
  · rw [GlobalTheory.LevDesc.coe_cuspPh, GlobalTheory.LevDesc.levPh_apply]
    exact (GlobalTheory.LevDesc.mem_levEigen.1 (GlobalTheory.LevDesc.levTr_mem_levEigen hpq hA χ _)) g

end GlobalTheory.LevDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulRkKChiLatLeRankW
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.CovolRank

theorem comap_val_finite {K B : Type} [Field K] [CommRing B] [Algebra K B] (A : Subalgebra K B)
    (C : Submodule K B) [FiniteDimensional K C] :
    FiniteDimensional K (C.comap A.val.toLinearMap) ∧
      Module.finrank K (C.comap A.val.toLinearMap) ≤ Module.finrank K C := by
  let f : C.comap A.val.toLinearMap →ₗ[K] C :=
    LinearMap.codRestrict C (A.val.toLinearMap ∘ₗ (C.comap A.val.toLinearMap).subtype)
      fun y => Submodule.mem_comap.1 y.2
  have hf : Function.Injective f := fun a b hab => by
    have h := congrArg (fun z : C => (z : B)) hab
    exact Subtype.ext (Subtype.ext h)
  haveI : FiniteDimensional K (C.comap A.val.toLinearMap) := Module.Finite.of_injective f hf
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_injective hf⟩

theorem finrank_span_le_of_map {K B : Type} [Field K] [CommRing B] [Algebra K B] (A : Subalgebra K B)
    (C : Submodule K B) (hC : C ≤ Subalgebra.toSubmodule A) {O : Type} [CommRing O] [Module O C]
    (L : Submodule O C) (N : Submodule K A) [FiniteDimensional K N]
    (hL : ∀ F ∈ L, (⟨(F : B), hC F.2⟩ : A) ∈ N) :
    Module.finrank K (Submodule.span K (L : Set C)) ≤ Module.finrank K N := by
  let Φ : C →ₗ[K] A := LinearMap.codRestrict (Subalgebra.toSubmodule A) C.subtype fun y => hC y.2
  have hΦ : Function.Injective Φ := fun a b hab => by
    have h := congrArg (fun z : A => (z : B)) hab
    exact Subtype.ext h
  have hle : Submodule.span K (L : Set C) ≤ N.comap Φ := by
    rw [Submodule.span_le]
    intro F hF
    exact hL F hF
  let ψ : Submodule.span K (L : Set C) →ₗ[K] N :=
    LinearMap.codRestrict N (Φ ∘ₗ (Submodule.span K (L : Set C)).subtype) fun y => hle y.2
  have hψ : Function.Injective ψ := fun a b hab => Subtype.ext (hΦ (congrArg Subtype.val hab))
  exact LinearMap.finrank_le_finrank_of_injective hψ

end GlobalTheory.CovolRank

namespace GlobalTheory.CovolRank

set_option maxHeartbeats 4000000 in
theorem card_mul_rkK_chiLat_le_rankW : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {D : D7} (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E), Even G.2 → Even W.2 → KeepsCusp U G → KeepsCusp U W → GoodW U x V dict G → GoodW U x V dict (G + W) → ∀ (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W), (∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) → Fintype.card S * Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ) ≤ rankW U (G + W) := by
  classical
  intro E _ _ _ H Dw l Xo c r U D x V dict S hpq hA G W hG hW hKG hKW hgG hgGW χ u hdet
  have hsec : ∀ G' : WTZ E, cuspW Xo c U G' ≤ Subalgebra.toSubmodule (secRing Xo c) :=
    fun G' f hf => GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ G' hf)
  have hfin : ∀ G' : WTZ E, GlobalTheory.AllWt.GoodW U x V dict G' → FiniteDimensional c.F (cuspW Xo c U G') := by
    intro G' hg
    obtain ⟨n, ⟨b, _⟩, _⟩ := hg.1.some
    exact Module.Finite.of_basis b
  have := hfin G hgG
  have := hfin (G + W) hgGW
  obtain ⟨hVs, -⟩ := comap_val_finite (secRing Xo c) (cuspW Xo c U G)
  obtain ⟨hVp, hVp'⟩ := comap_val_finite (secRing Xo c) (cuspW Xo c U (G + W))
  let uR : secRing Xo c := ⟨u, hsec W u.2⟩
  have hact := GlobalTheory.LevDesc.isRightAct_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA
  have hdet' : (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) uR).det ∈
      nonZeroDivisors (secRing Xo c) := by
    have hc := GlobalTheory.LevDesc.coe_det_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA uR
    refine mem_nonZeroDivisors_iff_left.mpr fun y hy => ?_
    apply Subtype.ext
    have h0 : levDet Xo c S u * (y : Rul Xo c) = 0 := by
      rw [← hc]; exact congrArg Subtype.val hy
    exact hdet _ y.2 h0

  let ι : secRing Xo c →ₗ[c.F] Rul Xo c := (secRing Xo c).val.toLinearMap
  let N : Submodule c.F (secRing Xo c) :=
    (cuspW Xo c U G).comap ι ⊓ GlobalTheory.LevDesc.eigen (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) χ
  have key := (GlobalTheory.finrank_le_card_mul_finrank_eigenspace_le S c.F (secRing Xo c)
    (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) hact.1 hact.2 χ uR hdet'
    ⊥ ((cuspW Xo c U G).comap ι) ((cuspW Xo c U (G + W)).comap ι) N
    (fun h y hy => hKG h _ hy)
    (fun h y hy => by
      rw [Submodule.mem_bot] at hy
      subst hy
      rw [zero_mul]; exact Submodule.zero_mem _)
    (fun h y hy => GlobalTheory.SlopeRec.mul_mem_cuspW hG hW hy (hKW h _ u.2))
    (fun y => Submodule.mem_inf)).2
  have : FiniteDimensional c.F N := Submodule.finiteDimensional_of_le inf_le_left
  have h1 : Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ) ≤ Module.finrank c.F N :=
    finrank_span_le_of_map (secRing Xo c) (cuspW Xo c U G) (hsec G) _ N fun F hF =>
      ⟨F.2, fun h => Subtype.ext (hF.2 h)⟩
  have e : rankW U (G + W) = Module.finrank c.F (cuspW Xo c U (G + W)) := by
    rw [rankW, Formalism.HN.rkK, hgGW.2.2, finrank_top]
  calc Fintype.card S * Formalism.HN.rkK (GlobalTheory.LevDesc.chiLat S U G χ)
      ≤ Fintype.card S * Module.finrank c.F N := Nat.mul_le_mul_left _ h1
    _ ≤ Module.finrank c.F ((cuspW Xo c U (G + W)).comap ι) := key
    _ ≤ rankW U (G + W) := e ▸ hVp'

end GlobalTheory.CovolRank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSqNormWCuspPhLe
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

theorem hasGram_norm_sum_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    {N : (K →+* ℂ) → V → ℝ} (hN : GlobalTheory.AllWt.HasGram N) (σ : K →+* ℂ)
    (hτ : ∀ y, N (InfinitePlace.mk σ).embedding y = N σ y) {ι : Type} (s : Finset ι) (y : ι → V) :
    N σ (∑ i ∈ s, y i) ≤ ∑ i ∈ s, N σ (y i) ∧ ∀ z, 0 ≤ N σ z := by
  obtain ⟨⟨n, ⟨b, X⟩, hbX⟩⟩ := hN
  letI : StarRing K := starRingOfComm
  let Φ : V →+ EuclideanSpace ℂ (Fin n) :=
    { toFun := fun y => (WithLp.equiv 2 (Fin n → ℂ)).symm (Formalism.HermitianLatticesTheory.fcoord b X (InfinitePlace.mk σ) y)
      map_zero' := by rw [Formalism.HermitianLatticesTheory.fcoord_zero]; rfl
      map_add' := fun y z => by rw [Formalism.HermitianLatticesTheory.fcoord_add]; rfl }
  have hΦ : ∀ y, N σ y = ‖Φ y‖ := by
    intro y
    rw [← hτ, ← (hbX (InfinitePlace.mk σ)).2 y, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, EuclideanSpace.norm_eq]
    rfl
  refine ⟨?_, fun z => (hΦ z).symm ▸ norm_nonneg _⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hΦ, map_sum]
  exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun g _ => (hΦ _).symm))

theorem sum_sq_normW_cuspPh_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {D : D7} (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (G W : WTZ E) (hG : Even G.2) (hW : Even W.2) (hK : KeepsCusp U (G + W)) (hKW : KeepsCusp U W) (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W) (B : ℝ), 0 ≤ B → GlobalTheory.AllWt.HasGram (GlobalTheory.AllWt.normW U x V dict (G + W)) → (∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U (G + W)), (g : Rul Xo c) = pull Xo c γ f → ∀ σ, GlobalTheory.AllWt.normW U x V dict (G + W) σ g = GlobalTheory.AllWt.normW U x V dict (G + W) σ f) → (∀ (γ : LevelAut Dw l) (f : cuspW Xo c U G) (g : cuspW Xo c U (G + W)), (g : Rul Xo c) = f * pull Xo c γ u → ∀ σ, GlobalTheory.AllWt.normW U x V dict (G + W) σ g ≤ B * GlobalTheory.AllWt.normW U x V dict G σ f) → ∀ (f : cuspW Xo c U G) (σ : c.F →+* ℂ), ∑ h : S, GlobalTheory.AllWt.normW U x V dict (G + W) σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h) ^ 2 ≤ (Fintype.card S : ℝ) ^ 3 * B ^ 2 * GlobalTheory.AllWt.normW U x V dict G σ f ^ 2 := by
  intro E _ _ _ H Dw l Xo c r U D x V dict S hpq hA G W hG hW hK hKW χ u B hB hGram hinv hbd f σ
  set N := GlobalTheory.AllWt.normW U x V dict (G + W) with hN
  have hconj : ∀ y, N ((starRingEnd ℂ).comp σ) y = N σ y := fun y => by
    rw [hN, GlobalTheory.AllWt.normW, GlobalTheory.AllWt.normW, GlobalTheory.AllWt.petW, GlobalTheory.AllWt.petW, GlobalTheory.CompHt.goodOf_conj σ]
  have hτ : ∀ y, N (InfinitePlace.mk σ).embedding y = N σ y := by
    intro y
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · have e : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun a => by rw [ComplexEmbedding.conjugate_coe_eq]; rfl
      rw [h, e, hconj]
  have hnn : ∀ y, 0 ≤ N σ y := (hasGram_norm_sum_le hGram σ hτ (∅ : Finset S) (fun _ => 0)).2
  have hsum : ∀ (s : Finset S) (y : S → cuspW Xo c U (G + W)), N σ (∑ g ∈ s, y g) ≤ ∑ g ∈ s, N σ (y g) :=
    fun s y => (hasGram_norm_sum_le hGram σ hτ s y).1
  have hsmul : ∀ (a : c.F) (y : cuspW Xo c U (G + W)), N σ (a • y) = ‖σ a‖ * N σ y := fun a y => by
    rw [hN, GlobalTheory.AllWt.normW, GlobalTheory.AllWt.normW, Submodule.coe_smul, GlobalTheory.AllWt.petW_smul]
  have hunit : ∀ g : S, ‖σ (((χ g)⁻¹ : (c.F)ˣ) : c.F)‖ = 1 := by
    intro g
    have h1 : ((χ g)⁻¹) ^ (Fintype.card S) = 1 := by rw [← map_inv, ← map_pow, pow_card_eq_one, map_one]
    refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card S) ?_ Fintype.card_ne_zero
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  have hcomp : ∀ h : S, N σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c)
      (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h) ≤
        (Fintype.card S : ℝ) * (B * GlobalTheory.AllWt.normW U x V dict G σ f) := by
    intro h
    have hFm : (f : Rul Xo c) * pull Xo c (h : LevelAut Dw l) u ∈ cuspW Xo c U (G + W) :=
      GlobalTheory.SlopeRec.mul_mem_cuspW hG hW f.2 (hKW (h : LevelAut Dw l) _ u.2)
    have hP : ∀ g : S, pull Xo c (g : LevelAut Dw l) ((f : Rul Xo c) * pull Xo c (h : LevelAut Dw l) u) ∈
        cuspW Xo c U (G + W) := fun g => hK (g : LevelAut Dw l) _ hFm
    have he : ((GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c)
        (fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hG hW hK hKW χ u.2 hf h) f h : cuspW Xo c U (G + W)) : Rul Xo c) =
          ((∑ g : S, (((χ g)⁻¹ : (c.F)ˣ) : c.F) • (⟨_, hP g⟩ : cuspW Xo c U (G + W)) : cuspW Xo c U (G + W)) :
            Rul Xo c) := by
      rw [GlobalTheory.LevDesc.coe_cuspPh, GlobalTheory.LevDesc.levPh_apply, GlobalTheory.LevDesc.levTr_apply, Submodule.coe_sum]
      rfl
    rw [Subtype.ext he]
    refine (hsum _ _).trans ?_
    calc ∑ g : S, N σ ((((χ g)⁻¹ : (c.F)ˣ) : c.F) • (⟨_, hP g⟩ : cuspW Xo c U (G + W)))
        ≤ ∑ _g : S, B * GlobalTheory.AllWt.normW U x V dict G σ f := by
          refine Finset.sum_le_sum fun g _ => ?_
          rw [hsmul, hunit, one_mul, hinv (g : LevelAut Dw l) ⟨_, hFm⟩ ⟨_, hP g⟩ rfl σ]
          exact hbd (h : LevelAut Dw l) f ⟨_, hFm⟩ rfl σ
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc _ ≤ ∑ _h : S, ((Fintype.card S : ℝ) * (B * GlobalTheory.AllWt.normW U x V dict G σ f)) ^ 2 :=
        Finset.sum_le_sum fun h _ => pow_le_pow_left₀ (hnn _) (hcomp h) 2
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevPhInjectiveOfLevDetNonZeroDivisor
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.AllWt (cuspW latW GoodW rankW)
open GlobalTheory.LevDesc (levDet secRing pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory

theorem levPh_injective_of_levDet_nonZeroDivisor : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (S : Subgroup (LevelAut Dw l)), 1 ≤ Dw.p + Dw.q → l.A.Coprime l.M → ∀ (χ : S →* (c.F)ˣ) (u : Rul Xo c), u ∈ secRing Xo c → (∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) → ∀ f ∈ secRing Xo c, (∀ h : S, GlobalTheory.LevDesc.levPh Xo c S χ u f h = 0) → f = 0 := by
  classical
  intro E _ _ _ H Dw l Xo c S hpq hA χ u hu hdet f hf hph
  have hact := GlobalTheory.LevDesc.isRightAct_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA
  have hdet' : (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) ⟨u, hu⟩).det ∈
      nonZeroDivisors (secRing Xo c) := by
    have h1 := GlobalTheory.LevDesc.coe_det_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA ⟨u, hu⟩
    have hl : ∀ x : secRing Xo c,
        (Matrix.of fun h g : S => GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA (h * g) ⟨u, hu⟩).det * x = 0 → x = 0 := by
      intro x hx
      have h2 := congrArg Subtype.val hx
      simp only [Subalgebra.coe_mul, Subalgebra.coe_zero] at h2
      apply Subtype.ext
      refine hdet x x.2 ?_
      rw [← h1]
      exact h2
    rw [mem_nonZeroDivisors_iff]
    exact ⟨hl, fun x hx => hl x (by rw [mul_comm]; exact hx)⟩
  have key := (GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet S c.F (secRing Xo c)
    (GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA) hact.1 hact.2 χ ⟨u, hu⟩ hdet').2.1 ⟨f, hf⟩ (fun h => by
      have h3 := GlobalTheory.LevDesc.coe_tr_pullSecOn (Xo := Xo) (c := c) (S := S) hpq hA χ
        (⟨f, hf⟩ * GlobalTheory.LevDesc.pullSecOn Xo c S hpq hA h ⟨u, hu⟩)
      rw [GlobalTheory.LevDesc.tr_apply] at h3
      apply Subtype.ext
      rw [h3]
      exact hph h)
  exact congrArg Subtype.val key

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

namespace GlobalTheory.CovTop.DescentMaps

set_option synthInstance.maxHeartbeats 200000 in
theorem mapsCore {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {D : D7} {x : ℝ}
    {V : (c.F →+* ℂ) → HSp D} {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
    (S : Subgroup (LevelAut Dw l)) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Gm W G : WTZ E) (hGW : Gm + W = G)
    (hGm : Even Gm.2) (hW : Even W.2) (hKG : KeepsCusp U G) (hKW : KeepsCusp U W)
    (hLG : ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U G), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U G → g ∈ latW U G)
    (hLW : ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U W), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U W → g ∈ latW U W)
    (hNG : ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U G), (g : Rul Xo c) = pull Xo c γ f →
      ∀ σ, GlobalTheory.AllWt.normW U x V dict G σ g = GlobalTheory.AllWt.normW U x V dict G σ f)
    (hGood : GoodW U x V dict G) (hGoodP : GoodW U x V dict (G + W))
    (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W) (hu : u ∈ latW U W)
    (hdet : ∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ (γ : LevelAut Dw l) (f : cuspW Xo c U Gm) (g : cuspW Xo c U (Gm + W)), (g : Rul Xo c) = f * pull Xo c γ u →
      ∀ σ, GlobalTheory.AllWt.normW U x V dict (Gm + W) σ g ≤ B * GlobalTheory.AllWt.normW U x V dict Gm σ f)
    (b : ℝ) (hb : (Fintype.card S : ℝ) ^ 3 * B ^ 2 ≤ Real.exp (2 * b))
    (Lt : Submodule (𝓞 c.F) (cuspW Xo c U G)) (hLt : Lt = GlobalTheory.LevDesc.chiLat S U G χ) (Gp : WTZ E) (hGp : G + W = Gp) :
    ∃ (n : ℕ) (φ : Fin n → cuspW Xo c U Gm →ₗ[c.F] cuspW Xo c U G),
      (∀ h, ∀ f ∈ latW U Gm, φ h f ∈ Lt) ∧ (∀ f, (∀ h, φ h f = 0) → f = 0) ∧
      (∀ σ f, ∑ h, GlobalTheory.AllWt.normW U x V dict G σ (φ h f) ^ 2 ≤
        Real.exp (2 * b) * GlobalTheory.AllWt.normW U x V dict Gm σ f ^ 2) ∧
      n * Formalism.HN.rkK Lt ≤ rankW U Gp := by
  subst hGW hLt hGp
  have hm : ∀ f ∈ cuspW Xo c U Gm, ∀ h : S, GlobalTheory.LevDesc.levPh Xo c S χ (u : Rul Xo c) f h ∈ cuspW Xo c U (Gm + W) :=
    fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hGm hW hKG hKW χ u.2 hf h
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun k => LinearMap.proj (e k) ∘ₗ GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm, ?_, ?_, ?_, ?_⟩
  · intro k f hf
    exact GlobalTheory.LevDesc.cuspPh_mem_chiLat Xo c U S hpq hA Gm W hGm hW hKG hKW hLG hLW χ u hu f hf (e k)
  · intro f hf0
    have hsec : (f : Rul Xo c) ∈ secRing Xo c :=
      GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ _ f.2)
    have husec : (u : Rul Xo c) ∈ secRing Xo c :=
      GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ _ u.2)
    apply Subtype.ext
    refine GlobalTheory.levPh_injective_of_levDet_nonZeroDivisor Xo c S hpq hA χ u husec hdet _ hsec fun h => ?_
    have h1 := hf0 (e.symm h)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval, Equiv.apply_symm_apply] at h1
    rw [← GlobalTheory.LevDesc.coe_cuspPh S χ _ hm f h, h1]
    rfl
  · intro σ f
    have h1 : ∑ k, GlobalTheory.AllWt.normW U x V dict (Gm + W) σ ((LinearMap.proj (e k) ∘ₗ GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm) f) ^ 2 =
        ∑ h : S, GlobalTheory.AllWt.normW U x V dict (Gm + W) σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm f h) ^ 2 :=
      e.sum_comp (fun h : S => GlobalTheory.AllWt.normW U x V dict (Gm + W) σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm f h) ^ 2)
    rw [h1]
    refine (GlobalTheory.sum_sq_normW_cuspPh_le Xo c U x V dict S hpq hA Gm W hGm hW hKG hKW χ u B hB0 hGood.1 hNG hB f σ).trans ?_
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  · exact GlobalTheory.CovolRank.card_mul_rkK_chiLat_le_rankW Xo c U x V dict S hpq hA (Gm + W) W (hGm.add hW) hW hKG hKW hGood hGoodP χ u hdet

end GlobalTheory.CovTop.DescentMaps

namespace GlobalTheory.CovTop.DescentMaps


end GlobalTheory.CovTop.DescentMaps
