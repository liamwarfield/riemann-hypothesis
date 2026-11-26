module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalBounds
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalCompare

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver reesCechModule

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] (F : X.Modules)

def transMap (n : ℕ) : (c : ℕ) → idealPow I F (n + c + 1) ⟶ idealPow I F (n + 1)
  | 0 => 𝟙 _
  | c + 1 => idealPowSucc I F (n + c + 1) ≫ transMap n c

lemma transMap_ι (n : ℕ) : ∀ c, transMap I F n c ≫ idealPowι I F (n + 1) = idealPowι I F (n + c + 1)
  | 0 => Category.id_comp _
  | c + 1 => by
    rw [transMap, Category.assoc, transMap_ι n c, idealPowSucc_ι]
    rfl

variable {F} [F.IsQuasicoherent] (hF : IsCoherent F)

lemma coeff_mem_pow_of_le (r : reesAlgebra I) {n i : ℕ} (h : n ≤ i) :
    (r : Polynomial A).coeff i ∈ I ^ n :=
  Ideal.pow_le_pow_right h ((mem_reesAlgebra_iff I _).1 r.2 i)

lemma transMap_reesDeg_smul {V : X.Opens} (hV : IsAffineOpen V) (n d : ℕ) (r : reesAlgebra I)
    (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) (hs : ∀ j, d < j → reesCoef I hF hV j s = 0) :
    (transMap I F n (d + 1)).app V (reesDeg I hF hV (n + (d + 1) + 1) (reesInr I V r • s)) =
      ∑ j : Fin (d + 1), (idealPowOfMem I F ((r : Polynomial A).coeff (n + (d + 1) + 1 - j))
        (coeff_mem_pow_of_le I r (by omega))).app V (reesCoef I hF hV j s) := by
  apply idealPowι_app_injective I (n + 1)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, transMap_ι, idealPowι_reesDeg,
    reesCoef_reesInr_smul, map_sum]
  simp_rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, idealPowOfMem_ι]
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k l => (r : Polynomial A).coeff l • reesCoef I hF hV k s)]
  rw [Fin.sum_univ_eq_sum_range (fun j => (smulHom F (algebraMap A Γ(X, ⊤)
    ((r : Polynomial A).coeff (n + (d + 1) + 1 - j)))).app V (reesCoef I hF hV j s)) (d + 1)]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_range] at hk hk'
    rw [hs k (by omega), map_zero]

variable {ι : Type u} (𝔘 : ι → X.Opens)
  (hU : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a))) [Finite ι] (p : ℕ)

set_option maxHeartbeats 4000000 in
include hF hU in
theorem exists_transMap_eq_zero [IsProper (X ↘ Spec (.of A))] (hUtop : iSup 𝔘 = ⊤) :
    ∃ c, ∀ n (y : cechH (modulesAb (idealPow I F (n + c + 1))).obj 𝔘 p),
      cechHMap 𝔘 (modulesAbMap (idealPowι I F (n + c + 1))).hom p y = 0 →
        cechHMap 𝔘 (modulesAbMap (transMap I F n c)).hom p y = 0 := by
  classical
  have := finite_reesCech I 𝔘 p hF hUtop hU
  have hnoeth : IsNoetherian (reesAlgebra I) (cechH (reesPre I F) 𝔘 p) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨S, hS⟩ := hnoeth.noetherian (LinearMap.ker (reesΦ I hF 𝔘 hU p))
  choose σ hσ Nb hcls hNb using fun g => exists_cls_coef_eq_zero I hF 𝔘 hU p g
  obtain ⟨d, hd⟩ : ∃ d, d = S.sup Nb := ⟨_, rfl⟩
  refine ⟨d + 1, fun n y hy => ?_⟩
  have hκ : (reesIncFam I hF 𝔘 hU (n + (d + 1) + 1)).cechH p y ∈
      LinearMap.ker (reesΦ I hF 𝔘 hU p) := by
    rw [LinearMap.mem_ker]
    apply PolynomialModule.ext
    ext k
    rw [reesΦ_coeff, reesCoefFam_reesIncFam]
    split_ifs with h
    · subst h
      exact hy
    · rfl
  rw [← hS, Submodule.mem_span_finset] at hκ
  obtain ⟨f, -, hf⟩ := hκ
  have hy' : y = (reesDegFam I hF 𝔘 hU (n + (d + 1) + 1)).cechH p (∑ g ∈ S, f g • g) := by
    rw [hf, reesDegFam_reesIncFam]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hy', map_sum, map_sum]
  refine Finset.sum_eq_zero fun g hg => ?_
  have hgker : reesΦ I hF 𝔘 hU p g = 0 :=
    LinearMap.mem_ker.1 (hS ▸ Submodule.subset_span hg)
  have hgd : Nb g ≤ d := hd ▸ Finset.le_sup (f := Nb) hg
  have key : ∀ r : reesAlgebra I, cechHMap 𝔘 (modulesAbMap (transMap I F n (d + 1))).hom p
      ((reesDegFam I hF 𝔘 hU (n + (d + 1) + 1)).cechH p (r • g)) = 0 := by
    intro r
    rw [← hcls g]
    change cechHMap 𝔘 (modulesAbMap (transMap I F n (d + 1))).hom p
      ((reesDegFam I hF 𝔘 hU (n + (d + 1) + 1)).cechH p
        (cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p (cls (σ g) (hσ g)))) = 0
    rw [cechHMap_cls, CechFamily.cechH_cls, cechHMap_cls]
    have hterm : ∀ j : Fin (d + 1), cechHMap 𝔘 (modulesAbMap (idealPowOfMem I F (k := n + 1)
        ((r : Polynomial A).coeff (n + (d + 1) + 1 - j)) (coeff_mem_pow_of_le I r (by omega)))).hom p
        ((reesCoefFam I hF 𝔘 hU j).cechH p (cls (σ g) (hσ g))) = 0 := by
      intro j
      rw [hcls g, ← reesΦ_coeff, hgker, PolynomialModule.coeff_zero, Finsupp.zero_apply, map_zero]
    refine Eq.trans ?_ (Finset.sum_eq_zero (s := Finset.univ) fun j _ => hterm j)
    simp_rw [CechFamily.cechH_cls, cechHMap_cls]
    rw [← cls_sum]
    · refine cls_congr 𝔘 (funext fun t => ?_) _ _
      rw [Finset.sum_apply]
      exact transMap_reesDeg_smul I hF (isAffineOpen_inter 𝔘 hU t) n d r (σ g t)
        (fun j hj => hNb g j (by omega) t)
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_sum]
        exact Finset.sum_eq_zero fun j _ => by
          rw [← push_d, ← CechFamily.cochain_d, hσ g, map_zero, map_zero]
  exact key (f g)

end

end GroundTheory.Arith.SchemeCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe c236Ext c236Scheme

end

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

theorem exists_finite_affineCover (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated] :
    ∃ (ι : Type u) (_ : Finite ι) (𝔘 : ι → X.Opens), iSup 𝔘 = ⊤ ∧
      ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a)) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens => (V : Set X))
    (fun V => V.1.isOpen) (fun x _ => by
      obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hx⟩)
  refine ⟨s, inferInstance, fun V => V.1.1, ?_, fun m t => IsAffineOpen.iInf fun a => (t a).1.2⟩
  apply le_antisymm le_top
  intro x _
  obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨⟨V, hV⟩, hx⟩

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules}

lemma isSeparated_of_over [IsSeparated (X ↘ Spec (.of A))] : X.IsSeparated := by
  refine ⟨?_⟩
  rw [show terminal.from X = (X ↘ Spec (.of A)) ≫ terminal.from _ from terminal.hom_ext _ _]
  infer_instance

lemma cechK_succ_le {ι : Type u} (𝔘 : ι → X.Opens) (p n : ℕ) :
    cechK I 𝔘 p (F := F) (n + 1) ≤ cechK I 𝔘 p n := by
  rintro _ ⟨z, rfl⟩
  refine ⟨cechH.linearMap 𝔘 A (idealPowSucc I F n) p z, ?_⟩
  have h := congrArg (fun f => f.hom) (show modulesAbMap (idealPowSucc I F n) ≫
      modulesAbMap (idealPowι I F n) = modulesAbMap (idealPowι I F (n + 1)) by
    rw [← modulesAbMap_comp, idealPowSucc_ι])
  change cechHMap 𝔘 (modulesAbMap (idealPowι I F n)).hom p
      (cechHMap 𝔘 (modulesAbMap (idealPowSucc I F n)).hom p z) =
    cechHMap 𝔘 (modulesAbMap (idealPowι I F (n + 1))).hom p z
  rw [← cechHMap_comp]
  exact congrArg (fun f => cechHMap 𝔘 f p z) h

lemma towerComp_formalτQ_val (q n : ℕ) : ∀ (c : ℕ) (y : formalQ I F q (n + c)),
    ((towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c y : formalQ I F q n) :
      Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) =
      H.linearMap A (transMap I F n c) (q + 1) y
  | 0, y => by
    change (y : Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) =
      H.linearMap A (𝟙 _) (q + 1) y
    rw [H.linearMap_id]
    rfl
  | c + 1, y => by
    change ((towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c
      (formalτQ I F q (n + c) y) : formalQ I F q n) : Sheaf.H.{u} (modulesAb (idealPow I F (n + 1))) (q + 1)) = _
    rw [towerComp_formalτQ_val q n c, transMap, H.linearMap_comp]
    rfl

variable [IsProper (X ↘ Spec (.of A))] (hF : IsCoherent F)

include hF in
lemma exists_formalK_le (q : ℕ) : ∃ c, ∀ n, formalK I F q (n + c) ≤
    I ^ n • (⊤ : Submodule A (Sheaf.H.{u} (modulesAb F) q)) := by
  have := hF.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have := isSeparated_of_over (A := A) (X := X)
  obtain ⟨ι, _, 𝔘, hUtop, hU⟩ := exists_finite_affineCover X
  obtain ⟨c, hc⟩ := exists_cechK_eq_pow_smul I hF 𝔘 hU q hUtop
  refine ⟨c, fun n => ?_⟩
  rintro _ ⟨z, rfl⟩
  obtain ⟨zČ, rfl⟩ := (cechHLinearEquivH 𝔘 hUtop hU A (idealPow I F (n + c + 1)) q).surjective z
  rw [formalα, ← cechHLinearEquivH_naturality]
  have h2 := cechK_succ_le I 𝔘 q (n + c) (F := F) ⟨zČ, rfl⟩
  rw [hc n] at h2
  have hmem : cechH.linearMap 𝔘 A (idealPowι I F (n + c + 1)) q zČ ∈
      I ^ n • (⊤ : Submodule A (cechH (modulesAb F).obj 𝔘 q)) :=
    Submodule.smul_mono le_rfl le_top h2
  refine Submodule.smul_induction_on hmem (fun a ha y _ => ?_) (fun y y' hy hy' => ?_)
  · rw [map_smul]
    exact Submodule.smul_mem_smul ha trivial
  · rw [map_add (f := _)]
    exact add_mem hy hy'

include hF in
lemma exists_towerComp_formalτQ_eq_zero (q : ℕ) :
    ∃ c, ∀ n, towerComp (E := fun m => formalQ I F q m) (formalτQ I F q) n c = 0 := by
  have := hF.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have := isSeparated_of_over (A := A) (X := X)
  obtain ⟨ι, _, 𝔘, hUtop, hU⟩ := exists_finite_affineCover X
  obtain ⟨c, hc⟩ := exists_transMap_eq_zero I hF 𝔘 hU (q + 1) hUtop
  refine ⟨c, fun n => LinearMap.ext fun y => Subtype.ext ?_⟩
  rw [towerComp_formalτQ_val, LinearMap.zero_apply, ZeroMemClass.coe_zero]
  obtain ⟨x, hx⟩ := y.2
  obtain ⟨yČ, hyČ⟩ :=
    (cechHLinearEquivH 𝔘 hUtop hU A (idealPow I F (n + c + 1)) (q + 1)).surjective y.1
  have hι : cechHMap 𝔘 (modulesAbMap (idealPowι I F (n + c + 1))).hom (q + 1) yČ = 0 := by
    apply (cechHLinearEquivH 𝔘 hUtop hU A F (q + 1)).injective
    rw [map_zero]
    change cechHLinearEquivH 𝔘 hUtop hU A F (q + 1)
      (cechH.linearMap 𝔘 A (idealPowι I F (n + c + 1)) (q + 1) yČ) = 0
    rw [cechHLinearEquivH_naturality, hyČ, ← hx]
    exact H.map_f_δ (shortExact_abSC_quotPow I F (n + c)) rfl x
  rw [← hyČ, ← cechHLinearEquivH_naturality]
  change cechHLinearEquivH 𝔘 hUtop hU A (idealPow I F (n + 1)) (q + 1)
    (cechHMap 𝔘 (modulesAbMap (transMap I F n c)).hom (q + 1) yČ) = 0
  rw [hc n yČ hι, map_zero]

include hF in
theorem formalFunctions_mem_range (q : ℕ) {x : ∀ n, Sheaf.H.{u} (modulesAb (quotPow I F n)) q}
    (hx : x ∈ towerLimit (E := fun m => Sheaf.H.{u} (modulesAb (quotPow I F m)) q)
      (formalτE I F q)) (n : ℕ) : x n ∈ LinearMap.range (formalβ I F q n) := by
  obtain ⟨c, hc⟩ := exists_towerComp_formalτQ_eq_zero I hF q
  exact mem_range_formalβ_of_mem_towerLimit hc hx n

end

end GroundTheory.Arith.SchemeCoh
