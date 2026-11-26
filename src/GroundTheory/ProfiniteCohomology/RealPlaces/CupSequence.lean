module

public import GroundTheory.ProfiniteCohomology.RealPlaces.ConeMap
public import GroundTheory.ProfiniteCohomology.RealPlaces.NormHomotopy
public import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.CompactCupEqCompactCupRight

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.RealPlaces.HomologyMapProdFstProdLeftHomology
section -- merged from GroundTheory.ProfiniteCohomology.RealPlaces.ConeHomotopy
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k : Type u} [CommRing k]

namespace LeibnizPairing

section Prod

variable {M₁ M₂ N₁ N₂ P₁ P₂ N : CochainComplex (ModuleCat.{u} k) ℕ}

noncomputable def prod (μ₁ : LeibnizPairing M₁ N₁ P₁) (μ₂ : LeibnizPairing M₂ N₂ P₂) :
    LeibnizPairing (prodComplex M₁ M₂) (prodComplex N₁ N₂) (prodComplex P₁ P₂) where
  μ {r s n} h := LinearMap.mk₂ k
    (fun (x : M₁.X r × M₂.X r) (y : N₁.X s × N₂.X s) =>
      (show (prodComplex P₁ P₂).X n from (μ₁.μ h x.1 y.1, μ₂.μ h x.2 y.2)))
    (fun _ _ _ => Prod.ext (LinearMap.map_add₂ _ _ _ _) (LinearMap.map_add₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (LinearMap.map_smul₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (map_add _ _ _) (map_add _ _ _))
    (fun _ _ _ => Prod.ext (map_smul _ _ _) (map_smul _ _ _))
  leibniz {r s n} h x y := by
    rw [prodComplex_d_hom_apply, prodComplex_d_hom_apply, prodComplex_d_hom_apply]
    exact Prod.ext (μ₁.leibniz h x.1 y.1) (μ₂.leibniz h x.2 y.2)

noncomputable def prodLeft (μ₁ : LeibnizPairing M₁ N P₁) (μ₂ : LeibnizPairing M₂ N P₂) :
    LeibnizPairing (prodComplex M₁ M₂) N (prodComplex P₁ P₂) where
  μ {r s n} h := LinearMap.mk₂ k
    (fun (x : M₁.X r × M₂.X r) (y : N.X s) =>
      (show (prodComplex P₁ P₂).X n from (μ₁.μ h x.1 y, μ₂.μ h x.2 y)))
    (fun _ _ _ => Prod.ext (LinearMap.map_add₂ _ _ _ _) (LinearMap.map_add₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (LinearMap.map_smul₂ _ _ _ _))
    (fun _ _ _ => Prod.ext (map_add _ _ _) (map_add _ _ _))
    (fun _ _ _ => Prod.ext (map_smul _ _ _) (map_smul _ _ _))
  leibniz {r s n} h x y := by
    rw [prodComplex_d_hom_apply, prodComplex_d_hom_apply]
    exact Prod.ext (μ₁.leibniz h x.1 y) (μ₂.leibniz h x.2 y)

end Prod

section DegZero

variable {E E' : ModuleCat.{u} k} {N : CochainComplex (ModuleCat.{u} k) ℕ}

noncomputable def degZeroμ (β : E →ₗ[k] N.X 0 →ₗ[k] E') :
    ∀ (r s n : ℕ), r + s = n →
      (degZeroComplex E).X r →ₗ[k] N.X s →ₗ[k] (degZeroComplex E').X n
  | 0, 0, 0, _ => β
  | _, _, _, _ => 0

theorem degZeroμ_succ (β : E →ₗ[k] N.X 0 →ₗ[k] E') (r s n : ℕ) (h : r + (s + 1) = n) :
    degZeroμ β r (s + 1) n h = 0 := by
  cases r <;> cases n <;> rfl

noncomputable def degZero (β : E →ₗ[k] N.X 0 →ₗ[k] E') :
    LeibnizPairing (degZeroComplex E) N (degZeroComplex E') where
  μ {r s n} h := degZeroμ β r s n h
  leibniz {r s n} h x y := by
    rw [degZeroComplex_d, degZeroComplex_d, degZeroμ_succ]
    simp

end DegZero

section CoconeHtpy

variable {K L K' L' N N' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'}
  (μL : LeibnizPairing L N' L') (ρ : N ⟶ N') (μK : LeibnizPairing K N K')
  (η : ∀ {r s n : ℕ}, r + s = n → K.X r →ₗ[k] N.X s →ₗ[k] shiftNegOneX L' n)

noncomputable def coconeLeftHtpyμ {r s n : ℕ} (h : r + s = n) :
    (mappingCoconeNat f).X r →ₗ[k] N.X s →ₗ[k] (mappingCoconeNat f').X n :=
  LinearMap.mk₂ k
    (fun (p : K.X r × shiftNegOneX L r) z =>
      ((μK.μ h p.1 z, μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z) :
        K'.X n × shiftNegOneX L' n))
    (fun p q z => Prod.ext (LinearMap.map_add₂ _ _ _ _) (by
      change μL.shiftLeft r s n h (p.2 + q.2) ((ρ.f s).hom z) + η h (p.1 + q.1) z = _
      rw [LinearMap.map_add₂, LinearMap.map_add₂]
      change _ = (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z) +
        (μL.shiftLeft r s n h q.2 ((ρ.f s).hom z) + η h q.1 z)
      abel))
    (fun c p z => Prod.ext (LinearMap.map_smul₂ _ _ _ _) (by
      change μL.shiftLeft r s n h (c • p.2) ((ρ.f s).hom z) + η h (c • p.1) z = _
      rw [LinearMap.map_smul₂, LinearMap.map_smul₂]
      change _ = c • (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z)
      rw [smul_add]))
    (fun p z z' => Prod.ext (map_add _ _ _) (by
      change μL.shiftLeft r s n h p.2 ((ρ.f s).hom (z + z')) + η h p.1 (z + z') = _
      rw [map_add (f := _), map_add (f := _), map_add (f := _)]
      change _ = (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z) +
        (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z') + η h p.1 z')
      abel))
    (fun c p z => Prod.ext (map_smul _ _ _) (by
      change μL.shiftLeft r s n h p.2 ((ρ.f s).hom (c • z)) + η h p.1 (c • z) = _
      rw [map_smul, map_smul, map_smul]
      change _ = c • (μL.shiftLeft r s n h p.2 ((ρ.f s).hom z) + η h p.1 z)
      rw [smul_add]))

noncomputable def coconeLeftHtpy
    (hη : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
      shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) + (shiftNegOneD L' n).hom (η h x z) =
        shiftNegOneSucc L' n (μL.μ h ((f.f r).hom x) ((ρ.f s).hom z)) +
          η (by omega) ((K.d r (r + 1)).hom x) z +
          (-1 : k) ^ r • η (by omega) x ((N.d s (s + 1)).hom z)) :
    LeibnizPairing (mappingCoconeNat f) N (mappingCoconeNat f') where
  μ h := coconeLeftHtpyμ μL ρ μK η h
  leibniz {r s n} h p z := by
    revert p
    intro (p : K.X r × shiftNegOneX L r)
    obtain ⟨x, y⟩ := p
    rw [mappingCoconeNat_d, mappingCoconeNat_d]
    refine Prod.ext (μK.leibniz h x z) ?_
    change shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) +
        (shiftNegOneD L' n).hom (μL.shiftLeft r s n h y ((ρ.f s).hom z) + η h x z) =
      (μL.shiftLeft (r + 1) s (n + 1) (by omega)
          (shiftNegOneSucc L r ((f.f r).hom x) + (shiftNegOneD L r).hom y) ((ρ.f s).hom z) +
        η (by omega) ((K.d r (r + 1)).hom x) z) +
        (-1 : k) ^ r • (μL.shiftLeft r (s + 1) (n + 1) (by omega) y
          ((ρ.f (s + 1)).hom ((N.d s (s + 1)).hom z)) + η (by omega) x ((N.d s (s + 1)).hom z))
    have key := eq_sub_of_add_eq' (hη h x z)
    rw [← hom_apply_hom_apply_eq_of_comp_eq (ρ.comm s (s + 1)) z, map_add (f := _), key,
      shiftLeft_leibniz, LinearMap.map_add₂, shiftLeft_succ, smul_add]
    abel

variable (hη : ∀ {r s n : ℕ} (h : r + s = n) (x : K.X r) (z : N.X s),
  shiftNegOneSucc L' n ((f'.f n).hom (μK.μ h x z)) + (shiftNegOneD L' n).hom (η h x z) =
    shiftNegOneSucc L' n (μL.μ h ((f.f r).hom x) ((ρ.f s).hom z)) +
      η (by omega) ((K.d r (r + 1)).hom x) z +
      (-1 : k) ^ r • η (by omega) x ((N.d s (s + 1)).hom z))

theorem coconeLeftHtpy_homology_homologyδ {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : L.homology r) (z : N.homology s) :
    (coconeLeftHtpy μL ρ μK η hη).homology h' ((mappingCoconeNat.homologyδ f r).hom ξ) z =
      (mappingCoconeNat.homologyδ f' n).hom
        (μL.homology h ξ ((HomologicalComplex.homologyMap ρ s).hom z)) := by
  obtain ⟨c, rfl⟩ := homologyπ_hom_surjective _ r ξ
  obtain ⟨w, rfl⟩ := homologyπ_hom_surjective _ s z
  obtain ⟨c', hc'1, hc'2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f r c
  rw [homologyMap_homologyπ_apply, homology_homologyπ]
  obtain ⟨c'', hc''1, hc''2⟩ := mappingCoconeNat.exists_homologyδ_homologyπ f' n
    (μL.cycles h c ((HomologicalComplex.cyclesMap ρ s).hom w))
  rw [hc'1, hc''1, homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cycles, hc'2, hc''2, iCycles_cycles, iCycles_cyclesMap_apply]
  refine Prod.ext (LinearMap.map_zero₂ _ _) ?_
  change μL.shiftLeft (r + 1) s (n + 1) h' _ _ + η h' 0 _ = _
  rw [LinearMap.map_zero₂, add_zero]
  rfl

end CoconeHtpy

end LeibnizPairing

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)

section Pairing

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Aᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] [∀ w, IsDiscreteRep (Cᵣ w)]
  {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w} {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}


variable (B) in
noncomputable def tateLocalResB :
    cochainsComplex B ⟶ tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom B)
      (fun w => Rep.res (ψ w).toMonoidHom B) :=
  prodLift (localRes φ B _ fun _ => 𝟙 _) (localRes ψ B _ fun _ => 𝟙 _)

variable (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
  (μᵣ : ∀ w, Aᵣ w ⊗ Rep.res (ψ w).toMonoidHom B ⟶ Cᵣ w)

noncomputable def zeroCochainValue : (cochainsComplex B).X 0 →ₗ[k] B where
  toFun z := cochainOf B z (fun i => i.elim0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def tateExtraPairingAt (w : κ) : Aᵣ w →ₗ[k] (cochainsComplex B).X 0 →ₗ[k] Cᵣ w :=
  ((TensorProduct.mk k (Aᵣ w) (Rep.res (ψ w).toMonoidHom B)).compr₂ (μᵣ w).hom.toLinearMap).compl₂
    (zeroCochainValue (B := B))

noncomputable def tateExtraPairing :
    (∀ w, Aᵣ w) →ₗ[k] (cochainsComplex B).X 0 →ₗ[k] (∀ w, Cᵣ w) :=
  LinearMap.mk₂ k (fun e z w => tateExtraPairingAt ψ μᵣ w (e w) z)
    (fun _ _ _ => funext fun w => LinearMap.map_add₂ (tateExtraPairingAt ψ μᵣ w) _ _ _)
    (fun _ _ _ => funext fun w => LinearMap.map_smul₂ (tateExtraPairingAt ψ μᵣ w) _ _ _)
    (fun _ _ _ => funext fun w => map_add (tateExtraPairingAt ψ μᵣ w _) _ _)
    (fun _ _ _ => funext fun w => map_smul (tateExtraPairingAt ψ μᵣ w _) _ _)


noncomputable def tateGlobalCup :
    LeibnizPairing (tateGlobalComplex A Aᵣ) (cochainsComplex B) (tateGlobalComplex C Cᵣ) :=
  LeibnizPairing.prodLeft (cupLeibniz μ) (LeibnizPairing.degZero (tateExtraPairing ψ μᵣ))

noncomputable def tateLocalCup :
    LeibnizPairing (tateLocalComplex Aᵥ Aᵣ)
      (tateLocalComplex (fun v => Rep.res (φ v).toMonoidHom B) (fun w => Rep.res (ψ w).toMonoidHom B))
      (tateLocalComplex Cᵥ Cᵣ) :=
  LeibnizPairing.prod (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v))
    (LeibnizPairing.pi fun w => cupLeibniz (μᵣ w))

noncomputable def tateNormHomotopy {s m : ℕ} (h : s = m + 1) :
    (∀ w, Aᵣ w) →ₗ[k] (cochainsComplex B).X s →ₗ[k] (∀ w, (cochainsComplex (Cᵣ w)).X m) :=
  LinearMap.mk₂ k (fun e z w => normHomotopy (μᵣ w) h (e w)
      (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f s).hom z w))
    (fun _ _ _ => funext fun w => LinearMap.map_add₂ (normHomotopy (μᵣ w) h) _ _ _)
    (fun _ _ _ => funext fun w => LinearMap.map_smul₂ (normHomotopy (μᵣ w) h) _ _ _)
    (fun e _ _ => funext fun w => by
      rw [map_add (f := _)]
      exact map_add (normHomotopy (μᵣ w) h (e w)) _ _)
    (fun c e _ => funext fun w => by
      rw [map_smul]
      exact map_smul (normHomotopy (μᵣ w) h (e w)) c _)

noncomputable def tateCupHomotopyL {s m : ℕ} (h : s = m + 1) :
    (∀ w, Aᵣ w) →ₗ[k] (cochainsComplex B).X s →ₗ[k] (tateLocalComplex Cᵥ Cᵣ).X m :=
  -(tateNormHomotopy ψ μᵣ h).compr₂ (LinearMap.inr k
    ((piComplex fun v => cochainsComplex (Cᵥ v)).X m) ((piComplex fun w => cochainsComplex (Cᵣ w)).X m))

omit [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateCupHomotopyL_apply {s m : ℕ} (h : s = m + 1) (e : ∀ w, Aᵣ w)
    (z : (cochainsComplex B).X s) :
    tateCupHomotopyL ψ μᵣ (Cᵥ := Cᵥ) h e z = ((0, -tateNormHomotopy ψ μᵣ h e z) :
        (piComplex fun v => cochainsComplex (Cᵥ v)).X m ×
          (piComplex fun w => cochainsComplex (Cᵣ w)).X m) :=
  Prod.ext neg_zero rfl

noncomputable def tateCupHomotopy : ∀ (r s n : ℕ), r + s = n →
    (tateGlobalComplex A Aᵣ).X r →ₗ[k] (cochainsComplex B).X s →ₗ[k]
      shiftNegOneX (tateLocalComplex Cᵥ Cᵣ) n
  | 0, _, n + 1, h => (tateCupHomotopyL ψ μᵣ (Cᵥ := Cᵥ) (by omega : _ = n + 1)).comp
      (LinearMap.snd k _ ((degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).X 0))
  | _, _, _, _ => 0

end Pairing

section Spec

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Aᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] [∀ w, IsDiscreteRep (Cᵣ w)]
  {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w} {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}
  (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
  (μᵣ : ∀ w, Aᵣ w ⊗ Rep.res (ψ w).toMonoidHom B ⟶ Cᵣ w)
  (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
    resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μᵥ v)
  (hμr : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (ar w) (𝟙 _) ≫ μᵣ w)

theorem normCochains_f_succ_apply' (n : ℕ) (e : (degZeroComplex (ModuleCat.of k (∀ w, Aᵣ w))).X (n + 1)) :
    ((normCochains Aᵣ).f (n + 1)).hom e = 0 :=
  rfl

omit [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateCupHomotopy_succ_left (r s n : ℕ) (h : r + 1 + s = n) :
    tateCupHomotopy ψ μᵣ (Cᵥ := Cᵥ) (A := A) (r + 1) s n h = 0 :=
  rfl

omit [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateCupHomotopy_zero_zero (s : ℕ) (h : 0 + s = 0) :
    tateCupHomotopy ψ μᵣ (Cᵥ := Cᵥ) (A := A) 0 s 0 h = 0 :=
  rfl

omit [∀ w, IsDiscreteRep (Aᵣ w)] in
theorem tateCupHomotopy_zero_succ (s n : ℕ) (h : 0 + s = n + 1) (hs : s = n + 1)
    (x : (tateGlobalComplex A Aᵣ).X 0) (z : (cochainsComplex B).X s) :
    tateCupHomotopy ψ μᵣ (Cᵥ := Cᵥ) 0 s (n + 1) h x z =
      tateCupHomotopyL ψ μᵣ (Cᵥ := Cᵥ) hs x.2 z :=
  rfl


include hμ hμr in
theorem tateCupHomotopy_spec {r s n : ℕ} (h : r + s = n) (x : (tateGlobalComplex A Aᵣ).X r)
    (z : (cochainsComplex B).X s) :
    shiftNegOneSucc (tateLocalComplex Cᵥ Cᵣ) n (((tateCompactRes φ ψ C Cᵥ c Cᵣ cr).f n).hom
        ((tateGlobalCup ψ μ μᵣ).μ h x z)) +
        (shiftNegOneD (tateLocalComplex Cᵥ Cᵣ) n).hom (tateCupHomotopy ψ μᵣ r s n h x z) =
      shiftNegOneSucc (tateLocalComplex Cᵥ Cᵣ) n ((tateLocalCup φ ψ μᵥ μᵣ).μ h
          (((tateCompactRes φ ψ A Aᵥ a Aᵣ ar).f r).hom x) (((tateLocalResB φ ψ B).f s).hom z)) +
        tateCupHomotopy ψ μᵣ (r + 1) s (n + 1) (by omega)
          (((tateGlobalComplex A Aᵣ).d r (r + 1)).hom x) z +
        (-1 : k) ^ r • tateCupHomotopy ψ μᵣ r (s + 1) (n + 1) (by omega) x
          (((cochainsComplex B).d s (s + 1)).hom z) := by
  rcases r with _ | r
  · rcases s with _ | t
    ·
      obtain rfl : n = 0 := by omega
      rw [tateCupHomotopy_zero_zero, tateCupHomotopy_succ_left,
        tateCupHomotopy_zero_succ ψ μᵣ 1 0 _ rfl, LinearMap.zero_apply, LinearMap.zero_apply,
        LinearMap.zero_apply, LinearMap.zero_apply, map_zero, add_zero, add_zero]
      rw [pow_zero]
      erw [one_smul]
      rw [shiftNegOneSucc_apply, shiftNegOneSucc_apply]
      erw [tateCupHomotopyL_apply]
      refine Prod.ext ?_ ?_
      · change ((localRes φ C Cᵥ c).f 0).hom (cupPairingCochains μ h x.1 z) =
          (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)).μ h (((localRes φ A Aᵥ a).f 0).hom x.1)
            (((localRes φ B _ fun _ => 𝟙 _).f 0).hom z) + 0
        rw [add_zero]
        exact localRes_cupPairingCochains φ μ μᵥ hμ h x.1 z
      · refine funext fun w => ?_
        change ((localRes ψ C Cᵣ cr).f 0).hom (cupPairingCochains μ h x.1 z) w +
            zeroCochain (Cᵣ w) ((Cᵣ w).ρ.norm (tateExtraPairing ψ μᵣ (show ∀ w, Aᵣ w from x.2) z w)) =
          cupPairingCochains (μᵣ w) h (((localRes ψ A Aᵣ ar).f 0).hom x.1 w +
              zeroCochain (Aᵣ w) ((Aᵣ w).ρ.norm ((show ∀ w, Aᵣ w from x.2) w)))
            (((localRes ψ B _ fun _ => 𝟙 _).f 0).hom z w) +
          -normHomotopy (μᵣ w) rfl ((show ∀ w, Aᵣ w from x.2) w)
            (((localRes ψ B _ fun _ => 𝟙 _).f (0 + 1)).hom (((cochainsComplex B).d 0 (0 + 1)).hom z) w)
        have hres := congrFun (localRes_cupPairingCochains ψ μ μᵣ hμr h x.1 z) w
        have hd : ((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f (0 + 1)).hom
            (((cochainsComplex B).d 0 (0 + 1)).hom z) w =
            ((cochainsComplex (Rep.res (ψ w).toMonoidHom B)).d 0 (0 + 1)).hom
              (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f 0).hom z w) := by
          rw [hom_f_d_apply]
          exact piComplex_d_hom_apply _ 0 _ w
        have hz0 : cochainOf (Rep.res (ψ w).toMonoidHom B)
            (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f 0).hom z w)
            (fun i => i.elim0) = cochainOf B z (fun i => i.elim0) :=
          congrArg (cochainOf B z) (Subsingleton.elim _ _)
        rw [hres, LinearMap.map_add₂, hd, normHomotopy_d_zero, hz0]
        change _ + zeroCochain (Cᵣ w) ((Cᵣ w).ρ.norm ((μᵣ w).hom _)) = _
        abel
    ·
      obtain rfl : n = t + 1 := by omega
      rw [tateCupHomotopy_zero_succ ψ μᵣ (t + 1) t _ rfl, tateCupHomotopy_succ_left,
        tateCupHomotopy_zero_succ ψ μᵣ (t + 1 + 1) (t + 1) _ rfl, LinearMap.zero_apply,
        LinearMap.zero_apply, add_zero]
      rw [pow_zero]
      erw [one_smul]
      rw [shiftNegOneSucc_apply, shiftNegOneSucc_apply, shiftNegOneD_succ_apply]
      erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply, prodComplex_d_hom_apply]
      refine Prod.ext ?_ ?_
      · change ((localRes φ C Cᵥ c).f (t + 1)).hom (cupPairingCochains μ h x.1 z) +
            -((piComplex fun v => cochainsComplex (Cᵥ v)).d t (t + 1)).hom 0 =
          (LeibnizPairing.pi fun v => cupLeibniz (μᵥ v)).μ h (((localRes φ A Aᵥ a).f 0).hom x.1)
            (((localRes φ B _ fun _ => 𝟙 _).f (t + 1)).hom z) + 0
        rw [map_zero, neg_zero, add_zero, add_zero]
        exact localRes_cupPairingCochains φ μ μᵥ hμ h x.1 z
      · refine funext fun w => ?_
        change ((localRes ψ C Cᵣ cr).f (t + 1)).hom (cupPairingCochains μ h x.1 z) w +
            ((normCochains Cᵣ).f (t + 1)).hom
              (LeibnizPairing.degZeroμ (tateExtraPairing ψ μᵣ) 0 (t + 1) (t + 1) h x.2 z) w +
            -(((piComplex fun w => cochainsComplex (Cᵣ w)).d t (t + 1)).hom
              (-tateNormHomotopy ψ μᵣ (rfl : t + 1 = t + 1) x.2 z) w) = _
        erw [piComplex_d_hom_apply]
        change ((localRes ψ C Cᵣ cr).f (t + 1)).hom (cupPairingCochains μ h x.1 z) w +
            ((normCochains Cᵣ).f (t + 1)).hom
              (LeibnizPairing.degZeroμ (tateExtraPairing ψ μᵣ) 0 (t + 1) (t + 1) h x.2 z) w +
            -((cochainsComplex (Cᵣ w)).d t (t + 1)).hom
              (-normHomotopy (μᵣ w) rfl ((show ∀ w, Aᵣ w from x.2) w)
                (((localRes ψ B _ fun _ => 𝟙 _).f (t + 1)).hom z w)) =
          cupPairingCochains (μᵣ w) h (((localRes ψ A Aᵣ ar).f 0).hom x.1 w +
              zeroCochain (Aᵣ w) ((Aᵣ w).ρ.norm ((show ∀ w, Aᵣ w from x.2) w)))
            (((localRes ψ B _ fun _ => 𝟙 _).f (t + 1)).hom z w) +
          -normHomotopy (μᵣ w) rfl ((show ∀ w, Aᵣ w from x.2) w)
            (((localRes ψ B _ fun _ => 𝟙 _).f (t + 1 + 1)).hom
              (((cochainsComplex B).d (t + 1) (t + 1 + 1)).hom z) w)
        have hres : ((localRes ψ C Cᵣ cr).f (t + 1)).hom (cupPairingCochains μ h x.1 z) w =
            cupPairingCochains (μᵣ w) h (((localRes ψ A Aᵣ ar).f 0).hom x.1 w)
              (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f (t + 1)).hom z w) :=
          congrFun (localRes_cupPairingCochains ψ μ μᵣ hμr h x.1 z) w
        have hd : ((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f
            (t + 1 + 1)).hom (((cochainsComplex B).d (t + 1) (t + 1 + 1)).hom z) w =
            ((cochainsComplex (Rep.res (ψ w).toMonoidHom B)).d (t + 1) (t + 1 + 1)).hom
              (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f
                (t + 1)).hom z w) := by
          rw [hom_f_d_apply]
          exact piComplex_d_hom_apply _ (t + 1) _ w
        have key := d_normHomotopy_add (μᵣ w) ((show ∀ w, Aᵣ w from x.2) w)
          (((localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) fun _ => 𝟙 _).f (t + 1)).hom z w)
        rw [hres, LinearMap.map_add₂, hd, map_neg, neg_neg, ← key]
        change _ + (0 : (cochainsComplex (Cᵣ w)).X (t + 1)) + _ = _
        abel
  ·
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
    rw [tateCupHomotopy_succ_left, tateCupHomotopy_succ_left, tateCupHomotopy_succ_left,
      LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply,
      LinearMap.zero_apply, LinearMap.zero_apply, map_zero, add_zero, add_zero, smul_zero, add_zero,
      shiftNegOneSucc_apply, shiftNegOneSucc_apply]
    refine Prod.ext ?_ ?_
    · exact localRes_cupPairingCochains φ μ μᵥ hμ h x.1 z
    · change ((localRes ψ C Cᵣ cr).f (m + 1)).hom (cupPairingCochains μ h x.1 z) +
          ((normCochains Cᵣ).f (m + 1)).hom
            (LeibnizPairing.degZeroμ (tateExtraPairing ψ μᵣ) (r + 1) s (m + 1) h x.2 z) =
        (LeibnizPairing.pi fun w => cupLeibniz (μᵣ w)).μ h
          (((localRes ψ A Aᵣ ar).f (r + 1)).hom x.1 + ((normCochains Aᵣ).f (r + 1)).hom x.2)
          (((localRes ψ B _ fun _ => 𝟙 _).f s).hom z)
      rw [normCochains_f_succ_apply', normCochains_f_succ_apply', add_zero, add_zero]
      exact localRes_cupPairingCochains ψ μ μᵣ hμr h x.1 z

end Spec

section ProdHomology

variable {M₁ M₂ N₁ N₂ P₁ P₂ N : CochainComplex (ModuleCat.{u} k) ℕ}

theorem LeibnizPairing.homologyMap_prodFst_prod_homology (μ₁ : LeibnizPairing M₁ N₁ P₁)
    (μ₂ : LeibnizPairing M₂ N₂ P₂) {r s n : ℕ} (h : r + s = n)
    (x : (prodComplex M₁ M₂).homology r) (y : (prodComplex N₁ N₂).homology s) :
    (HomologicalComplex.homologyMap (prodFst P₁ P₂) n).hom ((LeibnizPairing.prod μ₁ μ₂).homology h x y) =
      μ₁.homology h ((HomologicalComplex.homologyMap (prodFst M₁ M₂) r).hom x)
        ((HomologicalComplex.homologyMap (prodFst N₁ N₂) s).hom y) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, LeibnizPairing.homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles,
    iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
  rfl

theorem LeibnizPairing.homologyMap_prodSnd_prod_homology (μ₁ : LeibnizPairing M₁ N₁ P₁)
    (μ₂ : LeibnizPairing M₂ N₂ P₂) {r s n : ℕ} (h : r + s = n)
    (x : (prodComplex M₁ M₂).homology r) (y : (prodComplex N₁ N₂).homology s) :
    (HomologicalComplex.homologyMap (prodSnd P₁ P₂) n).hom ((LeibnizPairing.prod μ₁ μ₂).homology h x y) =
      μ₂.homology h ((HomologicalComplex.homologyMap (prodSnd M₁ M₂) r).hom x)
        ((HomologicalComplex.homologyMap (prodSnd N₁ N₂) s).hom y) := by
  obtain ⟨x, rfl⟩ := homologyπ_hom_surjective _ r x
  obtain ⟨y, rfl⟩ := homologyπ_hom_surjective _ s y
  rw [LeibnizPairing.homology_homologyπ, homologyMap_homologyπ_apply, homologyMap_homologyπ_apply,
    homologyMap_homologyπ_apply, LeibnizPairing.homology_homologyπ]
  congr 1
  apply iCycles_hom_injective
  rw [iCycles_cyclesMap_apply, LeibnizPairing.iCycles_cycles, LeibnizPairing.iCycles_cycles,
    iCycles_cyclesMap_apply, iCycles_cyclesMap_apply]
  rfl

end ProdHomology

section Cup

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {Aᵥ Cᵥ : ∀ v, Rep.{u} k (H v)} [∀ v, IsDiscreteRep (Aᵥ v)] [∀ v, IsDiscreteRep (Cᵥ v)]
  {a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v} {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Aᵣ Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Aᵣ w)] [∀ w, IsDiscreteRep (Cᵣ w)]
  {ar : ∀ w, Rep.res (ψ w).toMonoidHom A ⟶ Aᵣ w} {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}
  (μ : A ⊗ B ⟶ C) (μᵥ : ∀ v, Aᵥ v ⊗ Rep.res (φ v).toMonoidHom B ⟶ Cᵥ v)
  (μᵣ : ∀ w, Aᵣ w ⊗ Rep.res (ψ w).toMonoidHom B ⟶ Cᵣ w)
  (hμ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ ≫ c v =
    resTensorHom (φ v).toMonoidHom (a v) (𝟙 _) ≫ μᵥ v)
  (hμr : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (ar w) (𝟙 _) ≫ μᵣ w)

noncomputable def tateCompactCupLeibniz :
    LeibnizPairing (tateCompactCochains φ ψ A Aᵥ a Aᵣ ar) (cochainsComplex B)
      (tateCompactCochains φ ψ C Cᵥ c Cᵣ cr) :=
  LeibnizPairing.coconeLeftHtpy (tateLocalCup φ ψ μᵥ μᵣ) (tateLocalResB φ ψ B)
    (tateGlobalCup ψ μ μᵣ) (fun {r s n} h => tateCupHomotopy ψ μᵣ r s n h)
    (fun h x z => tateCupHomotopy_spec φ ψ μ μᵥ μᵣ hμ hμr h x z)

noncomputable def tateCompactCup {r s n : ℕ} (h : r + s = n) :
    tateCompactCohomology φ ψ A Aᵥ a Aᵣ ar r →ₗ[k] cohomology B s →ₗ[k]
      tateCompactCohomology φ ψ C Cᵥ c Cᵣ cr n :=
  (tateCompactCupLeibniz φ ψ μ μᵥ μᵣ hμ hμr).homology h

theorem tateCompactCup_tateLocalToCompact {r s n : ℕ} (h : r + s = n) (h' : r + 1 + s = n + 1)
    (ξ : (∀ v, cohomology (Aᵥ v) r) × (∀ w, cohomology (Aᵣ w) r)) (z : cohomology B s) :
    tateCompactCup φ ψ μ μᵥ μᵣ hμ hμr h' ((tateLocalToCompact φ ψ A Aᵥ a Aᵣ ar r).hom ξ) z =
      (tateLocalToCompact φ ψ C Cᵥ c Cᵣ cr n).hom
        ((fun v => cupPairing (μᵥ v) h (ξ.1 v)
            ((cohomologyMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v)) (𝟙 _) s).hom z)),
          (fun w => cupPairing (μᵣ w) h (ξ.2 w)
            ((cohomologyMapAlong (ψ w).toMonoidHom (continuous_toMonoidHom (ψ w)) (𝟙 _) s).hom z))) := by
  change (tateCompactCupLeibniz φ ψ μ μᵥ μᵣ hμ hμr).homology h'
      ((mappingCoconeNat.homologyδ (tateCompactRes φ ψ A Aᵥ a Aᵣ ar) r).hom
        ((tateLocalCohomologyIso Aᵥ Aᵣ r).inv.hom ξ)) z =
    (mappingCoconeNat.homologyδ (tateCompactRes φ ψ C Cᵥ c Cᵣ cr) n).hom
      ((tateLocalCohomologyIso Cᵥ Cᵣ n).inv.hom _)
  refine (LeibnizPairing.coconeLeftHtpy_homology_homologyδ _ _ _ _ _ h h' _ z).trans ?_
  congr 1
  apply (ModuleCat.mono_iff_injective (tateLocalCohomologyIso Cᵥ Cᵣ n).hom).1 inferInstance
  rw [hom_apply_hom_apply_of_comp_eq (tateLocalCohomologyIso Cᵥ Cᵣ n).inv_hom_id]
  have hξ := hom_apply_hom_apply_of_comp_eq (tateLocalCohomologyIso Aᵥ Aᵣ r).inv_hom_id
    (show ModuleCat.of k ((∀ v, cohomology (Aᵥ v) r) × (∀ w, cohomology (Aᵣ w) r)) from ξ)
  rw [tateLocalCohomologyIso_hom_apply] at hξ
  rw [tateLocalCohomologyIso_hom_apply]
  have ρ1 : tateLocalResB φ ψ B ≫ prodFst _ _ =
      localRes φ B (fun v => Rep.res (φ v).toMonoidHom B) (fun _ => 𝟙 _) := prodLift_prodFst _ _
  have ρ2 : tateLocalResB φ ψ B ≫ prodSnd _ _ =
      localRes ψ B (fun w => Rep.res (ψ w).toMonoidHom B) (fun _ => 𝟙 _) := prodLift_prodSnd _ _
  refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
  · rw [tateLocalCup, LeibnizPairing.homologyMap_prodFst_prod_homology]
    refine (LeibnizPairing.piHomologyIso_hom_pi_homology (fun v => cupLeibniz (μᵥ v)) h _ _ v).trans ?_
    refine (cupLeibniz_homology (μᵥ v) h _ _).trans ?_
    refine congrArg₂ (fun p q => cupPairing (μᵥ v) h p q) (congrFun (congrArg Prod.fst hξ) v) ?_
    rw [hom_apply_hom_apply_of_comp_eq
      (HomologicalComplex.homologyMap_comp (tateLocalResB φ ψ B) (prodFst _ _) s).symm z, ρ1]
    exact congrFun (ConcreteCategory.congr_hom (homologyMap_piLift_piHomologyIso_hom _
      (fun v => cochainsMapAlong (φ v).toMonoidHom (continuous_toMonoidHom (φ v))
        (𝟙 (Rep.res (φ v).toMonoidHom B))) s) z) v
  · rw [tateLocalCup, LeibnizPairing.homologyMap_prodSnd_prod_homology]
    refine (LeibnizPairing.piHomologyIso_hom_pi_homology (fun w => cupLeibniz (μᵣ w)) h _ _ w).trans ?_
    refine (cupLeibniz_homology (μᵣ w) h _ _).trans ?_
    refine congrArg₂ (fun p q => cupPairing (μᵣ w) h p q) (congrFun (congrArg Prod.snd hξ) w) ?_
    rw [hom_apply_hom_apply_of_comp_eq
      (HomologicalComplex.homologyMap_comp (tateLocalResB φ ψ B) (prodSnd _ _) s).symm z, ρ2]
    exact congrFun (ConcreteCategory.congr_hom (homologyMap_piLift_piHomologyIso_hom _
      (fun w => cochainsMapAlong (ψ w).toMonoidHom (continuous_toMonoidHom (ψ w))
        (𝟙 (Rep.res (ψ w).toMonoidHom B))) s) z) w

end Cup

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits MonoidalCategory GroundTheory.GroupCoh

universe u

section Compat

variable {k F : Type u} [CommRing k] [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
  [Fintype F]

theorem normHomotopy_compat_left {X₁ X₂ Y₁ Y₂ Z : Rep.{u} k F} [IsDiscreteRep Y₁] [IsDiscreteRep Y₂]
    [IsDiscreteRep Z] (μ₁ : X₁ ⊗ Y₁ ⟶ Z) (μ₂ : X₂ ⊗ Y₂ ⟶ Z) (f : X₁ ⟶ X₂) (g : Y₂ ⟶ Y₁)
    (hc : (f ⊗ₘ 𝟙 Y₂) ≫ μ₂ = (𝟙 X₁ ⊗ₘ g) ≫ μ₁) {s m : ℕ} (h : s = m + 1) (e : X₁)
    (y : (cochainsComplex Y₂).X s) :
    normHomotopy μ₂ h (f.hom e) y = normHomotopy μ₁ h e (((cochainsMap g).f s).hom y) := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_normHomotopy, cochainOf_normHomotopy]
  refine Finset.sum_congr rfl fun a _ => congrArg (Z.ρ a) ?_
  exact congrArg (fun φ : X₁ ⊗ Y₂ ⟶ Z => φ.hom ((e ⊗ₜ[k] cochainOf Y₂ y (consTuple h a⁻¹ σ) :
    (X₁ ⊗ Y₂ : Rep k F)))) hc

theorem normHomotopy_compat_right {X₂ X₃ Y₁ Y₂ Z : Rep.{u} k F} [IsDiscreteRep Y₁]
    [IsDiscreteRep Y₂] [IsDiscreteRep Z] (μ₂ : X₂ ⊗ Y₂ ⟶ Z) (μ₃ : X₃ ⊗ Y₁ ⟶ Z) (f : Y₁ ⟶ Y₂)
    (g : X₂ ⟶ X₃) (hc : (𝟙 X₂ ⊗ₘ f) ≫ μ₂ = (g ⊗ₘ 𝟙 Y₁) ≫ μ₃) {s m : ℕ} (h : s = m + 1) (e : X₂)
    (y : (cochainsComplex Y₁).X s) :
    normHomotopy μ₂ h e (((cochainsMap f).f s).hom y) = normHomotopy μ₃ h (g.hom e) y := by
  apply cochainOf_injective
  funext σ
  rw [cochainOf_normHomotopy, cochainOf_normHomotopy]
  refine Finset.sum_congr rfl fun a _ => congrArg (Z.ρ a) ?_
  exact congrArg (fun φ : X₂ ⊗ Y₁ ⟶ Z => φ.hom ((e ⊗ₜ[k] cochainOf Y₁ y (consTuple h a⁻¹ σ) :
    (X₂ ⊗ Y₁ : Rep k F)))) hc

end Compat

section TwoSequences

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  {κ : Type u} {F : κ → Type u} [∀ w, Group (F w)] [∀ w, TopologicalSpace (F w)]
  [∀ w, IsTopologicalGroup (F w)] [∀ w, Fintype (F w)] (ψ : ∀ w, F w →ₜ* G)
  {SA : ShortComplex (Rep.{u} k G)} [IsDiscreteRep SA.X₁] [IsDiscreteRep SA.X₂]
  [IsDiscreteRep SA.X₃] {SAᵥ : ∀ v, ShortComplex (Rep.{u} k (H v))}
  [∀ v, IsDiscreteRep (SAᵥ v).X₁] [∀ v, IsDiscreteRep (SAᵥ v).X₂] [∀ v, IsDiscreteRep (SAᵥ v).X₃]
  (sA : ∀ v, SA.map (Rep.resFunctor (φ v).toMonoidHom) ⟶ SAᵥ v)
  {SAᵣ : ∀ w, ShortComplex (Rep.{u} k (F w))}
  [∀ w, IsDiscreteRep (SAᵣ w).X₁] [∀ w, IsDiscreteRep (SAᵣ w).X₂] [∀ w, IsDiscreteRep (SAᵣ w).X₃]
  (sAr : ∀ w, SA.map (Rep.resFunctor (ψ w).toMonoidHom) ⟶ SAᵣ w)
  {SB : ShortComplex (Rep.{u} k G)} [IsDiscreteRep SB.X₁] [IsDiscreteRep SB.X₂]
  [IsDiscreteRep SB.X₃] {C : Rep.{u} k G} [IsDiscreteRep C] {Cᵥ : ∀ v, Rep.{u} k (H v)}
  [∀ v, IsDiscreteRep (Cᵥ v)] {c : ∀ v, Rep.res (φ v).toMonoidHom C ⟶ Cᵥ v}
  {Cᵣ : ∀ w, Rep.{u} k (F w)} [∀ w, IsDiscreteRep (Cᵣ w)]
  {cr : ∀ w, Rep.res (ψ w).toMonoidHom C ⟶ Cᵣ w}
  (μ₁ : SA.X₁ ⊗ SB.X₃ ⟶ C) (μ₂ : SA.X₂ ⊗ SB.X₂ ⟶ C) (μ₃ : SA.X₃ ⊗ SB.X₁ ⟶ C)
  (μ₁ᵥ : ∀ v, (SAᵥ v).X₁ ⊗ Rep.res (φ v).toMonoidHom SB.X₃ ⟶ Cᵥ v)
  (μ₂ᵥ : ∀ v, (SAᵥ v).X₂ ⊗ Rep.res (φ v).toMonoidHom SB.X₂ ⟶ Cᵥ v)
  (μ₃ᵥ : ∀ v, (SAᵥ v).X₃ ⊗ Rep.res (φ v).toMonoidHom SB.X₁ ⟶ Cᵥ v)
  (μ₁ᵣ : ∀ w, (SAᵣ w).X₁ ⊗ Rep.res (ψ w).toMonoidHom SB.X₃ ⟶ Cᵣ w)
  (μ₂ᵣ : ∀ w, (SAᵣ w).X₂ ⊗ Rep.res (ψ w).toMonoidHom SB.X₂ ⟶ Cᵣ w)
  (μ₃ᵣ : ∀ w, (SAᵣ w).X₃ ⊗ Rep.res (ψ w).toMonoidHom SB.X₁ ⟶ Cᵣ w)
  (hμ₁ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₁ ≫ c v =
    resTensorHom (φ v).toMonoidHom (sA v).τ₁ (𝟙 _) ≫ μ₁ᵥ v)
  (hμ₂ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₂ ≫ c v =
    resTensorHom (φ v).toMonoidHom (sA v).τ₂ (𝟙 _) ≫ μ₂ᵥ v)
  (hμ₃ : ∀ v, (Rep.resFunctor (φ v).toMonoidHom).map μ₃ ≫ c v =
    resTensorHom (φ v).toMonoidHom (sA v).τ₃ (𝟙 _) ≫ μ₃ᵥ v)
  (hμ₁ᵣ : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ₁ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (sAr w).τ₁ (𝟙 _) ≫ μ₁ᵣ w)
  (hμ₂ᵣ : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ₂ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (sAr w).τ₂ (𝟙 _) ≫ μ₂ᵣ w)
  (hμ₃ᵣ : ∀ w, (Rep.resFunctor (ψ w).toMonoidHom).map μ₃ ≫ cr w =
    resTensorHom (ψ w).toMonoidHom (sAr w).τ₃ (𝟙 _) ≫ μ₃ᵣ w)


include hμ₂ hμ₂ᵣ in
theorem tateCompactCup_tateCompactδ_add_tateCompactCup_δ
    (h₁₂ : (SA.f ⊗ₘ 𝟙 SB.X₂) ≫ μ₂ = (𝟙 SA.X₁ ⊗ₘ SB.g) ≫ μ₁)
    (h₂₃ : (𝟙 SA.X₂ ⊗ₘ SB.f) ≫ μ₂ = (SA.g ⊗ₘ 𝟙 SB.X₁) ≫ μ₃)
    (h₁₂ᵥ : ∀ v, ((SAᵥ v).f ⊗ₘ 𝟙 _) ≫ μ₂ᵥ v =
      (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v).toMonoidHom).map SB.g) ≫ μ₁ᵥ v)
    (h₂₃ᵥ : ∀ v, (𝟙 _ ⊗ₘ (Rep.resFunctor (φ v).toMonoidHom).map SB.f) ≫ μ₂ᵥ v =
      ((SAᵥ v).g ⊗ₘ 𝟙 _) ≫ μ₃ᵥ v)
    (h₁₂ᵣ : ∀ w, ((SAᵣ w).f ⊗ₘ 𝟙 _) ≫ μ₂ᵣ w =
      (𝟙 _ ⊗ₘ (Rep.resFunctor (ψ w).toMonoidHom).map SB.g) ≫ μ₁ᵣ w)
    (h₂₃ᵣ : ∀ w, (𝟙 _ ⊗ₘ (Rep.resFunctor (ψ w).toMonoidHom).map SB.f) ≫ μ₂ᵣ w =
      ((SAᵣ w).g ⊗ₘ 𝟙 _) ≫ μ₃ᵣ w)
    (hSA : SA.ShortExact) (hSAᵥ : ∀ v, (SAᵥ v).ShortExact) (hSAᵣ : ∀ w, (SAᵣ w).ShortExact)
    (hSB : SB.ShortExact) {r s n : ℕ} (h₁ : r + 1 + s = n + 1) (h₃ : r + (s + 1) = n + 1)
    (x : tateCompactCohomology φ ψ SA.X₃ (fun v => (SAᵥ v).X₃) (fun v => (sA v).τ₃)
      (fun w => (SAᵣ w).X₃) (fun w => (sAr w).τ₃) r)
    (y : cohomology SB.X₃ s) :
    tateCompactCup φ ψ μ₁ μ₁ᵥ μ₁ᵣ hμ₁ hμ₁ᵣ h₁ ((tateCompactδ φ ψ sA sAr hSA hSAᵥ hSAᵣ r).hom x) y +
      (-1 : k) ^ r • tateCompactCup φ ψ μ₃ μ₃ᵥ μ₃ᵣ hμ₃ hμ₃ᵣ h₃ x ((δ hSB s (s + 1) rfl).hom y) = 0 := by
  refine LeibnizPairing.homology_δ_add_homology_δ
    (SM := mappingCoconeNat.mapShortComplex (tateResShortComplex φ ψ SA SAᵥ sA SAᵣ sAr))
    (SN := cochainsShortComplex SB) (tateCompactCupLeibniz φ ψ μ₂ μ₂ᵥ μ₂ᵣ hμ₂ hμ₂ᵣ)
    (tateCompactCupLeibniz φ ψ μ₁ μ₁ᵥ μ₁ᵣ hμ₁ hμ₁ᵣ) (tateCompactCupLeibniz φ ψ μ₃ μ₃ᵥ μ₃ᵣ hμ₃ hμ₃ᵣ)
    ?_ ?_ (tateCompactCochains_shortExact φ ψ sA sAr hSA hSAᵥ hSAᵣ)
    (cochainsShortComplex_shortExact hSB) h₁ h₃ x y
  · intro r s n h p y
    revert p
    intro (p : (tateGlobalComplex SA.X₁ fun w => (SAᵣ w).X₁).X r ×
      shiftNegOneX (tateLocalComplex (fun v => (SAᵥ v).X₁) fun w => (SAᵣ w).X₁) r)
    obtain ⟨⟨x0, e⟩, b⟩ := p
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · apply cochainOf_injective
      funext σ
      exact cupCochain_pairing_left μ₁ μ₂ h₁₂ h (cochainOf _ x0) (cochainOf _ y) σ
    · rcases r with _ | r
      · rcases s with _ | s
        · obtain rfl : n = 0 := by omega
          funext w
          exact congrArg (fun φ' => Rep.Hom.hom φ' ((e w ⊗ₜ[k] cochainOf SB.X₂ y (fun i => i.elim0) :
            ((SAᵣ w).X₁ ⊗ Rep.res (ψ w).toMonoidHom SB.X₂ : Rep k (F w))))) (h₁₂ᵣ w)
        · rfl
      · rfl
    · rcases r with _ | r
      · rcases s with _ | t
        · obtain rfl : n = 0 := by omega
          exact Subsingleton.elim (α := PUnit) _ _
        · obtain rfl : n = t + 1 := by omega
          change (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₂ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1)
                ((piRepHom fun w => (SAᵣ w).f).hom e) y =
            (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₁ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1) e
                (((cochainsMap SB.g).f (t + 1)).hom y)
          erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
          refine congrArg _ (Prod.ext rfl (funext fun w => congrArg Neg.neg ?_))
          exact normHomotopy_compat_left (μ₁ᵣ w) (μ₂ᵣ w) (SAᵣ w).f _ (h₁₂ᵣ w) rfl (e w) _
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
        change (tateLocalCup φ ψ μ₂ᵥ μ₂ᵣ).μ (show r + s = m by omega)
              ((tateLocalMap (fun v => (SAᵥ v).f) fun w => (SAᵣ w).f).f r |>.hom b)
              (((tateLocalResB φ ψ SB.X₂).f s).hom y) + 0 =
            (tateLocalCup φ ψ μ₁ᵥ μ₁ᵣ).μ (show r + s = m by omega) b
              (((tateLocalResB φ ψ SB.X₃).f s).hom (((cochainsMap SB.g).f s).hom y)) + 0
        rw [add_zero, add_zero]
        refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_left (S := SAᵥ v)
            (T := SB.map (Rep.resFunctor (φ v).toMonoidHom)) (μ₁ᵥ v) (μ₂ᵥ v) (h₁₂ᵥ v)
            (show r + s = m by omega) (cochainOf _ (b.1 v))
            (fun τ => cochainOf SB.X₂ y (⇑(φ v).toMonoidHom ∘ τ)) σ
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_left (S := SAᵣ w)
            (T := SB.map (Rep.resFunctor (ψ w).toMonoidHom)) (μ₁ᵣ w) (μ₂ᵣ w) (h₁₂ᵣ w)
            (show r + s = m by omega) (cochainOf _ (b.2 w))
            (fun τ => cochainOf SB.X₂ y (⇑(ψ w).toMonoidHom ∘ τ)) σ
  · intro r s n h p y
    revert p
    intro (p : (tateGlobalComplex SA.X₂ fun w => (SAᵣ w).X₂).X r ×
      shiftNegOneX (tateLocalComplex (fun v => (SAᵥ v).X₂) fun w => (SAᵣ w).X₂) r)
    obtain ⟨⟨x0, e⟩, b⟩ := p
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · apply cochainOf_injective
      funext σ
      exact cupCochain_pairing_right μ₂ μ₃ h₂₃ h (cochainOf _ x0) (cochainOf _ y) σ
    · rcases r with _ | r
      · rcases s with _ | s
        · obtain rfl : n = 0 := by omega
          funext w
          exact congrArg (fun φ' => Rep.Hom.hom φ' ((e w ⊗ₜ[k] cochainOf SB.X₁ y (fun i => i.elim0) :
            ((SAᵣ w).X₂ ⊗ Rep.res (ψ w).toMonoidHom SB.X₁ : Rep k (F w))))) (h₂₃ᵣ w)
        · rfl
      · rfl
    · rcases r with _ | r
      · rcases s with _ | t
        · obtain rfl : n = 0 := by omega
          exact Subsingleton.elim (α := PUnit) _ _
        · obtain rfl : n = t + 1 := by omega
          change (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₂ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1) e
                (((cochainsMap SB.f).f (t + 1)).hom y) =
            (0 : (tateLocalComplex Cᵥ Cᵣ).X t) +
              tateCupHomotopyL ψ μ₃ᵣ (Cᵥ := Cᵥ) (rfl : t + 1 = t + 1)
                ((piRepHom fun w => (SAᵣ w).g).hom e) y
          erw [tateCupHomotopyL_apply, tateCupHomotopyL_apply]
          refine congrArg _ (Prod.ext rfl (funext fun w => congrArg Neg.neg ?_))
          exact normHomotopy_compat_right (μ₂ᵣ w) (μ₃ᵣ w)
            ((Rep.resFunctor (ψ w).toMonoidHom).map SB.f) (SAᵣ w).g (h₂₃ᵣ w) rfl (e w)
            (((localRes ψ SB.X₁ (fun w => Rep.res (ψ w).toMonoidHom SB.X₁) fun _ => 𝟙 _).f
              (t + 1)).hom y w)
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨r + s, by omega⟩
        change (tateLocalCup φ ψ μ₂ᵥ μ₂ᵣ).μ (show r + s = m by omega) b
              (((tateLocalResB φ ψ SB.X₂).f s).hom (((cochainsMap SB.f).f s).hom y)) + 0 =
            (tateLocalCup φ ψ μ₃ᵥ μ₃ᵣ).μ (show r + s = m by omega)
              ((tateLocalMap (fun v => (SAᵥ v).g) fun w => (SAᵣ w).g).f r |>.hom b)
              (((tateLocalResB φ ψ SB.X₁).f s).hom y) + 0
        rw [add_zero, add_zero]
        refine Prod.ext (funext fun v => ?_) (funext fun w => ?_)
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_right (S := SAᵥ v)
            (T := SB.map (Rep.resFunctor (φ v).toMonoidHom)) (μ₂ᵥ v) (μ₃ᵥ v) (h₂₃ᵥ v)
            (show r + s = m by omega) (cochainOf _ (b.1 v))
            (fun τ => cochainOf SB.X₁ y (⇑(φ v).toMonoidHom ∘ τ)) σ
        · apply cochainOf_injective
          funext σ
          exact cupCochain_pairing_right (S := SAᵣ w)
            (T := SB.map (Rep.resFunctor (ψ w).toMonoidHom)) (μ₂ᵣ w) (μ₃ᵣ w) (h₂₃ᵣ w)
            (show r + s = m by omega) (cochainOf _ (b.2 w))
            (fun τ => cochainOf SB.X₁ y (⇑(ψ w).toMonoidHom ∘ τ)) σ

end TwoSequences

end GroundTheory.ProfCoh
