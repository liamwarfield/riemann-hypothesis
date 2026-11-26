module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

theorem invT_val {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : (invT n R g).val = (g⁻¹).valᵀ := rfl

@[simp] theorem invT_invT' {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : invT n R (invT n R g) = g := by
  apply Units.ext
  rw [invT_val, ← map_inv, invT_val, inv_inv, transpose_transpose]

theorem invT_mem_Sim {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {i : B →+* A} {n : ℕ} {p : GL (Fin n) A × Bˣ}
    (h : p ∈ Sim σ i n) : (invT n A p.1, p.2⁻¹) ∈ Sim σ i n := by
  have h1 := mem_Sim.1 h
  have h2 : p.1.valᵀ * p.1.val.map σ = i p.2 • (1 : Matrix (Fin n) (Fin n) A) := by
    have := congrArg transpose h1
    rwa [transpose_mul, transpose_transpose, transpose_smul, transpose_one] at this
  have h3 : i (p.2⁻¹ : Bˣ) * i p.2 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have h4 : (p.1⁻¹).valᵀ * p.1.valᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  have h5 : (p.1⁻¹).val.map σ * p.1.val.map σ = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h6 : p.1.val.map σ = i p.2 • (p.1⁻¹).valᵀ := by
    rw [← Matrix.one_mul (p.1.val.map σ), ← h4, Matrix.mul_assoc, h2, Matrix.mul_smul, Matrix.mul_one]
  refine mem_Sim.2 ?_
  show (((p.1⁻¹).valᵀ).map σ)ᵀ * (p.1⁻¹).valᵀ = i (p.2⁻¹ : Bˣ) • 1
  rw [transpose_map, transpose_transpose, ← h5, h6, Matrix.mul_smul, smul_smul, h3, one_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def th : GUf E n →* GUf E n :=
  (((invT n (Af E)).prodMap invMonoidHom).comp (GUf E n).subtype).codRestrict _ fun g => invT_mem_Sim g.2

def th0 : Gam0 E n →* Gam0 E n :=
  (((invT n E).prodMap invMonoidHom).comp (Gam0 E n).subtype).codRestrict _ fun g =>
    ⟨invT_mem_Sim g.2.1, (Units.posSubgroup ℚ).inv_mem g.2.2⟩

@[simp] theorem sim_th (g : GUf E n) : sim (th g) = (sim g)⁻¹ := rfl

@[simp] theorem comp_th (w : Plc E) (g : GUf E n) : comp w (th g) = invT n _ (comp w g) := GlobalTheory.SplitPts.invT_map _ _

@[simp] theorem th_th (g : GUf E n) : th (th g) = g := Subtype.ext (Prod.ext (invT_invT' _) (inv_inv _))

theorem th_rat (γ : Gam0 E n) : th (rat γ) = rat (th0 γ) :=
  Subtype.ext (Prod.ext (GlobalTheory.SplitPts.invT_map _ _).symm (map_inv (Units.map (algebraMap ℚ AfQ).toMonoidHom) _).symm)

theorem guf_ext {g g' : GUf E n} (h1 : sim g = sim g') (h2 : ∀ w, comp w g = comp w g') : g = g' :=
  Subtype.ext (Prod.ext (Units.ext (GlobalTheory.SplitPts.matAf_ext fun w => congrArg Units.val (h2 w))) h1)

theorem invT_mem_KGL {w : Plc E} {y : GLw n w} (h : y ∈ KGL w (n := n)) : invT n _ y ∈ KGL w (n := n) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨invT n _ z, GlobalTheory.SplitPts.invT_map _ z⟩

def levT (Kw : ∀ w : Plc E, Subgroup (GLw n w)) : ∀ w : Plc E, Subgroup (GLw n w) := fun w => (Kw w).comap (invT n _)

theorem th_mem_lev {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} {k : GUf E n} :
    th k ∈ lev S Kw ↔ k ∈ lev S (levT Kw) := by
  simp only [mem_lev, sim_th, comp_th, inv_mem_iff, levT, Subgroup.mem_comap]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₃_congr fun w _ _ => ⟨fun h => ?_, invT_mem_KGL⟩
  simpa using invT_mem_KGL h

def ThLoc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  (∀ (w : Plc E) (hw : IsSplitAt w) (y : GLw n w), th (loc hw y) = loc hw (invT n _ y)) ∧
    (0 < n → ∀ (x : E) (w : Plc E) (z : GUf E n), IsCen x w z → th z = z⁻¹)

end UpperTheory.Gal.CertificateRingHomMap

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocComm
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.LocalCommutativity

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem rel (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := mem_Sim.1 k.2
  have h2 := congrArg (RingHom.mapMatrix (pLoc E u)) h
  rw [map_mul] at h2
  refine h2.trans ?_
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

private theorem gu_ext {a b : GUf E n} (hs : sim a = sim b) (hc : ∀ u, comp u a = comp u b) : a = b := by
  refine Subtype.ext (Prod.ext (Units.ext (GlobalTheory.SplitPts.matAf_ext fun u => ?_)) hs)
  exact congrArg Units.val (hc u)

private theorem comm_scalar {R : Type} [CommRing R] (M X : Matrix (Fin n) (Fin n) R)
    (ho : ∀ i j, i ≠ j → M i j = 0) (hd : ∀ i j, M i i = M j j) : M * X = X * M := by
  have e : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, ho i j hij]
  ext i j
  rw [e, Matrix.diagonal_mul, Matrix.mul_diagonal, hd i j, mul_comm]

end UpperTheory.Gal.CertificateRingHomMap.LocalCommutativity

open UpperTheory.Gal.CertificateRingHomMap.LocalCommutativity in
theorem UpperTheory.Gal.CertificateRingHomMap.pLocComm_of :
    UpperTheory.Gal.CertificateRingHomMap.LocComm := by
  intro E _ _ _ n w hw
  obtain ⟨hne, hund, hover⟩ := GlobalTheory.SplitPts.over_split hw
  have hcc : cj (cj w) = w := GlobalTheory.SplitPts.conjSrc_conjSrc_cm w
  have hap : ∀ u, GlobalTheory.Cong.Apart u w ↔ u ≠ w ∧ u ≠ cj w := by
    intro u
    constructor
    · intro h
      exact ⟨fun e => h (by rw [e]), fun e => h (by rw [e]; exact hund)⟩
    · rintro ⟨h1, h2⟩ h
      rcases hover u h with e | e
      · exact h1 e
      · exact h2 e
  refine ⟨?_, hap, hne, ⟨w, hne.symm, hund.symm⟩, hcc, ?_⟩
  · intro k hk y
    refine gu_ext (by rw [map_mul, map_mul]; exact mul_comm _ _) fun u => ?_
    rw [map_mul, map_mul]
    by_cases h1 : u = w
    · subst h1
      rw [hk, one_mul, mul_one]
    by_cases h2 : u = cj w
    · subst h2
      have r := rel k w
      rw [hk, Units.val_one, Matrix.mul_one] at r
      have r' := congrArg Matrix.transpose r
      rw [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at r'
      have hent : ∀ i j, conjLoc (GlobalTheory.SplitPts.conjE E) w ((comp (cj w) k).val i j) = _ :=
        fun i j => congrFun (congrFun r' i) j
      have hinj := (conjLoc (GlobalTheory.SplitPts.conjE E) w).injective
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul]
      refine comm_scalar _ _ (fun i j hij => hinj ?_) (fun i j => hinj ?_)
      · rw [hent i j, map_zero]; simp [hij]
      · rw [hent i i, hent j j]; simp
    · rw [comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩), mul_one, one_mul]
  · unfold locU
    rw [hund]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.POfUBij
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pOfUBij_of :
    UpperTheory.Gal.CertificateRingHomMap.OfUBij := by
  intro E _ _ _ n
  refine ⟨fun u v h => ?_, fun g hg => ?_⟩
  · have h1 : GeneralLinearGroup.map (pFin E) u.1.1 = GeneralLinearGroup.map (pFin E) v.1.1 :=
      congrArg (fun x : GUf E n => mat x) h
    have h2 := congrArg (finGL E n) h1
    rw [GlobalTheory.DefU.ClassFin.finGL_pFin, GlobalTheory.DefU.ClassFin.finGL_pFin] at h2
    exact Subtype.ext (Subtype.ext h2)
  · have hs : g.1.2 = 1 := hg
    have h : Formalism.UG.cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (mat g).val * (mat g).val = 1 :=
      (mem_Sim.1 g.2).trans (by rw [hs]; simp)
    refine ⟨⟨⟨finGL E n (mat g), GlobalTheory.DefU.ClassFin.finGL_mem_UA _ h⟩, pInf_finGL _⟩, ?_⟩
    exact Subtype.ext (Prod.ext (pFin_finGL _) hs.symm)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLocMem
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pLocMem_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocMem := by
  intro hIC hLC E _ _ _ n S Kw w hw hcw y
  obtain ⟨-, hap, -, -, hcc, -⟩ := hLC E n w hw
  have hsim : sim (loc hw y) ∈ ZU := by
    rw [sim_loc]; exact ZU.one_mem
  have hone : ∀ u, u ≠ w → u ≠ cj w → comp u (loc hw y) = 1 := fun u h1 h2 =>
    comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩) y
  refine ⟨fun hwS hy => mem_lev.2 ⟨hsim, ?_, ?_⟩, fun hwS hy => mem_lev.2 ⟨hsim, ?_, ?_⟩⟩
  · intro u hu
    by_cases h1 : u = w
    · subst h1
      rw [comp_loc]; exact hy
    · have h2 : u ≠ cj w := fun h => hcw (h ▸ hu)
      rw [hone u h1 h2]; exact (Kw u).one_mem
  · intro u hu hcu
    have h1 : u ≠ w := fun h => hu (h ▸ hwS)
    have h2 : u ≠ cj w := fun h => hcu (by rw [h, hcc]; exact hwS)
    rw [hone u h1 h2]; exact (GlobalTheory.LFun.KGL u (n := n)).one_mem
  · intro u hu
    have h1 : u ≠ w := fun h => hwS (h ▸ hu)
    have h2 : u ≠ cj w := fun h => hcw (h ▸ hu)
    rw [hone u h1 h2]; exact (Kw u).one_mem
  · intro u hu hcu
    by_cases h1 : u = w
    · subst h1
      rw [comp_loc]; exact hy
    · by_cases h2 : u = cj w
      · subst h2
        exact hIC E n (loc hw y) w hsim (by rw [comp_loc]; exact hy)
      · rw [hone u h1 h2]; exact (GlobalTheory.LFun.KGL u (n := n)).one_mem
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntSim
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

open GroundTheory.Global.AdeleBaseChange in
private theorem rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ)) • (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := mem_Sim.1 k.2
  have h2 := congrArg (RingHom.mapMatrix (pLoc E u)) h
  rw [map_mul] at h2
  refine Eq.trans ?_ (h2.trans ?_)
  · congr 1
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [RingHom.mapMatrix_apply, sim, Matrix.one_apply]
    · simp [RingHom.mapMatrix_apply, sim, Matrix.one_apply, hij]

open GroundTheory.Global.AdeleBaseChange in
private theorem val_le {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 0 < n) (k : GUf E n)
    (hk : ∀ w, comp w k ∈ GlobalTheory.LFun.KGL w (n := n)) (u : Plc E) :
    Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) ≤ 1 := by
  have h := congrFun (congrFun (rel k u) ⟨0, hn⟩) ⟨0, hn⟩
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  rw [← h]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul, Matrix.transpose_apply, Matrix.map_apply, (conjLoc_spec _ u).2.2]
  exact mul_le_one' (((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val _ _).1 (hk _)).1 _ _)
    (((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val _ _).1 (hk _)).1 _ _)

open GroundTheory.Global.AdeleBaseChange in
theorem UpperTheory.Gal.CertificateRingHomMap.pIntSim_of :
    UpperTheory.Gal.CertificateRingHomMap.IntSim := by
  intro E _ _ _ n hn k hk v
  obtain ⟨P, hPm, hPo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  let u : Plc E := ⟨P, hPm.isPrime, hP0⟩
  have hu : below ℚ u = v := (below_eq_iff u v).2 hPo
  subst hu
  have h1 := val_le hn k hk u
  have h2 := val_le hn k⁻¹ (fun w => by rw [map_inv]; exact inv_mem (hk w)) u
  have hmul : pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ)) * pLoc E u (finiteAdeleMap ℚ E (sim k⁻¹ : AfQˣ)) = 1 := by
    rw [← map_mul, ← map_mul, map_inv, Units.mul_inv, map_one, map_one]
  have h3 : Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : _) = Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) *
          Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k⁻¹ : AfQˣ))) := by
            rw [← map_mul, hmul, map_one]
      _ ≤ Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  have h4 : Valued.v (GroundTheory.Global.SemiLocal.completionMap (below ℚ u) u (((sim k : AfQˣ) : AfQ) (below ℚ u))) = 1 := h3
  rw [GroundTheory.Global.SemiLocal.valued_completionMap] at h4
  exact (pow_eq_one_iff.1 h4).resolve_right (Ideal.ramificationIdx_pos (R := 𝓞 ℚ) u.asIdeal).ne'
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PSphType
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pSphType_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.SphType := by
  intro hIC hLC E _ _ _ n π w hw
  refine ⟨?_, ?_⟩
  · rintro ⟨B, σ, ⟨-, f, hf0, hfV, hf⟩, hB⟩
    have hker : LinearMap.ker f = ⊥ := by
      refine (((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => ?_)).resolve_right
        fun h => hf0 (LinearMap.ker_eq_top.1 h)
      rw [LinearMap.mem_ker] at hv ⊢
      have h1 := hf ⟨(locF hw g).1, locF_mem hw g⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, cLoc_locF] at h1
      rw [h1, hv, map_zero]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    have hfix := GlobalTheory.LGrp.mem_fixed.1 hv
    have hφ0 : f v ≠ 0 := fun h => hv0 (LinearMap.ker_eq_bot.1 hker (h.trans (map_zero f).symm))
    have key : ∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n x (f v) = f v := by
      intro x hx hk
      have h1 := hf ⟨x, hx⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h1
      rw [← h1, hfix _ hk]
    obtain ⟨-, -, -, -, hcc, hloc⟩ := hLC E n w hw
    refine ⟨⟨f v, hfV v, hφ0, fun x hx h => ?_⟩, ⟨f v, hfV v, hφ0, fun x hx h => ?_⟩⟩
    · simpa using key x hx h
    · rw [hloc] at hx
      have h2 := hIC E n (ofU ⟨x, (Subgroup.mem_inf.1 hx).1⟩) (cj w) (by rw [sim_ofU]; exact one_mem _)
        (by rw [comp_ofU]; exact h)
      rw [hcc, comp_ofU] at h2
      simpa using key x hx h2
  · rintro J χ ⟨φ, hφ, h0, hact⟩
    have hlev := (π.isAut.aut φ hφ).level
    have hc : Continuous fun k : J => (locF hw k.1 : finU (E := E) (n := n)) := by
      have h1 : Continuous fun k : GLw n w => (locF hw k : finU (E := E) (n := n)) :=
        Continuous.subtype_mk (continuous_subtype_val.comp (locE hw).symm.continuous) _
      exact h1.comp continuous_subtype_val
    have hset : {k : J | χ k = 1} = (fun k : J => (locF hw k.1 : finU (E := E) (n := n))) ⁻¹' {k : finU (E := E) (n := n) | RU E n k φ = φ} := by
      ext k
      have hk : cLoc w (locF hw k.1).1 ∈ J := by rw [cLoc_locF]; exact k.2
      have h1 := hact (locF hw k.1).1 (locF_mem hw k.1) hk
      have h2 : (⟨cLoc w (locF hw k.1).1, hk⟩ : J) = k := Subtype.ext (cLoc_locF hw k.1)
      rw [h2] at h1
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [h1]
      constructor
      · intro h; rw [h]; simp
      · intro h
        have h3 : ((χ k : ℂˣ) : ℂ) = 1 := smul_left_injective ℂ h0 (by simpa using h)
        exact Units.ext h3
    rw [hset]
    exact hlev.preimage hc
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntCompact
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem isCompact_ZU : IsCompact (ZU : Set AfQˣ) := by
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles ℚ
  have hB' : IsCompact (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) : Set AfQᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hO
  have e : (ZU : Set AfQˣ) = Units.embedProduct _ ⁻¹'
      ((GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) ×ˢ
        (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ))) := by
    ext s
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, MulOpposite.unop_op,
      GroundTheory.Global.mem_integralFiniteAdeles]
    constructor
    · intro h
      have h2 := (ZU.inv_mem h)
      exact ⟨fun v => (h v).le, fun v => (h2 v).le⟩
    · rintro ⟨h1, h2⟩ v
      have h3 : Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) = 1 := by
        rw [← map_mul]
        show Valued.v (((s : AfQ) * (↑s⁻¹ : AfQ)) v) = 1
        rw [Units.mul_inv]; exact map_one _
      refine le_antisymm (h1 v) ?_
      calc (1 : _) = Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) := h3.symm
        _ ≤ Valued.v ((s : AfQ) v) * 1 := mul_le_mul_right (h2 v) _
        _ = _ := mul_one _
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hO.prod hB')

private theorem isClosed_GUf (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    IsClosed (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) := by
  have hl : Continuous fun p : GL (Fin n) (Af E) × AfQˣ =>
      (p.1.val.map (conjFin (GlobalTheory.SplitPts.conjE E)))ᵀ * p.1.val :=
    ((Units.continuous_val.comp continuous_fst).matrix_map (continuous_conjFin _)).matrix_transpose.matrix_mul
      (Units.continuous_val.comp continuous_fst)
  have hr : Continuous fun p : GL (Fin n) (Af E) × AfQˣ =>
      GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ) • (1 : Matrix (Fin n) (Fin n) (Af E)) :=
    Continuous.smul (f := fun p : GL (Fin n) (Af E) × AfQˣ => GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ))
      (g := fun _ => (1 : Matrix (Fin n) (Fin n) (Af E)))
      (GroundTheory.Global.AdeleBaseChange.continuous_finiteAdeleMap.comp (Units.continuous_val.comp continuous_snd))
      continuous_const
  exact isClosed_eq hl hr

theorem UpperTheory.Gal.CertificateRingHomMap.pIntCompact_of :
    UpperTheory.Gal.CertificateRingHomMap.IntCompact := by
  intro E _ _ _ n
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have e : Subtype.val '' (lev (E := E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n)) =
      (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) ∩ ((GlobalTheory.EulerTw.Kglob E n : Set _) ×ˢ (ZU : Set AfQˣ)) := by
    ext p
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨h1, -, h3⟩ := mem_lev.1 hk
      exact ⟨k.2, GlobalTheory.EulerTwRestr.mem_Kglob.2 fun w => h3 w (by simp) (by simp), h1⟩
    · rintro ⟨hp, h1, h2⟩
      refine ⟨⟨p, hp⟩, mem_lev.2 ⟨h2, by simp, fun w _ _ => GlobalTheory.EulerTwRestr.mem_Kglob.1 h1 w⟩, rfl⟩
  rw [e]
  exact ((GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)).prod isCompact_ZU).inter_left (isClosed_GUf E n)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCentralEig2Of
open Module

private theorem exists_common_eigenvector_of_commute_of_invariant {E ι : Type} [AddCommGroup E] [Module ℂ E]
    (T : ι → E →ₗ[ℂ] E) (hT : ∀ i j, T i ∘ₗ T j = T j ∘ₗ T i) :
    ∀ n : ℕ, ∀ W : Submodule ℂ E, finrank ℂ W = n → FiniteDimensional ℂ W → W ≠ ⊥ →
      (∀ i, ∀ x ∈ W, T i x ∈ W) → ∃ x ∈ W, x ≠ 0 ∧ ∀ i, ∃ c : ℂ, T i x = c • x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hfin hne hW
  by_cases hs : ∀ i, ∃ c : ℂ, ∀ x ∈ W, T i x = c • x
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨x, hx, hx0, fun i => (hs i).imp fun c hc => hc x hx⟩
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((T i).restrict (fun x hx => hW i x hx))
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    set W' : Submodule ℂ E := W ⊓ LinearMap.ker (T i - μ • LinearMap.id) with hW'
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ T i x = μ • x := by
      intro x
      simp [hW', sub_eq_zero]
    have hle : W' ≤ W := inf_le_left
    have hlt : W' < W := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      obtain ⟨x, hx, hne'⟩ := hi μ
      exact hne' ((hmem x).1 (by rw [heq]; exact hx)).2
    haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hle
    have hlt' : finrank ℂ W' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hne' : W' ≠ ⊥ := by
      intro hbot
      have hv0 : (v : E) ∈ W' := (hmem _).2 ⟨v.2, by
        have := hv.apply_eq_smul
        simpa using congrArg Subtype.val this⟩
      rw [hbot, Submodule.mem_bot] at hv0
      exact hv.2 (Subtype.ext hv0)
    have hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W' := by
      intro j x hx
      rw [hmem] at hx ⊢
      refine ⟨hW j x hx.1, ?_⟩
      have h1 := LinearMap.congr_fun (hT i j) x
      simp only [LinearMap.comp_apply] at h1
      rw [h1, hx.2, map_smul]
    obtain ⟨x, hx, hx0, hc⟩ := ih _ hlt' W' rfl inferInstance hne' hW'inv
    exact ⟨x, hle hx, hx0, hc⟩

theorem UpperTheory.Gal.CertificateRingHomMap.pCentralEig2_of :
    UpperTheory.Gal.CertificateRingHomMap.CentralEig2 := by
  intro Γ H Z V _ _ _ _ _ ι K ξ ζ hζ M hfin hM hne hinv
  let T : Z → (H → V) →ₗ[ℂ] (H → V) := fun z =>
    { toFun := fun Φ g => Φ (g * ζ z), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hT : ∀ a b, T a ∘ₗ T b = T b ∘ₗ T a := by
    intro a b
    refine LinearMap.ext fun Φ => funext fun g => ?_
    show Φ (g * ζ a * ζ b) = Φ (g * ζ b * ζ a)
    rw [mul_assoc, mul_assoc, hζ a (ζ b)]
  obtain ⟨Φ, hΦM, hΦ0, hc⟩ :=
    exists_common_eigenvector_of_commute_of_invariant T hT _ M rfl hfin hne (fun z Φ hΦ => hinv Φ hΦ z)
  choose c hc using hc
  have hcg : ∀ z g, Φ (g * ζ z) = c z • Φ g := fun z g => congrFun (hc z) g
  obtain ⟨g0, hg0⟩ := Function.ne_iff.mp hΦ0
  have hscal : ∀ a b : ℂ, a • Φ g0 = b • Φ g0 → a = b := fun a b h =>
    smul_left_injective ℂ hg0 h
  have hF : (∀ (γ : Γ) (g : H), Φ (ι γ * g) = ξ γ (Φ g)) ∧ ∀ k ∈ K, ∀ g : H, Φ (g * k) = Φ g :=
    hM hΦM
  have h1 : c 1 = 1 := by
    apply hscal
    rw [← hcg 1 g0, map_one, mul_one, one_smul]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    apply hscal
    rw [← hcg (a * b) g0, map_mul, ← mul_assoc, hcg b, hcg a, smul_smul, mul_comm]
  let χ : Z →* ℂ := { toFun := c, map_one' := h1, map_mul' := hmul }
  refine ⟨Φ, hΦM, hΦ0, χ.toHomUnits, ?_, ?_, ?_⟩
  · intro z g
    exact hcg z g
  · intro z hz
    apply Units.ext
    show c z = 1
    apply hscal
    rw [← hcg z g0, hF.2 _ hz g0, one_smul]
  · intro z γ a hzγ hξ
    show c z = a
    apply hscal
    rw [← hcg z g0, ← hξ (Φ g0), ← hF.1 γ g0, ← hzγ, hζ z g0]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PHeckePres
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep
open GlobalTheory.LFun (KGL heckeVec)
open GlobalTheory.Cong (Apart)
open GlobalTheory.LKDef.HeckeTraceForms (forms)
open Formalism.UG (Tj Ov IsUnifV)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem hecke_eq_sum {G : Type} [Group G] (K : Subgroup G) (h : G → ℂ) (h01 : ∀ g, h g ≠ 0 → h g = 1)
    (hfin : {q : G ⧸ K | h q.out ≠ 0}.Finite) : ∃ R : Finset G,
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V),
        heckeVec ρ K h x = ∑ g ∈ R, ρ g x := by
  refine ⟨hfin.toFinset.image Quotient.out, ?_⟩
  intro V _ _ ρ x
  rw [Finset.sum_image (fun a _ b _ e => Quotient.out_injective e)]
  have hsupp : (Function.support fun q : G ⧸ K => h q.out • ρ q.out x) ⊆ hfin.toFinset := by
    intro q hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    exact hq (by simp [h0])
  have hsum : heckeVec ρ K h x = ∑ q ∈ hfin.toFinset, h q.out • ρ q.out x :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hsum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [h01 _ ((Set.Finite.mem_toFinset hfin).1 hq), one_smul]

private theorem tj_one {L : Type} [Field L] {n : ℕ} {O : Subring L} {ϖ : L} {j : ℕ} (g : GL (Fin n) L)
    (hg : Tj ℂ n O ϖ j g ≠ 0) : Tj ℂ n O ϖ j g = 1 := by
  unfold Tj at hg ⊢
  exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero hg) _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem sum_mem_forms (hC : LocComm) (hM : LocMem) {w : Plc E} (hw : IsSplitAt w) {h : GLw n w → ℂ}
    (hh : h ∈ Formalism.UG.Hecke ℂ (KGL w (n := n))) {R : Finset (GLw n w)}
    (hR : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw n w) V) (v : V),
      heckeVec ρ (KGL w (n := n)) h v = ∑ g ∈ R, ρ g v)
    {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} (hS : w ∉ S) (hcS : cj w ∉ S)
    {V : Type} [AddCommGroup V] [Module ℂ V] {ξ : Representation ℂ (Gam0 E n) V} {Φ : GUf E n → V}
    (hΦ : Φ ∈ forms rat (lev S Kw) ξ) :
    (fun g => ∑ y ∈ R, Φ (g * loc hw y)) ∈ forms rat (lev S Kw) ξ := by
  have hloc : ∀ y ∈ KGL w (n := n), loc hw y ∈ lev S Kw := fun y hy => (hM E n S Kw w hw hcS y).2 hS hy
  let ρ : Representation ℂ (GLw n w) (GUf E n → V) := (rightReg ℂ (GUf E n) V).comp (loc hw)
  have hρ : ∀ y (f : GUf E n → V) g, ρ y f g = f (g * loc hw y) := fun _ _ _ => rfl
  have hfix : Φ ∈ fixed ρ (KGL w (n := n)) := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    funext g
    rw [hρ]
    exact hΦ.2 _ (hloc k hk) g
  have hΨ := GlobalTheory.LFun.SatCompare.heckeVec_mem_fixed (Formalism.UG.Final.GLintComm E w n) hh hfix
  rw [hR] at hΨ
  have hΨ' := GlobalTheory.LGrp.mem_fixed.1 hΨ
  have hev : ∀ g, (∑ y ∈ R, ρ y Φ) g = ∑ y ∈ R, Φ (g * loc hw y) := fun g => by
    rw [Finset.sum_apply]
    rfl
  refine ⟨fun γ g => ?_, fun k hk g => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, mul_assoc]
      exact Finset.sum_congr rfl fun y _ => hΦ.1 γ _
  · have hx : comp w k ∈ KGL w (n := n) := (mem_lev.1 hk).2.2 w hS hcS
    set x := comp w k with hxdef
    set k' := (loc hw x)⁻¹ * k with hk'def
    have hk'm : k' ∈ lev S Kw := (lev S Kw).mul_mem ((lev S Kw).inv_mem (hloc x hx)) hk
    have hk'1 : comp w k' = 1 := by
      rw [hk'def, map_mul, map_inv, comp_loc, ← hxdef, inv_mul_cancel]
    have hcomm := (hC E n w hw).1 k' hk'1
    have hkk : k = loc hw x * k' := by rw [hk'def, mul_inv_cancel_left]
    have e1 : ∀ y, Φ (g * k * loc hw y) = Φ (g * loc hw x * loc hw y) := fun y => by
      calc Φ (g * k * loc hw y) = Φ (g * loc hw x * loc hw y * k') := by
            rw [hkk, mul_assoc g, mul_assoc _ k', hcomm y]; simp only [mul_assoc]
        _ = _ := hΦ.2 _ hk'm _
    have e2 := congrFun (hΨ' x hx) g
    rw [hρ, hev, hev] at e2
    show ∑ y ∈ R, Φ (g * k * loc hw y) = ∑ y ∈ R, Φ (g * loc hw y)
    rw [← e2]
    exact Finset.sum_congr rfl fun y _ => e1 y

theorem pHeckePres_of (hC : LocComm) (hM : LocMem) : HeckePres := by
  intro E _ _ _ n w hw ϖ hϖ i
  have hh := GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ i
  obtain ⟨R, hR⟩ := hecke_eq_sum (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ i) (fun g hg => tj_one g hg)
    (Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w n) hh.2)
  exact ⟨R, hR, fun S Kw hS hcS V _ _ ξ Φ hΦ => sum_mem_forms hC hM hw hh hR hS hcS hΦ⟩

end UpperTheory.Gal.CertificateRingHomMap

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PNbhdU
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.PNbhdU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private noncomputable def th {w : Plc E} (hw : IsSplitAt w) : GLw n w →* GLw n (cj w) :=
  (cLoc (cj w)).comp ((finU (E := E) (n := n)).subtype.comp (locF hw))

private theorem continuous_th {w : Plc E} (hw : IsSplitAt w) : Continuous (th (n := n) hw) :=
  (GlobalTheory.BCT.GlobLev.continuous_cLoc (cj w)).comp
    ((continuous_subtype_val (p := (· ∈ locU n w))).comp (locE hw).symm.continuous)

private theorem cLoc_cj_eq {w : Plc E} (hw : IsSplitAt w) (u : finU (E := E) (n := n)) :
    cLoc (cj w) u.1 = th hw (cLoc w u.1) :=
  GlobalTheory.LocInj.cLoc_conj_eq w u.1 (locF hw (cLoc w u.1)).1 (cLoc_locF hw _).symm

private theorem cj_cj (w : Plc E) : cj (cj w) = w := GlobalTheory.SplitPts.conjSrc_conjSrc_cm w

private theorem exists_lt (α : Type) : ∃ lt : α → α → Prop, (∀ a b, a ≠ b → lt a b ∨ lt b a) ∧ ∀ a b, lt a b → ¬ lt b a := by
  refine ⟨WellOrderingRel, ?_, fun _ _ h => asymm h⟩
  intro a b h
  rcases trichotomous_of (WellOrderingRel : α → α → Prop) a b with hab | heq | hba
  · exact Or.inl hab
  · exact (h heq).elim
  · exact Or.inr hba

private def Top (lt : Plc E → Plc E → Prop) (Up : Plc E → Prop) (w₀ w : Plc E) : Prop :=
  Up w ∧ (Up (cj w) → w = w₀ ∨ (cj w ≠ w₀ ∧ lt w (cj w)))

private theorem top_or {lt : Plc E → Plc E → Prop} (h1 : ∀ a b, a ≠ b → lt a b ∨ lt b a) {Up : Plc E → Prop} (w₀ : Plc E)
    {w : Plc E} (hne : cj w ≠ w) (hup : Up w ∨ Up (cj w)) : Top lt Up w₀ w ∨ Top lt Up w₀ (cj w) := by
  by_cases ha : Up w
  · by_cases hb : Up (cj w)
    · by_cases e : w = w₀
      · exact Or.inl ⟨ha, fun _ => Or.inl e⟩
      · by_cases e' : cj w = w₀
        · exact Or.inr ⟨hb, fun _ => Or.inl e'⟩
        · rcases h1 w (cj w) hne.symm with h | h
          · exact Or.inl ⟨ha, fun _ => Or.inr ⟨e', h⟩⟩
          · exact Or.inr ⟨hb, fun _ => Or.inr ⟨by rwa [cj_cj], by rwa [cj_cj]⟩⟩
    · exact Or.inl ⟨ha, fun h => absurd h hb⟩
  · have hb := hup.resolve_left ha
    exact Or.inr ⟨hb, fun h => absurd (by rwa [cj_cj] at h) ha⟩

private theorem not_both {lt : Plc E → Plc E → Prop} (h2 : ∀ a b, lt a b → ¬ lt b a) {Up : Plc E → Prop} {w₀ w : Plc E}
    (hne : cj w ≠ w) (ha : Top lt Up w₀ w) (hb : Top lt Up w₀ (cj w)) : False := by
  have hb2 := hb.2 (by rw [cj_cj]; exact ha.1)
  rw [cj_cj] at hb2
  rcases ha.2 hb.1 with e | ⟨e, h⟩
  · rcases hb2 with e' | ⟨e', _⟩
    · exact hne (e'.trans e.symm)
    · exact e' e
  · rcases hb2 with e' | ⟨_, h'⟩
    · exact e e'
    · exact h2 _ _ h h'

end UpperTheory.Gal.CertificateRingHomMap.PNbhdU

open UpperTheory.Gal.CertificateRingHomMap.PNbhdU in
theorem UpperTheory.Gal.CertificateRingHomMap.pNbhdU_of :
    UpperTheory.Gal.CertificateRingHomMap.Nbhd2 → UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.NbhdU := by
  intro h2 hI hL _ E _ _ _ n O hO Up hUp w₀ hw₀ hu₀
  obtain ⟨S₀, K₀, hK₀, hS₀⟩ := h2 E n O hO
  obtain ⟨lt, hlt1, hlt2⟩ := exists_lt (Plc E)
  have hne : ∀ w : Plc E, IsSplitAt w → cj w ≠ w := fun w hw => (hL E n w hw).2.2.1
  have hsp : ∀ w : Plc E, IsSplitAt w → IsSplitAt (cj w) := fun w hw => (hL E n w hw).2.2.2.1
  let T : Finset (Plc E) := insert w₀ (S₀ ∪ S₀.image (fun w => cj w))
  let S : Finset (Plc E) := T.filter (fun w => IsSplitAt w → Top lt Up w₀ w)
  let Kw : ∀ w : Plc E, Subgroup (GLw n w) := fun w =>
    if hw : IsSplitAt w then K₀ w ⊓ (K₀ (cj w)).comap (UpperTheory.Gal.CertificateRingHomMap.PNbhdU.th hw) else K₀ w
  have hKle : ∀ w, Kw w ≤ K₀ w := by
    intro w
    by_cases hw : IsSplitAt w
    · simp only [Kw, dif_pos hw]; exact inf_le_left
    · simp only [Kw, dif_neg hw]; exact le_rfl
  have hKopen : ∀ w, IsOpen (Kw w : Set (GLw n w)) := by
    intro w
    by_cases hw : IsSplitAt w
    · simp only [Kw, dif_pos hw, Subgroup.coe_inf, Subgroup.coe_comap]
      exact (hK₀ w).1.inter ((hK₀ (cj w)).1.preimage (continuous_th hw))
    · simp only [Kw, dif_neg hw]; exact (hK₀ w).1
  have hKKGL : ∀ w, Kw w ≤ GlobalTheory.LFun.KGL w (n := n) := fun w => (hKle w).trans (hK₀ w).2
  have hmemS : ∀ w, w ∈ T → (IsSplitAt w → Top lt Up w₀ w) → w ∈ S := fun w h h' => Finset.mem_filter.2 ⟨h, h'⟩
  refine ⟨S, Kw, ⟨?_, fun w _ => hKopen w, fun w _ => ?_, fun w _ _ => hKKGL w, fun w hw hs => ?_⟩, ?_⟩
  · exact hmemS _ (Finset.mem_insert_self _ _) fun _ => ⟨hu₀, fun _ => Or.inl rfl⟩
  · exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen (Kw w) (hKopen w)) (hKKGL w)
  · have hw' := (Finset.mem_filter.1 hw).2 hs
    exact ⟨hw'.1, fun hc => not_both hlt2 (hne w hs) hw' ((Finset.mem_filter.1 hc).2 (hsp w hs))⟩
  · intro u hu
    obtain ⟨hz, hS, hout⟩ := mem_lev.1 hu
    have hint : ∀ w, cLoc w u.1 ∈ GlobalTheory.LFun.KGL w (n := n) := by
      intro w
      by_cases h1 : w ∈ S
      · exact hKKGL w (hS w h1)
      · by_cases h2 : cj w ∈ S
        · have h3 := hI E n (ofU u) (cj w) hz (hKKGL _ (hS _ h2))
          have key : ∀ v : Plc E, v = w → comp v (ofU u) ∈ GlobalTheory.LFun.KGL v (n := n) → cLoc w u.1 ∈ GlobalTheory.LFun.KGL w (n := n) := by
            rintro v rfl h; exact h
          exact key _ (cj_cj w) h3
        · exact hout w h1 h2
    refine hS₀ u hint fun w hw => ?_
    have hT : w ∈ T := Finset.mem_insert_of_mem (Finset.mem_union_left _ hw)
    by_cases hs : IsSplitAt w
    · by_cases ht : Top lt Up w₀ w
      · exact hKle w (hS w (hmemS w hT fun _ => ht))
      · have ht' := (top_or hlt1 w₀ (hne w hs) (hUp w hs)).resolve_left ht
        have hT' : cj w ∈ T := Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw))
        have h3 := hS (cj w) (hmemS _ hT' fun _ => ht')
        simp only [Kw, dif_pos (hsp w hs)] at h3
        have h4 : UpperTheory.Gal.CertificateRingHomMap.PNbhdU.th (hsp w hs) (cLoc (cj w) u.1) ∈ K₀ (cj (cj w)) := (Subgroup.mem_inf.1 h3).2
        rw [← cLoc_cj_eq (hsp w hs) u] at h4
        have key : ∀ v : Plc E, v = w → cLoc v u.1 ∈ K₀ v → cLoc w u.1 ∈ K₀ w := by
          rintro v rfl h; exact h
        exact key _ (cj_cj w) h4
    · exact hKle w (hS w (hmemS w hT fun h => absurd h hs))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PKerFormU
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem rat_eq_one_of_ZU (s : ℚˣ) (hpos : 0 < (s : ℚ))
    (h : Units.map (algebraMap ℚ AfQ).toMonoidHom s ∈ ZU) : s = 1 := by
  have hv : ∀ v : Plc ℚ, HeightOneSpectrum.valuation ℚ v (s : ℚ) = 1 := fun v => by
    have h1 : Valued.v ((algebraMap ℚ AfQ (s : ℚ)) v) = 1 := h v
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  have hi : ∀ x : ℚ, (∀ v : Plc ℚ, HeightOneSpectrum.valuation ℚ v x ≤ 1) → ∃ m : ℤ, (m : ℚ) = x := fun x hx => by
    obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ x hx
    have h2 : IsIntegral ℤ (algebraMap (𝓞 ℚ) ℚ a) := a.2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact ⟨m, by simpa using hm⟩
  obtain ⟨m, hm⟩ := hi s (fun v => (hv v).le)
  obtain ⟨m', hm'⟩ := hi (s : ℚ)⁻¹ (fun v => by rw [map_inv₀, hv v, inv_one])
  have hmm : m * m' = 1 := by
    have h3 : (m : ℚ) * m' = 1 := by rw [hm, hm']; exact mul_inv_cancel₀ s.ne_zero
    exact_mod_cast h3
  have hm1 : m = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hmm with h4 | h4
    · exact h4
    · subst h4
      rw [← hm] at hpos
      norm_num at hpos
  ext
  rw [← hm, hm1]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem coord_emb (v : InfinitePlace E) (x : E) :
    coord v.embedding (pInf E (algebraMap E (Ad E) x)) = v.embedding x := by
  have h : ∀ w : InfinitePlace E, pInf E (algebraMap E (Ad E) x) w = w.embedding x := fun w => pInf_algebraMap _ _
  unfold coord
  simp [h]

private theorem val_rat (W : Wt E n) (j : ℤ) (f : algForms W) (γ : Gam0 E n) (h1 : γ.1.2 = 1) :
    ∃ a : finU (E := E) (n := n), ofU a = rat γ ∧
      ∀ u : finU (E := E) (n := n), algForms.val f (a.1 * u.1) = xi0 W j γ (algForms.val f u.1) := by
  have hy : (γ.1.1.val.map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * γ.1.1.val = 1 := by
    have h : (γ.1.1.val.map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * γ.1.1.val =
      algebraMap ℚ E γ.1.2 • (1 : Matrix (Fin n) (Fin n) E) := γ.2.1
    rw [h, h1]
    simp
  have hY : ratGL E n γ.1.1 ∈ UA E n := by
    change Formalism.UG.cT (conjAd E) (γ.1.1.val.map (algebraMap E (Ad E))) * 1 * γ.1.1.val.map (algebraMap E (Ad E)) = 1
    rw [GlobalTheory.DefU.ClassFin.cT_map (algebraMap E (Ad E)) (IsCMField.complexConj E).toRingEquiv.toRingHom (conjAd E)
      (fun y => (conjAd_algebraMap y).symm), mul_one, ← Matrix.map_mul]
    have h2 : Formalism.UG.cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.1.val * γ.1.1.val = 1 := hy
    rw [h2]
    simp
  let Y : UA E n := ⟨ratGL E n γ.1.1, hY⟩
  have hYr : Y ∈ ratU E n := Subgroup.mem_subgroupOf.2 ⟨γ.1.1, rfl⟩
  let a := GlobalTheory.UnitarySplit.finPart Y
  let b := GlobalTheory.UnitarySplit.infPart Y
  have hab : Y = a.1 * b.1 := GlobalTheory.UnitarySplit.finPart_mul_infPart Y
  refine ⟨a, ?_, fun u => ?_⟩
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · exact pFin_finGL _
    · show (1 : AfQˣ) = Units.map (algebraMap ℚ AfQ).toMonoidHom γ.1.2
      rw [h1, map_one]
  · have e : a.1 * u.1 = Y * (u.1 * ((b⁻¹ : infU E n) : UA E n)) := by
      have hc := GlobalTheory.DefU.fin_mul_inf u.2 b.2
      rw [hab, Subgroup.coe_inv, mul_assoc, ← mul_assoc b.1, ← hc, mul_assoc u.1, mul_inv_cancel, mul_one]
    have hc : cAll b.1 = embAll E n γ.1.1 := by
      funext v
      show cEmb v.embedding b.1 = GeneralLinearGroup.map v.embedding γ.1.1
      refine Units.ext (Matrix.ext fun i k => ?_)
      have h3 : (cEmb v.embedding b.1).val i k = coord v.embedding ((cInf b.1).val i k) := rfl
      rw [h3, GlobalTheory.UnitarySplit.cInf_infPart]
      exact coord_emb v _
    rw [e, algForms.val_left f hYr, algForms.val_right, inv_inv]
    have h4 : xi0 W j γ = Representation.dual
        ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) γ.1.1 := by
      have h6 : xi0 W j γ = (((γ.1.2 : ℚ) : ℂ) ^ j) • Representation.dual
          ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) γ.1.1 := rfl
      rw [h6, h1]
      simp
    rw [h4, Representation.dual_apply, Representation.dual_apply]
    have h5 : W.rep b⁻¹ = ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) γ.1.1⁻¹ := by
      have h7 : cAll (b⁻¹ : infU E n).1 = embAll E n γ.1.1⁻¹ := by
        rw [Subgroup.coe_inv, map_inv, hc, map_inv]
      show Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W (cAll (b⁻¹ : infU E n).1) =
        Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W (embAll E n γ.1.1⁻¹)
      rw [h7]
    rw [h5]

theorem pKerFormU_of :
    UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.KerFormU := by
  intro hB E _ _ _ n W j f hf K hK hfix
  obtain ⟨hinj, hsurj⟩ := hB E n
  let φ : GUf E n → Module.Dual ℂ W.Sp := fun g => if h : ∃ u, ofU u = g then algForms.val f h.choose.1 else 0
  have hφ : ∀ u : finU (E := E) (n := n), φ (ofU u) = algForms.val f u.1 := fun u => by
    have h : ∃ u', ofU u' = ofU u := ⟨u, rfl⟩
    show (if h : ∃ u', ofU u' = ofU u then algForms.val f h.choose.1 else 0) = _
    rw [dite_eq_left h, hinj h.choose_spec]
  have hone : ∀ γ : Gam0 E n, sim (rat γ) ∈ ZU → γ.1.2 = 1 := fun γ h => rat_eq_one_of_ZU γ.1.2 γ.2.2 h
  refine ⟨φ, ⟨?_, ?_, ?_⟩, hφ, ?_⟩
  · intro γ k hk he
    have h1 := hone γ (he ▸ hK k hk)
    rw [← he]
    show Units.map (algebraMap ℚ AfQ).toMonoidHom γ.1.2 = 1
    rw [h1, map_one]
  · intro γ u hγ hu
    obtain ⟨u₀, rfl⟩ := hsurj u hu
    obtain ⟨a, ha, hau⟩ := val_rat W j f γ (hone γ (hγ ▸ ZU.one_mem))
    rw [← ha, ← map_mul, hφ, hφ]
    exact hau u₀
  · intro k hk u hk1 hu
    obtain ⟨u₀, rfl⟩ := hsurj u hu
    obtain ⟨u', rfl⟩ := hsurj k hk1
    rw [← map_mul, hφ, hφ]
    show algForms.val f (u₀.1 * u'.1) = _
    rw [← algForms.val_algRep, hfix u' hk]
  · have hex : ∃ g, algForms.val f g ≠ 0 := by
      by_contra hc
      push_neg at hc
      refine hf (Subtype.ext (LinearMap.ext fun v => funext fun g => ?_))
      exact LinearMap.congr_fun (hc g) v
    obtain ⟨g, hg⟩ := hex
    refine ⟨ofU (GlobalTheory.UnitarySplit.finPart g), sim_ofU _, ?_⟩
    rw [hφ]
    intro h0
    apply hg
    have h1 := algForms.val_right f (GlobalTheory.UnitarySplit.finPart g).1 (GlobalTheory.UnitarySplit.infPart g)
    rw [← GlobalTheory.UnitarySplit.finPart_mul_infPart g] at h1
    rw [h1, h0, map_zero]

end UpperTheory.Gal.CertificateRingHomMap
end
