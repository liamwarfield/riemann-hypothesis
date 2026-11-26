module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNondegenerateRightInvariantFormOfCompactQu
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNormVEqPrimePowLeFinrank
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEquivariantProjectionsOfSumIrreducible
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupAutomorphicRepsOfInvariantForm
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.SplitComp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Factor
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

noncomputable section

namespace UpperTheory.V.Z.Sym.Al.FactorizationTer

open GlobalTheory.SplitPts GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem ua_ext {g h : UA E n} (h1 : cInf g = cInf h) (h2 : ∀ u, cLoc u g = cLoc u h) : g = h := by
  refine Subtype.ext (ga_ext h1 ?_)
  refine Units.ext (matAf_ext fun u => ?_)
  exact congrArg Units.val (h2 u)


open Classical in
private def idem (P : HeightOneSpectrum (𝓞 E) → Prop) : Af E :=
  ⟨fun u => if P u then 1 else 0, Filter.Eventually.of_forall fun u => by
    dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
private theorem pLoc_idem (P : HeightOneSpectrum (𝓞 E) → Prop) (u : HeightOneSpectrum (𝓞 E)) :
    pLoc E u (idem P) = if P u then 1 else 0 := rfl

private def cutM (P : HeightOneSpectrum (𝓞 E) → Prop) (A : Matrix (Fin n) (Fin n) (Af E)) :
    Matrix (Fin n) (Fin n) (Af E) := idem P • A + (1 - idem P) • 1

private theorem map_cutM_pos {P : HeightOneSpectrum (𝓞 E) → Prop} (A : Matrix (Fin n) (Fin n) (Af E))
    {u : HeightOneSpectrum (𝓞 E)} (h : P u) :
    RingHom.mapMatrix (pLoc E u) (cutM P A) = RingHom.mapMatrix (pLoc E u) A := by
  ext i j
  simp [cutM, Matrix.add_apply, Matrix.smul_apply, pLoc_idem, h]

private theorem map_cutM_neg {P : HeightOneSpectrum (𝓞 E) → Prop} (A : Matrix (Fin n) (Fin n) (Af E))
    {u : HeightOneSpectrum (𝓞 E)} (h : ¬ P u) :
    RingHom.mapMatrix (pLoc E u) (cutM P A) = 1 := by
  have h0 : pLoc E u (idem P) = 0 := by rw [pLoc_idem, if_neg h]
  refine Matrix.ext fun i j => ?_
  change pLoc E u (idem P * A i j + (1 - idem P) * (1 : Matrix (Fin n) (Fin n) (Af E)) i j) =
    (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) i j
  rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem cutM_mul (P : HeightOneSpectrum (𝓞 E) → Prop) {A B : Matrix (Fin n) (Fin n) (Af E)}
    (h : A * B = 1) : cutM P A * cutM P B = 1 := by
  refine matAf_ext fun u => ?_
  rw [map_mul, map_one]
  by_cases hu : P u
  · rw [map_cutM_pos _ hu, map_cutM_pos _ hu, ← map_mul, h, map_one]
  · rw [map_cutM_neg _ hu, map_cutM_neg _ hu, one_mul]

private def cut (P : HeightOneSpectrum (𝓞 E) → Prop) (k : GL (Fin n) (Af E)) : GL (Fin n) (Af E) where
  val := cutM P k.val
  inv := cutM P (k⁻¹).val
  val_inv := cutM_mul P (by simp)
  inv_val := cutM_mul P (by simp)

private theorem under_conj (u : HeightOneSpectrum (𝓞 E)) :
    (conjSrc (conjE E) u).under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) :=
  (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
      (Or.inr (conjPl_self_conjSrc u))

private theorem exists_part (w : HeightOneSpectrum (𝓞 E)) (g : UA E n) :
    ∃ x : UA E n, cInf x = 1 ∧
      (∀ u, u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → cLoc u x = cLoc u g) ∧
      ∀ u, u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) → cLoc u x = 1 := by
  set P : HeightOneSpectrum (𝓞 E) → Prop := fun u =>
    u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) with hP
  set k : GL (Fin n) (Af E) := cut P (Matrix.GeneralLinearGroup.map (pFin E) g.1) with hk
  have hpos : ∀ u, P u → Matrix.GeneralLinearGroup.map (pLoc E u) k = cLoc u g := fun u hu =>
    Units.ext (map_cutM_pos _ hu)
  have hneg : ∀ u, ¬ P u → Matrix.GeneralLinearGroup.map (pLoc E u) k = 1 := fun u hu =>
    Units.ext (map_cutM_neg _ hu)
  have hmem : finGL E n k ∈ UA E n := by
    refine finGL_mem_UA k fun u => ?_
    by_cases hu : P u
    · have hc : P (conjSrc (conjE E) u) := (under_conj u).trans hu
      rw [hpos u hu, hpos _ hc]
      exact comp_eq g u
    · have hc : ¬ P (conjSrc (conjE E) u) := fun h => hu ((under_conj u).symm.trans h)
      rw [hneg u hu, hneg _ hc]
      simp
  have hloc : ∀ u, cLoc u (⟨_, hmem⟩ : UA E n) = Matrix.GeneralLinearGroup.map (pLoc E u) k := fun u => by
    change Matrix.GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) (finGL E n k) = _
    exact Units.ext (congrArg (fun M : GL (Fin n) (Af E) => RingHom.mapMatrix (pLoc E u) M.val) (pFin_finGL k))
  exact ⟨⟨_, hmem⟩, pInf_finGL k, fun u hu => (hloc u).trans (hpos u hu),
    fun u hu => (hloc u).trans (hneg u hu)⟩

end UpperTheory.V.Z.Sym.Al.FactorizationTer

end

theorem UpperTheory.V.Z.Sym.Al.factor :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (w : Plc L),
        (∀ x ∈ locU n w, ∀ y ∈ away n w, x * y = y * x) ∧
        (∀ g : UA L n, ∃ x ∈ locU n w, ∃ y ∈ away n w, g = x * y) ∧
        (∀ w' : Plc L, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) → locU n w' ≤ away n w) ∧ infU L n ≤ away n w ∧
        (∀ x ∈ locU n w, x ∈ Kall (L := L) n ↔ cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n)) ∧
        ∀ x ∈ locU n w, ∀ y ∈ away n w, (x * y ∈ Kall (L := L) n ↔ x ∈ Kall (L := L) n ∧ y ∈ Kall (L := L) n) := by
  intro L _ _ _ n w
  have hfin : ∀ {x : UA L n}, x ∈ locU n w → cInf x = 1 := fun hx => (Subgroup.mem_inf.1 hx).1
  have hout : ∀ {x : UA L n}, x ∈ locU n w → ∀ u : Plc L, u.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) →
      cLoc u x = 1 := fun hx u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u) hu)
  have hin : ∀ {y : UA L n}, y ∈ away n w → ∀ u : Plc L, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) →
      cLoc u y = 1 := fun hy u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy u) hu)
  have haway : ∀ {y : UA L n}, (∀ u : Plc L, u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) → cLoc u y = 1) →
      y ∈ away n w := fun h =>
    Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 (h u hu)
  have hK : ∀ {x : UA L n}, x ∈ Kall (L := L) n → ∀ u : Plc L, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n) := fun hx u =>
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
  have hKmk : ∀ {x : UA L n}, x ∈ finU (E := L) (n := n) → (∀ u : Plc L, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n)) → x ∈ Kall (L := L) n :=
    fun h1 h2 => Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun u => Subgroup.mem_comap.2 (h2 u)⟩
  have hKf : ∀ {x : UA L n}, x ∈ Kall (L := L) n → x ∈ finU (E := L) (n := n) := fun hx => (Subgroup.mem_inf.1 hx).1
  refine ⟨fun x hx y hy => ?_, fun g => ?_, fun w' hw' x hx => ?_, fun x hx => ?_, fun x hx => ⟨fun h => hK h w, fun h => ?_⟩,
    fun x hx y hy => ⟨fun h => ?_, fun h => mul_mem h.1 h.2⟩⟩
  · refine FactorizationTer.ua_ext ?_ fun u => ?_
    · rw [map_mul, map_mul, hfin hx, one_mul, mul_one]
    · rw [map_mul, map_mul]
      by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · rw [hin hy u hu, one_mul, mul_one]
      · rw [hout hx u hu, one_mul, mul_one]
  · obtain ⟨x, h1, h2, h3⟩ := FactorizationTer.exists_part w g
    refine ⟨x, Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu =>
      MonoidHom.mem_ker.2 (h3 u hu)⟩, x⁻¹ * g, haway fun u hu => ?_, by group⟩
    rw [map_mul, map_inv, h2 u hu, inv_mul_cancel]
  · refine haway fun u hu => ?_
    exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
      (by rw [hu]; exact hw'.symm))
  · refine haway fun u _ => ?_
    have h : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := hx
    have h' := congrArg (Matrix.GeneralLinearGroup.map (pLoc L u)) h
    rw [map_one] at h'
    exact h'
  · refine hKmk (Subgroup.mem_inf.1 hx).1 fun u => ?_
    by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc hu with e | e
      · subst e
        exact h
      · subst e
        exact GlobalTheory.BCT.GlobLev.integral_conjSrc x w h
    · rw [hout hx u hu]
      exact one_mem _
  · have hf : cInf (x * y) = 1 := hKf h
    rw [map_mul, hfin hx, one_mul] at hf
    refine ⟨hKmk (Subgroup.mem_inf.1 hx).1 fun u => ?_, hKmk hf fun u => ?_⟩
    · by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · have := hK h u
        rwa [map_mul, hin hy u hu, mul_one] at this
      · rw [hout hx u hu]
        exact one_mem _
    · by_cases hu : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · rw [hin hy u hu]
        exact one_mem _
      · have := hK h u
        rwa [map_mul, hout hx u hu, one_mul] at this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ExistsOpen
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

namespace UpperTheory.V.Z.Sym.Al.CofinalityAlt

open GroundTheory.Automorphic.AdelicGLn GroundTheory.Automorphic.GLnLocal

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

private noncomputable abbrev fp (x : UA L n) : GL (Fin n) (Af L) :=
  Matrix.GeneralLinearGroup.map (pFin L) (x : GA L n)

private theorem cont_fp : Continuous (fp : UA L n → GL (Fin n) (Af L)) :=
  continuous_mapFin.comp continuous_subtype_val

private theorem e_apply (w : Plc L) (x : UA L n) : finiteRestrictedEquiv L n (fp x) w = cLoc w x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [finiteRestrictedEquiv_apply]
  rfl

private theorem cont_cLoc (w : Plc L) : Continuous (cLoc w : UA L n → GL (Fin n) (w.adicCompletion L)) := by
  have e : (cLoc w : UA L n → GL (Fin n) (w.adicCompletion L)) =
      fun x => finiteRestrictedEquiv L n (fp x) w := funext fun x => (e_apply w x).symm
  rw [e]
  exact (RestrictedProduct.continuous_eval w).comp ((finiteRestrictedEquiv L n).continuous.comp cont_fp)

private theorem snd_eq (x : UA L n) : (prodEquiv L n (x : GA L n)).2 = fp x :=
  Units.ext (Matrix.ext fun a b => by rw [prodEquiv_apply_snd]; rfl)

private theorem fst_eq (x : finU (E := L) (n := n)) : (prodEquiv L n ((x : UA L n) : GA L n)).1 = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [prodEquiv_apply_fst]
  have key := congrArg (fun g : GL (Fin n) (Cinf L) => g.1 a b) (MonoidHom.mem_ker.1 x.2)
  refine (infEq L).symm.injective (key.trans ?_)
  by_cases h : a = b
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

private theorem mem_Kall {x : UA L n} :
    x ∈ Kall L n ↔ x ∈ finU (E := L) (n := n) ∧ ∀ w : Plc L, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) := by
  simp [Kall, Subgroup.mem_inf, Subgroup.mem_iInf]

private theorem exists_open {U : Subgroup (UA L n)} (hU : IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U}) :
    ∃ O : Set (GL (Fin n) (Af L)), IsOpen O ∧ 1 ∈ O ∧ ∀ x : finU (E := L) (n := n), fp x.1 ∈ O → (x : UA L n) ∈ U := by
  obtain ⟨A, hA, eA⟩ := isOpen_induced_iff.1 hU
  obtain ⟨B, hB, rfl⟩ := isOpen_induced_iff.1 hA
  let c : GL (Fin n) (Af L) → GA L n := fun k => (prodEquiv L n).symm (1, k)
  have hc : Continuous c := (prodEquiv L n).symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hx : ∀ x : finU (E := L) (n := n), c (fp x.1) = ((x : UA L n) : GA L n) := fun x => by
    change (prodEquiv L n).symm _ = _
    rw [← fst_eq x, ← snd_eq]
    exact (prodEquiv L n).symm_apply_apply _
  have hmem : ∀ x : finU (E := L) (n := n), (x : UA L n) ∈ U ↔ ((x : UA L n) : GA L n) ∈ B := fun x =>
    (Set.ext_iff.1 eA x).symm
  refine ⟨c ⁻¹' B, hB.preimage hc, ?_, fun x hx' => ?_⟩
  · have h := hx 1
    have h1 : fp ((1 : finU (E := L) (n := n)) : UA L n) = 1 := map_one _
    rw [h1] at h
    rw [Set.mem_preimage, h]
    exact (hmem 1).1 (one_mem U)
  · rw [Set.mem_preimage, hx] at hx'
    exact (hmem x).2 hx'

private theorem nbhd {O : Set (GL (Fin n) (Af L))} (hO : IsOpen O) (h1 : 1 ∈ O) :
    ∃ T : Finset (Plc L), ∀ g : GL (Fin n) (Af L), g ∈ integralFiniteGL L n →
      (∀ v ∈ T, finiteRestrictedEquiv L n g v = 1) → g ∈ O := by
  let e := finiteRestrictedEquiv L n
  let s := RestrictedProduct.structureMap (fun v : Plc L => GL (Fin n) (v.adicCompletion L))
    (fun v => (integralGL (v.adicCompletion L) n : Set (GL (Fin n) (v.adicCompletion L)))) Filter.cofinite
  have hs : Continuous fun a => e.symm (s a) :=
    e.symm.continuous.comp RestrictedProduct.isEmbedding_structureMap.continuous
  have hone : e.symm (s fun v => ⟨1, one_mem _⟩) = 1 := by
    have : s (fun v => ⟨1, one_mem _⟩) = 1 := rfl
    rw [this, map_one]
  obtain ⟨T, u, hu, hT⟩ := isOpen_pi_iff.1 (hO.preimage hs) (fun v => ⟨1, one_mem _⟩)
    (by rw [Set.mem_preimage, hone]; exact h1)
  refine ⟨T, fun g hg hgT => ?_⟩
  have hint := (mem_integralFiniteGL_iff_forall L n).1 hg
  have hg' : e.symm (s fun v => ⟨e g v, hint v⟩) = g := by
    have : s (fun v => ⟨e g v, hint v⟩) = e g := by
      ext v
      rfl
    rw [this, e.symm_apply_apply]
  rw [← hg']
  refine hT fun v hv => ?_
  have : (⟨e g v, hint v⟩ : (integralGL (v.adicCompletion L) n : Set (GL (Fin n) (v.adicCompletion L)))) = ⟨1, one_mem _⟩ :=
    Subtype.ext (hgT v hv)
  rw [this]
  exact (hu v hv).2

private theorem fp_mem {x : UA L n} (hx : ∀ w : Plc L, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n)) :
    fp x ∈ integralFiniteGL L n :=
  (mem_integralFiniteGL_iff_forall L n).2 fun v => by
    rw [e_apply]
    exact GlobalTheory.StabInt.mem_integralGL_of_mem_KGL (hx v)

private theorem clause1 (U : Subgroup (UA L n)) (hU : IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U}) :
    ∃ T : Finset (Plc L), Kall L n ⊓ ⨅ w ∈ T, away n w ≤ U := by
  obtain ⟨O, hO, h1, hOU⟩ := exists_open hU
  obtain ⟨T, hT⟩ := nbhd hO h1
  refine ⟨T, fun x hx => ?_⟩
  obtain ⟨hK, hA⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hf, hi⟩ := mem_Kall.1 hK
  refine hOU ⟨x, hf⟩ (hT _ (fp_mem hi) fun v hv => ?_)
  rw [e_apply]
  have h := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hA v) hv
  exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h v) rfl)

private theorem clause2 : IsLevel (Kall L n) := by
  refine ⟨le_rfl, ?_⟩
  have e : {x : finU (E := L) (n := n) | (x : UA L n) ∈ Kall L n} =
      (fun x : finU (E := L) (n := n) => fp x.1) ⁻¹' (integralFiniteGL L n : Set (GL (Fin n) (Af L))) := by
    ext x
    refine ⟨fun h => fp_mem (mem_Kall.1 h).2, fun h => mem_Kall.2 ⟨x.2, fun w => ?_⟩⟩
    have h' := (mem_integralFiniteGL_iff_forall L n).1 h w
    rw [e_apply] at h'
    exact GlobalTheory.StabInt.mem_KGL_of_mem_integralGL h'
  rw [e]
  exact (isOpen_integralFiniteGL L n).preimage (cont_fp.comp continuous_subtype_val)

private theorem clause3 (U : Subgroup (UA L n)) (hU : IsLevel U) (S : Finset (Plc L))
    (V : ∀ w : Plc L, Sig.Lev (Kw w)) : IsLevel (lev U S V) := by
  refine ⟨inf_le_left.trans hU.1, ?_⟩
  have e : {x : finU (E := L) (n := n) | (x : UA L n) ∈ lev U S V} = {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} ∩
      ⋂ w ∈ S, (fun x : finU (E := L) (n := n) => cLoc w (x : UA L n)) ⁻¹' ((V w).J n : Set (GL (Fin n) (Kw w))) := by
    ext x
    simp [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
  rw [e]
  exact hU.2.inter (isOpen_biInter_finset fun w _ =>
    ((Sig.finFacts _ (V w)).2.2.2.2.2 n).2.1.preimage ((cont_cLoc w).comp continuous_subtype_val))

private theorem clause4 (U : Subgroup (UA L n)) (hU : IsLevel U) :
    ∀ᶠ w : Plc L in Filter.cofinite, locU n w ⊓ Kall L n ≤ U := by
  obtain ⟨T, hT⟩ := clause1 U hU.2
  have hfin : ∀ t : Plc L, {w : Plc L | w.under (𝓞 (Lp L)) = t.under (𝓞 (Lp L))}.Finite := fun t =>
    ((IsDedekindDomain.primesOver_finite (t.under (𝓞 (Lp L))).asIdeal (𝓞 L)).preimage
      (fun a _ b _ h => HeightOneSpectrum.ext h)).subset
      fun w hw => ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩
  refine Filter.eventually_cofinite.2 ((T.finite_toSet.biUnion fun t _ => hfin t).subset fun w hw => ?_)
  by_contra hn
  refine hw fun x hx => hT ?_
  obtain ⟨hl, hK⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨hK, Subgroup.mem_iInf.2 fun t => Subgroup.mem_iInf.2 fun ht =>
    Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
  refine Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hl).2 u) fun huw => hn ?_
  exact Set.mem_biUnion (Finset.mem_coe.2 ht) (huw.symm.trans hu)

end UpperTheory.V.Z.Sym.Al.CofinalityAlt

open UpperTheory.V.Z.Sym.Al.CofinalityAlt in
theorem UpperTheory.V.Z.Sym.Al.cof :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ),
        (∀ U : Subgroup (UA L n), IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} → ∃ T : Finset (Plc L), Kall L n ⊓ ⨅ w ∈ T, away n w ≤ U) ∧
        IsLevel (Kall L n) ∧ (∀ U : Subgroup (UA L n), IsLevel U → ∀ S V, IsLevel (lev U S V)) ∧
        ∀ U : Subgroup (UA L n), IsLevel U → ∀ᶠ w : Plc L in Filter.cofinite, locU n w ⊓ Kall L n ≤ U := by
  intro L _ _ _ n
  exact ⟨clause1, clause2, clause3, clause4⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AfFin
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.afFin :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)), IsLevel U → FiniteDimensional ℂ (AF R U) := by
  intro L _ _ _ n V _ _ _ R U hU
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite L n (U.subgroupOf (finU (E := L) (n := n))) hU.2
  let T : AF R U →ₗ[ℂ] (S → V) :=
    { toFun := fun φ s => φ.1 s.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective T ((injective_iff_map_eq_zero T).2 fun φ h0 => ?_)
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
  have hφ : IsAF R U φ.1 := φ.2
  have hz : φ.1 s = 0 := congrFun h0 ⟨s, hs⟩
  rw [hφ.level _ (Subgroup.mem_subgroupOf.1 hk), hφ.inf x hx, hφ.left γ hγ, hz, map_zero]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.UnrSmooth
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem exists_small (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ∃ s : kˣ, valuation k (s : k) < 1 := by
  obtain ⟨x, hx0, hx⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  exact ⟨Units.mk0 x (fun h => hx0 (by simp [h])), hx⟩

private theorem split_small (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : kˣ) : ∃ s t : kˣ, valuation k (s : k) < 1 ∧ valuation k (t : k) < 1 ∧ x = s / t := by
  obtain ⟨p, hp⟩ := exists_small k
  by_cases hx : valuation k (x : k) < 1
  · refine ⟨x * p, p, ?_, hp, by simp⟩
    rw [Units.val_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hx.le) hp
  · refine ⟨p, p * x⁻¹, hp, ?_, by simp⟩
    have h1 : 1 ≤ valuation k (x : k) := not_lt.1 hx
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    have h0 : valuation k (x : k) ≠ 0 := by simp
    have h2 : (valuation k (x : k))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h2) hp

theorem UpperTheory.V.Z.Sym.Al.unrSmooth :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], (∀ χ : kˣ →* ℂˣ, (∀ u ∈ Hi.Uo k, χ u = 1) → IsSmoothChar χ) ∧
        ∀ (ψ : Fin 2 → kˣ →* ℂˣ) (b : kˣ →* ℂˣ), (∀ t : kˣ, valuation k (t : k) < 1 → expo ψ ![t, t⁻¹] = expo ![b, 1] ![t, t⁻¹]) → ψ 0 / ψ 1 = b := by
  intro k _ _ _ _
  refine ⟨fun χ h => isSmoothChar_of_isUnram fun x hx => h x hx, fun ψ b h => ?_⟩
  have key : ∀ t : kˣ, valuation k (t : k) < 1 → (ψ 0 / ψ 1) t = b t := by
    intro t ht
    have h1 := Units.val_injective (h t ht)
    have h2 := mul_right_cancel h1
    rw [torusChar_apply, torusChar_apply, Fin.prod_univ_two, Fin.prod_univ_two] at h2
    simpa [MonoidHom.div_apply, div_eq_mul_inv] using h2
  refine MonoidHom.ext fun x => ?_
  obtain ⟨s, t, hs, ht, rfl⟩ := split_small k x
  rw [map_div, map_div, key s hs, key t ht]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AutProj
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

open GlobalTheory.DefU in
theorem UpperTheory.V.Z.Sym.Al.autProj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (M : Submodule ℂ (GlobalTheory.DefU.autU L n)), FiniteDimensional ℂ M →
        ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Submodule ℂ (UA L n → ℂ)) (P : κ → GlobalTheory.DefU.autU L n →ₗ[ℂ] GlobalTheory.DefU.autU L n),
          (∀ i, IsAutRepU (σ i)) ∧ (∀ i φ, (P i φ).1 ∈ σ i) ∧
          (∀ i x φ, P i (GlobalTheory.DefU.autRep L n x φ) = GlobalTheory.DefU.autRep L n x (P i φ)) ∧ ∀ φ ∈ M, ∑ i, P i φ = φ := by
  intro L _ _ _ n M hM
  obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.unitary_adelic_t2_locallyCompact_secondCountable L n
  obtain ⟨C, hC, hcov⟩ := UpperTheory.exists_compact_fundamental_set_unitary L n
  obtain ⟨B, hdef, hinv⟩ := UpperTheory.exists_nondegenerate_right_invariant_form_of_compact_quotient (UA L n) (ratU L n) C hC hcov
  have hsum := UpperTheory.mem_iSup_automorphicReps_of_invariant_form L n B (fun φ h => hdef φ h.cont h.left)
    (fun x φ ψ h h' => hinv x φ ψ h.cont h.left h'.cont h'.left)
  have hi := Submodule.map_injective_of_injective (autU L n).injective_subtype
  obtain ⟨κ, _, U, P, hU, hP, hPe, hPs⟩ := UpperTheory.exists_equivariant_projections_of_sum_irreducible (UA L n) (autU L n) (autRep L n) (fun x => by
    have key : ∀ (Z : Submodule ℂ (autU L n)), (∀ σ, IsAutRepU σ → σ.comap (autU L n).subtype ≤ Z) → x ∈ Z := by
      intro Z hZ
      have hle : (⨆ σ : {σ : Submodule ℂ (UA L n → ℂ) // IsAutRepU σ}, σ.1) ≤ Z.map (autU L n).subtype :=
        iSup_le fun σ φ hφ => ⟨⟨φ, σ.2.aut φ hφ⟩, hZ σ.1 σ.2 hφ, rfl⟩
      obtain ⟨y, hy, e⟩ := hle (hsum x.1 x.2)
      exact Subtype.ext e ▸ hy
    refine key _ fun σ hσ => ?_
    have hm : (σ.comap (autU L n).subtype).map (autU L n).subtype = σ := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 hσ.aut
    refine le_iSup_of_le ⟨σ.comap (autU L n).subtype, fun h => hσ.ne_bot ?_, fun g u hu => hσ.stable g u.1 hu,
      fun N hN hst => ?_⟩ le_rfl
    · rw [← hm, h, Submodule.map_bot]
    · refine (hσ.irred (N.map (autU L n).subtype) (hm ▸ Submodule.map_mono hN) ?_).imp
        (fun h => hi (h.trans (Submodule.map_bot _).symm)) fun h => hi (h.trans hm.symm)
      rintro g _ ⟨u, hu, rfl⟩
      exact ⟨_, hst g u hu, rfl⟩) M hM
  refine ⟨κ, inferInstance, fun i => (U i).map (autU L n).subtype, P, fun i => ⟨?_, ?_, ?_, fun N hN hst => ?_⟩,
    fun i φ => ⟨_, hP i φ, rfl⟩, hPe, hPs⟩
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, (hU i).2.1 g u hu, rfl⟩
  · exact fun h => (hU i).1 (hi (h.trans (Submodule.map_bot _).symm))
  · have hm : (N.comap (autU L n).subtype).map (autU L n).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hN.trans (Submodule.map_subtype_le _ _))
    rcases (hU i).2.2 (N.comap (autU L n).subtype) (fun u hu => by
      obtain ⟨w, hw, e⟩ := hN hu
      exact Subtype.ext e ▸ hw) (fun g u hu => hst g u.1 hu) with h | h
    · left; rw [← hm, h, Submodule.map_bot]
    · right; rw [← hm, h]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.RegUnl
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem ne_of_div {G : Type*} [CommGroup G] {p x y : G} (h₁ : x / y ≠ 1) (h₂ : x / y ≠ p) :
    x ≠ y ∧ x ≠ y * p :=
  ⟨fun h => h₁ (by rw [h, div_self']), fun h => h₂ (by rw [h, mul_div_cancel_left])⟩

private theorem inv_ne_of {G : Type*} [CommGroup G] {p x : G} (h : x ≠ p⁻¹) : x⁻¹ ≠ p :=
  fun e => h (by rw [← e, inv_inv])

private theorem triple {G : Type*} [CommGroup G] {a p : G} (h1 : a ≠ 1) (hp : a ≠ p) (hm : a ≠ p⁻¹)
    (s1 : a ^ 2 ≠ 1) (sp : a ^ 2 ≠ p) (sm : a ^ 2 ≠ p⁻¹) (i i' : Fin 3) (hne : i ≠ i') :
    (![a, 1, a⁻¹] : Fin 3 → G) i ≠ ![a, 1, a⁻¹] i' ∧ (![a, 1, a⁻¹] : Fin 3 → G) i ≠ ![a, 1, a⁻¹] i' * p := by
  have e02 : a / a⁻¹ = a ^ 2 := by rw [div_inv_eq_mul, pow_two]
  have e20 : a⁻¹ / a = (a ^ 2)⁻¹ := by rw [← e02, inv_div]
  fin_cases i <;> fin_cases i' <;> first
    | exact absurd rfl hne
    | (apply ne_of_div <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, div_one, one_div, inv_inv, e02, e20]
       <;> first
         | exact h1 | exact hp | exact s1 | exact sp
         | exact inv_ne_one.2 h1 | exact inv_ne_one.2 s1
         | exact inv_ne_of hm | exact inv_ne_of sm)

theorem UpperTheory.V.Z.Sym.Al.regUnl :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a : kˣ →* ℂˣ), Reg a →
        ((∀ i, ∀ u ∈ Hi.Uo k, (![a, 1, a⁻¹] : Fin 3 → kˣ →* ℂˣ) i u = 1) ∧
          ∀ i i' : Fin 3, i ≠ i' → ![a, 1, a⁻¹] i ≠ ![a, 1, a⁻¹] i' ∧ ![a, 1, a⁻¹] i ≠ ![a, 1, a⁻¹] i' * absPow k 1) ∧
        ∀ ψ : Fin 2 → kˣ →* ℂˣ, ψ 0 / ψ 1 = a ^ 2 → ∀ i i', i ≠ i' → ψ i ≠ ψ i' ∧ ψ i ≠ ψ i' * absPow k 1 := by
  intro k _ _ _ _ a ⟨hu, hr⟩
  have two : absPow k 2 = absPow k 1 ^ 2 := by
    rw [pow_two, ← absPow_add]; norm_num
  have s1 : a ^ 2 ≠ 1 := by
    have := hr 0 (by norm_num)
    simpa using this
  have sp : a ^ 2 ≠ absPow k 1 := by
    have := hr 1 (by norm_num)
    simpa using this
  have sm : a ^ 2 ≠ (absPow k 1)⁻¹ := by
    have := hr (-1) (by norm_num)
    simpa [absPow_neg] using this
  have h1 : a ≠ 1 := fun h => s1 (by rw [h, one_pow])
  have hp : a ≠ absPow k 1 := fun h => hr 2 (by norm_num) (by
    rw [h]; push_cast; exact two.symm)
  have hm : a ≠ (absPow k 1)⁻¹ := fun h => hr (-2) (by norm_num) (by
    rw [h]; push_cast; rw [absPow_neg, two, inv_pow])
  refine ⟨⟨fun i u hu' => ?_, triple h1 hp hm s1 sp sm⟩, fun ψ hψ i i' hne => ?_⟩
  · fin_cases i
    · exact hu u hu'
    · rfl
    · show (a u)⁻¹ = 1
      rw [hu u hu', inv_one]
  · have e : ψ 1 / ψ 0 = (a ^ 2)⁻¹ := by rw [← hψ, inv_div]
    fin_cases i <;> fin_cases i'
    · exact absurd rfl hne
    · apply ne_of_div
      · exact hψ ▸ s1
      · exact hψ ▸ sp
    · apply ne_of_div
      · exact e ▸ inv_ne_one.2 s1
      · exact e ▸ inv_ne_of sm
    · exact absurd rfl hne
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.CoefAut
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem exists_finPart {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} :
    ∃ p : UA L n → finU (E := L) (n := n), Continuous p ∧ p 1 = 1 ∧ ∀ x, (p x : UA L n)⁻¹ * x ∈ infU L n := by
  have hfin : Continuous (finGL L n) :=
    Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
      (continuous_const.prodMk continuous_id : Continuous fun x : Af L => ((0, x) : InfiniteAdeleRing L × Af L))))
  refine ⟨fun x => ⟨⟨finGL L n (Matrix.GeneralLinearGroup.map (pFin L) x.1),
    GlobalTheory.SplitPts.finGL_mem_UA _ fun u => GlobalTheory.SplitPts.comp_eq x u⟩, MonoidHom.mem_ker.2 (pInf_finGL _)⟩,
    Continuous.subtype_mk (Continuous.subtype_mk
      (hfin.comp (GlobalTheory.DefU.continuous_map_pFin.comp continuous_subtype_val)) _) _, ?_, fun x => ?_⟩
  · refine Subtype.ext (Subtype.ext ?_)
    change finGL L n (Matrix.GeneralLinearGroup.map (pFin L) 1) = 1
    rw [map_one, map_one]
  · change Matrix.GeneralLinearGroup.map (pFin L)
      ((finGL L n (Matrix.GeneralLinearGroup.map (pFin L) x.1))⁻¹ * x.1) = 1
    rw [map_mul, map_inv, pFin_finGL, inv_mul_cancel]

private theorem continuous_infC {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} :
    Continuous (infC L n) := by
  have hτ : ∀ τ : L →+* ℂ, Continuous (cEmb (E := L) (n := n) τ) := fun τ => by
    have h1 : Continuous (coord (E := L) τ) := by
      unfold coord
      split_ifs
      · exact continuous_apply _
      · exact Complex.continuous_conj.comp (continuous_apply _)
    have h2 : Continuous (pInf L) := continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
        ((continuous_apply w).comp continuous_fst)
    exact (Continuous.units_map _ (continuous_id.matrix_map h1)).comp
      ((Continuous.units_map _ (continuous_id.matrix_map h2)).comp continuous_subtype_val)
  exact continuous_pi fun v => hτ v.embedding

private theorem infC_of_fin {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {k : UA L n}
    (hk : k ∈ finU (E := L) (n := n)) : infC L n k = 1 :=
  funext fun v => by
    change Matrix.GeneralLinearGroup.map (coord v.embedding) (cInf k) = 1
    rw [MonoidHom.mem_ker.1 hk, map_one]

theorem UpperTheory.V.Z.Sym.Al.coefAut :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V), ContCoef R → ∀ U, IsLevel U → ∀ φ : UA L n → V, IsAF R U φ →
        ∀ f : V →ₗ[ℂ] ℂ, IsAutFormU (f ∘ φ) := by
  intro L _ _ _ n V _ _ _ R hR U hU φ hφ f
  obtain ⟨p, hp, hp1, hp2⟩ := exists_finPart (L := L) (n := n)
  have hU1 : {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} ∈ nhds (1 : finU (E := L) (n := n)) := hU.2.mem_nhds U.one_mem

  have hsm : ∀ᶠ z in nhds (1 : UA L n), ∀ g, φ (g * z) = R (infC L n z⁻¹) (φ g) := by
    have hUp : {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} ∈ nhds (p 1) := by rwa [hp1]
    filter_upwards [(hp.tendsto 1).eventually hUp] with z hz g
    have h1 := hφ.inf _ (hp2 z) (g * (p z : UA L n))
    rw [hφ.level _ hz g, mul_assoc, mul_inv_cancel_left] at h1
    have e : infC L n ((p z : UA L n)⁻¹ * z)⁻¹ = infC L n z⁻¹ := by
      rw [mul_inv_rev, inv_inv, map_mul, infC_of_fin (p z).2, mul_one]
    rw [h1, e]
  refine ⟨?_, fun γ hγ g => congrArg f (hφ.left γ hγ g), ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g0 => ?_
    have hc : Continuous fun g : UA L n => f (R (infC L n (g⁻¹ * g0)) (φ g0)) :=
      (hR (φ g0) f).comp (continuous_infC.comp (continuous_inv.mul continuous_const))
    refine hc.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA L n => g0⁻¹ * g) (nhds g0) (nhds 1) := by
      have : Continuous fun g : UA L n => g0⁻¹ * g := continuous_const.mul continuous_id
      simpa only [inv_mul_cancel] using this.tendsto g0
    filter_upwards [ht.eventually hsm] with g hg
    have e := hg g0
    rw [mul_inv_cancel_left, mul_inv_rev, inv_inv] at e
    rw [Function.comp_apply, e]
  · refine isOpen_stab_of_mem_nhds ((RU L n).comp (finU (E := L) (n := n)).subtype) _ ?_
    filter_upwards [hU1] with k hk
    funext g
    exact congrArg f (hφ.level _ hk g)
  · let C : Module.Dual ℂ V →ₗ[ℂ] (UA L n → ℂ) :=
      { toFun := fun μ g => μ (φ g)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range C) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    refine ⟨f ∘ₗ R (infC L n (k : UA L n)⁻¹), ?_⟩
    funext g
    change f (R (infC L n (k : UA L n)⁻¹) (φ g)) = f (φ (g * k))
    rw [hφ.inf _ k.2 g]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.CompEx
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.compEx :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA L n → ℂ), IsAutRepU π → ∀ w, IsSplitAt w → ∃ τ, Comp π w τ := by
  intro H L _ _ _ unr n hn π hπ w hw
  obtain ⟨P, hb⟩ := UpperTheory.BaseChangeIdentities.splitComp
    (GlobalTheory.BcSpeh.bcSpeh_of_baseChange (GlobalTheory.BaseChangeBridge.main H.aut.bc H.loc.bern)
      (GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual H.aut.mw)) L unr n hn π hπ
  exact ⟨P w hw, hb w hw⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.EigTS
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.eigTS :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (V : Type) [AddCommGroup V] [Module ℂ V] (φ : UA L 2 → V) (w : Plc L) (W : Sig.Lev (Kw w)) (ψ : Fin 2 → (Kw w)ˣ →* ℂˣ), EigT φ w W ψ → EigS φ w W (ψ 0 / ψ 1) := by
  intro L _ _ _ V _ _ φ w W ψ h t ht
  have hd : Sig.SDom ![t, t⁻¹] := by
    intro i j hij
    have h0 : valuation (Kw w) (t : Kw w) ≠ 0 := by simp
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    exact ht.trans ((one_lt_inv₀ (zero_lt_iff.2 h0)).2 ht)
  have e : Dict.expo ![ψ 0 / ψ 1, 1] ![t, t⁻¹] = Dict.expo ψ ![t, t⁻¹] := by
    simp [Dict.expo, torusChar, Fin.prod_univ_two, div_eq_mul_inv]
  rw [e]; exact h _ hd
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SmoothDepth
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.smoothDepth :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ), IsSmoothChar χ → ∃ c₀ : ℕ, ∀ c ≥ c₀, ∀ u ∈ Hi.Uc k (c + 1), χ u = 1 := by
  intro k _ _ _ _ χ hχ
  have hopen : IsOpen (χ.ker : Set kˣ) := hχ
  obtain ⟨U, hU, hUe⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.mp hopen
  have h1U : (1 : k) ∈ U := by
    have h : (1 : kˣ) ∈ Units.val ⁻¹' U := by
      rw [hUe]
      exact χ.ker.one_mem
    exact h
  obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_iff.mp (hU.mem_nhds h1U)
  have hu1 : uniformizer k < 1 := uniformizer_lt_one
  obtain ⟨c₀, hc₀⟩ := exists_pow_lt₀ hu1 γ
  refine ⟨c₀, fun c hc u hu => ?_⟩
  obtain ⟨-, hv⟩ := Sig.mem_Uc.mp hu
  have hlt : valuation k ((u : k) - 1) < γ :=
    calc valuation k ((u : k) - 1) ≤ uniformizer k ^ ((c + 1 : ℕ) : ℤ) := hv
      _ = uniformizer k ^ (c + 1) := zpow_natCast _ _
      _ ≤ uniformizer k ^ c₀ := pow_le_pow_right_of_le_one' hu1.le (by omega)
      _ < γ := hc₀
  have hmem : (u : k) ∈ U := hγ ⟨(u : k) - 1, hlt, by ring⟩
  have h : u ∈ Units.val ⁻¹' U := hmem
  rw [hUe] at h
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.IsoCopy
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

private theorem isoCopy_struct {H T M : Type} [Group H] [AddCommGroup T] [Module ℂ T] [AddCommGroup M] [Module ℂ M]
    (τ : Representation ℂ H T) (μ : Representation ℂ H M) (hτ : τ.IsIrreducible)
    (hsup : (⨆ f : {f : T →ₗ[ℂ] M // ∀ h x, f (τ h x) = μ h (f x)}, LinearMap.range f.1) = ⊤) :
    IsSemisimpleModule (MonoidAlgebra ℂ H) μ.asModule ∧
      IsIsotypicOfType (MonoidAlgebra ℂ H) μ.asModule τ.asModule := by
  have hS : IsSimpleModule (MonoidAlgebra ℂ H) τ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule τ).1 hτ
  let F : {f : T →ₗ[ℂ] M // ∀ h x, f (τ h x) = μ h (f x)} →
      (τ.asModule →ₗ[MonoidAlgebra ℂ H] μ.asModule) := fun f =>
    Representation.IntertwiningMap.equivLinearMapAsModule τ μ
      (f.1.intertwiningMap_of_isIntertwiningMap τ μ f.2)
  have hle : ∀ f, LinearMap.range (F f) ≤ isotypicComponent (MonoidAlgebra ℂ H) μ.asModule τ.asModule := by
    intro f
    rcases LinearMap.injective_or_eq_zero (F f) with hi | h0
    · exact le_sSup ⟨(LinearEquiv.ofInjective (F f) hi).symm⟩
    · simp [h0]
  have htop : isotypicComponent (MonoidAlgebra ℂ H) μ.asModule τ.asModule = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : ∀ y : M, y ∈ (⨆ f : {f : T →ₗ[ℂ] M // ∀ h x, f (τ h x) = μ h (f x)}, LinearMap.range f.1) := fun y => by
      rw [hsup]; exact Submodule.mem_top
    refine Submodule.iSup_induction _
      (motive := fun y : M => (y : μ.asModule) ∈ isotypicComponent (MonoidAlgebra ℂ H) μ.asModule τ.asModule)
      (hx x) ?_ ?_ ?_
    · rintro f _ ⟨t, rfl⟩
      exact hle f ⟨t, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  have hss : IsSemisimpleModule (MonoidAlgebra ℂ H) (isotypicComponent (MonoidAlgebra ℂ H) μ.asModule τ.asModule) :=
    inferInstance
  rw [htop] at hss
  exact ⟨IsSemisimpleModule.congr (Submodule.topEquiv (R := MonoidAlgebra ℂ H) (M := μ.asModule)).symm,
    IsIsotypicOfType.of_isotypicComponent_eq_top htop⟩

theorem UpperTheory.V.Z.Sym.Al.isoCopy :
    ∀ (H T M : Type) [Group H] [AddCommGroup T] [Module ℂ T] [AddCommGroup M] [Module ℂ M] (τ : Representation ℂ H T) (μ : Representation ℂ H M),
        τ.IsIrreducible → (⨆ f : {f : T →ₗ[ℂ] M // ∀ h x, f (τ h x) = μ h (f x)}, LinearMap.range f.1) = ⊤ →
        (∀ v : M, v ≠ 0 → ∃ p : M →ₗ[ℂ] T, (∀ h x, p (μ h x) = τ h (p x)) ∧ p v ≠ 0) ∧
        ∀ (N I : Type) [AddCommGroup N] [Module ℂ N] [Finite I] (ν : Representation ℂ H N) (q : I → N →ₗ[ℂ] M),
          (∀ i h x, q i (ν h x) = μ h (q i x)) → (∀ x, (∀ i, q i x = 0) → x = 0) → Nontrivial N →
          ∃ f : T →ₗ[ℂ] N, f ≠ 0 ∧ ∀ h x, f (τ h x) = ν h (f x) := by
  intro H T M _ _ _ _ _ τ μ hτ hsup
  obtain ⟨hss, hiso⟩ := isoCopy_struct τ μ hτ hsup
  refine ⟨fun v hv => ?_, fun N I _ _ _ ν q hq hsep hN => ?_⟩
  · obtain ⟨ι, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
    have hev : e (v : μ.asModule) ≠ 0 := fun h => hv (e.map_eq_zero_iff.1 h)
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hev
    let P : μ.asModule →ₗ[MonoidAlgebra ℂ H] τ.asModule :=
      (Finsupp.lapply i).comp e.toLinearMap
    let p := (Representation.IntertwiningMap.equivLinearMapAsModule μ τ).symm P
    exact ⟨p.toLinearMap, fun h x => Representation.IntertwiningMap.isIntertwining _ _ p h x, hi⟩
  · let Q : I → (ν.asModule →ₗ[MonoidAlgebra ℂ H] μ.asModule) := fun i =>
      Representation.IntertwiningMap.equivLinearMapAsModule ν μ
        ((q i).intertwiningMap_of_isIntertwiningMap ν μ (hq i))
    have hinj : Function.Injective (LinearMap.pi Q) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      exact hsep x fun i => congrFun hx i
    have hNs : IsSemisimpleModule (MonoidAlgebra ℂ H) ν.asModule :=
      IsSemisimpleModule.of_injective _ hinj
    haveI : Nontrivial ν.asModule := hN
    obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule (MonoidAlgebra ℂ H) ν.asModule)
    rw [← isSimpleModule_iff_isAtom] at hS
    haveI := hS
    haveI := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) S
    obtain ⟨s, hs⟩ := exists_ne (0 : S)
    obtain ⟨i, hi⟩ : ∃ i, Q i s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hs (Subtype.ext (hsep s.1 fun i => hc i))
    have hne : (Q i).comp S.subtype ≠ 0 := fun h => hi (LinearMap.congr_fun h s)
    have hj : Function.Injective ((Q i).comp S.subtype) :=
      (LinearMap.injective_or_eq_zero _).resolve_right hne
    let e1 := LinearEquiv.ofInjective _ hj
    haveI : IsSimpleModule (MonoidAlgebra ℂ H) (LinearMap.range ((Q i).comp S.subtype)) := IsSimpleModule.congr e1.symm
    obtain ⟨e2⟩ := hiso (LinearMap.range ((Q i).comp S.subtype))
    let G : τ.asModule →ₗ[MonoidAlgebra ℂ H] ν.asModule :=
      S.subtype.comp (e1.symm.toLinearMap.comp e2.symm.toLinearMap)
    let g := (Representation.IntertwiningMap.equivLinearMapAsModule τ ν).symm G
    refine ⟨g.toLinearMap, ?_, fun h x => Representation.IntertwiningMap.isIntertwining _ _ g h x⟩
    intro h0
    have : IsSimpleModule (MonoidAlgebra ℂ H) τ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule τ).1 hτ
    haveI := IsSimpleModule.nontrivial (MonoidAlgebra ℂ H) τ.asModule
    obtain ⟨t, ht⟩ := exists_ne (0 : τ.asModule)
    have hG : G t = 0 := LinearMap.congr_fun h0 t
    have : (e1.symm (e2.symm t) : S) = 0 := Subtype.ext hG
    have hz : e2.symm t = 0 := e1.symm.injective (this.trans e1.symm.map_zero.symm)
    exact ht (e2.symm.injective (hz.trans e2.symm.map_zero.symm))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.OpenLev
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.openLev :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ φ : UA L n → V, CoefIn φ π →
        ∃ U : Subgroup (UA L n), IsOpen {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} ∧ ∀ u ∈ U, ∀ g, φ (g * u) = φ g := by
  intro L _ _ _ n V _ _ _ π hπ φ hc
  let U : Subgroup (UA L n) :=
    { carrier := {u | ∀ g, φ (g * u) = φ g}
      one_mem' := fun g => by rw [mul_one]
      mul_mem' := fun {a b} ha hb g => by rw [← mul_assoc, hb, ha]
      inv_mem' := fun {a} ha g => by rw [← ha, inv_mul_cancel_right] }
  refine ⟨U, ?_, fun u hu => hu⟩
  let b := Module.finBasis ℂ V
  have e : {x : finU (E := L) (n := n) | (x : UA L n) ∈ U} = ⋂ i, {k : finU (E := L) (n := n) | RU L n k (b.coord i ∘ φ) = b.coord i ∘ φ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun h i => funext fun g => congrArg (b.coord i) (h g), fun h g => b.ext_elem fun i => congrFun (h i) g⟩
  rw [e]
  exact isOpen_iInter_of_finite fun i => (hπ.aut _ (hc _)).level
end
