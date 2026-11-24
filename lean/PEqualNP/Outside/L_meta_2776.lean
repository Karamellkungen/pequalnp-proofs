import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_2776_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev B := BitVec 24

def gv (g : Gate) (w : List B) : B :=
  match g.op, g.inputs with
  | .and, [] => BitVec.allOnes 24
  | .or, [] => 0
  | .and, [a] => w.getD a 0
  | .or, [a] => w.getD a 0
  | .and, a :: b :: _ => w.getD a 0 &&& w.getD b 0
  | .or, a :: b :: _ => w.getD a 0 ||| w.getD b 0
  | _, _ => 0

def run : List Gate → List B → List B
  | [], w => w
  | g :: gs, w => run gs (w ++ [gv g w])

def Good (seed fresh : List B) : Prop :=
  ∀ (i : ℕ) (hi : i < fresh.length),
    fresh[i] ∉ seed ++ fresh.take i ∧
      ∃ a ∈ seed ++ fresh.take i, ∃ b ∈ seed ++ fresh.take i,
        fresh[i] = a &&& b ∨ fresh[i] = a ||| b

lemma get_mem (w seed : List B) (hw : ∀ a ∈ w, a ∈ seed)
    (hz : (0 : B) ∈ seed) (i : ℕ) : w.getD i 0 ∈ seed := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hw _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hz

lemma gate_step (g : Gate) (w seed : List B)
    (hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hw : ∀ a ∈ w, a ∈ seed) (hz : (0 : B) ∈ seed)
    (ho : BitVec.allOnes 24 ∈ seed) :
    gv g w ∈ seed ∨ ∃ a ∈ seed, ∃ b ∈ seed,
      gv g w = a &&& b ∨ gv g w = a ||| b := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with hm | hm <;>
    rcases hs : g.inputs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simpa [gv, hm, hs] using Or.inl ho
  · simpa [gv, hm, hs] using Or.inl (get_mem w seed hw hz a)
  · exact Or.inr ⟨_, get_mem w seed hw hz a, _, get_mem w seed hw hz b,
      Or.inl (by simp [gv, hm, hs])⟩
  · simpa [gv, hm, hs] using Or.inl hz
  · simpa [gv, hm, hs] using Or.inl (get_mem w seed hw hz a)
  · exact Or.inr ⟨_, get_mem w seed hw hz a, _, get_mem w seed hw hz b,
      Or.inr (by simp [gv, hm, hs])⟩

lemma good_cons {seed fresh : List B} {v : B}
    (hv : v ∉ seed)
    (hb : ∃ a ∈ seed, ∃ b ∈ seed, v = a &&& b ∨ v = a ||| b)
    (hf : Good (seed ++ [v]) fresh) : Good seed (v :: fresh) := by
  intro i hi
  cases i with
  | zero => simpa using And.intro hv hb
  | succ i =>
    have h := hf i (by simpa using hi)
    simpa [List.take_succ_cons, List.append_assoc] using h

lemma extract (gs : List Gate) (w seed : List B)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hw : ∀ a ∈ w, a ∈ seed) (hz : (0 : B) ∈ seed)
    (ho : BitVec.allOnes 24 ∈ seed) :
    ∃ fresh : List B, fresh.length ≤ gs.length ∧ Good seed fresh ∧
      ∀ a ∈ run gs w, a ∈ seed ++ fresh := by
  induction gs generalizing w seed with
  | nil =>
    refine ⟨[], by simp, ?_, ?_⟩
    · intro i hi; simp at hi
    · simpa [run] using hw
  | cons g gs ih =>
    have hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g hg => hm g (List.mem_cons_of_mem _ hg)
    by_cases hv : gv g w ∈ seed
    · obtain ⟨fresh, hlen, hf, hout⟩ := ih (w ++ [gv g w]) seed hgs
        (by simpa only [List.mem_append, List.mem_singleton] using
          (fun a h => h.elim (hw a) (fun e => e ▸ hv))) hz ho
      exact ⟨fresh, by simpa using hlen.trans (Nat.le_succ _), hf, hout⟩
    · have hb := (gate_step g w seed (hm g (by simp)) hw hz ho).resolve_left hv
      obtain ⟨fresh, hlen, hf, hout⟩ := ih (w ++ [gv g w]) (seed ++ [gv g w]) hgs
        (by
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact List.mem_append_left _ (hw a ha)
          · exact List.mem_append_right _ ha)
        (List.mem_append_left _ hz) (List.mem_append_left _ ho)
      refine ⟨gv g w :: fresh, by simpa using Nat.succ_le_succ hlen,
        good_cons hv hb hf, ?_⟩
      simpa [run, List.append_assoc] using hout

lemma read_bit (w : List B) (i : ℕ) (r : Fin 24) :
    (w.map (fun b => b[r.val])).getD i false = (w.getD i 0)[r.val] := by
  simpa using (List.getD_map (l := w) (d := (0 : B)) (n := i)
    (fun b => b[r.val]))

lemma gate_bit (g : Gate) (w : List B) (r : Fin 24)
    (hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    (gv g w)[r.val] =
      g.op.eval (g.inputs.map fun i => (w.map (fun b => b[r.val])).getD i false) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with hm | hm <;>
    rcases hs : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  all_goals try (simp [hs] at hlen)
  all_goals simp only [gv, hm, hs, GateOp.eval, List.map_nil, List.map_cons,
    List.all_nil, List.all_cons, List.any_nil, List.any_cons, id_eq,
    Bool.and_true, Bool.or_false, BitVec.getElem_and, BitVec.getElem_or,
    BitVec.getElem_allOnes, read_bit]
  all_goals simp

lemma run_bits (gs : List Gate) (w : List B) (r : Fin 24)
    (hm : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (run gs w).map (fun b => b[r.val]) =
      (Circuit.mk gs 0).wires (w.map (fun b => b[r.val])) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run, ih _ (fun g hg => hm g (List.mem_cons_of_mem _ hg))]
    simp only [List.map_append, List.map_cons, List.map_nil, Circuit.wires,
      List.foldl_cons, gate_bit g w r (hm g (by simp)).1 (hm g (by simp)).2]

def samples : List ℕ :=
  [3, 6, 12, 17, 24, 33, 42, 50, 66, 69, 104, 116, 132, 138, 160, 201,
   208, 261, 264, 276, 288, 320, 385, 402]

def positives : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320]

def inputs : List B :=
  [4358697, 8397251, 662022, 304212, 8980632, 1068256, 2199296,
   12709888, 16646144, 13339321]

def seed : List B := 0 :: BitVec.allOnes 24 :: inputs

def target : B := 3428671

lemma inputs_bits (r : Fin 24) :
    inputs.map (fun b => b[r.val]) =
      List.ofFn (fun j : Fin 9 => (samples.getD r.val 0).testBit j.val) ++
        [(samples.getD r.val 0).testBit 0 || (samples.getD r.val 0).testBit 4] := by
  fin_cases r <;> decide

lemma target_bits (r : Fin 24) :
    target[r.val] = decide (samples.getD r.val 0 ∈ positives) := by
  fin_cases r <;> decide

end PEqualNP.Outside.L_meta_2776_aux


theorem PEqualNP.Outside.L_meta_2776 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (42 : ℕ), (50 : ℕ), (66 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (132 : ℕ), (138 : ℕ), (160 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (264 : ℕ), (276 : ℕ), (288 : ℕ), (320 : ℕ), (385 : ℕ), (402 : ℕ)],         have x5 : Fin (9 : ℕ) → Bool := fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5;         x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ))]) = Decidable.decide (x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)])) →       have x4 : List (BitVec (24 : ℕ)) := [(0 : BitVec (24 : ℕ)), (16777215 : BitVec (24 : ℕ)), (4358697 : BitVec (24 : ℕ)), (8397251 : BitVec (24 : ℕ)), (662022 : BitVec (24 : ℕ)), (304212 : BitVec (24 : ℕ)), (8980632 : BitVec (24 : ℕ)), (1068256 : BitVec (24 : ℕ)), (2199296 : BitVec (24 : ℕ)), (12709888 : BitVec (24 : ℕ)), (16646144 : BitVec (24 : ℕ)), (13339321 : BitVec (24 : ℕ))];       ∃ (x5 : List (BitVec (24 : ℕ))), x5.length ≤ x1.size ∧ (∀ (x6 : ℕ) (x7 : x6 < x5.length), x5[x6] ∉ x4 ++ List.take x6 x5 ∧ ∃ x8 ∈ x4 ++ List.take x6 x5, ∃ x9 ∈ x4 ++ List.take x6 x5, x5[x6] = x8 &&& x9 ∨ x5[x6] = x8 ||| x9) ∧ (3428671 : BitVec (24 : ℕ)) ∈ x4 ++ x5 := by
  intro C hm he
  change ∃ fresh : List PEqualNP.Outside.L_meta_2776_aux.B,
    fresh.length ≤ C.size ∧
      PEqualNP.Outside.L_meta_2776_aux.Good PEqualNP.Outside.L_meta_2776_aux.seed fresh ∧
      PEqualNP.Outside.L_meta_2776_aux.target ∈ PEqualNP.Outside.L_meta_2776_aux.seed ++ fresh
  obtain ⟨fresh, hlen, hgood, hfinal⟩ :=
    PEqualNP.Outside.L_meta_2776_aux.extract C.gates
      PEqualNP.Outside.L_meta_2776_aux.inputs PEqualNP.Outside.L_meta_2776_aux.seed
      (fun g hg => (hm g hg).1)
      (by intro a ha; simp [PEqualNP.Outside.L_meta_2776_aux.seed, ha])
      (by simp [PEqualNP.Outside.L_meta_2776_aux.seed])
      (by simp [PEqualNP.Outside.L_meta_2776_aux.seed])
  refine ⟨fresh, hlen, hgood, ?_⟩
  have heq : (PEqualNP.Outside.L_meta_2776_aux.run C.gates
      PEqualNP.Outside.L_meta_2776_aux.inputs).getD C.output 0 =
      PEqualNP.Outside.L_meta_2776_aux.target := by
    apply BitVec.eq_of_getElem_eq
    intro r hr
    let i : Fin 24 := ⟨r, hr⟩
    have hs : PEqualNP.Outside.L_meta_2776_aux.samples.getD r 0 ∈
        PEqualNP.Outside.L_meta_2776_aux.samples := by
      rw [List.getD_eq_getElem _ _ (by simpa [PEqualNP.Outside.L_meta_2776_aux.samples] using hr)]
      exact List.getElem_mem _
    have hx := he (PEqualNP.Outside.L_meta_2776_aux.samples.getD r 0) hs
    change C.eval (List.ofFn (fun j : Fin 9 =>
        (PEqualNP.Outside.L_meta_2776_aux.samples.getD r 0).testBit j.val) ++
      [(PEqualNP.Outside.L_meta_2776_aux.samples.getD r 0).testBit 0 ||
       (PEqualNP.Outside.L_meta_2776_aux.samples.getD r 0).testBit 4]) =
      decide (PEqualNP.Outside.L_meta_2776_aux.samples.getD r 0 ∈
        PEqualNP.Outside.L_meta_2776_aux.positives) at hx
    rw [← PEqualNP.Outside.L_meta_2776_aux.inputs_bits i] at hx
    change ((PEqualNP.CircuitLowerBounds.Circuit.mk C.gates 0).wires
      (PEqualNP.Outside.L_meta_2776_aux.inputs.map (fun b => b[i.val]))).getD C.output false = _ at hx
    rw [← PEqualNP.Outside.L_meta_2776_aux.run_bits C.gates
      PEqualNP.Outside.L_meta_2776_aux.inputs i hm,
      PEqualNP.Outside.L_meta_2776_aux.read_bit] at hx
    exact hx.trans (PEqualNP.Outside.L_meta_2776_aux.target_bits i).symm
  have hout := PEqualNP.Outside.L_meta_2776_aux.get_mem _ _ hfinal
    (by simp [PEqualNP.Outside.L_meta_2776_aux.seed]) C.output
  rwa [heq] at hout
