import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27249_aux

open PEqualNP.CircuitLowerBounds

private def Shape (n : Nat) (g : Gate) : Prop :=
  (g.op = .not ∧ ∃ a, a < n ∧ g.inputs = [a]) ∨
    ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ b < n ∧ g.inputs = [a, b])

private theorem slot_arity_bound (gs : List Gate)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length ∧
      ((gs.flatMap Gate.inputs).length = 2 * gs.length →
        ∀ g ∈ gs, g.inputs.length = 2) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    obtain ⟨ht, he⟩ := ih (fun k hk => h k (List.mem_cons_of_mem _ hk))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    constructor
    · omega
    · intro hsum k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · omega
      · exact he (by omega) k hk

private theorem slot_rigidity (gs : List Gate) (h12 : gs.length ≤ 12) (hlen : 2 ≤ gs.length)
    (hshape : ∀ j : Fin gs.length, Shape (9+j.val) (gs.get j))
    (hlive : ∀ j : Fin gs.length, j.val+1 < gs.length →
      ∃ k : Fin gs.length, j.val < k.val ∧ 9+j.val ∈ (gs.get k).inputs)
    (hraw : ∀ i < 9, 1 ≤ (gs.flatMap Gate.inputs).count i)
    (hmore : ∀ i ∈ ([0,1,3,4] : List Nat), 2 ≤ (gs.flatMap Gate.inputs).count i) :
    (∀ j : Fin gs.length, (gs.get j).op = GateOp.and ∨ (gs.get j).op = GateOp.or) ∧
    (∀ i, i < 9 + gs.length - 1 → i ∉ ([0,1,3,4] : List Nat) →
      (gs.flatMap Gate.inputs).count i ≤ 1) := by
  let required := List.range (9 + gs.length - 1) ++ [0, 1, 3, 4]
  have hused : ∀ i < 9 + gs.length - 1, 1 ≤ (gs.flatMap Gate.inputs).count i := by
    intro i hi
    by_cases hir : i < 9
    · exact hraw i hir
    · let j : Fin gs.length := ⟨i - 9, by omega⟩
      obtain ⟨k, _, hk⟩ := hlive j (by dsimp [j]; omega)
      have hj : 9 + j.val = i := by dsimp [j]; omega
      rw [hj] at hk
      exact List.count_pos_iff.mpr
        (List.mem_flatMap.mpr ⟨gs.get k, List.mem_iff_get.mpr ⟨k, rfl⟩, hk⟩)
  have hcount : ∀ i, required.count i ≤ (gs.flatMap Gate.inputs).count i := by
    intro i
    by_cases hm : i ∈ ([0, 1, 3, 4] : List Nat)
    · have hone : ([0, 1, 3, 4] : List Nat).count i = 1 :=
        List.count_eq_one_of_mem (by decide) hm
      have hmore' := hmore i hm
      simp only [required, List.count_append, List.count_range, hone]
      split <;> omega
    · simp only [required, List.count_append, List.count_range,
        List.count_eq_zero_of_not_mem hm, Nat.add_zero]
      split
      · exact hused i (by assumption)
      · exact Nat.zero_le _
  obtain ⟨ws, hperm, hsub⟩ := List.subperm_iff.mp (List.subperm_iff_count.mpr hcount)
  have hrequired : required.length = gs.length + 12 := by
    simp [required]
    omega
  have hlower : required.length ≤ (gs.flatMap Gate.inputs).length :=
    hsub.length_le.trans_eq hperm.length_eq
  obtain ⟨hupper, hexact⟩ := slot_arity_bound gs (by
    intro g hg
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
    rcases hshape j with ⟨_, a, _, hi⟩ | ⟨_, a, b, _, _, hi⟩ <;> rw [hi] <;> simp)
  have hfull : (gs.flatMap Gate.inputs).length = 2 * gs.length := by omega
  have hws : required = ws := hsub.eq_of_length_le (by have := hperm.length_eq; omega)
  have hcounts_eq := (hws ▸ hperm : required.Perm (gs.flatMap Gate.inputs)).count_eq
  refine ⟨?_, ?_⟩
  · intro j
    rcases hshape j with ⟨_, a, _, ha⟩ | ⟨hop, _⟩
    · have hg := hexact hfull (gs.get j) (List.mem_iff_get.mpr ⟨j, rfl⟩)
      rw [ha] at hg
      simp at hg
    · exact hop
  · intro i hi hm
    rw [← hcounts_eq i]
    simp only [required, List.count_append, List.count_range, ite_eq_left hi,
      List.count_eq_zero_of_not_mem hm, Nat.add_zero, Nat.le_refl]

-- Labels distinguish constants, variables, and binary operations.
private abbrev RTree := BinaryTree ((Bool ⊕ Fin 4) ⊕ Bool)

namespace RTree

private def const (b : Bool) : RTree := .node (.inl (.inl b)) .nil .nil
private def var (i : Fin 4) : RTree := .node (.inl (.inr i)) .nil .nil
private def branch (b : Bool) (l r : RTree) : RTree := .node (.inr b) l r

private def eval : RTree → (Fin 4 → Bool) → Bool
  | .nil, _ => false
  | .node (.inl (.inl b)) _ _, _ => b
  | .node (.inl (.inr i)) _ _, x => x i
  | .node (.inr true) l r, x => eval l x && eval r x
  | .node (.inr false) l r, x => eval l x || eval r x

private def leaves : RTree → List (Fin 4)
  | .nil | .node (.inl (.inl _)) _ _ => []
  | .node (.inl (.inr i)) _ _ => [i]
  | .node (.inr _) l r => leaves l ++ leaves r

private theorem eval_congr_leaves (t : RTree) (x y : Fin 4 → Bool)
    (h : ∀ i ∈ t.leaves, x i = y i) : t.eval x = t.eval y := by
  induction t with
  | nil => rfl
  | node label l r ihl ihr =>
    rcases label with (b | i) | b
    · rfl
    · exact h i (by simp [leaves])
    · cases b <;> simp only [eval, leaves, List.mem_append] at h ⊢ <;>
        rw [ihl (fun i hi => h i (Or.inl hi)), ihr (fun i hi => h i (Or.inr hi))]

end RTree

private def p4 (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

private def mix (m x y : Fin 4 → Bool) (i : Fin 4) : Bool :=
  if m i then x i else y i

private theorem splitP4 : ∀ (m : Fin 4 → Bool) (b : Bool),
    (∃ i, m i = true) → (∃ i, m i = false) →
      ∃ x y : Fin 4 → Bool, p4 x = b ∧ p4 y = b ∧ p4 (mix m x y) ≠ b := by
  decide +kernel

private def gate (b x y : Bool) : Bool :=
  if b then x && y else x || y

private theorem gate_eq (b x y : Bool) : gate b x y = b ↔ x = b ∧ y = b := by
  cases b <;> cases x <;> cases y <;> decide +kernel

private theorem gate_id_left (b x : Bool) : gate b b x = x := by cases b <;> rfl
private theorem gate_id_right (b x : Bool) : gate b x b = x := by
  cases b <;> cases x <;> rfl

private theorem p4_uniform (b : Bool) : p4 (fun _ => b) = b := by
  cases b <;> rfl

private theorem p4_root (l r : RTree) (b : Bool)
    (ihl : l.leaves.Nodup → (∀ x, l.eval x = p4 x) → False)
    (ihr : r.leaves.Nodup → (∀ x, r.eval x = p4 x) → False)
    (h : (l.leaves ++ r.leaves).Nodup)
    (he : ∀ x, gate b (l.eval x) (r.eval x) = p4 x) : False := by
  obtain ⟨hl, hr, hd⟩ := List.nodup_append.mp h
  have hbase := (gate_eq _ _ _).mp ((he (fun _ => b)).trans (p4_uniform b))
  by_cases el : l.leaves = []
  · apply ihr hr
    intro x
    have hx : l.eval x = b :=
      (l.eval_congr_leaves x (fun _ => b) (by simp [el])).trans hbase.1
    simpa only [hx, gate_id_left] using he x
  by_cases er : r.leaves = []
  · apply ihl hl
    intro x
    have hx : r.eval x = b :=
      (r.eval_congr_leaves x (fun _ => b) (by simp [er])).trans hbase.2
    simpa only [hx, gate_id_right] using he x
  let m : Fin 4 → Bool := fun i => decide (i ∈ l.leaves)
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil l.leaves el
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil r.leaves er
  have ml : ∀ i ∈ l.leaves, m i = true := fun i hi => by simp [m, hi]
  have mr : ∀ i ∈ r.leaves, m i = false := fun i hi => by
    have hn : i ∉ l.leaves := fun hli => hd i hli i hi rfl
    simp [m, hn]
  obtain ⟨x, y, hx, hy, hxy⟩ := splitP4 m b ⟨i, ml i hi⟩ ⟨j, mr j hj⟩
  have hxl := ((gate_eq _ _ _).mp ((he x).trans hx)).1
  have hyr := ((gate_eq _ _ _).mp ((he y).trans hy)).2
  have hmxl : l.eval (mix m x y) = l.eval x :=
    l.eval_congr_leaves _ _ (fun i hi => by simp [mix, ml i hi])
  have hmyr : r.eval (mix m x y) = r.eval y :=
    r.eval_congr_leaves _ _ (fun i hi => by simp [mix, mr i hi])
  apply hxy
  rw [← he, hmxl, hmyr]
  exact (gate_eq _ _ _).mpr ⟨hxl, hyr⟩

private theorem p4_not_read_once (t : RTree) (huniq : t.leaves.Nodup)
    (heval : ∀ x, t.eval x = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3))) : False := by
  change ∀ x, t.eval x = p4 x at heval
  induction t with
  | nil =>
    have hh := heval (fun _ => true)
    contradiction
  | node label l r ihl ihr =>
    rcases label with (b | i) | b
    · have hf := heval (fun _ => false)
      have ht := heval (fun _ => true)
      change b = false at hf
      change b = true at ht
      simp [hf] at ht
    · have hx := heval (fun j => decide (i = j))
      change decide (i = i) = p4 (fun j => decide (i = j)) at hx
      have hsingle : p4 (fun j => decide (i = j)) = false := by
        fin_cases i <;> decide +kernel
      simp [hsingle] at hx
    · cases b
      · exact p4_root l r false ihl ihr huniq heval
      · exact p4_root l r true ihl ihr huniq heval

private def stepVal (g : Gate) (w : Nat → Bool) : Bool :=
  g.op.eval (g.inputs.map w)

private def run {α : Type} (step : Gate → (Nat → α) → α) :
    List Gate → Nat → (Nat → α) → Nat → α
  | [], _, w => w
  | g :: gs, n, w => run step gs (n+1) (Function.update w n (step g w))

private theorem append_value (xs : List Bool) (v : Bool) :
    (fun i => (xs ++ [v]).getD i false) =
      Function.update (fun i => xs.getD i false) xs.length v := by
  funext i
  rcases lt_trichotomy i xs.length with h | rfl | h
  · rw [List.getD_append _ _ _ _ h, Function.update_of_ne (Nat.ne_of_lt h)]
  · rw [Function.update_self, List.getD_append_right _ _ _ _ (by omega)]
    simp
  · rw [Function.update_of_ne (Nat.ne_of_gt h),
      List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private theorem run_bool (gs : List Gate) (xs : List Bool) (o : Nat) :
    run stepVal gs xs.length (fun i => xs.getD i false) o = (Circuit.mk gs o).eval xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change run stepVal gs (xs.length+1) (Function.update _ _ _) o =
      (Circuit.mk gs o).eval (xs ++ [stepVal g (fun i => xs.getD i false)])
    rw [← append_value, ← ih]
    simp

private theorem run_agree (gs : List Gate) (n o : Nat) (a b : Nat → Bool)
    (h : ∀ i ∈ gs.flatMap Gate.inputs ++ [o], a i = b i) :
    run stepVal gs n a o = run stepVal gs n b o := by
  induction gs generalizing n a b with
  | nil => exact h o (by simp)
  | cons g gs ih =>
    rw [run, run]
    have hev : stepVal g a = stepVal g b := by
      unfold stepVal
      congr 1
      exact List.map_congr_left (fun i hi => h i (by simp [hi]))
    apply ih
    intro i hi
    by_cases hn : i = n
    · subst i
      simpa using hev
    · rw [Function.update_of_ne hn, Function.update_of_ne hn]
      exact h i (by simpa [List.flatMap_cons, List.append_assoc] using
        List.mem_append_right g.inputs hi)

private def goalFun (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

-- Each high row is a minterm. For a pinned operand it omits the other operand.
private def hiRow (i k : Fin 9) : Bool :=
  ((![273,266,140,266,273,161,98,161,273] : Fin 9 → Nat) i).testBit k.val

private def loRow (i k : Fin 9) : Bool := k != i && hiRow i k

private theorem row_diff : ∀ i : Fin 9, goalFun (hiRow i) ≠ goalFun (loRow i) := by decide +kernel

private def raw (x : Fin 9 → Bool) (i : Nat) : Bool := (List.ofFn x).getD i false

private theorem raw_eq {j : Nat} (x : Fin 9 → Bool) (hj : j < 9) : raw x j = x ⟨j,hj⟩ := by
  unfold raw
  rw [List.getD_eq_getElem _ _ (by simpa), List.getElem_ofFn]

private theorem raw_agree (i : Fin 9) (j : Nat) (h : j ≠ i.val) :
    raw (hiRow i) j = raw (loRow i) j := by
  by_cases hj : j < 9
  · rw [raw_eq _ hj, raw_eq _ hj]
    have hn : (⟨j,hj⟩ : Fin 9) ≠ i := fun e => h (congrArg Fin.val e)
    simp [loRow, hn]
  · unfold raw
    rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)]

private def pinA : Gate := ⟨.and,[0,1]⟩
private def pinB : Gate := ⟨.and,[3,4]⟩

private theorem pin_prefix (gs : List Gate) (ha : gs.head? = some pinA)
    (hb : gs.tail.head? = some pinB) : ∃ s, gs = pinA :: pinB :: s := by
  cases gs with
  | nil => simp at ha
  | cons a gs =>
    have ea : a = pinA := by simpa using ha
    cases gs with
    | nil => simp at hb
    | cons b gs =>
      have eb : b = pinB := by simpa using hb
      exact ⟨gs, by rw [ea,eb]⟩

private theorem raw_count (gs : List Gate) (o : Nat) (ho : 9 ≤ o)
    (h : ∀ x, (Circuit.mk gs o).eval (List.ofFn x) = goalFun x) :
    ∀ i < 9, 1 ≤ (gs.flatMap Gate.inputs).count i := by
  intro i hi
  by_contra! hc
  have hm : i ∉ gs.flatMap Gate.inputs := by simpa [List.count_eq_zero] using (show (gs.flatMap Gate.inputs).count i = 0 by omega)
  let k : Fin 9 := ⟨i,hi⟩
  apply row_diff k
  rw [← h, ← h, ← run_bool, ← run_bool]
  simp only [List.length_ofFn]
  apply run_agree
  intro j hj
  apply raw_agree
  intro e
  subst j
  exact (List.mem_append.mp hj).elim hm (by simp [k]; omega)

private def pinState (w : Nat → Bool) : Nat → Bool :=
  let v := Function.update w 9 (stepVal pinA w)
  Function.update v 10 (stepVal pinB v)

private theorem pinState_new_agree : ∀ i : Fin 9, i.val ∈ ([0,1,3,4] : List Nat) →
    pinState (raw (hiRow i)) 9 = pinState (raw (loRow i)) 9 ∧
    pinState (raw (hiRow i)) 10 = pinState (raw (loRow i)) 10 := by decide +kernel

private theorem pinState_agree (i : Fin 9) (hi : i.val ∈ ([0,1,3,4] : List Nat)) (j : Nat)
    (hj : j ≠ i.val) : pinState (raw (hiRow i)) j = pinState (raw (loRow i)) j := by
  by_cases h9 : j = 9
  · subst j; exact (pinState_new_agree i hi).1
  by_cases h10 : j = 10
  · subst j; exact (pinState_new_agree i hi).2
  simpa [pinState, Function.update_of_ne h9, Function.update_of_ne h10] using raw_agree i j hj

private theorem extra_count (gs : List Gate) (o : Nat) (ho : 9 ≤ o)
    (h : ∀ x, (Circuit.mk (pinA :: pinB :: gs) o).eval (List.ofFn x) = goalFun x) :
    ∀ i ∈ ([0,1,3,4] : List Nat),
      2 ≤ ((pinA :: pinB :: gs).flatMap Gate.inputs).count i := by
  intro i hi
  have hlt : i < 9 := by simp at hi; omega
  have hprefix : ([0,1,3,4] : List Nat).count i = 1 := by
    simp at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  by_contra! hc
  have hc' : ([0,1,3,4] : List Nat).count i + (gs.flatMap Gate.inputs).count i < 2 := by
    change (([0,1,3,4] : List Nat) ++ gs.flatMap Gate.inputs).count i < 2 at hc
    simpa only [List.count_append] using hc
  have hm : i ∉ gs.flatMap Gate.inputs := by simpa [List.count_eq_zero] using (show (gs.flatMap Gate.inputs).count i = 0 by omega)
  let k : Fin 9 := ⟨i,hlt⟩
  apply row_diff k
  rw [← h, ← h, ← run_bool, ← run_bool]
  change run stepVal gs 11 (pinState (raw (hiRow k))) o =
    run stepVal gs 11 (pinState (raw (loRow k))) o
  apply run_agree
  intro j hj
  apply pinState_agree k hi
  intro e
  subst j
  exact (List.mem_append.mp hj).elim hm (by simp [k]; omega)

private def stepTree (g : Gate) (w : Nat → RTree) : RTree :=
  match g.inputs with
  | [a,b] => RTree.branch (if g.op matches .and then true else false) (w a) (w b)
  | _ => RTree.const false

private def BinaryAt (n : Nat) (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ b < n ∧ g.inputs = [a,b]

private theorem binary_head {g : Gate} {gs : List Gate} {n : Nat}
    (h : ∀ j : Fin (g::gs).length, BinaryAt (n+j.val) ((g::gs).get j)) : BinaryAt n g := by
  simpa using h ⟨0, by simp⟩

private theorem binary_tail {g : Gate} {gs : List Gate} {n : Nat}
    (h : ∀ j : Fin (g::gs).length, BinaryAt (n+j.val) ((g::gs).get j)) :
    ∀ j : Fin gs.length, BinaryAt (n+1+j.val) (gs.get j) := by
  intro j
  simpa [Nat.add_assoc, Nat.add_comm 1] using h ⟨j.val+1, by simp⟩

private theorem tree_step_val (w : Nat → RTree) (g : Gate) (n : Nat)
    (h : BinaryAt n g) (x : Fin 4 → Bool) :
    (stepTree g w).eval x = stepVal g (fun i => (w i).eval x) := by
  obtain ⟨hop, a, b, _, _, hin⟩ := h
  unfold stepTree stepVal
  rcases hop with h | h <;> simp [h,hin,RTree.branch,RTree.eval,GateOp.eval]

private theorem tree_step_leaves (w : Nat → RTree) (g : Gate) (n : Nat)
    (h : BinaryAt n g) : (stepTree g w).leaves = g.inputs.flatMap (fun i => (w i).leaves) := by
  obtain ⟨hop, a, b, _, _, hin⟩ := h
  rcases hop with h | h <;> simp [stepTree,h,hin,RTree.branch,RTree.leaves]

private theorem tree_run_val (gs : List Gate) (n o : Nat) (w : Nat → RTree)
    (h : ∀ j : Fin gs.length, BinaryAt (n+j.val) (gs.get j)) (x : Fin 4 → Bool) :
    (run stepTree gs n w o).eval x = run stepVal gs n (fun i => (w i).eval x) o := by
  induction gs generalizing n w with
  | nil => rfl
  | cons g gs ih =>
    rw [run,run, ih _ _ (binary_tail h)]
    congr 2
    funext i
    by_cases hi : i = n
    · subst i
      simp [tree_step_val w g n (binary_head h)]
    · simp [Function.update_of_ne hi]

private theorem nodup_move {α : Type} (ls : List Nat) (n : Nat) (f : Nat → List α)
    (p : List α) (hc : ls.count n ≤ 1) (h : (p ++ ls.flatMap f).Nodup) :
    (ls.flatMap fun j => if j = n then p else f j).Nodup := by
  induction ls with
  | nil => simp
  | cons a ls ih =>
    by_cases e : a = n
    · subst a
      have hn : n ∉ ls := by
        simp at hc
        exact List.count_eq_zero.mp (by omega)
      have he : (ls.flatMap fun j => if j = n then p else f j) = ls.flatMap f := by
        apply List.flatMap_congr
        intro i hi
        have hin : i ≠ n := fun eq => hn (eq ▸ hi)
        simp [hin]
      simp [he] at h ⊢
      exact h.sublist ((List.sublist_append_right (f n) (ls.flatMap f)).append_left p)
    · simp [e] at hc
      simp [e] at h ⊢
      have hp : (p ++ (f a ++ ls.flatMap f)).Perm (f a ++ (p ++ ls.flatMap f)) := by
        simpa only [List.append_assoc] using
          (List.perm_append_comm (l₁ := p) (l₂ := f a)).append_right (ls.flatMap f)
      have h' := hp.nodup_iff.mp h
      -- The updated tail uses only entries from the old tail or the moved block.
      rw [List.nodup_append] at h' ⊢
      refine ⟨h'.1, ih hc h'.2.1, ?_⟩
      intro x hx y hy
      apply h'.2.2 x hx y
      rw [List.mem_flatMap] at hy
      obtain ⟨i,hi,hyi⟩ := hy
      by_cases ei : i = n
      · exact List.mem_append_left _ (by simpa [ei] using hyi)
      · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨i,hi,by simpa [ei] using hyi⟩)

-- Live operands own disjoint variable lists; a step moves both lists into
-- the new wire, which can occur at most once among the remaining operands.
private theorem tree_run_nodup (gs : List Gate) (n o : Nat) (w : Nat → RTree)
    (ho : o+1 = n+gs.length)
    (h : ∀ j : Fin gs.length, BinaryAt (n+j.val) (gs.get j))
    (hc : ∀ i, n ≤ i → i ≤ o → (gs.flatMap Gate.inputs ++ [o]).count i ≤ 1)
    (hw : ((gs.flatMap Gate.inputs ++ [o]).flatMap (fun i => (w i).leaves)).Nodup) :
    (run stepTree gs n w o).leaves.Nodup := by
  induction gs generalizing n w with
  | nil => simpa [run] using hw
  | cons g gs ih =>
    rw [run]
    apply ih (n+1) _ (by simp at ho; omega) (binary_tail h)
    · intro i hi hio
      have hh := hc i (by omega) hio
      simp only [List.flatMap_cons, List.append_assoc, List.count_append] at hh ⊢
      omega
    · have hh := hc n (by omega) (by simp at ho; omega)
      simp only [List.flatMap_cons, List.append_assoc, List.count_append] at hh
      have hlim : (gs.flatMap Gate.inputs ++ [o]).count n ≤ 1 := by
        simp only [List.count_append]; omega
      have hn := nodup_move (gs.flatMap Gate.inputs ++ [o]) n
        (fun i => (w i).leaves) (stepTree g w).leaves hlim (by
          rw [tree_step_leaves w g n (binary_head h), ← List.flatMap_append,
            ← List.append_assoc, ← List.flatMap_cons]
          exact hw)
      simpa [Function.update_apply, apply_ite] using hn

private def seed (i : Nat) : RTree :=
  if i = 5 then RTree.var 0 else if i = 7 then RTree.var 1 else if i = 2 then RTree.var 2 else
    if i = 6 then RTree.var 3 else RTree.const (i == 0 || i == 3 || i == 4)

private def rawIndex (k : Fin 4) : Nat := (![5,7,2,6] : Fin 4 → Nat) k

private theorem count_seed (i : Nat) (k : Fin 4) : (seed i).leaves.count k = if i = rawIndex k then 1 else 0 := by
  fin_cases k <;> simp only [rawIndex] <;>
    by_cases h5 : i = 5 <;> by_cases h7 : i = 7 <;> by_cases h2 : i = 2 <;>
    by_cases h6 : i = 6 <;> simp_all [seed,RTree.const,RTree.var,RTree.leaves]

private theorem seed_nodup (ls : List Nat) (h : ∀ k, ls.count (rawIndex k) ≤ 1) :
    (ls.flatMap (fun i => (seed i).leaves)).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro k
  convert h k using 1
  clear h
  induction ls with
  | nil => simp
  | cons i ls ih =>
    simp only [List.flatMap_cons, List.count_append, count_seed, List.count_cons, ih, beq_iff_eq]
    omega

private def restrictRow (x : Fin 4 → Bool) (i : Fin 9) : Bool := (seed i.val).eval x

private theorem raw_restrict (x : Fin 4 → Bool) : raw (restrictRow x) = fun i => (seed i).eval x := by
  funext i
  by_cases hi : i < 9
  · exact raw_eq _ hi
  · unfold raw
    rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    have h0 : i ≠ 0 := by omega
    have h2 : i ≠ 2 := by omega
    have h3 : i ≠ 3 := by omega
    have h4 : i ≠ 4 := by omega
    have h5 : i ≠ 5 := by omega
    have h6 : i ≠ 6 := by omega
    have h7 : i ≠ 7 := by omega
    simp [seed,RTree.const,RTree.eval,h0,h2,h3,h4,h5,h6,h7]

private theorem restrict_p4 : ∀ x : Fin 4 → Bool,
    goalFun (restrictRow x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)) := by decide +kernel

end PEqualNP.Outside.L_meta_27249_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_27249_aux

theorem PEqualNP.Outside.L_meta_27249 :
¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩) := by
  rintro ⟨⟨gs, o⟩, _, hsize, hcorrect, hout, hshape, _, hlive, hfirst, hsecond⟩
  change gs.length ≤ 12 at hsize
  change o+1 = 9+gs.length at hout
  change ∀ x, (Circuit.mk gs o).eval (List.ofFn x) = goalFun x at hcorrect
  change (∀ j : Fin gs.length, Shape (9+j.val) (gs.get j)) at hshape
  obtain ⟨s, hs⟩ := pin_prefix gs hfirst hsecond
  have hlen : 2 ≤ gs.length := by rw [hs]; simp
  have hoo : 9 ≤ o := by omega
  have hmore : ∀ i ∈ ([0,1,3,4] : List Nat), 2 ≤ (gs.flatMap Gate.inputs).count i := by
    rw [hs] at hcorrect ⊢
    exact extra_count s o hoo hcorrect
  obtain ⟨hops, hsingle⟩ := slot_rigidity gs hsize hlen hshape hlive
    (raw_count gs o hoo hcorrect) hmore
  have hbin (j : Fin gs.length) : BinaryAt (9+j.val) (gs.get j) := by
    rcases hshape j with hn | hb
    · obtain ⟨he, _⟩ := hn
      rcases hops j with hh | hh <;> rw [he] at hh <;> contradiction
    · exact hb
  have hnotread : o ∉ gs.flatMap Gate.inputs := by
    intro hm
    obtain ⟨g, hg, hi⟩ := List.mem_flatMap.mp hm
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
    obtain ⟨_, a, b, hab, hb, he⟩ := hbin j
    change o ∈ (gs.get j).inputs at hi
    rw [he] at hi
    simp at hi
    have hj := j.isLt
    omega
  have hunique (i : Nat) (hi : 9 ≤ i) (hio : i ≤ o) :
      (gs.flatMap Gate.inputs ++ [o]).count i ≤ 1 := by
    rcases eq_or_lt_of_le hio with rfl | hio
    · simp [List.count_eq_zero.mpr hnotread]
    · have hlow : i < 9+gs.length-1 := by omega
      have hexcl : i ∉ ([0,1,3,4] : List Nat) := by simp; omega
      simpa [List.count_cons, show o ≠ i by omega] using hsingle i hlow hexcl
  have hseed (k : Fin 4) : (gs.flatMap Gate.inputs ++ [o]).count (rawIndex k) ≤ 1 := by
    have hi : rawIndex k < 9 := by fin_cases k <;> decide +kernel
    have hexcl : rawIndex k ∉ ([0,1,3,4] : List Nat) := by fin_cases k <;> decide +kernel
    have hlow : rawIndex k < 9+gs.length-1 := by omega
    simpa [List.count_cons, show o ≠ rawIndex k by omega] using hsingle (rawIndex k) hlow hexcl
  let t := run stepTree gs 9 seed o
  have ht : t.leaves.Nodup := tree_run_nodup gs 9 o seed hout hbin hunique (seed_nodup _ hseed)
  apply p4_not_read_once t ht
  intro x
  change (run stepTree gs 9 seed o).eval x = _
  rw [tree_run_val gs 9 o seed hbin, ← raw_restrict]
  calc
    run stepVal gs 9 (raw (restrictRow x)) o =
        (Circuit.mk gs o).eval (List.ofFn (restrictRow x)) := by
          change run stepVal gs 9 (fun i => (List.ofFn (restrictRow x)).getD i false) o = _
          simpa only [List.length_ofFn] using run_bool gs (List.ofFn (restrictRow x)) o
    _ = goalFun (restrictRow x) := hcorrect _
    _ = _ := restrict_p4 x
