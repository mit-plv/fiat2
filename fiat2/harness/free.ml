(* The names a program reads without binding.

   A workload has to supply exactly these: an environment entry for every
   free EVar and a store entry for every free ELoc.  Reading them off the
   term rather than off the Rocq file means the generators cannot drift away
   from the programs they feed. *)

open Extracted

module S = Set.Make (String)

let rec expr (bound : S.t) (e : expr) : S.t * S.t =
  (* (free variables, free locations) *)
  let union2 (a, b) (c, d) = (S.union a c, S.union b d) in
  let none = (S.empty, S.empty) in
  match e with
  | EVar x -> ((if S.mem x bound then S.empty else S.singleton x), S.empty)
  | ELoc x -> (S.empty, S.singleton x)
  | EAtom _ -> none
  | EUnop (_, a) | EACFold (_, a) | EACIFold (_, a) | EAccess (a, _)
  | ESort (_, a) | EBagOf a | ESetOf a -> expr bound a
  | EBinop (_, a, b) -> union2 (expr bound a) (expr bound b)
  | ETernop (_, a, b, c) | EIf (a, b, c) ->
      union2 (expr bound a) (union2 (expr bound b) (expr bound c))
  | ELet (a, x, b) -> union2 (expr bound a) (expr (S.add x bound) b)
  | EFlatmap (_, a, x, b) -> union2 (expr bound a) (expr (S.add x bound) b)
  | EFold (a, b, x, y, c) ->
      union2 (expr bound a)
        (union2 (expr bound b) (expr (S.add y (S.add x bound)) c))
  | EOptMatch (a, b, x, c) ->
      union2 (expr bound a) (union2 (expr bound b) (expr (S.add x bound) c))
  | ERecord l -> List.fold_left (fun acc (_, a) -> union2 acc (expr bound a)) none l

(* A location is free in a command when it is read, or assigned, outside the
   CLetMut that introduces it. *)
let rec command (bound : S.t) (mut : S.t) (c : command) : S.t * S.t =
  let union2 (a, b) (c, d) = (S.union a c, S.union b d) in
  let drop x (v, l) = (v, S.remove x l) in
  match c with
  | CSkip -> (S.empty, S.empty)
  | CSeq (a, b) -> union2 (command bound mut a) (command bound mut b)
  | CLet (e, x, a) -> union2 (expr bound e) (command (S.add x bound) mut a)
  | CLetMut (e, x, a) ->
      union2 (expr bound e) (drop x (command bound (S.add x mut) a))
  | CAssign (x, e) ->
      union2 ((if S.mem x mut then (S.empty, S.empty) else (S.empty, S.singleton x)))
        (expr bound e)
  | CIf (e, a, b) ->
      union2 (expr bound e) (union2 (command bound mut a) (command bound mut b))
  | CForeach (e, x, a) -> union2 (expr bound e) (command (S.add x bound) mut a)

let of_command (c : command) : string list * string list =
  let v, l = command S.empty S.empty c in
  (S.elements v, S.elements l)
