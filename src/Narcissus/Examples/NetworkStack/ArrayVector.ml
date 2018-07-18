type idx_t = int

let zero _ = 0
let succ (_, n) = Pervasives.succ n

type 'a storage_t =
  { version: int;
    data: 'a array;
    latest_version: int ref }

let of_array (arr: 'a array) : 'a storage_t =
  { version = 0;
    data = arr;
    latest_version = ref 0 }

let to_array (arr: 'a storage_t) : 'a array =
  arr.data

let destruct_idx _ _ _ =
  failwith "Not implemented: ArrayVector.destruct_idx"

let destruct_storage _ _ _ =
  failwith "Not implemented: ArrayVector.destruct_storage"

let throw_if_stale (fn: string) (arr: 'a storage_t) =
  if arr.version <> !(arr.latest_version) then
    failwith (Printf.sprintf "ArrayVector: Array version mismatch in '%s': %d != %d."
                fn arr.version !(arr.latest_version))

let length (arr: 'a storage_t) =
  Array.length arr.data

let hd (_: int) (arr: 'a storage_t) : 'a =
  throw_if_stale "hd" arr;
  Array.unsafe_get arr.data 0

let tl (_: int) (arr: 'a storage_t) : 'a storage_t =
  throw_if_stale "tl" arr;
  of_array (Array.init (Array.length arr.data - 1) (fun i -> arr.data.(i + 1)))

let index (_: int) (_: int) (x: 'a) (arr: 'a storage_t) : idx_t option =
  throw_if_stale "index" arr;
  let rec loop x arr i =
    if i >= Array.length arr then None
    else if arr.(i) = x then Some i
    else loop x arr (i + 1)
  in loop x arr.data 0

let nth _ (arr: 'a storage_t) (idx: idx_t) : 'a =
  throw_if_stale "nth" arr;
  Array.unsafe_get arr.data idx

let nth_opt _ (arr: 'a storage_t) (idx: idx_t) : 'a option =
  throw_if_stale "nth_opt" arr;
  if 0 <= idx && idx < Array.length arr.data then
    Some (Array.unsafe_get arr.data idx)
  else None

let set_nth _ (arr: 'a storage_t) (idx: idx_t) (x: 'a) : 'a storage_t =
  throw_if_stale "set_nth'" arr;
  incr arr.latest_version;
  Array.unsafe_set arr.data idx x;
  { version = !(arr.latest_version);
    latest_version = arr.latest_version;
    data = arr.data }

let fold_left_pair (f: 'a -> 'a -> 'b -> 'a) _ n (arr: 'a storage_t) (init: 'b) (pad: 'a) =
  let rec loop f arr acc pad len offset =
    if offset >= len then
      acc
    else if offset = len - 1  then
      f (arr.data.(offset)) pad acc
    else
      let acc = f (Array.unsafe_get arr.data offset)
                  (Array.unsafe_get arr.data (offset + 1))
                  acc in
      loop f arr acc pad len (offset  + 2)
  in loop f arr init pad (min n (Array.length arr.data)) 0

let append _ _ (arr1: 'a storage_t) (arr2: 'a storage_t) : 'a storage_t =
  throw_if_stale "append" arr1;
  throw_if_stale "append" arr2;
  of_array (Array.append arr1.data arr2.data)

let to_list _ (arr: 'a storage_t) =
  throw_if_stale "to_list" arr;
  Array.to_list arr.data

let cons ((hd, _, tl): ('a * 'b * 'a storage_t)) : 'a storage_t =
  throw_if_stale "cons" tl;
  of_array (Array.append (Array.make 1 hd) tl.data)

let empty () : 'a storage_t =
  of_array [| |]