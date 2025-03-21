abstype 'a oneshot = Oneshot of 'a option Unsynchronized.ref
with
  fun new_oneshot () = Oneshot (Unsynchronized.ref NONE)
  fun new_oneshots n = List.tabulate (n, (fn _ => new_oneshot ()))
  exception ONESHOT_ALREADY_SET
  fun set_oneshot (Oneshot rf, v) =
    (case !rf
       of SOME _ => raise ONESHOT_ALREADY_SET
        | NONE => (rf := SOME v))
  fun get_oneshot' (Oneshot rf) = !rf
  val get_oneshot = the o get_oneshot'
end

(*allowing one to construct a tree top-down gradually, leaving
  some leaves unknown for now and set them later using their references*)
datatype 'a gradual_tree = GRDTREE of 'a * 'a gradual_tree oneshot list 
