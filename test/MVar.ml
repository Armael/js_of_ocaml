module Sched = struct
  effect Fork    : (unit -> unit) -> unit
  effect Yield   : unit

  type 'a cont = ('a,unit) continuation
    effect Suspend : ('a cont -> unit) -> 'a
    effect Resume  : ('a cont * 'a) -> unit

  let run main =
    let run_q = Queue.create () in
    let enqueue t v =
      Queue.push (fun () -> continue t v) run_q
    in
    let rec dequeue () =
      if Queue.is_empty run_q then ()
      else Queue.pop run_q ()
    in
    let rec spawn f =
      match f () with
      | () -> dequeue ()
      | effect Yield k -> enqueue k (); dequeue ()
      | effect (Fork f) k -> enqueue k (); spawn f
      | effect (Suspend f) k -> f k; dequeue ()
      | effect (Resume (k', v)) k ->
        enqueue k' v; continue k ()
    in
    spawn main

  let fork f = perform (Fork f)
  let yield () = perform Yield
  let suspend f = perform (Suspend f)
  let resume (k,v) = perform (Resume (k,v))
end

module MVar = struct
  module type S = sig
    type 'a t
    val create       : 'a -> 'a t
    val create_empty : unit -> 'a t
    val put       : 'a -> 'a t -> unit
    val take      : 'a t -> 'a
  end

  module type SCHED = sig
    type 'a cont
    effect Suspend : ('a cont -> unit) -> 'a
      effect Resume  : ('a cont * 'a) -> unit
  end

  module Make (S : SCHED) : S = struct

  (** The state of mvar is either [Full v q] filled with value [v] and a queue
      [q] of threads waiting to fill the mvar, or [Empty q], with a queue [q] of
      threads waiting to empty the mvar. *)
    type 'a mv_state =
    | Full  of 'a * ('a * unit S.cont) Queue.t
    | Empty of 'a S.cont Queue.t

    type 'a t = 'a mv_state ref

    let create_empty () = ref (Empty (Queue.create ()))

    let create v = ref (Full (v, Queue.create ()))

    let suspend f = perform @@ S.Suspend f
    let resume (a,b) = perform @@ S.Resume (a,b)

    let put v mv =
      match !mv with
      | Full (v', q) -> suspend (fun k -> Queue.push (v,k) q)
      | Empty q ->
        if Queue.is_empty q then
          mv := Full (v, Queue.create ())
        else
          let t = Queue.pop q in
          resume (t, v)

    let take mv =
      match !mv with
      | Empty q -> suspend (fun k -> Queue.push k q)
      | Full (v, q) ->
        if Queue.is_empty q then
          (mv := Empty (Queue.create ()); v)
        else
          let (v', t) = Queue.pop q in
          (mv := Full (v', q);
           resume (t, ());
           v)
  end
end

module M = MVar.Make (Sched)
