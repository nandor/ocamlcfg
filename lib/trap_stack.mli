(* CR mshinwell: Please add file header and an explanation of what this
   module is doing (ideally with comments for each function below). *)
(* CR xclerc: the header is missing. *)

type t

exception Unresolved

val emp : t

val unknown : unit -> t

val pop : t -> t

val push : t -> Label.t -> t

(** Returns list representation of stack [t], with the head of the list
    representing the top of the stack. Raises [Unresolved] if the canonical
    representation of [t] contains any [Pop] or [Link] or [Unknown]. Does not
    terminate if [t] contains a cycle. *)
val to_list_exn : t -> Label.t list

(* CR mshinwell: Document which is the "top" of the stack. *)
(** Returns the top of the stack [t], or [None] if [t] is empty. Raises
    [Unresolved] if [t] cannot be resolved. *)
val top_exn : t -> Label.t option

val unify : t -> t -> unit

val print : t -> unit

(* debug print *)
val print_pair : string -> t -> t -> unit
