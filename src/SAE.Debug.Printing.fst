module SAE.Debug.Printing

open Comparse
open DY.Core
open DY.Lib
open SAE.Protocol.Total
open SAE.Protocol.Stateful

(*** Convert SAE Messages to String ***)

val message_to_string: bytes -> option string
let message_to_string frame_bytes =
  let? frame = parse auth_frame frame_bytes in
  match frame.body with
  | Commit msg -> (
    Some (Printf.sprintf "SAE Commit[sa=%s, da=%s, status=%d, group=%d, scalar=(%s), element=(%s)]"
      frame.sa frame.da frame.status msg.group (bytes_to_string msg.scalar) (bytes_to_string msg.element))
  )
  | Confirm msg -> (
    Some (Printf.sprintf "SAE Confirm[sa=%s, da=%s, status=%d, send_confirm=%d, confirm=(%s)]"
      frame.sa frame.da frame.status msg.send_confirm (bytes_to_string msg.confirm))
  )

(*** Convert SAE States to String ***)

val confirmed_data_to_string: confirmed_data -> string
let confirmed_data_to_string st =
  Printf.sprintf "peer=%s, group=%d, scalar=(%s), element=(%s), peer_scalar=(%s), peer_element=(%s), kck=(%s), pmk=(%s), sc=%d, rc=%d"
    st.peer st.group (bytes_to_string st.scalar) (bytes_to_string st.element)
    (bytes_to_string st.peer_scalar) (bytes_to_string st.peer_element)
    (bytes_to_string st.kck) (bytes_to_string st.pmk) st.sc st.rc

val instance_to_string: bytes -> option string
let instance_to_string sess_bytes =
  let? sess = parse sae_instance sess_bytes in
  match sess with
  | Committed st -> (
    Some (Printf.sprintf "Committed[peer=%s, group=%d, pwe=(%s), rand=(%s), scalar=(%s), element=(%s), sc=%d, rc=%d]"
      st.peer st.group (bytes_to_string st.pwe) (bytes_to_string st.rand)
      (bytes_to_string st.scalar) (bytes_to_string st.element) st.sc st.rc)
  )
  | Confirmed st -> (
    Some (Printf.sprintf "Confirmed[%s]" (confirmed_data_to_string st))
  )
  | Accepted st -> (
    Some (Printf.sprintf "Accepted[%s]" (confirmed_data_to_string st))
  )

val passwords_to_string: list (map_elem password_key password_value) -> string
let rec passwords_to_string m =
  match m with
  | [] -> ""
  | hd :: tl -> (
    (passwords_to_string tl) ^
    Printf.sprintf "%s = (%s)," hd.key.peer (bytes_to_string hd.value.password)
  )

val passwords_state_to_string: bytes -> option string
let passwords_state_to_string content_bytes =
  let? state = parse (map password_key password_value) content_bytes in
  Some (Printf.sprintf "[%s]" (passwords_to_string state.key_values))

val instance_ref_to_string: instance_ref -> string
let instance_ref_to_string inst =
  match inst with
  | NoInstance -> "none"
  | SomeInstance sess_id -> Printf.sprintf "%d" sess_id.the_id

val database_to_string: list (map_elem database_key database_value) -> string
let rec database_to_string m =
  match m with
  | [] -> ""
  | hd :: tl -> (
    (database_to_string tl) ^
    Printf.sprintf "%s = (unaccepted=%s, accepted=%s),"
      hd.key.peer (instance_ref_to_string hd.value.unaccepted) (instance_ref_to_string hd.value.accepted)
  )

val database_state_to_string: bytes -> option string
let database_state_to_string content_bytes =
  let? state = parse (map database_key database_value) content_bytes in
  Some (Printf.sprintf "[%s]" (database_to_string state.key_values))

(*** Convert SAE Events to String ***)

val event_to_string: bytes -> option string
let event_to_string event_bytes =
  let? ev = parse sae_event event_bytes in
  match ev with
  | EvCommitted sta peer scalar element -> (
    Some (Printf.sprintf "Committed[sta=%s, peer=%s, scalar=(%s), element=(%s)]"
      sta peer (bytes_to_string scalar) (bytes_to_string element))
  )
  | EvConfirmed sta peer scalar element peer_scalar peer_element pmk -> (
    Some (Printf.sprintf "Confirmed[sta=%s, peer=%s, scalar=(%s), element=(%s), peer_scalar=(%s), peer_element=(%s), pmk=(%s)]"
      sta peer (bytes_to_string scalar) (bytes_to_string element)
      (bytes_to_string peer_scalar) (bytes_to_string peer_element) (bytes_to_string pmk))
  )
  | EvAuth sta peer scalar element peer_scalar peer_element pmk -> (
    Some (Printf.sprintf "Auth[sta=%s, peer=%s, scalar=(%s), element=(%s), peer_scalar=(%s), peer_element=(%s), pmk=(%s)]"
      sta peer (bytes_to_string scalar) (bytes_to_string element)
      (bytes_to_string peer_scalar) (bytes_to_string peer_element) (bytes_to_string pmk))
  )
  | EvFail sta peer -> (
    Some (Printf.sprintf "Fail[sta=%s, peer=%s]" sta peer)
  )
  | EvDel sta peer -> (
    Some (Printf.sprintf "Del[sta=%s, peer=%s]" sta peer)
  )

val sae_trace_to_string_printers: trace_to_string_printers
let sae_trace_to_string_printers =
  trace_to_string_printers_builder
    message_to_string
    [
      (local_state_sae_instance.tag, instance_to_string);
      (map_types_passwords.tag, passwords_state_to_string);
      (map_types_database.tag, database_state_to_string);
    ]
    [(event_sae_event.tag, event_to_string)]
