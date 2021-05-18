signature JsonUtil =
sig
    exception NotBool of Json.json
    exception NotNumber of Json.json
    exception NotString of Json.json
    exception NotObject of Json.json
    exception FieldNotFound of Json.json * string
    exception NotArray of Json.json
    exception ArrayBounds of Json.json * int
    exception ElemNotFound of Json.json
    val exnMessage : exn -> string
    val asBool : Json.json -> bool
    val asString : Json.json -> string
    val asNumber : Json.json -> Arbnum.num
    val findField : Json.json -> string -> Json.json option
    val lookupField : Json.json -> string -> Json.json
    val hasField : string -> Json.json -> bool
    val testField : string -> (Json.json -> bool) -> Json.json -> bool
    val asArray : Json.json -> Json.json vector
    val arrayMap : (Json.json -> 'a) -> Json.json -> 'a list
    datatype edge
      = SEL of string
      | SUB of int
      | FIND of Json.json -> bool
    type path = edge list
    val get : Json.json * path -> Json.json
end

structure JsonUtil : JsonUtil =
struct

open Json;

exception NotBool of json
exception NotNumber of json
exception NotString of json
exception NotObject of json
exception FieldNotFound of json * string
exception NotArray of json
exception ArrayBounds of json * int
exception ElemNotFound of json

fun exnMessage e = General.exnMessage e

fun asBool (BOOL b) = b
  | asBool jv = raise NotBool jv

fun asNumber (NUMBER i) = i
  | asNumber jv = raise NotNumber jv

fun asString (STRING s) = s
  | asString jv = raise NotString jv

fun findField (OBJECT flds) key =
    let
	fun f [] = NONE
	  | f ((key',jv')::flds) = if key = key' then SOME jv' else f flds
    in
	f flds
    end
  | findField jv _ = raise NotObject jv

fun lookupField jv key =
    case findField jv key
     of SOME jv' => jv'
      | NONE => raise FieldNotFound(jv, key)

fun hasField key (OBJECT flds) = Option.isSome (findField (OBJECT flds) key)
  | hasField _ _ = false

fun testField key pred (OBJECT flds) =
    (case findField (OBJECT flds) key
      of SOME jv => pred jv
       | NONE => false)
  | testField _ _ _ = false

fun asArray (ARRAY lst) = Vector.fromList lst
  | asArray jv = raise NotArray jv

fun arrayMap f (ARRAY lst) = map f lst
  | arrayMap _ jv = raise NotArray jv
    
datatype edge
  = SEL of string
  | SUB of int
  | FIND of json -> bool
type path = edge list

local
    fun get' (jv, []) = jv
      | get' (OBJECT jv, SEL s::p) = get' (lookupField (OBJECT jv) s, p)
      | get' (ARRAY lst, SUB i::p) =
	let
	    val jv = List.nth(lst, i)
		     handle Subscript => raise ArrayBounds(ARRAY lst, i)
	in
	    get' (jv, p)
	end
      | get' (ARRAY lst, FIND pred::p) =
	(case List.find pred lst
	 of SOME jv => get' (jv, p)
	 | NONE => raise ElemNotFound (ARRAY lst))
      | get' (jv, SEL _::_) = raise NotObject jv
      | get' (jv, SUB _::_) = raise NotArray jv
      | get' (jv, FIND _::_) = raise NotArray jv
in
fun get (jv, p) = get' (jv, p)
end
end
