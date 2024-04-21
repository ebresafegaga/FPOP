module FamilyId = struct 
  type t = int 
end 

module FamilyName = struct 
  type t = Names.Id.t * FamilyId.t 
end 

(* The type of an "element" in a family *)
module rec FamilyBodyElemTy : sig 
   type t = ..
end = FamilyBodyElemTy

(* The family context, binding names to their respective types *)
and FamilyContext : sig 
  type t = (Names.Id.t * FamilyType.t) list
end = FamilyContext

(* The "type" of a family *)
and FamilyType : sig
  type t =
    { name : FamilyName.t; 
      body : (Names.Id.t * FamilyBodyElemTy.t) list; }

end = FamilyType
