module FamilyId = struct 
  type t = int 
end 

module NameTable = Map.Make(Names.Id)

module FamilyName = struct 
  type t = { name: Names.Id.t; id: FamilyId.t }
end 

(* The type of an "element" in a family *)
module rec FamilyBodyElemTy : sig 
   type t = ..
end = FamilyBodyElemTy

(* The family context, binding names to their respective types *)
and FamilyContext : sig
  type t = FamilyType.t NameTable.t
end = FamilyContext

(* The "type" of a family *)
and FamilyType : sig
  type t =
    { name : FamilyName.t; 
      body : FamilyBodyElemTy.t NameTable.t; }

end = FamilyType



