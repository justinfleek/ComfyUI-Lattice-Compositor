let Core = ./Core.dhall

let AuthLevel = < User | Admin | System >

let Resource =
  < Tokens : Natural
  | Compute : { flops : Natural, memory : Natural }
  | Network : { bandwidth : Natural, latency : Natural }
  | Auth : { scope : Text, level : AuthLevel }
  >

let Coeffects = List Resource

in { Resource, Coeffects, AuthLevel }
