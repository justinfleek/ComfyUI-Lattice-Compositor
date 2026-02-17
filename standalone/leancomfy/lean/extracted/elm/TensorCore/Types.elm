module TensorCore.Types exposing (..)

{-| AUTO-EXTRACTED FROM LEAN PROOFS
    
    Every type here has a corresponding Extractable instance in Lean
    with a proven roundtrip theorem. The encoder/decoder pairs are
    verified correct by construction.
    
    DO NOT EDIT - regenerate with `lake exe extract elm`
-}

import Json.Decode as D exposing (Decoder)
import Json.Decode.Pipeline exposing (required)
import Json.Encode as E


-- TYPES

type alias Point3 =
    { x : Float
    , y : Float
    , z : Float
    }

type alias Vec3 =
    { x : Float
    , y : Float
    , z : Float
    }

type alias ColorRGB =
    { r : Float
    , g : Float
    , b : Float
    }

type alias Vertex =
    { position : Point3
    , normal : Vec3
    }

type alias Transform =
    { matrix : List Float
    }


-- DECODERS

decodePoint3 : Decoder Point3
decodePoint3 =
    D.succeed Point3
        |> required "x" D.float
        |> required "y" D.float
        |> required "z" D.float

decodeVec3 : Decoder Vec3
decodeVec3 =
    D.succeed Vec3
        |> required "x" D.float
        |> required "y" D.float
        |> required "z" D.float

decodeColorRGB : Decoder ColorRGB
decodeColorRGB =
    D.succeed ColorRGB
        |> required "r" D.float
        |> required "g" D.float
        |> required "b" D.float

decodeVertex : Decoder Vertex
decodeVertex =
    D.succeed Vertex
        |> required "position" decodePoint3
        |> required "normal" decodeVec3

decodeTransform : Decoder Transform
decodeTransform =
    D.succeed Transform
        |> required "matrix" (D.list D.float)


-- ENCODERS

encodePoint3 : Point3 -> E.Value
encodePoint3 p =
    E.object
        [ ( "x", E.float p.x )
        , ( "y", E.float p.y )
        , ( "z", E.float p.z )
        ]

encodeVec3 : Vec3 -> E.Value
encodeVec3 v =
    E.object
        [ ( "x", E.float v.x )
        , ( "y", E.float v.y )
        , ( "z", E.float v.z )
        ]

encodeColorRGB : ColorRGB -> E.Value
encodeColorRGB c =
    E.object
        [ ( "r", E.float c.r )
        , ( "g", E.float c.g )
        , ( "b", E.float c.b )
        ]

encodeVertex : Vertex -> E.Value
encodeVertex v =
    E.object
        [ ( "position", encodePoint3 v.position )
        , ( "normal", encodeVec3 v.normal )
        ]

encodeTransform : Transform -> E.Value
encodeTransform t =
    E.object
        [ ( "matrix", E.list E.float t.matrix )
        ]