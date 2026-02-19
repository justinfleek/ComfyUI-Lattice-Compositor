module Scene.Types exposing
    ( Scene, SceneObject, Material(..)
    , Vertex, TriangleIndex
    , Transform, ColorRGB, Vec3
    , DirectionalLight
    , decodeScene, decodeObject
    )

{-| Types for the 3D scene, mirroring the Lean definitions.

The key insight: these types are simpler than Lean's because Elm
doesn't need the proofs. The Lean side guarantees correctness;
Elm just renders what it's given.

-}

import Json.Decode as D exposing (Decoder)


-- TYPES


type alias ColorRGB =
    { r : Float
    , g : Float
    , b : Float
    }


type alias Vec3 =
    { x : Float
    , y : Float
    , z : Float
    }


type alias Vertex =
    { position : Vec3
    , normal : Vec3
    }


type alias TriangleIndex =
    { i0 : Int
    , i1 : Int
    , i2 : Int
    }


type Material
    = Color ColorRGB
    | Matte ColorRGB
    | Metal ColorRGB Float -- roughness
    | PBR ColorRGB Float Float -- metallic, roughness


type alias Transform =
    { matrix : List Float -- 16 elements, column-major
    }


type alias SceneObject =
    { name : String
    , vertices : List Vertex
    , indices : List TriangleIndex
    , material : Material
    , transform : Transform
    }


type alias DirectionalLight =
    { direction : Vec3
    , color : ColorRGB
    }


type alias Scene =
    { objects : List SceneObject
    , ambientLight : ColorRGB
    , directionalLight : Maybe DirectionalLight
    }



-- DECODERS


decodeColor : Decoder ColorRGB
decodeColor =
    D.map3 ColorRGB
        (D.field "r" D.float)
        (D.field "g" D.float)
        (D.field "b" D.float)


decodeVec3 : Decoder Vec3
decodeVec3 =
    D.map3 Vec3
        (D.index 0 D.float)
        (D.index 1 D.float)
        (D.index 2 D.float)


decodeVertex : Decoder Vertex
decodeVertex =
    D.map2 Vertex
        (D.field "position" decodeVec3)
        (D.field "normal" decodeVec3)


decodeTriangleIndex : Decoder TriangleIndex
decodeTriangleIndex =
    D.map3 TriangleIndex
        (D.index 0 D.int)
        (D.index 1 D.int)
        (D.index 2 D.int)


decodeMaterial : Decoder Material
decodeMaterial =
    D.field "type" D.string
        |> D.andThen decodeMaterialByType


decodeMaterialByType : String -> Decoder Material
decodeMaterialByType typeStr =
    case typeStr of
        "color" ->
            D.map Color (D.field "color" decodeColor)

        "matte" ->
            D.map Matte (D.field "color" decodeColor)

        "metal" ->
            D.map2 Metal
                (D.field "color" decodeColor)
                (D.field "roughness" D.float)

        "pbr" ->
            D.map3 PBR
                (D.field "color" decodeColor)
                (D.field "metallic" D.float)
                (D.field "roughness" D.float)

        _ ->
            D.fail ("Unknown material type: " ++ typeStr)


decodeTransform : Decoder Transform
decodeTransform =
    D.map Transform (D.list D.float)


decodeObject : Decoder SceneObject
decodeObject =
    D.map5 SceneObject
        (D.field "name" D.string)
        (D.field "vertices" (D.list decodeVertex))
        (D.field "indices" (D.list decodeTriangleIndex))
        (D.field "material" decodeMaterial)
        (D.field "transform" decodeTransform)


decodeDirectionalLight : Decoder DirectionalLight
decodeDirectionalLight =
    D.map2 DirectionalLight
        (D.field "direction" decodeVec3)
        (D.field "color" decodeColor)


decodeScene : Decoder Scene
decodeScene =
    D.map3 Scene
        (D.field "objects" (D.list decodeObject))
        (D.field "ambientLight" decodeColor)
        (D.field "directionalLight" (D.nullable decodeDirectionalLight))
