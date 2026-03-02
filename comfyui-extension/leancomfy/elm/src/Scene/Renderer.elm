module Scene.Renderer exposing (view, Entity, toEntities)

{-| 3D rendering using elm-3d-scene.

This module takes the type-safe scene data from Lean and renders it.
All validation has already happened - we just draw.

-}

import Angle exposing (Angle)
import Camera3d exposing (Camera3d)
import Color exposing (Color)
import Direction3d exposing (Direction3d)
import Html exposing (Html)
import Length exposing (Meters)
import Luminance
import Illuminance
import Pixels
import Point3d exposing (Point3d)
import Scene3d
import Scene3d.Light as Light
import Scene3d.Material as Material
import Viewpoint3d
import Vector3d
import Block3d

import Scene.Types as Types exposing (Scene, SceneObject, Material(..), ColorRGB)


-- Coordinate system (matches Lean)
type WorldCoordinates
    = WorldCoordinates


type alias Entity =
    Scene3d.Entity WorldCoordinates


{-| Convert ColorRGB to elm-color Color -}
toColor : ColorRGB -> Color
toColor { r, g, b } =
    Color.rgb r g b


{-| Convert a scene object to a renderable entity.

For the demo, we render each object as a simple block.
In production, you'd use the actual mesh data.
-}
objectToEntity : SceneObject -> Entity
objectToEntity obj =
    let
        -- Extract position from transform matrix
        -- (assuming it's a translation for now)
        position =
            case obj.transform.matrix of
                [ _, _, _, _, _, _, _, _, _, _, _, _, tx, ty, tz, _ ] ->
                    Point3d.meters tx ty tz

                _ ->
                    Point3d.origin

        -- Create material based on type
        material =
            case obj.material of
                Color c ->
                    Material.color (toColor c)

                Matte c ->
                    Material.matte (toColor c)

                Metal c roughness ->
                    Material.metal
                        { baseColor = toColor c
                        , roughness = roughness
                        }

                PBR c metallic roughness ->
                    Material.pbr
                        { baseColor = toColor c
                        , metallic = metallic
                        , roughness = roughness
                        }

        -- Create a unit block centered at the position
        block =
            Block3d.from
                (Point3d.translateBy (Vector3d.meters -0.5 -0.5 -0.5) position)
                (Point3d.translateBy (Vector3d.meters 0.5 0.5 0.5) position)
    in
    Scene3d.blockWithShadow material block


{-| Convert entire scene to list of entities -}
toEntities : Scene -> List Entity
toEntities scene =
    List.map objectToEntity scene.objects


{-| Create the camera -}
camera : Float -> Float -> Camera3d Meters WorldCoordinates
camera azimuth elevation =
    Camera3d.perspective
        { viewpoint =
            Viewpoint3d.orbitZ
                { focalPoint = Point3d.origin
                , azimuth = Angle.degrees azimuth
                , elevation = Angle.degrees elevation
                , distance = Length.meters 10
                }
        , verticalFieldOfView = Angle.degrees 30
        }


{-| Render the scene -}
view : { width : Int, height : Int, azimuth : Float, elevation : Float } -> Scene -> Html msg
view config scene =
    let
        entities =
            toEntities scene

        -- Directional light (sun)
        sunlight =
            case scene.directionalLight of
                Just light ->
                    Light.directional (Light.castsShadows True)
                        { direction = 
                            Direction3d.unsafe
                                { x = light.direction.x
                                , y = light.direction.y
                                , z = light.direction.z
                                }
                        , intensity = Illuminance.lux 10000
                        , chromaticity = Light.daylight
                        }

                Nothing ->
                    Light.directional (Light.castsShadows False)
                        { direction = Direction3d.negativeZ
                        , intensity = Illuminance.lux 5000
                        , chromaticity = Light.daylight
                        }

        -- Soft ambient lighting
        ambientLighting =
            Light.soft
                { upDirection = Direction3d.positiveZ
                , chromaticity = Light.daylight
                , intensityAbove = Illuminance.lux 3000
                , intensityBelow = Illuminance.lux 1000
                }
    in
    Scene3d.custom
        { lights = Scene3d.twoLights sunlight ambientLighting
        , camera = camera config.azimuth config.elevation
        , clipDepth = Length.meters 0.1
        , exposure = Scene3d.exposureValue 11
        , toneMapping = Scene3d.noToneMapping
        , whiteBalance = Light.daylight
        , antialiasing = Scene3d.multisampling
        , dimensions = ( Pixels.int config.width, Pixels.int config.height )
        , background = Scene3d.backgroundColor (Color.rgb255 30 30 40)
        , entities = entities
        }
