module Test.Main where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect (Effect)
import Effect.Aff (launchAff_)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Hydrogen.HTML.Renderer (render, renderWith, defaultOptions)
import Hydrogen.HTML.Renderer as Renderer
import Hydrogen.Data.Format as Format
import Hydrogen.Data.RemoteData as RD
import Hydrogen.Query as Q
import Hydrogen.Router (normalizeTrailingSlash)
import Hydrogen.SSG as SSG
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)
import Test.Property as Property
import Test.ColorConversion as ColorConversion
import Test.ColorEdgeCases as ColorEdgeCases
import Test.Element as Element
import Test.QRCode as QRCode
import Test.Widget as Widget
import Test.Scene3D as Scene3D
import Test.WebGPU.Geometry as WebGPUGeometry
import Test.Submodular.Property as SubmodularProperty
import Test.GPU.Diffusion as GPUDiffusion
import Test.Schema.Property as SchemaProperty
import Test.Sensation.Property as SensationProperty
import Test.Cache.Property as CacheProperty
import Test.Element.Property as ElementProperty

main :: Effect Unit
main = launchAff_ $ runSpec [consoleReporter] do
  describe "Hydrogen Framework" do
    formatTests
    routerTests
    ssgTests
    rendererTests
    remoteDataTests
    queryTests
  describe "Render Abstraction" do
    Element.elementTests
  describe "Property Tests" do
    Property.propertyTests
  describe "Color System Tests" do
    ColorConversion.colorConversionTests
    ColorEdgeCases.colorEdgeCaseTests
  describe "QR Code Tests" do
    QRCode.qrCodeTests
  describe "Widget Tests" do
    Widget.widgetPropertyTests
  describe "Scene3D Tests" do
    Scene3D.scene3DTests
  describe "WebGPU Tests" do
    WebGPUGeometry.geometryTests
  describe "FAA Submodular Allocation" do
    SubmodularProperty.spec
  describe "GPU Diffusion" do
    GPUDiffusion.diffusionPropertyTests
  describe "Schema" do
    SchemaProperty.schemaPropertyTests
  describe "Sensation → Rights" do
    SensationProperty.sensationPropertyTests
  describe "Cache Property Tests" do
    CacheProperty.cachePropertyTests
  describe "Element Property Tests" do
    ElementProperty.elementPropertyTests

-- =============================================================================
--                                                              // format tests
-- =============================================================================

formatTests :: Spec Unit
formatTests = describe "Data.Format" do
  describe "formatBytes" do
    it "formats bytes" do
      Format.formatBytes 500.0 `shouldEqual` "500 B"
    
    it "formats kilobytes" do
      Format.formatBytes 1024.0 `shouldEqual` "1.0 KB"
    
    it "formats megabytes" do
      Format.formatBytes (1.5 * Format.mb) `shouldEqual` "1.5 MB"
    
    it "formats gigabytes" do
      Format.formatBytes (2.5 * Format.gb) `shouldEqual` "2.5 GB"
    
    it "handles negative numbers" do
      Format.formatBytes (-1024.0) `shouldEqual` "-1.0 KB"

  describe "formatBytesCompact" do
    it "formats without spaces" do
      Format.formatBytesCompact (1.5 * Format.gb) `shouldEqual` "1.5GB"

  describe "formatNum" do
    it "formats with one decimal" do
      Format.formatNum 3.14159 `shouldEqual` "3.1"

  describe "formatNumCompact" do
    it "formats thousands" do
      Format.formatNumCompact 1500.0 `shouldEqual` "1.5k"
    
    it "formats millions" do
      Format.formatNumCompact 2500000.0 `shouldEqual` "2.5M"
    
    it "keeps small numbers as-is" do
      Format.formatNumCompact 500.0 `shouldEqual` "500"

  describe "formatPercent" do
    it "formats percentages" do
      Format.formatPercent 0.874 `shouldEqual` "87.4%"

  describe "formatCount" do
    it "formats count" do
      Format.formatCount 45230 `shouldEqual` "45.2k"

  describe "formatDuration" do
    it "formats seconds" do
      Format.formatDuration 45 `shouldEqual` "45s"
    
    it "formats minutes and seconds" do
      Format.formatDuration 125 `shouldEqual` "2m 5s"
    
    it "formats hours" do
      Format.formatDuration 3661 `shouldEqual` "1h 1m 1s"
    
    it "handles zero" do
      Format.formatDuration 0 `shouldEqual` "-"

  describe "formatDurationCompact" do
    it "shows largest unit only" do
      Format.formatDurationCompact 3661 `shouldEqual` "1h"

  describe "percentage" do
    it "calculates percentage" do
      Format.percentage 750.0 1000.0 `shouldEqual` 75
    
    it "handles division by zero" do
      Format.percentage 1.0 0.0 `shouldEqual` 0

  describe "rate" do
    it "calculates rate" do
      Format.rate 90 100 `shouldEqual` 0.9
    
    it "handles zero total" do
      Format.rate 1 0 `shouldEqual` 0.0

  describe "ratio" do
    it "calculates ratio" do
      Format.ratio 3.0 4.0 `shouldEqual` 0.75
    
    it "handles zero denominator" do
      Format.ratio 1.0 0.0 `shouldEqual` 0.0

-- =============================================================================
--                                                              // router tests
-- =============================================================================

routerTests :: Spec Unit
routerTests = describe "Router" do
  describe "normalizeTrailingSlash" do
    it "preserves root path" do
      normalizeTrailingSlash "/" `shouldEqual` "/"
    
    it "removes trailing slash" do
      normalizeTrailingSlash "/about/" `shouldEqual` "/about"
    
    it "keeps path without trailing slash" do
      normalizeTrailingSlash "/about" `shouldEqual` "/about"
    
    it "handles nested paths" do
      normalizeTrailingSlash "/docs/api/" `shouldEqual` "/docs/api"

-- =============================================================================
--                                                                 // ssg tests
-- =============================================================================

ssgTests :: Spec Unit
ssgTests = describe "SSG" do
  describe "renderPage" do
    it "includes DOCTYPE" do
      let page = SSG.renderPage SSG.defaultDocConfig testMeta (HH.div_ [])
      page `shouldSatisfy` String.contains (String.Pattern "<!DOCTYPE html>")
    
    it "includes title" do
      let page = SSG.renderPage SSG.defaultDocConfig testMeta (HH.div_ [])
      page `shouldSatisfy` String.contains (String.Pattern "<title>Test Page</title>")
    
    it "includes meta description" do
      let page = SSG.renderPage SSG.defaultDocConfig testMeta (HH.div_ [])
      page `shouldSatisfy` String.contains (String.Pattern "Test description")

  describe "ogTags" do
    it "includes og:title" do
      let tags = SSG.ogTags SSG.defaultDocConfig testMeta
      let rendered = Renderer.render (HH.div_ tags)
      rendered `shouldSatisfy` String.contains (String.Pattern "og:title")
    
    it "includes og:description" do
      let tags = SSG.ogTags SSG.defaultDocConfig testMeta
      let rendered = Renderer.render (HH.div_ tags)
      rendered `shouldSatisfy` String.contains (String.Pattern "og:description")

  describe "twitterTags" do
    it "includes twitter:card" do
      let tags = SSG.twitterTags testMeta
      let rendered = Renderer.render (HH.div_ tags)
      rendered `shouldSatisfy` String.contains (String.Pattern "twitter:card")

testMeta :: SSG.PageMeta
testMeta =
  { title: "Test Page"
  , description: "Test description"
  , path: "/test"
  , ogImage: Nothing
  , canonicalUrl: Nothing
  }

-- =============================================================================
--                                                           // renderer tests
-- =============================================================================

rendererTests :: Spec Unit
rendererTests = describe "HTML.Renderer" do
  describe "basic rendering" do
    it "renders empty div" do
      render (HH.div [] []) `shouldEqual` "<div></div>"

    it "renders text content" do
      render (HH.div [] [ HH.text "Hello" ]) `shouldEqual` "<div>Hello</div>"

    it "renders multiple text nodes" do
      render (HH.div [] [ HH.text "Hello", HH.text " ", HH.text "World" ])
        `shouldEqual` "<div>Hello World</div>"

    it "renders span" do
      render (HH.span [] [ HH.text "test" ]) `shouldEqual` "<span>test</span>"

    it "renders paragraph" do
      render (HH.p [] [ HH.text "paragraph" ]) `shouldEqual` "<p>paragraph</p>"

    it "renders heading" do
      render (HH.h1 [] [ HH.text "Title" ]) `shouldEqual` "<h1>Title</h1>"

    it "renders ul/li" do
      render (HH.ul [] [ HH.li [] [ HH.text "item" ] ])
        `shouldEqual` "<ul><li>item</li></ul>"

  describe "attributes" do
    it "renders id attribute" do
      render (HH.div [ HP.id "my-id" ] []) `shouldEqual` "<div id=\"my-id\"></div>"

    it "renders title attribute" do
      render (HH.div [ HP.title "tooltip" ] [])
        `shouldEqual` "<div title=\"tooltip\"></div>"

    it "renders href on anchor" do
      render (HH.a [ HP.href "/path" ] [ HH.text "link" ])
        `shouldEqual` "<a href=\"/path\">link</a>"

    it "renders src on img" do
      render (HH.img [ HP.src "/image.png" ])
        `shouldEqual` "<img src=\"/image.png\"/>"

    it "renders multiple attributes" do
      render (HH.div [ HP.id "foo", HP.title "bar" ] [])
        `shouldEqual` "<div id=\"foo\" title=\"bar\"></div>"

    it "renders data attributes" do
      render (HH.div [ HP.attr (HH.AttrName "data-testid") "test" ] [])
        `shouldEqual` "<div data-testid=\"test\"></div>"

  describe "properties" do
    it "renders className as class" do
      render (HH.div [ HP.class_ (HH.ClassName "container") ] [])
        `shouldEqual` "<div class=\"container\"></div>"

    it "renders multiple classes" do
      render (HH.div [ HP.classes [ HH.ClassName "foo", HH.ClassName "bar" ] ] [])
        `shouldEqual` "<div class=\"foo bar\"></div>"

    it "renders disabled as boolean attribute" do
      render (HH.button [ HP.disabled true ] [ HH.text "click" ])
        `shouldEqual` "<button disabled>click</button>"

    it "omits disabled when false" do
      render (HH.button [ HP.disabled false ] [ HH.text "click" ])
        `shouldEqual` "<button>click</button>"

    it "renders checked attribute" do
      render (HH.input [ HP.type_ HP.InputCheckbox, HP.checked true ])
        `shouldEqual` "<input type=\"checkbox\" checked/>"

    it "renders placeholder" do
      render (HH.input [ HP.placeholder "Enter text" ])
        `shouldEqual` "<input placeholder=\"Enter text\"/>"

  describe "escaping" do
    it "escapes < in text" do
      render (HH.div [] [ HH.text "a < b" ]) `shouldEqual` "<div>a &lt; b</div>"

    it "escapes > in text" do
      render (HH.div [] [ HH.text "a > b" ]) `shouldEqual` "<div>a &gt; b</div>"

    it "escapes & in text" do
      render (HH.div [] [ HH.text "a & b" ]) `shouldEqual` "<div>a &amp; b</div>"

    it "escapes quotes in attributes" do
      render (HH.div [ HP.title "say \"hello\"" ] [])
        `shouldEqual` "<div title=\"say &quot;hello&quot;\"></div>"

  describe "self-closing" do
    it "renders br as self-closing" do
      render (HH.br []) `shouldEqual` "<br/>"

    it "renders hr as self-closing" do
      render (HH.hr []) `shouldEqual` "<hr/>"

    it "renders img as self-closing" do
      render (HH.img [ HP.src "x.png" ]) `shouldEqual` "<img src=\"x.png\"/>"

    it "renders input as self-closing" do
      render (HH.input []) `shouldEqual` "<input/>"

    it "renders non-self-closing without self-close" do
      renderWith (defaultOptions { selfClosingTags = false }) (HH.br [])
        `shouldEqual` "<br></br>"

  describe "nesting" do
    it "renders nested elements" do
      render (HH.div [] [ HH.span [] [ HH.text "inner" ] ])
        `shouldEqual` "<div><span>inner</span></div>"

    it "renders deeply nested elements" do
      render (HH.div [] [ HH.div [] [ HH.div [] [ HH.text "deep" ] ] ])
        `shouldEqual` "<div><div><div>deep</div></div></div>"

    it "renders siblings" do
      render (HH.div [] [ HH.span [] [], HH.span [] [] ])
        `shouldEqual` "<div><span></span><span></span></div>"

    it "renders complex structure" do
      render (HH.article [ HP.class_ (HH.ClassName "post") ]
        [ HH.h1 [] [ HH.text "Title" ]
        , HH.p [] [ HH.text "Content with ", HH.strong [] [ HH.text "bold" ], HH.text " text." ]
        ])
        `shouldEqual` "<article class=\"post\"><h1>Title</h1><p>Content with <strong>bold</strong> text.</p></article>"

-- =============================================================================
--                                                          // RemoteData tests
-- =============================================================================

remoteDataTests :: Spec Unit
remoteDataTests = describe "RemoteData" do
  describe "construction" do
    it "NotAsked equals itself" do
      (RD.NotAsked :: RD.RemoteData String Int) `shouldEqual` RD.NotAsked
    
    it "Loading equals itself" do
      (RD.Loading :: RD.RemoteData String Int) `shouldEqual` RD.Loading
    
    it "Success wraps data" do
      RD.Success 42 `shouldEqual` (RD.Success 42 :: RD.RemoteData String Int)
    
    it "Failure wraps error" do
      RD.Failure "oops" `shouldEqual` (RD.Failure "oops" :: RD.RemoteData String Int)
    
    it "fromEither converts Right to Success" do
      RD.fromEither (Right 42) `shouldEqual` (RD.Success 42 :: RD.RemoteData String Int)
    
    it "fromEither converts Left to Failure" do
      RD.fromEither (Left "err") `shouldEqual` (RD.Failure "err" :: RD.RemoteData String Int)

  describe "Functor" do
    it "maps over Success" do
      map (_ + 1) (RD.Success 1 :: RD.RemoteData String Int) `shouldEqual` RD.Success 2
    
    it "preserves NotAsked" do
      map (_ + 1) (RD.NotAsked :: RD.RemoteData String Int) `shouldEqual` RD.NotAsked
    
    it "preserves Loading" do
      map (_ + 1) (RD.Loading :: RD.RemoteData String Int) `shouldEqual` RD.Loading
    
    it "preserves Failure" do
      map (_ + 1) (RD.Failure "err" :: RD.RemoteData String Int) `shouldEqual` RD.Failure "err"

  describe "Applicative" do
    it "pure creates Success" do
      (pure 42 :: RD.RemoteData String Int) `shouldEqual` RD.Success 42
    
    it "applies functions" do
      (pure (_ + 1) <*> RD.Success 1) `shouldEqual` (RD.Success 2 :: RD.RemoteData String Int)
    
    it "combines Success values" do
      (pure (+) <*> RD.Success 1 <*> RD.Success 2) `shouldEqual` (RD.Success 3 :: RD.RemoteData String Int)
    
    it "combines with ado syntax" do
      let combined = ado
            a <- RD.Success 1 :: RD.RemoteData String Int
            b <- RD.Success 2
            c <- RD.Success 3
            in a + b + c
      combined `shouldEqual` RD.Success 6
    
    it "propagates Loading in ado" do
      let combined = ado
            a <- RD.Success 1 :: RD.RemoteData String Int
            b <- RD.Loading
            c <- RD.Success 3
            in a + b + c
      combined `shouldEqual` RD.Loading
    
    it "propagates Failure in ado" do
      let combined = ado
            a <- RD.Success 1 :: RD.RemoteData String Int
            b <- RD.Failure "oops"
            c <- RD.Success 3
            in a + b + c
      combined `shouldEqual` RD.Failure "oops"
    
    -- Applicative laws
    it "identity law: pure id <*> v = v" do
      let v = RD.Success 42 :: RD.RemoteData String Int
      (pure identity <*> v) `shouldEqual` v
    
    it "homomorphism: pure f <*> pure x = pure (f x)" do
      let f = (_ + 1)
      let x = 42
      (pure f <*> pure x) `shouldEqual` (pure (f x) :: RD.RemoteData String Int)
    
    it "interchange: u <*> pure y = pure ($ y) <*> u" do
      let u = RD.Success (_ + 1) :: RD.RemoteData String (Int -> Int)
      let y = 42
      (u <*> pure y) `shouldEqual` (pure (_ $ y) <*> u)

  describe "Monad" do
    it "bind chains Success" do
      let result = do
            a <- RD.Success 1 :: RD.RemoteData String Int
            b <- RD.Success 2
            pure (a + b)
      result `shouldEqual` RD.Success 3
    
    it "bind short-circuits on Failure" do
      let result = do
            a <- RD.Success 1 :: RD.RemoteData String Int
            _ <- RD.Failure "oops"
            pure a
      result `shouldEqual` RD.Failure "oops"
    
    it "bind short-circuits on Loading" do
      let result = do
            a <- RD.Success 1 :: RD.RemoteData String Int
            _ <- RD.Loading
            pure a
      result `shouldEqual` RD.Loading
    
    -- Monad laws
    it "left identity: pure a >>= f = f a" do
      let f x = RD.Success (x + 1) :: RD.RemoteData String Int
      (pure 42 >>= f) `shouldEqual` f 42
    
    it "right identity: m >>= pure = m" do
      let m = RD.Success 42 :: RD.RemoteData String Int
      (m >>= pure) `shouldEqual` m
    
    it "right identity holds for all states" do
      let notAsked = RD.NotAsked :: RD.RemoteData String Int
      let loading = RD.Loading :: RD.RemoteData String Int
      let failure = RD.Failure "err" :: RD.RemoteData String Int
      let success = RD.Success 42 :: RD.RemoteData String Int
      (notAsked >>= pure) `shouldEqual` notAsked
      (loading >>= pure) `shouldEqual` loading
      (failure >>= pure) `shouldEqual` failure
      (success >>= pure) `shouldEqual` success
    
    it "associativity: (m >>= f) >>= g = m >>= (\\x -> f x >>= g)" do
      let m = RD.Success 1 :: RD.RemoteData String Int
      let f x = RD.Success (x + 1) :: RD.RemoteData String Int
      let g x = RD.Success (x * 2) :: RD.RemoteData String Int
      ((m >>= f) >>= g) `shouldEqual` (m >>= (\x -> f x >>= g))

  describe "predicates" do
    it "isNotAsked works" do
      RD.isNotAsked (RD.NotAsked :: RD.RemoteData String Int) `shouldEqual` true
      RD.isNotAsked (RD.Loading :: RD.RemoteData String Int) `shouldEqual` false
    
    it "isLoading works" do
      RD.isLoading (RD.Loading :: RD.RemoteData String Int) `shouldEqual` true
      RD.isLoading (RD.Success 1 :: RD.RemoteData String Int) `shouldEqual` false
    
    it "isFailure works" do
      RD.isFailure (RD.Failure "err" :: RD.RemoteData String Int) `shouldEqual` true
      RD.isFailure (RD.Success 1 :: RD.RemoteData String Int) `shouldEqual` false
    
    it "isSuccess works" do
      RD.isSuccess (RD.Success 42 :: RD.RemoteData String Int) `shouldEqual` true
      RD.isSuccess (RD.Failure "err" :: RD.RemoteData String Int) `shouldEqual` false

  describe "fold" do
    it "handles all cases" do
      let handlers = 
            { notAsked: "notAsked"
            , loading: "loading"
            , failure: \e -> "failure: " <> e
            , success: \n -> "success: " <> show n
            }
      RD.fold handlers (RD.NotAsked :: RD.RemoteData String Int) `shouldEqual` "notAsked"
      RD.fold handlers (RD.Loading :: RD.RemoteData String Int) `shouldEqual` "loading"
      RD.fold handlers (RD.Failure "oops") `shouldEqual` "failure: oops"
      RD.fold handlers (RD.Success 42) `shouldEqual` "success: 42"

  describe "withDefault" do
    it "uses Success value" do
      RD.withDefault 0 (RD.Success 42 :: RD.RemoteData String Int) `shouldEqual` 42
    
    it "uses default for Loading" do
      RD.withDefault 0 (RD.Loading :: RD.RemoteData String Int) `shouldEqual` 0
    
    it "uses default for Failure" do
      RD.withDefault 0 (RD.Failure "err" :: RD.RemoteData String Int) `shouldEqual` 0

-- =============================================================================
--                                                             // query tests
-- =============================================================================

queryTests :: Spec Unit
queryTests = describe "Query" do
  describe "defaultQueryOptions" do
    it "creates options with key and fetch" do
      let opts = Q.defaultQueryOptions ["user", "123"] (pure $ Right 42)
      opts.key `shouldEqual` ["user", "123"]
      opts.retry `shouldEqual` 0
    
    it "has sensible defaults" do
      let opts = Q.defaultQueryOptions ["test"] (pure $ Right "data")
      opts.staleTime `shouldEqual` Nothing
      opts.retry `shouldEqual` 0

  describe "QueryState" do
    it "initialQueryState has NotAsked data" do
      let state = Q.initialQueryState :: Q.QueryState String Int
      state.data `shouldEqual` RD.NotAsked
      state.isStale `shouldEqual` false
      state.isFetching `shouldEqual` false

  describe "QueryState helpers" do
    it "getData extracts from Success" do
      let state = { data: RD.Success 42, isStale: false, isFetching: false } :: Q.QueryState String Int
      Q.getData state `shouldEqual` Just 42
    
    it "getData returns Nothing for Loading" do
      let state = { data: RD.Loading, isStale: false, isFetching: false } :: Q.QueryState String Int
      Q.getData state `shouldEqual` Nothing
    
    it "getError extracts from Failure" do
      let state = { data: RD.Failure "oops", isStale: false, isFetching: false } :: Q.QueryState String Int
      Q.getError state `shouldEqual` Just "oops"
    
    it "getError returns Nothing for Success" do
      let state = { data: RD.Success 42, isStale: false, isFetching: false } :: Q.QueryState String Int
      Q.getError state `shouldEqual` Nothing
    
    it "hasData is true for Success" do
      let state = { data: RD.Success 42, isStale: false, isFetching: false } :: Q.QueryState String Int
      Q.hasData state `shouldEqual` true
    
    it "hasData is false for Loading" do
      let state = { data: RD.Loading, isStale: false, isFetching: false } :: Q.QueryState String Int
      Q.hasData state `shouldEqual` false
    
    it "withDefaultData uses Success value" do
      let state = { data: RD.Success 42, isStale: false, isFetching: false } :: Q.QueryState String Int
      Q.withDefaultData 0 state `shouldEqual` 42
    
    it "withDefaultData uses default for Loading" do
      let state = { data: RD.Loading, isStale: false, isFetching: false } :: Q.QueryState String Int
      Q.withDefaultData 0 state `shouldEqual` 0
    
    it "foldData handles all cases" do
      let handlers = 
            { notAsked: "notAsked"
            , loading: "loading"
            , failure: \e -> "failure: " <> e
            , success: \n -> "success: " <> show n
            }
      let notAsked = { data: RD.NotAsked, isStale: false, isFetching: false } :: Q.QueryState String Int
      let loading = { data: RD.Loading, isStale: false, isFetching: true } :: Q.QueryState String Int
      let failure = { data: RD.Failure "oops", isStale: false, isFetching: false } :: Q.QueryState String Int
      let success = { data: RD.Success 42, isStale: false, isFetching: false } :: Q.QueryState String Int
      Q.foldData handlers notAsked `shouldEqual` "notAsked"
      Q.foldData handlers loading `shouldEqual` "loading"
      Q.foldData handlers failure `shouldEqual` "failure: oops"
      Q.foldData handlers success `shouldEqual` "success: 42"

  describe "Combining queries with RemoteData" do
    it "combines queries with ado" do
      let userState = { data: RD.Success "Alice", isStale: false, isFetching: false } :: Q.QueryState String String
      let postsState = { data: RD.Success 3, isStale: false, isFetching: false } :: Q.QueryState String Int
      let combined :: RD.RemoteData String { userName :: String, postCount :: Int }
          combined = ado
            user <- userState.data
            posts <- postsState.data
            in { userName: user, postCount: posts }
      RD.isSuccess combined `shouldEqual` true
    
    it "propagates Loading when combining" do
      let userState = { data: RD.Success "Alice", isStale: false, isFetching: false } :: Q.QueryState String String
      let postsState = { data: RD.Loading, isStale: false, isFetching: true } :: Q.QueryState String Int
      let combined :: RD.RemoteData String Int
          combined = ado
            _ <- userState.data
            posts <- postsState.data
            in posts
      combined `shouldEqual` RD.Loading
    
    it "propagates Failure when combining" do
      let userState = { data: RD.Success "Alice", isStale: false, isFetching: false } :: Q.QueryState String String
      let postsState = { data: RD.Failure "Network error", isStale: false, isFetching: false } :: Q.QueryState String Int
      let combined :: RD.RemoteData String Int
          combined = ado
            _ <- userState.data
            posts <- postsState.data
            in posts
      combined `shouldEqual` RD.Failure "Network error"

  describe "PagedState" do
    it "initialPagedState has NotAsked data" do
      let state = Q.initialPagedState :: Q.PagedState String Int
      state.data `shouldEqual` RD.NotAsked
      state.pages `shouldEqual` []
      state.hasNextPage `shouldEqual` false

-- Helper for length
length :: forall a. Array a -> Int
length = Array.length
