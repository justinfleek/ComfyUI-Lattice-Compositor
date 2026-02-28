-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // test // element
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tests for Hydrogen.Render.Element and Hydrogen.Target.Static
-- |
-- | Validates:
-- | - Element construction
-- | - Attribute handling
-- | - Static HTML rendering
-- | - Escaping behavior
-- | - Self-closing tags
module Test.Element
  ( elementTests
  ) where

import Prelude

import Data.String as String
import Hydrogen.Render.Element as E
import Hydrogen.Target.Static as TS
import Hydrogen.UI.Button as Button
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // test data
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Simple action type for testing event handlers
data TestAction
  = Click
  | Input String
  | Submit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // test suite
-- ═══════════════════════════════════════════════════════════════════════════════

elementTests :: Spec Unit
elementTests = describe "Element & Static Target" do
  elementConstructionTests
  attributeTests
  staticRenderingTests
  escapingTests
  selfClosingTests
  nestingTests
  eventHandlerTests
  buttonComponentTests

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // element construction
-- ═══════════════════════════════════════════════════════════════════════════════

elementConstructionTests :: Spec Unit
elementConstructionTests = describe "Element construction" do
  
  it "creates text nodes" do
    let el = E.text "Hello"
    TS.render el `shouldEqual` "Hello"
  
  it "creates empty elements" do
    let el = E.empty
    TS.render el `shouldEqual` ""
  
  it "creates div elements" do
    let el = E.div_ [] []
    TS.render el `shouldEqual` "<div></div>"
  
  it "creates span elements" do
    let el = E.span_ [] [ E.text "content" ]
    TS.render el `shouldEqual` "<span>content</span>"
  
  it "creates paragraph elements" do
    let el = E.p_ [] [ E.text "paragraph" ]
    TS.render el `shouldEqual` "<p>paragraph</p>"
  
  it "creates heading elements" do
    let h1 = E.h1_ [] [ E.text "Title" ]
    let h2 = E.h2_ [] [ E.text "Subtitle" ]
    TS.render h1 `shouldEqual` "<h1>Title</h1>"
    TS.render h2 `shouldEqual` "<h2>Subtitle</h2>"
  
  it "creates anchor elements" do
    let el = E.a_ [ E.attr "href" "/page" ] [ E.text "Link" ]
    TS.render el `shouldEqual` "<a href=\"/page\">Link</a>"
  
  it "creates button elements" do
    let el = E.button_ [] [ E.text "Click" ]
    TS.render el `shouldEqual` "<button>Click</button>"
  
  it "creates form elements" do
    let el = E.form_ [] [ E.text "Form content" ]
    TS.render el `shouldEqual` "<form>Form content</form>"
  
  it "creates list elements" do
    let el = E.ul_ [] 
          [ E.li_ [] [ E.text "Item 1" ]
          , E.li_ [] [ E.text "Item 2" ]
          ]
    TS.render el `shouldEqual` "<ul><li>Item 1</li><li>Item 2</li></ul>"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // attribute tests
-- ═══════════════════════════════════════════════════════════════════════════════

attributeTests :: Spec Unit
attributeTests = describe "Attributes" do
  
  it "renders id attribute" do
    let el = E.div_ [ E.id_ "my-id" ] []
    TS.render el `shouldEqual` "<div id=\"my-id\"></div>"
  
  it "renders class attribute" do
    let el = E.div_ [ E.class_ "foo bar" ] []
    TS.render el `shouldEqual` "<div class=\"foo bar\"></div>"
  
  it "renders multiple classes" do
    let el = E.div_ [ E.classes [ "one", "two", "three" ] ] []
    TS.render el `shouldEqual` "<div class=\"one two three\"></div>"
  
  it "renders generic attributes" do
    let el = E.div_ [ E.attr "data-value" "123" ] []
    TS.render el `shouldEqual` "<div data-value=\"123\"></div>"
  
  it "renders multiple attributes" do
    let el = E.div_ 
          [ E.id_ "test"
          , E.class_ "container"
          , E.attr "data-x" "y"
          ] []
    let rendered = TS.render el
    rendered `shouldSatisfy` String.contains (String.Pattern "id=\"test\"")
    rendered `shouldSatisfy` String.contains (String.Pattern "class=\"container\"")
    rendered `shouldSatisfy` String.contains (String.Pattern "data-x=\"y\"")
  
  it "renders properties as attributes" do
    let el = E.input_ [ E.prop "value" "hello" ]
    TS.render el `shouldSatisfy` String.contains (String.Pattern "value=\"hello\"")
  
  it "renders boolean properties when true" do
    let el = E.input_ [ E.propBool "disabled" true ]
    TS.render el `shouldSatisfy` String.contains (String.Pattern "disabled")
  
  it "omits boolean properties when false" do
    let el = E.input_ [ E.propBool "disabled" false ]
    let rendered = TS.render el
    rendered `shouldSatisfy` (not <<< String.contains (String.Pattern "disabled"))
  
  it "renders style attributes" do
    let el = E.div_ [ E.style "color" "red" ] []
    TS.render el `shouldSatisfy` String.contains (String.Pattern "style=\"color: red\"")

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // static rendering tests
-- ═══════════════════════════════════════════════════════════════════════════════

staticRenderingTests :: Spec Unit
staticRenderingTests = describe "Static rendering" do
  
  it "renders basic structure" do
    let el = E.div_ [ E.class_ "container" ]
          [ E.h1_ [] [ E.text "Title" ]
          , E.p_ [] [ E.text "Content" ]
          ]
    let expected = "<div class=\"container\"><h1>Title</h1><p>Content</p></div>"
    TS.render el `shouldEqual` expected
  
  it "handles empty children" do
    let el = E.div_ [] []
    TS.render el `shouldEqual` "<div></div>"
  
  it "handles text-only children" do
    let el = E.p_ [] [ E.text "Just text" ]
    TS.render el `shouldEqual` "<p>Just text</p>"
  
  it "handles mixed children" do
    let el = E.p_ []
          [ E.text "Start "
          , E.strong_ [] [ E.text "bold" ]
          , E.text " end"
          ]
    TS.render el `shouldEqual` "<p>Start <strong>bold</strong> end</p>"
  
  it "renders with custom options" do
    let opts = TS.defaultOptions { selfClosingSlash = false }
    let el = E.br_ []
    TS.renderWith opts el `shouldEqual` "<br>"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // escaping tests
-- ═══════════════════════════════════════════════════════════════════════════════

escapingTests :: Spec Unit
escapingTests = describe "HTML escaping" do
  
  it "escapes < in text" do
    let el = E.text "a < b"
    TS.render el `shouldEqual` "a &lt; b"
  
  it "escapes > in text" do
    let el = E.text "a > b"
    TS.render el `shouldEqual` "a &gt; b"
  
  it "escapes & in text" do
    let el = E.text "a & b"
    TS.render el `shouldEqual` "a &amp; b"
  
  it "escapes quotes in attributes" do
    let el = E.div_ [ E.attr "title" "Say \"hello\"" ] []
    TS.render el `shouldSatisfy` String.contains (String.Pattern "&quot;")
  
  it "escapes multiple special characters" do
    let el = E.text "<script>alert('xss')</script>"
    let rendered = TS.render el
    rendered `shouldSatisfy` (not <<< String.contains (String.Pattern "<script>"))
    rendered `shouldSatisfy` String.contains (String.Pattern "&lt;script&gt;")

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // self-closing tests
-- ═══════════════════════════════════════════════════════════════════════════════

selfClosingTests :: Spec Unit
selfClosingTests = describe "Self-closing tags" do
  
  it "renders br as self-closing" do
    let el = E.br_ []
    TS.render el `shouldEqual` "<br/>"
  
  it "renders hr as self-closing" do
    let el = E.hr_ []
    TS.render el `shouldEqual` "<hr/>"
  
  it "renders img as self-closing" do
    let el = E.img_ [ E.attr "src" "photo.jpg" ]
    TS.render el `shouldEqual` "<img src=\"photo.jpg\"/>"
  
  it "renders input as self-closing" do
    let el = E.input_ [ E.attr "type" "text" ]
    TS.render el `shouldEqual` "<input type=\"text\"/>"
  
  it "renders meta as self-closing" do
    let el = E.meta_ [ E.attr "charset" "utf-8" ]
    TS.render el `shouldEqual` "<meta charset=\"utf-8\"/>"
  
  it "renders link as self-closing" do
    let el = E.link_ [ E.attr "rel" "stylesheet", E.attr "href" "style.css" ]
    let rendered = TS.render el
    rendered `shouldSatisfy` String.contains (String.Pattern "/>")
    rendered `shouldSatisfy` (not <<< String.contains (String.Pattern "</link>"))
  
  it "does not self-close non-void elements" do
    let el = E.div_ [] []
    TS.render el `shouldEqual` "<div></div>"
  
  it "respects selfClosingSlash option" do
    let opts = TS.defaultOptions { selfClosingSlash = false }
    let el = E.br_ []
    TS.renderWith opts el `shouldEqual` "<br>"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // nesting tests
-- ═══════════════════════════════════════════════════════════════════════════════

nestingTests :: Spec Unit
nestingTests = describe "Element nesting" do
  
  it "handles deep nesting" do
    let el = E.div_ []
          [ E.div_ []
              [ E.div_ []
                  [ E.div_ []
                      [ E.text "deep" ]
                  ]
              ]
          ]
    TS.render el `shouldEqual` "<div><div><div><div>deep</div></div></div></div>"
  
  it "handles sibling elements" do
    let el = E.div_ []
          [ E.span_ [] [ E.text "one" ]
          , E.span_ [] [ E.text "two" ]
          , E.span_ [] [ E.text "three" ]
          ]
    TS.render el `shouldEqual` "<div><span>one</span><span>two</span><span>three</span></div>"
  
  it "handles complex structure" do
    let el = E.article_ []
          [ E.header_ []
              [ E.h1_ [] [ E.text "Title" ] ]
          , E.section_ []
              [ E.p_ [] [ E.text "Para 1" ]
              , E.p_ [] [ E.text "Para 2" ]
              ]
          , E.footer_ []
              [ E.text "Footer" ]
          ]
    let rendered = TS.render el
    rendered `shouldSatisfy` String.contains (String.Pattern "<article>")
    rendered `shouldSatisfy` String.contains (String.Pattern "<header>")
    rendered `shouldSatisfy` String.contains (String.Pattern "<section>")
    rendered `shouldSatisfy` String.contains (String.Pattern "<footer>")

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // event handler tests
-- ═══════════════════════════════════════════════════════════════════════════════

eventHandlerTests :: Spec Unit
eventHandlerTests = describe "Event handlers in static rendering" do
  
  it "ignores onClick in static output" do
    let el :: E.Element TestAction
        el = E.button_ [ E.onClick Click ] [ E.text "Click" ]
    let rendered = TS.render el
    rendered `shouldEqual` "<button>Click</button>"
    rendered `shouldSatisfy` (not <<< String.contains (String.Pattern "onclick"))
  
  it "ignores onInput in static output" do
    let el :: E.Element TestAction
        el = E.input_ [ E.onInput Input, E.attr "type" "text" ]
    let rendered = TS.render el
    rendered `shouldSatisfy` (not <<< String.contains (String.Pattern "oninput"))
  
  it "ignores onSubmit in static output" do
    let el :: E.Element TestAction
        el = E.form_ [ E.onSubmit Submit ] [ E.text "Form" ]
    let rendered = TS.render el
    rendered `shouldEqual` "<form>Form</form>"
  
  it "preserves non-handler attributes with handlers" do
    let el :: E.Element TestAction
        el = E.button_ 
          [ E.class_ "btn"
          , E.onClick Click
          , E.attr "data-test" "value"
          ] 
          [ E.text "Click" ]
    let rendered = TS.render el
    rendered `shouldSatisfy` String.contains (String.Pattern "class=\"btn\"")
    rendered `shouldSatisfy` String.contains (String.Pattern "data-test=\"value\"")

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // button component tests
-- ═══════════════════════════════════════════════════════════════════════════════

buttonComponentTests :: Spec Unit
buttonComponentTests = describe "Button component (Element-based)" do
  
  it "renders basic button" do
    let btn :: E.Element TestAction
        btn = Button.button [] [ E.text "Click me" ]
    let rendered = TS.render btn
    rendered `shouldSatisfy` String.contains (String.Pattern "<button")
    rendered `shouldSatisfy` String.contains (String.Pattern "Click me")
    rendered `shouldSatisfy` String.contains (String.Pattern "</button>")
  
  it "applies variant classes" do
    let btn :: E.Element TestAction
        btn = Button.button [ Button.variant Button.Destructive ] [ E.text "Delete" ]
    let rendered = TS.render btn
    rendered `shouldSatisfy` String.contains (String.Pattern "bg-destructive")
  
  it "applies size classes" do
    let btn :: E.Element TestAction
        btn = Button.button [ Button.size Button.Lg ] [ E.text "Large" ]
    let rendered = TS.render btn
    rendered `shouldSatisfy` String.contains (String.Pattern "h-11")
    rendered `shouldSatisfy` String.contains (String.Pattern "px-8")
  
  it "renders disabled state" do
    let btn :: E.Element TestAction
        btn = Button.button [ Button.disabled true ] [ E.text "Disabled" ]
    let rendered = TS.render btn
    rendered `shouldSatisfy` String.contains (String.Pattern "disabled")
  
  it "renders loading state with spinner" do
    let btn :: E.Element TestAction
        btn = Button.button [ Button.loading true ] [ E.text "Loading" ]
    let rendered = TS.render btn
    rendered `shouldSatisfy` String.contains (String.Pattern "animate-spin")
    rendered `shouldSatisfy` String.contains (String.Pattern "opacity-70")
  
  it "adds shadow classes when enabled" do
    let btn :: E.Element TestAction
        btn = Button.button [ Button.shadow true ] [ E.text "Elevated" ]
    let rendered = TS.render btn
    rendered `shouldSatisfy` String.contains (String.Pattern "shadow-lg")
  
  it "ignores click handler in static output" do
    let btn :: E.Element TestAction
        btn = Button.button [ Button.onClick Click ] [ E.text "Click" ]
    let rendered = TS.render btn
    rendered `shouldSatisfy` (not <<< String.contains (String.Pattern "onclick"))
  
  it "renders button link with href" do
    let link :: E.Element TestAction
        link = Button.buttonLink [ Button.variant Button.Secondary ] "/dashboard" [ E.text "Dashboard" ]
    let rendered = TS.render link
    rendered `shouldSatisfy` String.contains (String.Pattern "<a")
    rendered `shouldSatisfy` String.contains (String.Pattern "href=\"/dashboard\"")
    rendered `shouldSatisfy` String.contains (String.Pattern "Dashboard")
  
  it "sets button type attribute" do
    let btn :: E.Element TestAction
        btn = Button.button [ Button.type_ Button.TypeSubmit ] [ E.text "Submit" ]
    let rendered = TS.render btn
    rendered `shouldSatisfy` String.contains (String.Pattern "type=\"submit\"")
