// PureScript takes over rendering - this is the SSR fallback
// The actual content is rendered by public/straylight.js

export default function Home() {
  return (
    <script
      dangerouslySetInnerHTML={{
        __html: `window.__STRAYLIGHT_PAGE__ = { pageType: 'home', currentPath: '/' };`
      }}
    />
  )
}
