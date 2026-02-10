import Script from 'next/script'

export default function AppLayout({
  children,
}: {
  children: React.ReactNode
}) {
  return (
    <>
      <div id="straylight-app">{children}</div>
      <Script src="/straylight.js" strategy="afterInteractive" />
    </>
  )
}
