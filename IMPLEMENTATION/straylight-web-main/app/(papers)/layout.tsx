export default function PapersLayout({
  children,
}: {
  children: React.ReactNode
}) {
  // No straylight.js, no #straylight-app - papers render directly
  return <>{children}</>
}
