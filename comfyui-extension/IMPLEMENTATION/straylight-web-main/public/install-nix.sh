#!/bin/sh
# Straylight Nix Installer
# curl -sSfL https://straylight.dev/install-nix.sh | sh
#
# Installs straylight-nix (Nix fork with builtins.wasm and enhanced features).

set -e

STRAYLIGHT_NIX_VERSION="3.0.0"
STRAYLIGHT_NIX_URL="https://github.com/straylight-software/nix/releases/download/v${STRAYLIGHT_NIX_VERSION}"

echo "╔══════════════════════════════════════════════════════════════════╗"
echo "║              Straylight Nix Installer                            ║"
echo "╚══════════════════════════════════════════════════════════════════╝"
echo ""

# Detect platform
detect_platform() {
	OS="$(uname -s)"
	ARCH="$(uname -m)"

	case "$OS" in
	Linux) OS="linux" ;;
	Darwin) OS="darwin" ;;
	*)
		echo "Unsupported OS: $OS"
		exit 1
		;;
	esac

	case "$ARCH" in
	x86_64) ARCH="x86_64" ;;
	aarch64) ARCH="aarch64" ;;
	arm64) ARCH="aarch64" ;;
	*)
		echo "Unsupported architecture: $ARCH"
		exit 1
		;;
	esac

	echo "${ARCH}-${OS}"
}

# Install straylight-nix
install_nix() {
	PLATFORM=$(detect_platform)
	TARBALL="nix-${STRAYLIGHT_NIX_VERSION}-${PLATFORM}.tar.xz"
	TARBALL_URL="${STRAYLIGHT_NIX_URL}/${TARBALL}"

	echo ":: Platform: ${PLATFORM}"
	echo ":: Downloading straylight-nix ${STRAYLIGHT_NIX_VERSION}..."

	TMPDIR=$(mktemp -d)
	trap "rm -rf $TMPDIR" EXIT

	curl -sSfL -o "${TMPDIR}/${TARBALL}" "${TARBALL_URL}"

	echo ":: Extracting..."
	tar -xf "${TMPDIR}/${TARBALL}" -C "${TMPDIR}"

	echo ":: Running installer..."
	"${TMPDIR}/nix-${STRAYLIGHT_NIX_VERSION}-${PLATFORM}/install" --no-confirm
}

if ! command -v nix >/dev/null 2>&1; then
	install_nix

	# Source nix for this session
	if [ -e '/nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh' ]; then
		. '/nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh'
	fi
else
	echo ":: Nix already installed: $(nix --version)"
	echo ":: To upgrade, uninstall first: /nix/nix-installer uninstall"
fi

# Configure straylight registry
echo ":: Configuring straylight registry..."
mkdir -p ~/.config/nix

nix registry add straylight github:straylight-software/aleph 2>/dev/null || true

echo ""
echo ":: Installation complete!"
echo ""
echo "straylight-nix features:"
echo "  - builtins.wasm for WebAssembly module loading"
echo "  - Enhanced caching and performance"
echo ""
echo "Usage:"
echo "  nix run straylight#<package>"
echo "  nix develop straylight"
echo ""

# Install Determinate Nix if not present
if ! command -v nix >/dev/null 2>&1; then
	echo ":: Installing Determinate Nix..."
	curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install --no-confirm

	# Source nix for this session
	if [ -e '/nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh' ]; then
		. '/nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh'
	fi
else
	echo ":: Nix already installed: $(nix --version)"
fi

# Configure straylight-nix overlay
echo ":: Configuring straylight-nix..."
mkdir -p ~/.config/nix

# Add straylight flake registry
nix registry add straylight github:straylight-software/aleph 2>/dev/null || true

# Enable flakes if not already
if ! grep -q "experimental-features" ~/.config/nix/nix.conf 2>/dev/null; then
	echo "experimental-features = nix-command flakes" >>~/.config/nix/nix.conf
fi

echo ""
echo ":: Installation complete!"
echo ""
echo "You can now use straylight-nix:"
echo "  nix run straylight#<package>"
echo "  nix develop straylight"
echo ""
