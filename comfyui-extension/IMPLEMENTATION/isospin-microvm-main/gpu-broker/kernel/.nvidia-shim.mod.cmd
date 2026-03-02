savedcmd_nvidia-shim.mod := printf '%s\n'   nvidia-shim.o | awk '!x[$$0]++ { print("./"$$0) }' > nvidia-shim.mod
