-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // gpu // webgpu // texture-array
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Texture Arrays and Bindless Textures
-- |
-- | ## Texture Arrays
-- | - texture2d_array: Multiple 2D textures in single binding
-- | - textureCube_array: Multiple cubemaps for skybox arrays
-- | - texture3d: Volumetric textures
-- |
-- | ## Bindless Textures
-- | - Indices instead of samplers for O(1) lookup
-- | - Dynamic texture count at runtime
-- | - Eliminates descriptor set limits
-- |
-- | ## Dependencies
-- | - Prelude
-- | - WebGPU.Types (GPUTextureDescriptor, GPUTextureViewDescriptor)
-- |
-- | ## Dependents
-- | - Shader.* (bindless sampling)
-- | - Material.* (array textures)

module Hydrogen.GPU.WebGPU.TextureArray
  ( -- * Texture Array
    TextureArrayDescriptor
  , maxArrayLayers
    
    -- * Bindless Textures
  , BindlessTextureIndex
  , BindlessSamplerIndex
  , maxBindlessTextures
  , maxBindlessSamplers
  , BindlessBinding
  , bindless
    
    -- * Texture Atlas
  , TextureAtlas
  , AtlasEntry
  , atlasEntry
  , withUVTransform
    
    -- * Virtual Textures
  , VirtualTexturePage
  , PageState(PageLoaded, PagePending, PageUnloaded)
  , VirtualTextureDescriptor
  , defaultVirtualTexture
  , virtualPage
  , loadPage
  , isPageReady
  
    -- * Types
  , GPUTextureDescriptor
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // texture // array
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture array descriptor
type TextureArrayDescriptor = 
  { baseTexture :: GPUTextureDescriptor
  , arrayLayers :: Int
  }

-- | Maximum array layers
maxArrayLayers :: Int
maxArrayLayers = 256

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // texture // sample
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bindless texture sample
-- |
-- | Instead of sampler2D<f32>, use:
-- | - textureSampleLevel(texture2d_array, sampler, uv, layer, level)
type BindlessTextureIndex = Int

-- | Bindless sampler slot
type BindlessSamplerIndex = Int

-- | Maximum bindless textures
maxBindlessTextures :: Int
maxBindlessTextures = 1024

-- | Maximum bindless samplers
maxBindlessSamplers :: Int
maxBindlessSamplers = 16

-- | Bindless texture binding
type BindlessBinding =
  { textureIndex :: BindlessTextureIndex
  , samplerIndex :: BindlessSamplerIndex
  }

-- | Create binding from indices
bindless :: BindlessTextureIndex -> BindlessSamplerIndex -> BindlessBinding
bindless ti si = { textureIndex: ti, samplerIndex: si }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // texture // atlas
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture atlas for bindless rendering
-- |
-- | Packs multiple textures into single texture with UV offset
type TextureAtlas =
  { texture :: GPUTextureDescriptor
  , entries :: Array AtlasEntry
  }

-- | Single texture in atlas
type AtlasEntry =
  { id :: Int
  , layer :: Int
  , uvOffset :: { u :: Number, v :: Number }
  , uvScale :: { u :: Number, v :: Number }
  }

-- | Create atlas entry
atlasEntry :: Int -> Int -> AtlasEntry
atlasEntry id layer = 
  { id
  , layer
  , uvOffset: { u: 0.0, v: 0.0 }
  , uvScale: { u: 1.0, v: 1.0 }
  }

-- | Apply UV transform to entry
withUVTransform :: AtlasEntry -> { u :: Number, v :: Number } -> { u :: Number, v :: Number } -> AtlasEntry
withUVTransform entry offset scale =
  entry { uvOffset = offset, uvScale = scale }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // virtual // texture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Virtual texture page (for mega-textures)
type VirtualTexturePage =
  { pageIndex :: Int
  , mipLevel :: Int
  , state :: PageState
  }

-- | Page state
data PageState = PageLoaded | PagePending | PageUnloaded

derive instance eqPageState :: Eq PageState

-- | Virtual texture descriptor
type VirtualTextureDescriptor =
  { tileSize :: Int
  , maxMipLevels :: Int
  , pagePoolSize :: Int
  }

-- | Default virtual texture (8K mega texture)
defaultVirtualTexture :: VirtualTextureDescriptor
defaultVirtualTexture =
  { tileSize: 256
  , maxMipLevels: 8
  , pagePoolSize: 64
  }

-- | Page from index
virtualPage :: Int -> Int -> VirtualTexturePage
virtualPage index mip = 
  { pageIndex: index
  , mipLevel: mip
  , state: PagePending
  }

-- | Mark page as loaded
loadPage :: VirtualTexturePage -> VirtualTexturePage
loadPage p = p { state = PageLoaded }

-- | Check if page is ready
isPageReady :: VirtualTexturePage -> Boolean
isPageReady p = p.state == PageLoaded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // type // placeholder
-- ═════════════════════════════════════════════════════════════════════════════

-- | Placeholder for GPUTextureDescriptor (import from Types in full implementation)
type GPUTextureDescriptor = Unit
