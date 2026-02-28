-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // attestation // merkle-tree
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | MerkleTree — Binary hash tree for cryptographic membership proofs.
-- |
-- | ## Design Philosophy
-- |
-- | A Merkle tree is a binary tree where:
-- | - Each leaf is a hash of data
-- | - Each internal node is a hash of its two children
-- | - The root hash commits to all leaves
-- |
-- | This enables efficient proofs that a piece of data is included in a set
-- | without revealing the entire set.
-- |
-- | ## Why Merkle Trees?
-- |
-- | At billion-agent scale, agents need:
-- | - Efficient verification of set membership
-- | - Compact proofs (O(log n) size)
-- | - Tamper detection for entire datasets
-- | - Foundation for blockchain-style commitments
-- |
-- | ## Pure Implementation
-- |
-- | This module uses SHA-256 for hashing. No FFI, no side effects.
-- | The tree structure is represented as pure data.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Attestation.SHA256 (hashing)
-- |
-- | ## Dependents
-- |
-- | - State proofs
-- | - Batch attestations
-- | - Set membership verification

module Hydrogen.Schema.Attestation.MerkleTree
  ( -- * MerkleTree Type
    MerkleTree
  , MerkleNode(..)
  , MerkleProof
  , ProofElement(..)
  
  -- * Construction
  , fromLeaves
  , fromBytesArray
  , singleton
  , empty
  
  -- * Accessors
  , root
  , rootHex
  , leaves
  , leafCount
  , depth
  , getLeaf
  , treeSize
  , isPowerOf2
  
  -- * Proof Operations
  , getProof
  , verifyProof
  , verifyProofBytes
  
  -- * Tree Operations
  , isValid
  , contains
  , isEmpty
  , isNotEmpty
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (>=)
  , (<)
  , (>)
  , (&&)
  , (||)
  , otherwise
  , map
  , not
  )

import Data.Array (length, index, snoc, foldl, concat, head, tail) as Array
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Int.Bits (shr, and) as Bits

import Hydrogen.Schema.Attestation.SHA256 
  ( SHA256Hash
  , sha256Bytes
  , toHex
  , toBytes
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // merkle tree type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A node in the Merkle tree.
-- |
-- | - Leaf: Contains a hash of data
-- | - Branch: Contains hash of two children concatenated
-- | - Empty: Represents a placeholder for incomplete trees
data MerkleNode
  = Leaf SHA256Hash
  | Branch SHA256Hash MerkleNode MerkleNode
  | Empty

derive instance eqMerkleNode :: Eq MerkleNode
derive instance ordMerkleNode :: Ord MerkleNode

instance showMerkleNode :: Show MerkleNode where
  show Empty = "Empty"
  show (Leaf h) = "(Leaf " <> toHex h <> ")"
  show (Branch h _ _) = "(Branch " <> toHex h <> " ...)"

-- | The complete Merkle tree.
-- |
-- | Stores the root node and the original leaf hashes for proof generation.
newtype MerkleTree = MerkleTree
  { root :: MerkleNode
  , leafHashes :: Array SHA256Hash
  }

derive instance eqMerkleTree :: Eq MerkleTree
derive instance ordMerkleTree :: Ord MerkleTree

instance showMerkleTree :: Show MerkleTree where
  show (MerkleTree t) = "(MerkleTree { leafCount: " <> show (Array.length t.leafHashes) <> " })"

-- | Element of a Merkle proof.
-- |
-- | Each element specifies a sibling hash and which side it's on.
data ProofElement
  = LeftSibling SHA256Hash   -- ^ Sibling is on the left
  | RightSibling SHA256Hash  -- ^ Sibling is on the right

derive instance eqProofElement :: Eq ProofElement
derive instance ordProofElement :: Ord ProofElement

instance showProofElement :: Show ProofElement where
  show (LeftSibling h) = "(L " <> toHex h <> ")"
  show (RightSibling h) = "(R " <> toHex h <> ")"

-- | A Merkle proof for a leaf.
-- |
-- | Array of sibling hashes from leaf to root.
type MerkleProof = Array ProofElement

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Merkle tree from an array of leaf hashes.
-- |
-- | Builds a balanced binary tree. If the leaf count is not a power of 2,
-- | the tree is padded with Empty nodes.
fromLeaves :: Array SHA256Hash -> MerkleTree
fromLeaves hashes =
  let rootNode = buildTree (map Leaf hashes)
  in MerkleTree { root: rootNode, leafHashes: hashes }

-- | Create a Merkle tree from an array of byte arrays.
-- |
-- | Each byte array is hashed to create a leaf.
fromBytesArray :: Array (Array Int) -> MerkleTree
fromBytesArray byteArrays =
  let hashes = map sha256Bytes byteArrays
  in fromLeaves hashes

-- | Create a single-leaf tree.
singleton :: SHA256Hash -> MerkleTree
singleton h = fromLeaves [h]

-- | Create an empty tree.
empty :: MerkleTree
empty = MerkleTree { root: Empty, leafHashes: [] }

-- | Build tree from a level of nodes.
-- |
-- | Recursively pairs nodes until only one root remains.
buildTree :: Array MerkleNode -> MerkleNode
buildTree nodes =
  case Array.length nodes of
    0 -> Empty
    1 -> fromMaybe Empty (Array.head nodes)
    _ -> buildTree (pairNodes nodes)

-- | Pair adjacent nodes into parent nodes.
pairNodes :: Array MerkleNode -> Array MerkleNode
pairNodes nodes = go nodes []
  where
    go :: Array MerkleNode -> Array MerkleNode -> Array MerkleNode
    go remaining acc =
      case Array.head remaining of
        Nothing -> acc
        Just first ->
          let rest = fromMaybe [] (Array.tail remaining)
          in case Array.head rest of
               Nothing -> 
                 -- Odd number of nodes: pair with Empty
                 Array.snoc acc (combineNodes first Empty)
               Just second ->
                 let rest2 = fromMaybe [] (Array.tail rest)
                 in go rest2 (Array.snoc acc (combineNodes first second))

-- | Combine two nodes into a parent.
combineNodes :: MerkleNode -> MerkleNode -> MerkleNode
combineNodes left right =
  let
    leftBytes = nodeToBytes left
    rightBytes = nodeToBytes right
    combinedHash = sha256Bytes (Array.concat [leftBytes, rightBytes])
  in
    Branch combinedHash left right

-- | Get bytes representation of a node's hash.
nodeToBytes :: MerkleNode -> Array Int
nodeToBytes Empty = zeroHash
nodeToBytes (Leaf h) = toBytes h
nodeToBytes (Branch h _ _) = toBytes h

-- | 32 zero bytes for empty nodes.
zeroHash :: Array Int
zeroHash = 
  [ 0, 0, 0, 0, 0, 0, 0, 0
  , 0, 0, 0, 0, 0, 0, 0, 0
  , 0, 0, 0, 0, 0, 0, 0, 0
  , 0, 0, 0, 0, 0, 0, 0, 0
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the root hash of the tree.
root :: MerkleTree -> Maybe SHA256Hash
root (MerkleTree t) = nodeHash t.root

-- | Get the root hash as hex string.
rootHex :: MerkleTree -> String
rootHex tree = case root tree of
  Nothing -> "empty"
  Just h -> toHex h

-- | Get all leaf hashes.
leaves :: MerkleTree -> Array SHA256Hash
leaves (MerkleTree t) = t.leafHashes

-- | Get the number of leaves.
leafCount :: MerkleTree -> Int
leafCount (MerkleTree t) = Array.length t.leafHashes

-- | Calculate tree depth.
-- |
-- | Depth is ceiling(log2(leafCount)) for non-empty trees.
depth :: MerkleTree -> Int
depth tree =
  let n = leafCount tree
  in if n == 0 then 0 else ceilLog2 n

-- | Ceiling of log base 2.
ceilLog2 :: Int -> Int
ceilLog2 n = go n 0
  where
    go :: Int -> Int -> Int
    go x acc
      | x < 2 = acc
      | otherwise = go (Bits.shr x 1) (acc + 1)

-- | Extract hash from a node.
nodeHash :: MerkleNode -> Maybe SHA256Hash
nodeHash Empty = Nothing
nodeHash (Leaf h) = Just h
nodeHash (Branch h _ _) = Just h

-- | Get a specific leaf by index.
-- |
-- | Returns Nothing if index is out of bounds.
getLeaf :: MerkleTree -> Int -> Maybe SHA256Hash
getLeaf (MerkleTree t) idx = Array.index t.leafHashes idx

-- | Total number of nodes in the tree.
-- |
-- | For a complete binary tree with n leaves: 2n - 1 nodes.
-- | For incomplete trees, this is an upper bound.
treeSize :: MerkleTree -> Int
treeSize tree =
  let n = leafCount tree
  in if n == 0 then 0 else 2 * n - 1

-- | Check if a number is a power of 2.
-- |
-- | Useful for determining if tree is perfectly balanced.
isPowerOf2 :: Int -> Boolean
isPowerOf2 n = n > 0 && Bits.and n (n - 1) == 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // proof operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a proof for a leaf at a given index.
-- |
-- | Returns Nothing if index is out of bounds.
getProof :: MerkleTree -> Int -> Maybe MerkleProof
getProof (MerkleTree t) idx =
  if idx < 0 || idx >= Array.length t.leafHashes
  then Nothing
  else Just (buildProof t.root idx (Array.length t.leafHashes))

-- | Build proof by traversing from root to leaf.
buildProof :: MerkleNode -> Int -> Int -> MerkleProof
buildProof node idx size = go node idx size []
  where
    go :: MerkleNode -> Int -> Int -> MerkleProof -> MerkleProof
    go Empty _ _ acc = acc
    go (Leaf _) _ _ acc = acc
    go (Branch _ left right) i s acc =
      let
        halfSize = s / 2
        isLeft = i < halfSize
      in
        if isLeft
        then 
          let sibling = fromMaybe (toBytes (sha256Bytes zeroHash)) (map toBytes (nodeHash right))
          in go left i halfSize (Array.snoc acc (RightSibling (sha256Bytes sibling)))
        else
          let sibling = fromMaybe (toBytes (sha256Bytes zeroHash)) (map toBytes (nodeHash left))
          in go right (i - halfSize) halfSize (Array.snoc acc (LeftSibling (sha256Bytes sibling)))

-- | Verify a proof for a leaf hash.
-- |
-- | Recomputes the root from the leaf and proof, compares to expected root.
verifyProof :: MerkleTree -> SHA256Hash -> MerkleProof -> Boolean
verifyProof tree leafHash proof =
  case root tree of
    Nothing -> false
    Just expectedRoot ->
      let computedRoot = computeRoot leafHash proof
      in toHex computedRoot == toHex expectedRoot

-- | Verify a proof for raw byte data.
verifyProofBytes :: MerkleTree -> Array Int -> MerkleProof -> Boolean
verifyProofBytes tree bytes proof =
  verifyProof tree (sha256Bytes bytes) proof

-- | Compute root hash from leaf and proof.
computeRoot :: SHA256Hash -> MerkleProof -> SHA256Hash
computeRoot leafHash proof =
  Array.foldl applyProofElement leafHash proof

-- | Apply one proof element to current hash.
applyProofElement :: SHA256Hash -> ProofElement -> SHA256Hash
applyProofElement current (LeftSibling sibling) =
  -- Sibling is on left: hash(sibling || current)
  sha256Bytes (Array.concat [toBytes sibling, toBytes current])
applyProofElement current (RightSibling sibling) =
  -- Sibling is on right: hash(current || sibling)
  sha256Bytes (Array.concat [toBytes current, toBytes sibling])

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // tree operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a tree is structurally valid.
-- |
-- | Verifies that internal node hashes are correctly computed.
isValid :: MerkleTree -> Boolean
isValid (MerkleTree t) = validateNode t.root

-- | Validate a single node recursively.
validateNode :: MerkleNode -> Boolean
validateNode Empty = true
validateNode (Leaf _) = true
validateNode (Branch h left right) =
  let
    leftBytes = nodeToBytes left
    rightBytes = nodeToBytes right
    expectedHash = sha256Bytes (Array.concat [leftBytes, rightBytes])
  in
    toHex h == toHex expectedHash && validateNode left && validateNode right

-- | Check if a leaf hash exists in the tree.
contains :: MerkleTree -> SHA256Hash -> Boolean
contains (MerkleTree t) targetHash =
  containsHelper t.leafHashes targetHash

-- | Search for hash in leaf array.
containsHelper :: Array SHA256Hash -> SHA256Hash -> Boolean
containsHelper arr target = go arr
  where
    targetHex = toHex target
    go :: Array SHA256Hash -> Boolean
    go remaining =
      case Array.head remaining of
        Nothing -> false
        Just h -> 
          if toHex h == targetHex
          then true
          else go (fromMaybe [] (Array.tail remaining))

-- | Check if tree is empty.
isEmpty :: MerkleTree -> Boolean
isEmpty tree = leafCount tree == 0

-- | Check if tree is not empty.
isNotEmpty :: MerkleTree -> Boolean
isNotEmpty tree = not (isEmpty tree)
