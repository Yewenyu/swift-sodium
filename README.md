# Swift-Sodium [![Build Status](https://travis-ci.com/jedisct1/swift-sodium.svg?branch=master)](https://travis-ci.com/jedisct1/swift-sodium)

Swift-Sodium provides a safe and easy to use interface to perform common cryptographic operations on macOS, iOS, tvOS and watchOS.

It leverages the [Sodium](https://download.libsodium.org/doc/) library, and although Swift is the primary target, the framework can also be used in Objective-C applications.

## Please help!

The current Swift-Sodium documentation is not great. Your help to improve it and make it awesome would be very appreciated!

## Usage

To add Swift-Sodium as dependency to your Xcode project, select `File` > `Swift Packages` > `Add Package Dependency`, enter its repository URL: `https://github.com/jedisct1/swift-sodium.git` and import `Sodium` as well as `Clibsodium`.

Then, to use it in your source code, add:

```swift
import Sodium
```

The Sodium library itself doesn't have to be installed on the system: the repository already includes a precompiled library for armv7, armv7s, arm64, as well as for the iOS simulator, WatchOS and Catalyst.

The `Clibsodium.xcframework` framework has been generated by the
[dist-build/apple-xcframework.sh](https://github.com/jedisct1/libsodium/blob/master/dist-build/apple-xcframework.sh)
script.

Running this script on Xcode 15.0b8 (`15A5229m`) on the revision `ac14901c30ae58f7cf7014b68f75d592e931bc82` of libsodium generates files identical to the ones present in this repository.

## Secret-key cryptography

Messages are encrypted and decrypted using the same secret key, this is also known as symmetric cryptography.

A key can be generated using the `key()` method, derived from a password using the Password Hashing API, or computed using a secret key and the peer's public key utilising the Key Exchange API.

### Authenticated encryption for a sequence of messages

```swift
let sodium = Sodium()
let message1 = "Message 1".bytes
let message2 = "Message 2".bytes
let message3 = "Message 3".bytes

let secretkey = sodium.secretStream.xchacha20poly1305.key()

/* stream encryption */

let stream_enc = sodium.secretStream.xchacha20poly1305.initPush(secretKey: secretkey)!
let header = stream_enc.header()
let encrypted1 = stream_enc.push(message: message1)!
let encrypted2 = stream_enc.push(message: message2)!
let encrypted3 = stream_enc.push(message: message3, tag: .FINAL)!

/* stream decryption */

let stream_dec = sodium.secretStream.xchacha20poly1305.initPull(secretKey: secretkey, header: header)!
let (message1_dec, tag1) = stream_dec.pull(cipherText: encrypted1)!
let (message2_dec, tag2) = stream_dec.pull(cipherText: encrypted2)!
let (message3_dec, tag3) = stream_dec.pull(cipherText: encrypted3)!
```

A stream is a sequence of messages, that will be encrypted as they depart, and, decrypted as they arrive. The encrypted messages are expected to be received in the same order as they were sent.

Streams can be arbitrarily long. This API can thus be used for file encryption, by splitting files into small chunks, so that the whole file doesn't need to reside in memory concurrently.

It can also be used to exchange a sequence of messages between two peers.

The decryption function automatically checks that chunks have been received without modification, and truncation or reordering.

A tag is attached to each message, and can be used to signal the end of a sub-sequence (`PUSH`), or the end of the string (`FINAL`).

### Authenticated encryption for single messages

```swift
let sodium = Sodium()
let message = "My Test Message".bytes
let secretKey = sodium.secretBox.key()
let encrypted: Bytes = sodium.secretBox.seal(message: message, secretKey: secretKey)!
if let decrypted = sodium.secretBox.open(nonceAndAuthenticatedCipherText: encrypted, secretKey: secretKey) {
    // authenticator is valid, decrypted contains the original message
}
```

This API encrypts a message. The decryption process will check that the messages haven't been tampered with before decrypting them.

Messages encrypted this way are independent: if multiple messages are sent this way, the recipient cannot detect if some messages have been duplicated, deleted or reordered without the sender including additional data with each message.

Optionally, `SecretBox` provides the ability to utilize a user-defined nonce via `seal(message: secretKey: nonce:)`.

## Public-key Cryptography

With public-key cryptography, each peer has two keys: a secret (private) key, that has to remain secret, and a public key that anyone can use to send an encrypted message to that peer. That public key can be only be used to encrypt a message. The corresponding secret is required to decrypt it.

### Authenticated Encryption

```swift
let sodium = Sodium()
let aliceKeyPair = sodium.box.keyPair()!
let bobKeyPair = sodium.box.keyPair()!
let message = "My Test Message".bytes

let encryptedMessageFromAliceToBob: Bytes =
    sodium.box.seal(message: message,
                    recipientPublicKey: bobKeyPair.publicKey,
                    senderSecretKey: aliceKeyPair.secretKey)!

let messageVerifiedAndDecryptedByBob =
    sodium.box.open(nonceAndAuthenticatedCipherText: encryptedMessageFromAliceToBob,
                    senderPublicKey: aliceKeyPair.publicKey,
                    recipientSecretKey: bobKeyPair.secretKey)
```

This operation encrypts and sends a message to someone using their public key.

The recipient has to know the sender's public key as well, and will reject a message that doesn't appear to be valid for the expected public key.

`seal()` automatically generates a nonce and prepends it to the ciphertext. `open()` extracts the nonce and decrypts the ciphertext.

Optionally, `Box` provides the ability to utilize a user-defined nonce via `seal(message: recipientPublicKey: senderSecretKey: nonce:)`.

The `Box` class also provides alternative functions and parameters to deterministically generate key pairs, to retrieve the nonce and/or the authenticator, and to detach them from the original message.

## Anonymous Encryption (Sealed Boxes)

```swift
let sodium = Sodium()
let bobKeyPair = sodium.box.keyPair()!
let message = "My Test Message".bytes

let encryptedMessageToBob =
    sodium.box.seal(message: message, recipientPublicKey: bobKeyPair.publicKey)!

let messageDecryptedByBob =
    sodium.box.open(anonymousCipherText: encryptedMessageToBob,
                    recipientPublicKey: bobKeyPair.publicKey,
                    recipientSecretKey: bobKeyPair.secretKey)
```

`seal()` generates an ephemeral keypair, uses the ephemeral secret key in the encryption process, combines the ephemeral public key with the ciphertext, then destroys the keypair.

The sender cannot decrypt the resulting ciphertext. `open()` extracts the public key and decrypts using the recipient's secret key. Message integrity is verified, but the sender's identity cannot be correlated to the ciphertext.

## Key exchange

```swift
let sodium = Sodium()
let aliceKeyPair = sodium.keyExchange.keyPair()!
let bobKeyPair = sodium.keyExchange.keyPair()!

let sessionKeyPairForAlice = sodium.keyExchange.sessionKeyPair(publicKey: aliceKeyPair.publicKey,
    secretKey: aliceKeyPair.secretKey, otherPublicKey: bobKeyPair.publicKey, side: .CLIENT)!
let sessionKeyPairForBob = sodium.keyExchange.sessionKeyPair(publicKey: bobKeyPair.publicKey,
    secretKey: bobKeyPair.secretKey, otherPublicKey: aliceKeyPair.publicKey, side: .SERVER)!

let aliceToBobKeyEquality = sodium.utils.equals(sessionKeyPairForAlice.tx, sessionKeyPairForBob.rx) // true
let bobToAliceKeyEquality = sodium.utils.equals(sessionKeyPairForAlice.rx, sessionKeyPairForBob.tx) // true
```

## Public-key signatures

Signatures allow multiple parties to verify the authenticity of a public message, using the public key of the author's message.

This can be especially useful to sign software updates.

### Detached signatures

The signature is generated separately to the original message.

```swift
let sodium = Sodium()
let message = "My Test Message".bytes
let keyPair = sodium.sign.keyPair()!
let signature = sodium.sign.signature(message: message, secretKey: keyPair.secretKey)!
if sodium.sign.verify(message: message,
                      publicKey: keyPair.publicKey,
                      signature: signature) {
    // signature is valid
}
```

### Attached signatures

The signature is generated and prepended to the original message.

```swift
let sodium = Sodium()
let message = "My Test Message".bytes
let keyPair = sodium.sign.keyPair()!
let signedMessage = sodium.sign.sign(message: message, secretKey: keyPair.secretKey)!
if let unsignedMessage = sodium.sign.open(signedMessage: signedMessage, publicKey: keyPair.publicKey) {
    // signature is valid
}
```

## Hashing

### Deterministic hashing

Hashing effectively "fingerprints" input data, no matter what its size, and returns a fixed length "digest".

The digest length can be configured as required, from 16 to 64 bytes.

```swift
let sodium = Sodium()
let message = "My Test Message".bytes
let hash = sodium.genericHash.hash(message: message)
let hashOfSize32Bytes = sodium.genericHash.hash(message: message, outputLength: 32)
```

### Keyed hashing

```swift
let sodium = Sodium()
let message = "My Test Message".bytes
let key = "Secret key".bytes
let h = sodium.genericHash.hash(message: message, key: key)
```

### Streaming

```swift
let sodium = Sodium()
let message1 = "My Test ".bytes
let message2 = "Message".bytes
let key = "Secret key".bytes
let stream = sodium.genericHash.initStream(key: key)!
stream.update(input: message1)
stream.update(input: message2)
let h = stream.final()
```

### Short-output hashing (SipHash)

```swift
let sodium = Sodium()
let message = "My Test Message".bytes
let key = sodium.randomBytes.buf(length: sodium.shortHash.KeyBytes)!
let h = sodium.shortHash.hash(message: message, key: key)
```

## Random numbers generation

Random number generation produces cryptographically secure pseudorandom numbers suitable as key material.

```swift
let sodium = Sodium()
let randomBytes = sodium.randomBytes.buf(length: 1000)!
let seed = "0123456789abcdef0123456789abcdef".bytes
let stream = sodium.randomBytes.deterministic(length: 1000, seed: seed)!
```

Use `RandomBytes.Generator` as a generator to produce cryptographically secure pseudorandom numbers.

```swift
var rng = RandomBytes.Generator()
let randomUInt32 = UInt32.random(in: 0...10, using: &rng)
let randomUInt64 = UInt64.random(in: 0...10, using: &rng)
let randomInt = Int.random(in: 0...10, using: &rng)
let randomDouble = Double.random(in: 0...1, using: &rng)
```

## Password hashing

Password hashing provides the ability to derive key material from a low-entropy password. Password hashing functions are designed to be expensive to hamper brute force attacks, thus the computational and memory parameters may be user-defined.

```swift
let sodium = Sodium()
let password = "Correct Horse Battery Staple".bytes
let hashedStr = sodium.pwHash.str(passwd: password,
                                  opsLimit: sodium.pwHash.OpsLimitInteractive,
                                  memLimit: sodium.pwHash.MemLimitInteractive)!

if sodium.pwHash.strVerify(hash: hashedStr, passwd: password) {
    // Password matches the given hash string
} else {
    // Password doesn't match the given hash string
}

if sodium.pwHash.strNeedsRehash(hash: hashedStr,
                                opsLimit: sodium.pwHash.OpsLimitInteractive,
                                memLimit: sodium.pwHash.MemLimitInteractive) {
    // Previously hashed password should be recomputed because the way it was
    // hashed doesn't match the current algorithm and the given parameters.
}
```

## Authentication tags

The `sodium.auth.tag()` function computes an authentication tag (HMAC) using a message and a key. Parties knowing the key can then verify the authenticity of the message using the same parameters and the `sodium.auth.verify()` function.

Authentication tags are not signatures: the same key is used both for computing and verifying a tag. Therefore, verifiers can also compute tags for arbitrary messages.

```swift
let sodium = Sodium()
let input = "test".bytes
let key = sodium.auth.key()
let tag = sodium.auth.tag(message: input, secretKey: key)!
let tagIsValid = sodium.auth.verify(message: input, secretKey: key, tag: tag)
```

## Key derivation

The `sodium.keyDerivation.derive()` function generates a subkey using an input (master) key, an index, and a 8 bytes string identifying the context. Up to (2^64) - 1 subkeys can be generated for each context, by incrementing the index.

```swift
let sodium = Sodium()
let secretKey = sodium.keyDerivation.keygen()!

let subKey1 = sodium.keyDerivation.derive(secretKey: secretKey,
                                          index: 0, length: 32,
                                          context: "Context!")
let subKey2 = sodium.keyDerivation.derive(secretKey: secretKey,
                                          index: 1, length: 32,
                                          context: "Context!")
```

## Utilities

### Zeroing memory

```swift
let sodium = Sodium()
var dataToZero = "Message".bytes
sodium.utils.zero(&dataToZero)
```

### Constant-time comparison

```swift
let sodium = Sodium()
let secret1 = "Secret key".bytes
let secret2 = "Secret key".bytes
let equality = sodium.utils.equals(secret1, secret2)
```

### Padding

```swift
let sodium = Sodium()
var bytes = "test".bytes

// make bytes.count a multiple of 16
sodium.utils.pad(bytes: &bytes, blockSize: 16)!

// restore original size
sodium.utils.unpad(bytes: &bytes, blockSize: 16)!
```

Padding can be useful to hide the length of a message before it is encrypted.

### Constant-time hexadecimal encoding

```swift
let sodium = Sodium()
let bytes = "Secret key".bytes
let hex = sodium.utils.bin2hex(bytes)
```

### Hexadecimal decoding

```swift
let sodium = Sodium()
let data1 = sodium.utils.hex2bin("deadbeef")
let data2 = sodium.utils.hex2bin("de:ad be:ef", ignore: " :")
```

### Constant-time base64 encoding

```swift
let sodium = Sodium()
let b64 = sodium.utils.bin2base64("data".bytes)!
let b64_2 = sodium.utils.bin2base64("data".bytes, variant: .URLSAFE_NO_PADDING)!
```

### Base64 decoding

```swift
let data1 = sodium.utils.base642bin(b64)
let data2 = sodium.utils.base642bin(b64, ignore: " \n")
let data3 = sodium.utils.base642bin(b64_2, variant: .URLSAFE_NO_PADDING, ignore: " \n")
```

## Helpers to build custom constructions

Only use the functions below if you know that you absolutely need them, and know how to use them correctly.

## Unauthenticated encryption

The `sodium.stream.xor()` function combines (using the XOR operation) an arbitrary-long input with the output of a deterministic key stream derived from a key and a nonce. The same operation applied twice produces the original input.

No authentication tag is added to the output. The data can be tampered with; an adversary can flip arbitrary bits.

In order to encrypt data using a secret key, the `SecretBox` class is likely to be what you are looking for.

In order to generate a deterministic stream out of a seed, the `RandomBytes.deterministic_rand()` function is likely to be what you need.

```swift
let sodium = Sodium()
let input = "test".bytes
let key = sodium.stream.key()
let (output, nonce) = sodium.stream.xor(input: input, secretKey: key)!
let twice = sodium.stream.xor(input: output, nonce: nonce, secretKey: key)!

XCTAssertEqual(input, twice)
```

## Algorithms

* Stream ciphers: XChaCha20, XSalsa20
* MACs: Poly1305, HMAC-SHA512/256
* Hash function: BLAKE2B
* Key exchange: X25519
* Signatures: Ed25519
