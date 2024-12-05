import Foundation
import Clibsodium

public struct Aead {
//    public let aegis128l = Aegis128L()
//    public let aegis256 = Aegis256()
    public let aes256gcm = Aes256Gcm()
    public let xchacha20poly1305ietf = XChaCha20Poly1305Ietf()
    public static let salsa208Poly1305 = Salsa208Poly1305()
}

// Aegis128L

//extension Aead {
//    public struct Aegis128L {
//        public let ABytes = Int(crypto_aead_aegis128l_abytes())
//        public typealias MAC = Bytes
//    }
//}
//
//extension Aead.Aegis128L {
//    /**
//     Encrypts a message with a shared secret key.
//
//     - Parameter message: The message to encrypt.
//     - Parameter secretKey: The shared secret key.
//     - Parameter additionalData: A typical use for these data is to authenticate version numbers, timestamps or monotonically increasing counters
//
//     - Returns: A `Bytes` object containing the nonce and authenticated ciphertext.
//     */
//    public func encrypt(message: Bytes, secretKey: Key, additionalData: Bytes? = nil) -> Bytes? {
//        guard let (authenticatedCipherText, nonce): (Bytes, Nonce) = encrypt(
//            message: message,
//            secretKey: secretKey,
//            additionalData: additionalData
//        ) else { return nil }
//
//        return nonce + authenticatedCipherText
//    }
//
//    /**
//     Encrypts a message with a shared secret key.
//
//     - Parameter message: The message to encrypt.
//     - Parameter secretKey: The shared secret key.
//     - Parameter additionalData: A typical use for these data is to authenticate version numbers, timestamps or monotonically increasing counters
//
//     - Returns: The authenticated ciphertext and encryption nonce.
//     */
//    public func encrypt(message: Bytes, secretKey: Key, additionalData: Bytes? = nil) -> (authenticatedCipherText: Bytes, nonce: Nonce)? {
//        guard secretKey.count == KeyBytes else { return nil }
//
//        var authenticatedCipherText = Bytes(count: message.count + ABytes)
//        var authenticatedCipherTextLen: UInt64 = 0
//        let nonce = self.nonce()
//
//        guard .SUCCESS == crypto_aead_aegis128l_encrypt (
//            &authenticatedCipherText, &authenticatedCipherTextLen,
//            message, UInt64(message.count),
//            additionalData, UInt64(additionalData?.count ?? 0),
//            nil, nonce, secretKey
//        ).exitCode else { return nil }
//
//        return (authenticatedCipherText: authenticatedCipherText, nonce: nonce)
//    }
//}

//extension Aead.Aegis128L {
//    /**
//     Decrypts a message with a shared secret key.
//
//     - Parameter nonceAndAuthenticatedCipherText: A `Bytes` object containing the nonce and authenticated ciphertext.
//     - Parameter secretKey: The shared secret key.
//     - Parameter additionalData: Must be used same `Bytes` that was used to encrypt, if `Bytes` deferred will return nil
//
//     - Returns: The decrypted message.
//     */
//    public func decrypt(nonceAndAuthenticatedCipherText: Bytes, secretKey: Key, additionalData: Bytes? = nil) -> Bytes? {
//        guard nonceAndAuthenticatedCipherText.count >= ABytes + NonceBytes else { return nil }
//
//        let nonce = nonceAndAuthenticatedCipherText[..<NonceBytes].bytes as Nonce
//        let authenticatedCipherText = nonceAndAuthenticatedCipherText[NonceBytes...].bytes
//
//        return decrypt(authenticatedCipherText: authenticatedCipherText, secretKey: secretKey, nonce: nonce, additionalData: additionalData)
//    }
//
//    /**
//     Decrypts a message with a shared secret key.
//
//     - Parameter authenticatedCipherText: A `Bytes` object containing authenticated ciphertext.
//     - Parameter secretKey: The shared secret key.
//     - Parameter additionalData: Must be used same `Bytes` that was used to encrypt, if `Bytes` deferred will return nil
//
//     - Returns: The decrypted message.
//     */
//    public func decrypt(authenticatedCipherText: Bytes, secretKey: Key, nonce: Nonce, additionalData: Bytes? = nil) -> Bytes? {
//        guard authenticatedCipherText.count >= ABytes else { return nil }
//
//        var message = Bytes(count: authenticatedCipherText.count - ABytes)
//        var messageLen: UInt64 = 0
//
//        guard .SUCCESS == crypto_aead_aegis128l_decrypt (
//            &message, &messageLen,
//            nil,
//            authenticatedCipherText, UInt64(authenticatedCipherText.count),
//            additionalData, UInt64(additionalData?.count ?? 0),
//            nonce, secretKey
//        ).exitCode else { return nil }
//
//        return message
//    }
//}
//
//extension Aead.Aegis128L: NonceGenerator {
//    public typealias Nonce = Bytes
//    public var NonceBytes: Int { return Int(crypto_aead_aegis128l_npubbytes()) }
//}
//
//extension Aead.Aegis128L: SecretKeyGenerator {
//    public var KeyBytes: Int { return Int(crypto_aead_aegis128l_keybytes()) }
//    public typealias Key = Bytes
//
//    public static var keygen: (UnsafeMutablePointer<UInt8>) -> Void = crypto_aead_aegis128l_keygen
//}

// Aegis256

//extension Aead {
//    public struct Aegis256 {
//        public let ABytes = Int(crypto_aead_aegis256_abytes())
//        public typealias MAC = Bytes
//    }
//}
//
//extension Aead.Aegis256 {
//    /**
//     Encrypts a message with a shared secret key.
//
//     - Parameter message: The message to encrypt.
//     - Parameter secretKey: The shared secret key.
//     - Parameter additionalData: A typical use for these data is to authenticate version numbers, timestamps or monotonically increasing counters
//
//     - Returns: A `Bytes` object containing the nonce and authenticated ciphertext.
//     */
//    public func encrypt(message: Bytes, secretKey: Key, additionalData: Bytes? = nil) -> Bytes? {
//        guard let (authenticatedCipherText, nonce): (Bytes, Nonce) = encrypt(
//            message: message,
//            secretKey: secretKey,
//            additionalData: additionalData
//        ) else { return nil }
//
//        return nonce + authenticatedCipherText
//    }
//
//    /**
//     Encrypts a message with a shared secret key.
//
//     - Parameter message: The message to encrypt.
//     - Parameter secretKey: The shared secret key.
//     - Parameter additionalData: A typical use for these data is to authenticate version numbers, timestamps or monotonically increasing counters
//
//     - Returns: The authenticated ciphertext and encryption nonce.
//     */
//    public func encrypt(message: Bytes, secretKey: Key, additionalData: Bytes? = nil) -> (authenticatedCipherText: Bytes, nonce: Nonce)? {
//        guard secretKey.count == KeyBytes else { return nil }
//
//        var authenticatedCipherText = Bytes(count: message.count + ABytes)
//        var authenticatedCipherTextLen: UInt64 = 0
//        let nonce = self.nonce()
//
//        guard .SUCCESS == crypto_aead_aegis256_encrypt (
//            &authenticatedCipherText, &authenticatedCipherTextLen,
//            message, UInt64(message.count),
//            additionalData, UInt64(additionalData?.count ?? 0),
//            nil, nonce, secretKey
//        ).exitCode else { return nil }
//
//        return (authenticatedCipherText: authenticatedCipherText, nonce: nonce)
//    }
//}
//
//extension Aead.Aegis256 {
//    /**
//     Decrypts a message with a shared secret key.
//
//     - Parameter nonceAndAuthenticatedCipherText: A `Bytes` object containing the nonce and authenticated ciphertext.
//     - Parameter secretKey: The shared secret key.
//     - Parameter additionalData: Must be used same `Bytes` that was used to encrypt, if `Bytes` deferred will return nil
//
//     - Returns: The decrypted message.
//     */
//    public func decrypt(nonceAndAuthenticatedCipherText: Bytes, secretKey: Key, additionalData: Bytes? = nil) -> Bytes? {
//        guard nonceAndAuthenticatedCipherText.count >= ABytes + NonceBytes else { return nil }
//
//        let nonce = nonceAndAuthenticatedCipherText[..<NonceBytes].bytes as Nonce
//        let authenticatedCipherText = nonceAndAuthenticatedCipherText[NonceBytes...].bytes
//
//        return decrypt(authenticatedCipherText: authenticatedCipherText, secretKey: secretKey, nonce: nonce, additionalData: additionalData)
//    }
//
//    /**
//     Decrypts a message with a shared secret key.
//
//     - Parameter authenticatedCipherText: A `Bytes` object containing authenticated ciphertext.
//     - Parameter secretKey: The shared secret key.
//     - Parameter additionalData: Must be used same `Bytes` that was used to encrypt, if `Bytes` deferred will return nil
//
//     - Returns: The decrypted message.
//     */
//    public func decrypt(authenticatedCipherText: Bytes, secretKey: Key, nonce: Nonce, additionalData: Bytes? = nil) -> Bytes? {
//        guard authenticatedCipherText.count >= ABytes else { return nil }
//
//        var message = Bytes(count: authenticatedCipherText.count - ABytes)
//        var messageLen: UInt64 = 0
//
//        guard .SUCCESS == crypto_aead_aegis256_decrypt (
//            &message, &messageLen,
//            nil,
//            authenticatedCipherText, UInt64(authenticatedCipherText.count),
//            additionalData, UInt64(additionalData?.count ?? 0),
//            nonce, secretKey
//        ).exitCode else { return nil }
//
//        return message
//    }
//}
//
//extension Aead.Aegis256: NonceGenerator {
//    public typealias Nonce = Bytes
//    public var NonceBytes: Int { return Int(crypto_aead_aegis256_npubbytes()) }
//}
//
//extension Aead.Aegis256: SecretKeyGenerator {
//    public var KeyBytes: Int { return Int(crypto_aead_aegis256_keybytes()) }
//    public typealias Key = Bytes
//
//    public static var keygen: (UnsafeMutablePointer<UInt8>) -> Void = crypto_aead_aegis256_keygen
//}

// XChaCha20Poly1305

extension Aead {
    public struct XChaCha20Poly1305Ietf {
        public let ABytes = Int(crypto_aead_xchacha20poly1305_ietf_abytes())
        public typealias MAC = Bytes
    }
}

extension Aead.XChaCha20Poly1305Ietf {
    /**
     Encrypts a message with a shared secret key.

     - Parameter message: The message to encrypt.
     - Parameter secretKey: The shared secret key.
     - Parameter additionalData: A typical use for these data is to authenticate version numbers, timestamps or monotonically increasing counters

     - Returns: A `Bytes` object containing the nonce and authenticated ciphertext.
     */
    public func encrypt(message: Bytes, secretKey: Key, additionalData: Bytes? = nil) -> Bytes? {
        guard let (authenticatedCipherText, nonce): (Bytes, Nonce) = encrypt(
            message: message,
            secretKey: secretKey,
            additionalData: additionalData
        ) else { return nil }

        return nonce + authenticatedCipherText
    }

    /**
     Encrypts a message with a shared secret key.

     - Parameter message: The message to encrypt.
     - Parameter secretKey: The shared secret key.
     - Parameter additionalData: A typical use for these data is to authenticate version numbers, timestamps or monotonically increasing counters

     - Returns: The authenticated ciphertext and encryption nonce.
     */
    public func encrypt(message: Bytes, secretKey: Key, additionalData: Bytes? = nil) -> (authenticatedCipherText: Bytes, nonce: Nonce)? {
        guard secretKey.count == KeyBytes else { return nil }

        var authenticatedCipherText = Bytes(count: message.count + ABytes)
        var authenticatedCipherTextLen: UInt64 = 0
        let nonce = self.nonce()

        guard .SUCCESS == crypto_aead_xchacha20poly1305_ietf_encrypt (
            &authenticatedCipherText, &authenticatedCipherTextLen,
            message, UInt64(message.count),
            additionalData, UInt64(additionalData?.count ?? 0),
            nil, nonce, secretKey
        ).exitCode else { return nil }

        return (authenticatedCipherText: authenticatedCipherText, nonce: nonce)
    }
}

extension Aead.XChaCha20Poly1305Ietf {
    /**
     Decrypts a message with a shared secret key.

     - Parameter nonceAndAuthenticatedCipherText: A `Bytes` object containing the nonce and authenticated ciphertext.
     - Parameter secretKey: The shared secret key.
     - Parameter additionalData: Must be used same `Bytes` that was used to encrypt, if `Bytes` deferred will return nil

     - Returns: The decrypted message.
     */
    public func decrypt(nonceAndAuthenticatedCipherText: Bytes, secretKey: Key, additionalData: Bytes? = nil) -> Bytes? {
        guard nonceAndAuthenticatedCipherText.count >= ABytes + NonceBytes else { return nil }

        let nonce = nonceAndAuthenticatedCipherText[..<NonceBytes].bytes as Nonce
        let authenticatedCipherText = nonceAndAuthenticatedCipherText[NonceBytes...].bytes

        return decrypt(authenticatedCipherText: authenticatedCipherText, secretKey: secretKey, nonce: nonce, additionalData: additionalData)
    }

    /**
     Decrypts a message with a shared secret key.

     - Parameter authenticatedCipherText: A `Bytes` object containing authenticated ciphertext.
     - Parameter secretKey: The shared secret key.
     - Parameter additionalData: Must be used same `Bytes` that was used to encrypt, if `Bytes` deferred will return nil

     - Returns: The decrypted message.
     */
    public func decrypt(authenticatedCipherText: Bytes, secretKey: Key, nonce: Nonce, additionalData: Bytes? = nil) -> Bytes? {
        guard authenticatedCipherText.count >= ABytes else { return nil }

        var message = Bytes(count: authenticatedCipherText.count - ABytes)
        var messageLen: UInt64 = 0

        guard .SUCCESS == crypto_aead_xchacha20poly1305_ietf_decrypt (
            &message, &messageLen,
            nil,
            authenticatedCipherText, UInt64(authenticatedCipherText.count),
            additionalData, UInt64(additionalData?.count ?? 0),
            nonce, secretKey
        ).exitCode else { return nil }

        return message
    }
}

extension Aead.XChaCha20Poly1305Ietf: NonceGenerator {
    public typealias Nonce = Bytes
    public var NonceBytes: Int { return Int(crypto_aead_xchacha20poly1305_ietf_npubbytes()) }
}

extension Aead.XChaCha20Poly1305Ietf: SecretKeyGenerator {
    public var KeyBytes: Int { return Int(crypto_aead_xchacha20poly1305_ietf_keybytes()) }
    public typealias Key = Bytes

    public static var keygen: (UnsafeMutablePointer<UInt8>) -> Void = crypto_aead_xchacha20poly1305_ietf_keygen
}


// AES256-GCM

extension Aead {
    public struct Aes256Gcm {
        public let ABytes = Int(crypto_aead_aes256gcm_abytes())
        public typealias MAC = Bytes
    }
}

extension Aead.Aes256Gcm {
    /**
     Encrypts a message with a shared secret key.

     - Parameter message: The message to encrypt.
     - Parameter secretKey: The shared secret key.
     - Parameter additionalData: A typical use for these data is to authenticate version numbers, timestamps or monotonically increasing counters

     - Returns: A `Bytes` object containing the nonce and authenticated ciphertext.
     */
    public func encrypt(message: Bytes, secretKey: Key, additionalData: Bytes? = nil) -> Bytes? {
        guard let (authenticatedCipherText, nonce): (Bytes, Nonce) = encrypt(
            message: message,
            secretKey: secretKey,
            additionalData: additionalData
        ) else { return nil }

        return nonce + authenticatedCipherText
    }

    /**
     Encrypts a message with a shared secret key.

     - Parameter message: The message to encrypt.
     - Parameter secretKey: The shared secret key.
     - Parameter additionalData: A typical use for these data is to authenticate version numbers, timestamps or monotonically increasing counters

     - Returns: The authenticated ciphertext and encryption nonce.
     */
    public func encrypt(message: Bytes, secretKey: Key, additionalData: Bytes? = nil) -> (authenticatedCipherText: Bytes, nonce: Nonce)? {
        guard secretKey.count == KeyBytes else { return nil }

        var authenticatedCipherText = Bytes(count: message.count + ABytes)
        var authenticatedCipherTextLen: UInt64 = 0
        let nonce = self.nonce()

        guard .SUCCESS == crypto_aead_aes256gcm_encrypt (
            &authenticatedCipherText, &authenticatedCipherTextLen,
            message, UInt64(message.count),
            additionalData, UInt64(additionalData?.count ?? 0),
            nil, nonce, secretKey
        ).exitCode else { return nil }

        return (authenticatedCipherText: authenticatedCipherText, nonce: nonce)
    }
}

extension Aead.Aes256Gcm {
    /**
     Decrypts a message with a shared secret key.

     - Parameter nonceAndAuthenticatedCipherText: A `Bytes` object containing the nonce and authenticated ciphertext.
     - Parameter secretKey: The shared secret key.
     - Parameter additionalData: Must be used same `Bytes` that was used to encrypt, if `Bytes` deferred will return nil

     - Returns: The decrypted message.
     */
    public func decrypt(nonceAndAuthenticatedCipherText: Bytes, secretKey: Key, additionalData: Bytes? = nil) -> Bytes? {
        guard nonceAndAuthenticatedCipherText.count >= ABytes + NonceBytes else { return nil }

        let nonce = nonceAndAuthenticatedCipherText[..<NonceBytes].bytes as Nonce
        let authenticatedCipherText = nonceAndAuthenticatedCipherText[NonceBytes...].bytes

        return decrypt(authenticatedCipherText: authenticatedCipherText, secretKey: secretKey, nonce: nonce, additionalData: additionalData)
    }

    /**
     Decrypts a message with a shared secret key.

     - Parameter authenticatedCipherText: A `Bytes` object containing authenticated ciphertext.
     - Parameter secretKey: The shared secret key.
     - Parameter additionalData: Must be used same `Bytes` that was used to encrypt, if `Bytes` deferred will return nil

     - Returns: The decrypted message.
     */
    public func decrypt(authenticatedCipherText: Bytes, secretKey: Key, nonce: Nonce, additionalData: Bytes? = nil) -> Bytes? {
        guard authenticatedCipherText.count >= ABytes else { return nil }

        var message = Bytes(count: authenticatedCipherText.count - ABytes)
        var messageLen: UInt64 = 0

        guard .SUCCESS == crypto_aead_aes256gcm_decrypt (
            &message, &messageLen,
            nil,
            authenticatedCipherText, UInt64(authenticatedCipherText.count),
            additionalData, UInt64(additionalData?.count ?? 0),
            nonce, secretKey
        ).exitCode else { return nil }

        return message
    }
}

extension Aead.Aes256Gcm: NonceGenerator {
    public typealias Nonce = Bytes
    public var NonceBytes: Int { return Int(crypto_aead_aes256gcm_npubbytes()) }
}

extension Aead.Aes256Gcm: SecretKeyGenerator {
    public var KeyBytes: Int { return Int(crypto_aead_aes256gcm_keybytes()) }
    public typealias Key = Bytes

    public static var keygen: (UnsafeMutablePointer<UInt8>) -> Void = crypto_aead_aes256gcm_keygen
}

extension Aead {
    public class Salsa208Poly1305 {
        public let NonceBytes = 8
        public let KeyBytes = 32
        public typealias MAC = Bytes
        public var key = [UInt8](repeating: 0, count: 32)
    }
}

extension Aead.Salsa208Poly1305 {
    
    
    @discardableResult
    public func open(m: UnsafeMutablePointer<UInt8>, c: UnsafePointer<UInt8>, clen: UInt64, n: UnsafePointer<UInt8>, k: UnsafePointer<UInt8>) -> Int {
        if clen < 32 { return -1 }
        if crypto_onetimeauth_poly1305_verify(c + 16, c + 32, clen - 32, k) != 0 { return -1 }
        crypto_stream_salsa208_xor(m + 32, c + 32, clen - 32, n, k)
        return 0
    }
    
    
    @discardableResult
    public func encrypt(c: UnsafeMutablePointer<UInt8>, m: UnsafePointer<UInt8>, mlen: UInt64, n: UnsafePointer<UInt8>, k: UnsafePointer<UInt8>) -> Int {
        if mlen < 32 { return -1 }
        crypto_stream_salsa208_xor(c + 32, m + 32, mlen - 32, n, k)
        crypto_onetimeauth_poly1305(c + 16, c + 32, mlen - 32, k)
        return 0
    }

    

    @discardableResult
    public func encryptWithNonce(c: UnsafeMutablePointer<UInt8>, m: UnsafeMutablePointer<UInt8>, mlen: UInt64) -> Int {
        var nonce = [UInt8](repeating: 0, count: NonceBytes)
        randombytes_buf(&nonce, NonceBytes)
        let r = encrypt(c: c, m: m, mlen: mlen + 32, n: nonce, k: key)
        if r != 0 { return r }
        memcpy(c + 8, nonce, 8)
        return 0
    }

    @discardableResult
    public func decryptWithNonce(m: UnsafeMutablePointer<UInt8>, c: UnsafeMutablePointer<UInt8>, clen: UInt64) -> Int {
        var nonce = [UInt8](repeating: 0, count: NonceBytes)
        memcpy(&nonce, c + NonceBytes, NonceBytes)
        let r = open(m: m, c: c, clen: clen + 32, n: nonce, k: key)
        if r != 0 { return r }
        return 0
    }
}

// Key Initialization and Password Set
extension Aead.Salsa208Poly1305 {
    @discardableResult
    public func initializeCrypto() -> Int {
        if sodium_init() == -1 { return 1 }
        randombytes_set_implementation(&randombytes_salsa20_implementation)
        randombytes_stir()
        return 0
    }

    public func setPassword(_ password: String) {
        let password = password.data(using: .utf8).map { [UInt8]($0) } ?? []
        initializeCrypto()
        crypto_generichash(&key, key.count, password, UInt64(password.count), nil, 0)
    }
}


// ChaCha20

extension Aead {
    public struct ChaCha20 {

    }
}

extension Aead.ChaCha20 {
    @discardableResult
    public static func xor_ic(c: UnsafeMutablePointer<UInt8>, m: UnsafePointer<UInt8>, mlen: UInt64, n: UnsafePointer<UInt8>, k: UnsafePointer<UInt8>, ic: UInt64) -> Int {
        crypto_stream_chacha20_xor_ic(c, m, mlen, n, ic, k)
        return 0
    }

    
}
