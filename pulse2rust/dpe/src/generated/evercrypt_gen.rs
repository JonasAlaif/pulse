/* automatically generated by rust-bindgen 0.69.4 */

pub type Spec_Hash_Definitions_hash_alg = u8;
extern crate libloading;
pub struct evercrypt {
    __library: ::libloading::Library,
    pub EverCrypt_AutoConfig2_init: unsafe extern "C" fn(),
    pub EverCrypt_Ed25519_sign:
        unsafe extern "C" fn(signature: *mut u8, private_key: *mut u8, msg_len: u32, msg: *mut u8),
    pub EverCrypt_Ed25519_verify: unsafe extern "C" fn(
        public_key: *mut u8,
        msg_len: u32,
        msg: *mut u8,
        signature: *mut u8,
    ) -> bool,
    pub EverCrypt_HMAC_compute: unsafe extern "C" fn(
        a: Spec_Hash_Definitions_hash_alg,
        x0: *mut u8,
        x1: *mut u8,
        x2: u32,
        x3: *mut u8,
        x4: u32,
    ),
    pub EverCrypt_Hash_Incremental_hash_len:
        unsafe extern "C" fn(uu___: Spec_Hash_Definitions_hash_alg) -> u32,
    pub EverCrypt_Hash_Incremental_hash: unsafe extern "C" fn(
        a: Spec_Hash_Definitions_hash_alg,
        output: *mut u8,
        input: *mut u8,
        input_len: u32,
    ),
}
impl evercrypt {
    pub unsafe fn new<P>(path: P) -> Result<Self, ::libloading::Error>
    where
        P: AsRef<::std::ffi::OsStr>,
    {
        let library = ::libloading::Library::new(path)?;
        Self::from_library(library)
    }
    pub unsafe fn from_library<L>(library: L) -> Result<Self, ::libloading::Error>
    where
        L: Into<::libloading::Library>,
    {
        let __library = library.into();
        let EverCrypt_AutoConfig2_init = __library
            .get(b"EverCrypt_AutoConfig2_init\0")
            .map(|sym| *sym)?;
        let EverCrypt_Ed25519_sign = __library.get(b"EverCrypt_Ed25519_sign\0").map(|sym| *sym)?;
        let EverCrypt_Ed25519_verify = __library
            .get(b"EverCrypt_Ed25519_verify\0")
            .map(|sym| *sym)?;
        let EverCrypt_HMAC_compute = __library.get(b"EverCrypt_HMAC_compute\0").map(|sym| *sym)?;
        let EverCrypt_Hash_Incremental_hash_len = __library
            .get(b"EverCrypt_Hash_Incremental_hash_len\0")
            .map(|sym| *sym)?;
        let EverCrypt_Hash_Incremental_hash = __library
            .get(b"EverCrypt_Hash_Incremental_hash\0")
            .map(|sym| *sym)?;
        Ok(evercrypt {
            __library,
            EverCrypt_AutoConfig2_init,
            EverCrypt_Ed25519_sign,
            EverCrypt_Ed25519_verify,
            EverCrypt_HMAC_compute,
            EverCrypt_Hash_Incremental_hash_len,
            EverCrypt_Hash_Incremental_hash,
        })
    }
    pub unsafe fn EverCrypt_AutoConfig2_init(&self) {
        (self.EverCrypt_AutoConfig2_init)()
    }
    pub unsafe fn EverCrypt_Ed25519_sign(
        &self,
        signature: *mut u8,
        private_key: *mut u8,
        msg_len: u32,
        msg: *mut u8,
    ) {
        (self.EverCrypt_Ed25519_sign)(signature, private_key, msg_len, msg)
    }
    pub unsafe fn EverCrypt_Ed25519_verify(
        &self,
        public_key: *mut u8,
        msg_len: u32,
        msg: *mut u8,
        signature: *mut u8,
    ) -> bool {
        (self.EverCrypt_Ed25519_verify)(public_key, msg_len, msg, signature)
    }
    pub unsafe fn EverCrypt_HMAC_compute(
        &self,
        a: Spec_Hash_Definitions_hash_alg,
        x0: *mut u8,
        x1: *mut u8,
        x2: u32,
        x3: *mut u8,
        x4: u32,
    ) {
        (self.EverCrypt_HMAC_compute)(a, x0, x1, x2, x3, x4)
    }
    pub unsafe fn EverCrypt_Hash_Incremental_hash_len(
        &self,
        uu___: Spec_Hash_Definitions_hash_alg,
    ) -> u32 {
        (self.EverCrypt_Hash_Incremental_hash_len)(uu___)
    }
    pub unsafe fn EverCrypt_Hash_Incremental_hash(
        &self,
        a: Spec_Hash_Definitions_hash_alg,
        output: *mut u8,
        input: *mut u8,
        input_len: u32,
    ) {
        (self.EverCrypt_Hash_Incremental_hash)(a, output, input, input_len)
    }
}