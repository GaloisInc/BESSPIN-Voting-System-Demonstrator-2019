/**
 * SBB Crypto subysystem
 * @refine crypto.lando
 */

// General includes
#include <assert.h>

// Subsystem includes
#include "crypto.h"

void aes_encrypt(plaintext_block the_plaintext, ciphertext_block the_ciphertext, AES_Key_Name key)
{
    assert(false);
    //@ assert false;
    return;
}

void aes_decrypt(ciphertext_block the_ciphertext, plaintext_block the_plaintext, AES_Key_Name key)
{
    assert(false);
    //@ assert false;
    return;
}

void hash(message the_message, size_t the_message_size, digest the_digest)
{
    assert(false);
    //@ assert false;
    return;
}

void aes_cbc_mac(message the_message, size_t the_message_size,
                 block the_digest, AES_Key_Name key)
{
    assert(false);
    //@ assert false;
    return;
}
