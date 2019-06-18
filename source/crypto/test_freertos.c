#include "crypto.h"

typedef unsigned char aes_block[16];

int main(void)
{
  aes_block bufc  = { 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 };
  aes_block bufp  = { 0x80,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0 };
  aes_block bufp2 =
    { 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff };
  
  encrypt (bufp, bufc);    
  decrypt (bufc, bufp2);    

  return 0;
}
