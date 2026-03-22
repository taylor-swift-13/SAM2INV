int main1(){
  int z, kl, jzg, k, gysh, ajy, b5, kwd;
  z=(1%13)+16;
  kl=0;
  jzg=-4;
  k=z;
  gysh=z;
  ajy=-3;
  b5=kl;
  kwd=kl;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jzg == -4 + ((kl + 1) / 2);
  loop invariant gysh == z + ((kl + 1) / 2);
  loop invariant k == z + (kl / 2);
  loop invariant ajy == -3 + (kl / 2);
  loop invariant 0 <= b5;
  loop invariant z == 17;
  loop invariant 0 <= kl <= z;
  loop invariant kwd >= 0;
  loop assigns jzg, gysh, k, ajy, kl, b5, kwd;
*/
while (kl < z) {
      if (!(!(((kl % 2) == 0)))) {
          jzg++;
          gysh += 1;
      }
      else {
          k += 1;
          ajy = ajy + 1;
      }
      kl += 1;
      if (jzg<k+3) {
          b5 += kwd;
      }
      kwd = kwd + gysh;
      kwd += kwd;
      if (k<ajy+5) {
          b5 = b5 + kl;
      }
      else {
          kwd = kwd + b5;
      }
      kwd = kwd + b5;
  }
}