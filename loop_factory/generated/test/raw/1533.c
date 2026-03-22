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
