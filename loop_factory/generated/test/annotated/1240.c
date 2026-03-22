int main1(int g){
  int fa, q, kgx6, eu6, z, bw;
  fa=g+9;
  q=g;
  kgx6=16;
  eu6=g;
  z=(g%6)+2;
  bw=fa;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= eu6 - g;
  loop invariant eu6 - g <= 9;
  loop invariant fa == g + 9;
  loop invariant fa == \at(g, Pre) + 9;
  loop invariant 0 <= eu6 - \at(g,Pre);
  loop invariant eu6 - \at(g,Pre) <= 9;
  loop assigns bw, eu6, kgx6, q, z;
*/
while (eu6<fa) {
      eu6 += 1;
      kgx6 = kgx6*z;
      q = q*z+1;
      bw = bw+(q%8);
      z += 2;
      z = z*z+z;
  }
}