int main1(int k,int f){
  int de, vo, pi0, o, bh6;
  de=k+23;
  vo=-6;
  pi0=0;
  o=-6;
  bh6=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (pi0 % 3 == 0);
  loop invariant ((pi0 < 3) ==> (o == -6));
  loop invariant bh6 == 1 + (pi0/3) * vo;
  loop invariant pi0 >= 0;
  loop invariant de == \at(k, Pre) + 23;
  loop invariant (pi0 != 0) ==> (o == de - pi0 + 3);
  loop invariant bh6 == 1 - 2*pi0;
  loop invariant de == k + 23;
  loop assigns bh6, o, pi0;
*/
while (pi0<=de-1) {
      o = de-pi0;
      pi0 = pi0 + 3;
      bh6 = bh6 + vo;
  }
}