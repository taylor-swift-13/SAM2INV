int main1(){
  int ltod, ifwn, fl, r0p, nf2q, zwad, kpa, qf;
  ltod=1;
  ifwn=ltod+3;
  fl=1;
  r0p=1;
  nf2q=1;
  zwad=1;
  kpa=2;
  qf=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (zwad == 1 || zwad == -1);
  loop invariant 0 <= fl <= 1;
  loop invariant r0p >= 1;
  loop invariant qf == 1;
  loop invariant kpa >= 2;
  loop invariant ifwn == 4;
  loop invariant ltod == 1;
  loop invariant (nf2q == 1 && fl == 1) || (nf2q >= 2 && fl == 0);
  loop invariant 1 <= nf2q <= ltod + 1;
  loop invariant ((nf2q == 1) ==> (fl == 1)) && ((fl == 1) ==> (nf2q == 1));
  loop invariant (((nf2q - 1) / 2) % 2 == 0) ==> (zwad == 1);
  loop assigns fl, zwad, nf2q, r0p, qf, kpa;
*/
while (1) {
      if (!(nf2q<=ltod)) {
          break;
      }
      fl = fl*(1/nf2q);
      if ((nf2q/2)%2==0) {
          zwad = 1;
      }
      else {
          zwad = -1;
      }
      nf2q = nf2q + 1;
      r0p = r0p+zwad*fl;
      fl = fl*(1/nf2q);
      if (qf+6<ltod) {
          qf = kpa*kpa;
      }
      kpa += zwad;
      kpa += ifwn;
  }
}