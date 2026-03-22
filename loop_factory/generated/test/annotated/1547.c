int main1(int m,int l){
  int k31, eya, agu, bck, ehwb, h, fnk3, bn;
  k31=(l%31)+4;
  eya=0;
  agu=-2;
  bck=eya;
  ehwb=5;
  h=0;
  fnk3=16;
  bn=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bn == 0;
  loop invariant h == 0;
  loop invariant k31 == (((\at(l, Pre)) % 31) + 4);
  loop invariant bck >= 0;
  loop invariant agu >= -2;
  loop invariant l == \at(l, Pre) + 2*eya;
  loop invariant fnk3 == 16 + ((eya + 1) / 2);
  loop invariant (agu >= -2 + 4*eya);
  loop invariant fnk3 >= 16;
  loop invariant fnk3 <= 16 + eya;
  loop invariant agu <= (-2 + 9*eya);
  loop invariant ehwb >= (5 + 3*eya);
  loop invariant eya >= 0;
  loop invariant m == \at(m,Pre);
  loop assigns eya, bn, agu, h, ehwb, l, fnk3, bck;
*/
while (eya < k31) {
      eya++;
      if (!(bn!=0)) {
          bn = 0;
      }
      else {
          bn = 1;
      }
      if (fnk3<k31+2) {
          agu = agu + 5;
      }
      h += bn;
      ehwb = ehwb + 3;
      l += 2;
      fnk3 = fnk3+(eya%2);
      bck += bn;
      agu += 4;
      bck = bck + agu;
      ehwb += bck;
  }
}