int main1(){
  int kt85, kxsd, a65, pz, p36p, i2;
  kt85=1+22;
  kxsd=0;
  a65=1;
  pz=5;
  p36p=kxsd;
  i2=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pz == 5 + (a65 - 1) * (a65 - 1);
  loop invariant p36p == (kt85 + 4) * (a65 - 1);
  loop invariant 1 <= a65 <= kt85 + 1;
  loop invariant p36p == (a65 - 1) * (kt85 + 2*i2);
  loop assigns pz, a65, p36p;
*/
while (1) {
      if (!(a65<=kt85)) {
          break;
      }
      pz = pz+2*a65-1;
      a65 = a65 + 1;
      p36p += kt85;
      p36p = p36p+i2+i2;
  }
}