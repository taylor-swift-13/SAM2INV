int main1(){
  int gq0r, ru, z58, e, zgl, ckn;
  gq0r=1+14;
  ru=0;
  z58=0;
  e=0;
  zgl=gq0r;
  ckn=ru;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z58 == e;
  loop invariant ckn == e*(e+1)/2;
  loop invariant e >= 0;
  loop invariant e <= gq0r;
  loop assigns e, z58, zgl, ckn;
*/
while (e<gq0r) {
      e += 1;
      z58 = z58 + 1;
      zgl = zgl*2;
      ckn = ckn + z58;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gq0r >= e;
  loop invariant z58 >= e;
  loop invariant e >= 4;
  loop invariant gq0r >= 15;
  loop invariant z58 >= 15;
  loop invariant ckn >= 0;
  loop assigns z58, gq0r, e;
*/
while (1) {
      if (!(e>4)) {
          break;
      }
      z58 = z58+gq0r*e;
      gq0r = gq0r + e;
      gq0r += ckn;
      e = 4;
  }
}