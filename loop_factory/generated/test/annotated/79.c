int main1(int c){
  int zp, r, of, tt, a8;
  zp=28;
  r=zp;
  of=1;
  tt=3;
  a8=r;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a8 == r * of;
  loop invariant tt == 3 + ((of - 1) * of * (2 * of - 1)) / 6;
  loop invariant r == zp;
  loop invariant 1 <= of <= zp + 1;
  loop assigns a8, tt, of, c;
*/
while (1) {
      if (!(of<=zp)) {
          break;
      }
      tt = tt+of*of;
      a8 += r;
      of = of + 1;
      c = c + c;
  }
}