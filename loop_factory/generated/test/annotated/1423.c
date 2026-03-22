int main1(){
  int i3, zr7, fho, zz, rq8;
  i3=1;
  zr7=0;
  fho=i3;
  zz=-4;
  rq8=i3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rq8 == fho * zr7 + 1;
  loop invariant zz == zr7 - 4;
  loop invariant fho == i3;
  loop invariant rq8 == i3 + zr7 * fho;
  loop invariant 0 <= zr7;
  loop invariant zr7 <= i3;
  loop invariant rq8 == zr7 + 1;
  loop assigns zz, rq8, zr7;
*/
while (1) {
      if (!(zr7 < i3)) {
          break;
      }
      zz++;
      rq8 = rq8 + fho;
      zr7 = zr7 + 1;
  }
}