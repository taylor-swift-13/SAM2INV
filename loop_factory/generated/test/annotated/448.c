int main1(){
  int ghi7, qo, r, h;
  ghi7=1*2;
  qo=0;
  r=0;
  h=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= qo;
  loop invariant qo <= ghi7;
  loop invariant h == 0;
  loop invariant r == 0;
  loop invariant (qo == 0) || (qo == ghi7);
  loop assigns h, qo;
*/
while (qo<ghi7) {
      h += r;
      qo = ghi7;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h <= ghi7;
  loop invariant 0 <= h;
  loop invariant 0 <= qo;
  loop invariant (qo - h) == 2;
  loop assigns h, qo;
*/
while (1) {
      if (!(h<ghi7)) {
          break;
      }
      h += 1;
      qo += 1;
  }
}