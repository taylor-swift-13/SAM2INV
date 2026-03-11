int main1(){
  int py, hx, kgm;
  py=37;
  hx=0;
  kgm=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kgm == 5 * hx;
  loop invariant 0 <= hx;
  loop invariant hx <= py;
  loop assigns hx, kgm;
*/
while (1) {
      kgm = kgm + 5;
      hx += 1;
      if (hx>=py) {
          break;
      }
  }
}