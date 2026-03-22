int main1(){
  int x, bg, d;
  x=(1%20)+5;
  bg=(1%20)+5;
  d=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bg == 30 - 4*x;
  loop invariant 0 <= x <= 6;
  loop invariant x - d == 0;
  loop assigns x, bg, d;
*/
while (1) {
      if (!(x>=1)) {
          break;
      }
      if (bg>0) {
          if (d>0) {
              x--;
              bg--;
              d -= 1;
          }
      }
      bg = bg + 5;
  }
}