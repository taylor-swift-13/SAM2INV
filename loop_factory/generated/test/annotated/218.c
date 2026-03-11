int main1(){
  int cd3, yld, g3j, h;
  cd3=63;
  yld=0;
  g3j=0;
  h=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g3j == h;
  loop invariant 0 <= h;
  loop invariant h <= cd3;
  loop assigns g3j, h;
*/
while (h<cd3) {
      g3j += 1;
      h += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yld < cd3;
  loop invariant 1 <= h;
  loop invariant h == cd3;
  loop invariant 0 <= yld <= cd3;
  loop assigns h, yld;
*/
while (1) {
      if (h+1<cd3) {
          h += 4;
      }
      yld += 1;
      if (yld>=cd3) {
          break;
      }
  }
}