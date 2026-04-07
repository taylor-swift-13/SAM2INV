int main1(){
  int i3, j9x, y, dv;
  i3=1+25;
  j9x=0;
  y=25;
  dv=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dv == j9x;
  loop invariant 0 <= j9x <= i3;
  loop invariant i3 == 1 + 25;
  loop invariant 0 <= y;
  loop invariant y <= i3;
  loop assigns dv, j9x, y;
*/
while (j9x<i3) {
      if (dv<i3) {
          y = j9x;
      }
      j9x++;
      dv += 1;
  }
}