int main1(int j,int l){
  int okl2, eg, dx;
  okl2=13;
  eg=okl2;
  dx=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= \at(j, Pre);
  loop invariant l >= \at(l, Pre);
  loop invariant l - j >= \at(l, Pre) - \at(j, Pre);
  loop invariant (l - \at(l, Pre)) >= (j - \at(j, Pre));
  loop invariant (l - \at(l, Pre)) <= 2*(j - \at(j, Pre));
  loop invariant dx == 1 || dx == 2;
  loop invariant okl2 == 13;
  loop invariant eg == 13;
  loop assigns dx, l, j;
*/
while (eg>2) {
      if (dx==1) {
          dx = 2;
      }
      else {
          if (dx==2) {
              dx = 1;
          }
      }
      l += dx;
      j++;
  }
}