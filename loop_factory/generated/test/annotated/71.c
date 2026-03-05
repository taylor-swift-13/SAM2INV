int main1(int h){
  int r, n;
  r=61;
  n=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n >= 0;
  loop invariant h >= \at(h, Pre);
  loop invariant h - 2*n <= \at(h, Pre);
  loop invariant r == 61;
  loop invariant n <= 2 * r + 1;
  loop assigns h, n;
*/
while (n<=r) {
      n = 2*n;
      n += 1;
      h += n;
  }
}