int main1(int f,int e){
  int y, n, no9;
  y=f;
  n=y;
  no9=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant no9 == 1 + (f + e) * (f - n);
  loop invariant no9 == 1 + (f + e) * (\at(f, Pre) - n);
  loop invariant n <= \at(f, Pre);
  loop invariant n <= f;
  loop assigns no9, n;
*/
while (1) {
      if (!(n-1>=0)) {
          break;
      }
      no9 = no9+f+e;
      n = n - 1;
  }
}