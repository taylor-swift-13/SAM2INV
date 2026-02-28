int main1(int a,int n){
  int w, f, r;

  w=n+11;
  f=0;
  r=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == n + 11;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant f >= 0;

  loop invariant r <= 0;
  loop invariant w == \at(n, Pre) + 11;
  loop invariant 0 <= f;
  loop invariant r == 0 || r == -6;
  loop invariant r % 6 == 0;
  loop invariant (w < 0) || (f <= w);
  loop assigns f, r;
*/
while (f<=w-1) {
      if (r+5<w) {
          r = r-r;
      }
      else {
          r = r+r;
      }
      f = f+1;
  }

}
