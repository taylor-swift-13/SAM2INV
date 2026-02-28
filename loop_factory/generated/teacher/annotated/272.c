int main1(int b,int n){
  int r, f, v, e;

  r=68;
  f=0;
  v=3;
  e=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == 68;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 0 <= f;
  loop invariant f <= r;
  loop invariant f == 0 ==> (v == 3 && e == \at(b, Pre));
  loop invariant r >= 2;
  loop invariant f + 2 <= r + r;
  loop assigns e, v, f;
*/
while (f<=r-1) {
      v = v+1;
      e = e+v;
      if (f+2<=r+r) {
          v = e-v;
      }
      f = f+1;
  }

}
