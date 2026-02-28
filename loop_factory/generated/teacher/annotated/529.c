int main1(int n,int p){
  int w, y, v, r;

  w=n-10;
  y=0;
  v=4;
  r=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == n - 10;
  loop invariant (n == \at(n, Pre));
  loop invariant (p == \at(p, Pre));
  loop invariant (w >= 4) ==> (v <= w);
  loop invariant (w >= 4) ==> (v >= 4);

  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant w == \at(n, Pre) - 10;
  loop invariant (v <= w) || (v <= 4);
  loop invariant (v < w) ==> (v % 2 == 0);
  loop assigns v;
*/
while (1) {
      if (v+2<=w) {
          v = v+2;
      }
      else {
          v = w;
      }
  }

}
