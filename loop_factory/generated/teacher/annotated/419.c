int main1(int b,int p){
  int c, k, v, y;

  c=(p%24)+17;
  k=0;
  v=k;
  y=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v % 4 == 0;
  loop invariant (y - p) % 4 == 0;

  loop invariant v >= 0;
  loop invariant y >= p;
  loop invariant p == \at(p, Pre);
  loop invariant c == (\at(p, Pre) % 24) + 17;
  loop invariant k == 0;
  loop invariant y >= \at(p, Pre);
  loop invariant c == (p % 24) + 17;
  loop invariant b == \at(b, Pre);
  loop invariant y - p >= v;
  loop invariant v % 2 == 0;
  loop assigns v, y;
*/
while (k+1<=c) {
      v = v+2;
      v = v*2;
      y = y+v;
  }

}
