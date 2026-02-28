int main1(int b,int p){
  int n, z, v, y;

  n=30;
  z=0;
  v=p;
  y=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant z == 0;
  loop invariant n == 30;
  loop invariant y == -3;
  loop invariant v <= p;
  loop invariant ((v - p) % 2 == 0);
  loop invariant ((z < n/2) ==> (v <= p));
  loop invariant ((z >= n/2) ==> (v >= p));

  loop invariant v <= \at(p, Pre);
  loop assigns v;
*/
while (z<=n-2) {
      if (z<n/2) {
          v = v+y;
      }
      else {
          v = v+1;
      }
      v = v+1;
  }

}
