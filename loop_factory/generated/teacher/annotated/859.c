int main1(int m,int n){
  int v, w, z, p;

  v=m+17;
  w=0;
  z=0;
  p=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v == m + 17;

  loop invariant (z <= v/2) ==> (p == m);

  loop invariant z >= 0 && m == \at(m, Pre) && p >= m && ((p - m) % 2 == 0) && (p - m) <= 2 * z;
  loop invariant p >= m;
  loop invariant (p - m) % 2 == 0;
  loop invariant z >= 0;
  loop invariant (z < v/2) ==> (p == m);


  loop invariant (z < v/2) ==> (p == m) && (z >= v/2) ==> (p == m + 2*(z - v/2));
  loop invariant (z <= v/2) ==> p == m;

  loop assigns p, z;
*/
while (z<v) {
      if (z>=v/2) {
          p = p+2;
      }
      z = z+1;
  }

}
