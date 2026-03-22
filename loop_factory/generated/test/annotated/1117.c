int main1(int q){
  int y, b5, gdz, t, rc, eu;
  y=q;
  b5=1;
  gdz=0;
  t=0;
  rc=b5;
  eu=q+1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gdz == t * q;
  loop invariant rc == t + 1;
  loop invariant t >= 0;
  loop invariant y == q;
  loop invariant y == \at(q, Pre);
  loop invariant b5 == 1;
  loop assigns gdz, rc, t;
*/
while (1) {
      if (!(t<=y-1)) {
          break;
      }
      gdz = gdz + q;
      rc = rc + b5;
      t += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y >= \at(q, Pre);
  loop invariant rc > 0;
  loop invariant (gdz == 0) || (gdz == q * t);
  loop invariant y >= q;
  loop invariant eu >= q + 1;
  loop invariant t >= 0;
  loop assigns y, eu, gdz;
*/
while (rc-gdz>0) {
      y = y+t*rc;
      eu = eu + rc;
      gdz = 0;
  }
}