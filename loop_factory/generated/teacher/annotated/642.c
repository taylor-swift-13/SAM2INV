int main1(int b,int k){
  int m, j, v, z, n, y;

  m=9;
  j=0;
  v=0;
  z=1;
  n=6;
  y=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant j == 0;
  loop invariant n == 6 + 2*y;
  loop invariant z == y*y + 5*y + 1;
  loop invariant 3*v == y*y*y + 6*y*y - 4*y;
  loop invariant y <= m + 1;
  loop invariant v == ((y - 1) * y * (2 * y - 1)) / 6 + (5 * y * (y - 1)) / 2 + y + y * j;
  loop invariant 0 <= y;
  loop invariant z == 1 + y*y + 5*y;
  loop invariant 3*v == y*(y*y + 6*y - 4 + 3*j);
  loop invariant v == (y*y*y + 6*y*y - 4*y) / 3;
  loop invariant m == 9;
  loop invariant n - 2*y == 6;
  loop invariant z >= 1;
  loop assigns y, v, z, n;
*/
while (y<=m) {
      y = y+1;
      v = v+z;
      z = z+n;
      n = n+2;
      v = v+j;
  }

}
