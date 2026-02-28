int main1(int m,int p){
  int z, j, h, v;

  z=m;
  j=z;
  h=p;
  v=z;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == \at(m, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant h == \at(p, Pre) + v - z;
  loop invariant j <= z;
  loop invariant v * z >= 0;
  loop invariant v - h == \at(m, Pre) - \at(p, Pre);

  loop invariant h == p + v - z;
  loop invariant z == m;
  loop invariant m - j >= 0;
  loop invariant h - v == \at(p, Pre) - \at(m, Pre);
  loop assigns h, v, j;
*/
while (j>=1) {
      h = h+v;
      v = v+v;
      j = j-1;
  }

}
