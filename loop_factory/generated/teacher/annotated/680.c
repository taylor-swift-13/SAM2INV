int main1(int k,int m,int p,int q){
  int i, b, v, h, z, x, y;

  i=q+8;
  b=0;
  v=q;
  h=i;
  z=q;
  x=3;
  y=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == \at(q,Pre) &&
                   i == \at(q,Pre) + 8 &&
                   v >= \at(q,Pre) &&
                   k == \at(k,Pre);
  loop invariant m == \at(m,Pre) &&
                   p == \at(p,Pre) &&
                   q == \at(q,Pre) &&
                   z < i;
  loop invariant q == \at(q, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant i == \at(q, Pre) + 8;
  loop invariant (h == i || h == v - 1);
  loop invariant z == \at(q,Pre);
  loop invariant i == z + 8;
  loop invariant v >= z;
  loop invariant h >= z;
  loop invariant (z < i);
  loop invariant (v >= \at(q, Pre));
  loop invariant i - z == 8;

  loop assigns h, v;
*/
while (1) {
      if (z<i) {
          h = v;
      }
      v = v+1;
  }

}
