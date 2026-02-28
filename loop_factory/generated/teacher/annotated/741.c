int main1(int a,int b,int k,int m){
  int u, w, z, i, v, r;

  u=a;
  w=3;
  z=0;
  i=m;
  v=-8;
  r=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == -8;
  loop invariant u == a;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant i <= m;
  loop invariant z >= 0;
  loop invariant z >= 0 && ((i == m) || (i == v));
  loop invariant i == m || i == -8;
  loop invariant i <= \at(m, Pre);
  loop invariant (i == \at(m, Pre)) || (i == v);
  loop invariant (i == m) || (i == v);
  loop assigns i, z;
*/
while (1) {
      if (v<=i) {
          i = v;
      }
      z = z+1;
  }

}
