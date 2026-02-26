int main1(int m,int p){
  int z, j, h, v;

  z=m;
  j=0;
  h=z;
  v=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 0;
  loop invariant \at(m, Pre) <= h;
  loop invariant h <= z;
  loop invariant z == \at(m, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop assigns h, v;
*/
while (h<z) {
      if (h<z) {
          h = h+1;
      }
      v = v+v;
  }

}
