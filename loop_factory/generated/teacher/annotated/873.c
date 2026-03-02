int main1(int m,int q){
  int z, j, f, v;

  z=(q%27)+8;
  j=0;
  f=m;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= j;
  loop invariant z < 0 || j <= z;
  loop invariant z == \at(q, Pre) % 27 + 8;
  loop invariant z == (q % 27) + 8;

  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant ((j == 0) ==> (f == m));

  loop invariant m == \at(m,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant z == (\at(q,Pre) % 27) + 8;
  loop invariant j >= 0;

  loop invariant m == \at(m, Pre) && q == \at(q, Pre);
  loop invariant z == (\at(q, Pre) % 27) + 8;
  loop invariant q == \at(q, Pre) && z == (\at(q, Pre) % 27) + 8;
  loop assigns f, j;
*/
while (j<z) {
      f = f*2;
      j = j+1;
  }

}
