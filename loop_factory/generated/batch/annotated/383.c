int main1(int m,int n){
  int z, u, w, r;

  z=8;
  u=z+6;
  w=u;
  r=z;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 8;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant w % 2 == 0;
  loop invariant u % 2 == 0;
  loop invariant r % 2 == 0;

  loop invariant u <= z + 6;
  loop invariant w > 0;
  loop invariant (w % 2 == 0);
  loop invariant (w >= z + 6);
  loop invariant (u <= z + 6);
  loop invariant (u >= z);
  loop invariant (u % 2 == z % 2);
  loop invariant (r % 2 == z % 2);
  loop invariant u <= 14;
  loop assigns w, r, u;
*/
while (u>=z+1) {
      w = w*2;
      r = r+w;
      r = r%2;
      u = u-2;
  }

}
