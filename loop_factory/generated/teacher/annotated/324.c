int main1(int m,int p){
  int l, z, t;

  l=(p%15)+7;
  z=0;
  t=z;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 0;
  loop invariant t % 2 == 0;
  loop invariant t >= 0;
  loop invariant l == \at(p, Pre) % 15 + 7;
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant l == (\at(p, Pre) % 15) + 7;
  loop invariant (2 + z != 0) ==> t % (2 + z) == 0;

  loop assigns t;
*/
while (z+5<=l) {
      t = t+2;
      t = t+z;
  }

}
