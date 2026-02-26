int main1(int k,int m){
  int l, z, t;

  l=60;
  z=1;
  t=z;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 1;
  loop invariant z == 1;
  loop invariant l == 60;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant z < l;
  loop invariant 0 <= t <= 2;
  loop invariant t == t % 3;
  loop assigns t;
*/
while (z+1<=l) {
      t = t+3;
      t = t%3;
  }

}
