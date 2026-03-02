int main1(int m,int p){
  int r, k, z, u;

  r=75;
  k=r;
  z=k;
  u=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == 75;
  loop invariant k == r;
  loop invariant k >= 0;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant z % 75 == 0;
  loop invariant m == \at(m, Pre) && p == \at(p, Pre) && r == 75 && k > 0;
  loop invariant z >= 0;
  loop invariant u >= 0;
  loop invariant k > 0;
  loop invariant z >= r;
  loop invariant u <= r;
  loop invariant z >= 75;
  loop invariant z % k == 0;
  loop invariant z >= k;
  loop invariant 0 <= u;
  loop invariant m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant r == k;
  loop invariant z >= u;
  loop invariant 0 <= u && u <= r;
  loop invariant u <= 75 && m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant r == k && r == 75;
  loop invariant m == \at(m, Pre) && p == \at(p, Pre) && k == r;
  loop invariant z % 75 == 0 && 0 <= u && u <= k;
  loop invariant k == r && r == 75 && m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant z >= 75 && u >= 0 && k >= 0 && k <= r;
  loop assigns z, u;
*/
while (k>0) {
      z = z*2;
      u = u/2;
      z = z*2;
  }

}
