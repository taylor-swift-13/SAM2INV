int main1(int k,int p){
  int h, z, m, u;

  h=40;
  z=h;
  m=k;
  u=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 40;
  loop invariant ((\at(k,Pre) <= 41) ==> (m <= 41)) && ((\at(k,Pre) <= 41) ==> (m >= \at(k,Pre)));
  loop invariant h == 40;
  loop invariant z == h;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre) && ((m >= k) || (m >= h + 1));
  loop invariant p == \at(p, Pre);
  loop invariant z >= 0;
  loop invariant z <= 40;
  loop invariant z >= 1;
  loop invariant (k >= 41) ==> (m <= k);

  loop assigns m;
*/
while (z-1>=0) {
      if (m+5<=h) {
          m = m+5;
      }
      else {
          m = h;
      }
      m = m+1;
  }

}
