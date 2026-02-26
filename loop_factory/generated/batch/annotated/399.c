int main1(int b,int n){
  int k, v, z, s;

  k=21;
  v=0;
  z=k;
  s=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 21;
  loop invariant z >= 0;
  loop invariant s >= 0;
  loop invariant z <= k;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant z <= 21 && ((z == 21) ==> (s == 21 || s == 0));
  loop invariant z % 21 == 0;
  loop invariant s % 21 == 0;
  loop assigns z, s;
*/
while (z!=0&&s!=0) {
      if (z>s) {
          z = z-s;
      }
      else {
          s = s-z;
      }
      s = s+s;
  }

}
