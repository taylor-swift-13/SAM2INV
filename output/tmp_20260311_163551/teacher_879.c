int main1(int b,int m){
  int z, t, v;

  z=(b%20)+10;
  t=1;
  v=z;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= z;
  loop invariant t > 0;

  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant z == (\at(b, Pre) % 20) + 10;
  loop invariant t >= 1 && (t == 1 || t % 3 == 0);
  loop invariant (t == 1) || v >= 0;
  loop invariant z == (b % 20) + 10;

  loop invariant t >= 1;
  loop invariant z == \at(b, Pre) % 20 + 10 && m == \at(m, Pre) && b == \at(b, Pre);
  loop invariant t >= 1 &&
                   (t == 1 || t % 3 == 0) &&
                   (t == 1 ==> v == z) &&
                   (t == 1 || v % 4 == 0) &&
                   (t > 1 ==> v >= 0);

  loop invariant z == ((\at(b,Pre) % 20) + 10) && v >= z;
  loop invariant t > 0 && -9 <= z && z <= 29;
  loop invariant z == \at(b, Pre) % 20 + 10;
  loop invariant b == \at(b, Pre) && m == \at(m, Pre);
  loop assigns v, t;
*/
while (t*3<=z) {
      v = v*2;
      v = v*v;
      t = t*3;
  }
/*@
  assert !(t*3<=z) &&
         (v >= z);
*/


}
