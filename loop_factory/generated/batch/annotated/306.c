int main1(int b,int m){
  int z, t, v;

  z=(b%20)+10;
  t=z+6;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant (t - z) >= 0;
  loop invariant ((t - z) % 3) == 0;
  loop invariant 0 <= v;
  loop invariant v <= 8;


  loop invariant z == (b % 20) + 10;
  loop invariant t >= z;
  loop invariant (t - z) % 3 == 0;
  loop invariant z == (\at(b, Pre) % 20) + 10;
  loop invariant v >= 0;
  loop invariant t - z >= 0;
  loop assigns v, t;
*/
while (t-z>0) {
      v = v*v;
      v = v%5;
      if ((t%4)==0) {
          v = v*2;
      }
      t = t-3;
  }

}
