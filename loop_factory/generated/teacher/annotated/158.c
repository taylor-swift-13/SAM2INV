int main1(int k){
  int t, m, z;

  t=78;
  m=0;
  z=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 78;
  loop invariant k == \at(k, Pre);
  loop invariant m % 5 == 0;

  loop invariant 10*z == m*m - 5*m + 60;
  loop invariant z >= 6;
  loop invariant z == 6 + m*(m-5)/10;
  loop invariant m <= t;
  loop invariant m >= 0;

  loop invariant z == 6 + (m*m - 5*m)/10;
  loop invariant z == 6 + (m*(m - 5))/10;
  loop invariant 10*(z - 6) == m*(m - 5);
  loop assigns z, m;
*/
while (m<=t-5) {
      z = z+m;
      m = m+5;
  }

}
