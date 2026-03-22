int main1(){
  int m5b, m0, m, gu, j9d5, ebym, zp, cv1v;
  m5b=1;
  m0=m5b;
  m=19;
  gu=14;
  j9d5=0;
  ebym=-4;
  zp=m5b;
  cv1v=m0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (m + gu == 33);
  loop invariant (m0 <= m5b);
  loop invariant (m0 >= 1);
  loop invariant (m5b == 1);
  loop invariant (ebym == -4 + 2*(m0 - 1));
  loop invariant j9d5 == ((m0 - 1) % 2);
  loop invariant zp == 1;
  loop invariant m == 19 + ((m0 - 1) % 2);
  loop invariant cv1v == 19*m0 - (17 + (m0 % 2));
  loop invariant ebym - 2*m0 == -6;
  loop assigns m, gu, j9d5, m0, zp, cv1v, ebym;
*/
while (m0<m5b) {
      if (j9d5==0) {
          m++;
          gu -= 1;
          j9d5 = 1;
      }
      else {
          m -= 1;
          gu++;
          j9d5 = 0;
      }
      m0++;
      if (zp+6<m5b) {
          zp = cv1v-zp;
      }
      cv1v = cv1v + m;
      ebym = ebym + 1;
      ebym = ebym + 1;
  }
}