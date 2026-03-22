int main1(int o,int m){
  int o2, n0, b, a, c7, dm9e, i, gm;
  o2=65;
  n0=o2;
  b=m;
  a=-8;
  c7=m;
  dm9e=o;
  i=-8;
  gm=n0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == \at(o, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n0 >= 65;
  loop invariant o2 == 65;
  loop invariant gm == 2*n0 - 65;
  loop invariant c7 == \at(m,Pre) || (\at(m,Pre) == o2 && c7 == o2+1);
  loop invariant a >= 2*n0 - 138;
  loop invariant b >= \at(m,Pre) + 2*(n0 - 65);
  loop invariant ((m != o2) ==> (c7 == m)) && ((m == o2) ==> (c7 == o2 || c7 == o2 + 1));
  loop assigns b, a, c7, dm9e, gm, i, m, n0, o;
*/
while (n0-1>=0) {
      if (c7==o2+1) {
          b = b + 3;
          a = a + 3;
      }
      else {
          b += 2;
          a += 2;
      }
      if (c7==o2) {
          b += 1;
          c7++;
      }
      i = i + a;
      o = o+c7-c7;
      gm += 2;
      dm9e = dm9e+c7-a;
      m = m+c7-c7;
      n0 += 1;
  }
}