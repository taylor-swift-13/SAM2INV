int main1(int p,int a){
  int jy5, wj, m, sa;
  jy5=76;
  wj=0;
  m=0;
  sa=wj;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre) + jy5 * m;
  loop invariant sa + m <= jy5 + 1;
  loop invariant m >= 0;
  loop invariant jy5 == 76;
  loop invariant wj == 0;
  loop invariant a == \at(a, Pre);
  loop invariant (m > 0) ==> (sa == jy5 + 1 - m);
  loop assigns m, p, sa;
*/
while (wj+1<=jy5) {
      sa = jy5-m;
      m++;
      p += jy5;
  }
}