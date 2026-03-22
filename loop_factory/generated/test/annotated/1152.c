int main1(int l,int t){
  int t1q, qlv, xrf0, ug01, n, pap4;
  t1q=1;
  qlv=t1q;
  xrf0=-6;
  ug01=2;
  n=(l%35)+8;
  pap4=l+1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qlv  >= t1q;
  loop invariant xrf0 >= -6;
  loop invariant ug01 >= 2;
  loop invariant qlv >= 1;
  loop invariant pap4 - l - qlv >= 0;
  loop invariant n <= ((l % 35) + 8);
  loop assigns qlv, ug01, xrf0, n, pap4;
*/
while (n>=1) {
      qlv = qlv+xrf0*xrf0;
      ug01 = ug01+n*n;
      xrf0 = xrf0+n*n;
      n = n - 1;
      pap4 = pap4 + qlv;
  }
}