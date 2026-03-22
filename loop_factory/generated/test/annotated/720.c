int main1(int m,int b){
  int p, dd, lmh;
  p=63;
  dd=(b%40)+2;
  lmh=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 63;
  loop invariant m + dd == \at(m,Pre) + ((\at(b,Pre) % 40) + 2);
  loop invariant m + dd == \at(m,Pre) + ((b % 40) + 2);
  loop assigns m, dd, lmh;
*/
while (dd!=lmh) {
      lmh = dd;
      dd = (dd+p/dd)/2;
      m = m+lmh-dd;
  }
}