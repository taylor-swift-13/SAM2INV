int main1(){
  int eqy, upqf, cl, m, vsw, h;
  eqy=1+21;
  upqf=eqy;
  cl=0;
  m=(1%28)+10;
  vsw=eqy;
  h=eqy;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eqy == 22;
  loop invariant 0 <= m <= 11;
  loop invariant 0 <= cl <= 11;
  loop invariant vsw >= 22;
  loop invariant m == 11 - cl*(cl - 1)/2;
  loop assigns m, cl, vsw;
*/
while (m>cl) {
      m = m - cl;
      cl = cl + 1;
      vsw = vsw+(m%4);
      vsw = (vsw)+(vsw*vsw);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant eqy == 22;
  loop invariant 0 <= m <= 11;
  loop invariant vsw >= 22;
  loop invariant upqf >= 22;
  loop invariant h >= 0;
  loop invariant h <= eqy;
  loop assigns h, m, upqf, vsw;
*/
while (h>vsw) {
      h -= vsw;
      vsw++;
      m = m+(vsw%9);
      upqf += 2;
  }
}