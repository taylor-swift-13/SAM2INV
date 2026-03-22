int main1(int d){
  int ua, cj, lf, ogh, f6qk, k4;
  ua=d;
  cj=ua;
  lf=ua;
  ogh=cj;
  f6qk=-3;
  k4=(d%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d >= \at(d, Pre);
  loop invariant k4 <= (\at(d, Pre) % 35) + 8;
  loop invariant f6qk >= -3;
  loop invariant lf >= \at(d, Pre);
  loop invariant f6qk - ogh == -3 - \at(d,Pre);
  loop assigns f6qk, lf, ogh, k4, d;
*/
while (k4>0) {
      f6qk = f6qk+k4*k4;
      lf = (ogh*ogh)+(lf);
      ogh = ogh+k4*k4;
      k4--;
      d = d+(k4%6);
  }
}