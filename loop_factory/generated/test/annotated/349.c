int main1(int d){
  int r13k, km, tn1l, xfcm, f, s7s;
  r13k=d-2;
  km=0;
  tn1l=8;
  xfcm=0;
  f=r13k;
  s7s=km;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r13k == d - 2;
  loop invariant tn1l >= 0;
  loop invariant s7s == xfcm;
  loop invariant (xfcm == 0) || (xfcm == tn1l);
  loop invariant (km == 0) || (km == r13k);
  loop invariant (km == 0) ==> (xfcm == 0 && s7s == 0);
  loop assigns xfcm, s7s, km;
*/
while (km<r13k) {
      xfcm = xfcm + tn1l;
      s7s += xfcm;
      km = r13k;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r13k == d - 2;
  loop invariant s7s >= 0;
  loop invariant xfcm >= 0;
  loop invariant (f == r13k) || (f == s7s);
  loop invariant tn1l >= 8;
  loop assigns tn1l, xfcm, f;
*/
while (f<=s7s-1) {
      tn1l += xfcm;
      xfcm = xfcm + tn1l;
      f = s7s;
  }
}