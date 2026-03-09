int main1(){
  int qv, s, xr, o4;
  qv=1+13;
  s=3;
  xr=0;
  o4=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xr == (s - 3) * (s + 1);
  loop invariant o4 == 8 + (s - 3) * (s - 2) * (2*s + 7) / 6;
  loop invariant 3 <= s <= (qv + 1);
  loop assigns xr, o4, s;
*/
while (s<=qv) {
      xr = (xr+2*s)+(-(1));
      o4 += xr;
      s++;
  }
}