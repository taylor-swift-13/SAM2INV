int main1(){
  int tk8, l9w, xo6, r, qk, i;
  tk8=1;
  l9w=tk8;
  xo6=0;
  r=0;
  qk=5;
  i=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qk + xo6 == 5;
  loop invariant r == 5*xo6 - (xo6*(xo6 - 1))/2;
  loop invariant 0 <= xo6 <= tk8;
  loop invariant i - 7 == l9w * (5 - qk);
  loop invariant 0 <= qk <= 5;
  loop invariant 0 <= xo6 <= 1;
  loop invariant l9w == 1;
  loop assigns r, xo6, qk, i;
*/
while (xo6<tk8&&qk>0) {
      r += qk;
      xo6 = xo6 + 1;
      qk -= 1;
      i += l9w;
  }
}