int main1(){
  int oa2i, f6i, odv, d5n;
  oa2i=1*3;
  f6i=-5;
  odv=1+4;
  d5n=f6i;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (oa2i - f6i) >= 0;
  loop invariant odv >= 5;
  loop invariant d5n >= -5;
  loop invariant oa2i <= 3;
  loop invariant (oa2i == 3) || (oa2i == f6i);
  loop invariant f6i == -5;
  loop assigns odv, d5n, oa2i;
*/
while (f6i+1<=oa2i) {
      if (!(!(f6i<oa2i/2))) {
          odv += 1;
      }
      else {
          odv = odv + d5n;
      }
      d5n = d5n + oa2i;
      oa2i = (f6i+1)-1;
  }
}