int main1(int b,int m){
  int h, i, v, d;

  h=53;
  i=0;
  v=i;
  d=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == -12 * i;
  loop invariant i <= h;
  loop invariant i >= 0;
  loop invariant h == 53;
  loop invariant v == i * (d + d);
  loop invariant 0 <= i;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v <= 0;
  loop assigns i, v;
*/
while (i<h) {
      v = v+d+d;
      i = i+1;
  }

}
