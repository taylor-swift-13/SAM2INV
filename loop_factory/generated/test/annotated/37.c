int main1(int g){
  int b, yr1, ir, kj4l, i2m;
  b=g+12;
  yr1=b;
  ir=b;
  kj4l=0;
  i2m=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == \at(g, Pre);
  loop invariant b == (\at(g, Pre) + 12);
  loop invariant i2m == 4;
  loop invariant (yr1 == 0) || (yr1 == b && kj4l == 0 && ir == b);
  loop invariant yr1 <= b;
  loop assigns g, kj4l, ir, yr1;
*/
while (yr1>0) {
      g = g+b-yr1;
      kj4l = kj4l+ir*yr1;
      ir = ir+i2m+g;
      ir = ir + 1;
      yr1 = 0;
  }
}