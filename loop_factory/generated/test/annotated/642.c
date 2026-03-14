int main1(int n,int i){
  int cs, h, d1pz, s;
  cs=i;
  h=0;
  d1pz=-2;
  s=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d1pz == h - 2;
  loop invariant cs == i;
  loop invariant 0 <= h;
  loop invariant s == n + (h*h - 3*h)/2;
  loop assigns d1pz, s, h;
*/
while (h+1<=cs) {
      d1pz += 1;
      s = s + d1pz;
      h += 1;
  }
}