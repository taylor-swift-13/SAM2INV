int main1(int b,int p){
  int u, s, d, a;

  u=(b%30)+16;
  s=0;
  d=s;
  a=s;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == s;
  loop invariant a == d*(d+1)/2;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant u == (\at(b, Pre) % 30) + 16;
  loop invariant s == d;
  loop invariant d >= 0;
  loop invariant u == (b%30) + 16;
  loop assigns d, a, s;
*/
while (1) {
      d = d+1;
      a = a+d;
      s = s+1;
  }

}
