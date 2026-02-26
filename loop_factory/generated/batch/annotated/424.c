int main1(int k,int p){
  int c, g, v, d;

  c=(k%6)+19;
  g=0;
  v=c;
  d=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant c == (\at(k, Pre) % 6) + 19;

  loop invariant c == (k % 6) + 19;
  loop invariant d == k;
  loop invariant g % 3 == 0;
  loop invariant v == c + (g / 3) * d;
  loop invariant 0 <= g;
  loop invariant 3*(v - c) == d*g;

  loop invariant d == \at(k, Pre);
  loop invariant g <= c + 2;
  loop assigns g, v;
*/
while (g<c) {
      v = v+d;
      g = g+3;
  }

}
