int main1(int k,int p){
  int b, u, v, g;

  b=54;
  u=1;
  v=b;
  g=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v + 2*g == 54 + 2*\at(k, Pre);
  loop invariant g + u == \at(k, Pre) + 1;
  loop invariant u >= 1;
  loop invariant v >= 54;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant b == 54;
  loop invariant v == 2*u + 52;
  loop invariant g == k - u + 1;
  loop invariant v - 2*u == 52;
  loop invariant g + v - u == k + 53;
  loop invariant g <= k;
  loop invariant g + u == k + 1;
  loop assigns v, g, u;
*/
while (1) {
      v = v+1;
      g = g-1;
      v = v+1;
      u = u+1;
  }

}
