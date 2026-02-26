int main1(int k,int p){
  int b, u, v, g;

  b=54;
  u=2;
  v=k;
  g=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == 2 - u;
  loop invariant v == k + 2*u - 4;
  loop invariant 2 <= u <= b;
  loop invariant v >= k;
  loop invariant k == \at(k, Pre);
  loop invariant u <= b;
  loop invariant (u + g) == 2;
  loop invariant p == \at(p, Pre);
  loop invariant g + u == 2;
  loop invariant v == k + 2*(u - 2);
  loop invariant v - 2*u == k - 4;
  loop invariant 2 <= u;
  loop invariant v == 2*u + k - 4;
  loop assigns u, v, g;
*/
while (u<=b-1) {
      v = v+1;
      g = g-1;
      v = v+1;
      u = u+1;
  }

}
