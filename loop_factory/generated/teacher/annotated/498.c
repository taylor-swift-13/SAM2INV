int main1(int k,int p){
  int b, u, v, g;

  b=54;
  u=1;
  v=b;
  g=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == b + 4*(u - 1);
  loop invariant g == k - (u - 1);
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant u <= b;
  loop invariant 1 <= u;
  loop invariant g <= k;
  loop invariant b == 54;
  loop invariant g == k - u + 1;
  loop invariant 0 <= u;
  loop invariant v >= b;
  loop assigns v, u, g;
*/
while (1) {
      if (u>=b) {
          break;
      }
      v = v+3;
      u = u+1;
      v = v+1;
      g = g-1;
  }

}
