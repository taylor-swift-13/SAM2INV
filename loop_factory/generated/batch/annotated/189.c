int main1(int k,int n){
  int r, u, g, v;

  r=(k%34)+7;
  u=0;
  g=6;
  v=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant g == 3*u + 6;
  loop invariant v >= 3;

  loop invariant (u == 0 ==> v == 3) && (u >= 1 ==> (v % 2) == 0);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);

  loop invariant u >= 0;
  loop invariant r == (k % 34) + 7;
  loop assigns g, v, u;
*/
while (u+1<=r) {
      g = g+3;
      v = v+g;
      v = v+v;
      u = u+1;
  }

}
