int main1(int k,int n){
  int g, u, b;

  g=n;
  u=0;
  b=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant u >= 0;
  loop invariant b >= 8;
  loop invariant (b + 2) % 2 == 0;
  loop invariant g == n;
  loop invariant (b + 2) % 10 == 0;
  loop invariant b % 2 == 0;
  loop invariant g == n && n == \at(n, Pre) && u >= 0 && b >= 8;
  loop invariant g == n && u >= 0;
  loop invariant b >= 8 && n == \at(n, Pre);
  loop invariant b >= 8 + u;
  loop invariant b >= 2*u + 8;
  loop invariant b > 2*u;
  loop invariant k == \at(k, Pre) && n == \at(n, Pre);
  loop assigns b, u;
*/
while (1) {
      b = b+1;
      b = b+b;
      u = u+1;
  }

}
