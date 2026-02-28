int main1(int a,int b){
  int k, u, x, m;

  k=(a%33)+10;
  u=0;
  x=8;
  m=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x - u == 8;
  loop invariant m % 2 == 0;
  loop invariant a == \at(a, Pre);
  loop invariant u >= 0;
  loop invariant m >= 2;
  loop invariant b == \at(b, Pre);
  loop invariant x == u + 8;
  loop invariant x >= 8;
  loop invariant x == 8 + u;
  loop invariant k == (a % 33) + 10;
  loop assigns x, m, u;
*/
while (1) {
      x = x+1;
      m = m+x;
      m = m+m;
      u = u+1;
  }

}
