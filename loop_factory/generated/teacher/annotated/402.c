int main1(int p,int q){
  int h, d, n, c;

  h=48;
  d=h;
  n=d;
  c=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 48;
  loop invariant d == 48;
  loop invariant n % 5 == 3;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant n >= 48;
  loop invariant d >= 3;
  loop invariant n >= d;
  loop invariant (n - d) % 5 == 0;
  loop invariant (n - 48) % 5 == 0;
  loop assigns n;
*/
while (d>=3) {
      n = n+4;
      n = n+1;
  }

}
