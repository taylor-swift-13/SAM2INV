int main1(){
  int a, g30m, n, q0o8;
  a=(1%28)+8;
  g30m=(1%22)+5;
  n=0;
  q0o8=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a >= 9;
  loop invariant a % 9 == 0;
  loop invariant n >= 0;
  loop invariant n % 9 == 0;
  loop invariant (0 <= g30m);
  loop invariant (g30m <= 6);
  loop invariant (5 <= q0o8);
  loop invariant ((q0o8 - 5) >= (n % 8));
  loop assigns a, g30m, n, q0o8;
*/
while (g30m!=0) {
      if (g30m%2==1) {
          n = n + a;
          g30m = g30m - 1;
      }
      a = 2*a;
      g30m = g30m/2;
      q0o8 = q0o8+(n%8);
  }
}