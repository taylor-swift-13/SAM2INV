int main1(int a){
  int uv, f, xc, mb1n;
  uv=0;
  f=0;
  xc=(a%28)+10;
  mb1n=a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uv == 0;
  loop invariant mb1n == \at(a, Pre);
  loop invariant mb1n == a + f * uv;
  loop invariant xc == ((a % 28) + 10) - (f * (f - 1)) / 2;
  loop invariant f >= 0;
  loop assigns xc, mb1n, f;
*/
while (xc>f) {
      xc -= f;
      mb1n = mb1n + uv;
      f = (1)+(f);
  }
}