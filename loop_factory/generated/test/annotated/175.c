int main1(){
  int kt, j0n, f1h;
  kt=1+21;
  j0n=kt;
  f1h=kt;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kt == 1 + 21;
  loop invariant j0n == kt;
  loop invariant f1h >= 22;
  loop assigns f1h;
*/
while (j0n-1>=0) {
      f1h = f1h + 1;
      f1h = f1h+f1h*f1h;
  }
}