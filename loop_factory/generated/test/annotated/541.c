int main1(int o){
  int zx, hw, cu2, n;
  zx=o;
  hw=0;
  cu2=0;
  n=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cu2 == hw*(11 - hw)/2;
  loop invariant o == \at(o, Pre) * (1 + hw);
  loop invariant n + hw == 5;
  loop invariant zx == \at(o, Pre);
  loop invariant 0 <= n;
  loop assigns cu2, hw, o, n;
*/
while (hw<zx&&n>0) {
      cu2 += n;
      hw++;
      o += zx;
      n = n - 1;
  }
}