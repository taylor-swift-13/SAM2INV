int main1(){
  int l36, wm, lv, fs, h, z;
  l36=1;
  wm=0;
  lv=0;
  fs=0;
  h=l36;
  z=l36;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l36 == 1;
  loop invariant fs <= l36;
  loop invariant lv == fs;
  loop invariant z == 1 + fs*(fs + 1)/2;
  loop invariant h >= 1;
  loop invariant 0 <= fs;
  loop assigns lv, fs, h, z;
*/
while (1) {
      if (!(fs<l36)) {
          break;
      }
      lv++;
      fs++;
      h = h*h+h;
      z = z + fs;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fs <= h;
  loop invariant wm == fs - 1;
  loop invariant lv == fs*(fs + 1)/2;
  loop invariant wm >= 0;
  loop assigns fs, wm, lv;
*/
while (fs<h) {
      fs++;
      wm = wm + 1;
      lv = lv + fs;
  }
}