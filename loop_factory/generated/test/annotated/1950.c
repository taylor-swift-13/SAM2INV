int main1(int f){
  int wm, ol, a5;
  wm=f*3;
  ol=0;
  a5=ol;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == \at(f, Pre) + ol;
  loop invariant wm == \at(f, Pre) * 3;
  loop invariant a5 == 0;
  loop invariant (ol >= 0);
  loop invariant (wm >= 0 ==> ol <= wm);
  loop assigns a5, f, ol;
*/
while (ol < wm) {
      a5 += a5;
      f = f + 1;
      ol = ol + 1;
  }
}