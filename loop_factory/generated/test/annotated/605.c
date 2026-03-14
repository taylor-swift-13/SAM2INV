int main1(){
  int b7, zzl, je, on;
  b7=(1%28)+14;
  zzl=b7;
  je=0;
  on=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (je == 0) ==> (on == -6);
  loop invariant je <= b7;
  loop invariant zzl == b7;
  loop invariant on + je <= 2*b7 + 1;
  loop invariant (je == 0 ==> on == -6) && (je > 0 ==> on + je == 2*b7 + 1);
  loop invariant (0 <= je);
  loop assigns je, on;
*/
while (1) {
      if (!(je<=b7-1)) {
          break;
      }
      on = b7-je;
      je = je + 1;
      on += zzl;
  }
}