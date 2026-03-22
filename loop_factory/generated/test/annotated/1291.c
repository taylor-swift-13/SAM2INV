int main1(int e){
  int qpo, x;
  qpo=e-8;
  x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= x;
  loop invariant (qpo >= 0) ==> (0 <= x && x <= qpo);
  loop invariant qpo == (e - 8);
  loop assigns x;
*/
while (1) {
      if (!(x+1<=qpo)) {
          break;
      }
      x = x + 1;
  }
}