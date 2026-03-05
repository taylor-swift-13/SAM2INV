int main1(){
  int ww, v1m, c2x;
  ww=1-10;
  v1m=0;
  c2x=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v1m >= 0;
  loop invariant c2x == 4 + 3 * v1m;
  loop invariant ww == 1 - 10;
  loop assigns c2x, v1m;
*/
for (; v1m<ww; v1m = v1m + 1) {
      c2x = c2x + 3;
  }
}