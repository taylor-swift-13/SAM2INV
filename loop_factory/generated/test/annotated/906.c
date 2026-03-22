int main1(){
  int b, yn, l6, x, op;
  b=(1%12)+19;
  yn=0;
  l6=0;
  x=0;
  op=yn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == l6 * (l6 - 1) / 2;
  loop invariant op == b * l6;
  loop invariant 0 <= l6 <= b;
  loop assigns x, l6, op;
*/
while (l6<b) {
      x += l6;
      l6 = l6 + 1;
      op += b;
  }
}