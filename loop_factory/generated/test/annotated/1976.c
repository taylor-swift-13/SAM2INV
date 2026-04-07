int main1(){
  int v, d, n, x07;
  v=145;
  d=v;
  n=-3;
  x07=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x07 == -2;
  loop invariant v == 145;
  loop invariant d >= 0;
  loop invariant n >= -3;
  loop invariant (n % 3) == 0;
  loop invariant (d <= v);
  loop assigns n, d, x07;
*/
while (d > 0) {
      n = (3)+(n);
      d = d/2;
      x07 = x07*2+(n%3)+2;
  }
}