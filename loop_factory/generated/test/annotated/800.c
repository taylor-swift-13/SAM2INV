int main1(){
  int fxv, yj, l77w, xg1;
  fxv=1+12;
  yj=0;
  l77w=yj;
  xg1=11;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xg1 == (11 >> yj);
  loop invariant l77w == 0;
  loop invariant 0 <= yj;
  loop invariant yj <= fxv;
  loop invariant xg1 >= 0;
  loop invariant xg1 <= 11;
  loop invariant fxv == 13;
  loop assigns xg1, l77w, yj;
*/
for (; yj<=fxv-1; yj += 1) {
      xg1 = xg1/2;
      l77w = l77w*2;
  }
}