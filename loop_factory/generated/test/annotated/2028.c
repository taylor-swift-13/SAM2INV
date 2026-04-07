int main1(){
  int ep, t, bfu, y6, dl29, x;
  ep=1+5;
  t=0;
  bfu=0;
  y6=0;
  dl29=0;
  x=ep;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= t;
  loop invariant t <= ep;
  loop invariant bfu == dl29 + (t*(t+1))/2;
  loop invariant x >= ep;
  loop invariant y6 >= 0;
  loop invariant dl29 >= 0;
  loop invariant x >= 6;
  loop assigns t, bfu, y6, dl29, x;
*/
while (t < ep) {
      t = (bfu += x, y6 += bfu, t + 1);
      dl29 += x;
      x = x*2+(y6%4)+3;
      bfu += t;
  }
}