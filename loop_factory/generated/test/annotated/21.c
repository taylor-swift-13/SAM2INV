int main1(){
  int q6, ae, ez;
  q6=1;
  ae=q6;
  ez=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q6 == 1;
  loop invariant ae >= 1;
  loop invariant ez*2 == ae*ae + 3*ae - 4;
  loop invariant 2*ez == ae*ae + 3*ae - 4;
  loop invariant ez >= 0;
  loop invariant ae <= q6;
  loop invariant ez == (ae*ae + 3*ae - 4) / 2;
  loop assigns ez, ae;
*/
while (ae<q6) {
      ez++;
      ae = ae + 1;
      ez += ae;
  }
}