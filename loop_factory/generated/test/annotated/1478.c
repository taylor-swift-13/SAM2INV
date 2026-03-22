int main1(){
  int sfyr, d3, w, xos;
  sfyr=1+10;
  d3=(1%18)+5;
  w=(1%15)+3;
  xos=d3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xos + sfyr * d3 == 72;
  loop invariant d3 >= 0;
  loop invariant w == d3 - 2;
  loop invariant xos + sfyr*w == 50;
  loop assigns xos, d3, w;
*/
while (d3!=0) {
      xos += sfyr;
      d3 -= 1;
      w = w - 1;
  }
}