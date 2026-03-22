int main1(){
  int y, i, c9g, wf;
  y=1+20;
  i=0;
  c9g=1;
  wf=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wf == 2*c9g + 2;
  loop invariant i % 5 == 0;
  loop invariant 0 <= i;
  loop invariant i <= y;
  loop assigns c9g, wf, i;
*/
for (; i<=y-5; i = i + 5) {
      c9g = c9g*2;
      wf = wf + c9g;
  }
}