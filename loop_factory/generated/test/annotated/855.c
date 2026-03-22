int main1(){
  int wt, je, ibf, r;
  wt=1+12;
  je=1;
  ibf=-4;
  r=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant je == 1;
  loop invariant wt >= 1;
  loop invariant r >= 2;
  loop invariant ibf <= r * r;
  loop assigns r, ibf, wt;
*/
while (je*2<=wt) {
      r = r + 1;
      ibf = r*r;
      wt = (je*2)-1;
  }
}