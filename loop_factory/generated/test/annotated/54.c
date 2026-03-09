int main1(int p,int f){
  int ag, e, wo, cqu, yl;
  ag=f*4;
  e=0;
  wo=0;
  cqu=0;
  yl=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= yl;
  loop invariant yl <= 5;
  loop invariant e == 0;
  loop invariant cqu == 15 - (yl * (yl + 1)) / 2;
  loop invariant p == \at(p, Pre) + wo * ag;
  loop invariant wo + yl == 5;
  loop invariant cqu == wo*(11 - wo)/2;
  loop assigns cqu, wo, p, yl;
*/
while (wo<ag&&yl>0) {
      cqu = cqu + yl;
      wo += 1;
      p = p+ag-e;
      yl -= 1;
  }
}