int main1(){
  int hv, lvy, i, f, zd;
  hv=1;
  lvy=0;
  i=0;
  f=0;
  zd=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lvy == i;
  loop invariant f == i*(i+1)/2;
  loop invariant zd == i*(i+1)*(i+2)/6;
  loop invariant (0 <= lvy && lvy <= hv);
  loop invariant (0 <= i && i <= hv);
  loop assigns i, f, lvy, zd;
*/
while (lvy < hv) {
      i = i + 1;
      f = f + i;
      lvy += 1;
      zd += f;
  }
}