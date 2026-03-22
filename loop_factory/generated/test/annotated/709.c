int main1(){
  int bsf, vv, de1, lw, cj, bu, vx;
  bsf=1+21;
  vv=0;
  de1=6;
  lw=0;
  cj=bsf;
  bu=(1%35)+8;
  vx=vv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bsf == 22;
  loop invariant lw >= 0;
  loop invariant de1 >= 6;
  loop invariant vx >= 0;
  loop invariant (0 <= bu && bu <= 9);
  loop invariant cj == bsf + lw;
  loop assigns de1, cj, lw, bu, vx;
*/
while (bu>0) {
      de1 = de1+lw*lw;
      cj = cj+bu*bu;
      lw = lw+bu*bu;
      bu = bu - 1;
      vx = vx + cj;
  }
}