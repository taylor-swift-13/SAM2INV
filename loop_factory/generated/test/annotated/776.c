int main1(int r){
  int nx, i, s6l, sj;
  nx=(r%22)+10;
  i=0;
  s6l=r;
  sj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s6l == \at(r, Pre) + i*(i-1)/2;
  loop invariant sj == 0;
  loop invariant i >= 0;
  loop assigns i, s6l, sj;
*/
while (i+1<=nx) {
      s6l = s6l + i;
      sj = sj*sj;
      i = i + 1;
  }
}