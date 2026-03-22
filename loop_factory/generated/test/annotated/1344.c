int main1(int z,int c){
  int vmuf, r, ft, k4, jj;
  vmuf=c+20;
  r=vmuf+7;
  ft=0;
  k4=(z%28)+10;
  jj=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ft >= 0;
  loop invariant ((\at(z,Pre) % 28) + 10) - ft*(ft-1)/2 == k4;
  loop invariant jj == 6 + ft*r;
  loop assigns k4, jj, ft;
*/
while (k4>ft) {
      k4 -= ft;
      jj += r;
      ft = (1)+(ft);
  }
}