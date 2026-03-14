int main1(int s,int m){
  int ki33, ftj, cu, v2f, nf0;
  ki33=50;
  ftj=ki33;
  cu=1;
  v2f=0;
  nf0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ftj == ki33;
  loop invariant v2f == (cu - 1) * cu * (2 * cu - 1) / 6;
  loop invariant s == \at(s, Pre) + (cu - 1) * ki33;
  loop invariant ki33 == 50;
  loop invariant 1 <= cu <= ki33+1;
  loop assigns cu, v2f, s;
*/
while (cu<=ki33) {
      v2f = v2f+cu*cu;
      s += ftj;
      cu = cu + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cu >= 1;
  loop invariant ki33 >= 50;
  loop invariant nf0 == 0;
  loop assigns cu, ftj, ki33;
*/
while (cu<nf0) {
      cu = cu + 1;
      ftj = (nf0)+(-(cu));
      ki33 += ftj;
  }
}