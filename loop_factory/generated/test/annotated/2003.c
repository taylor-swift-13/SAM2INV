int main1(int b){
  int ed3m, m8, gf, bsg, hg;
  ed3m=b*2;
  m8=0;
  gf=1;
  bsg=1;
  hg=ed3m;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ed3m == b * 2;
  loop invariant m8 >= 0;
  loop invariant (ed3m >= 0) ==> (m8 <= ed3m);
  loop invariant hg == ed3m + (m8 * (m8 + 1)) / 2;
  loop invariant bsg == gf;
  loop invariant ed3m == \at(b,Pre) * 2;
  loop assigns m8, bsg, gf, hg;
*/
while (m8 < ed3m) {
      m8 = m8 + 1;
      bsg = bsg * b;
      gf = gf * b;
      hg = hg + m8;
  }
}