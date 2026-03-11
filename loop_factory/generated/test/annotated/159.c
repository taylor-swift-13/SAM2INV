int main1(int p,int c){
  int mu, r3, no, ge, sbj;
  mu=(p%31)+12;
  r3=mu;
  no=39;
  ge=1;
  sbj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mu == (\at(p, Pre) % 31) + 12;
  loop invariant r3 == mu + sbj;
  loop invariant ge == sbj + 1;
  loop invariant sbj >= 0;
  loop invariant 0 <= no;
  loop invariant no <= 39;
  loop invariant mu == (p % 31) + 12;
  loop assigns no, ge, sbj, r3;
*/
while (no>0&&ge<=mu) {
      if (no>ge) {
          no -= ge;
      }
      else {
          no = 0;
      }
      ge = ge + 1;
      sbj++;
      r3 = r3 + 1;
  }
}