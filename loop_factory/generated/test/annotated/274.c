int main1(int p){
  int ae, zo, sjp, ql, kp, cnv;
  ae=26;
  zo=0;
  sjp=20;
  ql=0;
  kp=1;
  cnv=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kp == zo + 1;
  loop invariant 0 <= zo <= ae;
  loop invariant 0 <= sjp;
  loop invariant 0 <= ql;
  loop invariant sjp + ql == 20;
  loop assigns cnv, kp, ql, sjp, zo;
*/
while (sjp>0&&zo<ae) {
      if (sjp<=kp) {
          cnv = sjp;
      }
      else {
          cnv = kp;
      }
      kp = kp + 1;
      ql = ql + cnv;
      sjp = sjp - cnv;
      zo += 1;
  }
}