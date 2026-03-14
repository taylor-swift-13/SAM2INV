int main1(int p){
  int ae, zo, sjp, ql, kp, cnv;

  ae=26;
  zo=0;
  sjp=20;
  ql=0;
  kp=1;
  cnv=0;

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
