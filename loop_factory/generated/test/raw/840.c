int main1(){
  int d5kq, q65, dqcr, rypl, i6p;

  d5kq=28;
  q65=0;
  dqcr=-2;
  rypl=6;
  i6p=(1%6)+2;

  while (1) {
      if (rypl>=d5kq) {
          break;
      }
      q65 = q65*i6p+1;
      dqcr = dqcr*i6p;
      rypl += 1;
      i6p = i6p*4+(rypl%7)+2;
  }

}
